Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

Definition make_nth_func
  {A:Type} (l:list A) (def:A) (n:Z) :=
  nth (Z.to_nat n) l def.

Definition Z_to_val (a:Z) := Vint (Int.repr a).

Fixpoint is_cstring (s:list Z) :=
  match s with
  | nil => false
  | 0 :: _ => true
  | Zneg _ :: _ => false
  | c :: t => 
      match Z_lt_dec c 256 with
      | left _ => is_cstring t
      | _ => false
      end
  end.

Fixpoint cstring_len (s:list Z) :=
  match s with
  | 0 :: _ => 0
  | c :: t => cstring_len t + 1
  | _ => 0
  end.

Lemma cstring_len_ge_0:
  forall s:list Z, cstring_len s >= 0.
Proof.
  induction s.
  + simpl; omega.
  + simpl; destruct a; omega.
Qed.

Definition assoc_array_cstr sh s id :=
  array_at tschar sh (make_nth_func (map Z_to_val s) (Z_to_val 1))
                  0 (Z.of_nat (length s)) id.

Lemma val_is_vint:
  forall i j l,
  (make_nth_func (map Z_to_val l) (Z_to_val j) i) =
  Vint (Int.repr (nth (Z.to_nat i) l j)).
Proof.
  intros i j l.
  unfold make_nth_func.
  assert (forall m, Z_to_val m =
          Vint (Int.repr m)) as Z_to_val_exp.
  unfold Z_to_val; auto.
  rewrite <-Z_to_val_exp.
  rewrite map_nth; auto.
Qed.

Lemma Z_of_nat_S_n:
  forall n:nat, Z.of_nat (S n) = Z.of_nat n + 1.
Proof.
  intros n.
  simpl; rewrite Zpos_P_of_succ_nat.
  auto.
Qed.

Lemma Zlt_0_n_implies_lt:
  forall n, 0 < Z.of_nat n -> (0 < n)%nat.
Proof.
  intros n HZlt.
  destruct n.
  + simpl in HZlt; exfalso; apply Zlt_irrefl with (x := 0); auto.
  + apply lt_O_Sn.
Qed.

Lemma cstr_contents:
  forall (s:list Z) (i:nat),
  is_cstring s = true ->
  (Z.of_nat i < cstring_len s -> (nth i s 0) <> 0) /\
  (Z.of_nat i = cstring_len s -> (nth i s 1) = 0).
Proof.
  induction s.
  {
    simpl; intros i false_eq_true; discriminate.
  }
  {  
    intros i Hcstr.
    destruct a, i.
    + split.
      - simpl; intros; exfalso; omega.
      - simpl; auto.
    + cut (Z.of_nat (S i) > 0).
      intros Z_of_nat_Si_gt_0.
      simpl cstring_len; omega.
      cut (Z.of_nat i >= 0).
      rewrite Z_of_nat_S_n; omega.
      destruct i.
      - simpl; omega.
      - unfold Z.ge; simpl; discriminate.
    + split.
      - simpl; discriminate.
      - simpl; intros Habs.
        cut (cstring_len s >= 0).
        intros cslen_ge_0; exfalso; omega.
        apply cstring_len_ge_0.
    + rewrite Z_of_nat_S_n.
      cut (is_cstring s = true).
      intros Hcstr'.
      simpl.
      split.
      - intros Hlt; apply IHs; auto; omega.
      - intros Heq; apply IHs; auto; omega.
      - simpl in *.
        destruct (Z_lt_dec (Z.pos p) 256).
        * auto.
        * discriminate Hcstr.
    + simpl in *; discriminate Hcstr.
    + simpl in *; discriminate Hcstr.
  }
Qed.

Lemma cstr_contents_not_null:
  forall (i:nat) (s:list Z),
  Z.of_nat i < cstring_len s ->
  nth i s 0 <> 0.
Proof.
  intros i s.
  generalize i; clear i.
  induction s.
  {
    intros i.
    cut (0 <= Z.of_nat i).
    simpl; intros i_ge_0 i_lt_0; exfalso; omega.
    apply Zle_0_nat.
  }
  {
    intros i; destruct i.
    + destruct a.
      - simpl; intros O_lt_O; exfalso; omega.
      - simpl; discriminate.
      - simpl; discriminate.
    + rewrite Z_of_nat_S_n; intros Si_lt_Scslen.
      simpl in *.
      apply IHs.
      destruct a.
      - exfalso; simpl in Si_lt_Scslen; omega.
      - omega.
      - omega.
  }
Qed.  
      
Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list Z, sh: share, s: val
    PRE [ _s OF tptr tschar ]
      PROP (is_cstring str = true;
            (cstring_len str) < Int.max_signed;
            (cstring_len str) < Zlength str)
      LOCAL (`(eq s) (eval_id _s);
             `isptr (eval_id _s))
      SEP(`(assoc_array_cstr sh str s))
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq s) (eval_id _s);
             `(eq (Vint (Int.repr (cstring_len str)))) retval)
      SEP (`(assoc_array_cstr sh str s)).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := my_strlen_spec :: nil.

Lemma body_my_strlen:
  semax_body Vprog Gprog f_my_strlen my_strlen_spec.
Proof.
  start_function.
  name s_ _s.
  name i_ _i.
  name c_ _c.
  forward.
  forward.
  {
    instantiate (1 := Zlength str).
    instantiate (1 := (make_nth_func (map Z_to_val str)
                                     (Z_to_val 1))).
    instantiate (1 := sh).
    entailer!.
    + cut (cstring_len str >= 0).
      omega.
      apply cstring_len_ge_0.
    + rewrite val_is_vint; simpl; auto.
    + unfold assoc_array_cstr.
      rewrite Zlength_correct.
      entailer!.
  }
  forward_while
    (EX i:Z, EX c:Z,
     PROP (forall j, 0 <= j < i -> (nth (Z.to_nat j) str 0) <> 0;
           0 <= i <= (cstring_len str);
           i < (cstring_len str) <-> c <> 0)
     LOCAL (`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.repr c))) (eval_id _c);
            `isptr (eval_id _s))
     SEP(`(assoc_array_cstr sh str s)))
    (EX i:Z,
     PROP (forall j, 0 <= j < i -> (nth (Z.to_nat j) str 0) <> 0;
           0 <= i <= (cstring_len str))
     LOCAL (`(eq (Vint (Int.repr i))) (eval_id _i))
     SEP(`(assoc_array_cstr sh str s))).
  {
    apply exp_right with 0.
    apply exp_right with (nth 0 str 0).
    entailer!.
    + intros; omega.
    + cut (cstring_len str >= 0).
      omega.
      apply cstring_len_ge_0.
    + destruct str.
      - simpl. 
         
  }
  {
    entailer!.
  }
  {
    apply exp_right with i.
    entailer!.
  }
  {
    forward.
    forward.
    entailer!.
    + instantiate (1 := Zlength str).
       omega.
(** FIXME: IN PROGRESS **)