Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

Definition Znth {A} i l def := nth (A := A) (Z.to_nat i) l def.

Definition make_arr_fun l := fun i => Znth i l (Vint (Int.repr 1)).

Inductive is_cstring: list int -> Prop :=
| cs_empty: is_cstring (Int.repr 0 :: nil)
| cs_prepend: 
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (c :: s)
| cs_append:
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (s ++ (c :: nil)).

Fixpoint cstring_len (s:list int) :=
  match s with
  | c :: t =>
    let i := Int.signed c in
    match i with
    | 0 => 0
    | _ => cstring_len t + 1
    end
  | nil => 0
  end.

Lemma cstring_len_ge_0:
  forall str, cstring_len str >= 0.
Proof.
  induction str; simpl; try case (Int.signed a); try intros; try omega.
Qed.

Lemma cstring_len_nz_prefix:
  forall str a, 
  a <> Int.repr 0 -> cstring_len (a :: str) = cstring_len str + 1.
Proof.
  intros str a Hnz.
  assert (a = Int.repr (Int.signed a)) as Ha_repr.
  symmetry; apply Int.repr_signed.
  simpl; destruct (Int.signed a); auto; try contradiction.
Qed.

Lemma aux_str_len_succ_lemma:
  forall str,
  Z.to_nat (cstring_len str + 1) = S (Z.to_nat (cstring_len str)).
Proof.
  intros str.
  rewrite Z2Nat.inj_add; simpl; try omega.
  cut (cstring_len str >= 0); try omega; apply cstring_len_ge_0.
Qed.

Lemma nth_cons_S:
  forall (A:Type) (l:list A) (n:nat) (a d:A),
  nth (S n) (a :: l) d = nth n l d.
Proof.
  intros A l n a d.
  simpl; auto.
Qed.

Lemma cstring_char_values:
  forall str,
  is_cstring str ->
  (Znth (cstring_len str) str (Int.repr 1)) = Int.repr 0 /\
  forall j, 0 <= j < (cstring_len str) ->
  (Znth (cstring_len str) str (Int.repr 1)) <> Int.repr 0.
Proof.
Admitted. (** FIXME **)

Lemma cstring_len_bounds:
  forall str,
  is_cstring str -> 0 <= cstring_len str < Zlength str.
Proof.
Admitted. (** FIXME **)

Lemma typecast_aux_lemma:
  forall i str,
  make_arr_fun (map Vint str) i =
  Vint (nth (Z.to_nat i) str (Int.repr 1)).
Proof.
  intros i str.
  unfold make_arr_fun, Znth; rewrite map_nth; simpl; auto.
Qed.

Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list int, sh: share, s: val
    PRE [ _s OF tptr tschar ]
      PROP (is_cstring str;
            (cstring_len str) < Int.max_signed)
      LOCAL (`(eq s) (eval_id _s);
             `isptr (eval_id _s))
      SEP(`(array_at tschar sh (make_arr_fun (map Vint str))
                     0 (Zlength str) s))
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq (Vint (Int.repr (cstring_len str)))) retval)
      SEP(`(array_at tschar sh (make_arr_fun (map Vint str))
                     0 (Zlength str) s)).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := my_strlen_spec :: nil.

Lemma body_my_strlen:
  semax_body Vprog Gprog f_my_strlen my_strlen_spec.
Proof.
  start_function.
  name s_ _s.
  name i_ _i.
  name c_ _c.
  assert (0 <= cstring_len str < Zlength str) as Hcstrlen.
  apply cstring_len_bounds; auto.
  forward.
  forward.
  {
    entailer!.
    + omega.
    + rewrite typecast_aux_lemma; simpl; auto.
  }
  forward_while
    (EX i:Z, EX c:Z,
     PROP (forall j, 0 <= j < i -> Znth j str (Int.repr 0) <> (Int.repr 0);
           0 <= i <= cstring_len str;
           c = Int.signed (Znth i str (Int.repr 0)))
     LOCAL (`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.sign_ext 8 (Int.repr c)))) (eval_id _c);
            `(eq s) (eval_id _s);
            `isptr (eval_id _s))
     SEP(`(array_at tschar sh (make_arr_fun (map Vint str))
                     0 (Zlength str) s)))
    (PROP ()
     LOCAL (`(eq (Vint (Int.repr (cstring_len str)))) (eval_id _i);
            `(eq s) (eval_id _s))
     SEP(`(array_at tschar sh (make_arr_fun (map Vint str))
                     0 (Zlength str) s))).
  {
    apply exp_right with 0.
    apply exp_right with (Int.signed (nth 0 str (Int.repr 0))).
    entailer!.
    + intros x Hge Hlt; exfalso; omega.
    + admit. (** FIXME **)
  }
  {
    entailer!.
  }
  {
    entailer!.
    + admit. (** FIXME **)
  }
  {
    forward.
    forward.
    {
      entailer!.
      + admit. (** FIXME **)
      + rewrite typecast_aux_lemma; simpl; auto.
    }
    {
      apply exp_right with (i + 1).
      apply exp_right with (Int.signed (Znth (i + 1) str (Int.repr 0))).
      entailer!.
      + admit. (** FIXME **)
      + admit. (** FIXME **)
      + rewrite typecast_aux_lemma in H4; simpl in H4.
        inversion H4; simpl.
        admit. (** FIXME **)
    }
  }
  forward.
Qed.