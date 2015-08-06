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
  array_at tuchar sh (make_nth_func (map Z_to_val s) (Z_to_val 1))
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

Lemma Zlt_0_n_implies_lt:
  forall n, 0 < Z.of_nat n -> (0 < n)%nat.
Proof.
  intros n HZlt.
  destruct n.
  + simpl in HZlt; exfalso; apply Zlt_irrefl with (x := 0); auto.
  + apply lt_O_Sn.
Qed.

Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list Z, sh: share, s: val
    PRE [ _s OF tptr tuchar ]
      PROP (is_cstring str = true;
            (cstring_len str) < Int.max_unsigned;
            (cstring_len str) < Zlength str)
      LOCAL (`(eq s) (eval_id _s))
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
    entailer!.
    + cut (cstring_len str >= 0).
      omega.
      apply cstring_len_ge_0.
    +
(** FIXME: IN PROGRESS **)