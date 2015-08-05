Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

Definition make_nth_func
  {A:Type} (l:list A) (def:A) (n:Z) :=
  nth (Z.to_nat n) l def.

Definition Z_to_val (a:Z) := Vint (Int.repr a).

Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list Z, len: nat, sh: share, s: val
    PRE [ _s OF tptr tuchar ]
      PROP ((len <= length str)%nat;
            (nth len str 1) = 0;
            (forall m, (m < len)%nat -> (nth m str 0) <> 0))
      LOCAL (`(eq s) (eval_id _s))
      SEP(`(array_at tuchar sh 
                     (make_nth_func (map Z_to_val str)
                                    (Z_to_val 1))
                     0 (Z.of_nat (length str)) s))
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq (Vint (Int.repr (Z.of_nat len))))
             retval)
      SEP ().

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := my_strlen_spec :: nil.

Lemma body_my_strlen:
  semax_body Vprog Gprog f_my_strlen my_strlen_spec.
Proof.
  start_function.
  name i _i.
  name c _c.
  forward.
(** FIXME: IN PROGRESS **)
    