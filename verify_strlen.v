Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

(* TO BE DONE *)
Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH a:Z, b:Z
    PRE [ _a OF tuint, _b OF tuint ]
      PROP (0 <= a <= Int.max_unsigned;
            0 <= b <= Int.max_unsigned)
      LOCAL (`(eq (Vint (Int.repr a)))
                  (eval_id _a);
             `(eq (Vint (Int.repr b)))
                  (eval_id _b))
      SEP()
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq (Vint (Int.repr (a + b))))
             retval)
      SEP ().

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := my_strlen_spec :: nil.