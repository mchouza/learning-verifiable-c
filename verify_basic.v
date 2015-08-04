Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import basic.

Local Open Scope logic.

Definition sum_spec :=
  DECLARE _sum
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

Definition mul_spec :=
  DECLARE _mul
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
      LOCAL (`(eq (Vint (Int.repr (a * b))))
             retval)
      SEP ().

Definition mul2_spec :=
  DECLARE _mul2
    WITH a:Z, b:Z
    PRE [ _a OF tuint, _b OF tint ]
      PROP (0 <= a <= Int.max_unsigned;
            0 <= b <= Int.max_signed)
      LOCAL (`(eq (Vint (Int.repr a)))
                  (eval_id _a);
             `(eq (Vint (Int.repr b)))
                  (eval_id _b))
      SEP()
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq (Vint (Int.repr (a * b))))
             retval)
      SEP ().

Definition mul3_spec :=
  DECLARE _mul3
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
      LOCAL (`(eq (Vint (Int.repr (a * b))))
             retval)
      SEP ().

Definition mul4_spec :=
  DECLARE _mul4
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
      LOCAL (`(eq (Vint (Int.repr (a * b))))
             retval)
      SEP ().

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := sum_spec :: mul_spec :: mul2_spec :: mul3_spec :: mul4_spec :: nil.

Lemma body_sum:
  semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_mul:
  semax_body Vprog Gprog f_mul mul_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_mul2:
  semax_body Vprog Gprog f_mul2 mul2_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound b
    (EX i:Z,
     PROP ()
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr (i * a))))
             (eval_id _c))
     SEP ()).
  entailer!.
  forward.
  entailer!.
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto.
  forward.
  rewrite Zmult_comm.
  entailer!.
Qed.

Lemma body_mul3:
  semax_body Vprog Gprog f_mul3 mul3_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while
    (EX i:Z,
     PROP (0 <= i <= b)
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr b)))
             (eval_id _b);
            `(eq (Vint (Int.repr i)))
             (eval_id _i);
            `(eq (Vint (Int.repr (i * a))))
             (eval_id _c))
     SEP ())
    (PROP ()
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr b)))
             (eval_id _b);
            `(eq (Vint (Int.repr (b * a))))
             (eval_id _c))
     SEP ()).
  {
    apply exp_right with 0.
    entailer!.
  }
  {
    entailer!.
  }
  {
    entailer!.
    cut (i = b).
    intros H4; rewrite H4; auto.
    cut (i >= b).
    {
      intros H4.
      unfold Zle, Zge in H2, H4.
      apply Z.compare_eq.
      destruct (i ?= b).
      + reflexivity.
      + exfalso; apply H4; reflexivity.
      + exfalso; apply H2; reflexivity.
    }
    apply ltu_repr_false; auto.
    omega.
  }
  {
    forward.
    forward.
    entailer!.
    apply exp_right with (i + 1).
    cut (i < b).
    intros H6.
    rewrite Zmult_plus_distr_l, Zmult_1_l.
    entailer!.
    apply ltu_repr; auto.
    omega.
  }
  {
    forward.
    rewrite Zmult_comm.
    entailer!.
  }
Qed.

Lemma body_mul4:
  semax_body Vprog Gprog f_mul4 mul4_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_for
    (EX i:Z,
     PROP (0 <= i <= b)
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr b)))
             (eval_id _b);
            `(eq (Vint (Int.repr i)))
             (eval_id _i);
            `(eq (Vint (Int.repr (i * a))))
             (eval_id _c))
     SEP ())
    (EX i:Z,
     PROP (0 <= i < b)
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr b)))
             (eval_id _b);
            `(eq (Vint (Int.repr i)))
             (eval_id _i);
            `(eq (Vint (Int.repr ((i + 1) * a))))
             (eval_id _c))
     SEP ())
    (PROP ()
     LOCAL (`(eq (Vint (Int.repr a)))
             (eval_id _a);
            `(eq (Vint (Int.repr b)))
             (eval_id _b);
            `(eq (Vint (Int.repr (b * a))))
             (eval_id _c))
     SEP ()).    
   {
     apply exp_right with 0.
     entailer!.
   }
   {
     entailer!.
   }
   {
     entailer!.
     cut (i = b).
     intros H4; rewrite H4; auto.
     cut (i >= b).
     intros H4.
     {
       unfold Zle, Zge in H2, H4.
       apply Z.compare_eq.
       destruct (i ?= b).
       + reflexivity.
       + exfalso; apply H4; reflexivity.
       + exfalso; apply H2; reflexivity.
     }
     apply ltu_repr_false; auto.
     omega.
   }
   {
     forward.
     apply exp_right with i.
     entailer!.
     apply ltu_repr; auto.
     omega.
     rewrite Zmult_plus_distr_l, Zmult_1_l.
     auto.
   }
   {
     apply extract_exists_pre.
     intros i.
     forward.
     apply exp_right with (i + 1).
     entailer!.
   }
   {
     forward.
     rewrite Zmult_comm.
     entailer!.
   }
Qed.