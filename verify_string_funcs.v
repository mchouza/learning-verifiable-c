Require Import List.
Require Import NArith.
Require Import ZArith.

Local Open Scope Z.

Definition Znth {A} i l def := if i >=? 0 then nth (A := A) (Z.to_nat i) l def else def.
Hint Unfold Znth.

Definition is_char_array (s:list Z) :=
  forall c, In c s -> -128 <= c < 128.

Definition is_cstring (s:list Z) :=
  is_char_array s /\ In 0 s.

Fixpoint strlen (s:list Z) :=
  match s with
  | nil => 0
  | 0 :: t => 0
  | c :: t => strlen t + 1
  end.

Lemma in_split_1st {A}:
  (forall x y:A, {x=y} + {x<>y}) ->
  forall (a:A) l, 
  In a l ->
  exists l1 l2, l = l1 ++ a :: l2 /\
  ~In a l1.
Proof.
  intros eq_dec a l a_in_l.
  induction l.
  + simpl in a_in_l; contradiction.
  + destruct a_in_l, (eq_dec a a0).
    - exists nil, l; subst a0; simpl; auto.
    - symmetry in H; contradiction.
    - exists nil, l; subst a0; simpl; auto.
    - destruct (IHl H) as (l1 & l2 & induct_eq & not_in_prefix).      
      exists (a0 :: l1), l2; subst l; firstorder.
Qed.

Lemma Zlength_nil:
  forall A, Zlength nil (A := A) = 0.
Proof.
  intros; rewrite Zlength_correct; auto.
Qed.

Lemma Zlength_cons {A}:
  forall (a:A) l, Zlength (a :: l) = Zlength l + 1.
Proof.
  intros; repeat rewrite Zlength_correct; simpl length; rewrite Nat2Z.inj_succ; omega.
Qed.

Lemma Zlength_ge_0 {A}: 
  forall (l:list A), 0 <= Zlength l.
Proof.
  intros; rewrite Zlength_correct; apply Nat2Z.is_nonneg.
Qed.

Lemma Znth_0 {A}:
  forall (a:A) l d, Znth 0 (a :: l) d = a.
Proof.
  intros; unfold Znth; auto.
Qed.

Lemma Znth_plus_1 {A}:
  forall (a:A) i l d, i >= 0 -> Znth (i + 1) (a :: l) d = Znth i l d.
Proof.
  intros; unfold Znth; simpl.
  assert (i + 1 = Z.succ i) as succ_eq by omega.
  assert (i + 1 >=? 0 = true) as cond_eq_true by (apply Z.geb_le; omega).
  assert (i >=? 0 = true) as cond_eq_true' by (apply Z.geb_le; omega).
  rewrite cond_eq_true, cond_eq_true', succ_eq, Z2Nat.inj_succ by omega; auto.
Qed.

Lemma Znth_def_indep {A}:
  forall (l:list A) i d1 d2, 
  0 <= i < Zlength l -> Znth i l d1 = Znth i l d2.
Proof.
  intros l i d1 d2 i_bounds; unfold Znth; rewrite Zlength_correct in *.
  assert (i >=? 0 = true) as i_ge_0_true by (apply Z.geb_le; omega).
  rewrite i_ge_0_true.
  apply nth_indep, Nat2Z.inj_lt.
  rewrite Z2Nat.id; omega.
Qed.

Lemma Znth_gen_prop {A}:
  forall (d:A) s P,
  (forall c, In c s -> P c) ->
  P d ->
  (forall i, P (Znth i s d)).
Proof.
  intros d s P P_in P_def i; unfold Znth.
  assert (forall i, P (nth (Z.to_nat i) s d)) as P_nth.
  {
    intros i'; destruct (nth_in_or_default (Z.to_nat i') s d) as [is_in | is_def].
    + apply P_in, is_in.
    + rewrite is_def; apply P_def.
  }
  case (i >=? 0); [ apply P_nth | apply P_def ].
Qed.

Lemma Znth_in {A}:
  forall (l:list A) i d, 0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros; unfold Znth; rewrite Zlength_correct in *.
  assert (i >=? 0 = true) as i_ge_0_true by (apply Z.geb_le; omega).
  rewrite i_ge_0_true.
  apply nth_In, Nat2Z.inj_lt; rewrite Z2Nat.id; omega.
Qed.

Lemma char_array_tail:
  forall c s, is_char_array (c :: s) -> is_char_array s.
Proof.
  intros c s c_s_is_carr c' c'_in_s; unfold is_char_array in *.
  apply c_s_is_carr, in_cons; auto.
Qed.

Lemma cstring_not_nil: 
  ~is_cstring nil.
Proof.
  intros [_ nil_has_null]; apply in_nil with (a := 0); auto.
Qed.

Lemma cstring_tail:
  forall c s, is_cstring (c :: s) -> c = 0 \/ is_cstring s.
Proof.
  intros c s [c_s_is_carr c_s_has_null]; unfold is_cstring.
  destruct (Z.eq_dec c 0).
  + auto.
  + right; split.
    - apply char_array_tail with (c := c); auto.
    - inversion c_s_has_null; try contradiction; auto.
Qed.

Lemma strlen_abs_bounds:
  forall s, 0 <= strlen s <= Zlength s.
Proof.
  induction s as [|c].
  + rewrite Zlength_nil; simpl; omega.
  + rewrite Zlength_cons; destruct c; simpl; omega.
Qed.

Lemma strlen_prefix:
  forall c s, strlen (c :: s) <= strlen s + 1.
Proof.
  intros; assert (0 <= strlen s) by apply strlen_abs_bounds.
  destruct c; simpl; try intros; omega.
Qed.

Lemma strlen_nz_prefix:
  forall c s, c <> 0 -> strlen (c :: s) = strlen s + 1.
  intros; destruct c.
  + exfalso; apply H; auto.
  + simpl; auto.
  + simpl; auto.
Qed.

Lemma cstring_strlen_bounds:
  forall s, is_cstring s -> 0 <= strlen s < Zlength s.
Proof.
  induction s as [|c].
  + intros; exfalso; apply cstring_not_nil; auto.
  + intros c_s_is_cstr.
    assert (c = 0 \/ is_cstring s) as [c_eq_0 | s_is_cstr] by (apply cstring_tail; auto).
    - assert (0 <= Zlength s) by apply Zlength_ge_0.
      rewrite Zlength_cons, c_eq_0; simpl; omega.
    - assert (strlen (c :: s) <= strlen s + 1) by apply strlen_prefix.
      assert (0 <= strlen (c :: s)) by apply strlen_abs_bounds.
      rewrite Zlength_cons; specialize (IHs s_is_cstr); omega.
Qed.

Lemma cstring_strlen_content:
  forall s d,
  is_cstring s ->
  Znth (strlen s) s d = 0 /\
  forall j, 0 <= j < strlen s -> Znth j s d <> 0.
Proof.
  intros s d [_ s_has_null].
  assert (exists p t, (s = p ++ 0 :: t) /\ ~In 0 p) as
    (p & t & s_splitted & prefix_has_no_null) by
    (apply (in_split_1st Z.eq_dec); auto).
  clear s_has_null; subst s; induction p.
  {
    simpl; rewrite Znth_0; split; try intros; omega.
  }
  {
    assert (~In 0 p) as p_has_no_null by
      (intros abs; apply prefix_has_no_null, in_cons; auto).
    specialize (IHp p_has_no_null).
    destruct (Z.eq_dec a 0).
    + subst a; exfalso; apply prefix_has_no_null, in_eq.
    + split.
      - rewrite <-app_comm_cons, strlen_nz_prefix, Znth_plus_1; auto.
        * apply IHp.
        * assert (0 <= strlen (p ++ 0 :: t)) by (apply strlen_abs_bounds; auto); omega.
      - intros j j_bounds; destruct (Z.eq_dec j 0).
        * rewrite e, <-app_comm_cons, Znth_0; auto.
        * assert (j = j - 1 + 1) as j_eq by omega.
          rewrite <-app_comm_cons, strlen_nz_prefix in j_bounds by auto.
          rewrite j_eq, <-app_comm_cons, Znth_plus_1; try omega; apply IHp; omega; auto.
  }
Qed.

Lemma cstring_has_bounded_chars:
  forall c s, is_cstring s -> In c s -> -128 <= c < 128.
Proof.
  intros c s [s_is_carr _] c_in_s; unfold is_char_array in *.
  apply s_is_carr, c_in_s.
Qed.
  
Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.
Require Import string_funcs.

Local Open Scope logic.

Lemma eqmod_small_eq_shifted:
  forall a b m k,
  k <= a < m + k ->
  k <= b < m + k ->
  Int.eqmod m a b ->
  a = b.
Proof.
  intros a b m k a_bounds b_bounds a_eqmod_b.
  cut (a - k = b - k); try omega.
  apply Int.eqmod_small_eq with (modul := m); try omega.
  apply Int.eqmod_add, Int.eqmod_refl; auto.
Qed.

Lemma eqmod_unsigned_repr:
  forall i n,
  0 < n < Int.zwordsize ->
  Int.eqmod (two_p n) (Int.unsigned (Int.repr i)) i.
Proof.
  intros i n n_bounds.
  apply Int.eqmod_divides with (n := Int.modulus).
  + fold Int.eqm.
    apply Int.eqm_unsigned_repr_l, Int.eqm_refl.
  + unfold Int.modulus.
    rewrite two_power_nat_two_p.
    fold Int.zwordsize.
    exists (two_p (Int.zwordsize - n)).
    rewrite <-two_p_is_exp by omega.
    assert (Int.zwordsize = Int.zwordsize - n + n) as ws_eq by omega.
    rewrite ws_eq at 1; auto.
Qed.

Lemma signed_ext_idempotence:
  forall i n,
  0 < n < Int.zwordsize ->
  -two_p (n - 1) <= i < two_p (n - 1) ->
  Int.sign_ext n (Int.repr i) = Int.repr i.
Proof.
  intros i n n_bounds i_bounds.
  assert (two_p n + - two_p (n - 1) = two_p (n - 1)) as two_p_eq.
  {
    assert (n = Z.succ (n - 1)) as n_eq by omega.
    rewrite n_eq at 1.
    rewrite two_p_S by omega.
    ring.
  }
  rewrite <-Int.repr_signed with (i := Int.sign_ext n (Int.repr i)).
  apply f_equal.
  apply eqmod_small_eq_shifted with (m := two_p n) (k := -two_p (n - 1)).
  + rewrite two_p_eq.
    apply Int.sign_ext_range; auto.
  + omega.
  + assert (Int.eqmod (two_p n)
                      (Int.signed (Int.sign_ext n (Int.repr i)))
                      (Int.unsigned (Int.repr i))) as eq_1 by
      (apply Int.eqmod_sign_ext; auto).
    assert (Int.eqmod (two_p n) (Int.unsigned (Int.repr i)) i) as eq_2 by
      (apply eqmod_unsigned_repr; auto).
    apply Int.eqmod_trans with (y := (Int.unsigned (Int.repr i))); auto.
Qed.

Lemma bool_char_eq_value:
  forall s i,
  is_char_array s ->
  0 <= i < Zlength s ->
  negb (Int.eq (Int.sign_ext 8 (Int.repr (Znth i s 0)))
               (Int.repr 0)) = 
  negb (Z.eqb (Znth i s 0) 0).
Proof.
  intros s i s_is_carr i_bounds.
  assert (-128 <= Znth i s 0 < 128) as char_bound by (apply s_is_carr, Znth_in; auto).
  rewrite signed_ext_idempotence by (compute; auto).
  apply f_equal.
  destruct (eq_dec (Znth i s 0) 0).
  + rewrite e; simpl; apply Int.eq_true.
  + rewrite Int.eq_false.
    - symmetry; rewrite Z.eqb_neq; auto.
    - intros repr_eq.    
      assert (Znth i s 0 = 0) as abs.
      {
        rewrite <-Int.signed_repr with (z := Znth i s 0) by
          (unfold Int.min_signed, Int.max_signed; simpl; omega).
        rewrite <-Int.signed_repr with (z := 0) at 2 by
          (unfold Int.min_signed, Int.max_signed; simpl; omega).
        rewrite repr_eq; auto.
      }
      contradiction.
Qed.
        
Lemma typecast_aux_lemma:
  forall s,
  is_int
    (force_val
       (sem_cast_i2i I8 Signed
          ((fun i : Z => Vint (Int.repr (Znth i s 1))) 0))).
Proof.
  unfold Znth; simpl; auto.
Qed.

Lemma cstring_in_lemma:
  forall i s,
  is_cstring s ->
  0 <= i <= strlen s ->
  negb (Int.eq (Int.sign_ext 8 (Int.repr (Znth i s 0)))
               (Int.repr 0)) = true ->
  i < strlen s.
Proof.
  intros i s s_is_cstr strlen_s_bounds char_eq.
  assert (0 <= strlen s < Zlength s) by (apply cstring_strlen_bounds; auto).
  rewrite bool_char_eq_value in char_eq by (destruct s_is_cstr; auto; omega).
  destruct (eq_dec i (strlen s)).
  + assert (Znth i s 0 = 0) as s_i_is_null by (rewrite e; apply cstring_strlen_content; auto).
    rewrite s_i_is_null in char_eq; simpl in char_eq; discriminate.
  + omega.
Qed.

Lemma cstring_end_lemma:
  forall i s,
  is_cstring s ->
  0 <= i <= strlen s ->
  negb (Int.eq (Int.sign_ext 8 (Int.repr (Znth i s 0)))
               (Int.repr 0)) = false ->
  strlen s = i.
Proof.
  intros i s s_is_cstr strlen_s_bounds char_eq.
  assert (0 <= strlen s < Zlength s) by (apply cstring_strlen_bounds; auto).
  rewrite bool_char_eq_value in char_eq by (destruct s_is_cstr; auto; omega).
  destruct (eq_dec i (strlen s)).
  + auto.
  + assert (forall j, 0 <= j < strlen s -> Znth j s 0 <> 0) as s_content_not_null by
      (apply cstring_strlen_content; auto).
    assert (Znth i s 0 <> 0) as char_ineq by (apply s_content_not_null; omega).
    assert (Znth i s 0 =? 0 = false) as char_eq_is_false by (apply Z.eqb_neq; auto).
    rewrite char_eq_is_false in char_eq; simpl in char_eq; discriminate.
Qed.

Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH s_arr: list Z, sh: share, s: val
    PRE [ _s OF tptr tschar ]
      PROP (is_cstring s_arr;
            Zlength s_arr <= Int.max_signed)
      LOCAL (`(eq s) (eval_id _s);
             `isptr (eval_id _s))
      SEP(`(array_at tschar sh (fun i => Vint (Int.repr (Znth i s_arr 1)))
                     0 (Zlength s_arr) s))
    POST [ tuint ]
      PROP ()
      LOCAL (`(eq (Vint (Int.repr (strlen s_arr)))) retval)
      SEP(`(array_at tschar sh (fun i => Vint (Int.repr (Znth i s_arr 1)))
                     0 (Zlength s_arr) s)).

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
    entailer!.
    + assert (0 <= strlen s_arr < Zlength s_arr) by (apply cstring_strlen_bounds; auto); omega.
    + apply typecast_aux_lemma.
  }
  forward_while
  (EX i:Z, EX c:Z,
   PROP (forall j, 0 <= j < i -> Znth j s_arr 0 <> 0;
         0 <= i <= strlen s_arr;
         c = Znth i s_arr 0)
   LOCAL (`(eq (Vint (Int.repr i))) (eval_id _i);
          `(eq (Vint (Int.sign_ext 8 (Int.repr c)))) (eval_id _c);
          `(eq s) (eval_id _s);
          `isptr (eval_id _s))
   SEP(`(array_at tschar sh (fun i => Vint (Int.repr (Znth i s_arr 1)))
                  0 (Zlength s_arr) s)))
  (PROP ()
   LOCAL (`(eq (Vint (Int.repr (strlen s_arr)))) (eval_id _i);
          `(eq s) (eval_id _s))
   SEP(`(array_at tschar sh (fun i => Vint (Int.repr (Znth i s_arr 1)))
                  0 (Zlength s_arr) s))).
  {
    apply exp_right with 0.
    apply exp_right with (Znth 0 s_arr 0).
    entailer!.
    + intros; omega.
    + assert (0 <= strlen s_arr) by apply strlen_abs_bounds; omega.
    + assert (0 <= strlen s_arr < Zlength s_arr) by (apply cstring_strlen_bounds; auto).
      rewrite Znth_def_indep with (d2 := 1) by omega; auto.
  }
  {
    entailer!.
  }
  {
    entailer!.
    + cut (strlen s_arr = i).
      - apply f_equal.
      - apply cstring_end_lemma; auto.
  }
  {
    forward.
    forward.
    {
      assert (0 <= strlen s_arr < Zlength s_arr) by (apply cstring_strlen_bounds; auto).
      assert (i < strlen s_arr) by (apply cstring_in_lemma; auto).
      entailer!.
      + omega.
      + apply typecast_aux_lemma; auto.
    }
    {
      apply exp_right with (i + 1).
      apply exp_right with (Znth (i + 1) s_arr 0).
      entailer!.
      - assert (i < strlen s_arr) by (apply cstring_in_lemma; auto).
        intros; apply cstring_strlen_content; auto; omega.
      - assert (i < strlen s_arr) by (apply cstring_in_lemma; auto); omega.
      - assert (i < strlen s_arr) by (apply cstring_in_lemma; auto).
        assert (0 <= strlen s_arr < Zlength s_arr) by (apply cstring_strlen_bounds; auto).
        rewrite Int.signed_repr.
        * rewrite Znth_def_indep with (d2 := 1); auto; omega.
        * assert (Int.min_signed < 0) by apply Int.min_signed_neg; omega.
    }
  }
  forward.
Qed.