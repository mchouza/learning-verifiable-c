Require Import List.
Require Import NArith.
Require Import ZArith.

Local Open Scope Z.

Definition Znth {A} i l def := if i >=? 0 then nth (A := A) (Z.to_nat i) l def else def.

Definition make_arr_fun l := fun i => Znth i l 1.

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
  forall s,
  is_cstring s ->
  Znth (strlen s) s 1 = 0 /\
  forall j, 0 <= j < strlen s -> Znth j s 1 <> 0.
Proof.
  intros s [_ s_has_null].
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
