Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

Definition Znth {A} i l def := nth (A := A) (Z.to_nat i) l def.

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

Definition make_arr_fun l := fun i => Znth i l (Vint (Int.repr 1)).

Inductive is_cstring: list int -> Prop :=
| cs_empty: is_cstring (Int.repr 0 :: nil)
| cs_prepend: 
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (c :: s)
| cs_append:
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (s ++ (c :: nil)).

Definition is_char_array (s:list int) :=
  forall c, In c s -> -128 <= Int.signed c < 128.

Definition is_cstring' (s:list int) :=
  is_char_array s /\ In (Int.repr 0) s.

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

Definition is_char_array str :=
  forall c, In c str -> -128 <= Int.signed c < 128.

Definition has_nulls str :=
  exists i,
  forall d,
  0 <= i < Zlength str /\
  Znth i str d = Int.repr 0 /\
  forall j, 0 <= j < i ->
  Znth j str d <> Int.repr 0.

Lemma nat_Z_xchg:
  forall n a,
  a >= 0 ->
  (Z.of_nat n = a <-> n = Z.to_nat a).
Proof.
  intros n a a_ge_0; split.
  + intros H; rewrite <-H, nat_of_Z_of_nat; auto.
  + intros H; rewrite H, nat_of_Z_eq; auto.
Qed.

Lemma nat_S_to_Z:
  forall n,
  Z.of_nat (S n) = (Z.of_nat n) + 1.
Proof.
  intros n; simpl.
  rewrite Zpos_P_of_succ_nat; auto.
Qed.

Lemma Z_plus_1_to_nat:
  forall a,
  a >= 0 -> Z.to_nat (a + 1) = S (Z.to_nat a).
Proof.
  intros a a_ge_0; simpl.
  rewrite Z2Nat.inj_add; simpl; auto; try omega.
Qed.

Lemma Zlength_ge_0:
  forall A (str:list A), Zlength str >= 0.
Proof.
  intros A str.
  cut (0 <= Zlength str).
  omega.
  rewrite Zlength_correct.
  apply Zle_0_nat.
Qed.

Lemma Zlength_cons:
  forall A (str:list A) c,
  Zlength (c :: str) = Zlength str + 1.
Proof.
  intros A str c.
  repeat rewrite Zlength_correct; simpl length; rewrite nat_S_to_Z; auto.
Qed.

Lemma Zlength_app:
  forall A (s1 s2:list A),
  Zlength (s1 ++ s2) = Zlength s1 + Zlength s2.
Proof.
  intros A s1 s2.
  repeat rewrite Zlength_correct; rewrite app_length.
  apply Nat2Z.inj_add.
Qed.

Lemma Zlength_single_elem:
  forall A (c:A), Zlength [c] = 1.
Proof.
  intros A c.
  rewrite Zlength_correct; simpl; auto.
Qed.

Lemma Znth_plus_one:
  forall A (str:list A) c i d,
  i >= 0 ->
  Znth (i + 1) (c :: str) d = Znth i str d.
Proof.
  intros A str c i d i_ge_0; unfold Znth.
  rewrite Z_plus_1_to_nat; simpl; auto.
Qed.

Lemma Znth_zero:
  forall A (str:list A) c d,
  Znth 0 (c :: str) d = c.
Proof.
  intros A str c d.
  unfold Znth; simpl; auto.
Qed.

Lemma Znth_le_zero:
  forall A (str:list A) i d,
  i <= 0 ->
  Znth i str d = Znth 0 str d.
Proof.
  intros A str i d i_hi_bound; unfold Znth.
  SearchAbout Z.to_nat.
  assert (Z.to_nat i = O) as nat_i_eq_0.
  {
    destruct i.
    + simpl; auto.
    + cut (0 < Z.pos p).
      - intros; omega.
      - unfold Z.lt; simpl; auto.
    + simpl; auto.
  }
  rewrite nat_i_eq_0; auto.
Qed.

Lemma Znth_default:
  forall A (str:list A) i d,
  Zlength str <= i ->
  Znth i str d = d.
Proof.
  intros A str i d i_lo_bound; unfold Znth.
  assert (0 <= Zlength str) as zl_ge_0.
  {
    rewrite Zlength_correct.
    apply Nat2Z.is_nonneg.
  }
  apply nth_overflow.
  rewrite <-nat_of_Z_of_nat with (n := length str), <-Zlength_correct.
  apply Z2Nat.inj_le; auto; omega.
Qed.

Lemma Znth_app_1st:
  forall A (s1 s2:list A) i d,
  0 <= i < Zlength s1 ->
  Znth i (s1 ++ s2) d = Znth i s1 d.
Proof.
  intros A s1 s2 i d i_bounds.
  unfold Znth; rewrite app_nth1; auto.
  cut (Z.to_nat i < Z.to_nat (Zlength s1))%nat.
  rewrite Zlength_correct, nat_of_Z_of_nat; auto.
  apply Z2Nat.inj_lt; auto; omega.
Qed.

Lemma Znth_app_2nd:
  forall A (s1 s2:list A) i d,
  i >= Zlength s1 ->
  Znth i (s1 ++ s2) d = Znth (i - Zlength s1) s2 d.
Proof.
  intros A s1 s2 i d i_lo_bound.
  unfold Znth; rewrite app_nth2.
  + rewrite Zlength_correct, Z2Nat.inj_sub, nat_of_Z_of_nat; auto.
    apply Zle_0_nat.
  + cut (length s1 <= Z.to_nat i)%nat.
    - omega.
    - assert (Zlength s1 >= 0) as zl_ge_0 by apply Zlength_ge_0.
      rewrite Zlength_correct in i_lo_bound.
      rewrite <-nat_of_Z_of_nat with (n := length s1).
      apply Z2Nat.inj_le; omega.
Qed.

Lemma Znth_matches:
  forall A (s:list A) i d1 d2,
  0 <= i < Zlength s ->
  Znth i s d1 = Znth i s d2.
Proof.
  intros A s i d1 d2 i_hi_bound.
  unfold Znth.
  apply nth_indep.
  rewrite Zlength_correct in i_hi_bound.
  rewrite <-nat_of_Z_of_nat.
  apply Z2Nat.inj_lt; omega.
Qed.

Lemma Znth_general_props:
  forall A (P:A -> Prop) (s:list A) i d,
  (forall c, In c s -> P c) ->
  P d ->
  P (Znth i s d).
Proof.
  intros A P s i d P_in P_out; unfold Znth.
  destruct (nth_in_or_default (Z.to_nat i) s d).
  + apply P_in with (c := (nth (Z.to_nat i) s d)); auto.
  + rewrite e; auto.
Qed.

Lemma cstring_not_nil: ~is_cstring [].
Proof.
  intros Habs.
  inversion Habs.
  assert (length (s ++ [c]) >= 1)%nat.
  rewrite app_length; simpl; omega.
  assert (length (s ++ [c]) = 0)%nat.
  rewrite H; simpl; auto.
  omega.
Qed.

Lemma cstring_Zlength_gt_zero:
  forall str, is_cstring str -> Zlength str > 0.
Proof.
  intros str str_is_cstring.
  destruct str.
  + exfalso; apply cstring_not_nil; auto.
  + rewrite Zlength_cons.
    cut (Zlength str >= 0).
    - omega.
    - apply Zlength_ge_0.
Qed.

Lemma cstring_has_bounded_chars:
  forall str d i,
  is_cstring str ->
  -128 <= Int.signed d < 128 ->
  -128 <= Int.signed (Znth i str d) < 128.
Proof.
  intros str d i str_is_cstring d_bounds.
  generalize i; clear i.
  induction str_is_cstring.
  {
    intros; destruct (zle i 0).
    + rewrite Znth_le_zero, Znth_zero by omega; simpl.
      rewrite Int.signed_repr.
      - omega.
      - assert (Int.min_signed < 0) as lo_bound by apply Int.min_signed_neg.
        assert (Int.max_signed >= 0) as hi_bound by apply Int.max_signed_pos.
        omega.
    + rewrite Znth_default; auto.
      unfold Zlength; simpl; omega.
  }
  {
    intros; destruct (zle i 0).
    + rewrite Znth_le_zero, Znth_zero by omega; auto.
    + assert (i = i - 1 + 1) as i_eq by omega.
      rewrite i_eq, Znth_plus_one by omega.
      apply IHstr_is_cstring.
  }
  {
    intros; destruct (zlt i (Zlength s)).
    + destruct (zlt i 0).
      - rewrite Znth_le_zero, Znth_app_1st; try omega.
        apply IHstr_is_cstring.
        cut (Zlength s > 0).
        * omega.
        * apply cstring_Zlength_gt_zero; auto.
      - rewrite Znth_app_1st by omega.
        apply IHstr_is_cstring.
    + rewrite Znth_app_2nd by auto.
      destruct (eq_dec i (Zlength s)).
      - assert (i - i = 0) as i_cancel by omega.
        rewrite <-e, i_cancel, Znth_zero; auto.
      - rewrite Znth_default.
        * omega.
        * rewrite Zlength_single_elem; omega.
  }
Qed.  

Lemma cstring_has_nulls:
  forall str, is_cstring str -> has_nulls str.
Proof.
  intros str str_is_cstring; unfold has_nulls.
  induction str_is_cstring.
  + exists 0; repeat split; simpl.
    - omega.
    - intros; omega.
  + destruct (eq_dec c (Int.repr 0)).
    - exists 0; rewrite e; repeat split; simpl.
      * omega.
      * cut (Zlength s >= 0).
        rewrite Zlength_cons; omega.
        apply Zlength_ge_0.
      * intros; omega.
    - destruct IHstr_is_cstring as [i str_is_cstring'].
      exists (i + 1); intros d; specialize (str_is_cstring' d);
      repeat split.
      * omega.
      * rewrite Zlength_cons; omega.
      * rewrite Znth_plus_one; try omega; apply str_is_cstring'.
      * intros j j_bounds; destruct (zeq j 0).
        {
          rewrite e, Znth_zero; auto.
        }
        {
          assert (j = j - 1 + 1) as j_pm_eq by omega.
          rewrite j_pm_eq, Znth_plus_one by omega.
          apply str_is_cstring' with (j := j - 1); omega.
        }
  + destruct IHstr_is_cstring as [i str_is_cstring'].
    exists i; intros d; specialize (str_is_cstring' d);
    repeat split; try omega.
    - rewrite Zlength_app, Zlength_single_elem; omega.
    - rewrite Znth_app_1st; auto; apply str_is_cstring'.
    - intros j j_bounds; rewrite Znth_app_1st; auto; try omega.
      apply str_is_cstring'; auto.
Qed.       

Lemma signed_bounds:
  forall a, -128 <= a < 128 ->
  Int.min_signed <= a <= Int.max_signed.
Proof.
  unfold Int.min_signed, Int.max_signed.
  intros a; simpl; omega.
Qed.

Lemma char_bound:
  forall c,
  -128 <= c < 128 ->
  -128 <= Int.signed (Int.repr c) < 128.
Proof.
  intros c c_bounds.
  rewrite Int.signed_repr; auto.
  apply signed_bounds; auto.
Qed.

Lemma char_eq:
  forall a b, 
  -128 <= a < 128 -> -128 <= b < 128 ->
  Int.repr a = Int.repr b ->
  a = b.
Proof.
  intros a b a_bounds b_bounds repr_eq.
  rewrite <-Int.signed_repr with (z := a), <-Int.signed_repr with (z := b) by
    (apply signed_bounds; auto).
  apply f_equal; auto.
Qed.  

Lemma char_zero_comp:
  forall a, -128 <= a < 128 -> a <> 0 -> Int.repr a <> Int.repr 0.
Proof.
  intros a Hbound_a Habs Habs_repr.
  apply Habs, char_eq; auto; omega.
Qed.

Lemma eqmod_small_eq_shifted:
  forall a b m k,
  k <= a < m + k ->
  k <= b < m + k ->
  Int.eqmod m a b ->
  a = b.
Proof.
  intros a b m k a_bounds b_bounds a_eqmod_b.
  cut (a - k = b - k).
  + omega.
  + apply Int.eqmod_small_eq with (modul := m).
    - apply Int.eqmod_add.
      * auto.
      * apply Int.eqmod_refl.
    - omega.
    - omega.
Qed.

Lemma unsigned_eq_implies_repr_equal:
  forall a b, Int.unsigned a = Int.unsigned b -> a = b.
Proof.
  intros a b unsigned_eq.
  cut (Int.repr (Int.unsigned a) = Int.repr (Int.unsigned b)).
  + repeat rewrite Int.repr_unsigned; auto.
  + apply f_equal; auto.
Qed.

Lemma eqmod_unsigned_repr:
  forall a, Int.eqmod (two_p 8) (Int.unsigned (Int.repr a)) a.
Proof.
  intros a.
  apply Int.eqmod_divides with (n := Int.modulus).
  + fold Int.eqm.
    apply Int.eqm_unsigned_repr_l, Int.eqm_refl.
  + exists (two_p 24); compute; auto.
Qed.

Lemma char_sign_ext_no_change:
  forall a,
  -128 <= a < 128 ->
  Int.sign_ext 8 (Int.repr a) = Int.repr a.
Proof.
  intros a a_bounds.
  rewrite <-Int.repr_signed with (i := Int.sign_ext 8 (Int.repr a)).
  apply f_equal.
  apply eqmod_small_eq_shifted with (m := two_p 8) (k := -two_p (8 - 1)).
  + apply Int.sign_ext_range; unfold Int.zwordsize; simpl; omega.
  + auto.
  + assert (Int.eqmod (two_p 8) (Int.signed (Int.sign_ext 8 (Int.repr a))) (Int.unsigned (Int.repr a))) as Heq_1.
    {
      apply Int.eqmod_sign_ext; unfold Int.zwordsize; simpl; omega.
    }
    assert (Int.eqmod (two_p 8) (Int.unsigned (Int.repr a)) a) as Heq_2.
    {
      apply eqmod_unsigned_repr.
    }
    apply Int.eqmod_trans with (y := (Int.unsigned (Int.repr a))); auto.
Qed.

Lemma char_sign_ext_zero_comp:
  forall a,
  -128 <= a < 128 ->
  Int.eq (Int.sign_ext 8 (Int.repr a)) (Int.repr 0) = Z.eqb a 0.
Proof.
  intros a a_bounds.
  destruct (eq_dec a 0).
  + rewrite e; simpl; auto.
  + assert ((a =? 0) = false) as a_neqb_0 by (apply Z.eqb_neq; auto).
    rewrite a_neqb_0.
    apply Int.eq_false.
    rewrite char_sign_ext_no_change by auto.
    apply char_zero_comp; auto.
Qed.     

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

Lemma cstring_len_aux_suffix_lemma:
  forall s c,
  cstring_len s <> cstring_len (s ++ [c]) ->
  cstring_len s = Zlength s.
Proof.
  intros s c.
  induction s.
  + intros _; rewrite Zlength_correct; simpl; auto.
  + intros len_ineq.
    destruct (eq_dec a (Int.repr 0)).
    - exfalso; apply len_ineq; rewrite e, <-app_comm_cons.
      simpl; auto.
    - rewrite Zlength_cons, cstring_len_nz_prefix; auto.
      cut (cstring_len s = Zlength s). omega.
      apply IHs.
      rewrite <-app_comm_cons in len_ineq.
      repeat rewrite cstring_len_nz_prefix in len_ineq by auto.
      omega.      
Qed.

Lemma cstring_len_abs_bound:
  forall str, 0 <= cstring_len str <= Zlength str.
Proof.
  induction str.
  + unfold Zlength; simpl; omega.
  + destruct (eq_dec a (Int.repr 0)).
    - rewrite e, Zlength_cons; simpl; omega.
    - rewrite cstring_len_nz_prefix, Zlength_cons by auto.
      omega.
Qed.

Lemma cstring_len_bounds:
  forall str,
  is_cstring str -> 0 <= cstring_len str < Zlength str.
Proof.
  intros str str_is_cstring.
  induction str_is_cstring.
  {
    simpl cstring_len; rewrite Zlength_single_elem; omega.
  }
  {
    destruct (eq_dec c (Int.repr 0)).
    + rewrite e, Zlength_cons; simpl cstring_len.
      assert (0 < Zlength s) as Zlength_bound by omega.
      omega.
    + rewrite cstring_len_nz_prefix, Zlength_cons; auto; omega.
  }
  {
    rewrite Zlength_app, Zlength_single_elem.
    destruct (eq_dec (cstring_len s) (cstring_len (s ++ [c]))).
    + rewrite <-e; omega.
    + cut (cstring_len s = Zlength s).
      - omega.
      - apply cstring_len_aux_suffix_lemma with (c := c).
        auto.
  }
Qed.

Lemma cstring_len_suffix:
  forall str c,
  is_cstring str ->
  cstring_len str = cstring_len (str ++ [c]).
Proof.
  intros str c str_is_cstring.
  destruct (eq_dec (cstring_len str) (cstring_len (str ++ [c]))).
  + rewrite e; auto.
  + assert (cstring_len str = Zlength str) as Habs1 by
      (apply cstring_len_aux_suffix_lemma with (c := c); auto).
    assert (0 <= cstring_len str < Zlength str) as Habs2 by
      (apply cstring_len_bounds; auto).
    omega.
Qed.

Lemma cstring_content_non_null:
  forall str,
  is_cstring str ->
  forall j d,
  0 <= j < cstring_len str ->
  Znth j str d <> Int.repr 0.
Proof.
  intros str str_is_cstring.
  induction str_is_cstring.
  + intros; unfold Zlength in *; simpl in *; omega.
  + intros j d j_bounds.
    destruct (eq_dec c (Int.repr 0)).
    - rewrite e in *; simpl in *; omega.
    - destruct (eq_dec j 0).
      * rewrite e, Znth_zero; auto.
      * rewrite cstring_len_nz_prefix in j_bounds by auto.
        assert (j = j - 1 + 1) as j_eq by omega.
        rewrite j_eq, Znth_plus_one by omega.
        apply IHstr_is_cstring; omega.
  + assert (cstring_len s < Zlength s) by (apply cstring_len_bounds; auto).
    destruct (eq_dec (cstring_len s) (cstring_len (s ++ [c]))).
    - rewrite <-e; intros j d j_bounds.
      rewrite Znth_app_1st by omega.
      apply IHstr_is_cstring; omega.
    - assert (cstring_len s = Zlength s) by
        (apply cstring_len_aux_suffix_lemma with (c := c); auto).
      intros; omega.
Qed.

Lemma cstring_ending_is_null:
  forall str d,
  is_cstring str ->
  Znth (cstring_len str) str d = Int.repr 0.
Proof.
  intros str d str_is_cstring.
  induction str_is_cstring.
  {
    apply Znth_zero.
  }
  {
    destruct (eq_dec c (Int.repr 0)).
    + rewrite e; apply Znth_zero.
    + rewrite cstring_len_nz_prefix by auto.
      rewrite Znth_plus_one by apply cstring_len_ge_0.
      auto.
  }
  {
    rewrite <-cstring_len_suffix, Znth_app_1st; auto.
    apply cstring_len_bounds; auto.
  }
Qed.

Lemma typecast_aux_lemma:
  forall i str,
  make_arr_fun (map Vint str) i =
  Vint (nth (Z.to_nat i) str (Int.repr 1)).
Proof.
  intros i str.
  unfold make_arr_fun, Znth; rewrite map_nth; simpl; auto.
Qed.

Lemma char_value_lemma:
  forall str c,
  is_cstring str ->  
  Vint (Int.sign_ext 8 (Znth 0 str (Int.repr 1))) = Vint c ->
  Int.sign_ext 8 (Int.repr (Int.signed (Znth 0 str (Int.repr 0)))) = c.
Proof.
  intros str c str_is_cstring vint_eq.
  cut (c = Int.sign_ext 8 (Znth 0 str (Int.repr 0))).
  {
    intros c_eq.
    rewrite Int.repr_signed, <-c_eq; auto.
  }
  {
    rewrite Znth_matches with (d2 := (Int.repr 1)).
    + inversion vint_eq; auto.
    + cut (Zlength str > 0).
      - omega.
      - apply cstring_Zlength_gt_zero; auto.
  }
Qed.

Lemma cstring_in_lemma:
  forall str i d,
  -128 <= Int.signed d < 128 ->
  0 <= i <= cstring_len str ->
  is_cstring str ->
  negb (Int.eq
         (Int.sign_ext 8
           (Int.repr (Int.signed (Znth i str d))))
         (Int.repr 0)) = true ->
  i < cstring_len str.
Proof.
  intros str i d d_bounds i_bounds str_is_cstring.
  remember (Znth i str d) as c.
  assert (-128 <= Int.signed c < 128) as c_bounds.
  {
    rewrite Heqc.
    apply cstring_has_bounded_chars; auto.
  }
  rewrite char_sign_ext_zero_comp; auto.
  + destruct (eq_dec c (Int.repr 0)).
    - rewrite e; simpl; discriminate.
    - destruct (eq_dec i (cstring_len str)).
      * rewrite e, cstring_ending_is_null in Heqc by auto.
        rewrite Heqc; simpl; discriminate.
      * intros _; omega.
Qed.

Lemma cstring_end_lemma:
  forall str i d,
  -128 <= Int.signed d < 128 ->
  0 <= i <= cstring_len str ->
  is_cstring str ->
  negb (Int.eq
         (Int.sign_ext 8
           (Int.repr (Int.signed (Znth i str d))))
         (Int.repr 0)) = false ->
  cstring_len str = i.
Proof.
  intros str i d d_bounds i_bounds str_is_cstring.
  remember (Znth i str d) as c.
  assert (-128 <= Int.signed c < 128) as c_bounds.
  {
    rewrite Heqc.
    apply cstring_has_bounded_chars; auto.
  }
  rewrite char_sign_ext_zero_comp; auto.
  + destruct (eq_dec i (cstring_len str)).
    - rewrite Heqc, e, cstring_ending_is_null by auto; simpl; auto.
    - destruct (eq_dec c (Int.repr 0)).
      * absurd (c = Int.repr 0); auto.
        rewrite Heqc.
        apply cstring_content_non_null; auto; omega.
      * rewrite <-Int.repr_signed with (i := c) in n0.
        cut ((Int.signed c =? 0) = false).
        intros c_ne_0_bool; rewrite c_ne_0_bool; simpl; discriminate.
        apply Z.eqb_neq.
        intros Habs.
        apply n0, f_equal; auto.
Qed.
        
Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list int, sh: share, s: val
    PRE [ _s OF tptr tschar ]
      PROP (is_cstring str;
           (Zlength str) <= Int.max_signed)
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
    apply exp_right with (Int.signed (Znth 0 str (Int.repr 0))).
    entailer!.
    + intros x Hge Hlt; exfalso; omega.
    + rewrite typecast_aux_lemma in H1; simpl in *.
      apply char_value_lemma; auto.
  }
  {
    entailer!.
  }
  {
    entailer!.
    + apply f_equal.
      apply cstring_end_lemma with (d := Int.repr 0); auto.
      apply char_bound; omega.
  }
  {
    forward.
    forward.
    {
      entailer!.
      + cut (i < cstring_len str < Zlength str).
        omega.
        split.
        - apply cstring_in_lemma with (d := Int.repr 0); auto; apply char_bound; omega.
        - apply cstring_len_bounds; auto.
      + rewrite typecast_aux_lemma; simpl; auto.
    }
    {
      apply exp_right with (i + 1).
      apply exp_right with (Int.signed (Znth (i + 1) str (Int.repr 0))).
      entailer!.
      + intros j j_lo_bound j_hi_bound.
        assert (i < cstring_len str) as i_hi_bound.
        apply cstring_in_lemma with (d := Int.repr 0); auto; apply char_bound; omega.
        apply cstring_content_non_null; auto; omega.
      + assert (i < cstring_len str) as i_hi_bound.
        apply cstring_in_lemma with (d := Int.repr 0); auto; apply char_bound; omega.
        omega.
      + rewrite typecast_aux_lemma in H4; simpl in H4.
        inversion H4; simpl.
        assert (nth (Z.to_nat (i + 1)) str (Int.repr 1) =
                Znth (i + 1) str (Int.repr 1)) as Znth_eq by
          (unfold Znth; auto).
        assert (Int.min_signed < 0) by apply Int.min_signed_neg.
        assert (0 <= cstring_len str < Zlength str) by
          (apply cstring_len_bounds; auto).
        assert (i < cstring_len str) as i_hi_bound by
          (apply cstring_in_lemma with (d := Int.repr 0); auto; apply char_bound; omega).
        rewrite Int.add_signed.
        repeat rewrite Int.signed_repr; try omega.
        repeat rewrite Int.repr_signed; try omega.
        rewrite Znth_eq, Znth_matches 
          with (d1 := Int.repr 0) (d2 := Int.repr 1); auto; omega.
    }
  }
  forward.
Qed.