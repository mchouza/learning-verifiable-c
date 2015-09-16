Require Import List.
Require Import Omega.

Lemma app_hd {A}:
  forall (l1 l2:list A) d,
  l1 <> nil -> hd d (l1 ++ l2) = hd d l1.
Proof.
  intros l1 l2 d l1_non_nil; destruct l1.
  + exfalso; apply l1_non_nil; auto.
  + rewrite <-app_comm_cons; simpl; auto.
Qed.

Lemma app_last {A}:
  forall (l1 l2:list A) d,
  l2 <> nil -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros l1 l2 d l2_non_nil; induction l1.
  + auto.
  + cut (length (l1 ++ l2) > 0).
    {
      rewrite <-app_comm_cons; simpl; destruct (l1 ++ l2).
      + simpl; intros; omega.
      + rewrite IHl1; auto.
    }
    cut (length l2 > 0).
    {
      intros; rewrite app_length; omega.
    }
    destruct l2.
    - exfalso; apply l2_non_nil; auto.
    - simpl; omega.
Qed.

Lemma app_firstn {A}:
  forall n (l1 l2:list A),
  n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  induction n.
  + auto.
  + destruct l1.
    - simpl in *; intros; omega.
    - intros; rewrite <-app_comm_cons; simpl in *; rewrite IHn by omega; auto.
Qed.

Lemma app_firstn' {A}:
  forall n (l1 l2:list A),
  length l1 <= n -> firstn n (l1 ++ l2) = l1 ++ (firstn (n - length l1) l2).
Proof.
  induction n.
  + destruct l1; simpl; auto; intros; omega.
  + destruct l1.
    - simpl; auto.
    - intros; simpl in *; rewrite IHn; auto; omega.
Qed.

Lemma app_skipn {A}:
  forall n (l1 l2:list A),
  n <= length l1 -> skipn n (l1 ++ l2) = (skipn n l1) ++ l2.
Proof.
  induction n.
  + auto.
  + destruct l1.
    - simpl in *; intros; omega.
    - intros; rewrite <-app_comm_cons; simpl in *; rewrite IHn by omega; auto.
Qed.

Lemma app_skipn' {A}:
  forall n (l1 l2:list A),
  length l1 <= n -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof.
  induction n.
  + destruct l1; auto; simpl; intros; omega.
  + destruct l1.
    - intros; simpl app; simpl length; rewrite <-minus_n_O; auto.
    - simpl; intros; rewrite IHn; auto; omega.
Qed.

Lemma firstn_whole {A}:
  forall n (l:list A),
  length l <= n -> firstn n l = l.
Proof.
  induction n.
  + destruct l; auto; simpl; intros; omega.
  + destruct l.
    - auto.
    - simpl; intros; rewrite IHn by omega; auto.
Qed.

Lemma hd_skip1_cons {A}:
  forall (l:list A) d,
  l <> nil -> (hd d l) :: (skipn 1 l) = l.
Proof.
  intros; destruct l.
  + exfalso; apply H; auto.
  + simpl; auto.
Qed.

Lemma removelast_length {A}:
  forall (l:list A),
  l <> nil -> S (length (removelast l)) = length l.
Proof.
  induction l.
  + intros Habs; exfalso; apply Habs; auto.
  + destruct l as [|b l].
    - intros; simpl; auto.
    - intros; simpl in *; apply f_equal, IHl; discriminate.
Qed.

Lemma skipn_length {A}:
  forall (l:list A) n,
  length (skipn n l) = length l - n.
Proof.
  induction l.
  + intros; case n; auto.
  + destruct n.
    - auto.
    - intros; simpl in *; apply IHl; omega.
Qed.

Inductive paren :=
  | open
  | close.

Inductive wp: list paren -> Prop :=
  | wp_e: wp nil
  | wp_p: forall l, wp l -> wp (open :: l ++ close :: nil)
  | wp_c: forall l1 l2, wp l1 -> wp l2 -> wp (l1 ++ l2).

Fixpoint is_wp_aux (l:list paren) (n:nat) :=
  match l, n with
  | nil, 0 => true
  | open :: t, k => is_wp_aux t (S k)
  | close :: t, S k => is_wp_aux t k
  | _, _ => false
  end.

Definition is_wp l := is_wp_aux l 0.

Lemma wp_implies_no_change: 
  forall l1 l2 n, wp l1 -> is_wp_aux (l1 ++ l2) n = is_wp_aux l2 n.
Proof.
  intros l1 l2 n wp_l1.
  generalize l2, n; clear l2 n.
  induction wp_l1.
  + simpl; auto.
  + intros; simpl; rewrite <-app_assoc, IHwp_l1; simpl; auto.
  + intros; rewrite <-app_assoc, IHwp_l1_1, IHwp_l1_2; auto.
Qed.
    
Lemma wp_implies_is_wp: forall l, wp l -> is_wp l = true.
Proof.
  intros; unfold is_wp; rewrite <-app_nil_r with (l := l).
  rewrite wp_implies_no_change by auto; auto.
Qed.

Fixpoint rep_open (n:nat) :=
  match n with
  | 0 => nil
  | S k => open :: (rep_open k)
  end.

Lemma rep_open_split_last:
  forall n l, rep_open n ++ open :: l = rep_open (S n) ++ l.
Proof.
  intros; induction n.
  + simpl; auto.
  + simpl rep_open in *; repeat rewrite <-app_comm_cons; rewrite IHn.
    repeat rewrite <-app_comm_cons; auto.
Qed.

Lemma wp_non_nil_starts_open:
  forall l d, wp l -> l <> nil -> hd d l = open.
Proof.
  intros l d wp_l l_non_nil.
  induction wp_l.
  + exfalso; apply l_non_nil; auto.
  + simpl; auto.
  + destruct l1, l2.
    - simpl in l_non_nil; exfalso; apply l_non_nil; auto.
    - simpl; apply IHwp_l2; discriminate.
    - simpl; apply IHwp_l1; discriminate.
    - simpl; apply IHwp_l1; discriminate.
Qed.

Lemma wp_non_nil_ends_close:
  forall l d, wp l -> l <> nil -> last l d = close.
Proof.
  intros l d wp_l l_non_nil.
  induction wp_l.
  + exfalso; apply l_non_nil; auto.
  + rewrite app_comm_cons, app_last.
    - auto.
    - discriminate.
  + destruct l1, l2.
    - simpl in *; exfalso; apply l_non_nil; auto.
    - rewrite app_nil_l, IHwp_l2; auto.
    - rewrite app_nil_r, IHwp_l1; auto; discriminate.
    - rewrite app_last.
      * rewrite IHwp_l2; auto; discriminate.
      * discriminate.
Qed.

Lemma open_close_ins_keeps_wp:
  forall l l', wp (l ++ l') -> wp (l ++ open :: close :: nil ++ l').
Proof.
  (* useful general assertion *)
  assert (wp (open :: close :: nil)) as wp_oc.
  {
    assert (open :: close :: nil = (open :: nil) ++ (close :: nil)) as oc_eq by (simpl; auto).
    rewrite oc_eq; apply wp_p, wp_e.
  }
  (* we do length induction *)
  cut (forall n l l', length (l ++ l') <= n -> wp (l ++ l') -> wp (l ++ open :: close :: nil ++ l')).
  {
    intros H l l'; apply H with (n := length (l ++ l')); omega.
  }
  induction n.
  {
    (* trivial length 0 case *)
    destruct l, l'; simpl; intros; try omega.
    apply wp_oc.
  }
  {
    (* now we do induction in the wp cases *)
    intros l l' ll'_length_bounds wp_ll'.
    remember (l ++ l') as ll'.
    induction wp_ll'.
    {
      (* nil case is trivial *)
      assert (l = nil /\ l' = nil) as [l_is_nil l'_is_nil] by (apply app_eq_nil; auto).
      rewrite l_is_nil, l'_is_nil; simpl; apply wp_oc.
    }
    {
      (* the parenthesized one, not so much: we need to start by disposing of the easy cases first *)
      destruct l, l'.
      + simpl; apply wp_oc.
      + assert (nil ++ open :: close :: nil ++ p :: l' = (open :: close :: nil) ++ p :: l') as Heq by auto.
        rewrite Heq; apply wp_c.
        - apply wp_oc.
        - rewrite <-app_nil_l, <-Heqll'; apply wp_p; auto.
      + assert ((p :: l) ++ open :: close :: nil ++ nil = (p :: l) ++ (open :: close :: nil)) as Heq by auto.
        rewrite Heq; apply wp_c.
        - rewrite <-app_nil_r, <-Heqll'; apply wp_p; auto.
        - apply wp_oc.
      (* now that we are in the main case, we start by showing the expression follows the
         open :: x ++ close :: nil shape *)
      + assert (p = open) as p_is_open.
        {
          assert (p = hd close ((p :: l) ++ p0 :: l')) as p_eq by auto.
          assert (open = hd close (open :: l0 ++ close :: nil)) as open_eq by auto.
          rewrite p_eq, open_eq, Heqll'; auto.
        }
        assert (last (p0 :: l') open = close) as last_is_close.
        {
          assert (last (p0 :: l') open = last ((p :: l) ++ p0 :: l') open) as last_eq
            by (rewrite app_last by discriminate; auto).
          assert (close = last (open :: l0 ++ close :: nil) open) as close_eq 
            by (rewrite app_comm_cons, app_last by discriminate; auto).
          rewrite last_eq, close_eq, Heqll'; auto.
        }
        rewrite p_is_open, app_removelast_last with (d := open) (l := p0 :: l'), last_is_close
          by discriminate.
        assert ((open :: l) ++ open :: close :: nil ++ removelast (p0 :: l') ++ close :: nil =
                open :: (l ++ open :: close :: nil ++ removelast (p0 :: l')) ++ close :: nil) as Heq.
        repeat (repeat rewrite app_assoc; repeat rewrite app_comm_cons); auto.
        (* now we can apply the usual machinery to shrink the string and call the inductive hypothesis *)
        rewrite Heq; apply wp_p, IHn.
        (* we have to prove the shrinking *)
        - assert (S(length(removelast (p0 :: l'))) = S(length l')) as removelast_len_eq
            by (rewrite removelast_length; try discriminate; auto).
          rewrite Heqll', app_length in ll'_length_bounds; simpl in ll'_length_bounds.
          rewrite app_length; omega.
        (* then we have to prove everything is well founded *)
        - assert (l0 = l ++ removelast (p0 :: l')) as l0_eq.
          {
            apply app_inv_head with (l := open :: nil); simpl app at 1.
            apply app_inv_tail with (l := close :: nil).
            rewrite <-app_comm_cons, Heqll', <-p_is_open, <-last_is_close.
            repeat rewrite <-app_assoc; rewrite <-app_removelast_last by discriminate.
            simpl; auto.
          }
          rewrite <-l0_eq; auto.
    }
    {
      (* the concatenation case *)
      (* we need to dispose of the easy cases *)
      destruct l1, l2.
      + apply IHwp_ll'1; auto; rewrite <-Heqll'.
      + apply IHwp_ll'2; auto; rewrite <-Heqll'.
      + apply IHwp_ll'1; rewrite app_nil_r in *; try omega; rewrite <-Heqll'; auto.
      (* this is the main case *)
      (* we need to handle the two cases, depending on where the added open :: close falls *)
      + destruct (le_dec (length (p :: l1)) (length l)).
        (* the easiest one: the open :: close is entirely beyond the first component *)
        - rewrite <-firstn_skipn with (n := length (p :: l1)).
          rewrite app_firstn, app_skipn by auto.
          assert (firstn (length (p :: l1)) l = p :: l1) as l1_eq.
          {
            erewrite <-app_firstn by auto; instantiate (1 := l').
            rewrite <-Heqll', app_firstn, firstn_whole by auto; auto.
          }
          assert (skipn (length (p :: l1)) l ++ l' = p0 :: l2) as l2_eq.
          {
            apply app_inv_head with (l := p :: l1).
            rewrite <-l1_eq, app_assoc, firstn_skipn, Heqll' at 1; auto.
          }
          rewrite l1_eq; apply wp_c, IHn; auto.
          * rewrite app_length, skipn_length.
            rewrite Heqll', app_length in ll'_length_bounds.
            assert (length (p :: l1) > 0) by (simpl; omega).
            omega.
          * rewrite l2_eq; auto.
        (* the open :: close falls in the middle or on the first component entirely *)
        - rewrite <-firstn_skipn with (n := length (p :: l1) + 2).
          rewrite app_firstn', app_skipn' by omega.
          assert (length (p :: l1) + 2 - length l - 2 = length (p :: l1) - length l) as len_eq by omega.
          assert (skipn (length (p :: l1) + 2 - length l) (open :: close :: nil ++ l') = p0 :: l2) as l2_eq.
          {
            do 2 rewrite app_comm_cons; rewrite app_skipn' by (simpl length at 1; omega); simpl length at 3.  
            rewrite len_eq, <-app_skipn' by omega.
            apply app_inv_head with (l := p :: l1).
            rewrite <-Heqll', app_skipn', <-minus_n_n by auto; auto.
          }
          assert (l ++ firstn (length (p :: l1) - length l) l' = p :: l1) as l1_eq
            by (rewrite <-app_firstn', <-Heqll', app_firstn, firstn_whole by omega; auto).
          rewrite l2_eq; apply wp_c; auto.
          do 2 rewrite app_comm_cons; rewrite app_firstn' by (simpl length at 1; omega); simpl length at 3.
          rewrite len_eq.
          apply IHn; rewrite <-app_firstn', <-Heqll', app_firstn, firstn_whole by omega.
          * rewrite app_length in ll'_length_bounds; simpl in *; omega.
          * auto.
    }
  }
Qed.    

Lemma is_wp_implies_wp_aux:
  forall l n, is_wp_aux l n = true -> wp ((rep_open n) ++ l).
Proof.
  induction l.
  {
    simpl; intros; destruct n.
    + simpl; apply wp_e.
    + discriminate.
  }
  {
    intros; destruct a.
    + rewrite rep_open_split_last; apply IHl; simpl in *; auto.
    + destruct n.
      - simpl in *; discriminate.
      - assert (rep_open (S n) ++ close :: l = rep_open n ++ open :: close :: nil ++ l) as Heq
          by (rewrite <-rep_open_split_last; simpl; auto).
        rewrite Heq.
        apply open_close_ins_keeps_wp, IHl; simpl in *; auto.
  }
Qed.

Lemma is_wp_implies_wp: forall l, is_wp l = true -> wp l.
Proof.
  unfold is_wp; intros.
  assert (nil = rep_open 0) as rep_open_0_is_nil by auto.
  rewrite <-app_nil_l, rep_open_0_is_nil.
  apply is_wp_implies_wp_aux; auto.
Qed.

Lemma is_wp_works:
  forall l, is_wp l = true <-> wp l.
Proof.
  split.
  + apply is_wp_implies_wp.
  + apply wp_implies_is_wp.
Qed.