Require Import List.
Require Import Omega.

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

Lemma open_close_keeps_wp:
  forall l n, wp ((rep_open n) ++ l) -> wp ((rep_open (S n)) ++ close :: l).
Proof.
  assert (forall (p:paren) l, p :: nil ++ l = p :: l) as cons_eq by auto.
  assert (wp (open :: close :: nil)) as wp_open_close by
    (rewrite <-cons_eq; apply wp_p, wp_e).
  cut (forall m l n,
       length l <= m ->
       wp (rep_open n ++ l) ->
       wp (rep_open (S n) ++ close :: l)).
  {
    intros H l n; apply H with (m := length l); omega.
  }
  induction m.
  {
    destruct l, n; simpl; intros; try omega.
    + apply wp_open_close.
    + rewrite app_comm_cons; apply wp_p; rewrite <-app_nil_r; auto.
  }
  {
    destruct l, n; simpl; intros.
    + apply wp_open_close.
    + rewrite app_comm_cons; apply wp_p; rewrite <-app_nil_r; auto.
    + rewrite <-cons_eq with (p := open).
      rewrite <-cons_eq with (p := close).
      do 2 rewrite app_comm_cons; rewrite app_assoc, <-app_comm_cons, cons_eq.
      apply wp_c.
      - apply wp_open_close.
      - auto.
    + admit. (** FIXME **)
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
      - simpl in *; apply open_close_keeps_wp, IHl; auto.
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