Require Import List.
Require Import Omega.

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