Add Rec LoadPath "../verifiable-c/vst".
Add LoadPath "../verifiable-c/compcert" as compcert.

Require Import floyd.proofauto.

Require Import strlen.

Local Open Scope logic.

Definition Znth {A} i l def := nth (A := A) (Z.to_nat i) l def.

Definition make_arr_fun l := fun i => Znth i l (Vint (Int.repr 1)).

Inductive is_cstring: list int -> Prop :=
| cs_empty: is_cstring (Int.repr 0 :: nil)
| cs_prepend: 
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (c :: s)
| cs_append:
    forall c s, -128 <= Int.signed c < 128 -> is_cstring s ->
    is_cstring (s ++ (c :: nil)).

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

Lemma char_eq:
  forall a b,
  -128 <= a < 128 -> -128 <= b < 128 ->
  Int.repr a = Int.repr b ->
  a = b.
Proof.
  assert (forall a, -128 <= a < 128 ->
          Int.min_signed <= a <= Int.max_signed) as Hbound_gen.
  { 
    intros a' H.
    unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus,
           Int.wordsize, Wordsize_32.wordsize in *.
    simpl; omega.
  }
  intros a b Hbound_a Hbound_b Heq_repr.
  rewrite <-Int.signed_repr with (z := a), <-Int.signed_repr with (z := b);
  try rewrite Heq_repr; auto.
Qed.  

Lemma char_zero_comp:
  forall a, -128 <= a < 128 -> a <> 0 -> Int.repr a <> Int.repr 0.
Proof.
  intros a Hbound_a Habs Habs_repr.
  apply Habs, char_eq; auto; omega.
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

Lemma cstring_len_upper_bound:
  forall str, exists i,
  (nth i str (Int.repr 1)) = Int.repr 0 ->
  cstring_len str <= Z.of_nat (S i).
Proof.
  induction str.
  + exists O; intros _; simpl; omega.
  + rewrite <-Int.repr_signed with (i := a).
    destruct (eq_dec (Int.signed a) 0) as [Heq | Hne].
    - exists O; rewrite Heq; intros _; simpl; omega.
    - destruct IHstr as [i IHstr]; exists (S i).
      rewrite cstring_len_nz_prefix; simpl nth.
      intros Hhas_null.
      cut (cstring_len str <= Z.of_nat (S i)).
      admit. (** FIXME **)
      apply IHstr; auto.
      admit. (** FIXME **)
Qed.      

Lemma aux_str_len_succ_lemma:
  forall str,
  Z.to_nat (cstring_len str + 1) = S (Z.to_nat (cstring_len str)).
Proof.
  intros str.
  rewrite Z2Nat.inj_add; simpl; try omega.
  cut (cstring_len str >= 0); try omega; apply cstring_len_ge_0.
Qed.

Lemma cstring_char_values:
  forall str j,
  is_cstring str ->
  (Znth (cstring_len str) str (Int.repr 1)) = Int.repr 0 /\
  (0 <= j < (cstring_len str) ->
  (Znth j str (Int.repr 1)) <> Int.repr 0).
Proof.
  (* strong induction over the number of bytes *)
  cut (forall n str j,
       (length str < n)%nat ->
       is_cstring str ->
       (Znth (cstring_len str) str (Int.repr 1)) = Int.repr 0 /\
       (0 <= j < (cstring_len str) ->
       (Znth j str (Int.repr 1)) <> Int.repr 0)).
  intros Hgen str j; apply Hgen with (n := S (length str)); omega.
  unfold Znth; induction n.
  (* trivial base case *)
  + intros str j Habs; exfalso; omega.
  (* main case, uses induction over C string definition *)
  + intros str j Hxlen Hxcstr; induction Hxcstr.
    (* empty C strings are easy *)
    - split; simpl; try intros; auto; omega.
    (* for prefixes we need to check if the first char is null *)
    - rewrite <-Int.repr_signed with (i := c).
      destruct (eq_dec (Int.signed c) 0).
      {
        (* a null prefix is easy to handle *)
        rewrite e; split; simpl; auto; omega.
      }
      {
        (* a non-null prefix just moves everything *)
        rewrite cstring_len_nz_prefix, aux_str_len_succ_lemma; simpl.
        (* TODO: ADD MORE COMMENTS *)
        + split.
          - simpl in *; apply IHn; auto; omega.
          - intros Hbound_j.
            assert (j = Z.of_nat (Z.to_nat j)) as H_j_repr.
            symmetry; apply nat_of_Z_eq; omega.
            destruct (Z.to_nat j).
            * apply char_zero_comp; try discriminate; omega.
            * rewrite <-nat_of_Z_of_nat with (n := n1).
              unfold nat_of_Z; simpl in *.
              rewrite Zpos_P_of_succ_nat in H_j_repr.
              apply IHn; simpl in *; auto; omega.
        + apply char_zero_comp; try discriminate; omega.
      }
    (* for suffixes we just have show the old values are OK *)
    - admit. (** FIXME **)
Qed.

Lemma cstring_len_bounds:
  forall str,
  is_cstring str -> 0 <= cstring_len str < Zlength str.
Proof.
Admitted. (** FIXME **)

Lemma typecast_aux_lemma:
  forall i str,
  make_arr_fun (map Vint str) i =
  Vint (nth (Z.to_nat i) str (Int.repr 1)).
Proof.
  intros i str.
  unfold make_arr_fun, Znth; rewrite map_nth; simpl; auto.
Qed.

Definition my_strlen_spec :=
  DECLARE _my_strlen
    WITH str: list int, sh: share, s: val
    PRE [ _s OF tptr tschar ]
      PROP (is_cstring str;
            (cstring_len str) < Int.max_signed)
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
    apply exp_right with (Int.signed (nth 0 str (Int.repr 0))).
    entailer!.
    + intros x Hge Hlt; exfalso; omega.
    + admit. (** FIXME **)
  }
  {
    entailer!.
  }
  {
    entailer!.
    + admit. (** FIXME **)
  }
  {
    forward.
    forward.
    {
      entailer!.
      + admit. (** FIXME **)
      + rewrite typecast_aux_lemma; simpl; auto.
    }
    {
      apply exp_right with (i + 1).
      apply exp_right with (Int.signed (Znth (i + 1) str (Int.repr 0))).
      entailer!.
      + admit. (** FIXME **)
      + admit. (** FIXME **)
      + rewrite typecast_aux_lemma in H4; simpl in H4.
        inversion H4; simpl.
        admit. (** FIXME **)
    }
  }
  forward.
Qed.