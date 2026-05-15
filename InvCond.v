(* From Hammer Require Import Hammer Reconstr. *)
From BV Require Import BVList Reconstr.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.



(*------------------------------Neg------------------------------*)


(* -x = t <=> True *)

Theorem bvneg_eq : forall (n : N), forall (t : bitvector),
  (size t) = n -> iff 
    True 
    (exists (x : bitvector), size x = n /\ bv_neg x = t).
Proof.
  intros n t Ht. split.
  + intros H. exists (bv_neg t). split.
    - apply bv_neg_size. apply Ht.
    - apply bv_neg_involutive. 
  + easy.
Qed.


(*------------------------------------------------------------*)


(*------------------------------Not------------------------------*)


(* ~x = t <=> True *)
Theorem bvnot_eq : forall (n : N), forall (t : bitvector),
 (size t) = n -> iff
    True
    (exists (x : bitvector), size x = n /\ bv_not x = t).
Proof.
  intros n t Ht. split; intros H.
  + exists (bv_not t). split.
    - apply bv_not_size. apply Ht.
    - apply bv_not_involutive.
  + easy.
Qed.


(*------------------------------------------------------------*)


(*------------------------------And------------------------------*)


(* t & s = t <=> (exists x, x & s = t) *)
Theorem bvand_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    ((bv_and t s) = t)
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - exists t. split. 
         + apply Ht.
         + apply A.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_and_comm n x s Hx Hs), (@bv_and_idem1 s x n Hs Hx).
Qed.


(* ~(-t) & s <s t <=> (exists x, x & s <s t) *)
Theorem bvand_slt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt (bv_and (bv_not (bv_neg t)) s) t) = true) 
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_and x s) t) = true)).
Proof.
  intros n s t Hs Ht. split.
  - intro H_cond. exists (bv_not (bv_neg t)). split.
        + rewrite (@bv_not_size n).
          * easy.
          * apply bv_neg_size. easy.
        + assumption.
  - intro H_exists. destruct H_exists as [x [Hx_size Hx_lt]].
    assert (H_x_and_s_size: size (bv_and x s) = n). 
    { apply (bv_and_size Hx_size Hs). }
    assert (H_not_min: t <> signed_min n). 
    { apply (not_signed_min_if_gt H_x_and_s_size Ht Hx_lt). }
    assert (H_size: size (bv_not (bv_neg t)) = n). 
    { apply bv_not_size, bv_neg_size; easy. }
    destruct (bv_slt s (zeros n)) eqn:H_sign.
    + assert (H_t_minus_1_lt : bv_slt (bv_not (bv_neg t)) t = true).
      { apply (bv_not_neg_slt Ht H_not_min). }
      assert (H_le : bv_sle (bv_and (bv_not (bv_neg t)) s) (bv_not (bv_neg t)) = true).
      { apply (bv_and_neg_sle_itself H_size Hs H_sign). }
      apply (bv_sle_slt_trans H_le H_t_minus_1_lt).
    + rewrite (bv_slt_negb_sle Hs (zeros_size n)) in H_sign. 
      apply negb_false_iff in H_sign. rewrite <- Hs in H_sign.
      rewrite bv_zeros_sle in H_sign. apply negb_true_iff in H_sign.
      assert (H_xs_pos : last (bv_and x s) false = false). 
      { apply (pos_bv_and Hx_size Hs H_sign). }
      destruct (bv_slt t (zeros n)) eqn:H_t_sign.
      * rewrite <- Ht in H_t_sign. rewrite bv_slt_zeros in H_t_sign. 
        assert (H_size_match : size t = size (bv_and x s)).
        { rewrite H_x_and_s_size; assumption. }
        pose proof (bv_slt_tf H_size_match H_t_sign H_xs_pos) as H_contra.
        pose proof (bv_slt_trans H_contra Hx_lt) as H_impossible.
        rewrite bv_slt_nrefl in H_impossible. discriminate.
      * rewrite (bv_slt_negb_sle Ht (zeros_size n)) in H_t_sign. 
        apply negb_false_iff in H_t_sign. apply bv_sle_eq in H_t_sign.
        destruct H_t_sign as [H_t_pos | H_t_eq_0].
        ** apply bv_sle_slt_trans with (b2 := bv_not (bv_neg t)).
           { assert (H_t_minus_1_pos : last (bv_not (bv_neg t)) false = false).
             { apply (bv_not_neg_pos_if_gt_zero Ht H_not_min H_t_pos). }
             apply (bv_and_pos_sle_1 H_size Hs H_t_minus_1_pos H_sign). }
           rewrite (bv_slt_iff_sbv2int H_size).
           *** rewrite (bv_not_neg_is_subt_one Ht).
               rewrite (sbv2int_sub_one Ht).
               **** lia.
               **** assumption.
           *** assumption.
        ** rewrite <- H_t_eq_0 in *. rewrite <- H_x_and_s_size in Hx_lt.
           rewrite (bv_slt_zeros (bv_and x s)) in Hx_lt.
           rewrite H_xs_pos in Hx_lt. discriminate.
Qed.


Theorem bvand_sgt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
  (bv_slt t (bv_and s (signed_max n)) = true)
  (exists (x : bitvector), (size x  = n) /\ ((bv_sgt (bv_and x s) t) = true)).
Proof.
  intros n s t Hs Ht. split.
  + intros. exists (signed_max n). split.
    - apply signed_max_size.
    - rewrite (@bv_and_comm n (signed_max n) s).
      apply bv_slt_bv_sgt in H. apply H. apply signed_max_size. apply Hs.
  + intros (x, (Hx, H)).
    apply bv_sgt_bv_slt in H. rewrite (@bv_and_comm n x s) in H.
    apply (@bv_slt_sle_trans t (bv_and s x) (bv_and s (signed_max n))).
    apply H. apply (@bv_and_sle_maxs n s x Hs Hx).
    apply Hx. apply Hs.
Qed.


(* s >=u t & mins <=> (exists x, x & s <=s t) *)
Theorem bvand_sle : forall (n : N) (s t : bitvector),
  size s = n -> size t = n -> iff
  (bv_uge s (bv_and t (signed_min n)) = true)
  (exists x, size x = n /\ bv_sle (bv_and x s) t = true).
Proof.
  intros n s t Hs Ht.
  split; intro H.
  - exists (signed_min n). split.
    { apply signed_min_size. }
    rewrite (bv_and_comm (signed_min_size n) Hs).
    destruct (last (bits t) false) eqn:Hsign_t.
    + assert (Hmask: bv_and t (signed_min n) = signed_min n) by (apply bv_and_signed_min_neg; assumption).
      rewrite Hmask in H.
      destruct (N.eq_dec n 0) as [Hn0 | Hnpos].
      * subst n. apply bv_sle_size_zero.
        -- rewrite <- Hn0. apply bv_and_size; [reflexivity | apply signed_min_size].
        -- rewrite Ht. exact Hn0.
      * assert (Hn_gt_0: (0 < n)%N) by lia.
        assert (Hs_neg: last (bits s) false = true) by (eapply bv_uge_signed_min_implies_msb; eassumption).
        assert (Hmask_s: bv_and s (signed_min n) = signed_min n) by (apply bv_and_signed_min_neg; assumption).
        rewrite Hmask_s, <- Ht.
        apply signed_min_sle; assumption.
    + assert (Hmask: bv_and t (signed_min n) = zeros n) by (apply bv_and_signed_min_pos; assumption).
      rewrite Hmask in H.
      destruct (last (bits s) false) eqn:Hsign_s.
      * destruct (N.eq_dec n 0) as [Hn0 | Hnpos].
        { exfalso. exact (@size_zero_msb_absurd n s Hs Hn0 Hsign_s). }
        assert (Hmask_s: bv_and s (signed_min n) = signed_min n) by (apply bv_and_signed_min_neg; assumption).
        rewrite Hmask_s, <- Ht. apply signed_min_sle.
      * assert (Hmask_s: bv_and s (signed_min n) = zeros n) by (apply bv_and_signed_min_pos; assumption).
        rewrite Hmask_s. apply zeros_sle_nonneg; assumption.
  - destruct H as [x [Hx Hsle]].
    destruct (last (bits t) false) eqn:Hsign_t.
    + assert (Hmask: bv_and t (signed_min n) = signed_min n) by (apply bv_and_signed_min_neg; assumption).
      rewrite Hmask. destruct (last (bits s) false) eqn:Hs_case.
      * destruct (N.eq_dec n 0) as [Hn0 | Hnpos].
        { exfalso. exact (@size_zero_msb_absurd n s Hs Hn0 Hs_case). }
        apply bv_msb_implies_uge_signed_min; try assumption; lia.
      * exfalso. 
        exact (@bvand_sle_backward_absurd n s t x Hs Ht Hx Hs_case Hsign_t Hsle).
    + assert (Hmask: bv_and t (signed_min n) = zeros n) by (apply bv_and_signed_min_pos; assumption).
      rewrite Hmask. apply bv_uge_zeros; assumption.
Qed.


(* (s & t = t) v (t <s (t - s) & s) <=> (exists x, x & s >=s t) *)
Theorem bvand_sge : forall (n : N), forall (s t : bitvector),
    (size s) = n -> (size t) = n -> iff
      ((bv_and s t) = t \/ (bv_slt t (bv_and (bv_subt t s) s) = true))
      (exists (x : bitvector), (size x = n) /\
          ((bv_sge (bv_and x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  split.
  - intros [Hst | Hslt].
    + (* bv_and s t = t: witness x = t *)
      exists t. split; [exact Ht |].
      rewrite bv_sge_sle_equiv.
      rewrite (bv_and_comm Ht Hs).
      rewrite Hst.
      apply bv_sle_refl.
    + (* bv_slt t (bv_and (bv_subt t s) s): witness x = bv_subt t s *)
      exists (bv_subt t s). split; [apply bv_subt_size; [exact Ht | exact Hs] |].
      rewrite bv_sge_sle_equiv.
      apply bv_sle_eq. left. exact Hslt.
  - intros [x [Hx Hxs]].
    rewrite bv_sge_sle_equiv in Hxs.
    apply bv_sle_eq in Hxs.
    destruct Hxs as [Hslt | Heq].
    + (* bv_slt t (bv_and x s): use bvand_sge_key *)
      apply (@bvand_sge_key n s t x Hs Ht Hx Hslt).
    + (* t = bv_and x s: bv_and s t = t *)
      left. rewrite Heq.
      rewrite (bv_and_comm Hs (bv_and_size Hx Hs)).
      exact (@bv_and_idem2 x s n Hx Hs).
Qed.


(*------------------------------------------------------------*)


(*------------------------------Or------------------------------*)


(* t & s = t <=> (exists x, x | s = t) *)
Theorem bvor_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    ((bv_or t s) = t)
    (exists (x : bitvector), (size x = n) /\ (bv_or x s) = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - exists t. split; easy.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_or_idem2 x s n Hx Hs).
Qed.


(* ~(s - t) | s <s t <=> (exists x, x | s <s t) *)
Theorem bvor_slt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt (bv_or (bv_not (bv_subt s t)) s) t) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_or x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  split.
  - intro H.
    exists (bv_not (bv_subt s t)).
    split.
    + apply bv_not_size. apply bv_subt_size; assumption.
    + exact H.
  - intro H.
    destruct H as [x [Hx_size H_slt]].
    exact (bvor_slt_key Hs Ht Hx_size H_slt).
Qed.


(* t <s s | smax <=> (exists x, x | s >s t) *)
Theorem bvor_sgt : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_sgt (bv_or x s) t = true)) 
    ((bv_slt t (bv_or s (signed_max n))) = true).
Proof.
  intros n s t Hn_s Hn_t.
  split.
  - intro H_exists.
    destruct H_exists as [x [Hx_size H_slt]].
    apply bv_sgt_bv_slt in H_slt.
    destruct (last s false) eqn:Hs_sign.
    + rewrite (bv_slt_sle_trans H_slt). 
      * easy. 
      * apply (bv_or_sle_or_smax Hx_size Hn_s ). 
    + rewrite (bv_slt_sle_trans H_slt).
      * easy.
      * apply (bv_or_sle_or_smax Hx_size Hn_s). 
  - intro H_slt.
    exists (signed_max n).
    split.
    + apply signed_max_size.
    + apply bv_slt_bv_sgt.
      rewrite bv_or_comm with (n := n).
      * exact H_slt.
      * apply signed_max_size.
      * exact Hn_s.
Qed.


(* t >=s (s | signed_min) <=> (exists x, x | s <=s t) *)
Theorem bvor_sle : forall (n : N), forall (s t : bitvector),
    (size s) = n -> (size t) = n -> iff
      ((bv_sge t (bv_or s (signed_min n))) = true)
      (exists (x : bitvector),
          (size x = n) /\
          ((bv_sle (bv_or x s) t) = true)).
Proof.
  intros n s t Hs Ht. assert (H_cases : (0 < n \/ n = 0)%N) by lia.
  destruct H_cases as [Hn_pos | Hn_zero].
  - split.
    + intro Hge.
      exists (signed_min n). split.
      * apply signed_min_size.
      * rewrite bv_sge_iff_sle in Hge.
        rewrite (@bv_or_comm n (signed_min n) s).
        -- exact Hge.
        -- apply signed_min_size.
        -- exact Hs.
    + intro Hex. destruct Hex as [x [Hx_size Hle]].
      rewrite bv_sge_iff_sle. eapply bv_sle_trans.
      * apply bv_or_signed_min_lower_bound with (x := x).
        -- lia.
        -- exact Hs.
        -- exact Hx_size.
      * exact Hle.
  - rewrite Hn_zero in *.
    destruct s; [| unfold size in Hs; discriminate Hs].
    destruct t; [| unfold size in Ht; discriminate Ht]. 
    split.
    + intro Hge. exists nil. split.
      * reflexivity.
      * compute. reflexivity.
    + intros [x [Hx_size Hle]].
      destruct x; [| unfold size in Hx_size; discriminate Hx_size].
      compute. reflexivity.
Qed.


(* s >=s s & t <=> (exists x, x | s >=s t) *)
Theorem bvor_sge :
  forall (n : N), forall (s t : bitvector), (size s) = n -> (size t) = n ->
    iff
      ((bv_sge s (bv_and s t)) = true)
      (exists (x : bitvector), (size x = n) /\
          ((bv_sge (bv_or x s) t) = true)).
Proof.
  intros n s t H_size_s H_size_t.
  assert (H_cases : (0 < n \/ n = 0)%N) by lia.
  destruct H_cases as [H_n_pos | H_n_zero].
  { 
    split.
    - intro H_sge_and.
      exists (signed_max n); split.
      + apply signed_max_size.
      + apply bvor_smax_sge_helper; assumption.
    - intro H_exists; destruct H_exists as [x [H_size_x H_sge_or]].
      eapply bvor_sge_exists_helper; eassumption.
  }
  { 
    rewrite H_n_zero in *.
    destruct s; [| unfold size in H_size_s; discriminate H_size_s].
    destruct t; [| unfold size in H_size_t; discriminate H_size_t].
    split.
    - intro H_sge_and. exists nil. split.
      + reflexivity.
      + compute. reflexivity.
    - intros [x [H_size_x H_sge_or]].
      destruct x; [| unfold size in H_size_x; discriminate H_size_x].
      compute. reflexivity.
  }
Qed.


(*------------------------------------------------------------*)


(*--------------------Logical left shift 1--------------------*)


(* (t >> s) << s = t <=> (exists x, x << s = t) *)
Theorem bvshl_eq : forall (n : N), forall (s t : bitvector),
   (size s) = n -> (size t) = n -> iff
     (bv_shl (bv_shr t s) s = t)
     (exists (x : bitvector), (size x = n) /\ bv_shl x s = t).
Proof. intros n s t Hs Ht.
        split; intro A.
        - exists (bv_shr_a t s). split.
          unfold size, bv_shr_a.
         rewrite Hs, Ht, N.eqb_refl.
         now rewrite length_shr_n_bits_a.
         rewrite bv_shr_eq, bv_shl_eq in A.
         rewrite bv_shl_eq.
         easy.
        - destruct A as (x, (Hx, A)).
          rewrite <- A.
          rewrite bv_shr_eq, !bv_shl_eq.
          unfold bv_shl_a, bv_shr_a.
          rewrite Hx, Hs, N.eqb_refl.
          unfold size in *. rewrite length_shl_n_bits_a, Hx.
          rewrite N.eqb_refl.
          rewrite length_shr_n_bits_a, length_shl_n_bits_a, Hx.
          rewrite N.eqb_refl.
          now rewrite shl_n_shr_a.
Qed.


(* t != 0 or s <u size(s) => (exists x, x << s != t) *)
Theorem bvshl_neq_ltr: forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    bv_eq t (zeros (size t)) = false \/ 
      bv_ult s (nat2bv (N.to_nat (size s)) (size s)) = true ->
    (exists (x : bitvector), (size x = n) /\ bv_eq (bv_shl x s) t = false).
Proof.
  intros n s t Hs Ht H. destruct H.
  + unfold bv_eq in H. rewrite zeros_size in H. rewrite N.eqb_refl in H.
    unfold bits in H. apply List_neq in H. exists (zeros n). split.
    - apply zeros_size.
    - unfold bv_eq. rewrite (@bv_shl_size n (zeros n) s (@zeros_size n) Hs).
      rewrite Ht. rewrite N.eqb_refl. unfold bits. apply List_neq2. 
      pose proof (@bvshl_zeros s) as bvshl_zeros. rewrite Hs in bvshl_zeros.
      rewrite bvshl_zeros. rewrite Ht in H. unfold not in *. 
      intros t_0. rewrite t_0 in H. 
      now specialize (@H (@eq_refl bitvector t)).
  + destruct (@list_cases_all_false s).
    - exists (bv_not t). split.
      * now apply bv_not_size.
      * unfold bv_eq. rewrite (@bv_shl_size n (bv_not t) s (@bv_not_size n t Ht) Hs).
        rewrite Ht. rewrite N.eqb_refl. unfold bits. apply List_neq2.
        rewrite H0. pose proof (@bvshl_b_zeros (bv_not t)) as bvshl0.
        rewrite bv_shl_eq. unfold zeros, size in bvshl0.
        rewrite Nat2N.id in bvshl0. pose proof Hs as Hss.
        pose proof Ht as Htt. unfold size in Hs, Ht. 
        rewrite <- N2Nat.inj_iff in Hs, Ht. rewrite Nat2N.id in Hs, Ht.
        rewrite Hs. rewrite <- Ht. pose proof (@bv_not_size n t) as bvnot_size.
        specialize (@bvnot_size Htt). unfold size in bvnot_size.
        rewrite <- N2Nat.inj_iff in bvnot_size.
        rewrite Nat2N.id in bvnot_size. rewrite bvnot_size in bvshl0.
        rewrite <- Ht in bvshl0. rewrite bvshl0. unfold not.
        induction t.
        ++ simpl in Ht. rewrite <- Ht in Hs. 
           pose proof (@length_zero_nil s) as length_nil.
           symmetry in Hs. specialize (@length_nil Hs).
           rewrite <- length_nil in H. simpl in H.
           now contradict H.
        ++ apply bv_not_not_eq.
    - destruct (@list_cases_all_false t).
      * exists (mk_list_true (N.to_nat n)). split. 
        ** unfold size. rewrite length_mk_list_true. 
           now rewrite N2Nat.id.
        ** unfold bv_eq. 
           pose proof (@bv_shl_size n (mk_list_true (N.to_nat n)) s) as Hsize.
           unfold size in Hsize at 1.
           rewrite (@length_mk_list_true (N.to_nat n)) in Hsize.
           rewrite N2Nat.id in Hsize. 
           specialize (@Hsize (@N.eq_refl n) Hs). rewrite Hsize. rewrite Ht.
           rewrite N.eqb_refl. unfold bits. apply List_neq2.
           rewrite H1. unfold size in Ht, Hs. rewrite <- N2Nat.inj_iff in Ht, Hs.
           rewrite Nat2N.id in Ht, Hs. rewrite Ht.
           pose proof (@bvshl_ones_neq_zero (N.to_nat n) s Hs H H0) as shift_ones.
           apply shift_ones.
      * exists (zeros n). split.
        ** apply zeros_size.
        ** unfold bv_eq. pose proof bv_shl_size. 
           rewrite (@bv_shl_size n (zeros n) s (@zeros_size n) Hs).
           rewrite Ht. rewrite N.eqb_refl. unfold bits. apply List_neq2.
           unfold not. intros contr.
           pose proof (@bvshl_zeros s) as shl_0. rewrite Hs in shl_0. 
           rewrite shl_0 in contr. unfold zeros in contr.
           unfold size in Ht. apply N2Nat.inj_iff in Ht. rewrite Nat2N.id in Ht.
           rewrite Ht in H1. unfold not in H1. apply H1. symmetry in contr.
           apply contr.
Qed. 


(* (exists x, x << s != t) => t != 0 or s <u size(s) *)
Theorem bvshl_neq_rtl: forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_eq (bv_shl x s) t = false) ->
    bv_eq t (zeros (size t)) = false \/ 
    bv_ult s (nat2bv (N.to_nat (size s)) (size s)) = true.
Proof. 
    intros. destruct H1 as (x, (H1, H2)). rewrite bv_shl_eq in H2.
    unfold nat2bv. rewrite N2Nat.id.
    unfold bv_shl_a, shl_n_bits_a, list2nat_be_a in *.
    rewrite bv_ult_nat in *. unfold bv2nat_a, list2nat_be_a.
    rewrite list2N_N2List_eq. rewrite H, H1, N.eqb_refl in H2.
    case_eq ( N.to_nat (list2N s) <? length x); intros.
    - right. rewrite H, <- H1. unfold size. now rewrite Nat2N.id.
    - rewrite H3 in H2. left. unfold zeros, size.
      rewrite Nat2N.id. unfold bv_eq in *. unfold size in *. 
      rewrite length_mk_list_false in *.
      rewrite H1, H0, N.eqb_refl in H2. rewrite H0, N.eqb_refl.
      unfold bits in *. apply List_neq2. apply List_neq in H2.
      Reconstr.reasy (@BV.BVList.BITVECTOR_LIST.of_bits_size,
                      @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
    - unfold size. rewrite length_N2list.
      rewrite N2Nat.id. now rewrite N.eqb_refl.
Qed.


Theorem bvshl_neq: forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (bv_eq t (zeros (size t)) = false \/ 
      bv_ult s (nat2bv (N.to_nat (size s)) (size s)) = true)
    (exists (x : bitvector), (size x = n) /\ bv_eq (bv_shl x s) t = false).
Proof.
  intros. split.
  + now apply bvshl_neq_ltr.
  + now apply bvshl_neq_rtl.
Qed.


(* (t <u (~0 << s)) <=> (exists x, x << s >u t) *)
Theorem bvshl_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_ult t (bv_shl (bv_not (zeros (size s))) s) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_shl x s) t = true)).
Proof.
  intros n s t Hs Ht. split. 
  + intro. exists (bv_not (zeros (size s))).
    split. 
    - apply bv_not_size. rewrite (zeros_size (size s)). 
      apply  Hs. 
    - apply bv_ult_bv_ugt. apply H.
  + intros. destruct H as (x, (Hx, H1)).
    apply bv_ugt_bv_ult in H1. rewrite bv_shl_eq in *. 
    assert (forall (n : N) (x s : bitvector), size x = n 
            -> size s = n -> 
            bv_ule (bv_shl_a x s) 
              (bv_shl_a (bv_not (zeros (size s))) s) = true).
    { apply bv_shl_a_1_leq. }
    specialize (@H n x s Hx Hs).
    pose proof (@bv_ult_ule_list_trans t (bv_shl_a x s)
                (bv_shl_a (bv_not (zeros (size s))) s) H1 H).
    apply H0.
Qed.


(* ~0 << s >=u t <=> x << s >= t *)
Theorem bvshl_uge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_uge (bv_shl (bv_not (zeros (size s))) s) t = true)
    (exists (x : bitvector), (size x = n) /\ (bv_uge (bv_shl x s) t = true)).
Proof.
  intros n s t Hs Ht. split.
  + intros H. exists (bv_not (zeros (size s))). split.
    - apply bv_not_size. rewrite Hs. apply zeros_size.
    - apply H.
  + intros H. destruct H as (x, (Hx, H)). rewrite bv_shl_eq in *.
    apply bv_uge_bv_ule in H. pose proof (@bv_shl_a_1_leq n x s Hx Hs).
    pose proof (@bv_ule_list_trans t (bv_shl_a x s) (bv_shl_a (bv_not (zeros (size s))) s) H H0).
    apply bv_ule_bv_uge in H1. apply H1.
Qed.


(* (mins >> s) << s <s t <=> (exists x, x << s <s t) *)
Theorem bvshl_slt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt (bv_shl (bv_shr (signed_min n) s) s) t = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_shl x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  split; intro A.
  + exists (bv_shr (signed_min n) s). split. 
    - apply bv_shr_size.
      * apply signed_min_size.
      * apply Hs.
    - apply A.
  + destruct A as (x, (Hx, A)).
    assert ((bv_sle (bv_shl (bv_shr (signed_min n) s) s) (bv_shl x s)) = true).
    { case_eq (Nat.leb (N.to_nat n) (list2nat_be_a (bits s))); intro.
      - rewrite !(@shl_ge_size n).
        * apply bv_sle_refl.
        * apply Hx.
        * apply Hs.
        * apply H.
        * apply bv_shr_size.
          ++ apply signed_min_size.
          ++ apply Hs.
        * apply Hs.
        * apply H.
      - rewrite shl_shr_signed_min.
        * replace n with (size (bv_shl x s)).
          ++ apply signed_min_sle.
          ++ now apply bv_shl_size.
        * apply Hs.
        * apply H.
    }
    now apply (@bv_sle_slt_trans (bv_shl (bv_shr (signed_min n) s) s) (bv_shl x s) t).
Qed.


(* t <s (maxs << s) & maxs <=> (exists x, x << s >s t) *)
Theorem bvshl_sgt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt t (bv_and (bv_shl (signed_max n) s) (signed_max n)) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sgt (bv_shl x s) t) = true)).
Proof.
  intros n s t Hs Ht. setoid_rewrite bv_sgt_slt_equiv.
  rewrite and_shl_shr_signed_max_eq by exact Hs. split.
  - intros H. exists (bv_shr (signed_max n) s). split.
    + apply bv_shr_size.
      * apply signed_max_size.
      * exact Hs.
    + exact H.
  - intros [x [Hx Hlt]].
    set (M := bv_shl (bv_shr (signed_max n) s) s).
    set (v := bv_shl x s).
    assert (Hsv : size v = n).
    { unfold v. apply bv_shl_size.
      - exact Hx.
      - exact Hs.
    }
    assert (Hle : bv_sle v M = true).
    { unfold v, M.
      destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hshift.
      - apply Nat.leb_le in Hshift.
        rewrite shl_ge_size with (n := n).
        + rewrite shl_ge_size with (n := n).
          * apply bv_sle_refl.
          * apply bv_shr_size. apply signed_max_size. exact Hs.
          * exact Hs.
          * unfold bits. apply Nat.leb_le. exact Hshift.
        + exact Hx.
        + exact Hs.
        + unfold bits. apply Nat.leb_le. exact Hshift.
      - apply Nat.leb_gt in Hshift.
        rewrite bv_shl_eq_shl_n_bits by (rewrite Hx; symmetry; exact Hs).
        assert (Hshr_size: size (bv_shr (signed_max n) s) = n).
        { apply bv_shr_size. apply signed_max_size. exact Hs. }
        rewrite bv_shl_eq_shl_n_bits by (rewrite Hshr_size; symmetry; exact Hs).
        rewrite bv_shr_eq_shr_n_bits by (rewrite signed_max_size; symmetry; exact Hs).
        assert (Hx_len: length x = N.to_nat n).
        { unfold size in Hx. rewrite <- Hx. rewrite Nat2N.id. reflexivity. }
        assert (Hsm_len: length (signed_max n) = N.to_nat n).
        { assert (Hsm: size (signed_max n) = n) by apply signed_max_size.
          unfold size in Hsm. 
          apply f_equal with (f := N.to_nat) in Hsm.
          rewrite Nat2N.id in Hsm. exact Hsm. }
        rewrite shl_n_bits_eq_shl_n_bits_a by (rewrite Hx_len; lia).
        rewrite shl_n_bits_eq_shl_n_bits_a by (rewrite length_shr_n_bits; rewrite Hsm_len; lia).
        rewrite <- N2Nat.id with (a := n).
        apply M_is_max_signed_in_shifted_general.
        + lia.
        + lia.
        + rewrite length_shl_n_bits_a. exact Hx_len.
        + unfold shl_n_bits_a.
          destruct (bv2nat_a s <? length x)%nat eqn:Hlt2.
          * rewrite firstn_app by (rewrite length_mk_list_false; lia).
            rewrite firstn_all2 by (rewrite length_mk_list_false; lia).
            rewrite length_mk_list_false. rewrite Nat.sub_diag. simpl.
            rewrite app_nil_r. reflexivity.
          * apply Nat.ltb_ge in Hlt2. rewrite Hx_len in Hlt2. lia.
    }
    eapply bv_slt_sle_trans.
    + exact Hlt.
    + exact Hle.
Qed.


(* t >> (t >> s) <u min_s <=> (exists x, x << s <=s t) *)
Theorem bvshl_sle : forall (n : N), forall (s t : bitvector),
  (0 < n)%N -> (size s) = n -> (size t) = n -> iff
    (bv_ult (bv_shr t (bv_shr t s)) (signed_min n) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sle (bv_shl x s) t) = true)).
Proof.
  intros n s t Hn Hs Ht.
  split.

  - (* Forward: LHS → RHS. Witness: bv_shr (signed_min n) s *)
    intro HLHS.
    exists (bv_shr (signed_min n) s).
    split.
    + apply bv_shr_size. apply signed_min_size. exact Hs.
    + destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hshift.
      * (* s >= n: bv_shl (bv_shr (signed_min n) s) s = zeros n *)
        apply Nat.leb_le in Hshift.
        rewrite shl_ge_size with (n := n).
        -- (* need bv_sle (zeros n) t = true *)
           apply zeros_sle_nonneg. { exact Ht. }
           apply ult_b_signed_min_implies_positive_sign with (n := n). { exact Ht. }
           (* bv_shr t s = zeros n, so bv_shr t (bv_shr t s) = t *)
           assert (Hts : bv_shr t s = zeros n).
           { apply shr_ge_size. exact Ht. exact Hs. apply Nat.leb_le. exact Hshift. }
           rewrite Hts in HLHS.
           rewrite bv_shr_zeros_is_self in HLHS by exact Ht.
           exact HLHS.
        -- apply bv_shr_size. apply signed_min_size. exact Hs.
        -- exact Hs.
        -- unfold bits. apply Nat.leb_le. exact Hshift.
      * (* s < n: bv_shl (bv_shr (signed_min n) s) s = signed_min n *)
        rewrite shl_shr_signed_min.
        -- rewrite <- Ht. apply signed_min_sle.
        -- exact Hs.
        -- exact Hshift.

  - (* Backward: RHS → LHS *)
    intros [x [Hx Hle]].
    assert (Hshr_size : size (bv_shr t s) = n) by (apply bv_shr_size; [exact Ht | exact Hs]).
    (* Case split: is the inner shift result positive? *)
    destruct (bvgez (bv_shr t s)) as [Hk1_0 | Hk1_pos].
    + (* bv2nat_a (bv_shr t s) = 0: inner result is zeros n *)
      assert (Hinner_zeros : bv_shr t s = zeros n)
        by (apply bv2nat_a_zero_eq_zeros; [exact Hshr_size | exact Hk1_0]).
      rewrite Hinner_zeros. rewrite bv_shr_zeros_is_self by exact Ht.
      apply nonneg_ult_signed_min with (n := n). { exact Hn. } { exact Ht. }
      (* Need: last t false = false *)
      destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hshift.
      * (* s >= n: bv_shl x s = zeros n, so bv_sle (zeros n) t = true *)
        apply Nat.leb_le in Hshift.
        assert (Hxs : bv_shl x s = zeros n).
        { apply shl_ge_size. exact Hx. exact Hs.
          unfold bits. apply Nat.leb_le. exact Hshift. }
        rewrite Hxs in Hle.
        pose proof (bv_zeros_sle t) as Hzs.
        rewrite Ht in Hzs. rewrite Hle in Hzs.
        apply negb_true_iff. exact (eq_sym Hzs).
      * (* s < n and bv_shr t s = zeros n *)
        apply Nat.leb_gt in Hshift.
        destruct (bvgez s) as [Hs0 | Hs_pos].
        -- (* s = 0: bv_shr t (zeros n) = t, so t = zeros n *)
           assert (Ht_zeros : t = zeros n).
           { pose proof (bv2nat_a_zero_eq_zeros Hs Hs0) as Hs_eq.
             rewrite Hs_eq in Hinner_zeros.
             rewrite bv_shr_zeros_is_self in Hinner_zeros by exact Ht.
             exact Hinner_zeros. }
           rewrite Ht_zeros. unfold zeros. apply last_mk_list_false.
        -- (* 0 < s < n: use bv_shr_pos_zeros_implies_last_false *)
           apply bv_shr_pos_zeros_implies_last_false with (n := n) (s := s).
           ++ exact Ht. ++ exact Hs. ++ exact Hs_pos. ++ exact Hshift.
           ++ exact Hinner_zeros.
    + (* bv2nat_a (bv_shr t s) > 0: outer shift has MSB = false *)
      apply nonneg_ult_signed_min with (n := n). { exact Hn. }
      { apply bv_shr_size. exact Ht. exact Hshr_size. }
      apply last_bv_shr_pos with (n := n) (s := bv_shr t s).
      * exact Ht.
      * exact Hshr_size.
      * exact Hk1_pos.
Qed.


(* (max_s << s) & max_s >=s t <=> (exists x, x << s >=s t) *)
Theorem bvshl_sge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sge (bv_and (bv_shl (signed_max n) s) (signed_max n)) t = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sge (bv_shl x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  setoid_rewrite bv_sge_sle_equiv.
  rewrite and_shl_shr_signed_max_eq by exact Hs.
  split.
  - intros H.
    exists (bv_shr (signed_max n) s).
    split.
    + apply bv_shr_size.
      * apply signed_max_size.
      * exact Hs.
    + exact H.
  - intros [x [Hx Hle_t_v]].
    set (M := bv_shl (bv_shr (signed_max n) s) s).
    set (v := bv_shl x s).
    assert (Hsv : size v = n).
    { unfold v. apply bv_shl_size.
      - exact Hx.
      - exact Hs.
    }
    assert (Hle : bv_sle v M = true).
    { unfold v, M.
      destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hshift.
      - apply Nat.leb_le in Hshift.
        rewrite shl_ge_size with (n := n).
        + rewrite shl_ge_size with (n := n).
          * apply bv_sle_refl.
          * apply bv_shr_size. apply signed_max_size. exact Hs.
          * exact Hs.
          * unfold bits. apply Nat.leb_le. exact Hshift.
        + exact Hx.
        + exact Hs.
        + unfold bits. apply Nat.leb_le. exact Hshift.
      - apply Nat.leb_gt in Hshift.
        rewrite bv_shl_eq_shl_n_bits by (rewrite Hx; symmetry; exact Hs).
        assert (Hshr_size: size (bv_shr (signed_max n) s) = n).
        { apply bv_shr_size. apply signed_max_size. exact Hs. }
        rewrite bv_shl_eq_shl_n_bits by (rewrite Hshr_size; symmetry; exact Hs).
        rewrite bv_shr_eq_shr_n_bits by (rewrite signed_max_size; symmetry; exact Hs).
        assert (Hx_len: length x = N.to_nat n).
        { unfold size in Hx. rewrite <- Hx. rewrite Nat2N.id. reflexivity. }
        assert (Hsm_len: length (signed_max n) = N.to_nat n).
        { assert (Hsm: size (signed_max n) = n) by apply signed_max_size.
          unfold size in Hsm.
          apply f_equal with (f := N.to_nat) in Hsm.
          rewrite Nat2N.id in Hsm. exact Hsm. }
        rewrite shl_n_bits_eq_shl_n_bits_a by (rewrite Hx_len; lia).
        rewrite shl_n_bits_eq_shl_n_bits_a by (rewrite length_shr_n_bits; rewrite Hsm_len; lia).
        rewrite <- N2Nat.id with (a := n).
        apply M_is_max_signed_in_shifted_general.
        + lia.
        + lia.
        + rewrite length_shl_n_bits_a. exact Hx_len.
        + unfold shl_n_bits_a.
          destruct (bv2nat_a s <? length x)%nat eqn:Hlt2.
          * rewrite firstn_app by (rewrite length_mk_list_false; lia).
            rewrite firstn_all2 by (rewrite length_mk_list_false; lia).
            rewrite length_mk_list_false.
            rewrite Nat.sub_diag. simpl.
            rewrite app_nil_r. reflexivity.
          * apply Nat.ltb_ge in Hlt2. rewrite Hx_len in Hlt2. lia.
    }
    eapply bv_sle_trans.
    + exact Hle_t_v.
    + exact Hle.
Qed.


(*------------------------------------------------------------*)


(*--------------------Logical left shift 2--------------------*)


(* (exists i, s << i = t) <=> (exists x, s << x = t) *)
Theorem bvshl_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (i : nat), 
      ((bv_shl s (nat2bv i (size s))) = t))
    (exists (x : bitvector), (size x = n) /\ (bv_shl s x = t)).
Proof. split; intros.
       - destruct H1 as (i, H1).
         exists (nat2bv i (size s)). split.
         unfold size.
         now rewrite length_nat2bv, Nat2N.id.
         easy.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         rewrite N2Nat.id. unfold size in *.
         rewrite H, <- H1, Nat2N.id. now rewrite N2List_list2N.
Qed.


(* min_s << s <u t + min_s <=> (exists x, s << x <s t) *)
Theorem bvshl_slt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_ult (bv_shl (signed_min n) s) (bv_add t (signed_min n)) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_shl s x) t) = true)).
Proof.
  intros n s t Hs Ht.
  assert (Hbshift_zero : bv_shl (signed_min n) (zeros n) = signed_min n).
  { rewrite bv_shl_eq.
    pose proof (bvshl_b_zeros (signed_min n)) as H.
    rewrite signed_min_size in H. exact H. }
  split.
  - (* Forward: LHS → RHS *)
    intro HLHS.
    destruct (bvgez s) as [Hs0 | Hs_pos].
    + (* s = zeros n *)
      assert (Hs_zeros : s = zeros n) by (apply bv2nat_a_zero_eq_zeros; [exact Hs | exact Hs0]).
      rewrite Hs_zeros, Hbshift_zero in HLHS.
      destruct (N.eq_dec n 0%N) as [Hn0 | Hn_ne].
      * assert (Ht_nil : t = nil).
        { apply length_zero_iff_nil. rewrite (size_to_length Ht), Hn0. reflexivity. }
        subst t. rewrite Hn0 in HLHS. cbn in HLHS. discriminate.
      * assert (Hn : (0 < n)%N) by (destruct n; [exact (False_ind _ (Hn_ne eq_refl)) | lia]).
        assert (Hzst : bv_slt (zeros n) t = true).
        { rewrite <- bv_ult_smin_add_smin_eq_slt_zeros by assumption. exact HLHS. }
        exists (zeros n). split. { apply zeros_size. }
        rewrite Hs_zeros.
        assert (Hzz : bv_shl (zeros n) (zeros n) = zeros n).
        { pose proof (bvshl_zeros (zeros n)) as H. rewrite zeros_size in H. exact H. }
        rewrite Hzz. exact Hzst.
    + (* s nonzero *)
      assert (Hn : (0 < n)%N) by exact (n_pos_of_bv2nat_a_pos Hs Hs_pos).
      assert (Hshl_zeros : bv_shl (signed_min n) s = zeros n).
      { apply bv_shl_signed_min_nonzero; assumption. }
      rewrite Hshl_zeros in HLHS.
      assert (Hne : t <> signed_min n).
      { intro Heq. subst t.
        rewrite (bv_add_smin_smin_eq_zeros Hn) in HLHS.
        pose proof (not_bv_ult_x_zero (zeros n)) as Hc.
        rewrite zeros_size in Hc. rewrite Hc in HLHS. discriminate. }
      destruct (nonzero_bv_shl_achieves_smin Hn Hs Hs_pos) as [x [Hx Hxeq]].
      exists x. split. { exact Hx. }
      rewrite Hxeq.
      apply (bv_slt_signed_min_iff Ht). exact Hne.
  - (* Backward: RHS → LHS *)
    intros [x [Hx Hle]].
    destruct (bvgez s) as [Hs0 | Hs_pos].
    + (* s = zeros n *)
      assert (Hs_zeros : s = zeros n) by (apply bv2nat_a_zero_eq_zeros; [exact Hs | exact Hs0]).
      rewrite Hs_zeros in Hle.
      assert (Hshift_x : bv_shl (zeros n) x = zeros n).
      { pose proof (bvshl_zeros x) as H. rewrite Hx in H. exact H. }
      rewrite Hshift_x in Hle.
      rewrite Hs_zeros, Hbshift_zero.
      destruct (N.eq_dec n 0%N) as [Hn0 | Hn_ne].
      * assert (Ht_nil : t = nil).
        { apply length_zero_iff_nil. rewrite (size_to_length Ht), Hn0. reflexivity. }
        subst t. rewrite Hn0 in Hle. cbn in Hle. discriminate.
      * assert (Hn : (0 < n)%N) by (destruct n; [exact (False_ind _ (Hn_ne eq_refl)) | lia]).
        rewrite bv_ult_smin_add_smin_eq_slt_zeros by assumption.
        exact Hle.
    + (* s nonzero *)
      assert (Hn : (0 < n)%N) by exact (n_pos_of_bv2nat_a_pos Hs Hs_pos).
      assert (Hshl_zeros : bv_shl (signed_min n) s = zeros n).
      { apply bv_shl_signed_min_nonzero; assumption. }
      rewrite Hshl_zeros.
      assert (Hslt : bv_slt (signed_min n) t = true).
      { eapply bv_sle_slt_trans.
        - rewrite <- (bv_shl_size Hs Hx). apply signed_min_sle.
        - exact Hle. }
      assert (Hne : t <> signed_min n).
      { intro Heq. rewrite Heq in Hslt. rewrite bv_slt_nrefl in Hslt. discriminate. }
      assert (Hadd_ne : bv_add t (signed_min n) <> zeros n).
      { apply bv_add_t_smin_ne_zeros; assumption. }
      assert (Hule : bv_ule (zeros n) (bv_add t (signed_min n)) = true).
      { apply bv_uge_bv_ule. apply bv_uge_zeros.
        apply bv_add_size; [exact Ht | apply signed_min_size]. }
      apply bv_ule_eq in Hule. destruct Hule as [Hult | Heq].
      * exact Hult.
      * exfalso. apply Hadd_ne. exact (eq_sym Heq).
Qed.

(* t >> s <u mins <=> (exists x, s << x <=s t) *)
Theorem bvshl_sle2 : forall (n : N), forall (s t : bitvector),
  (0 < n)%N -> (size s) = n -> (size t) = n -> iff
    (bv_ult (bv_shr t s) (signed_min n) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sle (bv_shl s x) t) = true)).
Proof.
  intros n s t Hn Hs Ht.
  split.
  - (* Forward: t >> s <u min_s -> exists x. s << x <=s t *)
    intro HLHS.
    destruct (bvgez s) as [Hs0 | Hs_pos].
    + (* bv2nat_a s = 0, so s = zeros n *)
      assert (Hs_zeros : s = zeros n) by (apply bv2nat_a_zero_eq_zeros; [exact Hs | exact Hs0]).
      (* bv_shr t (zeros n) = t, so hypothesis gives last t false = false *)
      assert (Hlast_t : last t false = false).
      { rewrite Hs_zeros in HLHS.
        rewrite bv_shr_zeros_is_self in HLHS by exact Ht.
        apply ult_b_signed_min_implies_positive_sign with (n := n).
        exact Ht. exact HLHS. }
      (* Witness: zeros n. bv_shl (zeros n) (zeros n) = zeros n <=s t *)
      exists (zeros n).
      split.
      * apply zeros_size.
      * rewrite Hs_zeros.
        assert (Hzz : bv_shl (zeros n) (zeros n) = zeros n).
        { specialize (bvshl_zeros (zeros n)) as Hb.
          rewrite zeros_size in Hb. exact Hb. }
        rewrite Hzz.
        rewrite <- Ht. rewrite bv_zeros_sle. rewrite Hlast_t. reflexivity.
    + (* bv2nat_a s > 0: use nonzero_bv_shl_achieves_smin *)
      destruct (@nonzero_bv_shl_achieves_smin n s Hn Hs Hs_pos) as [x [Hx Hxeq]].
      exists x.
      split.
      * exact Hx.
      * rewrite Hxeq.
        rewrite <- Ht. apply signed_min_sle.
  - (* Backward: exists x. s << x <=s t -> t >> s <u min_s *)
    intros [x [Hx Hle]].
    destruct (bvgez s) as [Hs0 | Hs_pos].
    + (* bv2nat_a s = 0, so s = zeros n *)
      assert (Hs_zeros : s = zeros n) by (apply bv2nat_a_zero_eq_zeros; [exact Hs | exact Hs0]).
      (* bv_shl (zeros n) x = zeros n, so zeros n <=s t *)
      rewrite Hs_zeros in Hle.
      assert (Hsxl : bv_shl (zeros n) x = zeros n).
      { rewrite <- Hx. exact (bvshl_zeros x). }
      rewrite Hsxl in Hle.
      assert (Hlast_t : last t false = false).
      { rewrite <- Ht in Hle. rewrite bv_zeros_sle in Hle.
        destruct (last t false); simpl in Hle; [discriminate | reflexivity]. }
      rewrite Hs_zeros.
      rewrite bv_shr_zeros_is_self by exact Ht.
      apply nonneg_ult_signed_min with (n := n); [exact Hn | exact Ht | exact Hlast_t].
    + (* bv2nat_a s > 0: bv_shr t s always has MSB = false *)
      assert (Hshr_size : size (bv_shr t s) = n)
        by (apply bv_shr_size; [exact Ht | exact Hs]).
      apply nonneg_ult_signed_min with (n := n).
      * exact Hn.
      * exact Hshr_size.
      * apply last_bv_shr_pos with (n := n) (s := s).
        -- exact Ht. -- exact Hs. -- exact Hs_pos.
Qed.


(*------------------------------------------------------------*)


(*--------------------Logical right shift 1--------------------*)


(* (t << s) >> s = t <=> (exists x, x >> s = t) *)
Theorem bvshr_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (bv_shr (bv_shl t s) s = t)
    (exists (x : bitvector), (size x = n) /\ bv_shr x s = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - exists (bv_shl_a t s). split.
         unfold size, bv_shl_a.
         rewrite Hs, Ht, N.eqb_refl.
         now rewrite length_shl_n_bits_a.
         rewrite bv_shr_eq.
         rewrite bv_shr_eq, bv_shl_eq in A.
         easy.
       - destruct A as (x, (Hx, A)).
         rewrite <- A.
         rewrite !bv_shr_eq, bv_shl_eq.
         unfold bv_shl_a, bv_shr_a.
         rewrite Hx, Hs, N.eqb_refl.
         unfold size in *. rewrite length_shr_n_bits_a, Hx.
         rewrite N.eqb_refl.
         rewrite length_shl_n_bits_a, length_shr_n_bits_a, Hx.
         rewrite N.eqb_refl.
         now rewrite shr_n_shl_a.
Qed.


(* (t <u (~s >> s)) => (exists x, (x >> s) >u t) *)
Theorem bvshr_ugt_ltr : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (bv_ult t (bv_shr (bv_not s) s) = true) -> 
    (exists (x : bitvector), (size x = n) /\ bv_ugt (bv_shr x s) t = true).
Proof. intros.
       exists (bv_not s). rewrite bv_shr_eq in *. split.
       Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size) Reconstr.Empty.
       apply bv_ult_bv_ugt.
       rewrite bv_ult_nat in *. easy.
       rewrite bv_shr_a_size with (n := n), H0, N.eqb_refl. easy.
       rewrite bv_not_size with (n:= n). easy.
       easy. easy.
       rewrite bv_shr_a_size with (n := n), H0, N.eqb_refl. easy.
       rewrite bv_not_size with (n:= n). easy.
       easy. easy.
Qed.


(* (exists x, (x >> s) >u t) => (t <u (~s >> s)) *)
Theorem bvshr_ugt_rtl : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_ugt (bv_shr x s) t = true)
          ->
    (bv_ult t (bv_shr (bv_not s) s) = true).
Proof.
  intros n s t Hs Ht H. destruct H as (x, (Hx, H)).
  apply bv_ugt_bv_ult in H. rewrite bv_shr_eq in *.
  unfold bv_ult in *. rewrite Ht in *. 
  unfold ult_list in *. rewrite <- (@bv_shr_a_size n x s Hx Hs) in H. 
  rewrite <- (@bv_shr_a_size n (bv_not s) s 
                (@bv_not_size n s Hs) Hs). 
  rewrite N.eqb_refl in *.
  unfold bv_shr_a in *. rewrite Hs, Hx in *. rewrite (@bv_not_size n s Hs).
  rewrite N.eqb_refl in *. unfold shr_n_bits_a in *.
  pose proof rev_skipn. pose proof Hx as Hx2. 
  pose proof (@bv_not_size n s Hs) as Hnots. pose proof Hs as Hs2. 
  unfold size in Hx2, Hnots, Hs2. apply N2Nat.inj_iff in Hx2. 
  apply N2Nat.inj_iff in Hnots. apply N2Nat.inj_iff in Hs2. 
  rewrite Nat2N.id in Hx2, Hnots, Hs2.
  case_eq (list2nat_be_a s <? length x); intros case.
  + pose proof (@bv_not_size n s Hs) as len. pose proof Hx as Hxlen.
    unfold size in len, Hxlen. apply N2Nat.inj_iff in len. 
    apply N2Nat.inj_iff in Hxlen. rewrite Nat2N.id in len, Hxlen.
    rewrite len. rewrite <- Hxlen. rewrite case in *. 
    rewrite rev_app_distr in *. rewrite rev_mk_list_false in *.
    apply Nat.ltb_lt in case.
    rewrite (@rev_skipn x (list2nat_be_a s) case) in H.
    pose proof rev_skipn. rewrite Hx2 in case. rewrite <- Hnots in case.
    rewrite (@rev_skipn (bv_not s) (list2nat_be_a s) case).
    rewrite Hnots. rewrite <- Hx2. rewrite Hnots in case.
    rewrite <- Hs2 in case. unfold list2nat_be_a in case.
    assert (ule_list_big_endian 
              (mk_list_false (list2nat_be_a s) ++
                firstn (length x - list2nat_be_a s) (rev x))
              (mk_list_false (list2nat_be_a s) ++
                firstn (length x - list2nat_be_a s) (rev (bv_not s))) = true) as ult.
    { apply (@app_ule_list_big_endian 
              (firstn (length x - list2nat_be_a s) (rev x)) 
              (firstn (length x - list2nat_be_a s) (rev (bv_not s)))
              (mk_list_false (list2nat_be_a s))). 
      unfold list2nat_be_a. rewrite rev_bvnot. rewrite Hx2. rewrite <- Hs2.
      apply first_bits_ule. unfold size. rewrite length_rev.
      rewrite Hx2, Hs2. easy. apply case. }
    apply (@ult_ule_list_big_endian_trans 
            (rev t) 
            (mk_list_false (list2nat_be_a s) ++
              firstn (length x - list2nat_be_a s) (rev x))
            (mk_list_false (list2nat_be_a s) ++
              firstn (length x - list2nat_be_a s) (rev (bv_not s)))
            H ult).
  + rewrite case in *. rewrite Hnots. rewrite <- Hx2. rewrite case.
    apply H.
Qed.


(* t <s (max_s << s) >> s <=> (exists x, x >> s >s t) *)
Theorem bvshr_sgt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt t (bv_shr (bv_shl (signed_max n) s) s) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sgt (bv_shr x s) t) = true)).
Proof.
  intros n s t Hs Ht. setoid_rewrite bv_sgt_slt_equiv. split.
  - intros H. exists (bv_shl (signed_max n) s). split.
    + apply bv_shl_size.
      * apply signed_max_size.
      * exact Hs.
    + exact H.
  - intros [x [Hx Hlt]].
    set (M := bv_shr (bv_shl (signed_max n) s) s).
    set (v := bv_shr x s).
    assert (Hsv : size v = n).
    { unfold v. apply bv_shr_size.
      - exact Hx.
      - exact Hs.
    }
    assert (Hle : bv_sle v M = true).
    { unfold v, M.
      destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hshift.
      - apply Nat.leb_le in Hshift. rewrite shr_ge_size with (n := n).
        + rewrite shr_ge_size with (n := n).
          * apply bv_sle_refl.
          * apply bv_shl_size. apply signed_max_size. exact Hs.
          * exact Hs.
          * apply Nat.leb_le. exact Hshift.
        + exact Hx.
        + exact Hs.
        + apply Nat.leb_le. exact Hshift.
      - apply Nat.leb_gt in Hshift.
        rewrite bv_shr_eq_shr_n_bits by (rewrite Hx; symmetry; exact Hs).
        assert (Hshl_size : size (bv_shl (signed_max n) s) = n).
        { apply bv_shl_size. apply signed_max_size. exact Hs. }
        rewrite bv_shr_eq_shr_n_bits by (rewrite Hshl_size; symmetry; exact Hs).
        rewrite bv_shl_eq_shl_n_bits by (rewrite signed_max_size; symmetry; exact Hs).
        assert (Hx_len : length x = N.to_nat n).
        { unfold size in Hx. rewrite <- Hx. rewrite Nat2N.id. reflexivity. }
        assert (Hsm_len : length (signed_max n) = N.to_nat n).
        { assert (Hsm : size (signed_max n) = n) by apply signed_max_size.
          unfold size in Hsm.
          apply f_equal with (f := N.to_nat) in Hsm.
          rewrite Nat2N.id in Hsm. exact Hsm. }
        rewrite <- N2Nat.id with (a := n).
        apply M_is_max_for_shr_general.
        + lia.
        + lia.
        + rewrite length_shr_n_bits. exact Hx_len.
        + replace (N.to_nat n) with (length x) by lia.
          apply shr_n_bits_high_bits_false. lia.
    }
    eapply bv_slt_sle_trans.
    + exact Hlt.
    + exact Hle.
Qed.


(* s != 0 => ~0 >> s >=s t <=> (exists x, x >> s >=s t) *)
Theorem bvshr_sge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_eq s (zeros n) = false -> bv_sge (bv_shr (bv_not (zeros n)) s) t = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sge (bv_shr x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  setoid_rewrite bv_sge_sle_equiv.
  split.
  - intros H.
    destruct (bv_eq s (zeros n)) eqn:Hsz.
    + apply bv_eq_reflect in Hsz. subst s.
      exists (signed_max n).
      split.
      * apply signed_max_size.
      * assert (Hsm_size : size (signed_max n) = n) by apply signed_max_size.
        rewrite bv_shr_eq_shr_n_bits
          by (rewrite Hsm_size; symmetry; exact Hs).
        unfold bv2nat_a.
        assert (Hzeros_eq : zeros n = mk_list_false (N.to_nat n)).
        { unfold zeros. reflexivity. }
        rewrite Hzeros_eq.
        unfold list2nat_be_a.
        rewrite list2N_mk_list_false.
        simpl.
        destruct (N.to_nat n) eqn:Hnn.
        --- assert (Ht_empty : t = nil).
           { unfold size in Ht.
             apply f_equal with (f := N.to_nat) in Ht.
             rewrite Nat2N.id in Ht. rewrite Hnn in Ht.
             destruct t; simpl in Ht; [reflexivity | lia]. }
           assert (Hsm_nil : signed_max n = nil).
           { unfold signed_max, smax_big_endian. rewrite Hnn. simpl. reflexivity. }
           subst t. rewrite Hsm_nil. apply bv_sle_refl.
        --- apply signed_max_is_max.
           ++ exact Ht.
           ++ lia.
    + exists (bv_not (zeros n)).
      split.
      * apply bv_not_size. apply zeros_size.
      * apply H. reflexivity.
  - intros [x [Hx Hle]] Hsne.
    eapply bv_sle_trans.
    + exact Hle.
    + apply shr_ones_is_max_sle; assumption.
Qed.


(*------------------------------------------------------------*)


(*--------------------Logical right shift 2--------------------*)


(* (exists x, s >> x = t) <=> (exists i, s >> i = t) *)
Theorem bvshr_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (i : nat), 
      ((bv_shr s (nat2bv i (size s))) = t))
    (exists (x : bitvector), (size x = n) /\ bv_shr s x = t).
Proof. split; intros.
       - destruct H1 as (i, H1).
         exists (nat2bv i (size s)). split.
         unfold size in *. rewrite H.
         now rewrite length_nat2bv, N2Nat.id.
         easy.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         case_eq (N.to_nat (list2N x) =? 0); intros.
         rewrite bv_shr_eq in H2.
         unfold bv_shr_a, list2nat_be_a in H2. 
         apply Nat.eqb_eq in H3.
         rewrite H, H1, N.eqb_refl, H3 in H2.
         rewrite H3. cbn.
         rewrite bv_shr_eq. unfold bv_shr_a.
         unfold size.
         rewrite length_mk_list_false, N2Nat.id, Nat2N.id, N.eqb_refl.
         unfold list2nat_be_a. cbn.
         rewrite list2N_mk_list_false. easy.
         cbn. rewrite N2Nat.id.
         unfold shr_n_bits_a in H2. unfold size in *.
         rewrite H, <- H1.
         now rewrite Nat2N.id, N2List_list2N.
Qed.


(*------------------------------------------------------------*)


(*--------------------Arithmetic right shift 1--------------------*)


(* (s <u size(s) => (t << s) >>a s = t) 
    and 
    (s >=u size(s) => (t = ~0 or t = 0)) 
      <=>
    (exists x, x >>a s = t) *)
Theorem bvashr_eq : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (((bv_ult s (nat2bv (N.to_nat (size s)) (size s))  = true) 
      ->  bv_ashr_a (bv_shl t s) s = t)
                        /\
     ((bv_ult s (nat2bv (N.to_nat (size s)) (size s)) = false) 
      ->  t = bv_not (zeros (size t)) \/ t = (zeros (size t))))
    (exists (x : bitvector), (size x = n) /\ (bv_ashr_a x s = t)).
Proof. 
  split; intros.
  - destruct H1 as (H1, H2).
    case_eq ( bv_ult s (nat2bv (N.to_nat (size s)) (size s))); intro HH.
    + exists (bv_shl t s). split.
      * erewrite bv_shl_size with (n := n); easy.
      * now apply H1.
    + specialize (H2 HH). destruct H2 as [H2 | H2].
      * exists (bv_not (zeros (size s))). split.
        { rewrite bv_not_size with (n := n); try easy.
          rewrite zeros_size; easy. }
        { unfold bv_not, bits, zeros. rewrite not_list_false_true.
          unfold bv_ashr_a. unfold size. 
          rewrite length_mk_list_true, N2Nat.id, N.eqb_refl, Nat2N.id.
          unfold ashr_aux_a, ashr_n_bits_a. rewrite bv_ult_nat in HH.
          unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
          rewrite list2N_N2List_s, N2Nat.id in HH. 
          unfold list2nat_be_a. rewrite length_mk_list_true.
          unfold size in HH. rewrite Nat2N.id in HH. rewrite HH.
          case_eq (length s); intros.
          + subst. cbn.
          assert (size t = 0%N).
          { Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.of_nat, 
                                           @BV.BVList.RAWBITVECTOR_LIST.size). }
          rewrite H in H2. cbn in H2. easy.
          + rewrite last_mk_list_true. cbn.
            unfold bv_not, bits, zeros in H2. rewrite not_list_false_true in H2.
            unfold size in H2. rewrite Nat2N.id in H2.
            assert (length t = length s).
       	   { Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                            (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                             @BV.BVList.RAWBITVECTOR_LIST.size). }
           rewrite H4, H3 in H2. now cbn in H2. easy.
          + unfold size. rewrite !N2Nat.id, !Nat2N.id. apply size_gt.
          + unfold size. rewrite !Nat2N.id. unfold nat2bv.
            rewrite length_N2list. rewrite Nat2N.id.
            now rewrite N.eqb_refl. }
      * exists (zeros (size s)). split.
        { rewrite zeros_size; easy. }
        { unfold zeros. unfold bv_ashr_a. unfold size. 
          rewrite length_mk_list_false, N2Nat.id, N.eqb_refl, Nat2N.id.
          unfold ashr_aux_a, ashr_n_bits_a. rewrite bv_ult_nat in HH.
          unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
          rewrite list2N_N2List_s, N2Nat.id in HH. 
          unfold list2nat_be_a. rewrite length_mk_list_false.
          unfold size in HH. rewrite Nat2N.id in HH. rewrite HH.
          pose proof (@last_mk_list_false (length s)).
          rewrite H3. cbn. unfold bv_not, bits, zeros in H2.
          unfold size in H2. rewrite Nat2N.id in H2.
          assert (length t = length s).
         	{ Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                           (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                            @BV.BVList.RAWBITVECTOR_LIST.size). }
           now rewrite <- H4. unfold size. rewrite !N2Nat.id, !Nat2N.id. 
           apply size_gt. unfold size. rewrite !Nat2N.id. unfold nat2bv.
           rewrite length_N2list. rewrite Nat2N.id.
           now rewrite N.eqb_refl. }
  - destruct H1 as (x, (Hx, A)). split. 
    rewrite <- A. rewrite bv_shl_eq.
    + unfold size. intro HH.
      unfold bv_ashr_a, bv_shl_a. unfold size in *.
      rewrite Hx, H, N.eqb_refl.
      specialize (@length_ashr_aux_a x s (N.to_nat n)); intro Haux.
      rewrite <- Haux, N2Nat.id, N.eqb_refl.
      rewrite length_shl_n_bits_a.
      rewrite <- Haux, N2Nat.id, N.eqb_refl. unfold ashr_aux_a.
      assert (H3: (last 
                    (shl_n_bits_a 
                      (ashr_n_bits_a x (list2nat_be_a s) (last x false)) 
                      (list2nat_be_a s)) 
                    false) =
                  (last x false)).
      { rewrite bv_ult_nat in HH. unfold nat2bv, bv2nat_a, list2nat_be_a in HH.
        rewrite list2N_N2List_s, !Nat2N.id in HH.
        unfold list2nat_be_a, ashr_n_bits_a.
        assert (length s = length x).
        { Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                         (@BV.BVList.RAWBITVECTOR_LIST.bitvector). }
        rewrite <- H1, HH. case_eq ( eqb (last x false) false); intros.
        - rewrite last_skipn_false. easy. rewrite <- H1. easy.
        - rewrite last_skipn_true. easy. rewrite <- H1. easy.
        - Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.size_gt) Reconstr.Empty.
        - rewrite Nat2N.id. unfold nat2bv. unfold size. rewrite length_N2list.
          rewrite Nat2N.id. now rewrite N.eqb_refl. } 
      now rewrite H3, ashr_n_shl_a.
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
	    Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
   + intro HH. rewrite bv_ult_nat in HH. unfold bv_ashr_a in *.
     rewrite Hx, H, N.eqb_refl in *. unfold ashr_aux_a, ashr_n_bits_a in A.
     unfold bv2nat_a in HH.
     assert ((list2nat_be_a (nat2bv (N.to_nat n) n) = length x)%nat).
     { rewrite <- Hx. unfold size. rewrite Nat2N.id. 
       unfold nat2bv, list2nat_be_a. rewrite list2N_N2List_s.
       Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                       @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                      (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                       @BV.BVList.RAWBITVECTOR_LIST.size).
       rewrite Nat.leb_le. specialize (size_gt (length x)); intro HHH.
       rewrite Nat2N.id.
	     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le) 
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                 @BV.BVList.RAWBITVECTOR_LIST.size). }
     rewrite H1 in HH. rewrite HH in A.
     case_eq (eqb (last x false) false); intros.
     * rewrite H2 in A. right. 
       Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id)
                      (@BV.BVList.RAWBITVECTOR_LIST.bitvector,
                       @BV.BVList.RAWBITVECTOR_LIST.size, 
                       @BV.BVList.RAWBITVECTOR_LIST.zeros).
     * rewrite H2 in A. left. 
       Reconstr.rcrush (@Coq.NArith.Nnat.Nat2N.id, 
                @BV.BVList.RAWBITVECTOR_LIST.bv_not_false_true) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.size, 
                @BV.BVList.RAWBITVECTOR_LIST.zeros).
     * unfold size. rewrite length_nat2bv. rewrite Nat2N.id. 
       now rewrite N.eqb_refl. 
Qed.


(* mins >>a s <s t <=> (exists x, x >>a s <s t) *)
Theorem bvashr_slt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt (bv_ashr (signed_min n) s) t = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_ashr x s) t) = true)).
Proof.
  intros n s t Hs Ht.
  split; intro A.
  + exists (signed_min n). split.
    - apply signed_min_size.
    - apply A.
  + destruct A as (x, (Hx, A)).
    assert ((bv_sle (bv_ashr (signed_min n) s) (bv_ashr x s)) = true).
    { apply (@sle_ashr n).
      + apply signed_min_size.
      + apply Hx.
      + apply Hs.
      + rewrite <- Hx.
        apply signed_min_sle.
    }
    now apply (@bv_sle_slt_trans (bv_ashr (signed_min n) s) (bv_ashr x s) t).
Qed.


(* t >=s ~(max_s >> s) <=> exists x, x >>a s <=s t *)
Theorem bvashr_sle:
  forall (n : N) (t s : bitvector), size t = n -> size s = n -> iff
      (bv_sge t (bv_not (bv_shr (signed_max n) s)) = true)
      (exists (x : bitvector),
          (size x = n) /\ (bv_sle (bv_ashr x s) t = true)).
Proof.
  intros n t s H_size_t H_size_s.
  assert (H_cases : (0 < n \/ n = 0)%N) by lia.
  destruct H_cases as [H_pos | H_zero].
  - split.
    + intro H_sge. exists (signed_min n). split.
      * apply signed_min_size.
      * rewrite <- (ashr_smin_eq_not_shr_smax H_pos H_size_s) in H_sge.
        rewrite bv_sge_iff_sle in H_sge. exact H_sge.
    + intros [x [H_size_x H_sle]]. rewrite bv_sge_iff_sle.
      rewrite <- (ashr_smin_eq_not_shr_smax H_pos H_size_s).
      pose proof (ashr_smin_is_minimal H_pos H_size_x H_size_s) as H_min_is_bottom.
      eapply bv_sle_trans.
      * exact H_min_is_bottom. 
      * exact H_sle.
  - rewrite H_zero in *.
    destruct s; [| unfold size in H_size_s; discriminate H_size_s].
    destruct t; [| unfold size in H_size_t; discriminate H_size_t].
    split.
    + intro H_sge. exists nil. split.
      * reflexivity. 
      * compute. reflexivity.
    + intros [x [H_size_x H_sle]].
      destruct x; [| unfold size in H_size_x; discriminate H_size_x].
      compute. reflexivity.
Qed.


(*------------------------------------------------------------*)


(*--------------------Arithmetic right shift 2--------------------*)


(* (exists i, s >>a i = t) <=> (exists x, s >>a x = t) *)
Theorem bvashr_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (i : nat), 
      ((bv_ashr s (nat2bv i (size s))) = t))
    (exists (x : bitvector), (size x = n) /\ (bv_ashr s x = t)).
Proof. split; intros.
       - destruct H1 as (i, H1).
         exists (nat2bv i (size s)). split.
         unfold size.
         now rewrite length_nat2bv, Nat2N.id.
         easy.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         rewrite N2Nat.id.
         unfold size in *.
         rewrite H, <- H1, Nat2N.id. now rewrite N2List_list2N.
Qed.


(* ((s <u t \/ s >=s 0) /\ t != 0) <=> (exists x, (s >>a x) <u t) *)
Theorem bvashr_ult2_ltr : forall (n : N), forall (s t : bitvector),
   (size s) = n -> (size t) = n ->
     (((bv_ult s t = true) \/ (bv_slt s (zeros (size s))) = false) /\
     (bv_eq t (zeros (size t))) = false) ->
     (exists (x : bitvector), (size x = n) /\ (bv_ult (bv_ashr_a s x) t = true)).
Proof. intros n s t Hs Ht (Ha, Hb).
        destruct Ha as [Ha | Ha].
        rewrite bv_ult_nat in *.
        exists (zeros (size s)).
        rewrite bv_ult_nat in *.
        split.
        - Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
        - unfold bv_ashr_a, ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
          unfold bv2nat_a, list2nat_be_a in Ha.
          assert (size (zeros (size s)) = n).
          Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
          rewrite H, Hs, N.eqb_refl.
          case_eq n; intros.
          + subst. assert (N.to_nat (list2N (zeros 0)) <? length s = false).
            Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
              @Coq.NArith.Nnat.Nat2N.id, @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false, 
              @BV.BVList.BITVECTOR_LIST.of_bits_size, @Coq.Arith.PeanoNat.Nat.ltb_irrefl) 
             (@BV.BVList.RAWBITVECTOR_LIST.zeros, @BV.BVList.RAWBITVECTOR_LIST.size,
              @Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
            rewrite H1.
            case_eq (eqb (last s false) false); intros.
            ++ Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                  @Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.size, 
                  @BV.BVList.RAWBITVECTOR_LIST.mk_list_true, 
                  @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a,
                  @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                  @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                  @Coq.NArith.BinNatDef.N.of_nat, 
                  @BV.BVList.RAWBITVECTOR_LIST.mk_list_false, @Coq.Init.Datatypes.length).
            ++ Reconstr.rsimple Reconstr.Empty (@Coq.NArith.BinNatDef.N.of_nat, 
                 @Coq.Init.Datatypes.length, 
                 @BV.BVList.RAWBITVECTOR_LIST.size, 
                 @Coq.Lists.List.last, @Coq.Bool.Bool.eqb, 
                 @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          + subst. assert (N.to_nat (list2N (zeros (N.pos p))) <? length s = true).
            Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0, 
                @Coq.NArith.Nnat.Nat2N.id, 
                @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                @Coq.Arith.PeanoNat.Nat.ltb_lt) 
               (@Coq.NArith.BinNatDef.N.of_nat, 
                @BV.BVList.RAWBITVECTOR_LIST.size, 
                @BV.BVList.RAWBITVECTOR_LIST.zeros, 
                @BV.BVList.RAWBITVECTOR_LIST.bitvector).
            rewrite H1. rewrite <- H0.
            case_eq (eqb (last s false) false); intros.
            ++ Reconstr.rsimple (@Coq.Init.Peano.O_S, @Coq.Lists.List.app_nil_r,
                 @Coq.NArith.Nnat.N2Nat.id, @Coq.NArith.Nnat.Nat2N.inj, 
                 @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false) 
                (@BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
                 @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                 @BV.BVList.RAWBITVECTOR_LIST.mk_list_false, 
                 @BV.BVList.RAWBITVECTOR_LIST.zeros, 
                 @Coq.Lists.List.skipn, @Coq.NArith.BinNatDef.N.of_nat, 
                 @BV.BVList.RAWBITVECTOR_LIST.bitvector).
            ++ Reconstr.rsimple (@Coq.Lists.List.app_nil_r, 
                  @Coq.NArith.Nnat.Nat2N.id, 
                  @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false) 
                 (@BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
                  @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
                  @BV.BVList.RAWBITVECTOR_LIST.mk_list_true, 
                  @BV.BVList.RAWBITVECTOR_LIST.zeros,
                  @Coq.Lists.List.skipn, 
                  @Coq.NArith.BinNatDef.N.of_nat, 
                  @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          - rewrite bv_ashr_a_size with (n := n).
            apply N.eqb_eq. easy.
            lia.
            Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
          - Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
          - assert ( (eqb (last s false) false) = true).
            { apply bv_slt_false_zeros in Ha. easy. }
            rewrite bv_slt_ult_last_eq with (d:= false) in Ha.
            rewrite bv_ult_nat in *.
            destruct (list_cases_all_false s).
            + exists (zeros (size s)).
              split.
	            Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
              rewrite H0 in *.
              rewrite bv_ult_nat in *.
              unfold bv_ashr_a, ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
              unfold bv2nat_a, list2nat_be_a in Ha.
              assert ((size (mk_list_false (length s)) =? 
                       size (zeros (size (mk_list_false (length s)))))%N = true).
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size, 
                 @Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
              rewrite H1.
              case_eq n; intros. 
              ** assert (N.to_nat (list2N (zeros (size (mk_list_false (length s))))) <?
                  length (mk_list_false (length s)) = false).
                  Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                    @BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                    @Coq.NArith.Nnat.Nat2N.id, @BV.BVList.BITVECTOR_LIST.of_bits_size)
                   (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                    @BV.BVList.RAWBITVECTOR_LIST.size, 
                    @BV.BVList.RAWBITVECTOR_LIST.zeros,
                    @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                 rewrite H3. 
                 assert (eqb (last (mk_list_false (length s)) false) false = true).
                 Reconstr.reasy Reconstr.Empty Reconstr.Empty.
                 rewrite H4.
                 Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.bv_eq_reflect,
                   @BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                   @Coq.Lists.List.length_zero_iff_nil,
                   @Coq.NArith.Nnat.Nat2N.id, 
                   @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                  (@BV.BVList.RAWBITVECTOR_LIST.size, 
                   @BV.BVList.RAWBITVECTOR_LIST.zeros, 
                   @Coq.NArith.BinNatDef.N.of_nat, 
                   @BV.BVList.RAWBITVECTOR_LIST.bitvector).
              ** assert (N.to_nat (list2N (zeros (size (mk_list_false (length s))))) <?
                  length (mk_list_false (length s)) = true).
                  Reconstr.rblast (@Coq.Arith.PeanoNat.Nat.ltb_lt, 
                    @Coq.NArith.Nnat.Nat2N.id, 
                    @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false, 
                    @BV.BVList.RAWBITVECTOR_LIST.of_bits_size,
                    @BV.BVList.BITVECTOR_LIST.of_bits_size,
                    @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) 
                   (@Coq.NArith.BinNatDef.N.of_nat, 
                    @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                    @BV.BVList.RAWBITVECTOR_LIST.size, 
                    @BV.BVList.RAWBITVECTOR_LIST.zeros).
                  rewrite H3.
                  assert (eqb (last (mk_list_false (length s)) false) false = true).
                  Reconstr.reasy Reconstr.Empty Reconstr.Empty.
                  rewrite H4.
                  assert (t <> (zeros (size t))).
                  { unfold bv_eq in Hb.
                    assert ((size (zeros (size t)))%N = n).
                    Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
                    rewrite H5, Ht, N.eqb_refl in Hb. apply List_neq in Hb.
                    Reconstr.reasy Reconstr.Empty Reconstr.Empty. }
                  unfold zeros, size. rewrite Nat2N.id. 
                  rewrite length_mk_list_false. 
                  rewrite list2N_mk_list_false. 
                  Reconstr.rblast (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                    @BV.BVList.RAWBITVECTOR_LIST.gt0_nmk_list_false, 
                    @BV.BVList.RAWBITVECTOR_LIST.skipn_nm_false, 
                    @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false, 
                    @Coq.NArith.Nnat.Nat2N.id, 
                    @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                   (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                    @Coq.NArith.BinNatDef.N.of_nat,
                    @BV.BVList.RAWBITVECTOR_LIST.zeros, 
                    @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                    @BV.BVList.RAWBITVECTOR_LIST.size, 
                    @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a).
              ** Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.bv_ashr_a_size, 
                   @BV.BVList.RAWBITVECTOR_LIST.zeros_size, 
                   @Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
            + exists (mk_list_true (N.to_nat n)). 
              split. Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true,
                       @Coq.NArith.Nnat.N2Nat.id) (@BV.BVList.RAWBITVECTOR_LIST.size).
              unfold bv_ashr_a, ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
              unfold bv2nat_a, list2nat_be_a in Ha.
              unfold size in *. rewrite Hs, length_mk_list_true, N2Nat.id, N.eqb_refl.
              case_eq n; intros.
              cbn. assert (length s = 0).
              Reconstr.rsimple Reconstr.Empty (@BV.BVList.RAWBITVECTOR_LIST.bitvector,
               @Coq.NArith.BinNatDef.N.of_nat).
              rewrite H2. rewrite H.
              Reconstr.rsimple (@Coq.Lists.List.length_zero_iff_nil) 
                (@BV.BVList.RAWBITVECTOR_LIST.mk_list_false, 
                 @BV.BVList.RAWBITVECTOR_LIST.bitvector).
              assert (N.to_nat (list2N (mk_list_true (N.to_nat (N.pos p)))) <? length s = false).
              rewrite <- H1.
              assert (length s = N.to_nat n).
              Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
                 @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
              rewrite H2. rewrite Nat.ltb_ge. rewrite pow_eqb_0.
              apply pos_powN. lia. 
              rewrite H2. rewrite H. 
              rewrite bv_ult_nat.
              assert (t <> (zeros (size t))).
              { unfold bv_eq in Hb.
                assert (size (zeros (N.of_nat (length t))) = size t).
                Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
                rewrite H3, Ht, N.eqb_refl in Hb. apply List_neq in Hb.
                Reconstr.rcrush Reconstr.Empty (@BV.BVList.RAWBITVECTOR_LIST.size). }
              Reconstr.rblast (@BV.BVList.RAWBITVECTOR_LIST.gt0_nmk_list_false, 
               @BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false, 
               @BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
               @BV.BVList.BITVECTOR_LIST.of_bits_size,
               @Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
               @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
               @Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.size, 
               @BV.BVList.RAWBITVECTOR_LIST.zeros, 
               @BV.BVList.RAWBITVECTOR_LIST.bitvector). 
             Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl, 
               @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false) 
              (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
               @BV.BVList.RAWBITVECTOR_LIST.size).
             + Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size, 
                  @Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
             + unfold zeros, size. rewrite Nat2N.id.
               rewrite last_mk_list_false. apply Bool.eqb_eq.
               rewrite H.
               easy.
Qed.

Theorem bvashr_ult2_rtl : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    (exists (x : bitvector), (size x = n) /\ (bv_ult (bv_ashr_a s x) t = true)) ->
    (((bv_ult s t = true) \/ (bv_slt s (zeros (size s))) = false) /\ 
    (bv_eq t (zeros (size t))) = false).
Proof. intros. split.
        destruct H1 as (x, (H1, H2)).
        rewrite bv_ult_nat in *.
        unfold bv_ashr_a in *.
        rewrite H, H1, N.eqb_refl in H2.
        unfold ashr_aux_a, list2nat_be_a, ashr_n_bits_a in *.
        case_eq (N.to_nat (list2N x) <? length s); intros. 
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            unfold zeros. 
            specialize (last_mk_list_false (N.to_nat (size s))); intros.
            rewrite bv_slt_ult_last_eq with (d := false); [ | now rewrite H5, H6].
            rewrite bv_ult_nat in *.
            right. unfold bv2nat_a, list2nat_be_a, size.
            now rewrite Nat2N.id, list_lt_false.
            unfold size.
            rewrite length_mk_list_false. unfold size.
            rewrite Nat2N.id. 
            Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl) (@BV.BVList.RAWBITVECTOR_LIST.size).
          + rewrite H4 in H2.
            unfold bv2nat_a, list2nat_be_a, zeros, size in *.
            rewrite Nat2N.id in *. left.
            destruct (n_cases_all (N.to_nat (list2N x))).
            * rewrite H5 in *.
              rewrite skip0 in H2.
              assert (mk_list_true 0 = nil) by easy.
              now rewrite H6, app_nil_r in H2.
            * destruct (list_cases_all_true s).
              ** rewrite H6 in H2.
                 rewrite skipn_nm in H2; [ | easy].
                 now rewrite H6.
              ** specialize (@skipn_gt (N.to_nat (list2N x)) s H5 H3 H6); intros.
                 apply Nat.ltb_lt.
                 apply Nat.ltb_lt in H2.
                 apply Nat.ltb_lt in H7.
                 lia.
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            unfold zeros. 
            specialize (last_mk_list_false (N.to_nat (size s))); intros.
            rewrite bv_slt_ult_last_eq with (d := false); [ | now rewrite H5, H6].
            rewrite bv_ult_nat in *.
            right. unfold bv2nat_a, list2nat_be_a, size.
            now rewrite Nat2N.id, list_lt_false.
            unfold size.
            rewrite length_mk_list_false. unfold size.
            rewrite Nat2N.id. 
            Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl) (@BV.BVList.RAWBITVECTOR_LIST.size).
          + rewrite H4 in H2. unfold bv_slt, slt_list.
            unfold bv2nat_a, list2nat_be_a, size in *.
            left.
            destruct (list_cases_all_true s).
            * now rewrite H5.
            * specialize (@pow_ltb s H5); intros.
              apply Nat.ltb_lt.
              apply Nat.ltb_lt in H2.
              apply Nat.ltb_lt in H6. 
              lia.
        - unfold bv_ashr_a. 
          rewrite H, H1, N.eqb_refl.
          specialize (@length_ashr_aux_a s x (N.to_nat n)); intros.
          unfold size.
          rewrite <- H3. rewrite N2Nat.id.
          Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.eqb_N)
            (@BV.BVList.RAWBITVECTOR_LIST.size).
           Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
              @BV.BVList.BITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
           Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
              @BV.BVList.BITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
        - unfold size. 
	        Reconstr.rcrush (@Coq.NArith.BinNat.N.eqb_refl) (@BV.BVList.RAWBITVECTOR_LIST.size).
        - destruct H1 as (x, (H1, H2)).
          unfold bv_eq. rewrite H0. unfold zeros, size.
          rewrite length_mk_list_false, N2Nat.id, N.eqb_refl.
          unfold bits.
          rewrite bv_ult_nat in *.
          unfold bv_ashr_a in *.
          rewrite H, H1, N.eqb_refl in H2.
          specialize (@bv2nat_gt0 t (bv2nat_a (ashr_aux_a s x)) H2); intros.
          rewrite <- H0. unfold size.
          rewrite Nat2N.id.
          now apply List_neq2 in H3.
          unfold bv_ashr_a.
          rewrite H, H1, N.eqb_refl. 
          specialize (@length_ashr_aux_a s x (N.to_nat n)); intros.
          unfold size. rewrite <- H3.
          rewrite N2Nat.id.
          Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_eq) (@BV.BVList.RAWBITVECTOR_LIST.size).
          Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
              @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
          Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
              @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
Qed.


Theorem bvashr_ult2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (((bv_ult s t = true) \/ (bv_slt s (zeros (size s)) = false)) /\ 
      (bv_eq t (zeros (size t))) = false)
    (exists (x : bitvector), (size x = n) /\ (bv_ult (bv_ashr_a s x) t = true)).
Proof. split.
      + now apply bvashr_ult2_ltr.
      + now apply bvashr_ult2_rtl.
Qed.


(* ((s <s (s >> !t)) \/ (t <u s)) <=> (exists x, (s >>a x) >u t) *)
Theorem bvashr_ugt2_ltr: forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)) ->
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_ashr_a s x) t = true)).
Proof. intros n s t Hs Ht Ha.
        destruct Ha as [Ha | Ha].
        unfold bv_shr_a in Ha.
        rewrite bv_not_size with (n := n), Hs, N.eqb_refl in Ha.
        unfold shr_n_bits_a, list2nat_be_a in Ha.
        case_eq (N.to_nat (list2N (bv_not t)) <? length s); intros.
        - rewrite H in Ha.
          case_eq (last s false); intros.
          + exists (mk_list_true (N.to_nat n)).
            split. Reconstr.rcrush (@Coq.NArith.Nnat.N2Nat.id, 
             @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
            (@BV.BVList.RAWBITVECTOR_LIST.size).
           apply bv_ult_bv_ugt.
          rewrite bv_ult_nat.
          unfold bv_ashr_a.
          assert (size (mk_list_true (N.to_nat n))%N = n).
          Reconstr.rcrush (@Coq.NArith.Nnat.N2Nat.id, 
            @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
           (@BV.BVList.RAWBITVECTOR_LIST.size).
          assert (He1: size (mk_list_true (N.to_nat n)) = n).
          Reconstr.reasy Reconstr.Empty Reconstr.Empty.
          rewrite He1, Hs, N.eqb_refl.
          unfold ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
          assert (length s = N.to_nat n). 
          Reconstr.reasy (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
           @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
          (@BV.BVList.RAWBITVECTOR_LIST.size,
           @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          rewrite H2.
          assert (N.to_nat (list2N (mk_list_true (N.to_nat n))) <? N.to_nat n = false).
          { case_eq (N.to_nat n); intros.
            - now cbn.
            - rewrite pow_eqb_0.
              apply Nat.ltb_ge. rewrite <- H3. 
              apply pos_powN. lia.
          } 
          rewrite H3.
          case_eq (last s false); intros.
          ** assert (eqb true false = false) by easy.
             rewrite H5.
             destruct (list_cases_all_true t).
             ++ rewrite H6 in Ha.
                assert ((N.to_nat (list2N (bv_not (mk_list_true (length t))))) = 0).
                Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                   @Coq.NArith.Nnat.Nat2N.id, 
                   @BV.BVList.RAWBITVECTOR_LIST.bv_not_true_false) 
                  (@Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                rewrite H7 in Ha.
                assert ((skipn 0 s ++ mk_list_false 0) = s).
                Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.skip0, @Coq.Lists.List.app_nil_r,
                  @Coq.Init.Peano.O_S) (@BV.BVList.RAWBITVECTOR_LIST.mk_list_false,
                  @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                rewrite H8 in Ha.
                rewrite bv_slt_nrefl in Ha. easy.
            ++ Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id, 
                 @BV.BVList.RAWBITVECTOR_LIST.skipn_same_mktr, 
                 @BV.BVList.RAWBITVECTOR_LIST.pow_ltb) 
                (@BV.BVList.RAWBITVECTOR_LIST.size, 
                 @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
                 @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
                 @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          ** rewrite bv_slt_ult_last_eq with (d := false) in Ha.
             rewrite bv_ult_nat in Ha.
             Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false, 
               @BV.BVList.RAWBITVECTOR_LIST.bv2nat_gt0) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
             Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl, 
              @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false) 
             (@BV.BVList.RAWBITVECTOR_LIST.size).
             Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.last_mk_list_false) 
              Reconstr.Empty.
          ** rewrite bv_ashr_a_size with (n := n).
             now rewrite Ht, N.eqb_refl.
             easy.
             Reconstr.rsimple (@Coq.NArith.Nnat.N2Nat.id, 
               @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
              (@BV.BVList.RAWBITVECTOR_LIST.size).
          + rewrite bv_slt_ult_last_eq with (d := false) in Ha.
            rewrite bv_ult_nat in Ha.
            destruct (list_cases_all_false s).
            * rewrite H1 in Ha. 
              Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.list_lt_false, 
                @BV.BVList.RAWBITVECTOR_LIST.skipn_nm_false) 
               (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                @BV.BVList.RAWBITVECTOR_LIST.bitvector,
                @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a).
            * destruct (n_cases_all (N.to_nat (list2N (bv_not t)))).
              rewrite H2 in Ha. 
              assert ((skipn 0 s ++ mk_list_false 0) = s).
              Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.skip0, 
                @Coq.Lists.List.app_nil_r, @Coq.Lists.List.length_zero_iff_nil,
                @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
              rewrite H3 in Ha. 
              Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.ltb_irrefl) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
              specialize (@skipn_lt (N.to_nat (list2N (bv_not t))) s H2 H H1); intros.
              unfold bv2nat_a, list2nat_be_a in Ha.
              apply Nat.ltb_lt in H3.
              apply Nat.ltb_lt in Ha. lia.
            * unfold size. rewrite length_app.
              rewrite length_skipn. rewrite length_mk_list_false.
              rewrite N.eqb_eq. Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.lt_le_incl,
                @Coq.Arith.PeanoNat.Nat.ltb_lt, 
                @Coq.Arith.PeanoNat.Nat.sub_add) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a).
            * destruct (n_cases_all_gt ((N.to_nat (list2N (bv_not t))))).
              ** rewrite H1. 
                 Reconstr.reasy (@Coq.Lists.List.app_nil_r) 
                   (@BV.BVList.RAWBITVECTOR_LIST.mk_list_false, 
                    @Coq.Lists.List.skipn, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
              ** rewrite last_append.
                 Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.last_mk_list_false) 
                   (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
                 Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0, 
                   @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false, 
                   @Coq.Lists.List.length_zero_iff_nil, 
                   @Coq.Arith.PeanoNat.Nat.ltb_lt) 
                  (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
        - rewrite H in Ha.
          exists (mk_list_true (N.to_nat n)).
          split. Reconstr.rcrush (@Coq.NArith.Nnat.N2Nat.id, 
             @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
            (@BV.BVList.RAWBITVECTOR_LIST.size).
          apply bv_ult_bv_ugt.
          rewrite bv_ult_nat.
          unfold bv_ashr_a.
          assert (size (mk_list_true (N.to_nat n))%N = n).
          Reconstr.rcrush (@Coq.NArith.Nnat.N2Nat.id, 
            @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
           (@BV.BVList.RAWBITVECTOR_LIST.size).
          rewrite H0, Hs, N.eqb_refl.
          unfold ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
          assert (length s = N.to_nat n). 
          Reconstr.reasy (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
           @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
          (@BV.BVList.RAWBITVECTOR_LIST.size,
           @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          rewrite H1.
          assert (N.to_nat (list2N (mk_list_true (N.to_nat n))) <? N.to_nat n = false).
          { case_eq (N.to_nat n); intros.
            - now cbn.
            - rewrite pow_eqb_0.
              apply Nat.ltb_ge. rewrite <- H2. 
              apply pos_powN. lia.
          } 
          rewrite H2.
          case_eq (last s false); intros.
          ** assert (eqb true false = false) by easy.
             rewrite H4.
             destruct (list_cases_all_true t).
             ++ rewrite H5 in H.
                unfold bv_not, bits in H.
                destruct (n_cases_all_gt (N.to_nat n)).
                *** assert ( (length t) = N.to_nat n).
                    Reconstr.rsimple (@Coq.Lists.List.length_zero_iff_nil)
                      (@Coq.Lists.List.last, 
                       @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                    assert ( (length s) = N.to_nat n).
                    Reconstr.rsimple (@Coq.Lists.List.length_zero_iff_nil)
                      (@Coq.Lists.List.last, 
                       @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                    rewrite H7, H8 in H.
                    assert (list2N (map negb (mk_list_true (N.to_nat n)))%N = 0%N).
                    Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                      @BV.BVList.RAWBITVECTOR_LIST.not_list_true_false) Reconstr.Empty.
                    rewrite H9 in H.
                    rewrite H8, H6 in Ha. cbn in Ha.
                    assert (s = nil). 
	                  Reconstr.rsimple Reconstr.Empty 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector, @Coq.Init.Datatypes.length).
                    subst. easy.
                *** assert ( (length t) = N.to_nat n).
                    Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                      (@BV.BVList.RAWBITVECTOR_LIST.size,
                       @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                    assert ( (length s) = N.to_nat n).
                    Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                      (@BV.BVList.RAWBITVECTOR_LIST.size,
                       @BV.BVList.RAWBITVECTOR_LIST.bitvector).
                    rewrite H7, H8 in H.
                    assert (list2N (map negb (mk_list_true (N.to_nat n)))%N = 0%N).
                    Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false,
                      @BV.BVList.RAWBITVECTOR_LIST.not_list_true_false) Reconstr.Empty.
                    rewrite H9 in H. 
                    Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                      (@Coq.Init.Datatypes.negb, @Coq.NArith.BinNatDef.N.of_nat).
             ++ Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.skipn_same_mktr, 
                  @Coq.NArith.Nnat.Nat2N.id, 
                  @BV.BVList.RAWBITVECTOR_LIST.pow_ltb) 
                 (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
                  @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a,
                  @BV.BVList.RAWBITVECTOR_LIST.size, 
                  @BV.BVList.RAWBITVECTOR_LIST.bitvector).
          ** rewrite bv_slt_ult_last_eq with (d := false) in Ha.
             rewrite bv_ult_nat in Ha.
             Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false, 
               @BV.BVList.RAWBITVECTOR_LIST.bv2nat_gt0) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
             Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl, 
              @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false) 
             (@BV.BVList.RAWBITVECTOR_LIST.size).
             Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.last_mk_list_false) 
              Reconstr.Empty.
          ** rewrite bv_ashr_a_size with (n := n).
             now rewrite Ht, N.eqb_refl.
             easy.
             Reconstr.rsimple (@Coq.NArith.Nnat.N2Nat.id, 
               @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true) 
              (@BV.BVList.RAWBITVECTOR_LIST.size).
        - easy.
        - exists (zeros n). split.
          Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.zeros_size) Reconstr.Empty.
          apply bv_ult_bv_ugt.
          unfold bv_ashr_a. rewrite zeros_size, Hs, N.eqb_refl.
          unfold ashr_aux_a, ashr_n_bits_a, list2nat_be_a.
          assert (N.to_nat (list2N (zeros n)) = 0).
          Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.list2N_mk_list_false, 
            @Coq.NArith.Nnat.Nat2N.id) 
           (@Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.zeros).
          rewrite H.
          destruct (n_cases_all_gt (N.to_nat n)).
          ++ assert (length s = N.to_nat n).
             Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
               @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
              (@BV.BVList.RAWBITVECTOR_LIST.size,
               @BV.BVList.RAWBITVECTOR_LIST.bitvector).
             rewrite H1, H0. simpl.
             assert (t = nil). unfold size in Ht. subst.
             Reconstr.ryelles4 (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
              @BV.BVList.BITVECTOR_LIST.of_bits_size) 
             (@Coq.Init.Datatypes.length, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
             rewrite H2. 
             Reconstr.reasy Reconstr.Empty (@BV.BVList.RAWBITVECTOR_LIST.bv_ult,
               @BV.BVList.RAWBITVECTOR_LIST.bitvector, @Coq.Init.Datatypes.length).
          ++ assert (0 <? length s = true). 
             Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
               @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
              (@BV.BVList.RAWBITVECTOR_LIST.size, 
               @BV.BVList.RAWBITVECTOR_LIST.bitvector).
             rewrite H1.
             Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.length_mk_list_false, 
                 @Coq.Lists.List.app_nil_r, 
                 @Coq.Lists.List.length_zero_iff_nil) 
                (@BV.BVList.RAWBITVECTOR_LIST.mk_list_true, 
                 @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                 @Coq.Lists.List.skipn).
Qed.

Theorem bvashr_ugt2_rtl: forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_ashr_a s x) t = true)) ->
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)).
Proof. intros.
        destruct H1 as (x, (H1, H2)).
        apply bv_ugt_bv_ult in H2.
        rewrite bv_ult_nat in *.
        unfold bv_ashr_a in H2.
        rewrite H, H1, N.eqb_refl in H2.
        unfold ashr_aux_a, list2nat_be_a, ashr_n_bits_a, bv_not in H2.
        case_eq (N.to_nat (list2N x) <? length s); intros.
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            destruct (n_cases_all (N.to_nat (list2N x))).
            * rewrite H6 in *.
              rewrite skip0 in H2.
              assert (mk_list_false 0 = nil) by easy.
              rewrite H7, app_nil_r in H2. now right.
            * destruct (list_cases_all_false s).
              ** rewrite H7 in H2.
                 rewrite skipn_nm_false in H2; [ | easy].
                 rewrite H7. now right.
              ** specialize (@skipn_lt (N.to_nat (list2N x)) s H6 H3 H7); intros.
                 right.
                 apply Nat.ltb_lt.
                 apply Nat.ltb_lt in H2.
                 apply Nat.ltb_lt in H8.
                 unfold bv2nat_a, list2nat_be_a in *.
                 lia.
          + rewrite H4 in H2. left.
            unfold bv2nat_a, list2nat_be_a in *.
            rewrite bv_slt_tf. easy.
            unfold bv_shr_a, size.
            assert ((length s) = (length (bv_not t))).
            unfold bv_not, bits.
            Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.not_list_length, 
               @Coq.NArith.Nnat.Nat2N.id) 
              (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
               @BV.BVList.RAWBITVECTOR_LIST.size).
            rewrite <- H5, N.eqb_refl.
            Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a)
              (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
            destruct ((last s false)); intros; cbn in H4; easy.
            destruct (list_cases_all_true t).
            * rewrite H5 in H2.
              assert (length (skipn (N.to_nat (list2N x)) s ++ 
                             mk_list_true (N.to_nat (list2N x))) =
                      length t). 
              Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.length_skipn,
                @Coq.Arith.PeanoNat.Nat.ltb_lt, 
                @Coq.NArith.Nnat.Nat2N.id, 
                @Coq.Lists.List.length_app, 
                @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true, 
                @Coq.Arith.PeanoNat.Nat.sub_add, 
                @Coq.Arith.PeanoNat.Nat.lt_le_incl) 
               (@BV.BVList.RAWBITVECTOR_LIST.size, 
                @BV.BVList.RAWBITVECTOR_LIST.bitvector).
              rewrite <- H6 in H2.
              now rewrite pow_ltb_false in H2.
            *
              apply mk_list_false_not_true in H5.
              specialize (@not_mk_list_false (bv_not t)); intros.
              assert ((length (bv_not t)) = length t).
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length) 
               (@BV.BVList.RAWBITVECTOR_LIST.bits,
                @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.bv_not).
              rewrite H7 in H6.
              specialize (H6 H5).
              eapply last_bv_ashr_gt0 with (s:= s) in H6.
              easy.
              Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size)
               Reconstr.Empty.
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            unfold bv2nat_a, list2nat_be_a in H2.
            rewrite list2N_mk_list_false in H2. easy.
          + rewrite H4 in H2.
            destruct (list_cases_all_true t).
            * rewrite H5 in H2.
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.skipn_same_mktr, 
                @BV.BVList.RAWBITVECTOR_LIST.skipn_gt_false, 
                @Coq.NArith.Nnat.Nat2N.id) 
               (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
                @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
                @BV.BVList.RAWBITVECTOR_LIST.bitvector,
                @BV.BVList.RAWBITVECTOR_LIST.size).
            * apply mk_list_false_not_true in H5.
              specialize (@not_mk_list_false (bv_not t)); intros.
              assert ((length (bv_not t)) = length t).
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length) 
               (@BV.BVList.RAWBITVECTOR_LIST.bits,
                @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.bv_not).
              rewrite H7 in H6.
              specialize (H6 H5).
              eapply last_bv_ashr_gt0 with (s:= s) in H6.
              left. rewrite bv_slt_tf. easy.
              unfold bv_shr_a, size.
              assert ((length s) = (length (bv_not t))).
              unfold bv_not, bits.
              Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.not_list_length, 
                 @Coq.NArith.Nnat.Nat2N.id) 
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                 @BV.BVList.RAWBITVECTOR_LIST.size).
              rewrite <- H8, N.eqb_refl.
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a)
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
              destruct ((last s false)); intros; cbn in H4; easy.
              easy.
              Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size) 
                Reconstr.Empty.
        - unfold bv_ashr_a. rewrite H, H1, N.eqb_refl.
          unfold size in *.
          specialize (@length_ashr_aux_a s x (N.to_nat n)); intros.
          unfold size. rewrite <- H3.
          rewrite N2Nat.id. now rewrite H0, N.eqb_refl.
          Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
              @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
          Reconstr.rcrush (@BV.BVList.BITVECTOR_LIST.of_bits_size, 
              @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
        - now rewrite H, H0, N.eqb_refl. 
Qed.


Theorem bvashr_ugt2: forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true))
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_ashr_a s x) t = true)).
Proof. split.
       + now apply bvashr_ugt2_ltr.
       + now apply bvashr_ugt2_rtl.
Qed.


(* (s <u min(s) \/ t >= s) <=> s >>a x <= t *)
Theorem bvashr_ule2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_ult s (signed_min n) = true) \/ (bv_uge t s = true))
    (exists (x : bitvector), (size x) = n /\ 
      bv_ule (bv_ashr s x) t = true).
Proof.
  intros n s t Hs Ht. split.
  + intros H. destruct H.
    - pose proof (@ult_b_signed_min_implies_positive_sign s n Hs H)
      as signb. exists (nat2bv (length s) (size s)). split.
      * rewrite nat2bv_size. apply Hs.
      * rewrite bv_ashr_eq. unfold size in Hs, Ht. 
        apply N2Nat.inj_iff in Hs. apply N2Nat.inj_iff in Ht.
        rewrite Nat2N.id in Hs, Ht.
        case s in *.
        ++ rewrite bvashr_nil. simpl in Hs. rewrite <- Hs in Ht. 
           apply length_zero_iff_nil in Ht. rewrite Ht. 
           apply bv_ule_refl.
        ++ rewrite (@ashr_size_sign0 (b :: s) signb). unfold zeros.
           unfold size. rewrite Nat2N.id. rewrite Hs. rewrite <- Ht. 
           apply bv_ule_0.
    - exists (zeros n). split.
      * apply zeros_size.
      * rewrite <- Hs. rewrite bv_ashr_eq. rewrite bvashr_zero. 
        apply bv_uge_bv_ule in H. apply H.
  + intros H. destruct H as (x, (Hx, H)).
    destruct (@sign_0_or_1 s).
    - unfold size in Hs, Ht. apply N2Nat.inj_iff in Hs.
      apply N2Nat.inj_iff in Ht. rewrite Nat2N.id in Hs, Ht. 
      case s in *.
      * simpl in Hs. rewrite <- Hs in Ht. 
        apply length_zero_iff_nil in Ht. rewrite Ht.
        right. apply bv_uge_refl.
      * left. rewrite <- (@N2Nat.id n). case (N.to_nat n) in *.
        ++ now contradict Hs.
        ++ unfold signed_min. rewrite Nat2N.id.
           unfold bv_ult. unfold size. rewrite Hs.
           rewrite length_smin_big_endian. rewrite N.eqb_refl.
           unfold ult_list. rewrite rev_involutive.
           assert (smin_big_endian (S n0) = 
                   true :: (mk_list_false n0)) by easy.
           rewrite H1. rewrite <- hd_rev in H0.
           rewrite <- length_rev in Hs.
           case (rev (b :: s)) in *.
           -- now contradict Hs.
           -- assert (hd false (b0 :: l) = false -> b0 = false) by easy.
              apply H2 in H0. rewrite H0. simpl. case l; 
              case (mk_list_false n0); easy.
    - apply bv_ule_bv_uge in H. right. rewrite <- Hs in Hx. 
      pose proof (@negative_bv_implies_bv_ashr_uge s x Hx H0).
      rewrite bv_ashr_eq in H. 
      apply (@bv_uge_list_trans t (bv_ashr_a s x) s H H1).
Qed.


(* s >=u ~s \/ s >= t <=> s >>a x >= t *)  
Theorem bvashr_uge2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_uge s (bv_not s) = true) \/ (bv_uge s t = true))
    (exists (x : bitvector), (size x = n) /\ (bv_uge (bv_ashr_a s x) t = true)).
Proof.
  intros n s t Hs Ht. split.
  + intros H. destruct H.
    - pose proof (@uge_bvnot_refl_implies_sign_neg s) as sign_s.
      exists (nat2bv (length s) (size s)). split.
      * rewrite nat2bv_size. apply Hs.
      * case s in *.
        ++ rewrite bvashr_nil. unfold size in Hs, Ht.
           simpl in Hs. rewrite <- Hs in Ht. rewrite <- N2Nat.inj_iff in Ht.
           rewrite Nat2N.id in Ht. apply length_zero_iff_nil in Ht. rewrite Ht.
           easy.
        ++ assert (b :: s <> nil) by easy. specialize (@sign_s H0 H). 
           pose proof (@ashr_size_sign1 (b :: s) sign_s) as ones.
           rewrite ones. unfold zeros. rewrite bv_not_false_true.
           rewrite Hs. rewrite <- Ht. apply ones_bv_uge_size.
    - exists (zeros n). split.
      * apply zeros_size.
      * rewrite <- Hs. rewrite bvashr_zero. apply H.
  + intros (x, (Hx, H)). destruct (@sign_0_or_1 s).
    - pose proof (@positive_bv_implies_uge_bv_ashr s x) as uge.
      rewrite Hs, Hx in uge. specialize (@uge eq_refl H0).
      right. apply (@bv_uge_list_trans s (bv_ashr_a s x) t uge H).
    - left. case s in *.
      * easy.
      * assert (b :: s <> nil) by easy.
        apply (@sign_neg_implies_uge_bvnot_refl (b :: s) H1 H0).
Qed.


(* s <s t \/ 0 <s t <=> (exists x, s >>a x <s t) *)
Theorem bvashr_slt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt s t = true) \/ (bv_slt (zeros (size t)) t = true))
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_ashr s x) t) = true)).
Proof.
  intros n s t Hs Ht.
  split; intro A.
  + case_eq (last s false); intro.
    - exists (zeros n). split.
      * apply zeros_size.
      * assert (bv_slt s t = true).
        {
         destruct A.
         + apply H0.
         + rewrite <- bv_slt_zeros in H.
           rewrite Hs in H.
           rewrite Ht in H0.
           now apply (@bv_slt_trans s (zeros n) t).
        }
        rewrite <- Hs.
        rewrite bv_ashr_eq.
        now rewrite bvashr_zero.
    - exists (nat2bv (N.to_nat n) n).
      split.
      * apply nat2bv_size.
      * assert ((bv_slt (zeros (size t)) t) = true).
        {
         destruct A.
         + rewrite Ht.
           apply (@f_equal bool bool negb) in H.
           rewrite <- bv_zeros_sle in H.
           rewrite Hs in H.
           now apply (@bv_sle_slt_trans (zeros n) s t).
         + apply H0.
        }
        rewrite bv_ashr_eq.
        rewrite <- Hs.
        unfold size at 1.
        rewrite Nat2N.id.
        rewrite ashr_size_sign0.
        ++ rewrite Hs.
           now rewrite Ht in H0.
        ++ apply H.
  + destruct A as (x, (Hx, A)).
    case_eq (last s false); intro.
    - left.
      assert ((bv_sle s (bv_ashr s x)) = true).
      {
       now apply (@bv_ashr_neg n).
      }
      now apply (@bv_sle_slt_trans s (bv_ashr s x) t).
    - right.
      rewrite Ht.
      apply (@bv_sle_slt_trans (zeros n) (bv_ashr s x) t).
      * rewrite <- (@bv_ashr_size n s x).
        ++ rewrite bv_zeros_sle.
           rewrite (@sign_bv_ashr n).
           -- now rewrite H.
           -- apply Hs.
           -- apply Hx.
        ++ apply Hs.
        ++ apply Hx.
      * apply A.
Qed.


(* t <s s & max_s /\ t <s s | max_s <=> (exists x, s >>a x >s t) *)
Theorem bvashr_sgt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt t (bv_and s (signed_max n)) = true /\
     bv_slt t (bv_or s (signed_max n)) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt t (bv_ashr s x)) = true)).
Proof.
  intros n s t Hs Ht.
  split.
  + (* Forward: LHS -> RHS *)
    intros (H1, H2).
    case_eq (last s false); intro Hsign.
    * (* s negative: bv_or s smax = ones n; witness shifts s to ones n *)
      rewrite (bv_or_neg_smax_ones Hs Hsign) in H2.
      exists (nat2bv (length s) (size s)). split.
      { rewrite nat2bv_size. exact Hs. }
      rewrite bv_ashr_eq. rewrite (ashr_size_sign1 Hsign).
      unfold ones, zeros. rewrite bv_not_false_true. rewrite Hs. exact H2.
    * (* s non-negative: bv_and s smax = s; witness zeros n shifts s to itself *)
      rewrite (bv_and_nonneg_smax_eq Hs Hsign) in H1.
      exists (zeros n). split.
      { apply zeros_size. }
      rewrite <- Hs. rewrite bv_ashr_eq. rewrite bvashr_zero. exact H1.
  + (* Backward: RHS -> LHS *)
    intros (x, (Hx, A)).
    (* When n = 0, t and bv_ashr s x are nil so bv_slt is false, contradicting A *)
    assert (Hn : (0 < N.to_nat n)%nat).
    { destruct n.
      - exfalso.
        assert (Ht_nil : t = nil).
        { apply length_zero_iff_nil. unfold size in Ht. simpl in Ht. lia. }
        assert (Hashr_nil : bv_ashr s x = nil).
        { apply length_zero_iff_nil.
          assert (H := bv_ashr_size Hs Hx). unfold size in H. simpl in H. lia. }
        rewrite Ht_nil, Hashr_nil in A. rewrite bv_slt_nrefl in A. discriminate.
      - simpl. apply Pos2Nat.is_pos. }
    case_eq (last s false); intro Hsign.
    * (* s negative *)
      pose proof (sign_bv_ashr Hs Hx) as Hsign_ashr.
      rewrite Hsign in Hsign_ashr.
      (* last (bv_and s smax) = false because last smax = false *)
      pose proof (last_signed_max_false Hn) as Hsmax_sign.
      assert (Hand_sign : last (bv_and s (signed_max n)) false = false).
      { rewrite (bv_and_comm Hs (signed_max_size n)).
        exact (pos_bvand_pos (signed_max_size n) Hs Hsmax_sign). }
      (* last t = true: if t were non-negative, bv_ashr s x <s t contradicts A *)
      assert (Ht_neg : last t false = true).
      { case_eq (last t false); intro Ht_case.
        - reflexivity.
        - exfalso.
          assert (H_size : size (bv_ashr s x) = size t).
          { rewrite (bv_ashr_size Hs Hx), Ht. reflexivity. }
          pose proof (bv_slt_tf H_size Hsign_ashr Ht_case) as Hlt.
          pose proof (bv_slt_trans A Hlt) as Hcontra.
          rewrite bv_slt_nrefl in Hcontra. discriminate. }
      split.
      { (* t <s bv_and s smax: t negative, bv_and s smax non-negative *)
        apply bv_slt_tf.
        - rewrite Ht, (bv_and_size Hs (signed_max_size n)). reflexivity.
        - exact Ht_neg.
        - exact Hand_sign. }
      { (* t <s bv_or s smax = ones n; chain t <s bv_ashr s x <=s ones n *)
        rewrite (bv_or_neg_smax_ones Hs Hsign).
        assert (Hones_sign : last (ones n) false = true).
        { unfold ones. apply last_mk_list_true. lia. }
        assert (sign_eq : last (bv_ashr s x) false = last (ones n) false).
        { rewrite Hsign_ashr. exact (eq_sym Hones_sign). }
        pose proof (ones_bv_uge_size (bv_ashr s x)) as Hones_uge.
        rewrite (bv_ashr_size Hs Hx) in Hones_uge.
        apply bv_uge_bv_ule in Hones_uge.
        assert (H_sle : bv_sle (bv_ashr s x) (ones n) = true).
        { rewrite (bv_sle_ule_same_sign (bv_ashr_size Hs Hx) (ones_size n) sign_eq).
          exact Hones_uge. }
        exact (bv_slt_sle_trans A H_sle). }
    * (* s non-negative *)
      pose proof (sign_bv_ashr Hs Hx) as Hsign_ashr_eq.
      (* bv_ashr s x <=s s since s is non-negative *)
      assert (H_ashr_sle_s : bv_sle (bv_ashr s x) s = true).
      { assert (H_size_eq : size x = size s). { rewrite Hx, Hs. reflexivity. }
        pose proof (positive_bv_implies_uge_bv_ashr (b := s) (x := x) H_size_eq Hsign) as Huge.
        rewrite <- bv_ashr_eq in Huge.
        apply bv_uge_bv_ule in Huge.
        rewrite (bv_sle_ule_same_sign (bv_ashr_size Hs Hx) Hs Hsign_ashr_eq).
        exact Huge. }
      pose proof (bv_slt_sle_trans A H_ashr_sle_s) as Ht_lt_s.
      split.
      { rewrite (bv_and_nonneg_smax_eq Hs Hsign). exact Ht_lt_s. }
      { rewrite (bv_or_pos_smax Hs Hsign).
        exact (bv_slt_sle_trans Ht_lt_s (signed_max_sle_any Hs Hn)). }
Qed.


(* t >=s 0 \/ t >=s s <=> (exists x, s >>a x <=s t) *)
Theorem bvashr_sle2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sge t (zeros n) = true \/ bv_sge t s = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_sle (bv_ashr s x) t) = true)).
Proof.
  intros n s t Hs Ht.
  rewrite (bv_sge_iff_sle t (zeros n)).
  rewrite (bv_sge_iff_sle t s).
  split.
  + intros [H | H].
    - (* bv_sle (zeros n) t: t >=s 0 *)
      case_eq (last s false); intro Hsign.
      * (* s negative: witness zeros n, ashr s 0 = s <=s t *)
        exists (zeros n). split.
        { apply zeros_size. }
        rewrite <- Hs. rewrite bv_ashr_eq. rewrite bvashr_zero.
        apply bv_sle_eq. left.
        assert (Hslt : bv_slt s (zeros n) = true).
        { rewrite <- Hs. rewrite bv_slt_zeros. exact Hsign. }
        exact (bv_slt_sle_trans Hslt H).
      * (* s non-negative: shift all the way to 0 *)
        exists (nat2bv (length s) (size s)). split.
        { rewrite nat2bv_size. exact Hs. }
        pose proof (ashr_size_sign0 Hsign) as Hshift.
        rewrite bv_ashr_eq. rewrite Hshift. rewrite Hs. exact H.
    - (* bv_sle s t: t >=s s, witness zeros n *)
      exists (zeros n). split.
      { apply zeros_size. }
      rewrite <- Hs. rewrite bv_ashr_eq. rewrite bvashr_zero.
      exact H.
  + intros (x, (Hx, A)).
    case_eq (last s false); intro Hsign.
    - (* s negative: ashr s x >=s s, so s <=s t *)
      right.
      exact (bv_sle_trans (bv_ashr_neg Hs Hx Hsign) A).
    - (* s non-negative: ashr s x >=s 0, so 0 <=s t *)
      left.
      pose proof (sign_bv_ashr Hs Hx) as Hsign_ashr.
      rewrite Hsign in Hsign_ashr.
      pose proof (bv_zeros_sle (bv_ashr s x)) as Hzero_sle.
      rewrite (bv_ashr_size Hs Hx) in Hzero_sle.
      rewrite Hsign_ashr in Hzero_sle. simpl in Hzero_sle.
      exact (bv_sle_trans Hzero_sle A).
Qed.


(*------------------------------------------------------------*)


(*--------------------------Addition--------------------------*)


(* T <=> (exists x, x + s = t) *)
Theorem bvadd : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    True
    (exists (x : bitvector), (size x = n) /\ ((bv_add x s) = t)).
Proof. 
    intros n s t Hs Ht.
    split; intro A.
    - exists (bv_subt' t s).
      split.
      + exact (bv_subt'_size Ht Hs).
      + now rewrite  (bv_add_subst_opp Ht Hs).
    - easy.
Qed.

(* Equivalent to bvadd *)
Theorem bvadd_e: forall (n : N),
  forall (s t : bitvector), (size s) = n /\ (size t) = n ->
  exists (x : bitvector), (size x) = n /\ (bv_add x s) = t.
Proof. intros n s t (Hs, Ht).
  exists (bv_subt' t s).
  split; [exact (bv_subt'_size Ht Hs) | exact (bv_add_subst_opp Ht Hs)].
Qed.


(*------------------------------------------------------------*)



(*-----------------------Multiplication-----------------------*)


(* (-s | s) & t = t <=> (exists x, x * s = t) *)
Theorem bvmult_eq : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_and (bv_or (bv_neg s) s) t = t)
    (exists (x : bitvector), (size x = n) /\ (bv_mult x s = t)).
Proof.
  intros n s t Hs Ht.
  destruct (@zeros_one_factorization s).
  + rewrite H at 1.
    rewrite bv_neg_zeros_zeros.
    rewrite (@bv_or_comm (size s)).
    - rewrite bv_or_0_neutral.
      rewrite H.
      rewrite (@bv_and_comm (size s)).
      * rewrite Hs.
        rewrite <- Ht.
        rewrite bv_and_0_absorb.
        split; intro.
        ++ exists (zeros (size t)).
           split.
           -- apply zeros_size.
           -- rewrite bv_mult_zeros_r.
              ** apply H0.
              ** apply zeros_size.
        ++ destruct H0 as (x, (H0, H1)).
           rewrite <- H1 at 2.
           now rewrite bv_mult_zeros_r.
      * apply zeros_size.
      * now rewrite Hs.
    - apply zeros_size.
    - easy.
  + destruct H as (k, (s', H)).
    apply (@iff_trans (bv_and (bv_or (bv_neg s) s) t = t)
          (exists (x : Z), ((x * pow2_int_N k) mod (pow2_int_N n) = bv2int t mod (pow2_int_N n))%Z)).
    - rewrite H.
      rewrite bv_neg_zeros_one.
      rewrite bv_or_neg_zeros_one.
      assert (n = (size s' + 1 + k)%N).
      {
        rewrite <- Hs.
        rewrite H.
        apply (@bv_concat_size (size s' + 1) k).
        + now apply (@bv_concat_size (size s') 1).
        + apply zeros_size.
      }
      rewrite bv_and_or_neg_zeros_one.
      * rewrite <- Ht.
        apply bv_and_or_neg_eq_zeros_one.
        rewrite Ht.
        rewrite H0.
        apply N.le_add_l.
      * now rewrite Ht.
    - apply (@iff_trans (exists (x : Z), ((x * pow2_int_N k) mod (pow2_int_N n) = bv2int t mod (pow2_int_N n))%Z)
            (exists (x : Z), ((x * bv2int s) mod (pow2_int_N n) = bv2int t mod (pow2_int_N n))%Z)).
      * replace (bv2int s) with (pow2_int_N k * (2 * list2int s' + 1))%Z.
        ++ apply divide_mod_pow2_int_N.
           now exists (bv2int s').
        ++ rewrite H.
           rewrite bv2int_app.
           rewrite zeros_size.
           rewrite bv2int_zeros.
           now rewrite Z.add_0_r.
      * now apply bv2int_exists_bv_mult_eq.
Qed.


(* s != 0 \/ t != 0 <=> (exists x, x * s != t) *)
Theorem bvmult_neq : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_eq s (zeros n) = false \/ bv_eq t (zeros n) = false)
    (exists (x : bitvector), (size x = n) /\ (bv_eq (bv_mult x s) t = false)).
Proof.
  intros n s t Hs Ht.
  case_eq (bv_eq t (zeros n)); intro.
  + split; intro A.
    - destruct A.
      * exists (one n).
        split.
        ++ apply one_size.
        ++ rewrite bv_mult_one_l.
           -- apply bv_eq_reflect in H.
              now rewrite H.
           -- apply Hs.
      * easy.
    - destruct A as (x, (Hx, A)).
      left.
      apply not_true_is_false.
      intro.
      apply bv_eq_reflect in H0.
      rewrite H0 in A.
      rewrite bv_mult_zeros_r in A.
      * apply bv_eq_reflect in H.
        rewrite H in A.
        now rewrite bv_eq_refl in A.
      * apply Hx.
  + split; intro A.
    - exists (zeros n).
      split.
      * apply zeros_size.
      * rewrite bv_mult_zeros_l.
        ++ apply not_true_is_false.
           intro.
           apply bv_eq_reflect in H0.
           rewrite H0 in H.
           now rewrite bv_eq_refl in H.
        ++ apply Hs.
    - now right.
Qed.


(* t <u (-s | s) <=> (exists x, x * s >u t) *)
Theorem bvmult_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_ult t (bv_or (bv_neg s) s) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_mult x s) t = true)).
Proof.
  intros n s t Hs Ht.
  split; intro A.
  + assert (exists x : bitvector, size x = n /\ bv_mult x s = bv_or (bv_neg s) s).
    {
      destruct (@bvmult_eq n s ((bv_or (bv_neg s) s))).
      + apply Hs.
      + rewrite (@bv_or_size n).
        * easy.
        * now apply bv_neg_size.
        * apply Hs.
      + apply H.
        apply bv_and_idem.
    }
    destruct H as (x, (Hx, B)).
    exists x.
    split.
    - apply Hx.
    - rewrite B.
      now apply bv_ult_bv_ugt.
  + destruct A as (x, (Hx, A)).
    apply (@bv_ult_ule_list_trans t (bv_mult x s)).
    - now apply bv_ugt_bv_ult.
    - assert (bv_and (bv_or (bv_neg s) s) (bv_mult x s) = bv_mult x s).
      {
        destruct (@bvmult_eq n s (bv_mult x s)).
        + apply Hs.
        + apply bv_mult_size.
          - apply Hx.
          - apply Hs.
        + apply H0.
          now exists x.
      }
      rewrite <- H.
      apply bv_ule_and.
      rewrite (@bv_or_size (size s)).
      * now rewrite (@bv_mult_size n).
      * now apply bv_neg_size.
      * easy.
Qed.


(* (-s | s) >=u t <=> (exists x, x * s >=u t) *)
Theorem bvmult_uge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_uge (bv_or (bv_neg s) s) t = true)
    (exists (x : bitvector), (size x = n) /\ (bv_uge (bv_mult x s) t = true)).
Proof.
  intros n s t Hs Ht.
  split; intro A.
  + assert (exists x : bitvector, size x = n /\ bv_mult x s = bv_or (bv_neg s) s).
    {
      destruct (@bvmult_eq n s ((bv_or (bv_neg s) s))).
      + apply Hs.
      + rewrite (@bv_or_size n).
        * easy.
        * now apply bv_neg_size.
        * apply Hs.
      + apply H.
        apply bv_and_idem.
    }
    destruct H as (x, (Hx, B)).
    exists x.
    split.
    - apply Hx.
    - now rewrite B.
  + destruct A as (x, (Hx, A)).
    apply (@bv_uge_list_trans (bv_or (bv_neg s) s) (bv_mult x s)).
    - assert (bv_and (bv_or (bv_neg s) s) (bv_mult x s) = bv_mult x s).
      {
        destruct (@bvmult_eq n s (bv_mult x s)).
        + apply Hs.
        + apply bv_mult_size.
          - apply Hx.
          - apply Hs.
        + apply H0.
          now exists x.
      }
      apply bv_ule_bv_uge.
      rewrite <- H.
      apply bv_ule_and.
      rewrite (@bv_or_size (size s)).
      * now rewrite (@bv_mult_size n).
      * now apply bv_neg_size.
      * easy.
    - apply A.
Qed.


(* ~(-t) & (-s | s) <s t <=> (exists x, x * s <s t) *)
Theorem bvmult_slt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_slt (bv_mult x s) t = true)
    (bv_slt (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)) t = true).
Proof.
  intros n s t Hs Ht.
  assert (HM : size (bv_or (bv_neg s) s) = n).
  { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
  assert (HA : size (bv_not (bv_neg t)) = n).
  { apply bv_not_size. apply bv_neg_size. exact Ht. }
  assert (HAM : size (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)) = n).
  { apply bv_and_size; [exact HA | exact HM]. }
  split.
  - intros (x, (Hx, Hxs)).
    pose proof (@not_signed_min_if_gt n (bv_mult x s) t (bv_mult_size Hx Hs) Ht Hxs) as H_not_min.
    pose proof (bv_not_neg_slt Ht H_not_min) as HA_lt_t.
    destruct (@zeros_one_factorization s) as [Hzeros | (k, (z, Hfact))].
    + rewrite Hzeros in Hxs.
      rewrite Hs in Hxs.
      rewrite (@bv_mult_zeros_r n x Hx) in Hxs.
      assert (H_simp : bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s) = zeros n).
      {
        pose proof (bv_neg_zeros_zeros (size s)) as H1.
        pose proof (@bv_or_0_neutral (zeros (size s))) as H2.
        rewrite zeros_size in H2.
        rewrite Hzeros, H1, H2, Hs.
        rewrite <- HA.
        apply bv_and_0_absorb.
      }
      rewrite H_simp. exact Hxs.
    + assert (H_M_eq : bv_or (bv_neg s) s = bv_concat (ones (size z + 1)) (zeros k)).
      {
        rewrite Hfact, bv_neg_zeros_one.
        apply bv_or_neg_zeros_one.
      }
      assert (H_ne : mk_list_true (N.to_nat (size z + 1)) <> nil).
      {
        rewrite N.add_1_r, N2Nat.inj_succ. simpl. discriminate.
      }
      assert (H_M_neg : bv_slt (bv_or (bv_neg s) s) (zeros n) = true).
      {
        rewrite <- HM, bv_slt_zeros, H_M_eq.
        unfold bv_concat, ones, zeros.
        rewrite (@last_append (mk_list_false (N.to_nat k))
                              (mk_list_true (N.to_nat (size z + 1))) false H_ne).
        apply last_mk_list_true.
        rewrite N.add_1_r, N2Nat.inj_succ. lia.
      }
      apply (bv_sle_slt_trans
        (@bv_and_neg_sle_itself n _ _ HA HM H_M_neg)
        HA_lt_t).
  - intro H.
    assert (H_idemp : bv_and (bv_or (bv_neg s) s)
                              (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s))
                      = bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)).
    {
      rewrite (@bv_and_comm n _ _ HM HAM).
      apply (@bv_and_idem2 _ _ n HA HM).
    }
    destruct (@bvmult_eq n s (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)) Hs HAM)
      as (Hfw, _).
    destruct (Hfw H_idemp) as (x, (Hx, Hx_eq)).
    exists x. split. exact Hx.
    rewrite Hx_eq. exact H.
Qed.


(* t <s t - ((s | t) | -s) <=> (exists x, x * s >s t) *)
Theorem bvmult_sgt: forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_slt t (bv_mult x s) = true)
    (bv_slt t (bv_subt t (bv_or (bv_or s t) (bv_neg s))) = true).
Proof.
  intros n s t Hs Ht.
  assert (HM : size (bv_or (bv_neg s) s) = n).
  { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
  assert (HMt : size (bv_or (bv_or (bv_neg s) s) t) = n).
  { apply bv_or_size; [exact HM | exact Ht]. }
  assert (Hv : size (bv_subt t (bv_or (bv_or (bv_neg s) s) t)) = n).
  { apply bv_subt_size; [exact Ht | exact HMt]. }
  assert (HMt_eq : bv_or (bv_or s t) (bv_neg s) = bv_or (bv_or (bv_neg s) s) t).
  { pose proof (bv_neg_size Hs) as Hneg.
    rewrite <- (bv_or_assoc Hs Ht Hneg).
    rewrite (bv_or_comm Ht Hneg).
    rewrite (bv_or_assoc Hs Hneg Ht).
    rewrite (bv_or_comm Hs Hneg).
    reflexivity. }
  rewrite HMt_eq. split.
  - intros (x, (Hx, Hxs)).
    destruct (@zeros_one_factorization s) as [Hzeros | (k, (z, Hfact))].
    + rewrite Hzeros, Hs in Hxs.
      rewrite (bv_mult_zeros_r Hx) in Hxs.
      assert (HM_zero : bv_or (bv_neg s) s = zeros n).
      { rewrite Hzeros, Hs, bv_neg_zeros_zeros.
        pose proof (bv_or_0_neutral (zeros n)) as H.
        rewrite zeros_size in H. exact H. }
      assert (HMt_zero : bv_or (zeros n) t = t).
      { rewrite (bv_or_comm (zeros_size n) Ht).
        pose proof (bv_or_0_neutral t) as H.
        rewrite Ht in H. exact H. }
      rewrite HM_zero, HMt_zero.
      assert (Hsubt_tt : bv_subt t t = zeros n).
      { apply list2int_inj.
        + pose proof (@size_to_length n (bv_subt t t) (bv_subt_size Ht Ht)) as Hlensubt.
          pose proof (@size_to_length n (zeros n) (zeros_size n)) as Hlenz.
          lia.
        + unfold bv_subt. rewrite N.eqb_refl.
          pose proof (@list2int_subst_list_formula t t eq_refl) as Hform.
          rewrite Z.sub_diag, Z.add_0_l in Hform.
          pose proof (zero_lt_pow2_int (length t)) as Hlt.
          rewrite Z.mod_same in Hform; [| lia].
          unfold zeros. rewrite list2int_mk_list_false.
          exact Hform. }
      rewrite Hsubt_tt. exact Hxs.
    + assert (H_M_eq : bv_or (bv_neg s) s = bv_concat (ones (size z + 1)) (zeros k)).
      { rewrite Hfact, bv_neg_zeros_one. apply bv_or_neg_zeros_one. }
      assert (Hn_eq : n = (size z + 1 + k)%N).
      { rewrite <- Hs, Hfact.
        apply (@bv_concat_size (size z + 1) k).
        + now apply (@bv_concat_size (size z) 1).
        + apply zeros_size. }
      assert (HXinM : bv_and (bv_or (bv_neg s) s) (bv_mult x s) = bv_mult x s).
      { apply (proj2 (@bvmult_eq n s (bv_mult x s) Hs (bv_mult_size Hx Hs))).
        exists x. split; [exact Hx | reflexivity]. }
      rewrite H_M_eq in HXinM.
      rewrite H_M_eq.
      exact (bvmult_sgt_fwd_key Ht (bv_mult_size Hx Hs) Hn_eq HXinM Hxs).
  - intro H.
    pose proof (bv_and_mult_subt_idemp Hs Ht) as Hidemp.
    destruct (proj1 (@bvmult_eq n s _ Hs Hv) Hidemp) as (x, (Hx, Hx_eq)).
    exists x. split. exact Hx. rewrite Hx_eq. exact H.
Qed.


(* ~(s = 0 /\ t <s s) <=> (exists x, x * s <=s t) *)
Theorem bvmult_sle : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sle (bv_mult x s) t = true)
    (~ (s = zeros n /\ bv_slt t s = true)).
Proof.
  intros n s t Hs Ht.
  split.
  - intros (x, (Hx, Hxs)) (Heqs, Hlts).
    rewrite Heqs in Hxs, Hlts.
    rewrite (bv_mult_zeros_r Hx) in Hxs.
    pose proof (bv_slt_negb_sle Ht (zeros_size n)) as Hneg.
    rewrite Hlts, Hxs in Hneg.
    discriminate.
  - intro Hcontra.
    destruct (@zeros_one_factorization s) as [Hzeros | (k, (z, Hfact))].
    + rewrite Hzeros, Hs in Hcontra.
      assert (Hlt : bv_slt t (zeros n) = false).
      { destruct (bv_slt t (zeros n)) eqn:Heq.
        - exfalso. apply Hcontra. split; reflexivity.
        - reflexivity. }
      assert (Hlast : last t false = false).
      { rewrite <- bv_slt_zeros, Ht. exact Hlt. }
      exists (zeros n). split. apply zeros_size.
      rewrite Hzeros, Hs.
      rewrite (bv_mult_zeros_r (zeros_size n)).
      exact (zeros_sle_nonneg Ht Hlast).
    + assert (HM : size (bv_or (bv_neg s) s) = n).
      { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
      assert (H_M_eq : bv_or (bv_neg s) s = bv_concat (ones (size z + 1)) (zeros k)).
      { rewrite Hfact, bv_neg_zeros_one. apply bv_or_neg_zeros_one. }
      assert (H_ne : mk_list_true (N.to_nat (size z + 1)) <> nil).
      { rewrite N.add_1_r, N2Nat.inj_succ. simpl. discriminate. }
      assert (H_M_neg : bv_slt (bv_or (bv_neg s) s) (zeros n) = true).
      { rewrite <- HM, bv_slt_zeros, H_M_eq.
        unfold bv_concat, ones, zeros.
        rewrite (@last_append (mk_list_false (N.to_nat k))
                              (mk_list_true (N.to_nat (size z + 1))) false H_ne).
        apply last_mk_list_true.
        rewrite N.add_1_r, N2Nat.inj_succ. lia. }
      assert (Hlast_M : last (bv_or (bv_neg s) s) false = true).
      { rewrite <- bv_slt_zeros, HM. exact H_M_neg. }
      assert (Hmin_in_M : bv_and (bv_or (bv_neg s) s) (signed_min n) = signed_min n).
      { apply bv_and_signed_min_neg; [exact HM | exact Hlast_M]. }
      destruct (proj1 (@bvmult_eq n s (signed_min n) Hs (signed_min_size n)) Hmin_in_M)
        as (x0, (Hx0, Hx0_eq)).
      exists x0. split. exact Hx0.
      rewrite Hx0_eq, <- Ht. exact (signed_min_sle t).
Qed.


(* (-s | s) & max_s >=s t <=> (exists x, x * s >=s t) *)
Theorem bvmult_sge: forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sge (bv_mult x s) t = true)
    (bv_sge (bv_and (bv_or (bv_neg s) s) (signed_max n)) t = true).
Proof.
  intros n s t Hs Ht.
  assert (HM : size (bv_or (bv_neg s) s) = n).
  { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
  assert (HMs : size (bv_and (bv_or (bv_neg s) s) (signed_max n)) = n).
  { apply bv_and_size; [exact HM | apply signed_max_size]. }
  split.
  - intros (x, (Hx, Hxs)).
    rewrite bv_sge_sle_equiv in Hxs |- *.
    assert (HXinM : bv_and (bv_or (bv_neg s) s) (bv_mult x s) = bv_mult x s).
    { apply (proj2 (@bvmult_eq n s (bv_mult x s) Hs (bv_mult_size Hx Hs))).
      exists x. split; [exact Hx | reflexivity]. }
    pose proof (bv_and_sle_maxs HM (bv_mult_size Hx Hs)) as Hslv.
    rewrite HXinM in Hslv.
    exact (bv_sle_trans Hxs Hslv).
  - intro H.
    rewrite bv_sge_sle_equiv in H.
    assert (HMMs : bv_and (bv_or (bv_neg s) s) (bv_and (bv_or (bv_neg s) s) (signed_max n))
                  = bv_and (bv_or (bv_neg s) s) (signed_max n)).
    { rewrite (bv_and_assoc HM HM (signed_max_size n)).
      rewrite bv_and_idem. reflexivity. }
    destruct (proj1 (@bvmult_eq n s _ Hs HMs) HMMs) as (x, (Hx, Hx_eq)).
    exists x. split. exact Hx.
    rewrite bv_sge_sle_equiv. rewrite Hx_eq. exact H.
Qed.


(*------------------------------------------------------------*)

(*-----------------------Division 1---------------------------*)

(* (s * t) / t & s = s <=> (exists x, x /u s >=u t) *)
Theorem bvudiv_uge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_uge (bv_udiv x s) t = true)
    (bv_eq
       (bv_and (bv_udiv (bv_mult s t) t) s)
       s
     = true).
Proof.
  intros n s t Hs Ht.
  assert (Hudiv00 : forall m, bv_udiv (zeros m) (zeros m) = ones m).
  { intro m. unfold bv_udiv.
    rewrite zeros_size, N.eqb_refl.
    unfold udiv_list, zeros.
    rewrite length_mk_list_false, List_eq_refl.
    unfold ones. reflexivity. }
  split.
  - intros [x [Hx Hxge]].
    destruct (bv_eq s (zeros n)) eqn:Hseq.
    + apply bv_eq_reflect in Hseq. subst s.
      rewrite bv_mult_zeros_l; [| exact Ht].
      pose proof (bv_udiv_size (zeros_size n) Ht) as Hdiv_sz.
      rewrite <- Hdiv_sz at 2. rewrite bv_and_0_absorb, Hdiv_sz. apply bv_eq_refl.
    + destruct (bv_eq t (zeros n)) eqn:Hteq.
      * apply bv_eq_reflect in Hteq. subst t.
        rewrite bv_mult_zeros_r; [| exact Hs].
        rewrite Hudiv00, (bv_and_comm (ones_size n) Hs), <- Hs, bv_and_1_neutral. apply bv_eq_refl.
      * assert (Hsne : s <> zeros n).
        { intro H. rewrite (proj2 (bv_eq_reflect _ _) H) in Hseq. discriminate. }
        assert (Htne : t <> zeros n).
        { intro H. rewrite (proj2 (bv_eq_reflect _ _) H) in Hteq. discriminate. }
        set (S := bv2nat_a s). set (T := bv2nat_a t). set (X := bv2nat_a x).
        assert (HS_pos : (0 < S)%nat) by exact (zeros_bv2nat_a_pos Hs Hseq).
        assert (HT_pos : (0 < T)%nat) by exact (zeros_bv2nat_a_pos Ht Hteq).
        assert (Hszeq : (size (bv_udiv x s) =? size t)%N = true).
        { rewrite (bv_udiv_size Hx Hs), Ht. apply N.eqb_refl. }
        apply bv_uge_implies_not_bv_ult in Hxge.
        rewrite bv_ult_nat in Hxge; [| exact Hszeq]. apply Nat.ltb_ge in Hxge.
        rewrite (bv2nat_a_udiv_nonzero Hx Hs Hsne) in Hxge.
        assert (HXge : (S * T <= X)%nat).
        { apply Nat.le_trans with (m := S * (X / S)).
          - apply Nat.mul_le_mono_l. exact Hxge.
          - apply Nat.Div0.mul_div_le. }
        assert (HST_lt : (S * T < 2^(N.to_nat n))%nat).
        { exact (Nat.le_lt_trans _ _ _ HXge (bv2nat_a_lt_pow2 Hx)). }
        pose proof (bv_mult_size Hs Ht) as Hst_sz.
        pose proof (bv2nat_a_mult_mod Hs Ht) as Hmult_eq.
        rewrite Nat.mod_small in Hmult_eq; [| exact HST_lt].
        pose proof (bv2nat_a_udiv_nonzero Hst_sz Ht Htne) as Hdiv_eq.
        rewrite Hmult_eq, Nat.div_mul in Hdiv_eq; [| lia].
        rewrite (bv2nat_a_inj (bv_udiv_size Hst_sz Ht) Hs Hdiv_eq).
        rewrite bv_and_idem. apply bv_eq_refl.
  - intro Hrhs. apply bv_eq_reflect in Hrhs.
    destruct (bv_eq s (zeros n)) eqn:Hseq.
    + apply bv_eq_reflect in Hseq. subst s.
      exists (zeros n). split; [exact (zeros_size n) |].
      rewrite Hudiv00, <- Ht. apply ones_bv_uge_size.
    + destruct (bv_eq t (zeros n)) eqn:Hteq.
      * apply bv_eq_reflect in Hteq. subst t.
        exists (zeros n). split; [apply zeros_size |].
        apply bv_uge_zeros. apply bv_udiv_size; [apply zeros_size | exact Hs].
      * assert (Hsne : s <> zeros n).
        { intro H. rewrite (proj2 (bv_eq_reflect _ _) H) in Hseq. discriminate. }
        assert (Htne : t <> zeros n).
        { intro H. rewrite (proj2 (bv_eq_reflect _ _) H) in Hteq. discriminate. }
        set (S := bv2nat_a s). set (T := bv2nat_a t).
        assert (HS_pos : (0 < S)%nat) by exact (zeros_bv2nat_a_pos Hs Hseq).
        assert (HT_pos : (0 < T)%nat) by exact (zeros_bv2nat_a_pos Ht Hteq).
        pose proof (bv_mult_size Hs Ht) as Hst_sz.
        assert (Hdiv_sz := bv_udiv_size Hst_sz Ht).
        assert (Hule : bv_ule s (bv_udiv (bv_mult s t) t) = true).
        { rewrite <- Hrhs at 1. apply bv_ule_and. rewrite Hdiv_sz, Hs. reflexivity. }
        apply bv_ule_bv_uge in Hule.
        apply bv_uge_implies_not_bv_ult in Hule.
        assert (Hszs : (size (bv_udiv (bv_mult s t) t) =? size s)%N = true).
        { rewrite Hdiv_sz, Hs. apply N.eqb_refl. }
        rewrite bv_ult_nat in Hule; [| exact Hszs].
        apply Nat.ltb_ge in Hule.
        rewrite (bv2nat_a_udiv_nonzero Hst_sz Ht Htne) in Hule.
        change (bv2nat_a s) with S in Hule. change (bv2nat_a t) with T in Hule.
        pose proof (bv2nat_a_mult_mod Hs Ht) as Hmult_eq.
        set (M := bv2nat_a (bv_mult s t)) in *.
        assert (Hdiv_le : (M / T <= S)%nat).
        { apply Nat.le_trans with (m := S * T / T).
          - apply Nat.Div0.div_le_mono. rewrite Hmult_eq. apply Nat.Div0.mod_le.
          - rewrite Nat.div_mul; lia. }
        assert (Hdiv_eq : (M / T = S)%nat) by lia.
        assert (HST_le : (S * T <= M)%nat).
        { rewrite <- Hdiv_eq, Nat.mul_comm. apply Nat.Div0.mul_div_le. }
        assert (HM_eq : (M = S * T)%nat).
        { rewrite Hmult_eq. apply Nat.mod_small.
          exact (Nat.le_lt_trans _ _ _ HST_le (bv2nat_a_lt_pow2 Hst_sz)). }
        exists (bv_mult s t). split; [exact Hst_sz |].
        assert (Hdivs_sz := bv_udiv_size Hst_sz Hs).
        apply not_bv_ult_implies_bv_uge; [rewrite Hdivs_sz, Ht; reflexivity |].
        rewrite bv_ult_nat; [| rewrite Hdivs_sz, Ht; apply N.eqb_refl].
        apply Nat.ltb_ge.
        rewrite (bv2nat_a_udiv_nonzero Hst_sz Hs Hsne).
        change (bv2nat_a (bv_mult s t)) with M. change (bv2nat_a s) with S.
        rewrite HM_eq, Nat.mul_comm, Nat.div_mul; [lia | lia].
Qed.

(*------------------------------------------------------------*)

(*-----------------------Division 2---------------------------*)

(* n = 1 -> s & t = 0 ; otherwise True <=> (exists x, s /u x != t) *)
Theorem bvudiv_reverse_neq : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_eq (bv_udiv s x) t = false)
    (if N.eq_dec n 1 then
       bv_eq (bv_and s t) (zeros n) = true
     else
       (0 < n)%N).
Proof.
  intros n s t Hs Ht.
  destruct (N.eq_dec n 1) as [Hn1 | Hn1].
  { split.
    - intros [x [Hx Hneq]].
      rewrite Hn1 in Hs, Ht, Hx |- *.
      pose proof (size_to_length Hs) as Hls. simpl in Hls.
      pose proof (size_to_length Ht) as Hlt. simpl in Hlt.
      pose proof (size_to_length Hx) as Hlx. simpl in Hlx.
      destruct s as [| bs [| ? ?]]; [discriminate | | simpl in Hls; lia].
      destruct t as [| bt [| ? ?]]; [discriminate | | simpl in Hlt; lia].
      destruct x as [| bx [| ? ?]]; [discriminate | | simpl in Hlx; lia].
      destruct bs, bt, bx; vm_compute in Hneq |- *; try discriminate; try reflexivity.
    - intro Hst.
      rewrite Hn1 in Hs, Ht, Hst |- *.
      pose proof (size_to_length Hs) as Hls. simpl in Hls.
      pose proof (size_to_length Ht) as Hlt. simpl in Hlt.
      destruct s as [| bs [| ? ?]]; [discriminate | | simpl in Hls; lia].
      destruct t as [| bt [| ? ?]]; [discriminate | | simpl in Hlt; lia].
      destruct bs, bt; try (vm_compute in Hst; discriminate).
      + exists (zeros 1). split; [apply zeros_size |]. vm_compute. reflexivity.
      + exists (ones 1). split; [apply ones_size |]. vm_compute. reflexivity.
      + exists (zeros 1). split; [apply zeros_size |]. vm_compute. reflexivity. }
  { split.
    - intros [x [Hx Hneq]].
      destruct (N.eq_dec n 0) as [Hn0 | Hn0].
      + exfalso.
        rewrite Hn0 in Hs, Ht, Hx.
        pose proof (size_to_length Hs) as Hls. simpl in Hls.
        pose proof (size_to_length Ht) as Hlt. simpl in Hlt.
        pose proof (size_to_length Hx) as Hlx. simpl in Hlx.
        apply length_zero_iff_nil in Hls, Hlt, Hlx. subst s t x.
        vm_compute in Hneq. discriminate.
      + lia.
    - intro Hn_pos.
      assert (Hn2 : (2 <= n)%N) by lia.
      destruct (bv_eq (ones n) t) eqn:Hteq.
      + apply bv_eq_reflect in Hteq. subst t.
        exists (ones n). split; [apply ones_size |].
        apply Bool.not_true_is_false. intro Heq. apply bv_eq_reflect in Heq.
        apply (f_equal bv2nat_a) in Heq.
        assert (H2n_ge : (2 < 2^(N.to_nat n))%nat).
        { assert (H2n : (2 <= N.to_nat n)%nat).
          { assert (Hn_eq : (n = 2 + (n - 2))%N) by lia.
            rewrite Hn_eq, N2Nat.inj_add. simpl. lia. }
          destruct (N.to_nat n) as [| [| k]]; [lia | lia |].
          simpl.
          assert (Hpow_k : (1 <= 2^k)%nat).
          { assert (H2ne : (2 <> 0)%nat) by lia.
            pose proof (Nat.pow_nonzero 2 k H2ne) as Hne. lia. }
          lia. }
        assert (Hones_ne_zeros : ones n <> zeros n).
        { intro H. apply (f_equal bv2nat_a) in H.
          rewrite bv2nat_a_ones, bv2nat_a_zeros_eq in H. lia. }
        rewrite (bv2nat_a_udiv_nonzero Hs (ones_size n) Hones_ne_zeros) in Heq.
        rewrite bv2nat_a_ones in Heq.
        pose proof (bv2nat_a_lt_pow2 Hs) as Hs_lt.
        destruct (lt_dec (bv2nat_a s) (2^(N.to_nat n) - 1)) as [Hlt | Hge].
        * assert (Hdiv0 : (bv2nat_a s / (2^(N.to_nat n) - 1) = 0)%nat).
          { apply Nat.div_small. lia. }
          rewrite Hdiv0 in Heq. lia.
        * assert (Hval : bv2nat_a s = 2^(N.to_nat n) - 1) by lia.
          rewrite Hval in Heq.
          assert (Hdiv1 : ((2^(N.to_nat n) - 1) / (2^(N.to_nat n) - 1) = 1)%nat).
          { apply Nat.div_same. lia. }
          rewrite Hdiv1 in Heq. lia.
      + exists (zeros n). split; [apply zeros_size |].
        rewrite bv_udiv_zeros; [| exact Hs]. exact Hteq. }
Qed.

(* n = 1 -> s >s t ; n != 1 -> ( (s >=s 0 => s >s t) /\ (s <s 0 => (s >> 1) >s t) ) 
   <=> (exists x, s /u x >s t) *)
Theorem bvudiv_reverse_sgt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sgt (bv_udiv s x) t = true)
    (if N.eq_dec n 1 then
       bv_sgt s t = true
     else
       (bv_sge s (zeros n) = true -> bv_sgt s t = true) /\
       (bv_slt s (zeros n) = true -> bv_sgt (bv_shr s (one n)) t = true)).
Proof.
  intros n s t Hs Ht.
  destruct (N.eq_dec n 1) as [Hn1 | Hn1].
  { (* n = 1: brute force on concrete single-bit bitvectors *)
    rewrite Hn1 in Hs, Ht |- *.
    pose proof (size_to_length Hs) as Hlen_s. simpl in Hlen_s.
    pose proof (size_to_length Ht) as Hlen_t. simpl in Hlen_t.
    destruct s as [| bs [| ]]; simpl in Hlen_s; [lia | | lia].
    destruct t as [| bt [| ]]; simpl in Hlen_t; [lia | | lia].
    split.
    - intros [x [Hx Hxsgt]].
      pose proof (size_to_length Hx) as Hlen_x. simpl in Hlen_x.
      destruct x as [| bx [| ]]; simpl in Hlen_x; [lia | | lia].
      destruct bs; destruct bt; destruct bx; vm_compute in *;
        try discriminate; try reflexivity.
    - intro Hrhs.
      destruct bs; destruct bt; vm_compute in Hrhs; try discriminate.
      (* Only bs=false, bt=true survives: [false] >s [true] = true *)
      exists (true :: nil). split.
      + unfold size. simpl. reflexivity.
      + vm_compute. reflexivity.
  }
  { (* n <> 1 *)
    split.
    - (* Forward: (exists x. s/x >s t) -> RHS *)
      intros [x [Hx Hsgt]].
      rewrite bv_sgt_slt_equiv in Hsgt.
      (* Hsgt : bv_slt t (bv_udiv s x) = true *)
      destruct (last s false) eqn:Hlast_s.
      + (* s < 0 (MSB = 1) *)
        assert (Hn_pos : (0 < N.to_nat n)%nat).
        { destruct (N.to_nat n) eqn:Hnt.
          - pose proof (size_to_length Hs) as Hlen_s.
            rewrite Hnt in Hlen_s. simpl in Hlen_s.
            apply length_zero_iff_nil in Hlen_s. subst s.
            simpl in Hlast_s. discriminate.
          - lia. }
        pose proof (bv_sle_udiv_shr Hs Hx Hn_pos Hlast_s) as Hsle.
        (* Hsle : bv_sle (bv_udiv s x) (bv_shr s (one n)) = true *)
        split.
        * (* bv_sge s (zeros n) = true -> bv_sgt s t: vacuous, s is negative *)
          intro Hsge.
          exfalso.
          rewrite bv_sge_sle_equiv in Hsge.
          (* Hsge : bv_sle (zeros n) s = true *)
          assert (Hzero_sle : bv_sle (zeros n) s = negb (last s false)).
          { rewrite <- Hs. exact (bv_zeros_sle s). }
          rewrite Hlast_s in Hzero_sle. simpl in Hzero_sle.
          rewrite Hsge in Hzero_sle. discriminate.
        * (* bv_slt s (zeros n) = true -> bv_sgt (bv_shr s (one n)) t *)
          intros _.
          rewrite bv_sgt_slt_equiv.
          exact (bv_slt_sle_trans Hsgt Hsle).
      + (* s >= 0 (MSB = 0) *)
        pose proof (bv_sle_udiv_nonneg Hs Hx Hlast_s) as Hsle.
        (* Hsle : bv_sle (bv_udiv s x) s = true *)
        split.
        * (* bv_sge s (zeros n) = true -> bv_sgt s t *)
          intros _.
          rewrite bv_sgt_slt_equiv.
          exact (bv_slt_sle_trans Hsgt Hsle).
        * (* bv_slt s (zeros n) = true -> ...: vacuous, s is nonneg *)
          intro Hslt.
          exfalso.
          assert (Hbslt : bv_slt s (zeros n) = false).
          { rewrite <- Hs. rewrite bv_slt_zeros. exact Hlast_s. }
          rewrite Hbslt in Hslt. discriminate.
    - (* Backward: RHS -> (exists x. s/x >s t) *)
      intro Hrhs.
      destruct Hrhs as [Hrhs1 Hrhs2].
      destruct (last s false) eqn:Hlast_s.
      + (* s < 0: witness x = nat2bv 2 n, s/2 = s>>1 *)
        assert (Hn_pos : (0 < N.to_nat n)%nat).
        { destruct (N.to_nat n) eqn:Hnt.
          - pose proof (size_to_length Hs) as Hlen_s.
            rewrite Hnt in Hlen_s. simpl in Hlen_s.
            apply length_zero_iff_nil in Hlen_s. subst s.
            simpl in Hlast_s. discriminate.
          - lia. }
        assert (Hn_ne_1 : (N.to_nat n <> 1)%nat).
        { intro Heq. apply Hn1. apply N2Nat.inj. simpl. exact Heq. }
        assert (Hn_ge_2 : (2 <= N.to_nat n)%nat) by lia.
        assert (Hslt_s : bv_slt s (zeros n) = true).
        { rewrite <- Hs. rewrite bv_slt_zeros. exact Hlast_s. }
        pose proof (Hrhs2 Hslt_s) as Hgoal.
        (* Hgoal : bv_sgt (bv_shr s (one n)) t = true *)
        assert (Hnat2bv2_sz : size (nat2bv 2 n) = n) by apply nat2bv_size.
        assert (Hnat2bv2_val : (bv2nat_a (nat2bv 2 n) = 2)%nat)
          by (apply bv2nat_a_nat2bv_two; exact Hn_ge_2).
        assert (Hnat2bv2_ne : nat2bv 2 n <> zeros n).
        { intro Heq. apply (f_equal bv2nat_a) in Heq.
          rewrite Hnat2bv2_val, bv2nat_a_zeros_eq in Heq. discriminate. }
        assert (Hudiv_val : (bv2nat_a (bv_udiv s (nat2bv 2 n)) = bv2nat_a s / 2)%nat).
        { rewrite (bv2nat_a_udiv_nonzero Hs Hnat2bv2_sz Hnat2bv2_ne).
          rewrite Hnat2bv2_val. reflexivity. }
        assert (Hshr_val : (bv2nat_a (bv_shr s (one n)) = bv2nat_a s / 2)%nat)
          by (apply bv2nat_a_shr_one; [exact Hs | exact Hn_pos]).
        assert (Heq_udiv_shr : bv_udiv s (nat2bv 2 n) = bv_shr s (one n)).
        { apply bv2nat_a_inj with (n := n).
          - exact (bv_udiv_size Hs Hnat2bv2_sz).
          - exact (bv_shr_size Hs (one_size n)).
          - rewrite Hudiv_val, Hshr_val. reflexivity. }
        exists (nat2bv 2 n). split.
        * exact Hnat2bv2_sz.
        * rewrite Heq_udiv_shr. exact Hgoal.
      + (* s >= 0: witness x = one n, s/1 = s *)
        assert (Hsge : bv_sge s (zeros n) = true).
        { rewrite bv_sge_sle_equiv.
          apply zeros_sle_nonneg; [exact Hs | exact Hlast_s]. }
        pose proof (Hrhs1 Hsge) as Hgoal.
        (* Hgoal : bv_sgt s t = true *)
        destruct (N.eq_dec n 0) as [Hn0 | Hn0].
        * (* n = 0: bv_sgt [] [] = false, contradicts Hgoal *)
          rewrite Hn0 in Hs, Ht.
          pose proof (size_to_length Hs) as Hlen_s. simpl in Hlen_s.
          pose proof (size_to_length Ht) as Hlen_t. simpl in Hlen_t.
          apply length_zero_iff_nil in Hlen_s.
          apply length_zero_iff_nil in Hlen_t.
          subst s. subst t.
          vm_compute in Hgoal. discriminate.
        * assert (Hn_pos : (0 < N.to_nat n)%nat).
          { destruct n. contradiction. simpl. lia. }
          exists (one n). split.
          -- apply one_size.
          -- rewrite (bv_udiv_one Hs Hn_pos). exact Hgoal.
  }
Qed.

(* (s >=s 0 => s >=s t) /\ (s <s 0 => s >> 1 >=s t) <=> (exists x, s /u x >=s t) *)
Theorem bvudiv_reverse_sge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sge (bv_udiv s x) t = true)
    (if N.eq_dec n 1 then
       bv_sge s t = true
     else
       (bv_sge s (zeros n) = true -> bv_sge s t = true) /\
       (bv_slt s (zeros n) = true -> bv_sge (bv_shr s (one n)) t = true)).
Proof.
  intros n s t Hs Ht.
  destruct (N.eq_dec n 1) as [Hn1 | Hn1].
  { (* n = 1: brute force on concrete single-bit bitvectors *)
    rewrite Hn1 in Hs, Ht |- *.
    pose proof (size_to_length Hs) as Hlen_s. simpl in Hlen_s.
    pose proof (size_to_length Ht) as Hlen_t. simpl in Hlen_t.
    destruct s as [| bs [| ]]; simpl in Hlen_s; [lia | | lia].
    destruct t as [| bt [| ]]; simpl in Hlen_t; [lia | | lia].
    split.
    - intros [x [Hx Hxsge]].
      pose proof (size_to_length Hx) as Hlen_x. simpl in Hlen_x.
      destruct x as [| bx [| ]]; simpl in Hlen_x; [lia | | lia].
      destruct bs; destruct bt; destruct bx; vm_compute in *;
        try discriminate; try reflexivity.
    - intro Hrhs.
      destruct bs; destruct bt; vm_compute in Hrhs; try discriminate;
        (exists (true :: nil); split;
         [unfold size; simpl; reflexivity | vm_compute; reflexivity]).
  }
  { (* n <> 1 *)
    split.
  - (* Forward: (exists x. s/x >=s t) -> RHS *)
    intros [x [Hx Hsge]].
    rewrite bv_sge_sle_equiv in Hsge.
    (* Hsge : bv_sle t (bv_udiv s x) = true *)
    destruct (last s false) eqn:Hlast_s.
    + (* s < 0 (MSB = 1) *)
      assert (Hn_pos : (0 < N.to_nat n)%nat).
      { destruct (N.to_nat n) eqn:Hnt.
        - pose proof (size_to_length Hs) as Hlen_s.
          rewrite Hnt in Hlen_s. simpl in Hlen_s.
          apply length_zero_iff_nil in Hlen_s. subst s.
          simpl in Hlast_s. discriminate.
        - lia. }
      pose proof (bv_sle_udiv_shr Hs Hx Hn_pos Hlast_s) as Hsle.
      (* Hsle : bv_sle (bv_udiv s x) (bv_shr s (one n)) = true *)
      split.
      * (* bv_sge s (zeros n) = true -> bv_sge s t: vacuous, s is negative *)
        intro Hsge_z.
        exfalso.
        rewrite bv_sge_sle_equiv in Hsge_z.
        assert (Hzero_sle : bv_sle (zeros n) s = negb (last s false)).
        { rewrite <- Hs. exact (bv_zeros_sle s). }
        rewrite Hlast_s in Hzero_sle. simpl in Hzero_sle.
        rewrite Hsge_z in Hzero_sle. discriminate.
      * (* bv_slt s (zeros n) = true -> bv_sge (bv_shr s (one n)) t *)
        intros _.
        rewrite bv_sge_sle_equiv.
        exact (bv_sle_trans Hsge Hsle).
    + (* s >= 0 (MSB = 0) *)
      pose proof (bv_sle_udiv_nonneg Hs Hx Hlast_s) as Hsle.
      (* Hsle : bv_sle (bv_udiv s x) s = true *)
      split.
      * (* bv_sge s (zeros n) = true -> bv_sge s t *)
        intros _.
        rewrite bv_sge_sle_equiv.
        exact (bv_sle_trans Hsge Hsle).
      * (* bv_slt s (zeros n) = true -> ...: vacuous, s is nonneg *)
        intro Hslt.
        exfalso.
        assert (Hbslt : bv_slt s (zeros n) = false).
        { rewrite <- Hs. rewrite bv_slt_zeros. exact Hlast_s. }
        rewrite Hbslt in Hslt. discriminate.
  - (* Backward: RHS -> (exists x. s/x >=s t) *)
    intro Hrhs.
    destruct Hrhs as [Hrhs1 Hrhs2].
    destruct (last s false) eqn:Hlast_s.
    + (* s < 0: witness x = nat2bv 2 n, s/2 = s>>1 *)
      assert (Hn_pos : (0 < N.to_nat n)%nat).
      { destruct (N.to_nat n) eqn:Hnt.
        - pose proof (size_to_length Hs) as Hlen_s.
          rewrite Hnt in Hlen_s. simpl in Hlen_s.
          apply length_zero_iff_nil in Hlen_s. subst s.
          simpl in Hlast_s. discriminate.
        - lia. }
      assert (Hslt_s : bv_slt s (zeros n) = true).
      { rewrite <- Hs. rewrite bv_slt_zeros. exact Hlast_s. }
      pose proof (Hrhs2 Hslt_s) as Hgoal.
      (* Hgoal : bv_sge (bv_shr s (one n)) t = true *)
      (* n > 0 (from last s false = true) and n <> 1, so n >= 2 *)
      assert (Hn_ne_1 : (N.to_nat n <> 1)%nat).
      { intro Heq. apply Hn1. apply N2Nat.inj. simpl. exact Heq. }
      assert (Hn_ge_2 : (2 <= N.to_nat n)%nat) by lia.
        assert (Hnat2bv2_sz : size (nat2bv 2 n) = n) by apply nat2bv_size.
        assert (Hnat2bv2_val : (bv2nat_a (nat2bv 2 n) = 2)%nat)
          by (apply bv2nat_a_nat2bv_two; exact Hn_ge_2).
        assert (Hnat2bv2_ne : nat2bv 2 n <> zeros n).
        { intro Heq. apply (f_equal bv2nat_a) in Heq.
          rewrite Hnat2bv2_val, bv2nat_a_zeros_eq in Heq. discriminate. }
        assert (Hudiv_val : (bv2nat_a (bv_udiv s (nat2bv 2 n)) = bv2nat_a s / 2)%nat).
        { rewrite (bv2nat_a_udiv_nonzero Hs Hnat2bv2_sz Hnat2bv2_ne).
          rewrite Hnat2bv2_val. reflexivity. }
        assert (Hshr_val : (bv2nat_a (bv_shr s (one n)) = bv2nat_a s / 2)%nat)
          by (apply bv2nat_a_shr_one; [exact Hs | exact Hn_pos]).
        assert (Heq_udiv_shr : bv_udiv s (nat2bv 2 n) = bv_shr s (one n)).
        { apply bv2nat_a_inj with (n := n).
          - exact (bv_udiv_size Hs Hnat2bv2_sz).
          - exact (bv_shr_size Hs (one_size n)).
          - rewrite Hudiv_val, Hshr_val. reflexivity. }
        exists (nat2bv 2 n). split.
        -- exact Hnat2bv2_sz.
        -- rewrite Heq_udiv_shr. exact Hgoal.
    + (* s >= 0: witness x = one n *)
      assert (Hsge_z : bv_sge s (zeros n) = true).
      { rewrite bv_sge_sle_equiv.
        apply zeros_sle_nonneg; [exact Hs | exact Hlast_s]. }
      pose proof (Hrhs1 Hsge_z) as Hgoal.
      (* Hgoal : bv_sge s t = true *)
      destruct (N.eq_dec n 0) as [Hn0 | Hn0].
      * (* n = 0: bv_sge [] [] = true, directly by bv_sle_refl *)
        rewrite Hn0 in Hs, Ht.
        pose proof (size_to_length Hs) as Hlen_s. simpl in Hlen_s.
        pose proof (size_to_length Ht) as Hlen_t. simpl in Hlen_t.
        apply length_zero_iff_nil in Hlen_s.
        apply length_zero_iff_nil in Hlen_t.
        subst s. subst t.
        exists (nil : bitvector). split.
        -- rewrite Hn0. unfold size. simpl. reflexivity.
        -- vm_compute. reflexivity.
      * assert (Hn_pos : (0 < N.to_nat n)%nat).
        { destruct n. contradiction. simpl. lia. }
        exists (one n). split.
        -- apply one_size.
        -- rewrite (bv_udiv_one Hs Hn_pos). exact Hgoal.
  }
Qed.

(*------------------------------------------------------------*)

(*-----------------------Remainder 1--------------------------*)

(* ~t <s (-s | -t) <=> (exists x, (x urem s) <s t) *)
Theorem bvurem_slt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_slt (bv_urem x s) t = true)
    (bv_slt 
       (bv_not t) 
       (bv_or (bv_neg s) (bv_neg t))
     = true).
Proof.
  intros n s t Hs Ht.
  destruct (N.eq_dec n 0) as [Hn0 | Hn0_ne].
  { assert (Hs_nil : s = nil).
    { apply length_zero_iff_nil. rewrite (size_to_length Hs), Hn0. reflexivity. }
    assert (Ht_nil : t = nil).
    { apply length_zero_iff_nil. rewrite (size_to_length Ht), Hn0. reflexivity. }
    subst s t.
    split.
    - intros [x [Hx Hr]].
      assert (Hx_nil : x = nil).
      { apply length_zero_iff_nil. rewrite (size_to_length Hx), Hn0. reflexivity. }
      subst x. vm_compute in Hr. discriminate.
    - intro H. vm_compute in H. discriminate. }
  assert (Hn_pos : (0 < n)%N) by (destruct n; [contradiction | lia]).
  assert (Hlen_s : length s = N.to_nat n) by (apply size_to_length; exact Hs).
  assert (Hlen_t : length t = N.to_nat n) by (apply size_to_length; exact Ht).
  assert (Hs_ne : s <> nil) by (intro H; subst s; simpl in Hlen_s; lia).
  assert (Ht_ne : t <> nil) by (intro H; subst t; simpl in Hlen_t; lia).
  assert (Hn_pos_nat : (0 < N.to_nat n)%nat) by (destruct n; [contradiction | simpl; lia]).
  assert (Hneg_s_sz : size (bv_neg s) = n) by (apply bv_neg_size; exact Hs).
  assert (Hneg_t_sz : size (bv_neg t) = n) by (apply bv_neg_size; exact Ht).
  assert (Hnot_t_sz : size (bv_not t) = n) by (apply bv_not_size; exact Ht).
  assert (Hor_sz : size (bv_or (bv_neg s) (bv_neg t)) = n)
    by (apply bv_or_size with (n := n); [exact Hneg_s_sz | exact Hneg_t_sz]).
  assert (Hneg_s_ne : bv_neg s <> nil) by
    (intro H; pose proof (size_to_length Hneg_s_sz) as Hl;
     rewrite H in Hl; simpl in Hl; lia).
  assert (HNN : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat)
    by (rewrite N2Nat.inj_sub; simpl N.to_nat; lia).
  (* bv2int(bv_neg t) ≤ bv2int(bv_or(bv_neg s)(bv_neg t)) from bv_ule *)
  assert (Hbv2int_le : (bv2int (bv_neg t) <= bv2int (bv_or (bv_neg s) (bv_neg t)))%Z).
  { assert (Hule : bv_ule (bv_neg t) (bv_or (bv_neg s) (bv_neg t)) = true).
    { rewrite (bv_or_comm Hneg_s_sz Hneg_t_sz).
      apply (@bv_ule_bv_or_l n); [exact Hneg_t_sz | exact Hneg_s_sz]. }
    unfold bv_ule in Hule. rewrite Hneg_t_sz, Hor_sz, N.eqb_refl in Hule.
    apply ule_list_list2int.
    - rewrite (size_to_length Hneg_t_sz), (size_to_length Hor_sz). reflexivity.
    - exact Hule. }
  (* last(bv_or(bv_neg s)(bv_neg t)) = OR of last bits *)
  assert (Hlast_or_eq : last (bv_or (bv_neg s) (bv_neg t)) false =
    orb (last (bv_neg s) false) (last (bv_neg t) false)).
  { unfold bv_or. rewrite Hneg_s_sz, Hneg_t_sz, N.eqb_refl.
    apply last_map2_orb_eq.
    - rewrite (size_to_length Hneg_s_sz), (size_to_length Hneg_t_sz). reflexivity.
    - exact Hneg_s_ne. }
  (* signed_min facts *)
  assert (Hmin_sz : size (signed_min n) = n) by apply signed_min_size.
  assert (Hmin_last : last (signed_min n) false = true)
    by (apply signed_min_msb; lia).
  assert (Hmin_bv2int : (bv2int (signed_min n) = pow2_int_N (n - 1)%N)%Z)
    by (apply bv2int_signed_min; exact Hn_pos).
  assert (Hmin_bv2nat : bv2nat_a (signed_min n) = 2^(N.to_nat n - 1)%nat).
  { apply Nat2Z.inj. rewrite <- bv2int_eq_Z_of_nat_bv2nat_a, Hmin_bv2int.
    unfold pow2_int_N. rewrite HNN.
    rewrite <- pow2_int_eq_Z_of_nat_pow2. reflexivity. }
  assert (Hpow_half_pos : (0 < pow2_int_N (n - 1)%N)%Z).
  { unfold pow2_int_N. apply zero_lt_pow2_int. }
  (* bv_neg(signed_min) = signed_min *)
  assert (Hneg_min : bv_neg (signed_min n) = signed_min n)
    by (apply bv_neg_signed_min; exact Hn_pos).
  (* bv_or(zeros)(-t) = bv_neg t simplification *)
  assert (Hsimp_zeros_or : bv_or (zeros n) (bv_neg t) = bv_neg t).
  { rewrite (bv_or_comm (zeros_size n) Hneg_t_sz).
    rewrite <- Hneg_t_sz. exact (bv_or_0_neutral (bv_neg t)). }
  (* pow2_int_N n = 2 * pow2_int_N(n-1) *)
  assert (Hpow_split : (pow2_int_N n = 2 * pow2_int_N (n - 1)%N)%Z).
  { unfold pow2_int_N. rewrite HNN.
    assert (Hn_nat : (N.to_nat n = S (N.to_nat n - 1))%nat) by lia.
    rewrite Hn_nat at 1. apply pow2_int_succ. }
  (* Helper: t ≠ signed_min iff last(bv_neg t) ≠ true *)
  assert (Ht_ne_smin_iff : last (bv_neg t) false = false -> t <> signed_min n).
  { intros Hlast_neg_t_false Heq. subst t.
    rewrite Hneg_min, Hmin_last in Hlast_neg_t_false. discriminate. }
  split.
  (* ===== FORWARD: (exists x, bv_urem x s <_s t) -> RHS ===== *)
  - intros [x [Hx Hr]].
    assert (Hr_sz : size (bv_urem x s) = n) by (apply bv_urem_size; [exact Hx | exact Hs]).
    (* t ≠ signed_min: signed_min is the minimum, nothing is <_s signed_min *)
    assert (Ht_ne_smin : t <> signed_min n).
    { intro Heq. subst t.
      pose proof (signed_min_sle (bv_urem x s)) as Hle. rewrite Hr_sz in Hle.
      rewrite (bv_slt_negb_sle Hr_sz Hmin_sz) in Hr. rewrite Hle in Hr. discriminate. }
    assert (Hsbv_not_t : (sbv2int n (bv_not t) = -sbv2int n t - 1)%Z)
      by (apply sbv2int_bv_not; [exact Ht | exact Hn_pos]).
    assert (Hsbv_neg_t : (sbv2int n (bv_neg t) = -sbv2int n t)%Z)
      by (apply sbv2int_bv_neg_nonmin; [exact Ht | exact Hn_pos | exact Ht_ne_smin]).
    (* Dispatch s = zeros *)
    destruct (beq_list s (zeros n)) eqn:Hs_zero.
    { apply List_eq in Hs_zero. subst s.
      rewrite bv_urem_zeros_s in Hr; [| exact Hx].
      rewrite bv_neg_zeros_zeros, Hsimp_zeros_or.
      rewrite (bv_slt_iff_sbv2int Hnot_t_sz Hneg_t_sz).
      rewrite Hsbv_not_t, Hsbv_neg_t. lia. }
    apply List_neq in Hs_zero.
    (* s ≠ zeros: r <_u s *)
    assert (Hult_r_s : bv_ult (bv_urem x s) s = true)
      by (apply (@bv_urem_ult_s n); [exact Hx | exact Hs | exact Hs_zero]).
    rewrite (bv_slt_iff_sbv2int Hnot_t_sz Hor_sz).
    rewrite Hsbv_not_t.
    destruct (last (bv_neg t) false) eqn:Hlast_neg_t.
    + (* last(-t) = true: last(or) = true, same sign *)
      assert (Hlast_or : last (bv_or (bv_neg s) (bv_neg t)) false = true).
      { rewrite Hlast_or_eq. apply Bool.orb_true_r. }
      assert (Hsbv_or_val : (sbv2int n (bv_or (bv_neg s) (bv_neg t)) =
          bv2int (bv_or (bv_neg s) (bv_neg t)) - pow2_int_N n)%Z)
        by (unfold sbv2int; rewrite Hlast_or; reflexivity).
      rewrite Hsbv_or_val.
      assert (Hbv2int_neg_t_val : (bv2int (bv_neg t) = pow2_int_N n - sbv2int n t)%Z).
      { assert (H : (sbv2int n (bv_neg t) = bv2int (bv_neg t) - pow2_int_N n)%Z)
          by (unfold sbv2int; rewrite Hlast_neg_t; reflexivity).
        lia. }
      lia.
    + (* last(-t) = false *)
      destruct (last (bv_neg s) false) eqn:Hlast_neg_s.
      * (* last(-s) = true, last(-t) = false: impossible from Hr *)
        exfalso.
        (* r <_u s → bv2nat(r) < bv2nat(s) *)
        assert (Hbv2nat_r_lt_s : (bv2nat_a (bv_urem x s) < bv2nat_a s)%nat).
        { rewrite bv_ult_nat in Hult_r_s;
            [apply Nat.ltb_lt; exact Hult_r_s |
             rewrite Hr_sz, Hs; apply N.eqb_refl]. }
        (* bv2nat(s) ≤ 2^(n-1): case on last(s) *)
        assert (Hbv2nat_s_le : (bv2nat_a s <= 2^(N.to_nat n - 1))%nat).
        { destruct (last s false) eqn:Hlast_s.
          - (* last(s)=true: s=signed_min (else last(-s)=false) *)
            destruct (beq_list s (signed_min n)) eqn:Hsmin_eq.
            + apply List_eq in Hsmin_eq. subst s. rewrite Hmin_bv2nat. lia.
            + apply List_neq in Hsmin_eq.
              pose proof (last_bv_neg_neg_nonmin Hs Hn_pos Hlast_s Hsmin_eq) as Hfls.
              rewrite Hfls in Hlast_neg_s. discriminate.
          - apply Nat.lt_le_incl. apply Nat2Z.inj_lt.
            rewrite <- bv2int_eq_Z_of_nat_bv2nat_a. unfold bv2int.
            pose proof (last_false_list2int_ub Hs_ne Hlast_s) as Hub.
            rewrite Hlen_s in Hub.
            rewrite <- pow2_int_eq_Z_of_nat_pow2. exact Hub. }
        (* bv2nat(r) < 2^(n-1) → last(r) = false *)
        assert (Hbv2nat_r_lt : (bv2nat_a (bv_urem x s) < 2^(N.to_nat n - 1))%nat) by lia.
        assert (Hlast_r_false : last (bv_urem x s) false = false).
        { destruct (last (bv_urem x s) false) eqn:Hlast_r; [| reflexivity]. exfalso.
          pose proof (size_to_length Hr_sz) as Hlen_r.
          assert (Hr_ne : bv_urem x s <> nil) by (intro H; rewrite H in Hlen_r; simpl in Hlen_r; lia).
          pose proof (last_true_list2int_lb Hr_ne Hlast_r) as Hlb.
          rewrite Hlen_r in Hlb.
          apply Nat2Z.inj_lt in Hbv2nat_r_lt.
          rewrite bv2int_eq_Z_of_nat_bv2nat_a in Hlb.
          rewrite pow2_int_eq_Z_of_nat_pow2 in Hlb.
          lia. }
        (* sbv2int(r) = bv2int(r) ≥ 0 *)
        assert (Hsbv_r_nonneg : (0 <= sbv2int n (bv_urem x s))%Z).
        { unfold sbv2int. rewrite Hlast_r_false.
          unfold bv2int. apply list2int_geq_zero. }
        (* sbv2int(t) ≤ 0 from last(-t)=false *)
        assert (Hsbv_t_nonpos : (sbv2int n t <= 0)%Z).
        { assert (Ht_ne_smin2 := Ht_ne_smin_iff eq_refl).
          assert (H : (sbv2int n (bv_neg t) = bv2int (bv_neg t))%Z)
            by (unfold sbv2int; rewrite Hlast_neg_t; reflexivity).
          rewrite Hsbv_neg_t in H.
          assert (Hge : (0 <= bv2int (bv_neg t))%Z) by (unfold bv2int; apply list2int_geq_zero).
          lia. }
        (* Hr: sbv2int(r) < sbv2int(t) ≤ 0. Contradicts ≥ 0. *)
        pose proof (bv_slt_iff_sbv2int Hr_sz Ht) as Hiff.
        apply Hiff in Hr. lia.
      * (* last(-s) = false, last(-t) = false: last(or) = false *)
        assert (Hlast_or : last (bv_or (bv_neg s) (bv_neg t)) false = false)
          by (rewrite Hlast_or_eq; reflexivity).
        assert (Hsbv_or_val : (sbv2int n (bv_or (bv_neg s) (bv_neg t)) =
            bv2int (bv_or (bv_neg s) (bv_neg t)))%Z)
          by (unfold sbv2int; rewrite Hlast_or; reflexivity).
        rewrite Hsbv_or_val.
        assert (Hbv2int_neg_t_val : (bv2int (bv_neg t) = -sbv2int n t)%Z).
        { assert (H : (sbv2int n (bv_neg t) = bv2int (bv_neg t))%Z)
            by (unfold sbv2int; rewrite Hlast_neg_t; reflexivity).
          lia. }
        lia.
  (* ===== BACKWARD: RHS -> (exists x, bv_urem x s <_s t) ===== *)
  - intro Hrhs.
    (* Case s = zeros *)
    destruct (beq_list s (zeros n)) eqn:Hs_zero.
    { apply List_eq in Hs_zero. subst s.
      rewrite bv_neg_zeros_zeros, Hsimp_zeros_or in Hrhs.
      (* Hrhs: bv_slt(bv_not t)(bv_neg t) = true *)
      rewrite (bv_slt_iff_sbv2int Hnot_t_sz Hneg_t_sz) in Hrhs.
      rewrite (sbv2int_bv_not Ht Hn_pos) in Hrhs.
      (* t ≠ signed_min: if t=signed_min, Hr gives 2^(n-1)-1 < -2^(n-1), impossible *)
      assert (Ht_ne_smin : t <> signed_min n).
      { intro Heq. subst t.
        rewrite Hneg_min in Hrhs.
        assert (Hsbv_min : (sbv2int n (signed_min n) = bv2int (signed_min n) - pow2_int_N n)%Z)
          by (unfold sbv2int; rewrite Hmin_last; reflexivity).
        lia. }
      (* Witness: signed_min n. bv_urem(signed_min)(zeros) = signed_min. *)
      exists (signed_min n). split; [exact Hmin_sz |].
      rewrite (bv_urem_zeros_s Hmin_sz).
      (* signed_min <_s t: from signed_min_sle + t ≠ signed_min *)
      pose proof (signed_min_sle t) as Hsle. rewrite Ht in Hsle.
      apply bv_sle_eq in Hsle. destruct Hsle as [Hslt | Heq].
      - exact Hslt.
      - exfalso. exact (Ht_ne_smin (eq_sym Heq)). }
    apply List_neq in Hs_zero.
    (* s ≠ zeros *)
    destruct (last (bv_neg t) false) eqn:Hlast_neg_t.
    + (* last(-t) = true: t is strictly positive. Witness: zeros n. *)
      (* last(-t)=true → last(t)=false and t≠zeros (from last_bv_neg_pos) *)
      assert (Hlast_t : last t false = false).
      { destruct (last t false) eqn:Hlt; [| reflexivity]. exfalso.
        destruct (beq_list t (signed_min n)) eqn:Htsmin.
        - apply List_eq in Htsmin. subst t.
          rewrite Hneg_min in Hrhs, Hor_sz.
          assert (Hnotmin : bv_not (signed_min n) = signed_max n).
          { pose proof (signed_min_eq_not_smax Hn_pos) as H. rewrite H. apply bv_not_involutive. }
          rewrite Hnotmin in Hrhs.
          pose proof (signed_max_size n) as Hsmax_sz.
          pose proof (signed_max_sle_any Hor_sz Hn_pos_nat) as Hmaxle.
          rewrite (bv_slt_negb_sle Hsmax_sz Hor_sz) in Hrhs.
          rewrite Hmaxle in Hrhs. simpl in Hrhs. discriminate.
        - apply List_neq in Htsmin.
          pose proof (last_bv_neg_neg_nonmin Ht Hn_pos Hlt Htsmin) as Hfls.
          rewrite Hfls in Hlast_neg_t. discriminate. }
      assert (Ht_ne_zeros : t <> zeros n).
      { intro Heq. subst t. rewrite bv_neg_zeros_zeros in Hlast_neg_t.
        unfold zeros in Hlast_neg_t. rewrite last_mk_list_false in Hlast_neg_t. discriminate. }
      exists (zeros n). split; [apply zeros_size |].
      rewrite (bv_urem_zeros_l Hs).
      rewrite (bv_slt_iff_sbv2int (zeros_size n) Ht).
      assert (Hsbv_zeros : (sbv2int n (zeros n) = 0)%Z).
      { unfold sbv2int, zeros. rewrite (last_mk_list_false (N.to_nat n)).
        unfold bv2int. rewrite list2int_mk_list_false. simpl. reflexivity. }
      rewrite Hsbv_zeros.
      assert (Hsbv_t_pos : (0 < sbv2int n t)%Z).
      { unfold sbv2int. rewrite Hlast_t.
        rewrite bv2int_eq_Z_of_nat_bv2nat_a.
        assert (Hbv2nat_t_pos : (0 < bv2nat_a t)%nat).
        { destruct (bv2nat_a t) eqn:H.
          - exfalso. apply Ht_ne_zeros. exact (bv2nat_a_zero_eq_zeros Ht H).
          - lia. }
        lia. }
      lia.
    + (* last(-t) = false *)
      destruct (last (bv_neg s) false) eqn:Hlast_neg_s.
      * (* last(-s) = true, last(-t) = false: RHS is false, exfalso *)
        exfalso.
        (* From RHS being true: -st-1 < sbv2int(bv_or(-s)(-t)) *)
        rewrite (bv_slt_iff_sbv2int Hnot_t_sz Hor_sz) in Hrhs.
        rewrite (sbv2int_bv_not Ht Hn_pos) in Hrhs.
        (* last(or) = true (last(-s)=true) *)
        assert (Hlast_or : last (bv_or (bv_neg s) (bv_neg t)) false = true)
          by (rewrite Hlast_or_eq; reflexivity).
        (* sbv2int(or) = bv2int(or) - P *)
        assert (Hsbv_or_val : (sbv2int n (bv_or (bv_neg s) (bv_neg t)) =
            bv2int (bv_or (bv_neg s) (bv_neg t)) - pow2_int_N n)%Z)
          by (unfold sbv2int; rewrite Hlast_or; reflexivity).
        rewrite Hsbv_or_val in Hrhs.
        (* bv2int(bv_neg t) ≥ 0 (unsigned) and = -sbv2int(t) (since last(-t)=false) *)
        assert (Ht_ne_smin2 := Ht_ne_smin_iff eq_refl).
        assert (Hsbv_neg_t : (sbv2int n (bv_neg t) = -sbv2int n t)%Z)
          by (apply sbv2int_bv_neg_nonmin; [exact Ht | exact Hn_pos | exact Ht_ne_smin2]).
        assert (Hbv2int_neg_t_val : (bv2int (bv_neg t) = -sbv2int n t)%Z).
        { assert (H : (sbv2int n (bv_neg t) = bv2int (bv_neg t))%Z)
            by (unfold sbv2int; rewrite Hlast_neg_t; reflexivity).
          lia. }
        assert (Hsbv_t_nonpos : (sbv2int n t <= 0)%Z).
        { assert (Hge : (0 <= bv2int (bv_neg t))%Z) by (unfold bv2int; apply list2int_geq_zero).
          lia. }
        (* bv2int(or) ≥ bv2int(-t) = -st ≥ 0 *)
        (* Hrhs: -st - 1 < bv2int(or) - P. Since bv2int(or) < P: bv2int(or)-P < 0 ≤ -st-1? *)
        (* -st ≥ 0 → -st - 1 ≥ -1. And bv2int(or) - P < 0. *)
        (* We need -st - 1 < bv2int(or) - P. *)
        (* bv2int(or) ≥ bv2int(-t) = -st ≥ 0. So bv2int(or) - P ≥ -st - P. *)
        (* And -st - 1 < bv2int(or) - P requires bv2int(or) > -st - 1 + P = P - st - 1. *)
        (* bv2int(or) ≥ -st. And P - st - 1 > -st (since P > 1). *)
        (* So bv2int(or) ≥ -st < P - st - 1. Not sufficient! *)
        (* The contradiction is: bv2int(or) < P, so bv2int(or)-P < 0 ≤ -st - 1. *)
        assert (Hbv2int_or_nonneg : (0 <= bv2int (bv_or (bv_neg s) (bv_neg t)))%Z)
          by (unfold bv2int; apply list2int_geq_zero).
        assert (Hbv2int_or_lt_P : (bv2int (bv_or (bv_neg s) (bv_neg t)) < pow2_int_N n)%Z).
        { unfold bv2int. unfold pow2_int_N. rewrite <- (size_to_length Hor_sz).
          apply list2int_lt_pow2_int. reflexivity. }
        lia.
      * (* last(-s) = false, last(-t) = false: witness = signed_min n *)
        (* From last(-s)=false AND s≠zeros: last(s)=true AND s≠signed_min → bv2nat(s) > 2^(n-1) *)
        assert (Hlast_s_true : last s false = true).
        { destruct (last s false) eqn:Hlast_s; [reflexivity |].
          exfalso.
          pose proof (last_bv_neg_pos Hs Hn_pos Hlast_s Hs_zero) as Hfls.
          rewrite Hfls in Hlast_neg_s. discriminate. }
        assert (Hs_ne_smin : s <> signed_min n).
        { intro Heq. subst s.
          rewrite Hneg_min, Hmin_last in Hlast_neg_s. discriminate. }
        assert (Hbv2nat_s_gt : (2^(N.to_nat n - 1) < bv2nat_a s)%nat).
        { apply Nat2Z.inj_lt.
          pose proof (last_true_list2int_lb Hs_ne Hlast_s_true) as Hlb.
          rewrite Hlen_s in Hlb.
          assert (Hne : (bv2nat_a s <> 2^(N.to_nat n - 1))%nat).
          { intro Heq. apply Hs_ne_smin.
            apply (bv2nat_a_inj Hs Hmin_sz). lia. }
          rewrite pow2_int_eq_Z_of_nat_pow2 in Hlb.
          change (list2int s) with (bv2int s) in Hlb.
          rewrite bv2int_eq_Z_of_nat_bv2nat_a in Hlb.
          assert (Hne_Z : (Z.of_nat (bv2nat_a s) <> Z.of_nat (2^(N.to_nat n - 1)))%Z)
            by (intro H; apply Hne; exact (Nat2Z.inj _ _ H)).
          lia. }
        (* bv_urem(signed_min)(s) = signed_min (since bv2nat(signed_min) = 2^(n-1) < bv2nat(s)) *)
        assert (Hurem_smin : bv_urem (signed_min n) s = signed_min n).
        { apply bv2nat_a_inj with (n := n);
            [apply bv_urem_size; [exact Hmin_sz | exact Hs] | exact Hmin_sz |].
          rewrite (bv2nat_a_urem_nonzero Hmin_sz Hs Hs_zero).
          rewrite Hmin_bv2nat.
          apply Nat.mod_small. exact Hbv2nat_s_gt. }
        (* t ≠ signed_min from last(-t)=false *)
        assert (Ht_ne_smin := Ht_ne_smin_iff eq_refl).
        exists (signed_min n). split; [exact Hmin_sz |].
        rewrite Hurem_smin.
        (* signed_min <_s t *)
        pose proof (signed_min_sle t) as Hsle. rewrite Ht in Hsle.
        apply bv_sle_eq in Hsle. destruct Hsle as [Hslt | Heq].
        -- exact Hslt.
        -- exfalso. exact (Ht_ne_smin (eq_sym Heq)).
Qed.

(* ~0 <s -s & t <=> (exists x, x urem s <=s t) *)
Theorem bvurem_sle : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sle (bv_urem x s) t = true)
    (n = 0%N \/ bv_slt (bv_not (zeros n)) (bv_and (bv_neg s) t) = true).
Proof.
  intros n s t Hs Ht.
  destruct (N.eq_dec n 0%N) as [Hn0 | Hn0_ne].
  { split.
    + intros. left. exact Hn0.
    + intros Hrhs0.
      assert (Hs_nil : s = nil).
      { apply length_zero_iff_nil. rewrite (size_to_length Hs), Hn0. reflexivity. }
      assert (Ht_nil : t = nil).
      { apply length_zero_iff_nil. rewrite (size_to_length Ht), Hn0. reflexivity. }
      subst s. subst t.
      exists nil. split; [rewrite Hn0; reflexivity | vm_compute; reflexivity]. }
  assert (Hn_pos : (0 < n)%N) by (destruct n; [contradiction | lia]).
  assert (Hneg_sz : size (bv_neg s) = n) by (apply bv_neg_size; exact Hs).
  assert (Hand_sz : size (bv_and (bv_neg s) t) = n) by
    (apply bv_and_size; [exact Hneg_sz | exact Ht]).
  assert (Hlen_s : length s = N.to_nat n) by (apply size_to_length; exact Hs).
  assert (Hs_ne : s <> nil).
  { intro H. rewrite H in Hlen_s. simpl in Hlen_s.
    destruct n; [apply Hn0_ne; reflexivity | simpl in Hlen_s; lia]. }
  assert (Hmin_sz : size (signed_min n) = n) by apply signed_min_size.
  assert (Hmin_last : last (bits (signed_min n)) false = true) by
    (apply signed_min_msb; lia).
  assert (Hnn : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat).
  { rewrite N2Nat.inj_sub. simpl. lia. }
  assert (Hmin_bv2nat : (bv2nat_a (signed_min n) = 2^(N.to_nat n - 1))%nat).
  { apply Nat2Z.inj.
    rewrite <- bv2int_eq_Z_of_nat_bv2nat_a, (bv2int_signed_min Hn_pos).
    unfold pow2_int_N. rewrite Hnn. apply pow2_int_eq_Z_of_nat_pow2. }
  assert (HRHS_iff : bv_slt (bv_not (zeros n)) (bv_and (bv_neg s) t) =
                     negb (last (bv_and (bv_neg s) t) false)) by
    (apply bv_slt_not_zeros_nonneg; [exact Hn_pos | exact Hand_sz]).
  split.
  - intros [x [Hx_sz Hsle_xt]].
    right. rewrite HRHS_iff.
    assert (Hlast_and : last (bv_and (bv_neg s) t) false = false).
    { destruct (last s false) eqn:Hlast_s.
      + (* B: s negative *)
        destruct (bv_eq s (signed_min n)) eqn:Heq_min.
        * (* B1: s = signed_min n *)
          rewrite bv_eq_reflect in Heq_min. subst s.
          rewrite (bv_neg_signed_min Hn_pos).
          assert (Hs_ne_z : signed_min n <> zeros n).
          { intro Heq. rewrite Heq in Hmin_last.
            unfold bits, zeros in Hmin_last. rewrite last_mk_list_false in Hmin_last.
            discriminate. }
          assert (Hurem_sz : size (bv_urem x (signed_min n)) = n) by
            (apply bv_urem_size; [exact Hx_sz | exact Hmin_sz]).
          assert (Hurem_ult : bv_ult (bv_urem x (signed_min n)) (signed_min n) = true) by
            exact (bv_urem_ult_s Hx_sz Hmin_sz Hs_ne_z).
          assert (Hnuge : bv_uge (bv_urem x (signed_min n)) (signed_min n) = false) by
            exact (ult_implies_not_uge Hurem_ult).
          assert (Hlast_urem : last (bv_urem x (signed_min n)) false = false).
          { destruct (last (bv_urem x (signed_min n)) false) eqn:Hlast_ur; [| reflexivity].
            exfalso.
            pose proof (bv_msb_implies_uge_signed_min Hurem_sz Hn_pos Hlast_ur) as Hmsb.
            rewrite Hnuge in Hmsb. discriminate. }
          assert (Hlast_t : last t false = false).
          { destruct (last t false) eqn:Hlast_t; [| reflexivity].
            exfalso.
            exact (bv_sle_pos_neg_absurd Hn_pos Hurem_sz Ht Hlast_urem Hlast_t Hsle_xt). }
          exact (pos_bv_and Hmin_sz Ht Hlast_t).
        * (* B2: s ≠ signed_min n *)
          assert (Hs_ne_min : s <> signed_min n).
          { intro Heq. rewrite <- bv_eq_reflect in Heq. rewrite Heq in Heq_min. discriminate. }
          assert (Hlast_neg : last (bv_neg s) false = false) by
            exact (last_bv_neg_neg_nonmin Hs Hn_pos Hlast_s Hs_ne_min).
          exact (pos_bvand_pos Hneg_sz Ht Hlast_neg).
      + (* A: s nonneg *)
        destruct (bv_eq s (zeros n)) eqn:Hseq.
        * (* A1: s = zeros n *)
          rewrite bv_eq_reflect in Hseq. subst s.
          rewrite (bv_neg_zeros_zeros n).
          rewrite (bv_and_comm (zeros_size n) Ht).
          pose proof (bv_and_0_absorb t) as Habs. rewrite Ht in Habs. rewrite Habs.
          unfold zeros. apply last_mk_list_false.
        * (* A2: s ≠ zeros n, nonneg *)
          assert (Hs_ne_z : s <> zeros n) by
            (intro Heq; rewrite <- bv_eq_reflect in Heq; rewrite Heq in Hseq; discriminate).
          assert (Hurem_sz : size (bv_urem x s) = n) by
            (apply bv_urem_size; [exact Hx_sz | exact Hs]).
          assert (Hurem_ult_s : bv_ult (bv_urem x s) s = true) by
            exact (bv_urem_ult_s Hx_sz Hs Hs_ne_z).
          assert (Hs_ult_smin : bv_ult s (signed_min n) = true) by
            (apply nonneg_ult_signed_min; [exact Hn_pos | exact Hs | exact Hlast_s]).
          assert (Hurem_ult_smin : bv_ult (bv_urem x s) (signed_min n) = true) by
            exact (bv_ult_trans Hurem_ult_s Hs_ult_smin).
          assert (Hnuge : bv_uge (bv_urem x s) (signed_min n) = false) by
            exact (ult_implies_not_uge Hurem_ult_smin).
          assert (Hlast_urem : last (bv_urem x s) false = false).
          { destruct (last (bv_urem x s) false) eqn:Hlast_ur; [| reflexivity].
            exfalso.
            pose proof (bv_msb_implies_uge_signed_min Hurem_sz Hn_pos Hlast_ur) as Hmsb.
            rewrite Hnuge in Hmsb. discriminate. }
          assert (Hlast_t : last t false = false).
          { destruct (last t false) eqn:Hlast_t; [| reflexivity].
            exfalso.
            exact (bv_sle_pos_neg_absurd Hn_pos Hurem_sz Ht Hlast_urem Hlast_t Hsle_xt). }
          assert (Hlast_neg_s : last (bv_neg s) false = true) by
            exact (last_bv_neg_pos Hs Hn_pos Hlast_s Hs_ne_z).
          exact (pos_bv_and Hneg_sz Ht Hlast_t). }
    rewrite Hlast_and. reflexivity.
  - intros [Hn0' | Hrhs].
    { exfalso. apply Hn0_ne. exact Hn0'. }
    rewrite HRHS_iff in Hrhs.
    assert (Hlast_and : last (bv_and (bv_neg s) t) false = false).
    { destruct (last (bv_and (bv_neg s) t) false) eqn:Hlast_and_eqn; simpl in Hrhs.
      + discriminate.
      + reflexivity. }
    destruct (last s false) eqn:Hlast_s.
    + (* B: s negative *)
      destruct (bv_eq s (signed_min n)) eqn:Heq_min.
      * (* B1: s = signed_min n *)
        rewrite bv_eq_reflect in Heq_min. subst s.
        rewrite (bv_neg_signed_min Hn_pos) in Hlast_and.
        assert (Hlast_t : last t false = false).
        { destruct (last t false) eqn:Hlast_t; [| reflexivity].
          exfalso.
          assert (Hlast_and_true : last (bv_and (signed_min n) t) false = true) by
            exact (neg_bvand_neg Hmin_sz Ht Hmin_last Hlast_t).
          rewrite Hlast_and_true in Hlast_and. discriminate. }
        exists (zeros n). split. apply zeros_size.
        rewrite (bv_urem_zeros_l Hmin_sz).
        apply zeros_sle_nonneg; [exact Ht | exact Hlast_t].
      * (* B2: s ≠ signed_min n *)
        assert (Hs_ne_min : s <> signed_min n).
        { intro Heq. rewrite <- bv_eq_reflect in Heq. rewrite Heq in Heq_min. discriminate. }
        assert (Hs_ne_z : s <> zeros n).
        { intro Heq. rewrite Heq in Hlast_s.
          unfold zeros in Hlast_s. rewrite last_mk_list_false in Hlast_s. discriminate. }
        assert (Hbv2nat_s_gt : (2^(N.to_nat n - 1) < bv2nat_a s)%nat).
        { apply Nat2Z.inj_lt.
          pose proof (last_true_list2int_lb Hs_ne Hlast_s) as Hlb.
          rewrite Hlen_s in Hlb.
          assert (Hne_nat : (bv2nat_a s <> 2^(N.to_nat n - 1))%nat).
          { intro Heq. apply Hs_ne_min.
            apply bv2nat_a_inj with (n := n); [exact Hs | exact Hmin_sz |].
            rewrite Heq, Hmin_bv2nat. reflexivity. }
          rewrite pow2_int_eq_Z_of_nat_pow2 in Hlb.
          change (list2int s) with (bv2int s) in Hlb.
          rewrite bv2int_eq_Z_of_nat_bv2nat_a in Hlb.
          assert (Hne_Z : (Z.of_nat (bv2nat_a s) <> Z.of_nat (2^(N.to_nat n - 1)))%Z)
            by (intro H; apply Hne_nat; exact (Nat2Z.inj _ _ H)).
          lia. }
        assert (Hurem_smin : bv_urem (signed_min n) s = signed_min n).
        { apply bv2nat_a_inj with (n := n);
            [apply bv_urem_size; [exact Hmin_sz | exact Hs] | exact Hmin_sz |].
          rewrite (bv2nat_a_urem_nonzero Hmin_sz Hs Hs_ne_z), Hmin_bv2nat.
          apply Nat.mod_small. exact Hbv2nat_s_gt. }
        exists (signed_min n). split. exact Hmin_sz.
        rewrite Hurem_smin.
        pose proof (signed_min_sle t) as Hsle. rewrite Ht in Hsle. exact Hsle.
    + (* A: s nonneg *)
      destruct (bv_eq s (zeros n)) eqn:Hseq.
      * (* A1: s = zeros n *)
        rewrite bv_eq_reflect in Hseq. subst s.
        exists t. split. exact Ht.
        rewrite (bv_urem_zeros_s Ht). apply bv_sle_refl.
      * (* A2: s ≠ zeros n, nonneg *)
        assert (Hs_ne_z : s <> zeros n) by
          (intro Heq; rewrite <- bv_eq_reflect in Heq; rewrite Heq in Hseq; discriminate).
        assert (Hlast_neg_s : last (bv_neg s) false = true) by
          exact (last_bv_neg_pos Hs Hn_pos Hlast_s Hs_ne_z).
        assert (Hlast_t : last t false = false).
        { destruct (last t false) eqn:Hlast_t; [| reflexivity].
          exfalso.
          assert (Hlast_and_true : last (bv_and (bv_neg s) t) false = true) by
            exact (neg_bvand_neg Hneg_sz Ht Hlast_neg_s Hlast_t).
          rewrite Hlast_and_true in Hlast_and. discriminate. }
        exists (zeros n). split. apply zeros_size.
        rewrite (bv_urem_zeros_l Hs).
        apply zeros_sle_nonneg; [exact Ht | exact Hlast_t].
Qed.

(*------------------------------------------------------------*)

(*-----------------------Remainder 2--------------------------*)
 
(* (t + t - s) & s >=u t <=> (exists x, s urem x = t) *)
Theorem bvurem_reverse_eq : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_eq (bv_urem s x) t = true)
    (bv_uge 
       (bv_and (bv_subt (bv_add t t) s) s) 
       t
     = true).
Proof.
Admitted.

 
(* (s >=s 0 => s >s t) /\ (s <s 0 => ((s - 1) >> 1) >s t) <=> (exists x, s urem x >s t) *)
Theorem bvurem_reverse_sgt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sgt (bv_urem s x) t = true)
    (
      (bv_sge s (zeros n) = true -> bv_sgt s t = true) /\
      (bv_slt s (zeros n) = true -> bv_sgt (bv_shr (bv_subt s (one n)) (one n)) t = true)
    ).
Proof.
Admitted.

(* (s >=s 0 => s >=s t) /\ ((s <s 0 /\ t >=s 0) => s - t >u t) <=> (exists x, s urem x >=s t) *)
Theorem bvurem_reverse_sge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sge (bv_urem s x) t = true)
    (
      (bv_sge s (zeros n) = true -> bv_sge s t = true) /\
      ((bv_slt s (zeros n) = true /\ bv_sge t (zeros n) = true) -> 
       bv_ugt (bv_subt s t) t = true)
    ).
Proof.
Admitted.

(*------------------------------------------------------------*)