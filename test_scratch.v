From BV Require Import BVList.
Import RAWBITVECTOR_LIST.
Require Import List Bool NArith Psatz ZArith Nnat Lia PeanoNat.

Lemma list2int_eq_Z_of_N_list2N : forall a, (list2int a = Z.of_N (list2N a))%Z.
Proof.
  induction a as [| b t IH]; [reflexivity |].
  rewrite list2int_cons. simpl list2N. destruct b.
  - rewrite N.succ_double_spec, N2Z.inj_add, N2Z.inj_mul, <- IH.
    replace (Z.of_N 2) with 2%Z by reflexivity.
    replace (Z.of_N 1) with 1%Z by reflexivity. simpl bool2int. ring.
  - rewrite N.double_spec, N2Z.inj_mul, <- IH.
    replace (Z.of_N 2) with 2%Z by reflexivity. simpl bool2int. ring.
Qed.

Lemma bv2int_eq_Z_of_nat_bv2nat_a : forall a, (bv2int a = Z.of_nat (bv2nat_a a))%Z.
Proof.
  intro a. unfold bv2int, bv2nat_a, list2nat_be_a.
  rewrite list2int_eq_Z_of_N_list2N, N_nat_Z. reflexivity.
Qed.

Lemma pow2_int_eq_Z_of_nat_pow2 : forall k, pow2_int k = Z.of_nat (2^k).
Proof.
  induction k as [| k IH]; [reflexivity |].
  rewrite pow2_int_succ, IH. simpl (2^(S k))%nat. rewrite Nat2Z.inj_add. lia.
Qed.

Lemma bv2nat_a_lt_pow2 : forall (n : N) (a : bitvector),
  size a = n -> (bv2nat_a a < 2^(N.to_nat n))%nat.
Proof.
  intros n a Ha. unfold bv2nat_a, list2nat_be_a.
  pose proof (pow_gt a) as Hpg. apply Nat.ltb_lt in Hpg.
  now rewrite (size_to_length Ha) in Hpg.
Qed.

Lemma bv2nat_a_mult_mod : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  bv2nat_a (bv_mult s t) = (bv2nat_a s * bv2nat_a t) mod 2^(N.to_nat n).
Proof.
  intros n s t Hs Ht. apply Nat2Z.inj.
  rewrite Nat2Z.inj_mod, Nat2Z.inj_mul.
  rewrite <- pow2_int_eq_Z_of_nat_pow2. unfold pow2_int_N.
  rewrite <- bv2int_eq_Z_of_nat_bv2nat_a, <- (bv2int_eq_Z_of_nat_bv2nat_a s), <- (bv2int_eq_Z_of_nat_bv2nat_a t).
  pose proof (bv2int_mult Hs Ht) as Hmult. unfold pow2_int_N in Hmult.
  rewrite Z.mod_small in Hmult; [exact Hmult |].
  split.
  - rewrite bv2int_eq_Z_of_nat_bv2nat_a. apply Nat2Z.is_nonneg.
  - rewrite bv2int_eq_Z_of_nat_bv2nat_a, pow2_int_eq_Z_of_nat_pow2.
    apply Nat2Z.inj_lt. exact (bv2nat_a_lt_pow2 n (bv_mult s t) (bv_mult_size Hs Ht)).
Qed.

Lemma N_size_le_nat : forall (q : N) (k : nat),
  (N.to_nat q < 2^k)%nat -> (N.to_nat (N.size q) <= k)%nat.
Proof.
  intros q k Hlt. destruct q as [| p]; [simpl; lia |].
  assert (Hpos : (0 < N.pos p)%N) by constructor.
  assert (HN : (N.pos p < N.pow 2 (N.of_nat k))%N).
  { rewrite <- N.compare_lt_iff, N2Nat.inj_compare.
    apply PeanoNat.Nat.compare_lt_iff.
    rewrite N2Nat.inj_pow, Nat2N.id. simpl N.to_nat. exact Hlt. }
  apply N.log2_lt_pow2 in HN; [| exact Hpos].
  rewrite N.size_log2 by discriminate. rewrite N2Nat.inj_succ. lia.
Qed.

Lemma bv2nat_a_udiv_nonzero : forall (n : N) (a b : bitvector),
  size a = n -> size b = n -> b <> zeros n ->
  (bv2nat_a (bv_udiv a b) = bv2nat_a a / bv2nat_a b)%nat.
Proof.
  intros n a b Ha Hb Hbne.
  unfold bv2nat_a, list2nat_be_a, bv_udiv, udiv_list.
  pose proof (size_to_length Ha) as Hlen_a. pose proof (size_to_length Hb) as Hlen_b.
  rewrite Ha, Hb, N.eqb_refl.
  assert (Hbeq : beq_list b (mk_list_false (length b)) = false).
  { apply List_neq2. intro Heq. apply Hbne. unfold zeros. now rewrite <- Hlen_b. }
  rewrite Hbeq, Hlen_a.
  rewrite list2N_N2List_s; [rewrite N2Nat.inj_div; reflexivity |].
  apply Nat.leb_le. apply N_size_le_nat.
  apply Nat.le_lt_trans with (m := N.to_nat (list2N a)).
  - rewrite N2Nat.inj_div. destruct (N.to_nat (list2N b)); [simpl; lia |].
    apply Nat.Div0.div_le_upper_bound. lia.
  - pose proof (pow_gt a) as Hpg. apply Nat.ltb_lt in Hpg.
    rewrite Hlen_a in Hpg. exact Hpg.
Qed.

Lemma bv2nat_a_inj : forall (n : N) (a b : bitvector),
  size a = n -> size b = n -> bv2nat_a a = bv2nat_a b -> a = b.
Proof.
  intros n a b Ha Hb Heq. unfold bv2nat_a, list2nat_be_a in Heq.
  apply N2Nat.inj in Heq.
  rewrite <- N2List_list2N with (a := a), <- N2List_list2N with (a := b).
  rewrite Heq, (size_to_length Ha), (size_to_length Hb). reflexivity.
Qed.

Theorem bvudiv_uge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_uge (bv_udiv x s) t = true)
    (bv_eq (bv_and (bv_udiv (bv_mult s t) t) s) s = true).
Proof.
  intros n s t Hs Ht.
  (* Helper: bv_udiv zeros zeros = ones *)
  assert (Hudiv00 : forall m, bv_udiv (zeros m) (zeros m) = ones m).
  { intro m. unfold bv_udiv.
    rewrite zeros_size, N.eqb_refl.
    unfold udiv_list, zeros.
    rewrite length_mk_list_false, List_eq_refl.
    unfold ones. reflexivity. }
  split.
  (* Forward: exists x with x/s >=u t => RHS *)
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
        rewrite (bv2nat_a_udiv_nonzero n x s Hx Hs Hsne) in Hxge.
        assert (HXge : (S * T <= X)%nat).
        { apply Nat.le_trans with (m := S * (X / S)).
          - apply Nat.mul_le_mono_l. exact Hxge.
          - apply Nat.Div0.mul_div_le. }
        assert (HST_lt : (S * T < 2^(N.to_nat n))%nat).
        { exact (Nat.le_lt_trans _ _ _ HXge (bv2nat_a_lt_pow2 n x Hx)). }
        pose proof (bv_mult_size Hs Ht) as Hst_sz.
        pose proof (bv2nat_a_mult_mod n s t Hs Ht) as Hmult_eq.
        rewrite Nat.mod_small in Hmult_eq; [| exact HST_lt].
        pose proof (bv2nat_a_udiv_nonzero n (bv_mult s t) t Hst_sz Ht Htne) as Hdiv_eq.
        rewrite Hmult_eq, Nat.div_mul in Hdiv_eq; [| lia].
        rewrite (bv2nat_a_inj n _ _ (bv_udiv_size Hst_sz Ht) Hs Hdiv_eq).
        rewrite bv_and_idem. apply bv_eq_refl.

  (* Backward: RHS => exists x *)
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
        rewrite (bv2nat_a_udiv_nonzero n (bv_mult s t) t Hst_sz Ht Htne) in Hule.
        change (bv2nat_a s) with S in Hule. change (bv2nat_a t) with T in Hule.
        pose proof (bv2nat_a_mult_mod n s t Hs Ht) as Hmult_eq.
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
          exact (Nat.le_lt_trans _ _ _ HST_le (bv2nat_a_lt_pow2 n (bv_mult s t) Hst_sz)). }
        exists (bv_mult s t). split; [exact Hst_sz |].
        assert (Hdivs_sz := bv_udiv_size Hst_sz Hs).
        apply not_bv_ult_implies_bv_uge; [rewrite Hdivs_sz, Ht; reflexivity |].
        rewrite bv_ult_nat; [| rewrite Hdivs_sz, Ht; apply N.eqb_refl].
        apply Nat.ltb_ge.
        rewrite (bv2nat_a_udiv_nonzero n (bv_mult s t) s Hst_sz Hs Hsne).
        change (bv2nat_a (bv_mult s t)) with M. change (bv2nat_a s) with S.
        rewrite HM_eq, Nat.mul_comm, Nat.div_mul; [lia | lia].
Qed.
