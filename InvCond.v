(* From Hammer Require Import Hammer Reconstr. *)
From BV Require Import BVList Reconstr.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

(* Remaining Proofs - CSC490 *)


(* (* t <s (maxs >> s) << s <=> (exists x, t <s x << s) *)
Theorem bvshl_sgt :
  forall (n : N) (s t : bitvector),
    size s = n ->
    size t = n ->
    iff
      (bv_slt t (bv_shl (bv_shr (signed_max n) s) s) = true)
      (exists x, size x = n /\ bv_slt t (bv_shl x s) = true).
Proof.
Admitted.

(* (mins >> s) << s <=s t <=> (exists x, (x << s) <=s t) *)
Theorem bvshl_sle : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sle (bv_shl (bv_shr (signed_min n) s) s) t = true)
    (exists (x : bitvector), (size x = n) /\ (bv_sle (bv_shl x s) t = true)).
Proof.
Admitted.


(* t <=s (maxs >> s) << s <=> (exists x, t <=s (x << s)) *)
Theorem bvshl_sge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sle t (bv_shl (bv_shr (signed_max n) s) s) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_sle t (bv_shl x s) = true)).
Proof.
Admitted.

(* mins << s <=s t + mins <=> (exists x, (s << x) <=s t) *)
Theorem bvshl_sle2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sle (bv_shl (signed_min n) s) (bv_add t (signed_min n)) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_sle (bv_shl s x) t = true)).
Proof.
Admitted.

(* t <s (~0 >> s) <=> (exists x, t <s (x >> s)) *)
Theorem bvshr_sgt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt t (bv_shr (bv_not (zeros (size s))) s) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_slt t (bv_shr x s) = true)).
Proof.
Admitted.

(* t <=s (~0 >> s) <=> (exists x, t <=s (x >> s)) *)
Theorem bvshr_sge : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sle t (bv_shr (bv_not (zeros (size s))) s) = true)
    (exists (x : bitvector), (size x = n) /\ (bv_sle t (bv_shr x s) = true)).
Proof.
Admitted.

(* (mins >>_a s) <=s t <=> (exists x, (x >>_a s) <=s t) *)
Theorem bvashr_sle : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_sle (bv_ashr (signed_min n) s) t = true)
    (exists (x : bitvector), (size x = n) /\ (bv_sle (bv_ashr x s) t = true)).
Proof.
Admitted.

(* (t <s s \/ t <s ~0) <=> (exists x, t <s (s >>_a x)) *)
Theorem bvashr_sgt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt t s = true) \/ (bv_slt t (bv_not (zeros (size t))) = true))
    (exists (x : bitvector), (size x = n) /\ (bv_slt t (bv_ashr s x) = true)).
Proof.
Admitted.

(* (s <=s t \/ 0 <=s t \/ ~0 <=s t) <=> (exists x, (s >>_a x) <=s t) *)
Theorem bvashr_sle2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_sle s t = true) \/
     (bv_sle (zeros (size t)) t = true) \/
     (bv_sle (bv_not (zeros (size t))) t = true))
    (exists (x : bitvector), (size x = n) /\ (bv_sle (bv_ashr s x) t = true)).
Proof.
Admitted.

(* ~(-t) & (-s | s) <s t <=> (exists x, x * s <s t) *)
Theorem bvmult_slt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists x, size x = n /\ bv_slt (bv_mult x s) t = true)
    (bv_slt (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)) t = true).
Proof.
Admitted.
    
(* t <s t - ((s | t) | -s) <=> (exists x, x * s >s t) *)
Theorem bvmult_sgt: forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists x, size x = n /\ bv_slt t (bv_mult x s) = true)
    (bv_slt t (bv_subt t (bv_or (bv_or s t) (bv_neg s))) = true).
Proof.
Admitted. *)

(* 
(* ~(s - t) | s <s t <=> (exists x, x | s <s t) *)
Theorem bvor_slt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    ((bv_slt (bv_or (bv_not (bv_subt s t)) s) t) = true) 
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_or x s) t) = true)).
Proof.
Admitted. *)

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

Search bv_not.
  intros n s t Hs Ht.
  split.
  - intro H_cond.
      exists (bv_not (bv_neg t)).
      split.
        rewrite (@bv_not_size n).
        split.
        rewrite (@bv_neg_size n).
        reflexivity.
        assumption.
        +
        assumption. 
  - intro H_exists.
  (*Pre-step: Normalize the syntax of "t minus 1" *)
    assert (H_syntax_fix : bv_not (bv_neg t) = bv_subt' t (one n)).
    {
          (* 2. Apply algebra to move the subtraction *)
          
          assert (H_sizes : size (one n) = n /\ size t = n /\ size (bv_not (bv_neg t)) = n).
          { 
            split. apply one_size.
            split. exact Ht.
            apply bv_not_size, bv_neg_size; auto.
          }
          (* Only pass the proof H_sizes explicitly, let Coq infer the rest *)
          apply (proj1 (bvadd_U H_sizes)).
          Check bv_neg_involutive.  
          rewrite <- bv_neg_involutive.
          Check bv_neg_is_not_plus_one.
          Search bv_not one.
          symmetry. 
          apply bv_neg_is_not_plus_one.
          apply bv_neg_size. easy.
    }
    (* t <> signed_min *) 
    destruct H_exists as [x [Hx_size Hx_lt]].
    assert (H_not_min : t <> signed_min n).
    {
         intro H_is_min.
         
         
         rewrite H_is_min in Hx_lt.
         
         pose proof (signed_min_sle (bv_and x s)) as H_imp.
         Search bv_and.
         rewrite (bv_and_size Hx_size Hs) in H_imp.
         rewrite bv_sle_eq in H_imp.
         destruct H_imp as [H_min_lt_val | H_min_eq_val].
         + 
          pose proof (bv_slt_trans Hx_lt H_min_lt_val) as H_cycle.
          rewrite bv_slt_nrefl in H_cycle. 
          discriminate.
         + 
          rewrite <- H_min_eq_val in Hx_lt.
          rewrite bv_slt_nrefl in Hx_lt.
          discriminate.
    }
    destruct (bv_slt s (zeros n)) eqn:H_sign.
    + (* Case 1: s < 0 *)
      (* Step 2: Prove that (t - 1) is strictly less than t *)
      (* Reasoning: Since t != min, subtracting 1 stays smaller. *)
      assert (H_t_minus_1_lt : bv_slt (bv_not (bv_neg t)) t = true).
      {
      Search ones.
        (* 1. Bridge: Convert signed bitvector comparison to Integer comparison *)
        rewrite bv_slt_iff_sbv2int with (n := n).
        
        (* Side goal 1: Prove size (t-1) = n *)
        2: { 
        Search "bv_not_size".
          apply bv_not_size. 
          apply bv_neg_size.
          exact Ht. 
        }
        
        (* Side goal 2: Prove size t = n *)
        2: { exact Ht. }
        rewrite H_syntax_fix.

        (* 2. Arithmetic: Replace value of (t-1) with (val t) - 1 *)
        (* This requires proving t is not MIN_INT, which is H_not_min *)
        
        rewrite sbv2int_sub_one with (n := n).
        
        (* Side goal 3: Prove size conditions for the subtraction lemma *)
        2: { exact Ht. }
        
        (* Side goal 4: Prove t <> min (The Guard) *)
        2: { exact H_not_min. }

        (* 3. Solve: The goal is now (val t - 1 < val t)%Z *)
        lia.
        
      }

      (* Step 3: Prove that ((t-1) & s) <= (t-1) *)
      (* This was your 'bvand_slt_helper1' *)
      assert (H_le : bv_sle (bv_and (bv_not (bv_neg t)) s) (bv_not (bv_neg t)) = true).
      {
        apply bv_and_neg_sle_itself with (n := n).
        - (* 1. size (bv_not (bv_neg t)) = n *)
          apply bv_not_size, bv_neg_size.
          exact Ht.
          
        - (* 2. size s = n *)
          exact Hs.
          
        - (* 3. bv_slt s (zeros n) = true *)
          exact H_sign.
      }
      
      
      apply (bv_sle_slt_trans H_le H_t_minus_1_lt).
    
    (* ========================================================== *)
    (* CASE 2: s is NON-NEGATIVE (s >= 0)                         *)
    (* ========================================================== *)
    +
      rewrite (bv_slt_negb_sle Hs (zeros_size n)) in H_sign. 
      apply negb_false_iff in H_sign.
      
      (* 2. Prove s is Positive (last bit is 0) *)
      rewrite <- Hs in H_sign.
      rewrite bv_zeros_sle in H_sign.
      apply negb_true_iff in H_sign.
       assert (H_and_sz : size (bv_and x s) = n).
        { apply bv_and_size; assumption. }
        
      (* 3. Prove (x & s) is Positive *)
      assert (H_xs_pos : last (bv_and x s) false = false).
      {
         Search "pos_bvand_pos".
         Search bv_and.
         rewrite (bv_and_comm Hx_size Hs).
         apply (pos_bvand_pos Hs Hx_size H_sign).  
      }
      destruct (bv_slt t (zeros n)) eqn:H_t_sign.
      * 
      (* Case 2a: t < 0 (Contradiction) *)
      (* 1. Prove t is Negative (last bit is 1) *)
      rewrite <- Ht in H_t_sign.
      rewrite bv_slt_zeros in H_t_sign. 
      (* H_t_sign: last t false = true *)

      assert (H_size_match : size t = size (bv_and x s)).
      { 
        rewrite H_and_sz.
        assumption.
      }
      (* 4. Use bv_slt_tf to prove t < (x & s) *)
      pose proof (bv_slt_tf H_size_match H_t_sign H_xs_pos) as H_contra.
      
      (* 5. Final Clash: (x&s) < t AND t < (x&s) implies (x&s) < (x&s) *)
      pose proof (bv_slt_trans H_contra Hx_lt) as H_impossible.
      rewrite bv_slt_nrefl in H_impossible.
      discriminate.
      *
      rewrite (bv_slt_negb_sle Ht (zeros_size n)) in H_t_sign. 
      apply negb_false_iff in H_t_sign.
      Search bv_sle.
      apply bv_sle_eq in H_t_sign.
      destruct H_t_sign as [H_t_pos | H_t_eq_0].
      **
        Check bv_sle_slt_trans.
        apply bv_sle_slt_trans with (b2 := bv_not (bv_neg t)).
        (* Subgoal 1: Prove ((t-1) & s) <= (t-1) . Need to prove bv_not (bv_neg t)) is pos given t > 0*)
        { 
          admit.
        }
    
        (* Subgoal 2: Prove (t-1) < t *)
        {
          (* 1. Bridge: Convert signed bitvector comparison to Integer comparison *)
          rewrite bv_slt_iff_sbv2int with (n := n).
          
          (* Side goal 1: Prove size (t-1) = n *)
          2: { 
          Search "bv_not_size".
            apply bv_not_size. 
            apply bv_neg_size.
            exact Ht. 
          }
          
          (* Side goal 2: Prove size t = n *)
          2: { exact Ht. }
          rewrite H_syntax_fix.

          (* 2. Arithmetic: Replace value of (t-1) with (val t) - 1 *)
          (* This requires proving t is not MIN_INT, which is H_not_min *)
          
          rewrite sbv2int_sub_one with (n := n).
          
          (* Side goal 3: Prove size conditions for the subtraction lemma *)
          2: { exact Ht. }
          
          (* Side goal 4: Prove t <> min (The Guard) *)
          2: { exact H_not_min. }

          (* 3. Solve: The goal is now (val t - 1 < val t)%Z *)
          lia.
        }             
      **
        (* 1. Replace t with 0 everywhere *)
        rewrite <- H_t_eq_0 in *.
        rewrite <- H_and_sz in Hx_lt.
        
        (* 2. Expose the contradiction in Hx_lt *)
        (* Hx_lt says: (x & s) < 0 *)
        (* This means the sign bit of (x & s) is 1 (true) *)
        rewrite (bv_slt_zeros (bv_and x s)) in Hx_lt.

        (* 4. Final Clash *)
        (* Hx_lt says it's true, H_pos says it's false *)
        rewrite H_xs_pos in Hx_lt.
        discriminate.
Admitted.

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

(* (* mins << s <s t + mins <=> (exists x, s << x <s t) *)
Theorem bvshl_slt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (bv_slt (bv_shl (signed_min n) s) (bv_add t (signed_min n)) = true)
    (exists (x : bitvector), (size x = n) /\ ((bv_slt (bv_shl s x) t) = true)).
Proof.
Admitted. *)

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
      apply first_bits_ule. unfold size. rewrite rev_length.
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
            * unfold size. rewrite app_length.
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
                @Coq.Lists.List.app_length, 
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
           rewrite <- rev_length in Hs.
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

(* t <u s | -s <=> (exists x, x * s >u t) *)
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

(* s | -s >=u t <=> (exists x, x * s >=u t) *)
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

(* (* ~(-t) & (-s | s) <s t <=> (exists x, x * s <s t) *)
Theorem bvmult_slt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists x, size x = n /\ bv_slt (bv_mult x s) t = true)
    (bv_slt (bv_and (bv_not (bv_neg t)) (bv_or (bv_neg s) s)) t = true).
Proof.
Admitted. *)
    
(* (* t <s t - ((s | t) | -s) <=> (exists x, x * s >s t) *)
Theorem bvmult_sgt: forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists x, size x = n /\ bv_slt t (bv_mult x s) = true)
    (bv_slt t (bv_subt t (bv_or (bv_or s t) (bv_neg s))) = true).
Proof.
Admitted. *)

(*------------------------------------------------------------*)

(*-----------------------Division 1---------------------------*)

(* (* (s * t) / t & s = s <=> (exists x, x /u s >=u t) *)
Theorem udiv_uge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_uge (bv_udiv x s) t = true)
    (bv_eq 
       (bv_and (bv_udiv (bv_mult s t) t) s) 
       s
    ) = true.
Proof.
Admitted. *)

(*------------------------------------------------------------*)

(*-----------------------Division 2---------------------------*)

(* (* n = 1 -> s & t = 0   (Otherwise True) <=> (exists x, s /s x != t) *)
Theorem sdiv_reverse_neq : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_eq (bv_sdiv s x) t = false)
    (if (N.eq_dec n 1) then
       bv_eq (bv_and s t) (zeros n)
     else
       true) = true.
Proof.
Admitted.

(* n=1 -> s >s t ; n!=1 -> ( (s >=s 0 => s >s t) /\ (s <s 0 => (s >> 1) >s t) ) 
<=> (exists x, s /s x != t) *)
Theorem sdiv_reverse_sgt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sgt (bv_sdiv s x) t = true)
    (if (N.eq_dec n 1) then
       bv_sgt s t
     else
       (
         (bv_sge s (zeros n) = true -> bv_sgt s t = true) /\
         (bv_slt s (zeros n) = true -> bv_sgt (bv_shr s (one n)) t = true)
       )
    ) = true.
Proof.
Admitted.

(* (s >=s 0 => s >=s t) /\ (s <s 0 => s >> 1 >=s t) <=> (exists x, s /s x != t) *)
Theorem sdiv_reverse_sge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sge (bv_sdiv s x) t = true)
    (
      (bv_sge s (zeros n) = true -> bv_sge s t = true) /\
      (bv_slt s (zeros n) = true -> bv_sge (bv_shr s (one n)) t = true)
    ) = true.
Proof.
Admitted. *)

(*------------------------------------------------------------*)

(*-----------------------Remainder 1--------------------------*)
(* (* ~t <s (-s | -t) <=> (exists x, (x srem s) <s t) *)
Theorem srem_slt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_slt (bv_srem x s) t = true)
    (bv_slt 
       (bv_not t) 
       (bv_or (bv_neg s) (bv_neg t))
    ) = true.
    
(* ~0 <s -s & t <=> (exists x, x srem s <=s t) *)
Theorem srem_sle : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sle (bv_srem x s) t = true)
    (bv_slt 
       (bv_not (zeros n)) 
       (bv_and (bv_neg s) t)
    ) = true.
Proof.
Admitted.
 *)
 
 (*------------------------------------------------------------*)
 (*-----------------------Remainder 2--------------------------*)
 
(* (* (t + t - s) & s >=u t <=> (exists x, s srem x = t) *)
Theorem srem_reverse_eq : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_eq (bv_srem s x) t = true)
    (bv_uge 
       (bv_and (bv_sub (bv_add t t) s) s) 
       t
    ) = true.
Proof.
Admitted.

(* (s >=s 0 => s >s t) /\ (s <s 0 => ((s - 1) >> 1) >s t) <=> (exists x, s srem x >s t) *)
Theorem srem_reverse_sgt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sgt (bv_srem s x) t = true)
    (
      (bv_sge s (zeros n) = true -> bv_sgt s t = true) /\
      (bv_slt s (zeros n) = true -> bv_sgt (bv_shr (bv_sub s (one n)) (one n)) t = true)
    ).
Proof.
Admitted.

(* (s >=s 0 => s >=s t) /\ ((s <s 0 /\ t >=s 0) => s - t >u t) <=> (exists x, s srem x >=s t) *)
Theorem srem_reverse_sge : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_sge (bv_srem s x) t = true)
    (
      (bv_sge s (zeros n) = true -> bv_sge s t = true) /\
      ((bv_slt s (zeros n) = true /\ bv_sge t (zeros n) = true) -> 
       bv_ugt (bv_sub s t) t = true)
    ).
Proof.
Admitted.
 *)
