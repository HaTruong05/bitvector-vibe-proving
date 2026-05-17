(**************************************************************************)
(*                                                                        *)
(*     DTBitVector                                                        *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller   *                                                 *)
(*     Alain   Mebsout  ♯                                                 *)
(*     Burak   Ekici    ♯                                                 *)
(*     Arjun Viswanathan♯                                                 *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.
Require Import Lia.
Require Import Coq.Structures.Equalities.
Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Reals.ArithProp.
(*Require Import Misc.*)
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.




Set Implicit Arguments.
Unset Strict Implicit.

(* From Hammer Require Import Hammer Reconstr. *)
From BV Require Import Reconstr.

(* (* We temporarily assume proof irrelevance to handle dependently typed
   bit vectors *)
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2. *)

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof. intros. lia. Qed.

  Fixpoint leb (n m: nat) : bool :=
    match n with
      | O => 
      match m with
        | O => true
        | S m' => true
      end
      | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
    end.

Module Type BITVECTOR.

  Parameter bitvector : N -> Type.
  Parameter bits      : forall n, bitvector n -> list bool.
  Parameter of_bits   : forall (l:list bool), bitvector (N.of_nat (List.length l)).
  Parameter bitOf     : forall n, nat -> bitvector n -> bool.

  (* Constants *)
  Parameter zeros     : forall n, bitvector n.
  Parameter one       : forall n, bitvector n.
  Parameter signed_min : forall n, bitvector n.
  Parameter signed_max : forall n, bitvector n.

  (*equality*)
  Parameter bv_eq     : forall n, bitvector n -> bitvector n -> bool.

  (*binary operations*)
  Parameter bv_concat : forall n m, bitvector n -> bitvector m -> bitvector (n + m).
  Parameter bv_and    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_or     : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_add    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_xor    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_subt   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_subt'  : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_mult   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ult    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_slt    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_ule    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_sle    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_uge    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_sge    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_ugt    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_sgt    : forall n, bitvector n -> bitvector n -> bool.

  Parameter bv_ultP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_sltP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_uleP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_sleP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_ugeP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_sgeP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_ugtP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_sgtP   : forall n, bitvector n -> bitvector n -> Prop.

  Parameter bv_shl    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_shr    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_shr_a  : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_shl_a  : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ashr   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ashr_a : forall n, bitvector n -> bitvector n -> bitvector n.

    (*unary operations*)
  Parameter bv_not    : forall n,     bitvector n -> bitvector n.
  Parameter bv_neg    : forall n,     bitvector n -> bitvector n.
  Parameter bv_extr   : forall (i n0 n1 : N), bitvector n1 -> bitvector n0.
  Parameter nat2bv    : forall (n: nat) (s: N), bitvector s.

 (* Parameter bv_extr   : forall (n i j : N) {H0: n >= j} {H1: j >= i}, bitvector n -> bitvector (j - i). *)

  Parameter bv_zextn  : forall (n i: N), bitvector n -> bitvector (i + n).
  Parameter bv_sextn  : forall (n i: N), bitvector n -> bitvector (i + n).
 (* Parameter bv_extr   : forall n i j : N, bitvector n -> n >= j -> j >= i -> bitvector (j - i). *)

  (* Specification *)
  Axiom bits_size     : forall n (bv:bitvector n), List.length (bits bv) = N.to_nat n.
(*   Axiom bv_eq_reflect : forall n (a b:bitvector n), bv_eq a b = true <-> a = b. *)
  Axiom bv_eq_refl    : forall n (a:bitvector n), bv_eq a a = true.

  Axiom bv_ult_B2P    : forall n (a b:bitvector n), bv_ult a b = true <-> bv_ultP a b.
  Axiom bv_slt_B2P    : forall n (a b:bitvector n), bv_slt a b = true <-> bv_sltP a b.
  Axiom bv_ult_not_eq : forall n (a b:bitvector n), bv_ult a b = true -> a <> b.
  Axiom bv_slt_not_eq : forall n (a b:bitvector n), bv_slt a b = true -> a <> b.
  Axiom bv_ult_not_eqP: forall n (a b:bitvector n), bv_ultP a b -> a <> b.
  Axiom bv_slt_not_eqP: forall n (a b:bitvector n), bv_sltP a b -> a <> b.
  Axiom bv_ugt_B2P    : forall n (a b:bitvector n), bv_ugt a b = true <-> bv_ugtP a b.
  Axiom bv_ugt_not_eq : forall n (a b:bitvector n), bv_ugt a b = true -> a <> b.
  Axiom bv_ugt_not_eqP: forall n (a b:bitvector n), bv_ugtP a b -> a <> b.
  Axiom bv_ule_B2P    : forall n (a b:bitvector n), bv_ule a b = true <-> bv_uleP a b.
  Axiom bv_uge_B2P    : forall n (a b:bitvector n), bv_uge a b = true <-> bv_ugeP a b.

  Axiom bv_and_comm   : forall n (a b:bitvector n), bv_eq (bv_and a b) (bv_and b a) = true.
  Axiom bv_or_comm    : forall n (a b:bitvector n), bv_eq (bv_or a b) (bv_or b a) = true.
  Axiom bv_add_comm   : forall n (a b:bitvector n), bv_eq (bv_add a b) (bv_add b a) = true. 

  Axiom bv_and_assoc  : forall n (a b c: bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Axiom bv_or_assoc   : forall n (a b c: bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Axiom bv_xor_assoc  : forall n (a b c: bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Axiom bv_add_assoc  : forall n (a b c: bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Axiom bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.

  Parameter _of_bits  : forall (l: list bool) (s : N), bitvector s.

  (** for invertibility conditions *)
  Parameter bv2nat_a: forall n, bitvector n -> nat.
  Axiom bv_add_subst_opp: forall n (a b: bitvector n), bv_eq (bv_add (bv_subt' a b) b) a = true.
  Axiom bv_ult_nat: forall n (a b: bitvector n), (bv_ult a b) = (bv2nat_a a <? bv2nat_a b)%nat.
(*   Axiom inv_bvadd: forall n, forall (s t : bitvector n),
    iff (exists (x : bitvector n), ((bv_add x s) = t)) True. *)

End BITVECTOR.

Module Type RAWBITVECTOR.

Parameter bitvector  : Type.
Parameter size       : bitvector -> N.
Parameter bits       : bitvector -> list bool.
Parameter of_bits    : list bool -> bitvector.
Parameter _of_bits   : list bool -> N -> bitvector.
Parameter bitOf      : nat -> bitvector -> bool.

(* Constants *)
Parameter zeros      : N -> bitvector.
Parameter one        : N -> bitvector.
Parameter signed_min : N -> bitvector.
Parameter signed_max : N -> bitvector.

(*equality*)
Parameter bv_eq      : bitvector -> bitvector -> bool.

(*binary operations*)
Parameter bv_concat  : bitvector -> bitvector -> bitvector.
Parameter bv_and     : bitvector -> bitvector -> bitvector.
Parameter bv_or      : bitvector -> bitvector -> bitvector.
Parameter bv_xor     : bitvector -> bitvector -> bitvector.
Parameter bv_add     : bitvector -> bitvector -> bitvector.
Parameter bv_mult    : bitvector -> bitvector -> bitvector.
Parameter bv_udiv    : bitvector -> bitvector -> bitvector.
Parameter bv_urem    : bitvector -> bitvector -> bitvector.
Parameter bv_subt    : bitvector -> bitvector -> bitvector.
Parameter bv_subt'   : bitvector -> bitvector -> bitvector.
Parameter bv_ult     : bitvector -> bitvector -> bool.
Parameter bv_slt     : bitvector -> bitvector -> bool.
Parameter bv_ule     : bitvector -> bitvector -> bool.
Parameter bv_sle     : bitvector -> bitvector -> bool.
Parameter bv_ugt     : bitvector -> bitvector -> bool.
Parameter bv_sgt     : bitvector -> bitvector -> bool.
Parameter bv_uge     : bitvector -> bitvector -> bool.
Parameter bv_sge     : bitvector -> bitvector -> bool.
Parameter bv2nat_a   : bitvector -> nat.


Parameter bv_ultP    : bitvector -> bitvector -> Prop.
Parameter bv_sltP    : bitvector -> bitvector -> Prop.
Parameter bv_uleP    : bitvector -> bitvector -> Prop.
Parameter bv_sleP    : bitvector -> bitvector -> Prop.
Parameter bv_ugtP    : bitvector -> bitvector -> Prop.
Parameter bv_sgtP    : bitvector -> bitvector -> Prop.
Parameter bv_ugeP    : bitvector -> bitvector -> Prop.
Parameter bv_sgeP    : bitvector -> bitvector -> Prop.


Parameter bv_shl     : bitvector -> bitvector -> bitvector.
Parameter bv_shr     : bitvector -> bitvector -> bitvector.
Parameter bv_shr_a   : bitvector -> bitvector -> bitvector.
Parameter bv_shl_a   : bitvector -> bitvector -> bitvector.
Parameter bv_ashr    : bitvector -> bitvector -> bitvector.
Parameter bv_ashr_a  : bitvector -> bitvector -> bitvector.

(*unary operations*)
Parameter bv_not     : bitvector -> bitvector.
Parameter bv_neg     : bitvector -> bitvector.
Parameter bv_extr    : forall (i n0 n1: N), bitvector -> bitvector.


(*Parameter bv_extr    : forall (n i j: N) {H0: n >= j} {H1: j >= i}, bitvector -> bitvector.*)

Parameter bv_zextn   : forall (n i: N), bitvector -> bitvector.
Parameter bv_sextn   : forall (n i: N), bitvector -> bitvector.
Parameter nat2bv     : forall (n: nat) (s: N), bitvector.

(* All the operations are size-preserving *)

Axiom bits_size      : forall bv, List.length (bits bv) = N.to_nat (size bv).
Axiom of_bits_size   : forall l, N.to_nat (size (of_bits l)) = List.length l.
Axiom _of_bits_size  : forall l s,(size (_of_bits l s)) = s.
Axiom zeros_size     : forall n, size (zeros n) = n.
Axiom one_size       : forall n, size (one n) = n.
Axiom signed_min_size : forall n, size (signed_min n) = n.
Axiom signed_max_size : forall n, size (signed_max n) = n.
Axiom bv_concat_size : forall n m a b, size a = n -> size b = m -> size (bv_concat a b) = n + m.
Axiom bv_and_size    : forall n a b, size a = n -> size b = n -> size (bv_and a b) = n.
Axiom bv_or_size     : forall n a b, size a = n -> size b = n -> size (bv_or a b) = n.
Axiom bv_xor_size    : forall n a b, size a = n -> size b = n -> size (bv_xor a b) = n.
Axiom bv_add_size    : forall n a b, size a = n -> size b = n -> size (bv_add a b) = n.
Axiom bv_subt_size   : forall n a b, size a = n -> size b = n -> size (bv_subt a b) = n.
Axiom bv_subt'_size  : forall n a b, size a = n -> size b = n -> size (bv_subt' a b) = n.
Axiom bv_mult_size   : forall n a b, size a = n -> size b = n -> size (bv_mult a b) = n.
Axiom bv_udiv_size   : forall n a b, size a = n -> size b = n -> size (bv_udiv a b) = n.
Axiom bv_urem_size   : forall n a b, size a = n -> size b = n -> size (bv_urem a b) = n.
Axiom bv_not_size    : forall n a, size a = n -> size (bv_not a) = n.
Axiom bv_neg_size    : forall n a, size a = n -> size (bv_neg a) = n.
Axiom bv_shl_size    : forall n a b, size a = n -> size b = n -> size (bv_shl a b) = n.
Axiom bv_shr_size    : forall n a b, size a = n -> size b = n -> size (bv_shr a b) = n.
Axiom bv_shr_a_size  : forall n a b, size a = n -> size b = n -> size (bv_shr_a a b) = n.
Axiom bv_shl_a_size  : forall n a b, size a = n -> size b = n -> size (bv_shl_a a b) = n.
Axiom bv_ashr_size   : forall n a b, size a = n -> size b = n -> size (bv_ashr a b) = n.
Axiom bv_ashr_a_size : forall n a b, size a = n -> size b = n -> size (bv_ashr_a a b) = n.
Axiom bv_extr_size   : forall i n0 n1 a, size a = n1 -> size (@bv_extr i n0 n1 a) = n0.

(*
Axiom bv_extr_size   : forall n (i j: N) a (H0: n >= j) (H1: j >= i), 
  size a = n -> size (@bv_extr n i j H0 H1 a) = (j - i).
*)

Axiom bv_zextn_size  : forall (n i: N) a, 
  size a = n -> size (@bv_zextn n i a) = (i + n).
Axiom bv_sextn_size  : forall (n i: N) a, 
  size a = n -> size (@bv_sextn n i a) = (i + n).

(* Specification *)
Axiom bv_eq_reflect  : forall a b, bv_eq a b = true <-> a = b.
Axiom bv_eq_refl     : forall a, bv_eq a a = true.


Axiom bv_ult_not_eq  : forall a b, bv_ult a b = true -> a <> b.
Axiom bv_slt_not_eq  : forall a b, bv_slt a b = true -> a <> b.
Axiom bv_ult_not_eqP : forall a b, bv_ultP a b -> a <> b.
Axiom bv_slt_not_eqP : forall a b, bv_sltP a b -> a <> b.
Axiom bv_ult_B2P     : forall a b, bv_ult a b = true <-> bv_ultP a b.
Axiom bv_slt_B2P     : forall a b, bv_slt a b = true <-> bv_sltP a b.
Axiom bv_ugt_not_eq  : forall a b, bv_ugt a b = true -> a <> b.
Axiom bv_ugt_not_eqP : forall a b, bv_ugtP a b -> a <> b.
Axiom bv_ugt_B2P     : forall a b, bv_ugt a b = true <-> bv_ugtP a b.
Axiom bv_ule_B2P     : forall a b, bv_ule a b = true <-> bv_uleP a b.
Axiom bv_uge_B2P     : forall a b, bv_uge a b = true <-> bv_ugeP a b.

Axiom bv_and_comm    : forall n a b, size a = n -> size b = n -> bv_and a b = bv_and b a.
Axiom bv_or_comm     : forall n a b, size a = n -> size b = n -> bv_or a b = bv_or b a.
Axiom bv_add_comm    : forall n a b, size a = n -> size b = n -> bv_add a b = bv_add b a.

Axiom bv_and_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Axiom bv_or_assoc    : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Axiom bv_xor_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Axiom bv_add_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Axiom bv_not_involutive: forall a, bv_not (bv_not a) = a.

(** for invertibility conditions *)
Axiom bv_add_subst_opp:  forall n a b, (size a) = n -> (size b) = n -> (bv_add (bv_subt' a b) b) = a.
Axiom bv_ult_nat: forall a b, (size a) =? (size b) = true -> (bv_ult a b) = (bv2nat_a a <? bv2nat_a b)%nat.
Axiom nat2bv_size   : forall (n: nat) (s: N), size (nat2bv n s) = s.
(* Axiom inv_bvadd: forall (n : N) (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
  (exists (x : bitvector) (p: size x = n), ((bv_add x s) = t))
  True. *)

End RAWBITVECTOR.

Module RAW2BITVECTOR (M:RAWBITVECTOR) <: BITVECTOR.

  Record bitvector_ (n:N) : Type :=
    MkBitvector
      { bv :> M.bitvector;
        wf : M.size bv = n
      }.
  Definition bitvector := bitvector_.

  Definition bits n (bv:bitvector n) := M.bits bv.

  Lemma of_bits_size l : M.size (M.of_bits l) = N.of_nat (List.length l).
  Proof. now rewrite <- M.of_bits_size, N2Nat.id. Qed.

  Lemma _of_bits_size l s: M.size (M._of_bits l s) = s.
  Proof. apply (M._of_bits_size l s). Qed. 

  Definition of_bits (l:list bool) : bitvector (N.of_nat (List.length l)) :=
    @MkBitvector _ (M.of_bits l) (of_bits_size l).

  Definition _of_bits (l: list bool) (s : N): bitvector s :=
  @MkBitvector _ (M._of_bits l s) (_of_bits_size l s).

  Definition bitOf n p (bv:bitvector n) : bool := M.bitOf p bv.

  Definition zeros (n:N) : bitvector n :=
    @MkBitvector _ (M.zeros n) (M.zeros_size n).

  Definition one (n:N) : bitvector n :=
    @MkBitvector _ (M.one n) (M.one_size n).

  Definition signed_min (n:N) : bitvector n :=
    @MkBitvector _ (M.signed_min n) (M.signed_min_size n).

  Definition signed_max (n:N) : bitvector n :=
    @MkBitvector _ (M.signed_max n) (M.signed_max_size n).

  Definition nat2bv (n: nat) (s: N): bitvector s.
  Proof. specialize (@MkBitvector s (M.nat2bv n s)); intros. apply X.
         now rewrite M.nat2bv_size.
  Defined.

  Definition bv_eq n (bv1 bv2:bitvector n) := M.bv_eq bv1 bv2.

  Definition bv_ultP n (bv1 bv2:bitvector n) := M.bv_ultP bv1 bv2.

  Definition bv_sltP n (bv1 bv2:bitvector n) := M.bv_sltP bv1 bv2.

  Definition bv_uleP n (bv1 bv2:bitvector n) := M.bv_uleP bv1 bv2.

  Definition bv_sleP n (bv1 bv2:bitvector n) := M.bv_sleP bv1 bv2.

  Definition bv_ugtP n (bv1 bv2:bitvector n) := M.bv_ugtP bv1 bv2.

  Definition bv_sgtP n (bv1 bv2:bitvector n) := M.bv_sgtP bv1 bv2.

  Definition bv_ugeP n (bv1 bv2:bitvector n) := M.bv_ugeP bv1 bv2.

  Definition bv_sgeP n (bv1 bv2:bitvector n) := M.bv_sgeP bv1 bv2.

  Definition bv_and n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_and bv1 bv2) (M.bv_and_size (wf bv1) (wf bv2)).

  Definition bv_or n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_or bv1 bv2) (M.bv_or_size (wf bv1) (wf bv2)).

  Definition bv_add n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_add bv1 bv2) (M.bv_add_size (wf bv1) (wf bv2)).

  Definition bv_subt n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_subt bv1 bv2) (M.bv_subt_size (wf bv1) (wf bv2)).

  Definition bv_subt' n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_subt' bv1 bv2) (M.bv_subt'_size (wf bv1) (wf bv2)).

  Definition bv_mult n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_mult bv1 bv2) (M.bv_mult_size (wf bv1) (wf bv2)).

  Definition bv_udiv n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_udiv bv1 bv2) (M.bv_udiv_size (wf bv1) (wf bv2)).

  Definition bv_urem n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_urem bv1 bv2) (M.bv_urem_size (wf bv1) (wf bv2)).

  Definition bv_xor n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_xor bv1 bv2) (M.bv_xor_size (wf bv1) (wf bv2)).

  Definition bv_ult n (bv1 bv2:bitvector n) : bool := M.bv_ult bv1 bv2.

  Definition bv_slt n (bv1 bv2:bitvector n) : bool := M.bv_slt bv1 bv2.

  Definition bv_ule n (bv1 bv2:bitvector n) : bool := M.bv_ule bv1 bv2. 

  Definition bv_sle n (bv1 bv2:bitvector n) : bool := M.bv_sle bv1 bv2. 

  Definition bv_ugt n (bv1 bv2:bitvector n) : bool := M.bv_ugt bv1 bv2.

  Definition bv_sgt n (bv1 bv2:bitvector n) : bool := M.bv_sgt bv1 bv2.

  Definition bv_uge n (bv1 bv2:bitvector n) : bool := M.bv_uge bv1 bv2.

  Definition bv_sge n (bv1 bv2:bitvector n) : bool := M.bv_sge bv1 bv2.

  Definition bv2nat_a n (bv1: bitvector n) : nat := M.bv2nat_a bv1.

  Definition bv_not n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_not bv1) (M.bv_not_size (wf bv1)).

  Definition bv_neg n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_neg bv1) (M.bv_neg_size (wf bv1)).

  Definition bv_concat n m (bv1:bitvector n) (bv2: bitvector m) : bitvector (n + m) :=
    @MkBitvector (n + m) (M.bv_concat bv1 bv2) (M.bv_concat_size (wf bv1) (wf bv2)).

  Definition bv_extr (i n0 n1: N) (bv1: bitvector n1) : bitvector n0 :=
    @MkBitvector n0 (@M.bv_extr i n0 n1 bv1) (@M.bv_extr_size i n0 n1 bv1 (wf bv1)).

(*
  Definition bv_extr  n (i j: N) (H0: n >= j) (H1: j >= i) (bv1: bitvector n) : bitvector (j - i) :=
    @MkBitvector (j - i) (@M.bv_extr n i j H0 H1 bv1) (@M.bv_extr_size n i j bv1 H0 H1 (wf bv1)).
*)

  Definition bv_zextn n (i: N)  (bv1: bitvector n) : bitvector (i + n) :=
    @MkBitvector (i + n) (@M.bv_zextn n i bv1) (@M.bv_zextn_size n i bv1 (wf bv1)).

  Definition bv_sextn n (i: N)  (bv1: bitvector n) : bitvector (i + n) :=
    @MkBitvector (i + n) (@M.bv_sextn n i bv1) (@M.bv_sextn_size n i bv1 (wf bv1)).

  Definition bv_shl n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shl bv1 bv2) (M.bv_shl_size (wf bv1) (wf bv2)).

  Definition bv_shr n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shr bv1 bv2) (M.bv_shr_size (wf bv1) (wf bv2)).

  Definition bv_ashr n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_ashr bv1 bv2) (M.bv_ashr_size (wf bv1) (wf bv2)).

  Definition bv_shr_a n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shr_a bv1 bv2) (M.bv_shr_a_size (wf bv1) (wf bv2)).

  Definition bv_shl_a n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shl_a bv1 bv2) (M.bv_shl_a_size (wf bv1) (wf bv2)).

  Definition bv_ashr_a n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_ashr_a bv1 bv2) (M.bv_ashr_a_size (wf bv1) (wf bv2)).

  Lemma bits_size n (bv:bitvector n) : List.length (bits bv) = N.to_nat n.
  Proof. unfold bits. now rewrite M.bits_size, wf. Qed.

(*   (* The next lemma is provable only if we assume proof irrelevance *)
  Lemma bv_eq_reflect n (a b: bitvector n) : bv_eq a b = true <-> a = b.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. split.
    - revert a b. intros [a Ha] [b Hb]. simpl. intros ->.
      rewrite (proof_irrelevance Ha Hb). reflexivity.
    - intros. case a in *. case b in *. simpl in *.
      now inversion H. (* now intros ->. *)
  Qed. *)

  Lemma bv_exists: forall n (P: M.bitvector -> Prop),
  (exists (x: bitvector n), P (bv x)) <-> (exists x: M.bitvector, M.size x = n /\ P x).
  Proof.
    split; intros.
    destruct H as (x, p).
    exists (bv x). split.
    apply (wf x). easy.
    destruct H as (x, (wf, p)). cbn.
    exists (@MkBitvector n x wf). now simpl.
  Qed.

  Lemma bv_existsn: forall n (P: bitvector n -> Prop),
  (exists (x: bitvector n), P x) <->
  (exists (x: M.bitvector) (p: M.size x = n), P (@MkBitvector n x p)).
  Proof.
    split; intros.
    destruct H as (x, p).
    exists (bv x). exists (wf x).
    destruct x. cbn in *. easy.
    destruct H as (x, (wf, p)). cbn.
    exists (@MkBitvector n x wf). now simpl.
  Qed.


  Lemma bv_eq_refl n (a : bitvector n) : bv_eq a a = true.
  Proof.
    unfold bv_eq. now rewrite M.bv_eq_reflect.
  Qed.

  Lemma bv_ult_not_eqP: forall n (a b: bitvector n), bv_ultP a b -> a <> b.
  Proof. 
    unfold bv_ultP, bv_ult. intros n a b H.
    apply M.bv_ult_not_eqP in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_slt_not_eqP: forall n (a b: bitvector n), bv_sltP a b -> a <> b.
  Proof. 
    unfold bv_sltP, bv_slt. intros n a b H.
    apply M.bv_slt_not_eqP in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_ugt_not_eqP: forall n (a b: bitvector n), bv_ugtP a b -> a <> b.
  Proof.
    unfold bv_ugtP, bv_ugt. intros n a b H.
    apply M.bv_ugt_not_eqP in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed. 

  Lemma bv_ult_not_eq: forall n (a b: bitvector n), bv_ult a b = true -> a <> b.
  Proof. 
    unfold bv_ult. intros n a b H.
    apply M.bv_ult_not_eq in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_slt_not_eq: forall n (a b: bitvector n), bv_slt a b = true -> a <> b.
  Proof. 
    unfold bv_slt. intros n a b H.
    apply M.bv_slt_not_eq in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_ugt_not_eq: forall n (a b: bitvector n), bv_ugt a b = true -> a <> b.
  Proof.
    unfold bv_ugt. intros n a b H.
    apply M.bv_ugt_not_eq in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_ult_B2P: forall n (a b: bitvector n), bv_ult a b = true <-> bv_ultP a b.
  Proof. 
      unfold bv_ultP, bv_ult; intros; split; intros;
      now apply M.bv_ult_B2P.
  Qed. 

  Lemma bv_slt_B2P: forall n (a b: bitvector n), bv_slt a b = true <-> bv_sltP a b.
  Proof. 
      unfold bv_sltP, bv_slt; intros; split; intros;
      now apply M.bv_slt_B2P.
  Qed.

  Lemma bv_ugt_B2P: forall n (a b: bitvector n), bv_ugt a b = true <-> bv_ugtP a b.
  Proof.
      unfold bv_ugtP, bv_ugt; intros; split; intros;
      now apply M.bv_ugt_B2P.
  Qed.

  Lemma bv_ule_B2P: forall n (a b: bitvector n), bv_ule a b = true <-> bv_uleP a b.
  Proof.
      unfold bv_uleP, bv_ule; intros; split; intros;
      now apply M.bv_ule_B2P.
  Qed.

  Lemma bv_uge_B2P: forall n (a b: bitvector n), bv_uge a b = true <-> bv_ugeP a b.
  Proof.
      unfold bv_ugeP, bv_uge; intros; split; intros;
      now apply M.bv_uge_B2P.
  Qed.

  Lemma bv_and_comm n (a b:bitvector n) : bv_eq (bv_and a b) (bv_and b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_and_comm n); now rewrite wf.
  Qed.

  Lemma bv_or_comm n (a b:bitvector n) : bv_eq (bv_or a b) (bv_or b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_or_comm n); now rewrite wf.
  Qed.

  Lemma bv_add_comm n (a b:bitvector n) : bv_eq (bv_add a b) (bv_add b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_add_comm n); now rewrite wf.
  Qed.

  Lemma bv_and_assoc : forall n (a b c :bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_and_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_or_assoc : forall n (a b c :bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_or_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_xor_assoc : forall n (a b c :bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_xor_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_add_assoc : forall n (a b c :bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_add_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.
  Proof.
       intros n a.
       unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
       apply (@M.bv_not_involutive a); now rewrite wf.
  Qed.

(** for invertibility conditions *)
 Lemma bv_add_subst_opp: forall n (a b: bitvector n), bv_eq (bv_add (bv_subt' a b) b) a = true.
 Proof. intros n a b. unfold bv_eq.
         rewrite M.bv_eq_reflect. simpl. 
         erewrite M.bv_add_subst_opp;try easy.
         now rewrite !wf.
  Qed.

Lemma bv_ult_nat: forall n (a b: bitvector n), (bv_ult a b) = (bv2nat_a a <? bv2nat_a b)%nat.
 Proof. intros n a b.
         unfold bv2nat_a, bv_ult.
         erewrite M.bv_ult_nat. easy.
         now rewrite !wf, N.eqb_refl.
  Qed.

End RAW2BITVECTOR.

Module RAWBITVECTOR_LIST <: RAWBITVECTOR.

Definition bitvector := list bool.
Definition bits (a:bitvector) : list bool := a.
Definition size (a:bitvector) := N.of_nat (List.length a).
Definition of_bits (a:list bool) : bitvector := a.

Lemma size_rev : forall (l : bitvector), size (rev l) = size l.
Proof.
  intros l.
  unfold size. 
  rewrite length_rev.
  reflexivity.
Qed.

Lemma bits_size bv : List.length (bits bv) = N.to_nat (size bv).
Proof. unfold bits, size. now rewrite Nat2N.id. Qed.

Lemma of_bits_size l : N.to_nat (size (of_bits l)) = List.length l.
Proof. unfold of_bits, size. now rewrite Nat2N.id. Qed.

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Definition bv_eq (a b: bitvector): bool:=
  if ((size a) =? (size b)) then beq_list (bits a) (bits b) else false.

Fixpoint beq_listP (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => True
    | x :: l', y :: m' => (x = y) /\ (beq_listP l' m')
    | _, _ => False
  end.


Lemma bv_mk_eq l1 l2 : bv_eq l1 l2 = beq_list l1 l2.
Proof.
  unfold bv_eq, size, bits.
  case_eq (Nat.eqb (length l1) (length l2)); intro Heq.
  - specialize Nat.eqb_eq; intro H.
    destruct (H (length l1) (length l2)) as (H1,H2).
    specialize(H1 Heq).
    now rewrite H1, N.eqb_refl.
  - replace (N.of_nat (length l1) =? N.of_nat (length l2)) with false.
    * revert l2 Heq. induction l1 as [ |b1 l1 IHl1]; intros [ |b2 l2]; simpl in *; auto.
      intro Heq. now rewrite <- (IHl1 _ Heq), andb_false_r.
    * symmetry. rewrite N.eqb_neq. intro H. apply Nat2N.inj in H. rewrite H in Heq.
      rewrite Nat.eqb_refl in Heq. discriminate.
Qed.

Definition bv_concat (a b: bitvector) : bitvector := b ++ a.

Section Map2.

  Variables A B C: Type.
  Variable f : A -> B -> C.

  Fixpoint map2 (l1 : list A) (l2 : list B) {struct l1} : list C :=
    match l1, l2 with
      | b1::tl1, b2::tl2 => (f b1 b2)::(map2 tl1 tl2)
      | _, _ => nil
    end.

End Map2.

Section Fold_left2.

  Variables A B: Type.
  Variable f : A -> B -> B -> A.

  Fixpoint fold_left2 (xs ys: list B) (acc:A) {struct xs} : A :=
    match xs, ys with
    | nil, _ | _, nil => acc
    | x::xs, y::ys    => fold_left2 xs ys (f acc x y)
    end.

  Lemma foo : forall (I: A -> Prop) acc, I acc -> 
              (forall a b1 b2, I a -> I (f a b1 b2)) -> 
              forall xs ys, I (fold_left2 xs ys acc).
  Proof. intros I acc H0 H1 xs. revert acc H0.
         induction xs as [ | a xs IHxs]; intros acc H.
         simpl. auto.
         intros [ | b ys].
            + simpl. exact H.
            + simpl. apply IHxs, H1. exact H.
  Qed.

Fixpoint mk_list_true_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_true_acc t' (true::acc)
  end.

Fixpoint mk_list_true (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => true::(mk_list_true t')
  end.

Definition ones (n : N) : bitvector := mk_list_true (N.to_nat n).

Fixpoint mk_list_false_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_false_acc t' (false::acc)
  end.

Fixpoint mk_list_false (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => false::(mk_list_false t')
  end.

Definition zeros (n : N) : bitvector := mk_list_false (N.to_nat n).

End Fold_left2.

Fixpoint mk_list_one (t: nat) : list bool := 
  match t with
    | O => []
    | S O => [true]
    | S t' => false :: (mk_list_one t')
  end.

Definition one (n : N) : bitvector := rev (mk_list_one (N.to_nat n)).

Definition bitOf (n: nat) (a: bitvector): bool := nth n a false.

(* rev (mk_list_true n) = mk_list_true n *)
Lemma mk_list_true_succ : forall (n : nat), 
mk_list_true (S n) = true :: mk_list_true n.
Proof.
  intros. easy.
Qed.

Lemma mk_list_true_app : forall (n : nat),
mk_list_true (S n) = (mk_list_true n) ++ [true].
Proof.
  intros. induction n.
  + easy.
  + rewrite mk_list_true_succ. rewrite mk_list_true_succ.
    assert (forall (a b : bool) (l : list bool), (b :: l) ++ [a]
      = b :: (l ++ [a])).
    { easy. }
    rewrite H. rewrite <- IHn. rewrite mk_list_true_succ. easy.
Qed.

Lemma rev_mk_list_true : forall n : nat, 
  rev (mk_list_true n) = mk_list_true n.
Proof. 
  intros. induction n.
  + easy.
  + simpl. rewrite IHn. induction n.
    - easy.
    - rewrite mk_list_true_app at 2. rewrite mk_list_true_succ at 1.
      easy.
Qed.

(* rev (mk_list_false n) = mk_list_false n *)
Lemma mk_list_false_succ : forall (n : nat), 
mk_list_false (S n) = false :: mk_list_false n.
Proof.
  intros. easy.
Qed.

Lemma mk_list_false_app : forall (n : nat),
mk_list_false (S n) = (mk_list_false n) ++ [false].
Proof.
  intros. induction n.
  + easy.
  + rewrite mk_list_false_succ. rewrite mk_list_false_succ.
    assert (forall (a b : bool) (l : list bool), (b :: l) ++ [a]
      = b :: (l ++ [a])).
    { easy. }
    rewrite H. rewrite <- IHn. rewrite mk_list_false_succ. easy.
Qed.

Lemma rev_mk_list_false : forall n : nat, 
  rev (mk_list_false n) = mk_list_false n.
Proof. 
  intros. induction n.
  + easy.
  + simpl. rewrite IHn. induction n.
    - easy.
    - rewrite mk_list_false_app at 2. rewrite mk_list_false_succ at 1.
      easy.
Qed.

(* mk_list_false (n + m) = mk_list_false n ++ mk_list_false m *)
Lemma mk_list_false_plus : forall (n m : nat),
  mk_list_false (n + m) = mk_list_false n ++ mk_list_false m.
Proof.
  intros. induction n.
  + easy.
  + simpl. now rewrite IHn.
Qed.

(* forall x : bitvector, size(x) >= 0 *)

Theorem length_of_tail : forall (h : bool) (t : list bool), 
 length (h :: t) = S (length t).
  intros h t.
Proof. 
  induction t; reflexivity.
Qed.

Theorem non_empty_list_size : forall (h : bool) (t : list bool),
          N.to_nat (size (h :: t)) = S (N.to_nat (size t)).
Proof.
  intros h t. induction t as [| h' t' IHt].
    + reflexivity.
    + unfold size in *. rewrite -> length_of_tail.
      rewrite -> length_of_tail. rewrite -> Nat2N.id in *.
      rewrite -> Nat2N.id. reflexivity.
Qed.

Theorem succ_gt_pred : forall (n : nat), (n >= 0)%nat -> (S n >= 0)%nat.
Proof.
  intros n. induction n as [| n' IHn].
  + unfold ge. intros H. apply Nat.le_0_l.
  + unfold ge. intros H. auto.
Qed.

Theorem bv_size_nonnegative : forall (x : bitvector), (N.to_nat(size x) >= 0)%nat.
Proof.
  intros x. induction x.
  - auto.
  - rewrite -> non_empty_list_size. unfold size in *. 
    rewrite -> Nat2N.id in *. apply succ_gt_pred. apply IHx.
  Qed.



(* Logical Operations *)

(* and *)
Definition bv_and (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 andb (@bits a) (@bits b)
    | _    => nil
  end.

(* or *)
Definition bv_or (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 orb (@bits a) (@bits b)
    | _    => nil
  end.

(* xor *)
Definition bv_xor (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 xorb (@bits a) (@bits b)
    | _    => nil
  end.

(* not *)
Definition bv_not (a: bitvector) : bitvector := map negb (@bits a).



(* Arithmetic Operations *)

(* addition *)
Definition add_carry b1 b2 c :=
  match b1, b2, c with
    | true,  true,  true  => (true, true)
    | true,  true,  false
    | true,  false, true
    | false, true,  true  => (false, true)
    | false, false, true
    | false, true,  false
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

(* Truncating addition in little-endian, direct style *)
Fixpoint add_list_ingr bs1 bs2 c {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, c) := add_carry b1 b2 c in r :: (add_list_ingr bs1 bs2 c)
  end.

Definition add_list (a b: list bool) := add_list_ingr a b false.

Definition bv_add (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => add_list a b
    | _    => nil
  end.


(* subtraction *)

(* Using 2's Complement *)
Definition twos_complement b :=
  add_list_ingr (map negb b) (mk_list_false (length b)) true.
  
Definition bv_neg (a: bitvector) : bitvector := (twos_complement a).

Definition subst_list' a b := add_list a (twos_complement b).

Definition bv_subt' (a b : bitvector) : bitvector :=
   match (@size a) =? (@size b) with
     | true => (subst_list' (@bits a) (@bits b))
     | _    => nil
   end.

(* Using Borrow *)
Definition subst_borrow b1 b2 b :=
  match b1, b2, b with
    | true,  true,  true  => (true, true)
    | true,  true,  false => (false, false)
    | true,  false, true  => (false, false)
    | false, true,  true  => (false, true)
    | false, false, true  => (true, true)
    | false, true,  false => (true, true)
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

Fixpoint subst_list_borrow bs1 bs2 b {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, b) := subst_borrow b1 b2 b in r :: (subst_list_borrow bs1 bs2 b)
  end.

Definition subst_list (a b: list bool) := subst_list_borrow a b false.

Definition bv_subt (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with 
    | true => subst_list (@bits a) (@bits b)
    | _    => nil 
  end.


(* multiplication *)
Fixpoint mult_list_carry (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry xs (false :: b) n)
      else
        mult_list_carry xs (false :: b) n
  end.

Fixpoint mult_list_carry2 (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry2 xs (false :: (removelast b)) n)
      else
        mult_list_carry2 xs (false :: (removelast b)) n
  end.
  
Fixpoint and_with_bool (a: list bool) (bt: bool) : list bool :=
  match a with
    | nil => nil
    | ai :: a' => (bt && ai) :: and_with_bool a' bt 
  end.

Fixpoint mult_bool_step_k_h (a b: list bool) (c: bool) (k: Z) : list bool :=
  match a, b with
    | nil , _ => nil
    | ai :: a', bi :: b' =>
      if ((k - 1)%Z <? 0)%Z then
        let carry_out := (ai && bi) || ((xorb ai bi) && c) in
        let curr := xorb (xorb ai bi) c in
        curr :: mult_bool_step_k_h a' b' carry_out (k - 1)
      else
        ai :: mult_bool_step_k_h a' b c (k - 1)
    | ai :: a' , nil => ai :: mult_bool_step_k_h a' b c k
  end.

Fixpoint top_k_bools (a: list bool) (k: Z) : list bool :=
  if (Z.eqb k 0) then nil
  else match a with
         | nil => nil
         | ai :: a' => ai :: top_k_bools a' (k - 1)
       end.

Fixpoint mult_bool_step (a b: list bool) (res: list bool) (k k': nat) : list bool :=
  let ak := List.firstn (S k') a in
  let b' := and_with_bool ak (nth k b false) in
  let res' := mult_bool_step_k_h res b' false (Z.of_nat k) in
  match k' with
    | O => res'
    (* | S O => res' *)
    | S pk' => mult_bool_step a b res' (S k) pk'
  end.

Definition bvmult_bool (a b: list bool) (n: nat) : list bool :=
  let res := and_with_bool a (nth 0 b false) in
  match n with
    | O => res
    | S O => res
    | S (S k) => mult_bool_step a b res 1 k
  end.

Definition mult_list a b := bvmult_bool a b (length a).

Definition bv_mult (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then mult_list a b
  else nil.



(* Comparison Operations *)
  
(* less than *)

(* unsigned less than *)
Fixpoint ult_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => andb (negb xi) yi
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ult_list_big_endian x' y'))
          (andb (negb xi) yi)
  end.

(* bool output *)
Definition ult_list (x y: list bool) :=
  (ult_list_big_endian (List.rev x) (List.rev y)).

Definition bv_ult (a b : bitvector) : bool :=
  if @size a =? @size b then ult_list a b else false.

(* Prop output *)
Definition ult_listP (x y: list bool) :=
  if ult_list x y then True else False.

Definition bv_ultP (a b : bitvector) : Prop :=
  if @size a =? @size b then ult_listP a b else False.


(* unsigned less than or equal to *)
Fixpoint ule_list_big_endian (x y : list bool) :=
  match x, y with
  | nil, nil => true
  | nil, _ => false 
  | _, nil => false 
  | xi :: x', yi :: y' =>
    orb (andb (Bool.eqb xi yi) (ule_list_big_endian x' y'))
          (andb (negb xi) yi)
  end. 

(* bool output *)
Definition ule_list (x y: list bool) :=
  (ule_list_big_endian (List.rev x) (List.rev y)).

Definition bv_ule (a b : bitvector) : bool :=
  if @size a =? @size b then ule_list a b else false.

(* Prop output *)
Definition ule_listP (x y: list bool) :=
  if ule_list x y then True else False.

Definition bv_uleP (a b : bitvector) : Prop :=
  if @size a =? @size b then ule_listP a b else False.


(* signed less than *)
Definition slt_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ult_list_big_endian x' y'))
          (andb xi (negb yi))
  end.

(* bool output *)
Definition slt_list (x y: list bool) :=
  slt_list_big_endian (List.rev x) (List.rev y).

Lemma ult_slt_eq: forall a b x, ult_list_big_endian (x :: a) (x :: b) =
                                 slt_list_big_endian (x :: a) (x :: b).
Proof. intros. simpl.
        case_eq a; intros. 
        + cbn.
          Reconstr.reasy (@Coq.Bool.Bool.andb_negb_r) 
            (@Coq.Init.Datatypes.negb, @Coq.Init.Datatypes.andb).
        + f_equal.
	        Reconstr.reasy (@Coq.Bool.Bool.andb_negb_r)
            (@Coq.Init.Datatypes.andb, @Coq.Init.Datatypes.negb).
Qed.

Definition bv_slt (a b : bitvector) : bool :=
  if @size a =? @size b then slt_list a b else false.

Lemma bv_slt_ult_eq: forall a b x, bv_slt (a ++ [x]) (b ++ [x]) = 
                                    bv_ult (a ++ [x]) (b ++ [x]).
Proof. intros. unfold bv_slt, bv_ult, slt_list, ult_list.
        case (size (a ++ [x]) =? size (b ++ [x])).
        - now rewrite !rev_unit, ult_slt_eq.
        - easy.
Qed.


Lemma last_app: forall {A: Type} (a: list A) x d, List.last (a ++ [x]) d = x.
Proof. intros A a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq (a0 ++ [x]); intros.
          + contradict H.
            destruct a0; easy.
          + now rewrite <- H.
Qed.

Lemma last_eq: forall {A: Type} (a b: list A) x y d,
  List.last (a ++ [x]) d = List.last (b ++ [y]) d -> x = y.
Proof. intros. now rewrite !last_app in H. Qed.

Lemma bv_slt_ult_last_eq: forall a b d, last a d = last b d -> bv_slt a b = bv_ult a b.
Proof. intro a.
        induction a using rev_ind; intros.
        - case_eq b; intros; now cbn.
        - induction b using rev_ind; intros. 
          + unfold bv_slt, bv_ult, slt_list, ult_list in *.
	          Reconstr.rsimple Reconstr.Empty 
              (@RAWBITVECTOR_LIST.ult_list_big_endian, 
               @RAWBITVECTOR_LIST.slt_list_big_endian).
          + rewrite !last_app in H.
            now rewrite H, bv_slt_ult_eq.
Qed.

(* Prop output *)
Definition slt_listP (x y: list bool) :=
  if slt_list x y then True else False.

Definition bv_sltP (a b : bitvector) : Prop :=
  if @size a =? @size b then slt_listP a b else False.


(* signed less than or equal to *)
Definition sle_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, nil  => true
    | nil, _ => false 
    | _, nil => false
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ule_list_big_endian x' y'))
          (andb xi (negb yi))
  end.

(* bool output *)
Definition sle_list (x y: list bool) :=
  sle_list_big_endian (List.rev x) (List.rev y).

Definition bv_sle (a b : bitvector) : bool :=
  if @size a =? @size b then sle_list a b else false.

(* Prop output *)
Definition sle_listP (x y: list bool) :=
  if sle_list x y then True else False.

Definition bv_sleP (a b : bitvector) : Prop :=
  if @size a =? @size b then sle_listP a b else False.

(* greater than *)

(* unsigned greater than *)
Fixpoint ugt_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => andb xi (negb yi)
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ugt_list_big_endian x' y'))
          (andb xi (negb yi))
  end.

(* bool output *)
Definition ugt_list (x y: list bool) :=
  (ugt_list_big_endian (List.rev x) (List.rev y)).

Definition bv_ugt (a b : bitvector) : bool :=
  if @size a =? @size b then ugt_list a b else false.

(* Prop output *)
Definition ugt_listP (x y: list bool) :=
  if ugt_list x y then True else False.

Definition bv_ugtP (a b : bitvector) : Prop :=
  if @size a =? @size b then ugt_listP a b else False.

(* signed greater than *)

Definition sgt_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ugt_list_big_endian x' y'))
          (andb (negb xi) yi)
  end.

(* bool output *)
Definition sgt_list (x y: list bool) :=
  sgt_list_big_endian (List.rev x) (List.rev y).

Definition bv_sgt (a b : bitvector) : bool :=
  if @size a =? @size b then sgt_list a b else false.

(* Prop output *)
Definition sgt_listP (x y: list bool) :=
  if sgt_list x y then True else False.

Definition bv_sgtP (a b : bitvector) : Prop :=
  if @size a =? @size b then sgt_listP a b else False.



(* Theorems *)

Lemma length_mk_list_false: forall n, length (mk_list_false n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma length_mk_list_one: forall n, length (rev (mk_list_one n)) = n.
Proof. intro n.
  induction n as [| n' IHn].
  - reflexivity.
  - assert (H: forall n, length (rev (mk_list_one (S n))) = S (length (rev(mk_list_one n)))).
    { intros n. rewrite -> length_rev. rewrite -> length_rev. induction n as [ | n'' IHn'].
      + reflexivity.
      + reflexivity. }
    rewrite -> H. rewrite -> IHn. reflexivity.
Qed.

Lemma mk_list_one_succ : forall (n : nat), mk_list_one (S n) = mk_list_false n ++ [true].
Proof.
  induction n.
  + easy.
  + replace (mk_list_one (S (S n))) with (false :: mk_list_one (S n)).
    - now rewrite IHn.
    - easy.
Qed.

Lemma rev_mk_list_one_succ : forall (n : nat), rev (mk_list_one (S n)) = true :: mk_list_false n.
Proof.
  intro.
  rewrite mk_list_one_succ.
  rewrite rev_app_distr.
  now rewrite rev_mk_list_false.
Qed.

Lemma one_succ : forall (n : N), one (n + 1) = bv_concat (zeros n) (one 1).
Proof.
  intro.
  unfold bv_concat, one, zeros.
  rewrite N2Nat.inj_add.
  rewrite Nat.add_1_r.
  apply rev_mk_list_one_succ.
Qed.

Definition _of_bits (a:list bool) (s: N) := 
if (N.of_nat (length a) =? s) then a else zeros s.

Lemma _of_bits_size l s: (size (_of_bits l s)) = s.
Proof. unfold of_bits, size. unfold _of_bits.
       case_eq ( N.of_nat (length l) =? s).
       intros. now rewrite N.eqb_eq in H.
       intros. unfold zeros. rewrite length_mk_list_false.
       now rewrite N2Nat.id.
Qed.

Lemma length_mk_list_true: forall n, length (mk_list_true n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma zeros_size (n : N) : size (zeros n) = n.
Proof. unfold size, zeros. now rewrite length_mk_list_false, N2Nat.id. Qed. 

Lemma one_size (n : N) : size (one n) = n.
Proof. unfold size. unfold one. rewrite length_mk_list_one.
  rewrite N2Nat.id. reflexivity. Qed.

Lemma ones_size (n : N) : size (ones n) = n.
Proof. unfold size, ones. now rewrite length_mk_list_true, N2Nat.id. Qed. 

Definition smin_big_endian (t : nat) : list bool :=
  match t with
    | O => []
    | S t' => true :: mk_list_false t'
  end.

Definition signed_min (n : N) : bitvector := 
    rev (smin_big_endian (N.to_nat n)).

Lemma length_smin_big_endian : forall n, 
  length (rev (smin_big_endian n)) = n.
Proof. 
  intro n. induction n as [| n' IHn].
  + reflexivity.
  + rewrite length_rev in *. simpl.
    rewrite length_mk_list_false. easy.
Qed.

Lemma signed_min_size (n : N) : size (signed_min n) = n.
Proof. unfold size. unfold signed_min. 
  rewrite length_smin_big_endian. rewrite N2Nat.id. easy. Qed.


Definition smax_big_endian (t : nat) : list bool :=
  match t with
    | O => []
    | S t' => false :: mk_list_true t'
  end.

Definition signed_max (n : N) : bitvector := 
    rev (smax_big_endian (N.to_nat n)).

Lemma length_smax_big_endian : forall n, 
  length (rev (smax_big_endian n)) = n.
Proof. 
  intro n. induction n as [| n' IHn].
  + reflexivity.
  + rewrite length_rev in *. simpl.
    rewrite length_mk_list_true. easy.
Qed.

Lemma signed_max_size (n : N) : size (signed_max n) = n.
Proof. unfold size. unfold signed_max. 
  rewrite length_smax_big_endian. rewrite N2Nat.id. easy. Qed.

Lemma List_eq : forall (l m: list bool), beq_list l m = true <-> l = m.
Proof.
    induction l; destruct m; simpl; split; intro; try (reflexivity || discriminate).
    - rewrite andb_true_iff in H. destruct H. rewrite eqb_true_iff in H. rewrite H.
    apply f_equal. apply IHl. exact H0.
    - inversion H. subst b. subst m. rewrite andb_true_iff. split.
      + apply eqb_reflx.
      + apply IHl; reflexivity.
Qed.

Lemma List_eqP : forall (l m: list bool), beq_listP l m  <-> l = m.
Proof.
    induction l; destruct m; simpl; split; intro; try (reflexivity || discriminate); try now contradict H.
    - destruct H. rewrite H.
      apply f_equal. apply IHl. exact H0.
    - inversion H. subst b. subst m. split.
      + reflexivity.
      + apply IHl; reflexivity.
Qed.

Lemma List_eq_refl : forall (l: list bool), beq_list l l = true.
Proof.
    induction l; simpl; try (reflexivity || discriminate).
    - rewrite andb_true_iff. split. apply eqb_reflx. apply IHl.
Qed.

Lemma List_eqP_refl : forall (l: list bool), beq_listP l l  <-> l = l.
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - easy.
       - simpl. repeat split. now apply IHl.
Qed.

Lemma List_neq : forall (l m: list bool), beq_list l m = false -> l <> m.
Proof. 
       intro l.
       induction l.
       - intros. case m in *; simpl. now contradict H. easy.
       - intros. simpl in H.
         case_eq m; intros; rewrite H0 in H. 
           easy. simpl.
           case_eq (Bool.eqb a b); intros.
           rewrite H1 in H. rewrite andb_true_l in H.
           apply Bool.eqb_prop in H1.
           specialize (IHl l0 H).
           rewrite H1. 
           unfold not in *.
           intros. apply IHl.
           now inversion H2.
           apply Bool.eqb_false_iff in H1.
           unfold not in *.
           intros. apply H1.
           now inversion H2.
Qed.

Lemma List_neq2: forall (l m: list bool), l <> m -> beq_list l m = false.
Proof. intro l.
        induction l; intros.
        - Reconstr.reasy Reconstr.Empty (@RAWBITVECTOR_LIST.beq_list).
        - case_eq m; intros.
          + subst. easy.
          + subst. cbn.
            specialize (IHl l0).
            case_eq a; case_eq b; intros.
            * cbn. apply IHl.
              Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            * now cbn.
            * now cbn.
            * cbn. apply IHl.
              Reconstr.reasy Reconstr.Empty Reconstr.Empty.
Qed.

Lemma List_neqP : forall (l m: list bool), ~beq_listP l m -> l <> m.
Proof. 
       intro l.
       induction l.
       - intros. case m in *; simpl. now contradict H. easy.
       - intros. unfold not in H. simpl in H.
         case_eq m; intros. easy.
         rewrite H0 in H.
         unfold not. intros. apply H. inversion H1.
         split; try easy.
         now apply List_eqP_refl.
Qed.

Lemma bv_eq_reflect a b : bv_eq a b = true <-> a = b.
Proof.
  unfold bv_eq. case_eq (size a =? size b); intro Heq; simpl.
  - apply List_eq.
  - split; try discriminate.
    intro H. rewrite H, N.eqb_refl in Heq. discriminate.
Qed.

Lemma bv_eq_refl a: bv_eq a a = true.
Proof.
  unfold bv_eq. rewrite N.eqb_refl. now apply List_eq. 
Qed.

Lemma bv_concat_size n m a b : size a = n -> size b = m -> size (bv_concat a b) = (n + m)%N.
Proof.
  unfold bv_concat, size. intros H0 H1.
  rewrite length_app, Nat2N.inj_add, H0, H1; now rewrite N.add_comm.
Qed.

(*list bitwise AND properties*)

Lemma map2_and_comm: forall (a b: list bool), (map2 andb a b) = (map2 andb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' = b' && a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply andb_comm.
Qed.

Lemma map2_and_assoc: forall (a b c: list bool), (map2 andb a (map2 andb b c)) = (map2 andb (map2 andb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' && (b' && c') = a' && b' && c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply andb_assoc.
Qed.

Lemma map2_and_idem1:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && a' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite andb_comm, andb_assoc, andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem1. Qed.

Lemma map2_and_idem2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && b' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- andb_assoc. rewrite andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem : forall (a : list bool), map2 andb a a = a.
Proof.
  induction a.
  + easy.
  + simpl.
    rewrite IHa.
    now destruct a.
Qed.

Lemma map2_and_idem_comm2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem2. Qed.

Lemma map2_and_empty_empty1:  forall (a: list bool), (map2 andb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_and_empty_empty2:  forall (a: list bool), (map2 andb [] a) = [].
Proof. intros a. rewrite map2_and_comm. apply map2_and_empty_empty1. Qed.

Lemma map2_nth_empty_false:  forall (i: nat), nth i [] false = false.
Proof. intros i. induction i as [ | IHi]; simpl; reflexivity. Qed.

Lemma mk_list_true_equiv: forall t acc, mk_list_true_acc t acc = (List.rev (mk_list_true t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt.
       rewrite <- app_assoc.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma mk_list_false_equiv: forall t acc, mk_list_false_acc t acc = (List.rev (mk_list_false t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt. 
       rewrite <- app_assoc.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma len_mk_list_true_empty: length (mk_list_true_acc 0 []) = 0%nat.
Proof. simpl. reflexivity. Qed.

Lemma add_mk_list_true: forall n acc, length (mk_list_true_acc n acc) = (n + length acc)%nat.
Proof. intros n.
       induction n as [ | n' IHn].
         + auto.
         + intro acc. simpl. rewrite IHn. simpl. lia.
Qed.

Lemma map2_and_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 andb a b) false = (nth i a false) && (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_and_empty_empty2.
             rewrite map2_nth_empty_false. reflexivity.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_and_empty_empty1.
             rewrite map2_nth_empty_false. rewrite andb_false_r. reflexivity.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma length_mk_list_true_full: forall n, length (mk_list_true_acc n []) = n.
Proof. intro n. rewrite (@add_mk_list_true n []). auto. Qed.

Lemma mk_list_app: forall n acc, mk_list_true_acc n acc = mk_list_true_acc n [] ++ acc.
Proof. intro n.
       induction n as [ | n IHn].
         + auto.
         + intro acc. simpl in *. rewrite IHn. 
           cut (mk_list_true_acc n [] ++ [true] = mk_list_true_acc n [true]). intro H.
           rewrite <- H. rewrite <- app_assoc. unfold app. reflexivity.
           rewrite <- IHn. reflexivity.
Qed.

Lemma mk_list_ltrue: forall n, mk_list_true_acc n [true] = mk_list_true_acc (S n) [].
Proof. intro n. induction n as [ | n IHn]; auto. Qed.

Lemma map2_and_1_neutral: forall (a: list bool), (map2 andb a (mk_list_true (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite andb_true_r. reflexivity.
Qed.

Lemma map2_and_0_absorb: forall (a: list bool), (map2 andb a (mk_list_false (length a))) = (mk_list_false (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite andb_false_r; reflexivity.
Qed.

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_and_app : forall (a a' b b' : list bool),
  length a = length b -> length a' = length b' ->
  (map2 andb (a ++ a') (b ++ b')) = map2 andb a b ++ map2 andb a' b'.
Proof.
  induction a; intros.
  + now destruct b.
  + destruct b.
    - easy.
    - simpl.
      rewrite IHa.
      * easy.
      * now injection H.
      * apply H0.
Qed.

Lemma rev_map2_and : forall (a b : list bool),
  length a = length b ->
  rev (map2 andb a b) = map2 andb (rev a) (rev b).
Proof.
  induction a; intros.
  + now destruct b.
  + destruct b.
    - now rewrite !map2_and_empty_empty1.
    - simpl.
      rewrite IHa.
      rewrite map2_and_app.
      * easy.
      * rewrite !length_rev.
        now injection H.
      * easy.
      * now injection H.
Qed.

(*bitvector AND properties*)

Lemma bv_and_size n a b : size a = n -> size b = n -> size (bv_and a b) = n.
Proof.
  unfold bv_and. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_and_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_comm n a b : size a = n -> size b = n -> bv_and a b = bv_and b a.
Proof.
  intros H1 H2. unfold bv_and. rewrite H1, H2.
  rewrite N.eqb_compare, N.compare_refl.
  rewrite map2_and_comm. reflexivity.
Qed.

Lemma bv_and_assoc: forall n a b c, size a = n -> size b = n -> size c = n -> 
                                  (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_and, size, bits in *. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite H0. rewrite N.compare_refl.
       rewrite <- (@map2_and_length a b). rewrite <- map2_and_length. rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite map2_and_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_and_idem1:  forall a b n, size a = n -> size b = n -> (bv_and (bv_and a b) a) = (bv_and a b).
Proof. intros a b n H0 H1.
        unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem1; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_idem2: forall a b n, size a = n ->  size b = n -> (bv_and (bv_and a b) b) = (bv_and a b).
Proof. intros a b n H0 H1.
       unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem2; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_idem : forall (a : bitvector), bv_and a a = a.
Proof.
  intro.
  unfold bv_and.
  rewrite N.eqb_refl.
  apply map2_and_idem.
Qed.

Definition bv_empty: bitvector := nil.

Lemma bv_and_empty_empty1: forall a, (bv_and a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty, bv_and, size, bits. simpl.
       rewrite map2_and_empty_empty1.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a))) in H.
           rewrite H. simpl. reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_and_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_and a b)) false = (nth i (bits a) false) && (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_and. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_and_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_and_empty_empty2: forall a, (bv_and bv_empty a) = bv_empty.
Proof. intro a. unfold bv_and, bv_empty, size.
       case (length a); simpl; auto.
Qed.

Lemma bv_and_1_neutral: forall a, (bv_and a (ones (size a))) = a.
Proof. intro a. unfold bv_and.
       rewrite ones_size. rewrite N.eqb_refl. unfold ones, size, bits.
       rewrite Nat2N.id.
       apply map2_and_1_neutral.
Qed.

Lemma bv_and_0_absorb: forall a, (bv_and a (zeros (size a))) = zeros (size a).
Proof. intro a. unfold bv_and.
       rewrite zeros_size. rewrite N.eqb_refl. unfold zeros, size, bits.
       rewrite Nat2N.id.
       apply map2_and_0_absorb.
Qed.

(* lists bitwise OR properties *)

Lemma map2_or_comm: forall (a b: list bool), (map2 orb a b) = (map2 orb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' = b' || a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply orb_comm.
Qed.

Lemma map2_or_assoc: forall (a b c: list bool), (map2 orb a (map2 orb b c)) = (map2 orb (map2 orb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' || (b' || c') = a' || b' || c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply orb_assoc.
Qed.

Lemma map2_or_length: forall (a b: list bool), length a = length b -> length a = length (map2 orb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_or_empty_empty1:  forall (a: list bool), (map2 orb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_or_empty_empty2:  forall (a: list bool), (map2 orb [] a) = [].
Proof. intros a. rewrite map2_or_comm. apply map2_or_empty_empty1. Qed.

Lemma map2_or_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 orb a b) false = (nth i a false) || (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_or_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_or_empty_empty1.
             rewrite map2_nth_empty_false. rewrite orb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma map2_or_0_neutral: forall (a: list bool), (map2 orb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite orb_false_r. reflexivity.
Qed.

Lemma map2_or_1_true: forall (a: list bool), (map2 orb a (mk_list_true (length a))) = (mk_list_true (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite orb_true_r; reflexivity.
Qed.

Lemma map2_or_idem1:  forall (a b: list bool), (map2 orb (map2 orb a b) a) = (map2 orb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' || a' = a' || b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite orb_comm, orb_assoc, orb_diag. reflexivity. 
Qed.

Lemma map2_or_idem2:  forall (a b: list bool), (map2 orb (map2 orb a b) b) = (map2 orb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' || b' = a' || b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- orb_assoc. rewrite orb_diag. reflexivity. 
Qed.

Lemma map2_or_neg_true:  forall (a: list bool), (map2 orb (map negb a) a) = mk_list_true (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn.
         assert (negb a || a = true).
         case a; easy.
         now rewrite H, IHa.
Qed.

Lemma map2_or_app : forall (a a' b b' : list bool),
  length a = length b -> length a' = length b' ->
  (map2 orb (a ++ a') (b ++ b')) = map2 orb a b ++ map2 orb a' b'.
Proof.
  induction a; intros.
  + now destruct b.
  + destruct b.
    - easy.
    - simpl.
      rewrite IHa.
      * easy.
      * now injection H.
      * apply H0.
Qed.

(*bitvector OR properties*)

Lemma bv_or_size n a b : size a = n -> size b = n -> size (bv_or a b) = n.
Proof.
  unfold bv_or. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_or_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_comm: forall n a b, (size a) = n -> (size b) = n -> bv_or a b = bv_or b a.
Proof. intros a b n H0 H1. unfold bv_or.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_comm. reflexivity.
Qed.

Lemma bv_or_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_or. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_or_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_or_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_or_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_empty_empty1: forall a, (bv_or a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_or, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_or_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_or_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_or a b)) false = (nth i (bits a) false) || (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_or. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_or_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_or_0_neutral: forall a, (bv_or a (zeros (size a))) = a.
Proof. intro a. unfold bv_or.
       rewrite zeros_size. rewrite N.eqb_refl. unfold zeros, size, bits.
       rewrite Nat2N.id.
       apply map2_or_0_neutral.
Qed.

Lemma bv_or_1_true: forall a, (bv_or a (ones (size a))) = (ones (size a)).
Proof. intro a. unfold bv_or.
       rewrite ones_size. rewrite N.eqb_refl. unfold ones, size, bits.
       rewrite Nat2N.id.
       apply map2_or_1_true.
Qed.

Lemma bv_or_idem1:  forall a b n, size a = n -> size b = n -> (bv_or (bv_or a b) a) = (bv_or a b).
Proof. intros a b n H0 H1.
       unfold bv_or. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_or_length. rewrite N.compare_refl. 
       rewrite map2_or_idem1; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_idem2: forall a b n, size a = n ->  size b = n -> (bv_or (bv_or a b) b) = (bv_or a b).
Proof. intros a b n H0 H1.
       unfold bv_or. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_or_length. rewrite N.compare_refl. 
       rewrite map2_or_idem2; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.


(* lists bitwise XOR properties *)

Lemma map2_xor_comm: forall (a b: list bool), (map2 xorb a b) = (map2 xorb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (xorb a' b' = xorb b' a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply xorb_comm.
Qed.

Lemma map2_xor_assoc: forall (a b c: list bool), (map2 xorb a (map2 xorb b c)) = (map2 xorb (map2 xorb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (xorb a' (xorb b' c') = (xorb (xorb a'  b')  c')). intro H. rewrite <- H. apply f_equal.
            apply IHxs. rewrite xorb_assoc_reverse. reflexivity.
Qed.

Lemma map2_xor_length: forall (a b: list bool), length a = length b -> length a = length (map2 xorb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_xor_empty_empty1:  forall (a: list bool), (map2 xorb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_xor_empty_empty2:  forall (a: list bool), (map2 xorb [] a) = [].
Proof. intros a. rewrite map2_xor_comm. apply map2_xor_empty_empty1. Qed.

Lemma map2_xor_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 xorb a b) false = xorb (nth i a false) (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_xor_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_xor_empty_empty1.
             rewrite map2_nth_empty_false. rewrite xorb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma map2_xor_0_neutral: forall (a: list bool), (map2 xorb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite xorb_false_r. reflexivity.
Qed.

Lemma map2_xor_1_true: forall (a: list bool), (map2 xorb a (mk_list_true (length a))) = map negb a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs. rewrite <- IHxs.
         rewrite xorb_true_r; reflexivity.
Qed.

(*bitvector OR properties*)

Lemma bv_xor_size n a b : size a = n -> size b = n -> size (bv_xor a b) = n.
Proof.
  unfold bv_xor. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_xor_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_comm: forall n a b, (size a) = n -> (size b) = n -> bv_xor a b = bv_xor b a.
Proof. intros n a b H0 H1. unfold bv_xor.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_xor_comm. reflexivity.
Qed.

Lemma bv_xor_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_xor. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_xor_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_xor_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_xor_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_empty_empty1: forall a, (bv_xor a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_xor, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_xor_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_xor_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_xor a b)) false = xorb (nth i (bits a) false) (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_xor. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_xor_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_xor_0_neutral: forall a, (bv_xor a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite map2_xor_0_neutral. reflexivity.
Qed.

Lemma bv_xor_1_true: forall a, (bv_xor a (mk_list_true (length (bits a)))) = map negb a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare.  unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_xor_1_true. reflexivity.
Qed.

(*bitwise NOT properties*)

Lemma not_list_length: forall a, length a = length (map negb a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto. 
       - simpl. apply f_equal. exact IHxs.
Qed.

Lemma not_list_involutative: forall a, map negb (map negb a) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]; auto.
       simpl. rewrite negb_involutive. apply f_equal. exact IHxs.
Qed.

Lemma not_list_false_true: forall n, map negb (mk_list_false n) = mk_list_true n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_true_false: forall n, map negb (mk_list_true n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_and_or: forall a b, map negb (map2 andb a b) = map2 orb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_andb. apply f_equal. apply IHxs.
Qed.

Lemma not_list_or_and: forall a b, map negb (map2 orb a b) = map2 andb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_orb. apply f_equal. apply IHxs.
Qed.

(*bitvector NOT properties*)

Lemma bv_not_size: forall n a, (size a) = n -> size (bv_not a) = n.
Proof. intros n a H. unfold bv_not.
       unfold size, bits in *. rewrite <- not_list_length. exact H.
Qed.

Lemma bv_not_involutive: forall a, bv_not (bv_not a) = a.
Proof. intro a. unfold bv_not.
       unfold size, bits. rewrite not_list_involutative. reflexivity.
Qed.

Lemma bv_not_false_true: forall n, bv_not (mk_list_false n) = (mk_list_true n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_false_true. reflexivity.
Qed.

Lemma bv_not_true_false: forall n, bv_not (mk_list_true n) = (mk_list_false n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_true_false. reflexivity.
Qed.

Lemma bv_not_and_or: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_and a b) = bv_or (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       do 2 rewrite <- not_list_length. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *. 
       rewrite not_list_and_or. reflexivity.
Qed.

Lemma bv_not_or_and: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_or a b) = bv_and (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and, size, bits in *. 
       do 2 rewrite <- not_list_length.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *.
       rewrite not_list_or_and. reflexivity.
Qed.

Lemma bvdm: forall a b: bitvector, size a = size b ->
   (bv_not (bv_and a b)) = (bv_or (bv_not a) (bv_not b)).
Proof. intros. unfold bv_and, bv_or, bv_not.
       rewrite H, N.eqb_refl.
       unfold bits, size in *. 
       rewrite !length_map, H, N.eqb_refl.
       now rewrite not_list_and_or.
Qed.


(* list bitwise ADD properties*)

Lemma add_carry_ff: forall a, add_carry a false false = (a, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f: forall a, add_carry a (negb a) false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f_r: forall a, add_carry (negb a) a false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_t: forall a, add_carry a (negb a) true = (false, true).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_tt: forall a, add_carry a true true = (a, true).
Proof. intro a. case a; auto. Qed.

Lemma add_list_empty_l: forall (a: list bool), (add_list [] a) = [].
Proof. intro a. induction a as [ | a xs IHxs].
         - unfold add_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma add_list_empty_r: forall (a: list bool), (add_list a []) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_l: forall (a: list bool) (c: bool), (add_list_ingr [] a c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_r: forall (a: list bool) (c: bool), (add_list_ingr a [] c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_carry_comm: forall (a b:  list bool) (c: bool), add_list_ingr a b c = add_list_ingr b a c.
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c.
       - simpl. rewrite add_list_ingr_r. reflexivity.
       - case b as [ | b' ys].
         + simpl. auto.
         + simpl in *. cut (add_carry a' b' c = add_carry b' a' c).
           * intro H. rewrite H. destruct (add_carry b' a' c) as (r, c0).
             rewrite IHxs. reflexivity.
           * case a', b', c;  auto.
Qed.

Lemma add_list_comm: forall (a b: list bool), (add_list a b) = (add_list b a).
Proof. intros a b. unfold add_list. apply (add_list_carry_comm a b false). Qed.

Lemma add_list_carry_assoc: forall (a b c:  list bool) (d1 d2 d3 d4: bool),
                            add_carry d1 d2 false = add_carry d3 d4 false ->
                            (add_list_ingr (add_list_ingr a b d1) c d2) = (add_list_ingr a (add_list_ingr b c d3) d4).
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c d1 d2 d3 d4.
       - simpl. reflexivity.
       - case b as [ | b' ys].
         + simpl. auto.
         + case c as [ | c' zs].
           * simpl. rewrite add_list_ingr_r. auto.
           * simpl.
             case_eq (add_carry a' b' d1); intros r0 c0 Heq0. simpl.
             case_eq (add_carry r0 c' d2); intros r1 c1 Heq1.
             case_eq (add_carry b' c' d3); intros r3 c3 Heq3.
             case_eq (add_carry a' r3 d4); intros r2 c2 Heq2.
             intro H. rewrite (IHxs _ _ c0 c1 c3 c2);
               revert Heq0 Heq1 Heq3 Heq2;
               case a', b', c', d1, d2, d3, d4; simpl; do 4 (intros H'; inversion_clear H'); 
                 try reflexivity; simpl in H; discriminate.
Qed.

Lemma add_list_carry_length_eq: forall (a b: list bool) c, length a = length b -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity.
Qed.

Lemma add_list_carry_length_ge: forall (a b: list bool) c, (length a >= length b)%nat -> length b = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. lia.
       intros [ | b ys].
       - simpl. intros. auto.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma add_list_carry_length_le: forall (a b: list bool) c, (length b >= length a)%nat -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. reflexivity.
       intros [ | b ys].
       - simpl. intros. contradict H. lia.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma bv_neg_size: forall n a, (size a) = n -> size (bv_neg a) = n.
Proof. intros n a H. unfold bv_neg.
       unfold size, bits in *. unfold twos_complement.
       specialize (@add_list_carry_length_eq  (map negb a) (mk_list_false (length a)) true).
       intros. rewrite <- H0. now rewrite length_map.
       rewrite length_map.
       now rewrite length_mk_list_false.
Qed.

Lemma length_add_list_eq: forall (a b: list bool), length a = length b -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_eq a b false). exact H. Qed.

Lemma length_add_list_ge: forall (a b: list bool), (length a >= length b)%nat -> length b = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_ge a b false). exact H. Qed.

Lemma length_add_list_le: forall (a b: list bool), (length b >= length a)%nat -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_le a b false). exact H. Qed.

Lemma add_list_assoc: forall (a b c: list bool), (add_list (add_list a b) c) = (add_list a (add_list b c)).
Proof. intros a b c. unfold add_list.
       apply (@add_list_carry_assoc a b c false false false false).
       simpl; reflexivity.
Qed.

Lemma add_list_carry_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr (mk_list_false n) a false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_r. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr a (mk_list_false n) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_l. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_l: forall (a: list bool), (add_list_ingr (mk_list_false (length a)) a false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_l; auto.
Qed.

Lemma add_list_carry_empty_neutral_r: forall (a: list bool), (add_list_ingr a (mk_list_false (length a)) false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_r; auto.
Qed.

Lemma add_list_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list (mk_list_false n) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_l a).
Qed.

Lemma add_list_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list a (mk_list_false n)) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_r a).
Qed.

Lemma add_list_empty_neutral_r: forall (a: list bool), (add_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_r a).
Qed.

Lemma add_list_empty_neutral_l: forall (a: list bool), (add_list (mk_list_false (length a)) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_l a).
Qed.

Lemma add_list_carry_unit_t : forall a, add_list_ingr a (mk_list_true (length a)) true = a.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. case_eq (add_carry a true true). intros r0 c0 Heq0.
         rewrite add_carry_tt in Heq0. inversion Heq0.
         apply f_equal. exact IHxs.
Qed.

Lemma add_list_carry_twice: forall a c, add_list_ingr a a c = removelast (c :: a).
Proof. intro a. 
       induction a as [ | a xs IHxs].
       - intros c. simpl. reflexivity.
       - intros [ | ].
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
Qed.

Lemma add_list_twice: forall a, add_list a a = removelast (false :: a).
Proof. intro a. 
       unfold add_list. rewrite add_list_carry_twice. reflexivity.
Qed.

(*bitvector ADD properties*)

Lemma bv_add_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_add a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_add. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@length_add_list_eq a b). auto.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_add_comm: forall n a b, (size a) = n -> (size b) = n -> bv_add a b = bv_add b a.
Proof. intros n a b H0 H1.
       unfold bv_add, size, bits in *. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_comm. reflexivity.
Qed.

Lemma bv_add_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_add, size, bits in *. rewrite H1, H2.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq b c). rewrite H0, H1.
       rewrite N.compare_refl. rewrite N.eqb_compare.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq a b). rewrite H0.
       rewrite N.compare_refl.
       rewrite add_list_assoc. reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_add_empty_neutral_l: forall a, (bv_add (mk_list_false (length (bits a))) a) = a.
Proof. intro a. unfold bv_add, size, bits. 
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_l. reflexivity.
Qed.

Lemma bv_add_empty_neutral_r: forall a, (bv_add a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

Lemma bv_add_twice: forall a, bv_add a a = removelast (false :: a).
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_twice. reflexivity.
Qed.

(* bitwise SUBST properties *)

Lemma subst_list_empty_empty_l: forall a, (subst_list [] a) = [].
Proof. intro a. unfold subst_list; auto. Qed.

Lemma subst_list_empty_empty_r: forall a, (subst_list a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list; auto. 
Qed.

Lemma subst_list'_empty_empty_r: forall a, (subst_list' a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list' in *. unfold twos_complement. simpl. reflexivity.
Qed.

Lemma subst_list_borrow_length: forall (a b: list bool) c, length a = length b -> length a = length (subst_list_borrow a b c). 
Proof. induction a as [ | a' xs IHxs]. 
       simpl. auto. 
       intros [ | b ys].
       - simpl. intros. exact H. 
       - intros. simpl in *. 
         case_eq (subst_borrow a' b c); intros r c0 Heq. simpl. apply f_equal. 
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity. 
Qed.

Lemma length_twos_complement: forall (a: list bool), length a = length (twos_complement a).
Proof. intro a.
      induction a as [ | a' xs IHxs].
      - auto.
      - unfold twos_complement. specialize (@add_list_carry_length_eq (map negb (a' :: xs)) (mk_list_false (length (a' :: xs))) true).        
        intro H. rewrite <- H. simpl. apply f_equal. rewrite <- not_list_length. reflexivity.
        rewrite length_mk_list_false. rewrite <- not_list_length. reflexivity.
Qed.

Lemma subst_list_length: forall (a b: list bool), length a = length b -> length a = length (subst_list a b). 
Proof. intros a b H. unfold subst_list. apply (@subst_list_borrow_length a b false). exact H. Qed.

Lemma subst_list'_length: forall (a b: list bool), length a = length b -> length a = length (subst_list' a b).
Proof. intros a b H. unfold subst_list'.
       rewrite <- (@length_add_list_eq a (twos_complement b)).
       - reflexivity.
       - rewrite <- (@length_twos_complement b). exact H.
Qed.

Lemma subst_list_borrow_empty_neutral: forall (a: list bool), (subst_list_borrow a (mk_list_false (length a)) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl.
         cut(subst_borrow a' false false = (a', false)).
         + intro H. rewrite H. rewrite IHxs. reflexivity.
         + unfold subst_borrow. case a'; auto.
Qed.

Lemma subst_list_empty_neutral: forall (a: list bool), (subst_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list.
       apply (@subst_list_borrow_empty_neutral a).
Qed.

Lemma twos_complement_cons_false: forall a, false :: twos_complement a = twos_complement (false :: a).
Proof. intro a.
       induction a as [ | a xs IHxs]; unfold twos_complement; simpl; reflexivity.
Qed.

Lemma twos_complement_false_false: forall n, twos_complement (mk_list_false n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. rewrite <- twos_complement_cons_false.
         apply f_equal. exact IHn.
Qed.

Lemma bv_neg_zeros_zeros : forall (n : N), bv_neg (zeros n) = zeros n.
Proof.
  intro.
  apply twos_complement_false_false.
Qed.

Lemma subst_list'_empty_neutral: forall (a: list bool), (subst_list' a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list'.
       rewrite (@twos_complement_false_false (length a)).
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.


(* some list ult and slt properties *)

(* Transitivity : x < y => y < z => x < z *)
Lemma ult_list_big_endian_trans : forall x y z,
    ult_list_big_endian x y = true ->
    ult_list_big_endian y z = true ->
    ult_list_big_endian x z = true.
Proof.
  intros x. induction x.
  + simpl. easy.
  + intros y z. case y.
    - simpl. case x; easy.
    - intros b l. intros. simpl in *. case x in *.
      * case z in *. 
        { case l in *; easy. } 
        { case l in *.
          + rewrite andb_true_iff in H. destruct H.
            apply negb_true_iff in H. subst. simpl. 
            case z in *. 
            * easy.
            * rewrite !orb_true_iff, !andb_true_iff in H0.
              destruct H0.
              - destruct H. apply Bool.eqb_prop in H.
                subst. rewrite orb_true_iff. now right.
              - destruct H. easy.
          + rewrite !orb_true_iff, !andb_true_iff in H, H0.
            destruct H.
            * simpl in H. easy.
            * destruct H. apply negb_true_iff in H. subst. 
              simpl. destruct H0. 
              - destruct H. apply Bool.eqb_prop in H.
                subst. case z; easy.
              - destruct H. easy. }
      * case l in *.
        { rewrite !orb_true_iff, !andb_true_iff in H.
          simpl in H. destruct H.
          + destruct H. case x in H1; easy.
          + destruct H. apply negb_true_iff in H. subst.
            simpl in H0. case z in *.
            * easy.
            * case b in H0.
              - simpl in H0. case z in *; easy.
              - simpl in H0. case z in *; easy. }
        { case z in *.
          + easy.
          + rewrite !orb_true_iff, !andb_true_iff in *.
            destruct H.
            *  destruct H. destruct H0.
               -  destruct H0. apply Bool.eqb_prop in H. 
                  apply Bool.eqb_prop in H0. subst. left. split.
                  { apply Bool.eqb_reflx. }
                  { now apply (IHx (b1 :: l) z H1 H2). }
               - right. apply Bool.eqb_prop in H. now subst. 
            * right. destruct H0.
               { destruct H0. apply Bool.eqb_prop in H0. now subst. }
               { split; easy. } }
Qed.  
  
(* bool output *)
Lemma ult_list_trans : forall x y z,
    ult_list x y = true -> ult_list y z = true -> ult_list x z = true.
Proof. unfold ult_list. intros x y z. apply ult_list_big_endian_trans.
Qed.

Lemma bv_ult_trans : forall (b1 b2 b3 : bitvector), 
  bv_ult b1 b2 = true -> bv_ult b2 b3 = true -> bv_ult b1 b3 = true.
Proof.
  intros. unfold bv_ult in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_ult_b1_b2. 
    rewrite H1 in H. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_ult_b2_b3.
      rewrite H2 in H0. case_eq (size b1 =? size b3).
      * intros. pose proof ult_list_trans as ult_list_trans.
        specialize (@ult_list_trans b1 b2 b3 H H0).
        apply ult_list_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        now rewrite N.eqb_refl in H3. 
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.

(* Prop output *)
Lemma ult_listP_trans : forall (b1 b2 b3 : bitvector),
  ult_listP b1 b2 -> ult_listP b2 b3 -> ult_listP b1 b3.
Proof.
  unfold ult_listP. unfold ult_list. intros.
  case_eq (ult_list_big_endian (rev b1) (rev b3)).
  + intros. easy.
  + intros. case_eq (ult_list_big_endian (rev b1) (rev b2)).
    - intros. case_eq (ult_list_big_endian (rev b2) (rev b3)).
      * intros. pose proof ult_list_big_endian_trans.
        specialize (@H4 (rev b1) (rev b2) (rev b3) H2 H3). 
        rewrite H4 in H1. now contradict H1. 
      * intros. rewrite H3 in H0. apply H0.
    - intros. rewrite H2 in H. apply H.
Qed.

Lemma bv_ultP_trans : forall (b1 b2 b3 : bitvector), 
  bv_ultP b1 b2 -> bv_ultP b2 b3 -> bv_ultP b1 b3.
Proof.
  intros. unfold bv_ultP in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_ultP_b1_b2. 
    rewrite H1 in bv_ultP_b1_b2. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_ultP_b2_b3. 
      rewrite H2 in bv_ultP_b2_b3. case_eq (size b1 =? size b3).
      * intros. pose proof ult_listP_trans as ult_listP_trans.  
        specialize (@ult_listP_trans b1 b2 b3 bv_ultP_b1_b2 bv_ultP_b2_b3). 
        apply ult_listP_trans. 
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        now rewrite N.eqb_refl in H3.
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.


(* x <= y => y <= z => x <= z *)

Lemma ule_list_big_endian_trans : forall x y z, 
  ule_list_big_endian x y = true ->
  ule_list_big_endian y z = true -> 
  ule_list_big_endian x z = true.
Proof.
  intros x. induction x.
  + intros y z. case y.
    - intros Hxy Hyz. case z in *; easy.
    - intros b l Hxy Hyz. easy.
  + intros y z. case y.
    - simpl. case x; easy.
    - intros b l. intros. simpl in *. case x in *.
      * case z in *.
        { case l in *; easy. }
        { case l in *.
          + rewrite orb_true_iff in H. destruct H.
            ++ rewrite andb_true_iff, eqb_true_iff in H.
               destruct H. rewrite <- H in H0. apply H0. 
            ++ rewrite andb_true_iff, negb_true_iff in H.
               destruct H. subst. case z in *.
              -- rewrite orb_true_iff, andb_true_iff, negb_true_iff, eqb_true_iff in *.
                 destruct H0.
                ** right. rewrite andb_true_iff. split; easy.
                ** right. rewrite andb_true_iff in *. destruct H. split; easy. 
              -- rewrite orb_true_iff, andb_true_iff, negb_true_iff, eqb_true_iff in *.
                 destruct H0.
                ** right. rewrite andb_true_iff, negb_true_iff. destruct H.
                   now split.
                ** rewrite andb_true_iff, negb_true_iff in H. now destruct H.
          + rewrite !orb_true_iff, !andb_true_iff in H, H0.
            destruct H.
            * simpl in H. easy. 
            * destruct H. apply negb_true_iff in H. subst. 
              simpl.  destruct H0.
              - destruct H. apply Bool.eqb_prop in H.
                subst. case z; easy.
              - destruct H. easy. }
      * case l in *.
        { rewrite !orb_true_iff, !andb_true_iff in H.
          simpl in H. destruct H.
          + destruct H. case x in H1; easy.
          + destruct H. apply negb_true_iff in H.
            subst. simpl in H0. case z in *.
            * easy.
            * case b in *.
              - simpl in H0. case z in *; easy.
              - simpl in H0. case z in *; easy. }
        { case z in *; try easy.
          rewrite !orb_true_iff, !andb_true_iff in *.
          destruct H.
          + destruct H. destruct H0.
            * destruct H0. apply Bool.eqb_prop in H.
              apply Bool.eqb_prop in H0. subst. left. split.
              - apply Bool.eqb_reflx.
              - specialize (@IHx (b1 :: l) z H1 H2).
                apply IHx. 
            * right. apply Bool.eqb_prop in H. now subst.
          + right. destruct H0.
            * destruct H0. apply Bool.eqb_prop in H0. now subst.
            * split; easy. }
Qed.

(* bool output *)
Lemma ule_list_trans : forall x y z,
  ule_list x y = true -> ule_list y z = true -> ule_list x z = true.
Proof.
  unfold ule_list. intros x y z. apply ule_list_big_endian_trans. 
Qed.

Lemma bv_ule_list_trans : forall (b1 b2 b3 : bitvector), 
  bv_ule b1 b2 = true -> bv_ule b2 b3 = true -> bv_ule b1 b3 = true.
Proof.
  intros. unfold bv_ule in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_ule_b1_b2.
    rewrite H1 in bv_ule_b1_b2. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_ule_b2_b3.
      rewrite H2 in bv_ule_b2_b3. case_eq (size b1 =? size b3).
      * intros. pose proof ule_list_trans as ule_list_trans.
        specialize (@ule_list_trans b1 b2 b3 bv_ule_b1_b2 bv_ule_b2_b3).
        apply ule_list_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        specialize (@N.eqb_refl (size b3)). rewrite N.eqb_refl in H3.
        now contradict eqb_refl.
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.
 
(* Prop output *)
Lemma ule_listP_trans : forall (b1 b2 b3 : bitvector),
  ule_listP b1 b2 -> ule_listP b2 b3 -> ule_listP b1 b3.
Proof.
  unfold ule_listP. unfold ule_list. intros.
  case_eq (ule_list_big_endian (rev b1) (rev b3)).
  + intros. easy.
  + intros. case_eq (ule_list_big_endian (rev b1) (rev b2)).
    - intros. case_eq (ule_list_big_endian (rev b2) (rev b3)).
      * intros. pose proof ule_list_big_endian_trans.
        specialize (@H4 (rev b1) (rev b2) (rev b3) H2 H3).
        rewrite H4 in H1. now contradict H1.
      * intros. unfold ule_listP in H0. unfold ule_list in H0. 
        rewrite H3 in H0. apply H0.
    - intros. rewrite H2 in H. apply H.
Qed.

Lemma bv_uleP_trans : forall (b1 b2 b3 : bitvector),
  bv_uleP b1 b2 -> bv_uleP b2 b3 -> bv_uleP b1 b3.
Proof.
  intros. unfold bv_uleP in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_uleP_b1_b2.
    rewrite H1 in bv_uleP_b1_b2. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_uleP_b2_b3.
      rewrite H2 in bv_uleP_b2_b3. case_eq (size b1 =? size b3).
      * intros. pose proof ule_listP_trans as ule_listP_trans.
        specialize (@ule_listP_trans b1 b2 b3 bv_uleP_b1_b2 bv_uleP_b2_b3).
        apply ule_listP_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        specialize (@N.eqb_refl (size b3)). rewrite N.eqb_refl in H3.
        now contradict eqb_refl.
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.


(* x < y => y <= z => x < z *)

(* x < y => x <= y *)
Lemma ult_list_big_endian_implies_ule : forall x y,
  ult_list_big_endian x y = true -> ule_list_big_endian x y = true.
Proof.
  intros x. induction x as [| h t].
  + simpl. easy.
  + intros y. case y.
    - case h; case t; easy.
    - intros b l. simpl. 
      case t in *.
      * simpl. case l in *.
        { case h; case b; simpl; easy. }
        { easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. specialize (@IHt l H0). rewrite IHt. apply Bool.eqb_prop in H.
          rewrite H in *. left. split.
          + apply eqb_reflx.
          + easy. }
        { destruct H. rewrite negb_true_iff in *. subst. 
          right. easy. }
Qed.

Lemma ult_ule_list_big_endian_trans : forall x y z, 
  ult_list_big_endian x y = true ->
  ule_list_big_endian y z = true -> 
  ult_list_big_endian x z = true.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y z. case y.
    - simpl. case x; easy.
    - intros b l. intros. simpl in *. case x in *.
      * case z in *.
        { case l in *; easy. }
        { case l in *.
          + rewrite andb_true_iff in H. destruct H.
            apply negb_true_iff in H. subst. simpl.
            case z in *.
            * rewrite orb_true_iff in H0. destruct H0.
              - rewrite andb_true_iff, eqb_true_iff in H. 
                destruct H. symmetry. apply H.
              - rewrite andb_true_iff in H. destruct H.
                simpl in H. now contradict H.
            * rewrite !orb_true_iff, !andb_true_iff in H0. 
              destruct H0.
              - destruct H. apply Bool.eqb_prop in H.
                subst. rewrite orb_true_iff. now right.
              - destruct H. easy. 
          + rewrite !orb_true_iff, !andb_true_iff in H, H0.
            destruct H.
            * simpl in H. easy. 
            * destruct H. apply negb_true_iff in H. subst. 
              simpl.  destruct H0.
              - destruct H. apply Bool.eqb_prop in H.
                subst. case z; easy.
              - destruct H. easy. }
      * case l in *.
        { rewrite !orb_true_iff, !andb_true_iff in H.
          simpl in H. destruct H.
          + destruct H. case x in H1; easy.
          + destruct H. apply negb_true_iff in H.
            subst. simpl in H0. case z in *.
            * easy.
            * case b in *.
              - simpl in H0. case z in *; easy.
              - simpl in H0. case z in *; easy. }
        { case z in *; try easy.
          rewrite !orb_true_iff, !andb_true_iff in *.
          destruct H.
          + destruct H. destruct H0.
            * destruct H0. apply Bool.eqb_prop in H.
              apply Bool.eqb_prop in H0. subst. left. split.
              - apply Bool.eqb_reflx.
              - specialize (@IHx (b1 :: l) z H1 H2).
                apply IHx. 
            * right. apply Bool.eqb_prop in H. now subst.
          + right. destruct H0.
            * destruct H0. apply Bool.eqb_prop in H0. now subst.
            * split; easy. }
Qed.

(* bool output *)
Lemma ult_ule_list_trans : forall x y z,
  ult_list x y = true -> ule_list y z = true -> ult_list x z = true.
Proof.
  unfold ult_list, ule_list. intros x y z. apply ult_ule_list_big_endian_trans. 
Qed.

Lemma bv_ult_ule_list_trans : forall (b1 b2 b3 : bitvector), 
  bv_ult b1 b2 = true -> bv_ule b2 b3 = true -> bv_ult b1 b3 = true.
Proof.
  intros. unfold bv_ult, bv_ule in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_ult_b1_b2.
    rewrite H1 in bv_ult_b1_b2. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_ule_b2_b3.
      rewrite H2 in bv_ule_b2_b3. case_eq (size b1 =? size b3).
      * intros. pose proof ult_ule_list_trans as ult_ule_list_trans.
        specialize (@ult_ule_list_trans b1 b2 b3 bv_ult_b1_b2 bv_ule_b2_b3).
        apply ult_ule_list_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        now rewrite N.eqb_refl in H3. 
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.
 
(* Prop output *)
Lemma ult_ule_listP_trans : forall (b1 b2 b3 : bitvector),
  ult_listP b1 b2 -> ule_listP b2 b3 -> ult_listP b1 b3.
Proof.
  unfold ult_listP. unfold ult_list. intros.
  case_eq (ult_list_big_endian (rev b1) (rev b3)).
  + intros. easy.
  + intros. case_eq (ult_list_big_endian (rev b1) (rev b2)).
    - intros. case_eq (ule_list_big_endian (rev b2) (rev b3)).
      * intros. pose proof ult_ule_list_big_endian_trans.
        specialize (@H4 (rev b1) (rev b2) (rev b3) H2 H3).
        rewrite H4 in H1. now contradict H1.
      * intros. unfold ule_listP in H0. unfold ule_list in H0. 
        rewrite H3 in H0. apply H0.
    - intros. rewrite H2 in H. apply H.
Qed.

Lemma bv_ult_uleP_trans : forall (b1 b2 b3 : bitvector),
  bv_ultP b1 b2 -> bv_uleP b2 b3 -> bv_ultP b1 b3.
Proof.
  intros. unfold bv_ultP, bv_uleP in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_ultP_b1_b2.
    rewrite H1 in bv_ultP_b1_b2. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_uleP_b2_b3.
      rewrite H2 in bv_uleP_b2_b3. case_eq (size b1 =? size b3).
      * intros. pose proof ult_ule_listP_trans as ult_ule_listP_trans.
        specialize (@ult_ule_listP_trans b1 b2 b3 bv_ultP_b1_b2 bv_uleP_b2_b3).
        apply ult_ule_listP_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        now rewrite N.eqb_refl in H3. 
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed. 

(*x <= x*)
Lemma ule_list_big_endian_refl : forall (b : list bool), 
   ule_list_big_endian b b = true.
Proof.
  induction b.
  + easy.
  + case a; simpl; rewrite IHb; case b; easy.
Qed.

Lemma bv_ule_refl : forall (b : bitvector), bv_ule b b = true.
Proof.
  intros. unfold bv_ule. 
  rewrite N.eqb_refl. unfold ule_list.
  induction (rev b).
  + easy.
  + rewrite (@ule_list_big_endian_refl (a :: l)). easy.
Qed.

Lemma bv_uleP_refl : forall (b : bitvector), bv_uleP b b.
Proof.
  intros. unfold bv_uleP. 
  rewrite N.eqb_refl. unfold ule_listP. unfold ule_list.
  induction (rev b).
  + easy.
  + rewrite (@ule_list_big_endian_refl (a :: l)). easy.
Qed.

(* forall x y, x < y => x != y *)
(* Unsigned less than *)

Lemma ult_list_big_endian_not_eq : forall x y,
    ult_list_big_endian x y = true -> x <> y.
Proof.
  intros x. induction x.
  + simpl. easy.
  + intros y. case y.
    - easy.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *. 
        { case a; case b; simpl; easy. }
        { easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H. 
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H. 
          rewrite H in *. unfold not in *; intro. 
          inversion H1; subst. now apply H0. }
        { destruct H. apply negb_true_iff in H. subst. easy. }
Qed.  

(* Boolean comparison *)
Lemma ult_list_not_eq : forall x y, ult_list x y = true -> x <> y.
Proof. unfold ult_list.
  unfold not. intros.
  apply ult_list_big_endian_not_eq in H.
  subst. auto.
Qed.

Lemma bv_ult_not_eq : forall x y, bv_ult x y = true -> x <> y.
Proof. intros x y. unfold bv_ult.
       case_eq (size x =? size y); intros.
       - now apply ult_list_not_eq in H0.
       - now contradict H0.
Qed.

(* Prop comparison *)
Lemma ult_list_not_eqP : forall x y, ult_listP x y -> x <> y.
Proof. unfold ult_listP.
  unfold not. intros. unfold ult_list in H.
  case_eq (ult_list_big_endian (List.rev x) (List.rev y)).
  + intros. apply ult_list_big_endian_not_eq in H1. subst. now contradict H1.
  + intros. now rewrite H1 in H.
Qed.

Lemma bv_ult_not_eqP : forall x y, bv_ultP x y -> x <> y.
Proof. intros x y. unfold bv_ultP.
       case_eq (size x =? size y); intros.
       - now apply ult_list_not_eqP in H0.
       - now contradict H0.
Qed.


(* forall x y, x > y => x != y *)
(* Unsigned greater than *)
Lemma ugt_list_big_endian_not_eq : forall x y,
  ugt_list_big_endian x y = true -> x <> y.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y. case y. 
    - easy. 
    - intros b l. simpl. 
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. unfold not in *; intro.
          inversion H1; subst. now apply H0. }
        { destruct H. apply negb_true_iff in H0. subst. easy. }
Qed.


(* Boolean comparison *)
Lemma ugt_list_not_eq : forall x y, ugt_list x y = true -> x <> y.
Proof. 
  unfold ugt_list. unfold not. intros.
  apply ugt_list_big_endian_not_eq in H.
  subst. auto.
Qed.

Lemma bv_ugt_not_eq : forall x y, bv_ugt x y = true -> x <> y.
Proof.
  intros x y. unfold bv_ugt.
  case_eq (size x =? size y); intros.
  - now apply ugt_list_not_eq in H0.
  - now contradict H0.
Qed.

(* Prop comparison *)
Lemma ugt_list_not_eqP : forall x y, ugt_listP x y -> x <> y.
Proof.
  unfold ugt_listP.
  unfold not. intros. unfold ugt_list in H.
  case_eq (ugt_list_big_endian (List.rev x) (List.rev y)).
  + intros. apply ugt_list_big_endian_not_eq in H1. subst. now contradict H1.
  + intros. now rewrite H1 in H.
Qed.

Lemma bv_ugt_not_eqP : forall x y, bv_ugtP x y -> x <> y.
Proof. intros x y. unfold bv_ugtP.
       case_eq (size x =? size y); intros.
       - now apply ugt_list_not_eqP in H0.
       - now contradict H0.
Qed.

(* forall x y, x < y => x != y *)
(* Signed less than *)
Lemma slt_list_big_endian_not_eq : forall x y,
    slt_list_big_endian x y = true -> x <> y.
Proof.
  intros x. induction x.
  + simpl. easy.
  + intros y. case y.
    - simpl. case x; easy.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *. 
        { case a; case b; simpl; easy. }
        { easy. }
      * rewrite !orb_true_iff, !andb_true_iff.
        intro. destruct H.
        { destruct H.  apply ult_list_big_endian_not_eq in H0.
          apply Bool.eqb_prop in H. rewrite H in *.
          unfold not in *. intros. apply H0. now inversion H1. }
        { destruct H. apply negb_true_iff in H0. subst. easy. }
Qed.  

(* Boolean comparison *)
Lemma slt_list_not_eq : forall x y, slt_list x y = true -> x <> y.
Proof. unfold slt_list.
  unfold not. intros.
  apply slt_list_big_endian_not_eq in H.
  subst. auto.
Qed.

Lemma bv_slt_not_eq : forall x y, bv_slt x y = true -> x <> y.
Proof. intros x y. unfold bv_slt.
       case_eq (size x =? size y); intros.
       - now apply slt_list_not_eq in H0.
       - now contradict H0.
Qed.

(* Prop comparison *)
Lemma slt_list_not_eqP : forall x y, slt_listP x y -> x <> y.
Proof. unfold slt_listP.
  unfold not. intros. unfold slt_list in H.
  case_eq (slt_list_big_endian (List.rev x) (List.rev y)); intros.
  apply slt_list_big_endian_not_eq in H1. subst. now contradict H1.
  now rewrite H1 in H.
Qed.

Lemma bv_slt_not_eqP : forall x y, bv_sltP x y -> x <> y.
Proof. intros x y. unfold bv_sltP.
       case_eq (size x =? size y); intros.
       - now apply slt_list_not_eqP in H0.
       - now contradict H0.
Qed.


(* Equivalence of boolean and Prop comparisons *)

Lemma bv_ult_B2P: forall x y, bv_ult x y = true <-> bv_ultP x y.
Proof. intros. split; intros; unfold bv_ult, bv_ultP in *.
       + case_eq (size x =? size y). 
         - intros. rewrite H0 in H. unfold ult_listP. now rewrite H.
         - intros. rewrite H0 in H. now contradict H.
       + unfold ult_listP in *. case_eq (size x =? size y); intros.
         - rewrite H0 in H. case_eq (ult_list x y); intros. 
           * easy.
           * rewrite H1 in H. now contradict H.
         - rewrite H0 in H. now contradict H.
Qed.

Lemma bv_slt_B2P: forall x y, bv_slt x y = true <-> bv_sltP x y.
Proof. intros. split; intros; unfold bv_slt, bv_sltP in *.
       + case_eq (size x =? size y); intros; 
         rewrite H0 in H; unfold slt_listP. 
         - now rewrite H.
         - now contradict H.
       + unfold slt_listP in *. case_eq (size x =? size y); intros.
         - rewrite H0 in H. case_eq (slt_list x y); intros. 
           * easy.
           * rewrite H1 in H. now contradict H.
         - rewrite H0 in H. now contradict H.
Qed.

Lemma bv_ugt_B2P: forall x y, bv_ugt x y = true <-> bv_ugtP x y.
Proof.
  intros. split; intros; unfold bv_ugt, bv_ugtP in *.
  + case_eq (size x =? size y); intros.
    - rewrite H0 in H. unfold ugt_listP. now rewrite H.
    - rewrite H0 in H. unfold ugt_listP. now contradict H.
  + unfold ugt_listP in *. case_eq (size x =? size y); intros.
    - rewrite H0 in H. case_eq (ugt_list x y); intros.
      * easy.
      * rewrite H1 in H. now contradict H.
    - rewrite H0 in H. now contradict H.
Qed.

Lemma bv_ule_B2P: forall x y, bv_ule x y = true <-> bv_uleP x y.
Proof.
  intros. split; intros; unfold bv_ule, bv_uleP in *.
  + case_eq (size x =? size y); intros.
    - rewrite H0 in H. unfold ule_listP. now rewrite H.
    - rewrite H0 in H. now contradict H.
  + unfold ule_listP in *. case_eq (size x =? size y); intros.
    - rewrite H0 in H. case_eq (ule_list x y); intros.
      * easy.
      * rewrite H1 in H. now contradict H.
    - rewrite H0 in H. now contradict H.
Qed.


(* a >u b -> ~(a <u b) *)
Lemma ugt_list_big_endian_not_ult_list_big_endian : forall x y,
  ugt_list_big_endian x y = true -> ult_list_big_endian x y = false.
Proof.
  intros x. induction x.
  + simpl. easy.
  + intros y. case y.
    - intros. case a; case x; easy.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. case b; easy. }
        { destruct H.  apply negb_true_iff in H0. subst. easy. }
Qed.
    
Lemma ugt_list_not_ult_list : forall x y, ugt_list x y = true -> ult_list x y = false.
Proof.
  intros x y. unfold ugt_list. intros.
  apply ugt_list_big_endian_not_ult_list_big_endian in H.
  unfold ult_list. apply H.
Qed.

Lemma bv_ugt_not_bv_ult : forall x y, bv_ugt x y = true -> bv_ult x y = false.
Proof.
  intros x y. unfold bv_ugt.
  case_eq (size x =? size y); intros.
  - apply ugt_list_not_ult_list in H0. unfold bv_ult. 
    rewrite H. apply H0.
  - now contradict H0.
Qed.

Lemma ugt_listP_not_ult_listP : forall x y, ugt_listP x y -> ~ (ult_listP x y).
Proof.
  unfold ugt_listP.
  unfold not. intros. unfold ugt_list in H.
  case_eq (ugt_list_big_endian (List.rev x) (List.rev y)).
  + intros. apply ugt_list_big_endian_not_ult_list_big_endian in H1.
    unfold ult_listP in H0. unfold ult_list in H0. rewrite H1 in H0. 
    now contradict H0.
  + intros. now rewrite H1 in H.
Qed.

Lemma bv_ugtP_not_bv_ultP : forall x y, bv_ugtP x y -> ~ (bv_ultP x y).
Proof.
  intros x y. unfold bv_ugtP. unfold not.
  case_eq (size x =? size y); intros.
  - unfold ugt_listP in H0. unfold bv_ultP in H1.
    rewrite H in H1. unfold ult_listP in H1.  
    now apply ugt_listP_not_ult_listP in H0.
  - now contradict H0.
Qed.


(* a <u b -> ~(a >u b) *)
Lemma ult_list_big_endian_not_ugt_list_big_endian : forall x y,
  ult_list_big_endian x y = true -> ugt_list_big_endian x y = false.
Proof.
  intros x. induction x.
  + simpl. easy.
  + intros y. case y.
    - intros. case a; case x; easy.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. case b; easy. }
        { destruct H. apply negb_true_iff in H. subst. easy. }
Qed. 

Lemma ult_list_not_ugt_list : forall x y, ult_list x y = true -> ugt_list x y = false.
Proof.
  intros x y. unfold ult_list. intros.
  apply ult_list_big_endian_not_ugt_list_big_endian in H.
  unfold ugt_list. apply H.
Qed.

Lemma bv_ult_not_bv_ugt : forall x y, bv_ult x y = true -> bv_ugt x y = false.
Proof.
  intros x y. unfold bv_ult.
  case_eq (size x =? size y); intros.
  - apply ult_list_not_ugt_list in H0. unfold bv_ugt.
    rewrite H. apply H0.
  - now contradict H0.
Qed.

Lemma ult_listP_not_ugt_listP : forall x y, ult_listP x y -> ~ (ugt_listP x y).
Proof.
  unfold ult_listP.
  unfold not. intros. unfold ult_list in H.
  case_eq (ult_list_big_endian (List.rev x) (List.rev y)).
  + intros. apply ult_list_big_endian_not_ugt_list_big_endian in H1.
    unfold ugt_listP in H0. unfold ugt_list in H0. rewrite H1 in H0.
    now contradict H0.
  + intros. now rewrite H1 in H.
Qed.

Lemma bv_ultP_not_bv_ugtP : forall x y, bv_ultP x y -> ~ (bv_ugtP x y).
Proof. 
  intros x y. unfold bv_ultP. unfold not.
  case_eq (size x =? size y); intros.
  - unfold ult_listP in H0. unfold bv_ugtP in H1.
    rewrite H in H1. unfold ugt_listP in H1.
    now apply ugt_listP_not_ult_listP in H0.
  - now contradict H0.
Qed.


(* a <u b -> b >u a *)

Lemma ult_list_big_endian_ugt_list_big_endian : forall x y, 
  ult_list_big_endian x y = true -> ugt_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. case b; case l; easy. }
        { destruct H. apply negb_true_iff in H. subst. case l; easy. }
Qed. 

Lemma ult_list_ugt_list : forall x y, ult_list x y = true -> ugt_list y x = true.
Proof.
  intros x y. unfold ult_list. intros. 
  apply ult_list_big_endian_ugt_list_big_endian in H.
  unfold ugt_list. apply H.
Qed.

Lemma bv_ult_bv_ugt : forall x y, bv_ult x y = true -> bv_ugt y x = true.
Proof.
  intros x y. unfold bv_ult.
  case_eq (size x =? size y); intros.
  - apply ult_list_ugt_list in H0. unfold bv_ugt.
    case_eq (size y =? size x ); intros. easy.
    rewrite N.eqb_eq in H.
    rewrite H in H1.
    now rewrite N.eqb_refl in H1.
  - easy.
Qed.

Lemma ult_listP_ugt_listP : forall x y, ult_listP x y -> ugt_listP y x.
Proof.
  unfold ult_listP.
  intros. unfold ult_list in H.
  case_eq (ult_list_big_endian (List.rev x) (List.rev y)).
  + intros. unfold ugt_listP. unfold ugt_list. 
    apply (@ult_list_big_endian_ugt_list_big_endian (List.rev x) (List.rev y)) in H0.
    rewrite H0. easy.
  + intros. rewrite H0 in H. now contradict H.
Qed.

Lemma bv_ultP_bv_ugtP : forall x y, bv_ultP x y -> (bv_ugtP y x).
Proof.
  intros x y. unfold bv_ultP, bv_ugtP.
  case_eq (size x =? size y ); intros.
  - rewrite N.eqb_eq in H. rewrite H.
    rewrite N.eqb_refl.
    now apply ult_listP_ugt_listP.
  - easy.
Qed.


(*a >u b -> b <u a *)
Lemma ugt_list_big_endian_ult_list_big_endian : forall x y,
  ugt_list_big_endian x y = true -> ult_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl. 
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. case b; case l; easy. }
        { destruct H. apply negb_true_iff in H0. subst. case l; easy. }
Qed. 

Lemma ugt_list_ult_list : forall x y, ugt_list x y = true -> ult_list y x = true.
Proof.
  intros x y. unfold ugt_list. intros. 
  apply ugt_list_big_endian_ult_list_big_endian in H.
  unfold ult_list. apply H.
Qed.

Lemma bv_ugt_bv_ult : forall x y, bv_ugt x y = true -> bv_ult y x = true.
Proof.
  intros x y. unfold bv_ugt.
  case_eq (size x =? size y); intros.
  - apply ugt_list_ult_list in H0. unfold bv_ult.
    rewrite N.eqb_eq in H.
    rewrite H. now rewrite N.eqb_refl.
  - easy. 
Qed.

Lemma ugt_listP_ult_listP : forall x y, ugt_listP x y -> ult_listP y x.
Proof.
  unfold ugt_listP.
  intros. unfold ugt_list in H.
  case_eq (ugt_list_big_endian (List.rev x) (List.rev y)).
  + intros. unfold ult_listP. unfold ult_list. 
    apply (@ugt_list_big_endian_ult_list_big_endian (List.rev x) (List.rev y)) in H0.
    rewrite H0. easy.
  + intros. rewrite H0 in H. now contradict H.
Qed.
 
Lemma bv_ugtP_bv_ultP : forall x y, bv_ugtP x y -> (bv_ultP y x).
Proof.
  intros x y. unfold bv_ugtP, bv_ultP.
  case_eq (size x =? size y); intros.
  - rewrite N.eqb_eq in H.
    rewrite H, N.eqb_refl.
    now apply ugt_listP_ult_listP.
  - easy.
Qed.


Lemma nlt_be_neq_gt: forall x y,
    length x = length y -> ult_list_big_endian x y = false ->
    beq_list x y = false -> ult_list_big_endian y x = true.
Proof. intro x.
       induction x as [ | x xs IHxs ].
       - intros. simpl in *. case y in *; now contradict H. 
       - intros.
         simpl in H1.

         case_eq y; intros.
         rewrite H2 in H. now contradict H.
         simpl.
         case_eq l. intros. case_eq xs. intros.
         rewrite H2 in H1.
         rewrite H4 in H0, H. simpl in H0, H.
         rewrite H2, H3 in H0, H.
         rewrite H4, H3 in H1. simpl in H1. rewrite andb_true_r in H1.
         case b in *; case x in *; easy.
         intros.
         rewrite H4, H2, H3 in H. now contradict H.
         intros.
         rewrite H2, H3 in H0, H1.

         simpl in H0.
         case_eq xs. intros. rewrite H4, H2, H3 in H. now contradict H.
         intros. rewrite H4 in H0.
         rewrite <- H3, <- H4.
         rewrite <- H3, <- H4 in H0.
         rewrite <- H3 in H1.
         rewrite orb_false_iff in H0.
         destruct H0.

         case_eq (Bool.eqb x b); intros.
         rewrite H6 in H0, H1.
         rewrite andb_true_l in H0, H1.
         assert (Bool.eqb b x = true).
          { case b in *; case x in *; easy. }
         rewrite H7. rewrite andb_true_l.
         rewrite orb_true_iff.
         left.
         apply IHxs. rewrite H2 in H.
         now inversion H.
         easy. easy.
         assert (Bool.eqb b x = false). 
           { case b in *; case x in *; easy. }
         rewrite H7. rewrite orb_false_l.
         case x in *. case b in *.
         now contradict H6.
         now easy.
         case b in *.
         now contradict H5.
         now contradict H6.
Qed.

(* forall x, ~(x < 0) *)

Lemma not_ult_list_big_endian_x_0 : forall (x : list bool),
  ult_list_big_endian x (mk_list_false (length x)) = false.
Proof.
  intros x. induction x.
  + easy.
  + case a.
    - assert (simpl : mk_list_false (length (true :: x)) = 
              false :: mk_list_false (length x)).
      { easy. } rewrite simpl. 
      simpl. case x; easy.
    - simpl. rewrite IHx. case x; easy.
Qed.

Lemma not_ult_list_x_zero : forall (x : bitvector), 
  ult_list x (mk_list_false (length x)) = false.
Proof.
  intros x. unfold ult_list. rewrite rev_mk_list_false.
  rewrite <- length_rev. apply not_ult_list_big_endian_x_0.
Qed.

Lemma not_bv_ultP_x_zero : forall (x : bitvector), ~(bv_ultP x (zeros (size x))).
Proof.
  intros x. unfold not. intros contr_x_0.
  unfold bv_ultP in contr_x_0. rewrite zeros_size in contr_x_0.
  rewrite N.eqb_refl in contr_x_0.
  unfold ult_listP in contr_x_0.
  unfold zeros in contr_x_0. unfold size in contr_x_0. 
  rewrite Nat2N.id in contr_x_0. 
  now rewrite not_ult_list_x_zero in contr_x_0.
Qed.

Lemma not_bv_ult_x_zero : forall (x : bitvector), bv_ult x (zeros (size x)) = false.
Proof.
  intros x. unfold bv_ult. rewrite zeros_size.
  rewrite N.eqb_refl.
  unfold zeros. unfold size. rewrite Nat2N.id. apply not_ult_list_x_zero.
Qed.


(* forall a, (exists b, b > a) => (a != 1) *)

Lemma not_ugt_list_big_endian_ones : forall (b : bitvector), 
  ugt_list_big_endian (rev b) (rev (bv_not (zeros (size b)))) = false.
Proof. 
  intros. unfold zeros. unfold size. rewrite Nat2N.id.
  rewrite bv_not_false_true.
  assert (forall n : nat, rev (mk_list_true n) = mk_list_true n).
  { apply rev_mk_list_true. }
  rewrite H. rewrite <- length_rev.
  induction (rev b).
  + easy.
  + simpl. destruct l.
    - simpl. apply andb_false_r.
    - rewrite IHl. rewrite andb_false_r. 
      rewrite andb_false_r. easy.
Qed.

Lemma not_ugt_list_ones : forall (b : bitvector), 
    ugt_list b (bv_not (zeros (size b))) = false.
Proof.
  intros. unfold ugt_list.
  assert (forall (b : bitvector), ugt_list_big_endian (rev b)
    (rev (bv_not (zeros (size b)))) = false).
    { apply not_ugt_list_big_endian_ones. }
  apply H.
Qed.

Lemma not_ugt_listP_ones : forall (b : bitvector),
  ~ ugt_listP b (bv_not (zeros (size b))).
Proof.
  intros. unfold not. intros. unfold ugt_listP in H.
  assert (forall (b : bitvector), 
    ugt_list b (bv_not (zeros (size b))) = false).
  { apply not_ugt_list_ones. }
  specialize (@H0 b). rewrite H0 in H. apply H.
Qed.

Lemma bv_ugtP_not_ones : forall (a : bitvector), 
  (exists (b : bitvector), bv_ugtP b a) -> 
  ~ (a = bv_not (zeros (size a))).
Proof.
  intros. destruct H as (b, H). unfold not. intros.
  unfold bv_ugtP in H. case_eq (size b =? size a).
  + intros. pose proof H1 as H1Prop. apply Neqb_ok in H1Prop. 
  rewrite <- H1Prop in H0. rewrite H1 in H. rewrite H0 in H.
  pose proof (@not_ugt_listP_ones b). unfold not in H2. 
  apply H2. apply H.
  + intros. rewrite H1 in H. apply H.
Qed.


(* b != 1 -> b < 1 *)

Theorem rev_func : forall (b1 b2 : bitvector), b1 = b2 -> rev b1 = rev b2.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem rev_inj : forall (b1 b2 : bitvector), rev b1 = rev b2 -> b1 = b2.
Proof.
  intros.
  rewrite <- rev_involutive with (l := b1).
  rewrite <- rev_involutive with (l := b2).
  apply rev_func.
  apply H.
Qed.

Lemma rev_neg_func : forall (b1 b2 : bitvector), b1 <> b2 -> 
  rev b1 <> rev b2.
Proof.
  intros. unfold not. intros. 
  apply rev_inj in H0. unfold not in H.
  apply H in H0. apply H0.
Qed.

Theorem rev_neg_inj : forall (b1 b2 : bitvector), rev b1 <> rev b2 -> 
  b1 <> b2.
Proof.
  intros.
  rewrite <- rev_involutive with (l := b1).
  rewrite <- rev_involutive with (l := b2).
  apply rev_neg_func. apply H.
Qed.

Lemma rev_uneq : forall b : bitvector, b <> mk_list_true (length b)
    -> (rev b) <> (rev (mk_list_true (length b))).
Proof. 
  intros. apply rev_neg_inj. rewrite rev_involutive. rewrite rev_involutive.
  apply H.
Qed.

Lemma ult_list_big_endian_true : forall (b1 b2 : list bool),
  ult_list_big_endian b1 b2 = true ->
  ult_list_big_endian (true :: b1) (true :: b2) = true.
Proof.
  intros. unfold ult_list_big_endian. case b1 in *.
  + case b2 in *; easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * easy.
      * fold ult_list_big_endian. apply H.
Qed.

Lemma mk_list_true_cons : forall (b : bool) (l : list bool), 
  mk_list_true (length (b :: l)) = true :: mk_list_true (length l).
Proof.
  unfold mk_list_true. simpl. induction l; simpl; easy.
Qed.

Lemma bv_not_1_ult_list_big_endian_1 : forall (b : bitvector), 
  b <> mk_list_true (length b)
  -> ult_list_big_endian (rev b) (rev (mk_list_true (length b))) = true.
Proof.
  intros. rewrite rev_mk_list_true.
  assert (rev_uneq : forall b : bitvector, b <> mk_list_true (length b)
    -> (rev b) <> (rev (mk_list_true (length b)))).
  { apply rev_uneq. }
  apply rev_uneq in H. rewrite <- length_rev in *.
  rewrite rev_mk_list_true in H.
  destruct (rev b) as [| h t]. (*induction (rev b) as [| a l IHrev].*)
  + now contradict H.
  + assert (ult_cons_false : forall (b : list bool), 
            ult_list_big_endian (false :: b) 
            (mk_list_true (length (false :: b))) = true).
            { intros. induction b0; easy. }
    destruct h.
    - induction t as [| h2 t2 IH].
      * easy.
      * assert (ult_cons_true : forall (b : list bool), 
            ult_list_big_endian b (mk_list_true (length b)) = true ->
            ult_list_big_endian 
            (true :: b) (mk_list_true (length (true :: b))) = true).
            { pose proof ult_list_big_endian_true as ult_list_big_endian_true.
              intros. specialize (@ult_list_big_endian_true b0 (mk_list_true (length b0)) H0). 
              pose proof mk_list_true_cons as mk_list_true_cons. 
              specialize (@mk_list_true_cons true b0).
              rewrite mk_list_true_cons. apply ult_list_big_endian_true.  
            } destruct h2. 
        { assert (forall (b : list bool), 
            true :: b <> mk_list_true (length (true :: b)) -> 
            b <> mk_list_true (length b)).
            { intros. rewrite mk_list_true_cons in H0. 
              unfold not. intros. unfold not in H0. rewrite <- H1 in H0.
              now contradict H0. }
          apply H0 in H. apply IH in H.
          apply ult_cons_true in H. apply H. }
        { apply ult_cons_true. apply ult_cons_false. }
     - apply ult_cons_false. 
Qed.

Lemma bv_not_eq_1_ult_listP :forall b : bitvector, 
      b <> bv_not (zeros (size b)) -> 
      ult_listP b (bv_not (zeros (size b))).
Proof.
  intros. unfold ult_listP.
    case_eq (ult_list b (bv_not (zeros (size b)))).
    + intros. easy.
    + intros. unfold ult_list in H0. unfold zeros in *. 
      unfold size in *. rewrite Nat2N.id in *.
      rewrite bv_not_false_true in *.
      assert (forall (b : bitvector), b <> mk_list_true (length b)
        -> ult_list_big_endian (rev b) (rev (mk_list_true (length b))) = true).
      { apply bv_not_1_ult_list_big_endian_1. }
      specialize (@H1 b). specialize (@H1 H).
      rewrite H0 in H1. now contradict H1. 
Qed.

Lemma bv_not_eq_1_ultP_1 : forall (b : bitvector), 
      b <> (bv_not (zeros (size b))) -> 
      bv_ultP b (bv_not (zeros (size b))).
Proof.
  intros. unfold bv_ultP.
  assert (size b = size (bv_not (zeros (size b)))).
  { rewrite (@bv_not_size (size b) (zeros (size b))).
    + easy.
    + rewrite zeros_size. easy. }
  case_eq (size b =? size (bv_not (zeros (size b)))).
  + intros. assert (forall b : bitvector, 
      b <> bv_not (zeros (size b)) -> 
      ult_listP b (bv_not (zeros (size b)))).
      { apply bv_not_eq_1_ult_listP. }
    apply H2. apply H.
  + intros. rewrite <- H0 in H1.
    rewrite N.eqb_neq in H1. now contradict H1.
Qed.


(* forall b : BV, b <= 1 *)
Lemma ule_list_big_endian_true : forall (b1 b2 : list bool), 
  ule_list_big_endian b1 b2 = true ->
  ule_list_big_endian (true :: b1) (true :: b2) = true.
Proof.
  intros. unfold ule_list_big_endian. case b1 in *.
  + case b2 in *; easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * easy.
      * fold ult_list_big_endian. apply H.
Qed.

Lemma ule_list_big_endian_1 : forall (l : list bool), 
ule_list_big_endian l (mk_list_true (length l)) = true.
Proof.
  intros. induction l.
  + easy. 
  + case_eq a.
    - intros.
      assert (forall (n : nat), mk_list_true (S n) = true :: mk_list_true n).
      { intros. induction n; easy. }
      assert (forall (b : bool) (l : list bool), length (b :: l) = S (length l)).
      { intros. induction l0; easy. } 
      rewrite H1. rewrite H0.
      apply (@ule_list_big_endian_true l (mk_list_true (length l)) IHl).
    - intros. unfold ule_list_big_endian. 
      case_eq l; easy.
Qed.

Lemma ule_list_1 : forall (b : list bool), 
  ule_list b (mk_list_true (N.to_nat (size b))) = true.
Proof.
  intros. unfold size. rewrite Nat2N.id. unfold ule_list.
  rewrite rev_mk_list_true. rewrite <- length_rev. apply (@ule_list_big_endian_1 (rev b)).
Qed.

Lemma bv_ule_1_size : forall (x : bitvector), 
  bv_ule x (mk_list_true (N.to_nat (size x))) = true.
Proof.
  intros. induction x.
  + easy. 
  + unfold bv_ule. 
    case_eq (size (a :: x) =? size (mk_list_true (N.to_nat (size (a :: x))))).
    - intros. rewrite ule_list_1. easy.
    - intros. unfold size in H. rewrite Nat2N.id in H.
      rewrite length_mk_list_true in H.
      now rewrite N.eqb_refl in H.
Qed.

Lemma bv_ule_1_length : forall (x : bitvector),
  bv_ule x (mk_list_true (length x)) = true.
Proof.
  intros. pose proof (@bv_ule_1_size x). unfold size in H.
  rewrite Nat2N.id in H. apply H.
Qed.

Lemma bv_uleP_1_size : forall (x : bitvector), bv_uleP x (mk_list_true (N.to_nat (size x))).
Proof.
  intros. induction x.
  + easy. 
  + unfold bv_uleP. 
    case_eq (size (a :: x) =? size (mk_list_true (N.to_nat (size (a :: x))))).
    - intros. unfold ule_listP. rewrite ule_list_1. easy.
    - intros. unfold size in H. rewrite Nat2N.id in H.
      rewrite length_mk_list_true in H.
      now rewrite N.eqb_refl in H.
Qed.

Lemma bv_uleP_1_length : forall (x : bitvector),
  bv_uleP x (mk_list_true (length x)).
Proof.
  intros. pose proof (@bv_uleP_1_size x). unfold size in H.
  rewrite Nat2N.id in H. apply H.
Qed.


(* a <s b -> b >s a *)

Lemma slt_list_big_endian_sgt_list_big_endian : forall x y, 
  slt_list_big_endian x y = true -> sgt_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. unfold slt_list_big_endian in IHx.
          unfold sgt_list_big_endian in IHx. case l in *; 
          left; split.
            - apply Bool.eqb_prop in H; rewrite H. apply eqb_reflx.
            - now apply ult_list_big_endian_ugt_list_big_endian.
            - apply Bool.eqb_prop in H. rewrite H. apply eqb_reflx.
            - now apply ult_list_big_endian_ugt_list_big_endian.
        }
        destruct H. apply negb_true_iff in H0. subst. now right.
Qed. 

Lemma slt_list_sgt_list : forall x y, slt_list x y = true -> sgt_list y x = true.
Proof.
  intros x y. unfold slt_list. intros. 
  apply slt_list_big_endian_sgt_list_big_endian in H.
  unfold sgt_list. apply H.
Qed.

Lemma bv_slt_bv_sgt : forall x y, bv_slt x y = true -> bv_sgt y x = true.
Proof.
  intros x y. unfold bv_slt.
  case_eq (size x =? size y); intros.
  - apply slt_list_sgt_list in H0. unfold bv_sgt.
    case_eq (size y =? size x ); intros. easy.
    rewrite N.eqb_eq in H.
    rewrite H in H1.
    now rewrite N.eqb_refl in H1.
  - easy.
Qed.

Lemma slt_listP_sgt_listP : forall x y, slt_listP x y -> sgt_listP y x.
Proof.
  unfold slt_listP, sgt_listP.
  intros. unfold sgt_list, slt_list in *.
  case_eq (slt_list_big_endian (List.rev x) (List.rev y)).
  + intros. apply (@slt_list_big_endian_sgt_list_big_endian (List.rev x) (List.rev y)) in H0. now rewrite H0.
  + intros. rewrite H0 in H. now contradict H.
Qed.

Lemma bv_sltP_bv_sgtP : forall x y, bv_sltP x y -> (bv_sgtP y x).
Proof.
  intros x y. unfold bv_sltP, bv_sgtP.
  case_eq (size x =? size y ); intros.
  - rewrite N.eqb_eq in H. rewrite H.
    rewrite N.eqb_refl.
    now apply slt_listP_sgt_listP.
  - easy.
Qed.


(*a >s b -> b <s a *)
Lemma sgt_list_big_endian_slt_list_big_endian : forall x y,
  sgt_list_big_endian x y = true -> slt_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. easy. 
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl. 
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. unfold sgt_list_big_endian in IHx.
          unfold slt_list_big_endian in IHx. case l in *; left; split.
          - apply Bool.eqb_prop in H; rewrite H. apply eqb_reflx.
          - now apply ugt_list_big_endian_ult_list_big_endian. 
          - apply Bool.eqb_prop in H. rewrite H. apply eqb_reflx.
          - now apply ugt_list_big_endian_ult_list_big_endian. }
        destruct H. apply negb_true_iff in H. subst. now right.
Qed.
 
Lemma sgt_list_slt_list : forall x y, sgt_list x y = true -> slt_list y x = true.
Proof.
  intros x y. unfold sgt_list. intros. 
  apply sgt_list_big_endian_slt_list_big_endian in H.
  unfold slt_list. apply H.
Qed.

Lemma bv_sgt_bv_slt : forall x y, bv_sgt x y = true -> bv_slt y x = true.
Proof.
  intros x y. unfold bv_sgt.
  case_eq (size x =? size y); intros.
  - apply sgt_list_slt_list in H0. unfold bv_slt.
    rewrite N.eqb_eq in H.
    rewrite H. now rewrite N.eqb_refl.
  - easy. 
Qed.

Lemma sgt_listP_slt_listP : forall x y, sgt_listP x y -> slt_listP y x.
Proof.
  unfold sgt_listP.
  intros. unfold sgt_list in H.
  case_eq (sgt_list_big_endian (List.rev x) (List.rev y)).
  + intros. unfold slt_listP. unfold slt_list. 
    apply (@sgt_list_big_endian_slt_list_big_endian (List.rev x) (List.rev y)) in H0.
    rewrite H0. easy.
  + intros. rewrite H0 in H. now contradict H.
Qed.
 
Lemma bv_sgtP_bv_sltP : forall x y, bv_sgtP x y -> (bv_sltP y x).
Proof.
  intros x y. unfold bv_sgtP, bv_sltP.
  case_eq (size x =? size y); intros.
  - rewrite N.eqb_eq in H.
    rewrite H, N.eqb_refl.
    now apply sgt_listP_slt_listP.
  - easy.
Qed.


(* bv_and x y <= y *)

Lemma ule_list_big_endian_map2_and : forall (x y : list bool),
  length x = length y -> 
  ule_list_big_endian (map2 andb x y) x = true.
Proof.
  induction x; intros.
  + now destruct y.
  + destruct y.
    - easy.
    - simpl.
      rewrite IHx.
      * now destruct a; destruct b.
      * now injection H.
Qed.

Lemma ule_list_map2_and : forall (x y : list bool),
  length x = length y -> 
  ule_list (map2 andb x y) x = true.
Proof.
  intros.
  unfold ule_list.
  rewrite rev_map2_and.
  + apply ule_list_big_endian_map2_and.
    now rewrite !length_rev.
  + apply H.
Qed.

Lemma bv_ule_and : forall (x y : bitvector),
  size x = size y ->
  bv_ule (bv_and x y) x = true.
Proof.
  intros.
  unfold bv_ule.
  rewrite (@bv_and_size (size x)).
  + rewrite N.eqb_refl.
    unfold bv_and.
    rewrite H.
    rewrite N.eqb_refl.
    unfold bits.
    apply ule_list_map2_and.
    now apply Nat2N.inj.
  + easy.
  + easy.
Qed.






(** bitvector ult/slt *)

Lemma rev_eq: forall x y, beq_list x y = true ->
                     beq_list (List.rev x) (List.rev y)  = true.
Proof. intros.
       apply List_eq in H.
       rewrite H.
       now apply List_eq_refl.
Qed.

Lemma rev_neq: forall x y, beq_list x y = false ->
                      beq_list (List.rev x) (List.rev y) = false.
Proof. intros.
       specialize (@List_neq x y H).
       intros.
       apply not_true_is_false.
       unfold not in *.
       intros. apply H0.
       apply List_eq in H1.

       specialize (f_equal (@List.rev bool) H1 ).
       intros.
       now rewrite !rev_involutive in H2.
Qed.

Lemma nlt_neq_gt: forall x y,
    length x = length y -> ult_list x y = false -> 
    beq_list x y = false -> ult_list y x = true.
Proof. intros.
  unfold ult_list in *.
  apply nlt_be_neq_gt.
  now rewrite !length_rev.
  easy. 
  now apply rev_neq in H1.
Qed.


(* bitvector SUBT properties *)

Lemma bv_subt_size: forall n a b, size a = n -> size b = n -> size (bv_subt a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_subt, size, bits in *. rewrite H0, H1. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- subst_list_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt_empty_neutral_r: forall a, (bv_subt a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list_empty_neutral. reflexivity.
Qed.

Lemma bv_subt'_size: forall n a b, (size a) = n -> (size b) = n -> size (bv_subt' a b) = n.
Proof. intros n a b H0 H1. unfold bv_subt', size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- subst_list'_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt'_empty_neutral_r: forall a, (bv_subt' a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt', size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list'_empty_neutral. reflexivity.
Qed.

(* bitwise ADD-NEG properties *)

Lemma add_neg_list_carry_false: forall a b c, add_list_ingr a (add_list_ingr b c true) false = add_list_ingr a (add_list_ingr b c false) true.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. auto.
       - case b as [ | b ys].
         + simpl. auto.
         + case c as [ | c zs].
           * simpl. auto.
           * simpl.
             case_eq (add_carry b c false); intros r0 c0 Heq0.
             case_eq (add_carry b c true); intros r1 c1 Heq1.
             case_eq (add_carry a r1 false); intros r2 c2 Heq2.
             case_eq (add_carry a r0 true); intros r3 c3 Heq3.
             case a, b, c; inversion Heq0; inversion Heq1; 
             inversion Heq2; inversion Heq3; rewrite <- H2 in H4; 
             rewrite <- H0 in H5; inversion H4; inversion H5; apply f_equal;
             try reflexivity; rewrite IHxs; reflexivity.
Qed.


Lemma add_neg_list_carry_neg_f: forall a, (add_list_ingr a (map negb a) false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_f_r: forall a, (add_list_ingr (map negb a) a false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry (negb a) a false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f_r in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_t: forall a, (add_list_ingr a (map negb a) true) = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) true); intros r0 c0 Heq0.
         rewrite add_carry_neg_t in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry: forall a, add_list_ingr a (twos_complement a) false = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - unfold twos_complement. rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
         rewrite add_list_carry_empty_neutral_r.
         rewrite add_neg_list_carry_neg_t. reflexivity.
Qed.

Lemma add_neg_list_absorb: forall a, add_list a (twos_complement a) = mk_list_false (length a).
Proof. intro a. unfold add_list. rewrite add_neg_list_carry. reflexivity. Qed.

Lemma subt'_add_list: forall (a b : bitvector) (n : N), 
  N.of_nat (length a) = n -> 
  N.of_nat (length b) = n -> 
  subst_list' (add_list_ingr a b false) b = a.
Proof. intros.
  unfold subst_list', twos_complement, add_list.
  rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
  rewrite add_list_carry_empty_neutral_r.
  specialize (@add_list_carry_assoc a b (map negb b) false true false true).
  intro H2. rewrite H2; try auto. rewrite add_neg_list_carry_neg_f.
  assert (length b = length a).
    { rewrite <- H in H0. now apply Nat2N.inj in H0. }
  rewrite H1.
  now rewrite add_list_carry_unit_t.
Qed.

(* bitvector ADD-NEG properties *)

Lemma bv_add_neg_unit: forall a, bv_add a (bv_not a) = mk_list_true (nat_of_N (size a)).
Proof. intro a. unfold bv_add, bv_not, size, bits. rewrite not_list_length.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold add_list. rewrite add_neg_list_carry_neg_f.
       rewrite Nat2N.id, not_list_length. reflexivity.
Qed. 


(* bitwise ADD-SUBST properties *)

Lemma add_subst_list_carry_opp: forall n a b, (length a) = n -> (length b) = n -> (add_list_ingr (subst_list' a b) b false) = a.
Proof. intros n a b H0 H1.
       unfold subst_list', twos_complement, add_list.
       rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
       rewrite add_list_carry_empty_neutral_r.
       specialize (@add_list_carry_assoc a (map negb b) b true false false true).
       intro H2. rewrite H2; try auto. rewrite add_neg_list_carry_neg_f_r.
       rewrite H1. rewrite <- H0. rewrite add_list_carry_unit_t; reflexivity.
Qed.

Lemma add_subst_opp:  forall n a b, (length a) = n -> (length b) = n -> (add_list (subst_list' a b) b) = a.
Proof. intros n a b H0 H1. unfold add_list, size, bits.
       apply (@add_subst_list_carry_opp n a b); easy.
Qed.

(* bitvector ADD-SUBT properties *)

Lemma bv_add_subst_opp:  forall n a b, (size a) = n -> (size b) = n -> (bv_add (bv_subt' a b) b) = a.
Proof. intros n a b H0 H1. unfold bv_add, bv_subt', add_list, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@subst_list'_length a b). rewrite H0.
       rewrite N.compare_refl. rewrite (@add_subst_list_carry_opp (nat_of_N n) a b); auto;
       inversion H0; rewrite Nat2N.id; auto.
       symmetry. now rewrite <- Nat2N.inj_iff, H0.
        now rewrite <- Nat2N.inj_iff, H0.
Qed.

(* a + b - b = a *)
Lemma bv_subt'_add:  forall n a b, 
  (size a) = n -> (size b) = n -> (bv_subt' (bv_add a b) b) = a.
Proof. intros n a b H0 H1. unfold bv_add, bv_subt', add_list, size, bits in *.
  rewrite H0, H1.
  rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
  rewrite <- add_list_carry_length_eq, H0.
  rewrite N.compare_refl.
  apply (@subt'_add_list a b n); easy.
  rewrite <- H0 in H1. now apply Nat2N.inj in H1.
Qed.

Theorem bvadd_U: forall (n : N),
  forall (s t x: bitvector), (size s) = n /\ (size t) = n /\ (size x) = n ->
  (bv_add x s) = t <-> (x = (bv_subt' t s)).
Proof. intros n s t x (Hs, (Ht, Hx)).
  split; intro A.
  - rewrite <- A. symmetry. exact (@bv_subt'_add n x s Hx Hs).
  - rewrite A. exact (bv_add_subst_opp Ht Hs).
Qed.


Lemma neg_add_list_ingr : forall (x y : list bool) (b : bool), 
  map negb (add_list_ingr x y b) = add_list_ingr (map negb x) (map negb y) (negb b).
Proof.
  induction x.
  + induction y; easy.
  + induction y.
    - easy.
    - intros b. case b.
      * case a.
        ++ case a0; specialize (@IHx y true); simpl; rewrite IHx; easy.
        ++ case a0.
           -- simpl. specialize (@IHx y true). rewrite IHx. easy.
           -- simpl. specialize (@IHx y false). rewrite IHx. easy.
      * case a.
        ++ case a0.
           -- simpl. specialize (@IHx y true). rewrite IHx. easy.
           -- simpl. specialize (@IHx y false). rewrite IHx. easy.
        ++ case a0; simpl; specialize (@IHx y false); rewrite IHx; easy.
Qed.

Lemma bv_neg_involutive_aux : forall (x y z : list bool), 
  add_list_ingr (add_list_ingr x y false) z true 
  = add_list_ingr (add_list_ingr x y true) z false.
Proof.
  induction x.
  + induction y; induction z; easy.
  + induction y.
    - induction z; easy.
    - induction z.
      * case a; case a0; easy.
      * case a in *.
        ++ case a0 in *.
           -- easy.
           -- Reconstr.scrush.
        ++ case a0 in *; Reconstr.scrush.
Qed. 

Lemma bv_neg_involutive : forall b, bv_neg (bv_neg b) = b.
Proof.
  intros b. unfold bv_neg.
  induction b.
  + easy.
  + unfold twos_complement at 1. rewrite <- length_twos_complement.
    unfold twos_complement in *. 
    pose proof (@add_list_carry_length_eq (map negb b) (mk_list_false (length b)) true).
    rewrite (@length_map bool bool negb b) in H. 
    rewrite (@length_mk_list_false (length b)) in H. specialize (@H eq_refl).
    rewrite <- H in IHb. rewrite neg_add_list_ingr in *. rewrite not_list_involutative in *. 
    rewrite not_list_false_true in *. assert (negb true = false) by easy.
    rewrite H0 in *. case a. 
    - simpl. rewrite bv_neg_involutive_aux in IHb. rewrite IHb. easy.
    - simpl. rewrite IHb. easy.
Qed.



 (* bitvector MULT properties *) 

Lemma prop_mult_bool_step_k_h_len: forall a b c k,
length (mult_bool_step_k_h a b c k) = length a.
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. simpl. easy.
       - intros.
         case b in *. simpl. rewrite IHa. simpl. lia.
         simpl. case (k - 1 <? 0)%Z; simpl; now rewrite IHa.
Qed. 

Lemma mult_bool_step_k_h_nil : forall (a : list bool) (k : Z),
  mult_bool_step_k_h a [] false k = a.
Proof.
  intros.
  induction a.
  + easy.
  + simpl.
    now rewrite IHa.
Qed.

Lemma empty_list_length: forall {A: Type} (a: list A), (length a = 0)%nat <-> a = [].
Proof. intros A a.
       induction a; split; intros; auto; contradict H; easy.
Qed.

Lemma prop_mult_bool_step: forall k' a b res k, 
                       length (mult_bool_step a b res k k') = (length res)%nat.
Proof. intro k'.
       induction k'.
       - intros. simpl. rewrite prop_mult_bool_step_k_h_len. simpl. lia.
       - intros. simpl. rewrite IHk'. rewrite prop_mult_bool_step_k_h_len. simpl; lia.
Qed.

Lemma and_with_bool_len: forall a b, length (and_with_bool a b) = length a.
Proof. intro a.
       - induction a.
         intros. now simpl.
         intros. simpl. now rewrite IHa.
Qed.

Lemma and_with_true : forall (x : list bool),
  and_with_bool x true = x.
Proof.
  induction x.
  + easy.
  + simpl.
    now rewrite IHx.
Qed.

Lemma and_with_false : forall (x : list bool),
  and_with_bool x false = mk_list_false (length x).
Proof.
  induction x.
  + easy.
  + simpl.
    now rewrite IHx.
Qed.

Lemma and_with_bool_app : forall (x y : list bool) (b : bool),
  (and_with_bool (x ++ y) b) = and_with_bool x b ++ and_with_bool y b.
Proof.
  intros.
  induction x.
  + easy.
  + simpl.
    now rewrite IHx.
Qed.

Lemma bv_mult_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_mult a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold mult_list, bvmult_bool.
       case_eq (length a).
         intros.
         + rewrite empty_list_length in H. rewrite H in *. now simpl in *.
         + intros.
           case n0 in *. now rewrite and_with_bool_len.
           rewrite prop_mult_bool_step. now rewrite and_with_bool_len.
Qed.


(* miscellaneous properties of nth, skipn and firstn *)

Lemma skipn_length_minus_1 : forall (a : list bool) (n : nat),
  length a = S n -> skipn n a = [nth n a false].
Proof.
  induction a; intros.
  + easy.
  + destruct n.
    - now destruct a0.
    - apply IHa.
      now injection H.
Qed.

Lemma nth_cons_skip_n : forall (a : list bool) (n : nat),
  (n < length a)%nat -> skipn n a = nth n a false :: skipn (S n) a.
Proof.
  induction a; intros.
  + now apply Nat.nlt_0_r in H.
  + destruct n.
    - easy.
    - simpl.
      rewrite IHa.
      * easy.
      * now apply Nat.succ_lt_mono.
Qed.

Lemma first_n_app_cons : forall (a : list bool) (n : nat),
  (n < length a)%nat -> firstn (S n) a = firstn n a ++ [nth n a false].
Proof.
  induction a; intros.
  + now apply Nat.nlt_0_r in H.
  + destruct n.
    - easy.
    - simpl.
      f_equal.
      apply IHa.
      now apply Nat.succ_lt_mono.
Qed.

 (** list extraction *)
  Fixpoint extract (x: list bool) (i j: nat) : list bool :=
    match x with
      | [] => []
      | bx :: x' => 
      match i with
        | O      =>
        match j with
          | O    => []
          | S j' => bx :: extract x' i j'
        end
        | S i'   => 
        match j with
          | O    => []
          | S j' => extract x' i' j'
        end
     end
   end.

  Lemma zero_false: forall p, ~ 0 >= Npos p.
  Proof. intro p. induction p; lia. Qed.

  Lemma min_distr: forall i j: N, N.to_nat (j - i) = ((N.to_nat j) - (N.to_nat i))%nat.
  Proof. intros i j; case i; case j in *; try intros; lia. Qed. 

  Lemma posSn: forall n, (Pos.to_nat (Pos.of_succ_nat n)) = S n.
  Proof. intros; case n; [easy | intros; lia ]. Qed.

  Lemma _length_extract: forall a (i j: N) (H0: (N.of_nat (length a)) >= j) (H1: j >= i), 
                         length (extract a 0 (N.to_nat j)) = (N.to_nat j).
  Proof. intro a.
         induction a as [ | xa xsa IHa ].
         - simpl. case i in *. case j in *.
           easy. lia.
           case j in *; lia.
         - intros. simpl.
           case_eq j. intros.
           now simpl.
           intros. rewrite <- H.
           case_eq (N.to_nat j).
           easy. intros. simpl.
           apply f_equal.
           specialize (@IHa 0%N (N.of_nat n)).
           rewrite Nat2N.id in IHa.
           apply IHa.
           apply (f_equal (N.of_nat)) in H2.
           rewrite N2Nat.id in H2.
           rewrite H2 in H0. simpl in *. lia.
           lia.
  Qed.

  Lemma length_extract: forall a (i j: N) (H0: (N.of_nat (length a)) >= j) (H1: j >= i), 
                        length (extract a (N.to_nat i) (N.to_nat j)) = (N.to_nat (j - i)).
  Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. simpl.
         case i in *. case j in *.
         easy. simpl in *.
         contradict H0. apply zero_false.
         case j in *. now simpl.
         apply zero_false in H0; now contradict H0.
       - intros. simpl.     
         case_eq (N.to_nat i). intros.
         case_eq (N.to_nat j). intros.
         rewrite min_distr. now rewrite H, H2.
         intros. simpl.
         rewrite min_distr. rewrite H, H2.
         simpl. apply f_equal.

         specialize (@IHa 0%N (N.of_nat n)).
         rewrite Nat2N.id in IHa.
         simpl in *.
         rewrite IHa. lia.
         lia. lia.
         intros.
         case_eq (N.to_nat j).
         simpl. intros.
         rewrite min_distr. rewrite H, H2. now simpl.
         intros.
         rewrite min_distr. rewrite H, H2.
         simpl.
         specialize (@IHa (N.of_nat n) (N.of_nat n0)).
         rewrite !Nat2N.id in IHa.
         rewrite IHa. lia.
         apply (f_equal (N.of_nat)) in H2.
         rewrite N2Nat.id in H2.
         rewrite H2 in H0. simpl in H0. lia.
         lia.
Qed.

  (** bit-vector extraction *)
  Definition bv_extr (i n0 n1: N) a : bitvector :=
    if (N.ltb n1 (n0 + i)) then mk_list_false (nat_of_N n0)
    else  extract a (nat_of_N i) (nat_of_N (n0 + i)).

  Lemma not_ltb: forall (n0 n1 i: N), (n1 <? n0 + i)%N = false -> n1 >= n0 + i.
  Proof. intro n0.
         induction n0.
         intros. simpl in *.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. lia.
         intros. simpl.
         case_eq i.
         intros. subst. simpl in H.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. intros. simpl in H. lia.
         intros. subst.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. lia.
  Qed.
 
  Lemma bv_extr_size: forall (i n0 n1 : N) a, 
                      size a = n1 -> size (@bv_extr i n0 n1 a) = n0%N.
  Proof. 
    intros. unfold bv_extr, size in *.
    case_eq (n1 <? n0 + i).
    intros. now rewrite length_mk_list_false, N2Nat.id.
    intros.
    specialize (@length_extract a i (n0 + i)). intros.
    assert ((n0 + i - i) = n0)%N.
    { lia. } rewrite H2 in H1.
    rewrite H1.
      now rewrite N2Nat.id.
      rewrite H.
      now apply not_ltb.
      lia.
  Qed.

Lemma extract_app: forall (a b: list bool), extract (a ++ b) 0 (length a) = a.
Proof. intro a.
       induction a; intros.
       - cbn. case_eq b; intros.
         + now cbn.
         + now cbn.
       - cbn. now rewrite (IHa b).
Qed. 

Lemma extract_all: forall (a: list bool), extract a 0 (length a) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. now rewrite IHa at 1.
Qed. 

Lemma extract_app_all: forall (a b: list bool),
extract a 0 (length b) ++ extract a (length b) (length a) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq b; intros.
         cbn. now rewrite (extract_all a0).
         cbn. f_equal. now rewrite IHa.
Qed.

  (** list extension *)
  Fixpoint extend (x: list bool) (i: nat) (b: bool) {struct i}: list bool :=
    match i with
      | O => x
      | S i' =>  b :: extend x i' b
    end.

  Definition zextend (x: list bool) (i: nat): list bool :=
    extend x i false.

  Definition sextend (x: list bool) (i: nat): list bool :=
    match x with
      | []       => mk_list_false i
      | xb :: x' => extend x i xb
    end.

  Lemma extend_size_zero: forall i b, (length (extend [] i b)) = i.
  Proof.
    intros.
    induction i as [ | xi IHi].
    - now simpl.
    - simpl. now rewrite IHi.
  Qed.

  Lemma extend_size_one: forall i a b, length (extend [a] i b) = S i.
  Proof. intros.
         induction i.
         - now simpl.
         - simpl. now rewrite IHi.
  Qed.

  Lemma length_extend: forall a i b, length (extend a i b) = ((length a) + i)%nat.
  Proof. intro a.
         induction a.
         - intros. simpl. now rewrite extend_size_zero.
         - intros.
           induction i.
           + intros. simpl. lia.
           + intros. simpl. apply f_equal.
             rewrite IHi. simpl. lia.
   Qed.

  Lemma zextend_size_zero: forall i, (length (zextend [] i)) = i.
  Proof.
    intros. unfold zextend. apply extend_size_zero. 
  Qed.

  Lemma zextend_size_one: forall i a, length (zextend [a] i) = S i.
  Proof.
    intros. unfold zextend. apply extend_size_one. 
  Qed.

  Lemma length_zextend: forall a i, length (zextend a i) = ((length a) + i)%nat.
  Proof.
     intros. unfold zextend. apply length_extend.
  Qed.

  Lemma sextend_size_zero: forall i, (length (sextend [] i)) = i.
  Proof.
    intros. unfold sextend. now rewrite length_mk_list_false.
  Qed.

  Lemma sextend_size_one: forall i a, length (sextend [a] i) = S i.
  Proof.
    intros. unfold sextend. apply extend_size_one. 
  Qed.

  Lemma length_sextend: forall a i, length (sextend a i) = ((length a) + i)%nat.
  Proof.
     intros. unfold sextend.
     case_eq a. intros. rewrite length_mk_list_false. easy.
     intros. apply length_extend.
  Qed.

  (** bit-vector extension *)
  Definition bv_zextn (n i: N) (a: bitvector): bitvector :=
    zextend a (nat_of_N i).

  Definition bv_sextn (n i: N) (a: bitvector): bitvector :=
    sextend a (nat_of_N i).

  Lemma plus_distr: forall i j: N, N.to_nat (j + i) = ((N.to_nat j) + (N.to_nat i))%nat.
  Proof. intros i j; case i; case j in *; try intros; lia. Qed. 
 
  Lemma bv_zextn_size: forall n (i: N) a, 
                      size a = n -> size (@bv_zextn n i a) = (i + n)%N.
  Proof.
    intros. unfold bv_zextn, zextend, size in *.
    rewrite <- N2Nat.id. apply f_equal. 
    specialize (@length_extend a (nat_of_N i) false). intros.
    rewrite H0. rewrite plus_distr. rewrite Nat.add_comm.
    apply f_equal.
    apply (f_equal (N.to_nat)) in H.
    now rewrite Nat2N.id in H.
  Qed.

  Lemma bv_sextn_size: forall n (i: N) a, 
                      size a = n -> size (@bv_sextn n i a) = (i + n)%N.
  Proof.
    intros. unfold bv_sextn, sextend, size in *.
    rewrite <- N2Nat.id. apply f_equal.
    case_eq a.
    intros. rewrite length_mk_list_false.
    rewrite H0 in H. simpl in H. rewrite <- H.
    lia.
    intros.
    specialize (@length_extend a (nat_of_N i) b). intros.
    subst. rewrite plus_distr. rewrite Nat.add_comm.
    rewrite Nat2N.id.
    now rewrite <- H1.
  Qed.



(* BV Shift Operations *)


(*BV -> Nat Conversion *)

Fixpoint pow2 (n: nat): nat :=
  match n with
    | O => 1%nat
    | S n' => (2 * pow2 n')%nat
  end.

Fixpoint _list2nat_be (a: list bool) (n i: nat) : nat :=
  match a with
    | [] => n
    | xa :: xsa =>
        if xa then _list2nat_be xsa (n + (pow2 i)) (i + 1)
        else _list2nat_be xsa n (i + 1)
  end.  

Definition list2nat_be (a: list bool) := _list2nat_be a 0 0.

Definition bv2nat (a: bitvector) := list2nat_be a.


Fixpoint list2N (a: list bool) :=
  match a with
    | []  => 0
    | x ::  xs => if x then N.succ_double (list2N xs) else N.double (list2N xs)
  end.

Definition list2nat_be_a (a: list bool) := N.to_nat (list2N a).

Definition bv2nat_a (a: list bool) := list2nat_be_a a.


(*Nat -> BV Conversion *)

Fixpoint pos2list (n: positive) acc :=
  match n with
    | xI m => pos2list m (acc ++ [true])
    | xO m => pos2list m (acc ++ [false])
    | xH => (acc ++ [true])
  end.

Lemma pos2list_acc: forall p a, (pos2list p a) = a ++ (pos2list p []).
Proof. intro p.
       induction p; intros.
       - cbn. rewrite IHp. specialize (IHp [true]).
         rewrite IHp. now rewrite app_assoc.
       - cbn. rewrite IHp. specialize (IHp [false]).
         rewrite IHp. now rewrite app_assoc.
       - now cbn.
Qed.

Lemma length_pos2list_acc: forall p a, (length (pos2list p a)) = (length a  + length (pos2list p []))%nat.
Proof. intros p a.
       now rewrite pos2list_acc, length_app.
Qed.

Lemma length_pos2list_nil: forall p, 
length (pos2list p []) = Pos.to_nat (Pos.size p).
Proof. intro p.
       induction p; intros.
       - cbn. rewrite length_pos2list_acc.
         cbn. rewrite IHp.
         Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty.
       - cbn. rewrite length_pos2list_acc. cbn. rewrite IHp.
         Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty.
       - now cbn.
Qed.

Lemma length_pos2list: forall p a, 
  (length (pos2list p a)) = (length a  + N.to_nat (N.size (Npos p)))%nat.
Proof. intros.  
       rewrite pos2list_acc, length_app.
       f_equal. rewrite length_pos2list_nil.
       Reconstr.reasy (@Coq.ZArith.Znat.positive_N_nat) (@Coq.NArith.BinNatDef.N.size).
Qed.

Definition N2list (n: N) s :=
  match n with 
    | N0     => mk_list_false s
    | Npos p => if (s <? (N.to_nat (N.size n)))%nat then (firstn s (pos2list p []))
                else (pos2list p []) ++ mk_list_false (s - (N.to_nat (N.size n)))
  end.

Lemma length_N2list: forall n s, length (N2list n s) = s.
Proof. intro n.
       induction n; intros.
       - cbn. now rewrite length_mk_list_false.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + contradict H.
          	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.is_pos, 
            @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty. 
         + case_eq ( (s <=? n)%nat); intros.
           * rewrite length_firstn. rewrite length_pos2list_nil, H.
            	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.min_l,
               @Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Arith.PeanoNat.Nat.succ_le_mono)
              (@Coq.Init.Nat.min, @Coq.Init.Peano.lt).
           * rewrite length_app, length_pos2list_nil, H, length_mk_list_false.
             rewrite Coq.Arith.Arith_base.le_plus_minus_stt with (n := S n).
             reflexivity.
             specialize(Arith.Compare_dec.leb_complete_conv); intro Ha.
             specialize(Ha n s H0).
             easy.
Qed.

Definition nat2bv (n: nat) (s: N): bitvector := N2list (N.of_nat n) (N.to_nat s).

Lemma length_nat2bv: forall n s, length (nat2bv n s) = N.to_nat s.
Proof. intros. unfold nat2bv.
       now rewrite length_N2list.
Qed.

Lemma nat2bv_size: forall (n: nat) (s: N), size (nat2bv n s) = s.
Proof. intros.
       Reconstr.reasy (@Coq.NArith.Nnat.N2Nat.id,
        @RAWBITVECTOR_LIST.length_nat2bv) (@RAWBITVECTOR_LIST.size).
Qed.

(* unsigned division: b=0 yields all-ones (SMT-LIB bvudiv semantics) *)
Definition udiv_list (a b : list bool) : list bool :=
  if beq_list b (mk_list_false (length b))
  then mk_list_true (length a)
  else N2list (N.div (list2N a) (list2N b)) (length a).

Definition bv_udiv (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then udiv_list a b
  else nil.

(* unsigned remainder: b=0 yields a (SMT-LIB bvurem semantics) *)
Definition urem_list (a b : list bool) : list bool :=
  if beq_list b (mk_list_false (length b))
  then a
  else N2list (N.modulo (list2N a) (list2N b)) (length a).

Definition bv_urem (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then urem_list a b
  else nil.

Lemma bv_udiv_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_udiv a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_udiv, udiv_list, size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       destruct (beq_list b (mk_list_false (length b))).
       - now rewrite length_mk_list_true.
       - now rewrite length_N2list.
Qed.

Lemma bv_urem_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_urem a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_urem, urem_list, size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       destruct (beq_list b (mk_list_false (length b))).
       - easy.
       - now rewrite length_N2list.
Qed.

Lemma N2list_S_true: forall n m,
N2list (N.succ_double n) (S m) = true :: N2list n m.
Proof. intro n.
       induction n; intros.
       - cbn. rewrite Pos2Nat.inj_1. assert ((m - 0)%nat = m) by lia. now rewrite H.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + cbn. contradict H.
  	         Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0,
             @Coq.PArith.Pnat.Pos2Nat.is_pos) Reconstr.Empty.
         + assert ((Pos.to_nat (Pos.succ (Pos.size p))%nat = S (S n))).
           { Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. }
           rewrite H0.
           case_eq (m <=? n)%nat; intros; rewrite pos2list_acc; now cbn.
Qed.

Lemma N2list_S_false: forall n m,
N2list (N.double n) (S m) = false :: N2list n m.
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + cbn. contradict H.
  	         Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0,
             @Coq.PArith.Pnat.Pos2Nat.is_pos) Reconstr.Empty.
         + assert ((Pos.to_nat (Pos.succ (Pos.size p))%nat = S (S n))).
           { Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. }
           rewrite H0.
           case_eq (m <=? n)%nat; intros; rewrite pos2list_acc; now cbn.
Qed.

Lemma N2List_list2N: forall a, N2list (list2N a) (length a) = a.
Proof. intro a. 
       induction a; intros.
       - now cbn.
       - cbn in *. case_eq a; intros.
         + now rewrite N2list_S_true, IHa.
         + now rewrite N2list_S_false, IHa.
Qed.


Lemma list2N_pos2list: forall p, list2N (pos2list p []) = N.pos p.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite pos2list_acc. cbn. rewrite IHp.
          Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.succ_double).
        - cbn. rewrite pos2list_acc. cbn. rewrite IHp.
          Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.succ_double).
        - now cbn.
Qed.

Lemma list2N_N2List: forall a, list2N (N2list a (N.to_nat (N.size a))) = a.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
          + contradict H. Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.is_pos,
              @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty.
          + assert ((S n <=? n)%nat = false). rewrite Nat.leb_gt.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_diag_r) Reconstr.Empty.
            rewrite H0. cbn.
            assert (mk_list_false (n - n) = nil).
            { Reconstr.rsimple (@Coq.Init.Peano.plus_n_O, @Coq.Init.Peano.le_n, 
               @Coq.Arith.PeanoNat.Nat.sub_0_le) (@RAWBITVECTOR_LIST.mk_list_false).
            } now rewrite H1, app_nil_r, list2N_pos2list.
Qed.

Lemma listE: forall n, (list2N (mk_list_false n)) = 0.
Proof. intro n.
        induction n; intros; try now cbn.
        cbn. rewrite IHn. easy.
Qed.

Lemma pos2list_mk_list_false: forall p n,
list2N (pos2list p [] ++ mk_list_false n) = N.pos p.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite pos2list_acc. cbn.
          rewrite IHp. easy.
        - cbn. rewrite pos2list_acc. cbn.
          rewrite IHp. easy.
        - cbn. rewrite listE. easy.
Qed. 

Lemma list2N_N2List_s: forall a n,
 ((N.to_nat (N.size a)) <=? n)%nat = true ->
 list2N (N2list a n) = a.
Proof. intro a.
        induction a; intros.
        - cbn. now rewrite listE.
        - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
          + contradict H0. Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.is_pos,
              @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty.
          + assert ((n <=? n0)%nat = false).
            unfold N.size in *.
            Reconstr.rsimple (@Coq.ZArith.Znat.positive_N_nat, @Coq.Arith.PeanoNat.Nat.leb_le,
            @Coq.Arith.Compare_dec.leb_correct_conv) (@Coq.Init.Peano.lt).
            now rewrite H1, pos2list_mk_list_false.
Qed.

Lemma PosSizeNPos: forall p,
(N.pos (Pos.size p) <=? N.pos p) = true.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite N.leb_le in *. lia.
        - cbn. rewrite N.leb_le in *. lia.
        - now cbn.
Qed.

Lemma Nsize_lt: forall a, ((N.size a) <=? a) = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn in *. now rewrite PosSizeNPos.
Qed.

Lemma PosSuc: forall a, (Pos.of_succ_nat a) = Pos.of_nat (S a).
Proof. intro a. Reconstr.reasy (@Coq.PArith.BinPos.Pos.of_nat_succ)
                 Reconstr.Empty. 
Qed.

Lemma NPos_size: forall a, a <> O -> (Pos.to_nat (Pos.size (Pos.of_nat a))) =
  (N.to_nat (N.size (N.of_nat a))) .
Proof. intro a.
        induction a; intros.
        - cbn. easy.
        - cbn. case_eq a; intros.
          + now cbn.
          + rewrite Coq.PArith.BinPos.Pos.succ_of_nat. easy.
            lia.
Qed.

Lemma size_gt: forall a, ((N.to_nat (N.size (N.of_nat a)))%nat <=? a)%nat = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn in *. rewrite PosSuc. rewrite NPos_size.
          specialize (Nsize_lt (N.of_nat (S a))); intro HH.
          assert ( (N.to_nat (N.size (N.of_nat (S a))) <=? N.to_nat (N.of_nat (S a)))%nat = true).
        	Reconstr.rcrush (@Coq.NArith.Nnat.Nat2N.id, @Coq.NArith.Nnat.N2Nat.inj_compare,
            @Coq.NArith.BinNat.N.leb_le,
            @Coq.Arith.Compare_dec.leb_compare) 
           (@Coq.NArith.BinNat.N.le).
          rewrite Nat2N.id in H. easy.
          lia.
Qed.

Lemma list2N_N2List_eq: forall a, list2N (N2list a (N.to_nat a)) = a.
Proof. intros. rewrite list2N_N2List_s. easy.
        specialize (size_gt (N.to_nat a)); intro HH.
        rewrite N2Nat.id in HH. easy.
Qed.

Lemma list2N_mk_list_false: forall n, (list2N (mk_list_false n)) = 0%N.
Proof. intro n.
       induction n; intros. 
       + now cbn.
       + cbn. now rewrite IHn.
Qed.

(* Shift Left *)

Definition shl_one_bit  (a: list bool) : list bool :=
   match a with
     | [] => []
     | _ => false :: removelast a 
   end.

Fixpoint shl_n_bits  (a: list bool) (n: nat): list bool :=
    match n with
      | O => a
      | S n' => shl_n_bits (shl_one_bit a) n'  
    end.

Definition shl_n_bits_a  (a: list bool) (n: nat): list bool :=
  if (n <? length a)%nat then mk_list_false n ++ firstn (length a - n) a
  else mk_list_false (length a).

Definition shl_aux  (a b: list bool): list bool :=
shl_n_bits a (list2nat_be_a b).

Definition bv_shl (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shl_aux a b
  else nil.

Definition bv_shl_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shl_n_bits_a a (list2nat_be_a b)
  else nil.


Lemma length_shl_one_bit : forall a, length (shl_one_bit a) = length a.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl. rewrite <- IHa.
         case_eq a0; easy.
Qed.

Lemma length_shl_n_bits : forall n a, length (shl_n_bits a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - reflexivity.
       - now rewrite (IHn (shl_one_bit a)), length_shl_one_bit.
Qed.

Lemma length_shl_aux : forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (shl_aux a b)).
Proof.
    intros.
    unfold shl_aux. now rewrite length_shl_n_bits.
Qed.

Lemma bv_shl_size n a b : size a = n -> size b = n -> size (bv_shl a b) = n.
Proof.
  unfold bv_shl. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_shl_aux a b (nat_of_N n)).
  now rewrite N2Nat.id.
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
Qed.


Lemma length_shl_n_bits_a: forall n a, length (shl_n_bits_a a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - unfold shl_n_bits_a.
         case_eq a; intros. now cbn. 
         cbn. rewrite firstn_all. easy.
       - unfold shl_n_bits_a.         
         case_eq ( (S n <? length a)%nat); intros. cbn.
         rewrite length_app, length_mk_list_false.
         rewrite length_firstn. apply Nat.ltb_lt in H.
         assert ((Init.Nat.min (length a - S n) (length a))%nat = (length a - S n)%nat).
         {  lia. }
         rewrite H0. lia.
         now rewrite length_mk_list_false.
Qed.

(* here *)
Lemma bv_shl_a_size n a b : size a = n -> size b = n -> size (bv_shl_a a b) = n.
Proof.
  unfold bv_shl_a. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. now rewrite length_shl_n_bits_a.
Qed.


(* firstn n x <= firstn n 1 *)

Lemma eqb_N : forall (a b : N), a = b -> a =? b = true.
Proof.
  intros. induction a; rewrite H; apply N.eqb_refl.
Qed.

Lemma length_eq_firstn_eq : forall (n : nat) (x y : bitvector), 
length x = length y -> (n < length x)%nat -> length (firstn n x) = length (firstn n y).
Proof.
  intros n x y len_xy lt_n_lenx. induction n.
  + easy.
  + destruct x.
    - simpl. destruct y.
      * easy.
      * now contradict len_xy.
    - destruct y.
      * now contradict len_xy.
      * pose proof lt_n_lenx as lt_n_leny. rewrite len_xy in lt_n_leny.
        apply Nat.lt_le_incl in lt_n_lenx. apply Nat.lt_le_incl in lt_n_leny.
        rewrite (@firstn_length_le bool (b :: x) (S n) lt_n_lenx).
        rewrite (@firstn_length_le bool (b0 :: y) (S n) lt_n_leny).
        easy.
Qed.

Lemma prefix_mk_list_true : forall x y : nat, (x < y)%nat -> 
  firstn x (mk_list_true y) = mk_list_true x.
Proof.
  intros x y ltxy. induction x.
  + easy.
  + induction y.
    - easy.
    - simpl. pose proof ltxy as ltxy2. apply Nat.succ_lt_mono in ltxy2. 
      pose proof ltxy2 as ltxSy. apply Nat.lt_lt_succ_r in ltxSy.
      apply IHx in ltxSy. rewrite <- ltxSy.
      rewrite mk_list_true_app. rewrite firstn_app. rewrite length_mk_list_true.
      assert (forall (n m : nat), (n < m)%nat -> Nat.sub n m = O).
      { induction n.
        + easy.
        + induction m.
          - intros. now contradict H.
          - intros. simpl. apply Nat.succ_lt_mono in H. specialize (@IHn m H). apply IHn.
      }
      specialize (@H x y ltxy2). rewrite H. simpl. rewrite app_nil_r. easy.
Qed.

Lemma bv_ule_1_firstn : forall (n : nat) (x : bitvector), 
  (n < length x)%nat ->
  bv_ule (firstn n x) (firstn n (mk_list_true (length x))) = true.
Proof.
  intros. unfold bv_ule. 
  case_eq (size (firstn n x) =? size (firstn n (mk_list_true (length x)))).
  + intros. pose proof bv_ule_1_length as bv_leq_1. unfold ule_list.
    case_eq (ule_list_big_endian (rev (firstn n x)) (rev (firstn n (mk_list_true (length x))))).
    - intros. easy.
    - intros. 
      assert ((n < length x)%nat -> firstn n (mk_list_true (length x)) = mk_list_true n).
      { apply prefix_mk_list_true. }
      assert (ule_list_big_endian (rev (firstn n x)) (rev (firstn n (mk_list_true (length x)))) = true).
      { specialize (@H2 H). rewrite H2. rewrite rev_mk_list_true.
        specialize (@bv_leq_1 (rev (firstn n x))). 
        assert (n = length (rev (firstn n x))). 
        { rewrite length_rev. pose proof firstn_length_le as firstn_length_le.
          specialize (@firstn_length_le bool x n). 
          apply Nat.lt_le_incl in H. specialize (@firstn_length_le H). 
          rewrite firstn_length_le; easy. } 
        rewrite H3 at 2. apply ule_list_big_endian_1. }
      rewrite H3 in H1. now contradict H1.
  + intros size_x_mlt. assert (length_x_mlt : length x = length (mk_list_true (length x))).
    { rewrite length_mk_list_true. easy. } 
    pose proof length_eq_firstn_eq as length_eq_firstn_eq.
    unfold size in size_x_mlt. pose proof eqb_refl as eqb_refl. 
    specialize (@N.eqb_refl (N.of_nat (length (firstn n (mk_list_true (length x)))))).
    specialize (@length_eq_firstn_eq n x (mk_list_true (length x)) length_x_mlt H).
    rewrite length_eq_firstn_eq in size_x_mlt. rewrite N.eqb_refl in size_x_mlt.
    now contradict size_x_mlt.
Qed.

Lemma bv_uleP_1_firstn : forall (n : nat) (x : bitvector), (n < length x)%nat ->
        bv_uleP (firstn n x) (firstn n (mk_list_true (length x))).
Proof.
  intros. unfold bv_uleP. 
  case_eq (size (firstn n x) =? size (firstn n (mk_list_true (length x)))).
  + intros. pose proof bv_uleP_1_length as bv_leq_1. unfold ule_listP.
    unfold ule_list. 
    case_eq (ule_list_big_endian (rev (firstn n x)) (rev (firstn n (mk_list_true (length x))))).
    - intros. easy.
    - intros. 
      assert ((n < length x)%nat -> firstn n (mk_list_true (length x)) = mk_list_true n).
      { apply prefix_mk_list_true. }
      assert (ule_list_big_endian (rev (firstn n x)) (rev (firstn n (mk_list_true (length x)))) = true).
      { specialize (@H2 H). rewrite H2. rewrite rev_mk_list_true.
        specialize (@bv_leq_1 (rev (firstn n x))). 
        assert (n = length (rev (firstn n x))). 
        { rewrite length_rev. pose proof firstn_length_le as firstn_length_le.
          specialize (@firstn_length_le bool x n). 
          apply Nat.lt_le_incl in H. specialize (@firstn_length_le H). 
          rewrite firstn_length_le; easy. } 
        rewrite H3 at 2. apply ule_list_big_endian_1. }
      rewrite H3 in H1. now contradict H1.
  + intros size_x_mlt. assert (length_x_mlt : length x = length (mk_list_true (length x))).
    { rewrite length_mk_list_true. easy. } 
    pose proof length_eq_firstn_eq as length_eq_firstn_eq.
    unfold size in size_x_mlt. pose proof eqb_refl as eqb_refl. 
    specialize (@N.eqb_refl (N.of_nat (length (firstn n (mk_list_true (length x)))))).
    specialize (@length_eq_firstn_eq n x (mk_list_true (length x)) length_x_mlt H).
    rewrite length_eq_firstn_eq in size_x_mlt. rewrite N.eqb_refl in size_x_mlt.
    now contradict size_x_mlt.
Qed.


(* x <= y -> z ++ x <= z ++ y *)
Lemma preappend_length : forall (x y z : bitvector), length x = length y ->
            length (z ++ x) = length (z ++ y).
Proof.
  intros. induction z.
  + easy.
  + simpl. pose proof eq_S. specialize (@H0 (length (z ++ x)) (length (z ++ y))).
    apply H0 in IHz. apply IHz.
Qed.

Lemma ule_list_big_endian_cons_nil : forall (b : bool) (l : list bool),
  ule_list_big_endian (b :: l) [] = false.
Proof.
  intros. destruct l; easy.
Qed.

Lemma cons_disjunct_ule_list_big_endian : forall (h1 h2 : bool) (t1 t2 : list bool),
  (orb 
    (andb (negb h1) h2) 
    (andb (eqb h1 h2) (ule_list_big_endian t1 t2))) = true ->
  ule_list_big_endian (h1 :: t1) (h2 :: t2) = true.
Proof.
  intros. rewrite orb_true_iff, andb_true_iff in H. destruct H.
  + unfold ule_list_big_endian. simpl. fold ule_list_big_endian.
    destruct t1.
    - destruct t2; rewrite orb_true_iff; right; rewrite andb_true_iff; apply H.
    - rewrite orb_true_iff; right; rewrite andb_true_iff; apply H.
  + unfold ule_list_big_endian. simpl. fold ule_list_big_endian.
    destruct t1.
    - rewrite andb_true_iff in H.  destruct H. destruct t2.
      * rewrite orb_true_iff. left. rewrite andb_true_iff. split; easy.
      * now contradict H0.
    - rewrite orb_true_iff. left. apply H.
Qed.

Lemma ule_list_big_endian_cons_disjunct : forall (h1 h2 : bool) (t1 t2 : list bool),
  ule_list_big_endian (h1 :: t1) (h2 :: t2) = true -> 
  (orb 
    (andb (negb h1) h2) 
    (andb (eqb h1 h2) (ule_list_big_endian t1 t2))) = true.
Proof.
  intros. unfold ule_list_big_endian in H. simpl in H.
  fold ule_list_big_endian in H. destruct t1 in *.
  + destruct t2 in *.
    - rewrite orb_true_iff in *. rewrite andb_true_iff in *. 
      destruct H.
      * right. rewrite andb_true_iff. split.
        { apply H. }
        { easy. }
      * left. rewrite andb_true_iff in H. apply H.
    - rewrite orb_true_iff, andb_true_iff in *. destruct H.
      * destruct H. now contradict H0.
      * left. rewrite andb_true_iff in H. apply H.
  + rewrite orb_true_iff, andb_true_iff in *. destruct H.
    - destruct H. right. rewrite andb_true_iff. split.
      * apply H.
      * apply H0.
    - left. rewrite andb_true_iff in H. apply H.
Qed.    

Lemma ule_list_big_endian_app : forall (x y z : bitvector), 
  ule_list_big_endian x y = true -> ule_list_big_endian (x ++ z) (y ++ z) = true.
Proof.
  induction x, y; intros.
  + simpl. apply ule_list_big_endian_refl.
  + now contradict H.
  + pose proof (@ule_list_big_endian_cons_nil a x). rewrite H0 in H.
    now contradict H.
  + pose proof (@ule_list_big_endian_cons_disjunct a b x y H).
    rewrite orb_true_iff, andb_true_iff in H0. destruct H0.
    - rewrite <- app_comm_cons. rewrite <- app_comm_cons.
      apply cons_disjunct_ule_list_big_endian.
      rewrite orb_true_iff. left. rewrite andb_true_iff.
      apply H0.
    - rewrite andb_true_iff in H0. destruct H0. 
      specialize (@IHx y z H1). rewrite <- app_comm_cons.
      rewrite <- app_comm_cons. apply cons_disjunct_ule_list_big_endian.
      rewrite orb_true_iff. right. rewrite andb_true_iff. split.
      * apply H0.
      * apply IHx.
Qed.

Lemma ule_list_big_endian_rev_app : forall (x y z : bitvector), 
      ule_list_big_endian (rev x) (rev y) = true -> 
      ule_list_big_endian (rev (z ++ x)) (rev (z ++ y)) = true.
Proof.
  intros x y z ule_rx_ry. rewrite rev_app_distr. rewrite rev_app_distr.
  apply ule_list_big_endian_app. apply ule_rx_ry.
Qed.

Lemma bv_ule_pre_append : forall (x y z : bitvector), bv_ule x y  = true ->
              bv_ule (z ++ x) (z ++ y) = true.
Proof.
  intros. unfold bv_ule in *. case_eq (size x =? size y).
  + intros. rewrite H0 in H. apply Neqb_ok in H0.
    unfold size in H0. apply Nat2N.inj in H0.
    pose proof (@preappend_length x y z). apply H1 in H0. rewrite <- Nat2N.id in H0 at 1.
    rewrite <- Nat2N.id in H0. apply N2Nat.inj in H0.
    unfold size. apply eqb_N in H0. rewrite H0. unfold ule_list in *.
    assert (forall (x y z : bitvector), 
      ule_list_big_endian (rev x) (rev y) = true -> 
      ule_list_big_endian (rev (z ++ x)) (rev (z ++ y)) = true).
    { apply ule_list_big_endian_rev_app. }
    specialize (@H2 x y z). case_eq (ule_list_big_endian (rev x) (rev y)).
    - intros. apply H2 in H3. rewrite H3. easy.
    - intros. rewrite H3 in H. now contradict H.
  + intros. rewrite H0 in H. now contradict H.
Qed.

Lemma bv_uleP_pre_append : forall (x y z : bitvector), bv_uleP x y ->
              bv_uleP (z ++ x) (z ++ y).
Proof.
  intros. unfold bv_uleP in *. case_eq (size x =? size y).
  + intros. rewrite H0 in H. apply Neqb_ok in H0.
    unfold size in H0. apply Nat2N.inj in H0.
    pose proof (@preappend_length x y z). apply H1 in H0. rewrite <- Nat2N.id in H0 at 1.
    rewrite <- Nat2N.id in H0. apply N2Nat.inj in H0.
    unfold size. apply eqb_N in H0. rewrite H0. unfold ule_listP in *.
    unfold ule_list in *.
    assert (forall (x y z : bitvector), 
      ule_list_big_endian (rev x) (rev y) = true -> 
      ule_list_big_endian (rev (z ++ x)) (rev (z ++ y)) = true).
    { apply ule_list_big_endian_rev_app. }
    specialize (@H2 x y z). case_eq (ule_list_big_endian (rev x) (rev y)).
    - intros. apply H2 in H3. rewrite H3. easy.
    - intros. rewrite H3 in H. now contradict H.
  + intros. rewrite H0 in H. now contradict H.
Qed.


(* x <= y -> x ++ z <= y ++ z *)
Lemma postappend_length : forall (x y z : bitvector), length x = length y ->
            length (x ++ z) = length (y ++ z).
Proof.
  induction x, y.
  + easy.
  + intros. now contradict H. 
  + intros. now contradict H.
  + intros. specialize (@IHx y z). simpl in H. apply eq_add_S in H.
    specialize (@IHx H). simpl. apply eq_S. apply IHx. 
Qed.

Lemma app_ule_list_big_endian : forall (x y z : bitvector), 
  ule_list_big_endian x y = true -> ule_list_big_endian (z ++ x) (z ++ y) = true.
Proof.
  induction z; intros Hxy.
  + easy. 
  + specialize (@IHz Hxy). rewrite <- app_comm_cons. rewrite <- app_comm_cons.
    apply cons_disjunct_ule_list_big_endian. 
    rewrite orb_true_iff. right. rewrite andb_true_iff. split.
    - apply eqb_reflx.
    - apply IHz.
Qed.

Lemma rev_app_ule_list_big_endian : forall (x y z : bitvector),
  ule_list_big_endian (rev x) (rev y) = true -> 
  ule_list_big_endian (rev (x ++ z)) (rev (y ++ z)) = true.
Proof.
  intros  x y z ule_rx_ry. rewrite rev_app_distr. rewrite rev_app_distr.
  apply app_ule_list_big_endian. apply ule_rx_ry.
Qed.

Lemma bv_uleP_post_append : forall (x y z : bitvector), bv_uleP x y -> 
  bv_uleP (x ++ z) (y ++ z).
Proof.
  intros x y z Hlexy. unfold bv_uleP in *. case_eq (size x =? size y).
  + intros Hxy. rewrite Hxy in Hlexy. apply Neqb_ok in Hxy.
    unfold size in Hxy. apply Nat2N.inj in Hxy.
    pose proof (@postappend_length x y z) as app_len. apply app_len in Hxy.
    rewrite <- Nat2N.id in Hxy at 1. rewrite <- Nat2N.id in Hxy.
    apply N2Nat.inj in Hxy. unfold size. apply eqb_N in Hxy. rewrite Hxy.
    unfold ule_listP in *. unfold ule_list in *.
    pose proof (@rev_app_ule_list_big_endian x y z) as rev_app.
    case_eq (ule_list_big_endian (rev x) (rev y)).
    - intros. apply rev_app in H. rewrite H. easy.
    - intros. rewrite H in Hlexy. now contradict Hlexy.
  + intros Hxy. rewrite Hxy in Hlexy. now contradict Hlexy.
Qed.


(* x << s <= 1 << s *)

Lemma bv_shl_n_bits_a_1_leq : forall (n : N) (x s : bitvector),
  size x = n -> size s = n -> 
  bv_ule (shl_n_bits_a x (list2nat_be_a s))
         (shl_n_bits_a (mk_list_true (length s)) (list2nat_be_a s)) = true.
Proof.
  intros n x s Hx Hs. assert (length x = length (mk_list_true (length s))).
    { pose proof Hx as Hxx. pose proof Hs as Hss. unfold size in Hxx, Hss.
      rewrite <- N2Nat.id in Hxx. apply Nat2N.inj in Hxx.
      rewrite <- N2Nat.id in Hss. apply Nat2N.inj in Hss.
      rewrite Hxx, Hss. rewrite length_mk_list_true. easy. }
  unfold shl_n_bits_a. rewrite <- H.
  case_eq ((list2nat_be_a s <? length x)%nat).
  + intros. assert (length s = length x). 
      { pose proof Hx as Hxx. pose proof Hs as Hss.  unfold size in Hxx, Hss.
        rewrite <- N2Nat.id in Hxx. apply Nat2N.inj in Hxx. 
        rewrite <- N2Nat.id in Hss. apply Nat2N.inj in Hss. 
        rewrite <- Hxx in Hss. apply Hss. }
    induction (list2nat_be_a s).
    - simpl. rewrite Nat.sub_0_r. rewrite firstn_all.
      rewrite H. rewrite firstn_all. 
      rewrite H1. apply bv_ule_1_length. 
    - rewrite Nat.ltb_lt in H0.
      pose proof Nat.lt_succ_l as lt_succ_l.
      specialize (@lt_succ_l n0 (length x) H0). apply Nat.ltb_lt in lt_succ_l.
      apply IHn0 in lt_succ_l.
      assert (bv_ule_1_firstn : forall (n : nat) (x : bitvector), 
        (n < length x)%nat ->
        bv_ule (firstn n x) (firstn n (mk_list_true (length x))) = true).
      { apply bv_ule_1_firstn. }
      rewrite H1.
      specialize (@bv_ule_1_firstn ((length x) - (S n0))%nat x).
      assert (bv_ule_pre_append : forall (x y z : bitvector), bv_ule x y = true ->
              bv_ule (z ++ x) (z ++ y) = true).
      { apply bv_ule_pre_append. }
      specialize (@bv_ule_pre_append (firstn (length x - S n0) x)
      (firstn (length x - S n0) (mk_list_true (length x))) (mk_list_false (S n0))).
      apply bv_ule_pre_append. apply bv_ule_1_firstn.
      assert (forall m n : nat, (S m < n)%nat -> (n - (S m) < n)%nat). 
      { intros. apply Nat.sub_lt. apply Nat.lt_le_incl in H2. 
        apply H2. apply Nat.lt_0_succ. }
      specialize (@H2 n0 (length x) H0). apply H2.
  + intros. apply bv_ule_refl.
Qed.

Lemma bv_shl_a_1_leq : forall (n : N) (x s : bitvector), 
  size x = n -> size s = n -> 
  bv_ule (bv_shl_a x s) (bv_shl_a (bv_not (zeros (size s))) s) = true.
Proof.
  intros n x s Hx Hs. unfold zeros. unfold size. rewrite Nat2N.id.
  rewrite bv_not_false_true. unfold bv_shl_a. rewrite Hx, Hs.
  unfold size. rewrite length_mk_list_true. pose proof Hs as Hss.
  unfold size in Hss. rewrite Hss.
  pose proof (@N.eqb_refl n). rewrite H.
  apply (@bv_shl_n_bits_a_1_leq n x s Hx Hs).
Qed.


(* x <= y <-> (x < y \/ x = y) *)
Lemma ult_list_big_endian_cons : forall (b : bool) (b1 b2 : list bool),
  ult_list_big_endian b1 b2 = true -> 
  ult_list_big_endian (b :: b1) (b :: b2) = true.
Proof.
  intros. unfold ult_list_big_endian. case b1 in *.
  + case b2 in *; easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * rewrite eqb_true_iff. easy.
      * fold ult_list_big_endian. apply H.
Qed.

Lemma ule_list_big_endian_implies_ult_list_big_endian_or_eq : forall (x y : list bool), 
  ule_list_big_endian x y = true -> ult_list_big_endian x y = true \/ (x = y).
Proof.
  induction x.
  + intros y H. induction y.
    - now right.
    - easy.
  + intros y H. induction y.
    - rewrite ule_list_big_endian_cons_nil in H. easy.
    - case x in *.
      * case y in *.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           destruct H.
           *** rewrite eqb_true_iff in H. right. destruct H. now rewrite H.
           *** rewrite andb_true_iff, negb_true_iff in H. destruct H as (Ha, Ha0).
               rewrite Ha, Ha0. now left.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           rewrite andb_true_iff, negb_true_iff in H. destruct H.
           *** destruct H as (H, contr). easy.
           *** destruct H as (Ha, Ha0). rewrite Ha, Ha0.
               now left.
      * case y in *.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           rewrite andb_true_iff, negb_true_iff in H. destruct H.
           *** rewrite eqb_true_iff in H. destruct H. case x in *; easy.
           *** destruct H as (Ha, Ha0). rewrite Ha, Ha0. now left.
        ** specialize (@IHx (b0 :: y)). 
           assert (Hunfolded : (a = false /\ a0 = true) \/ 
                   (a = a0 /\ ule_list_big_endian (b :: x) (b0 :: y) = true)).
           { unfold ule_list_big_endian in H. fold ule_list_big_endian in H.
             rewrite orb_true_iff, andb_true_iff in H. destruct H.
             + right. rewrite eqb_true_iff in H. destruct H. split.
               * apply H.
               * apply H0.
             + rewrite andb_true_iff, negb_true_iff in H. left. apply H. }
           destruct Hunfolded.
           *** destruct H0 as (Ha, Ha0). rewrite Ha, Ha0. now left.
           *** case a in *.
               ++ case a0 in *.
                  +++ destruct H0. specialize (@IHx H1). destruct IHx.
                      -- left. apply (@ult_list_big_endian_cons true). apply H2.
                      -- right. now rewrite H2.
                  +++ destruct H0. now contradict H0.
               ++ case a0 in *.
                  +++ left. easy.
                  +++ destruct H0. specialize (@IHx H1). destruct IHx.
                      -- left. apply (@ult_list_big_endian_cons false). apply H2.
                      -- right. now rewrite H2.
Qed.

Lemma ult_list_big_endian_or_eq_implies_ule_list_big_endian : forall (x y : list bool), 
  ult_list_big_endian x y = true \/ (x = y) -> ule_list_big_endian x y = true.
Proof.
  induction x.
  + intros y H. induction y.
    - easy.
    - destruct H; easy.
  + intros y H. induction y.
    - destruct H; case a in *; case x in *; easy.
    - destruct H.
      * apply ult_list_big_endian_implies_ule. apply H.
      * rewrite H. apply ule_list_big_endian_refl.
Qed.

Lemma bv_ule_eq : forall (x y : bitvector), bv_ule x y = true <->
  (bv_ult x y = true) \/ (x = y).
Proof.
  intros x y. 
  assert (eq : x = y <-> (rev x) = (rev y)).
  { split.
    + apply rev_func.
    + apply rev_inj.
  }
  split.
  + rewrite eq. unfold bv_ule, bv_ult. 
    case_eq (size x =? size y); intros case. 
    - unfold ule_list, ult_list. intros H. induction (rev x).
      * induction (rev y).
        ++ now right.
        ++ easy.
      * induction (rev y).
        ++ apply ule_list_big_endian_implies_ult_list_big_endian_or_eq. apply H.
        ++ unfold ule_list in H. unfold ult_list. 
           apply ule_list_big_endian_implies_ult_list_big_endian_or_eq. apply H.
    - intros. now contradict H.
  + rewrite eq. unfold bv_ule, bv_ult.
    case_eq (size x =? size y); intros case. 
    - unfold ule_list, ult_list. intros H. induction (rev x).
      * induction (rev y).
        ++ easy.
        ++ destruct H; easy.
      * induction (rev y);
        apply ult_list_big_endian_or_eq_implies_ule_list_big_endian; apply H.
    - intros. destruct H. 
      * now contradict H.
      * rewrite <- eq in H. rewrite H in case. rewrite N.eqb_refl in case.
        easy.
Qed.


(* size x = size y -> x !> y -> x <= y *)

Lemma ule_list_big_endian_cons : forall (b : bool) (b1 b2 : list bool),
  ule_list_big_endian b1 b2 = true -> 
  ule_list_big_endian (b :: b1) (b :: b2) = true.
Proof.
  intros. unfold ule_list_big_endian. case b1 in *.
  + case b2 in *.
    - rewrite orb_true_iff, andb_true_iff, eqb_true_iff. now left.
    - easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * rewrite eqb_true_iff. easy.
      * fold ule_list_big_endian. apply H.
Qed.

Lemma not_ugt_list_big_endian_implies_ule_list_big_endian : forall (x y : list bool), 
  size x = size y -> ugt_list_big_endian x y = false -> ule_list_big_endian x y = true.
Proof.
  induction x.
  + intros y. case y.
    - easy.
    - intros b l Hxy H. now contradict Hxy.
  + intros y Hxy H. case y in *. 
    - now contradict Hxy.
    - case x in *.
      * case y in *.
        ++ simpl in H. rewrite andb_false_iff, negb_false_iff in H.
           destruct H.
           -- rewrite H. case b; easy.
           -- rewrite H. case a; easy.
        ++ assert (size [a] <> size (b :: b0 :: y)). 
           { unfold size. rewrite <- N2Nat.inj_iff. 
             rewrite Nat2N.id. rewrite Nat2N.id. easy. } 
           easy.
      * case y in *.
        ++ assert (size (a :: b0 :: x) <> size [b]).
           { unfold size. rewrite <- N2Nat.inj_iff. 
             rewrite Nat2N.id. rewrite Nat2N.id. easy. } 
           easy.
        ++ unfold ugt_list_big_endian in H.
           fold ugt_list_big_endian in H. 
           rewrite orb_false_iff, andb_false_iff in H.
           destruct H. rewrite andb_false_iff, negb_false_iff in H0.
           destruct H0.
           -- rewrite H0. destruct H.
              ** rewrite H0 in H. rewrite eqb_false_iff in H.
                 apply not_eq_sym in H. apply not_false_is_true in H. 
                 rewrite H. easy.
              ** case b.
                 +++ easy.
                 +++ assert (size (b0 :: x) = size (b1 :: y)).
                     { unfold size in *. rewrite <- N2Nat.inj_iff in Hxy. 
                       rewrite Nat2N.id in Hxy. rewrite Nat2N.id in Hxy. 
                       simpl in Hxy. apply Nat.succ_inj in Hxy. 
                       rewrite <- N2Nat.inj_iff. rewrite Nat2N.id. 
                       rewrite Nat2N.id. simpl. rewrite Hxy. easy. }
                      specialize (@IHx (b1 :: y) H1 H). 
                      apply ule_list_big_endian_cons. apply IHx.
           -- rewrite H0. destruct H.
              ** rewrite eqb_false_iff, H0 in H. 
                 apply not_true_is_false in H. rewrite H. easy.
              ** case a.
                 +++ assert (size (b0 :: x) = size (b1 :: y)).
                     { unfold size in *. rewrite <- N2Nat.inj_iff in Hxy. 
                       rewrite Nat2N.id in Hxy. rewrite Nat2N.id in Hxy. 
                       simpl in Hxy. apply Nat.succ_inj in Hxy. 
                       rewrite <- N2Nat.inj_iff. rewrite Nat2N.id. 
                       rewrite Nat2N.id. simpl. rewrite Hxy. easy. }
                     specialize (@IHx (b1 :: y) H1 H).
                     apply ule_list_big_endian_cons. apply IHx.
                 +++ easy.
Qed.

Lemma not_bv_ugt_implies_bv_ule : forall (x y : bitvector), 
  size x = size y -> (bv_ugt x y = false) -> bv_ule x y = true.
Proof.
  intros x y Hsize H. unfold bv_ugt, bv_ule in *.
  case_eq (size x =? size y); intros Hxy.
  - rewrite Hxy in H. unfold size in Hxy. 
    rewrite <- length_rev in Hxy.
    rewrite <- (@length_rev bool y) in Hxy.
    unfold ugt_list, ule_list in *. induction (rev x).
    * case (rev y) in *.
      ++ easy.
      ++ simpl in *. apply Hxy. 
    * case (rev y) in *.
      ++ simpl in *. case l in *; apply Hxy.
      ++ apply Neqb_ok in Hxy. 
         apply not_ugt_list_big_endian_implies_ule_list_big_endian. 
         apply Hxy. apply H.
  - apply N.eqb_neq in Hxy. easy. 
Qed.


(* b1 = b2 -> !(b1 > b2) *)

Lemma ugt_list_big_endian_not_refl : forall (b : list bool),
 ugt_list_big_endian b b = false.
Proof.
  intros. induction b.
  + easy.
  + simpl. case b in *.
    - apply andb_negb_r.
    - rewrite orb_false_iff, andb_false_iff. split.
      * now right.
      * apply andb_negb_r.
Qed.

Lemma eq_not_ugt_list_big_endian : forall (b1 b2 : list bool),
  b1 = b2 -> ugt_list_big_endian b1 b2 = false.
Proof.
  induction b1.
  + intros. case b2; easy.
  + intros b2 H. induction b2.
    - easy.
    - rewrite H. apply ugt_list_big_endian_not_refl. 
Qed.

Lemma eq_not_bv_ugt : forall (b1 b2 : bitvector),
  b1 = b2 -> bv_ugt b1 b2 = false.
Proof.
  intros b1 b2 H. unfold bv_ugt.
  case_eq (size b1 =? size b2); intros size.
  + unfold ugt_list. apply rev_func in H.
    apply eq_not_ugt_list_big_endian. apply H.
  + easy.
Qed.



(* x <= y -> x !> y *)

Lemma bv_ule_implies_not_bv_ugt : forall (x y : bitvector), 
  bv_ule x y = true -> (bv_ugt x y = false).
Proof.
  intros x y. intros Hule. rewrite bv_ule_eq in Hule. 
  destruct Hule.
  - apply bv_ult_not_bv_ugt. apply H.
  - apply eq_not_bv_ugt. apply H.
Qed.


(* unsigned greater than or equal to *)

Fixpoint uge_list_big_endian (x y : list bool) :=
  match x, y with
  | nil, nil => true
  | nil, _ => false 
  | _, nil => false 
  | xi :: x', yi :: y' =>
    orb (andb (Bool.eqb xi yi) (uge_list_big_endian x' y'))
          (andb xi (negb yi))
  end. 

(* bool output *)
Definition uge_list (x y: list bool) :=
  (uge_list_big_endian (List.rev x) (List.rev y)).

Definition bv_uge (a b : bitvector) : bool :=
  if @size a =? @size b then uge_list a b else false.

(* Prop output *)
Definition uge_listP (x y: list bool) :=
  if uge_list x y then True else False.

Definition bv_ugeP (a b : bitvector) : Prop :=
  if @size a =? @size b then uge_listP a b else False.


(* Equivalence of boolean and Prop comparisons *)
Lemma bv_uge_B2P: forall x y, bv_uge x y = true <-> bv_ugeP x y.
Proof.
  intros. split; intros; unfold bv_uge, bv_ugeP in *.
  + case_eq (size x =? size y); intros.
    - rewrite H0 in H. unfold uge_listP. now rewrite H.
    - rewrite H0 in H. now contradict H.
  + unfold uge_listP in *. case_eq (size x =? size y); intros.
    - rewrite H0 in H. case_eq (uge_list x y); intros.
      * easy.
      * rewrite H1 in H. now contradict H.
    - rewrite H0 in H. now contradict H.
Qed.


(* a <=u b -> b >=u a *)
Lemma ule_list_big_endian_uge_list_big_endian : forall x y, 
  ule_list_big_endian x y = true -> uge_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. intros y. case y; easy.
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl.
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. left. now rewrite eqb_true_iff. }
        { destruct H. apply negb_true_iff in H. subst. right. now rewrite negb_true_iff. }
Qed. 

Lemma ule_list_uge_list : forall x y, ule_list x y = true -> uge_list y x = true.
Proof.
  intros x y. unfold ule_list. intros. 
  apply ule_list_big_endian_uge_list_big_endian in H.
  unfold uge_list. apply H.
Qed.

Lemma bv_ule_bv_uge : forall x y, bv_ule x y = true -> bv_uge y x = true.
Proof.
  intros x y. unfold bv_ule.
  case_eq (size x =? size y); intros.
  - apply ule_list_uge_list in H0. unfold bv_uge. rewrite (@N.eqb_sym (size x) (size y)) in H. 
    rewrite H. apply H0. 
  - now contradict H0. 
Qed.

Lemma ule_listP_uge_listP : forall x y, ule_listP x y -> uge_listP y x.
Proof.
  unfold ule_listP.
  intros. unfold ule_list in H.
  case_eq (ule_list_big_endian (List.rev x) (List.rev y)).
  + intros. unfold uge_listP. unfold uge_list. 
    apply (@ule_list_big_endian_uge_list_big_endian (List.rev x) (List.rev y)) in H0.
    rewrite H0. easy.
  + intros. rewrite H0 in H. now contradict H.
Qed.

Lemma bv_uleP_bv_ugeP : forall x y, bv_uleP x y -> (bv_ugeP y x).
Proof.
  intros x y. unfold bv_uleP, bv_ugeP.
  rewrite (@N.eqb_sym (size y) (size x)).
  case_eq (size x =? size y); intros.
  - apply ule_listP_uge_listP. apply H0.
  - apply H0.
Qed.

(*a >=u b -> b <=u a *)
Lemma uge_list_big_endian_ule_list_big_endian : forall x y,
  uge_list_big_endian x y = true -> ule_list_big_endian y x = true.
Proof.
  intros x. induction x.
  + simpl. intros y. case y;easy. 
  + intros y. case y.
    - intros. case a; case x in *; simpl in H; now contradict H.
    - intros b l. simpl. 
      specialize (IHx l). case x in *.
      * simpl. case l in *.
        { case a; case b; simpl; easy. }
        { case a; case b; simpl; easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. apply IHx in H0. apply Bool.eqb_prop in H.
          rewrite H. rewrite H0. left. now rewrite eqb_true_iff. }
        { destruct H. apply negb_true_iff in H0. subst. now right. }
Qed. 

Lemma uge_list_ule_list : forall x y, uge_list x y = true -> ule_list y x = true.
Proof.
  intros x y. unfold uge_list. intros. 
  apply uge_list_big_endian_ule_list_big_endian in H.
  unfold ule_list. apply H.
Qed.

Lemma bv_uge_bv_ule : forall x y, bv_uge x y = true -> bv_ule y x = true.
Proof.
  intros x y. unfold bv_uge.
  case_eq (size x =? size y); intros.
  - apply uge_list_ule_list in H0. unfold bv_ule. rewrite (@N.eqb_sym (size x) (size y)) in H. 
    rewrite H. apply H0. 
  - now contradict H0. 
Qed.

Lemma uge_listP_ule_listP : forall x y, uge_listP x y -> ule_listP y x.
Proof.
  unfold uge_listP.
  intros. unfold uge_list in H.
  case_eq (uge_list_big_endian (List.rev x) (List.rev y)).
  + intros. unfold ule_listP. unfold ule_list. 
    apply (@uge_list_big_endian_ule_list_big_endian (List.rev x) (List.rev y)) in H0.
    rewrite H0. easy.
  + intros. rewrite H0 in H. now contradict H.
Qed.
 
Lemma bv_ugeP_bv_uleP : forall x y, bv_ugeP x y -> (bv_uleP y x).
Proof.
  intros x y. unfold bv_ugeP, bv_uleP.
  rewrite (@N.eqb_sym (size y) (size x)).
  case_eq (size x =? size y); intros.
  - apply uge_listP_ule_listP. apply H0.
  - apply H0.
Qed.


(* x > y => x >= y *)
Lemma ugt_list_big_endian_implies_uge : forall x y,
  ugt_list_big_endian x y = true -> uge_list_big_endian x y = true.
Proof.
  intros x. induction x as [| h t].
  + simpl. easy.
  + intros y. case y.
    - case h; case t; easy.
    - intros b l. simpl. 
      case t in *.
      * simpl. case l in *.
        { case h; case b; simpl; easy. }
        { easy. }
      * rewrite !orb_true_iff, !andb_true_iff. intro. destruct H.
        { destruct H. specialize (@IHt l H0). rewrite IHt. apply Bool.eqb_prop in H.
          rewrite H in *. left. split.
          + apply eqb_reflx.
          + easy. }
        { destruct H. rewrite negb_true_iff in *. subst. 
          right. easy. }
Qed.


(* forall b : BV, 1 >= b *)

Lemma ones_bv_uge_size : forall (x : bitvector), 
  bv_uge (mk_list_true (N.to_nat (size x))) x = true.
Proof.
  intros x. pose proof (@bv_ule_1_size x). now apply bv_ule_bv_uge in H.
Qed.

Lemma ones_bv_uge_length : forall (x : bitvector),
  bv_uge (mk_list_true (length x)) x = true.
Proof.
  intros x. pose proof (@bv_ule_1_length x). now apply bv_ule_bv_uge in H.
Qed.

Lemma ones_bv_ugeP_size : forall (x : bitvector), bv_ugeP (mk_list_true (N.to_nat (size x))) x.
Proof.
  intros x. pose proof (@bv_uleP_1_size x). now apply bv_uleP_bv_ugeP in H.
Qed.

Lemma ones_bv_ugeP_length : forall (x : bitvector),
  bv_ugeP (mk_list_true (length x)) x.
Proof.
  intros x. pose proof (@bv_uleP_1_length x). now apply bv_uleP_bv_ugeP in H.
Qed.


(* x >= x *)

Lemma uge_list_big_endian_refl : forall (b : list bool), 
  uge_list_big_endian b b = true.
Proof.
  induction b.
  + easy.
  + case a; simpl; rewrite IHb; case b; easy.
Qed.

Lemma bv_ugeP_refl : forall (b : bitvector), bv_ugeP b b.
Proof.
  intros b. pose proof (@bv_uleP_refl b). now apply bv_uleP_bv_ugeP in H.
Qed.

Lemma bv_uge_refl : forall (b : bitvector), bv_uge b b = true.
Proof.
  intros b. pose proof (@bv_ule_refl b). now apply bv_ule_bv_uge in H.
Qed.


Lemma uge_list_big_endian_cons_nil : forall (b : bool) (l : list bool),
  uge_list_big_endian (b :: l) [] = false.
Proof.
  intros. destruct l; easy.
Qed.


(* x >= y <-> (x > y \/ x = y) *)

Lemma ugt_list_big_endian_cons : forall (b : bool) (b1 b2 : list bool),
  ugt_list_big_endian b1 b2 = true -> 
  ugt_list_big_endian (b :: b1) (b :: b2) = true.
Proof.
  intros. unfold ugt_list_big_endian. case b1 in *.
  + case b2 in *; easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * rewrite eqb_true_iff. easy.
      * fold ugt_list_big_endian. apply H.
Qed.

Lemma uge_list_big_endian_implies_ugt_list_big_endian_or_eq : forall (x y : list bool), 
  uge_list_big_endian x y = true -> ugt_list_big_endian x y = true \/ (x = y).
Proof.
  induction x.
  + intros y H. induction y.
    - now right.
    - easy.
  + intros y H. induction y.
    - rewrite uge_list_big_endian_cons_nil in H. easy.
    - case x in *.
      * case y in *.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           destruct H.
           *** rewrite eqb_true_iff in H. right. destruct H. now rewrite H.
           *** rewrite andb_true_iff, negb_true_iff in H. destruct H as (Ha, Ha0).
               rewrite Ha, Ha0. now left.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           rewrite andb_true_iff, negb_true_iff in H. destruct H.
           *** destruct H as (H, contr). easy.
           *** destruct H as (Ha, Ha0). rewrite Ha, Ha0.
               now left.
      * case y in *.
        ** simpl in H. rewrite orb_true_iff, andb_true_iff in H.
           rewrite andb_true_iff, negb_true_iff in H. destruct H.
           *** rewrite eqb_true_iff in H. destruct H. case x in *; easy.
           *** destruct H as (Ha, Ha0). rewrite Ha, Ha0. now left.
        ** specialize (@IHx (b0 :: y)). 
           assert (Hunfolded : (a = true /\ a0 = false) \/ 
                   (a = a0 /\ uge_list_big_endian (b :: x) (b0 :: y) = true)).
           { unfold uge_list_big_endian in H. fold uge_list_big_endian in H.
             rewrite orb_true_iff, andb_true_iff in H. destruct H.
             + right. rewrite eqb_true_iff in H. destruct H. split.
               * apply H.
               * apply H0.
             + rewrite andb_true_iff, negb_true_iff in H. left. apply H. }
           destruct Hunfolded.
           *** destruct H0 as (Ha, Ha0). rewrite Ha, Ha0. now left.
           *** case a in *.
               ++ case a0 in *.
                  +++ destruct H0. specialize (@IHx H1). destruct IHx.
                      -- left. apply (@ugt_list_big_endian_cons true). apply H2.
                      -- right. now rewrite H2.
                  +++ destruct H0. now contradict H0.
               ++ case a0 in *.
                  +++ left. easy.
                  +++ destruct H0. specialize (@IHx H1). destruct IHx.
                      -- left. apply (@ugt_list_big_endian_cons false). apply H2.
                      -- right. now rewrite H2.
Qed.

Lemma ugt_list_big_endian_or_eq_implies_uge_list_big_endian : forall (x y : list bool), 
  ugt_list_big_endian x y = true \/ (x = y) -> uge_list_big_endian x y = true.
Proof.
  induction x.
  + intros y H. induction y.
    - easy.
    - destruct H; easy.
  + intros y H. induction y.
    - destruct H; case a in *; case x in *; easy.
    - destruct H.
      * apply ugt_list_big_endian_implies_uge. apply H.
      * rewrite H. apply uge_list_big_endian_refl.
Qed.

Lemma bv_uge_eq : forall (x y : bitvector), bv_uge x y = true <->
  (bv_ugt x y = true) \/ (x = y).
Proof.
  intros x y. 
  assert (eq : x = y <-> (rev x) = (rev y)).
  { split.
    + apply rev_func.
    + apply rev_inj.
  }
  split.
  + rewrite eq. unfold bv_uge, bv_ugt. 
    case_eq (size x =? size y); intros case. 
    - unfold uge_list, ugt_list. intros H. induction (rev x).
      * induction (rev y).
        ++ now right.
        ++ easy.
      * induction (rev y).
        ++ apply uge_list_big_endian_implies_ugt_list_big_endian_or_eq. apply H.
        ++ unfold uge_list in H. unfold ugt_list. 
           apply uge_list_big_endian_implies_ugt_list_big_endian_or_eq. apply H.
    - intros. now contradict H.
  + rewrite eq. unfold bv_uge, bv_ugt.
    case_eq (size x =? size y); intros case. 
    - unfold uge_list, ugt_list. intros H. induction (rev x).
      * induction (rev y).
        ++ easy.
        ++ destruct H; easy.
      * induction (rev y);
        apply ugt_list_big_endian_or_eq_implies_uge_list_big_endian; apply H.
    - intros. destruct H. 
      * now contradict H.
      * rewrite <- eq in H. rewrite H in case. rewrite N.eqb_refl in case.
        easy.
Qed.


(* size x = size y -> x !< y -> x >= y *)
Lemma uge_list_big_endian_cons : forall (b : bool) (b1 b2 : list bool),
  uge_list_big_endian b1 b2 = true -> 
  uge_list_big_endian (b :: b1) (b :: b2) = true.
Proof.
  intros. unfold uge_list_big_endian. case b1 in *.
  + case b2 in *.
    - rewrite orb_true_iff, andb_true_iff, eqb_true_iff. now left.
    - easy.
  + case b2 in *.
    - simpl in H. case b1 in *; easy.
    - rewrite orb_true_iff, andb_true_iff. left. simpl. split.
      * rewrite eqb_true_iff. easy.
      * fold uge_list_big_endian. apply H.
Qed.

Lemma not_ult_list_big_endian_implies_uge_list_big_endian : forall (x y : list bool), 
  size x = size y -> ult_list_big_endian x y = false -> uge_list_big_endian x y = true.
Proof.
  induction x.
  + intros y. case y.
    - easy.
    - intros b l Hxy H. now contradict Hxy.
  + intros y Hxy H. case y in *. 
    - now contradict Hxy.
    - case x in *.
      * case y in *.
        ++ simpl in H. rewrite andb_false_iff, negb_false_iff in H.
           destruct H.
           -- rewrite H. case b; easy.
           -- rewrite H. case a; easy.
        ++ assert (size [a] <> size (b :: b0 :: y)). 
           { unfold size. rewrite <- N2Nat.inj_iff. 
             rewrite Nat2N.id. rewrite Nat2N.id. easy. } 
           easy.
      * case y in *.
        ++ assert (size (a :: b0 :: x) <> size [b]).
           { unfold size. rewrite <- N2Nat.inj_iff. 
             rewrite Nat2N.id. rewrite Nat2N.id. easy. } 
           easy.
        ++ unfold ult_list_big_endian in H.
           fold ult_list_big_endian in H. 
           rewrite orb_false_iff, andb_false_iff in H.
           destruct H. rewrite andb_false_iff, negb_false_iff in H0.
           destruct H0.
           -- rewrite H0. destruct H.
              ** rewrite H0 in H. rewrite eqb_false_iff in H.
                 apply not_eq_sym in H. apply not_true_is_false in H.
                 rewrite H. easy.
              ** case b.
                 +++ assert (size (b0 :: x) = size (b1 :: y)).
                     { unfold size in *. rewrite <- N2Nat.inj_iff in Hxy. 
                       rewrite Nat2N.id in Hxy. rewrite Nat2N.id in Hxy. 
                       simpl in Hxy. apply Nat.succ_inj in Hxy. 
                       rewrite <- N2Nat.inj_iff. rewrite Nat2N.id. 
                       rewrite Nat2N.id. simpl. rewrite Hxy. easy. }
                      specialize (@IHx (b1 :: y) H1 H). 
                      apply uge_list_big_endian_cons. apply IHx.
                 +++ easy.
           -- rewrite H0. destruct H.
              ** rewrite eqb_false_iff, H0 in H. 
                 apply not_false_is_true in H. rewrite H. easy.
              ** case a.
                 +++ easy.
                 +++ assert (size (b0 :: x) = size (b1 :: y)).
                     { unfold size in *. rewrite <- N2Nat.inj_iff in Hxy. 
                       rewrite Nat2N.id in Hxy. rewrite Nat2N.id in Hxy. 
                       simpl in Hxy. apply Nat.succ_inj in Hxy. 
                       rewrite <- N2Nat.inj_iff. rewrite Nat2N.id. 
                       rewrite Nat2N.id. simpl. rewrite Hxy. easy. }
                     specialize (@IHx (b1 :: y) H1 H).
                     apply uge_list_big_endian_cons. apply IHx.
Qed.

Lemma not_bv_ult_implies_bv_uge : forall (x y : bitvector), 
  size x = size y -> (bv_ult x y = false) -> bv_uge x y = true.
Proof.
  intros x y Hsize H. unfold bv_ult, bv_uge in *.
  case_eq (size x =? size y); intros Hxy.
  - rewrite Hxy in H. unfold size in Hxy. 
    rewrite <- length_rev in Hxy.
    rewrite <- (@length_rev bool y) in Hxy.
    unfold ult_list, uge_list in *. induction (rev x).
    * case (rev y) in *.
      ++ easy.
      ++ simpl in *. apply Hxy. 
    * case (rev y) in *.
      ++ simpl in *. case l in *; apply Hxy.
      ++ apply Neqb_ok in Hxy. 
         apply not_ult_list_big_endian_implies_uge_list_big_endian. 
         apply Hxy. apply H.
  - apply N.eqb_neq in Hxy. easy. 
Qed.


(* b1 = b2 -> !(b1 < b2) *)

Lemma ult_list_big_endian_not_refl : forall (b : list bool),
 ult_list_big_endian b b = false.
Proof.
  intros. induction b.
  + easy.
  + simpl. case b in *.
    - rewrite andb_comm. apply andb_negb_r.
    - rewrite orb_false_iff, andb_false_iff. split.
      * now right.
      * rewrite andb_comm. apply andb_negb_r.
Qed.

Lemma eq_not_ult_list_big_endian : forall (b1 b2 : list bool),
  b1 = b2 -> ult_list_big_endian b1 b2 = false.
Proof.
  induction b1.
  + intros. case b2; easy.
  + intros b2 H. induction b2.
    - easy.
    - rewrite H. apply ult_list_big_endian_not_refl. 
Qed.

Lemma eq_not_bv_ult : forall (b1 b2 : bitvector),
  b1 = b2 -> bv_ult b1 b2 = false.
Proof.
  intros b1 b2 H. unfold bv_ult.
  case_eq (size b1 =? size b2); intros size.
  + unfold ult_list. apply rev_func in H.
    apply eq_not_ult_list_big_endian. apply H.
  + easy.
Qed.


(* x >= y -> x !< y *)

Lemma bv_uge_implies_not_bv_ult : forall (x y : bitvector), 
  bv_uge x y = true -> (bv_ult x y = false).
Proof.
  intros x y. intros Hule. rewrite bv_uge_eq in Hule. 
  destruct Hule.
  - apply bv_ugt_not_bv_ult. apply H.
  - apply eq_not_bv_ult. apply H.
Qed.


(* x != [] ->
     x >= ~x <-> sign(x) = 0 *)

Lemma ult_big_endian_implies_not_uge_big_endian : forall (x y : bitvector),
  ult_list_big_endian x y = true -> uge_list_big_endian x y = false.
Proof.
  induction x.
  + intros y ult.
    case y in *.
    - easy.
    - easy.
  + intros y ult. case y in *.
    - case x in *; now contradict ult.
    - case a in *.
      * case b in *.
        ++ assert (ult_list_big_endian x y = true).
           { simpl in ult. case x in *.
             + case y in ult.
               - easy.
               - rewrite orb_true_iff in ult. destruct ult; now simpl in H.
             + case y in *.
               - rewrite orb_true_iff in ult. destruct ult.
                 * simpl in H; case x in H; easy.
                 * easy.
               - rewrite orb_true_iff in ult. destruct ult; easy. }
            specialize (@IHx y H). simpl. case x in *.
            -- case y in *.
               ** now contradict H.
               ** now contradict H.   
            -- case y in *.
               ** case x in *; now contradict H.
               ** rewrite orb_false_iff. split; easy.
        ++ case x in *; case y in *; now contradict ult.
      * case b in *.
        ++ case x in *; case y in *; easy.
        ++ assert (ult_list_big_endian x y = true).
           { simpl in ult. case x in *.
             + case y in ult.
               - easy.
               - rewrite orb_true_iff in ult. destruct ult; now simpl in H.
             + case y in *.
               - rewrite orb_true_iff in ult. destruct ult.
                 * simpl in H; case x in H; easy.
                 * easy.
               - rewrite orb_true_iff in ult. destruct ult; easy. }
            specialize (@IHx y H). simpl. case x in *.
            -- case y in *.
               ** now contradict H.
               ** now contradict H.   
            -- case y in *.
               ** case x in *; now contradict H.
               ** rewrite orb_false_iff. split; easy.
Qed.

Lemma ult_implies_not_uge : forall (x y : bitvector), bv_ult x y = true ->
  bv_uge x y = false.
Proof.
  intros x y ult.
  unfold bv_ult, bv_uge in *. case_eq (size x =? size y); intros H.
  + rewrite H in ult. unfold ult_list, uge_list in *.
    unfold size in H. rewrite <- length_rev in H. 
    rewrite <- (@length_rev bool y) in H. apply Neqb_ok in H. 
    rewrite <- N2Nat.inj_iff in H. rewrite Nat2N.id in H.
    rewrite Nat2N.id in H.
    apply ult_big_endian_implies_not_uge_big_endian. apply ult.
  + easy.
Qed.

Lemma bv_not_app : forall (x : bitvector) (b : bool),
  bv_not (x ++ [b]) = bv_not x ++ bv_not [b].
Proof.
  intros x b. induction x.
  + easy.
  + simpl. unfold bv_not in IHx.
    unfold bv_not. simpl. unfold bits in IHx.
    simpl in IHx. rewrite IHx. easy. 
Qed.

Lemma rev_bvnot : forall x : bitvector, rev (bv_not x) = bv_not (rev x).
Proof.
  intros x. induction x.
  + easy.
  + simpl. rewrite bv_not_app. 
    unfold bv_not, bits in IHx. 
    rewrite IHx. easy.
Qed. 

Lemma hd_rev: forall a,
  hd false (rev a) = last a false.
Proof. intro a.
        induction a using rev_ind; intros.
        - now cbn.
        - Reconstr.rblast (@Coq.Lists.List.rev_unit, 
            @RAWBITVECTOR_LIST.last_app) 
           (@Coq.Lists.List.hd).
Qed.

Lemma uge_bvnot_refl_implies_sign_neg : forall (x : bitvector),
  x <> [] -> bv_uge x (bv_not x) = true -> last x false = true.
Proof.
  intros x notnil uge. unfold bv_uge in uge.
  assert (Hsize : size x = size (bv_not x)).
  { rewrite (@bv_not_size (size x) x). easy. easy. }
  rewrite <- Hsize in uge. rewrite N.eqb_refl in uge.
  unfold uge_list in uge. rewrite rev_bvnot in uge.
  apply rev_neg_func in notnil. simpl in notnil. 
  rewrite <- hd_rev. induction (rev x).
  + now contradict notnil.
  + case a in *.
    * easy. 
    * assert (bv_not (false :: l) = true :: bv_not l) by easy.
      rewrite H in uge.
      assert (contr : forall (b1 b2 : bitvector), uge_list_big_endian (false :: b1) (true :: b2) = false).
      { intros b1 b2. apply ult_big_endian_implies_not_uge_big_endian. case b1; case b2; easy. }
      specialize (@contr l (bv_not l)). rewrite contr in uge. easy.
Qed.

Lemma sign_neg_implies_uge_bvnot_refl : forall (x : bitvector),
  x <> [] -> last x false = true -> bv_uge x (bv_not x) = true.
Proof.
  intros x notnil sign. induction x.
  + now contradict notnil.
  + unfold bv_uge. rewrite (@bv_not_size (size (a :: x)) (a :: x) eq_refl).
    rewrite N.eqb_refl. unfold uge_list. unfold bv_not, bits.
    rewrite <- map_rev. rewrite <- hd_rev in sign. 
    case (rev (a :: x)) in *.
    - easy.
    - simpl in sign. rewrite sign. simpl. case l; easy.
Qed.

Lemma uge_bvnot_refl_eq_sign_neg : forall (x : bitvector),
  x <> [] -> bv_uge x (bv_not x) = true <-> last x false = true.
Proof. 
  split.
  + now apply uge_bvnot_refl_implies_sign_neg.
  + now apply sign_neg_implies_uge_bvnot_refl.
Qed.


(* Transitivity : x >= y => y >= z => x >= z *)
Lemma uge_list_big_endian_trans : forall x y z,
    uge_list_big_endian x y = true ->
    uge_list_big_endian y z = true ->
    uge_list_big_endian x z = true.
Proof.
  intros. apply uge_list_big_endian_ule_list_big_endian in H.
  apply uge_list_big_endian_ule_list_big_endian in H0.
  apply ule_list_big_endian_uge_list_big_endian.
  apply (@ule_list_big_endian_trans z y x H0 H).
Qed.

(* bool output *)
Lemma uge_list_trans : forall x y z,
  uge_list x y = true -> uge_list y z = true -> uge_list x z = true.
Proof.
  unfold uge_list. intros x y z. apply uge_list_big_endian_trans. 
Qed.

Lemma bv_uge_list_trans : forall (b1 b2 b3 : bitvector), 
  bv_uge b1 b2 = true -> bv_uge b2 b3 = true -> bv_uge b1 b3 = true.
Proof.
  intros. apply bv_uge_bv_ule in H. apply bv_uge_bv_ule in H0. 
  apply bv_ule_bv_uge. apply (@bv_ule_list_trans b3 b2 b1 H0 H).
Qed.

(* Prop output *)
Lemma uge_listP_trans : forall (b1 b2 b3 : bitvector),
  uge_listP b1 b2 -> uge_listP b2 b3 -> uge_listP b1 b3.
Proof.
  intros. apply uge_listP_ule_listP in H. apply uge_listP_ule_listP in H0.
  apply ule_listP_uge_listP. apply (@ule_listP_trans b3 b2 b1 H0 H).
Qed.

Lemma bv_ugeP_trans : forall (b1 b2 b3 : bitvector),
  bv_ugeP b1 b2 -> bv_ugeP b2 b3 -> bv_ugeP b1 b3.
Proof.
  intros. apply bv_ugeP_bv_uleP in H. apply bv_ugeP_bv_uleP in H0.
  apply bv_uleP_bv_ugeP. apply (@bv_uleP_trans b3 b2 b1 H0 H).
Qed.

(* signed greater than or equal to *)

Definition sge_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, nil  => true
    | nil, _ => false 
    | _, nil => false
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (uge_list_big_endian x' y'))
          (andb (negb xi) yi)
  end.

(* bool output *)
Definition sge_list (x y: list bool) :=
  sge_list_big_endian (List.rev x) (List.rev y).

Definition bv_sge (a b : bitvector) : bool :=
  if @size a =? @size b then sge_list a b else false.

(* Prop output *)
Definition sge_listP (x y: list bool) :=
  if sge_list x y then True else False.

Definition bv_sgeP (a b : bitvector) : Prop :=
  if @size a =? @size b then sge_listP a b else False.


(* Shift Right (Logical) *)

Definition shr_one_bit (a: list bool) : list bool :=
   match a with
     | [] => []
     | xa :: xsa => xsa ++ [false]
   end.

Definition shr_n_bits_a (a: list bool) (n: nat): list bool :=
   if (n <? length a)%nat then skipn n a ++ mk_list_false n 
   else mk_list_false (length a).

Fixpoint shr_n_bits (a: list bool) (n: nat): list bool :=
    match n with
      | O => a
      | S n' => shr_n_bits (shr_one_bit a) n'  
    end.

Definition shr_aux (a b: list bool): list bool :=
shr_n_bits a (list2nat_be_a b).

Definition shr_aux_a (a b: list bool): list bool :=
shr_n_bits_a a (list2nat_be_a b).

Definition bv_shr (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shr_aux a b
  else nil.

Definition bv_shr_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shr_n_bits_a a (list2nat_be_a b)
  else nil.

Lemma length_skipn: forall n (a: list bool), length (skipn n a) = (length a - n)%nat.
Proof. intro n.
       induction n; intros.
       - cbn. now rewrite Nat.sub_0_r.
       - cbn. case_eq a; intros.
         now cbn.
         cbn. now rewrite <- IHn.
Qed.

Lemma help_same: forall a n,
(n <? length a)%nat = true ->
firstn (length a - n) (skipn n a ++ false :: false :: mk_list_false n) =
firstn (length a - n) (skipn n a ++ false :: mk_list_false n).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq n; intros.
         cbn. f_equal. rewrite !firstn_app, !firstn_all.
         rewrite Nat.sub_diag. now cbn.
         cbn. rewrite !firstn_app. f_equal.
         rewrite length_skipn. 
         assert ((length a0 - n0 - (length a0 - n0))%nat = 0%nat) by lia.
         rewrite H1. now cbn.
Qed.

Lemma fs: forall a n,
(n <? length a)%nat = true ->
skipn n (mk_list_false n ++ firstn (length a - n) (skipn n a ++ false :: mk_list_false n)) =
skipn n a.
Proof. intro a.
       induction a; intros.
       - cbn. now rewrite app_nil_r.
       - cbn. case_eq n; intros.
         cbn. rewrite firstn_app.
         now rewrite Nat.sub_diag, firstn_all, app_nil_r.
         cbn. specialize (IHa n0).
         rewrite help_same. apply IHa.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in H. lia.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in H. lia.
Qed.

Lemma shr_n_shl_a: forall a n,
  shr_n_bits_a (shl_n_bits_a (shr_n_bits_a a n) n) n = shr_n_bits_a a n.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - unfold shr_n_bits_a.
         case_eq ((n <? length (a :: a0))%nat); intros.
         assert ( length (shl_n_bits_a (skipn n (a :: a0) ++ mk_list_false n) n) = 
                  length  (a :: a0)).
         { rewrite length_shl_n_bits_a, length_app, length_mk_list_false, length_skipn.
           apply Nat.ltb_lt in H.
           lia.
         } 
         rewrite H0, H.
         unfold shl_n_bits_a.
         assert ((length (skipn n (a :: a0) ++ mk_list_false n) = length (a :: a0))).
         { rewrite length_app, length_skipn, length_mk_list_false.
           apply Nat.ltb_lt in H.
           lia.
         }
         rewrite H1, H. cbn.
         case_eq n; intros. cbn.
         assert (firstn (length a0) (a0 ++ []) = a0).
         { now rewrite app_nil_r, firstn_all. }
         now rewrite H3.
         cbn. f_equal. rewrite fs. easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
         assert (length (shl_n_bits_a (mk_list_false (length (a :: a0))) n) = length (a :: a0)).
         { now rewrite length_shl_n_bits_a, length_mk_list_false. } 
         now rewrite H0, H.
Qed.

Lemma skipn_all: forall (A: Type) n (l: list A), ((length l <=? n)%nat = true)-> skipn n l = [].
Proof. intros A n.
       induction n; intros.
       - cbn. assert (length l = 0%nat).
         { apply Nat.leb_le in H. lia. }
         now apply length_zero_iff_nil in H0.
       - cbn. case_eq l; intros.
         + easy.
         + apply IHn. subst. cbn in H.
         apply Nat.leb_le in H.
         apply Nat.leb_le. lia.
Qed.

(* skipn n0 (mk_list_false n0 ++ firstn (length a0 - n0) (a :: a0)) = firstn (length a0 - n0) (a :: a0)
 *)
Lemma skipn_jo: forall n (a: list bool),
skipn n (mk_list_false n ++ a) = a.
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. apply IHn.
Qed.

Lemma shl_n_shr_a: forall a n,
   shl_n_bits_a (shr_n_bits_a (shl_n_bits_a a n) n) n = shl_n_bits_a a n.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - unfold shr_n_bits_a, shl_n_bits_a.
          case_eq ((n <? length (a :: a0))%nat); intros.
          rewrite !length_app, !length_mk_list_false, !length_firstn.
          assert (Hone: Init.Nat.min (length (a :: a0) - n) (length (a :: a0))%nat =
                      (length (a :: a0) - n)%nat).
          { 
            rewrite Nat.min_l. easy.
            lia.
          }
          rewrite Hone. 
          assert (Htwo: (n + (length (a :: a0) - n))%nat = (length (a :: a0))%nat).
          { rewrite Nat.add_comm, Nat.sub_add.
            easy.
            apply Nat.ltb_lt in H. lia. 
          }
          rewrite Htwo, H.
          assert (length (skipn n (mk_list_false n ++
                   firstn (length (a :: a0) - n) (a :: a0)) ++ mk_list_false n) = length (a :: a0)).
          { rewrite skipn_jo.
            rewrite length_app, length_firstn, length_mk_list_false.
            rewrite Nat.min_l, Nat.sub_add.
            easy. 
            apply Nat.ltb_lt in H. lia.
            lia.
          }
          rewrite H0, H.
          f_equal.
          rewrite firstn_app, length_skipn, length_app, length_mk_list_false.
          assert ((n + length (firstn (length (a :: a0) - n) (a :: a0)) - n)%nat = 
                  (length (a :: a0) - n)%nat).
          { rewrite length_firstn.
            rewrite Nat.min_l, Nat.add_comm, Nat.add_sub. easy.
            apply Nat.ltb_lt in H. lia.
          }
          rewrite H1.
          assert ((length (a :: a0) - n - (length (a :: a0) - n))%nat = 0%nat).
          { lia. }
          rewrite H2. 
          assert (firstn 0 (mk_list_false n) = []).
          { now cbn. }
          rewrite H3, app_nil_r.
          assert ((skipn n (mk_list_false n ++ firstn (length (a :: a0) - n) (a :: a0) )) =
                  (firstn (length (a :: a0) - n) (a :: a0))).
          { cbn. case_eq n; intros.
            now cbn.
            cbn. rewrite skipn_jo. easy.
          } rewrite H4. 
          now rewrite firstn_firstn, Nat.min_id.
          now rewrite !length_mk_list_false, H, length_mk_list_false, H.
Qed.

Lemma length_shr_one_bit: forall a, length (shr_one_bit a) = length a.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl. rewrite <- IHa.
         case_eq a0; easy.
Qed.

Lemma length_shr_n_bits_a: forall n a, length (shr_n_bits_a a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - unfold shr_n_bits_a.
         case_eq a; intros. now cbn. 
         cbn. rewrite length_app. f_equal. easy.
       - unfold shr_n_bits_a.
         case_eq ( (S n <? length a)%nat); intros. cbn.
         case_eq a; intros. subst. cbn in *.
         now contradict H.
         unfold shr_n_bits_a. subst.
         rewrite !length_app. cbn.
         rewrite length_mk_list_false.
         rewrite length_skipn. rewrite <- plus_n_Sm.
         f_equal. rewrite Nat.sub_add; try easy.
         apply Nat.ltb_lt in H. cbn in H.
         inversion H. rewrite H1. lia.
         lia.
         now rewrite length_mk_list_false.
Qed.

Lemma length_shr_n_bits: forall n a, length (shr_n_bits a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - reflexivity.
       - now rewrite (IHn (shr_one_bit a)), length_shr_one_bit.
Qed.

Lemma length_shr_aux: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (shr_aux a b)).
Proof.
    intros.
    unfold shr_aux. now rewrite length_shr_n_bits.
Qed.

Lemma bv_shr_size n a b : size a = n -> size b = n -> size (bv_shr a b) = n.
Proof.
  unfold bv_shr. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_shr_aux a b (nat_of_N n)).
  now rewrite N2Nat.id.
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
Qed.

Lemma shl_n_shl_one: forall n a, (shl_n_bits (shl_one_bit a) n) = shl_n_bits a (S n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shr_n_shr_one: forall n a, (shr_n_bits (shr_one_bit a) n) = shr_n_bits a (S n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shr_n_shr_one_comm: forall n a, (shr_n_bits (shr_one_bit a) n) = shr_one_bit (shr_n_bits a n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shl_n_shl_one_comm: forall n a, (shl_n_bits (shl_one_bit a) n) = shl_one_bit (shl_n_bits a n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma rl_fact: forall (a: list bool) b, removelast (a ++ [b]) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq (a0 ++ [b]); intros.
         contradict H.
         case_eq a0; intros; subst; easy.
         now rewrite <- H, IHa.
Qed.

Lemma shl_one_b: forall a b, (shl_one_bit (a ++ [b])) = false :: a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq (a0 ++ [b]); intros.
         contradict H.
         case_eq a0; intros; subst; easy.
         rewrite <- H. f_equal. f_equal. apply rl_fact.
Qed. 

Lemma shr_one_shl: forall a, shr_one_bit (shl_one_bit (shr_one_bit a)) = shr_one_bit a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. rewrite shl_one_b. now cbn.
Qed.

(* a >> b <= ~b >> b *)

Lemma skipn_bv_not : forall (n : nat) (b : bitvector), 
  bv_not (skipn n b) = skipn n (bv_not b).
Proof.
  induction n.
  + easy.
  + destruct b.
    - easy.
    - simpl. specialize (@IHn b0). apply IHn.
Qed.

Lemma eq_bv_not : forall (x y : bitvector), x = y -> bv_not x = bv_not y.
Proof.
  induction x.
  + destruct y. 
    - easy.
    - intros Hxy. now contradict Hxy.
  + destruct y.
    - intros Hxy. now contradict Hxy.
    - unfold bv_not in *. unfold bits in *. simpl.
      intros Hxy. inversion Hxy. easy. 
Qed.


(* Shift Right (Arithmetic) *)

Definition ashr_one_bit (a: list bool) (sign: bool) : list bool :=
   match a with
     | [] => []
     | h :: t => t ++ [sign]
   end.

Definition ashr_n_bits_a (a: list bool) (n: nat) (sign: bool): list bool :=
   if (n <? length a)%nat then 
     if (Bool.eqb sign false) then skipn n a ++ mk_list_false n 
     else skipn n a ++ mk_list_true n 
   else 
     if (Bool.eqb sign false) then mk_list_false (length a)
     else mk_list_true (length a).

Fixpoint ashr_n_bits (a: list bool) (n: nat) (sign: bool): list bool :=
    match n with
      | O => a
      | S n' => ashr_n_bits (ashr_one_bit a sign) n' sign
    end.

Definition ashr_aux_a (a b: list bool): list bool :=
ashr_n_bits_a a (list2nat_be_a b) (last a false).

Definition ashr_aux (a b: list bool): list bool :=
ashr_n_bits a (list2nat_be_a b) (last a false).

Definition bv_ashr_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then ashr_aux_a a b
  else nil.

Definition bv_ashr (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then ashr_aux a b
  else nil.


(* b >>a 0 = b *)
Lemma ashr_n_bits_a_zero : forall (b : list bool) (sign : bool),
  ashr_n_bits_a b 0 sign = b.
Proof.
  intros b. unfold ashr_n_bits_a. 
  case_eq ((0 <? length b)%nat); intros.
  + case_eq (eqb sign false); intros; simpl;
    now rewrite app_nil_r.
  + case_eq (eqb sign false); intros.
    rewrite Nat.ltb_ge in H;
    apply Nat.le_0_r in H;
    rewrite symmetry in H;
    pose proof (@empty_list_length bool b);
    apply H1 in H; rewrite H;
    simpl;
    symmetry.
    apply H1.
    easy.
    easy.
    rewrite Nat.ltb_ge in H.
    apply Nat.le_0_r in H.
    rewrite H.
    simpl.
    case_eq b; intros.
    - easy.
    - subst. simpl in *. easy.
Qed.

Lemma bvashr_zero : forall (b : bitvector), bv_ashr_a b (zeros (size b)) = b.
Proof. 
  intros b. unfold bv_ashr_a. rewrite zeros_size. 
  rewrite N.eqb_refl. unfold ashr_aux_a.
  unfold zeros, size, list2nat_be_a. rewrite Nat2N.id. 
  rewrite list2N_mk_list_false. simpl. apply ashr_n_bits_a_zero.
Qed.


(* ashr <-> ashr_a *)

Lemma ashr_n_ashr_one_comm: forall n a b, 
  (ashr_n_bits (ashr_one_bit a b) n b) = ashr_one_bit (ashr_n_bits a n b) b.
Proof. 
  induction n; intros.
  + easy.
  + simpl. now rewrite IHn.
Qed.

Lemma ashr_skip_n_one_bit: forall n l b sign,
  ((n <? length (b :: l))%nat = true) ->
  ashr_one_bit (skipn n (b :: l)) sign =  skipn n l ++ [sign].
Proof. 
  intro n. induction n; intros.
  + easy.
  + simpl. 
    case_eq l; intros. 
    - subst. cbn in *. now contradict H.
    - rewrite <- (IHn l0 b0). easy.
      apply Nat.ltb_lt in H.
      apply Nat.ltb_lt. subst. cbn in *. lia.
Qed.

Lemma mk_list_false_cons2: forall n,
mk_list_false n ++ [false] = false :: mk_list_false n.
Proof. intro n.
       induction n; intros.
       now cbn.
       cbn. now rewrite <- IHn.
Qed.

Lemma ashr_one_bit_append_false: forall a n,
  ashr_one_bit (a ++ (mk_list_false n)) false = 
  (ashr_one_bit a) false ++ (mk_list_false n).
Proof. 
  intro a. induction a; intros.
  + simpl. case_eq n; intros.
    - easy.
    - simpl. now rewrite mk_list_false_cons2.
  + simpl. repeat rewrite <- app_assoc.
    assert (mk_list_false n ++ [false] = [false] ++ mk_list_false n).
    { simpl. induction n; intros.
      + now cbn. 
      + cbn. now rewrite <- IHn. } 
    now rewrite H. 
Qed.

Lemma mk_list_true_cons2: forall n,
mk_list_true n ++ [true] = true :: mk_list_true n.
Proof. 
  intro n. induction n; intros.
  + now cbn.
  + cbn. now rewrite <- IHn.
Qed.

Lemma ashr_one_bit_append_true: forall a n,
  ashr_one_bit (a ++ (mk_list_true n)) true = 
  (ashr_one_bit a) true ++ (mk_list_true n).
Proof. 
  intro a. induction a; intros.
  + simpl. case_eq n; intros.
    - easy.
    - simpl. now rewrite mk_list_true_cons2.
  + simpl. repeat rewrite <- app_assoc.
    assert (mk_list_true n ++ [true] = [true] ++ mk_list_true n).
    { simpl. induction n; intros.
      + now cbn. 
      + cbn. now rewrite <- IHn. } 
    now rewrite H. 
Qed.

Lemma ashr_one_bit_skipn_sign: forall n a b,
  length a = S n -> ashr_one_bit (skipn n a) b = [b].
Proof. 
  intro n. induction n; intros.
  + cbn. case_eq a; intros. 
    - subst. now contradict H.
    - cbn. assert (l = nil).
      { subst. cbn in *. inversion H.
        apply length_zero_iff_nil in H1.
        now subst. } 
      now rewrite H1, app_nil_l.
  + cbn. case_eq a; intros.
    - subst. now contradict H.
    - apply IHn. subst. cbn in H. lia.
Qed.

Lemma ashr_one_bit_skipn_false: forall n a, length a = S n ->
  ashr_one_bit (skipn n a ++ mk_list_false n) false 
  = mk_list_false n ++ [false].
Proof. 
  intro n. induction n; intros.
  + cbn. rewrite app_nil_r. case_eq a; intros.
    subst. now contradict H. subst. cbn in *. 
    inversion H. apply length_zero_iff_nil in H1.
    subst. now rewrite app_nil_l. 
  + cbn. case_eq a; intros. subst. now contradict H.
    rewrite <- (IHn l). rewrite ashr_one_bit_append_false.
    assert (false :: mk_list_false n = mk_list_false (S n)) by easy.
    rewrite H1, ashr_one_bit_append_false.
    cbn. rewrite ashr_one_bit_skipn_sign. easy.
    subst. cbn in *. lia.
    subst. cbn in *. lia.
Qed.

Lemma ashr_one_bit_skipn_true: forall n a, length a = S n ->
  ashr_one_bit (skipn n a ++ mk_list_true n) true
  = mk_list_true n ++ [true].
Proof. 
  intro n. induction n; intros.
  + cbn. rewrite app_nil_r. case_eq a; intros.
    subst. now contradict H. subst. cbn in *. 
    inversion H. apply length_zero_iff_nil in H1.
    subst. now rewrite app_nil_l. 
  + cbn. case_eq a; intros. subst. now contradict H.
    rewrite <- (IHn l). rewrite ashr_one_bit_append_true.
    assert (true :: mk_list_true n = mk_list_true (S n)) by easy.
    rewrite H1, ashr_one_bit_append_true.
    cbn. rewrite ashr_one_bit_skipn_sign. easy.
    subst. cbn in *. lia.
    subst. cbn in *. lia.
Qed.

Lemma ashr_one_bit_all_false: forall (a: list bool),
  ashr_one_bit (mk_list_false (length a)) false = mk_list_false (length a).
Proof. 
  intro a. induction a; intros.
  - now cbn.
  - cbn. now rewrite mk_list_false_cons2.
Qed.

Lemma ashr_one_bit_all_true: forall (a: list bool),
  ashr_one_bit (mk_list_true (length a)) true = mk_list_true (length a).
Proof. 
  intro a. induction a; intros.
  - now cbn.
  - cbn. now rewrite mk_list_true_cons2.
Qed.

Theorem bv_ashr_aux_eq: forall n a b, 
  ashr_n_bits a n b = ashr_n_bits_a a n b.
Proof. 
  induction n. 
  + intros. simpl. rewrite ashr_n_bits_a_zero. easy.
  + intros a b. simpl. rewrite ashr_n_ashr_one_comm. 
    rewrite IHn. unfold ashr_n_bits_a.
    case_eq ((S n <? length a)%nat); intros case.
    - apply Nat.ltb_lt in case. 
      apply Nat.lt_succ_l in case. apply Nat.ltb_lt in case. 
      rewrite case. case_eq (eqb b false); intros sign.
      * rewrite eqb_true_iff in sign. subst. 
        case a in *.
        ++ now contradict case. 
        ++ simpl. 
           assert (cons_app: skipn n a ++ false :: mk_list_false n 
           = skipn n a ++ [false] ++ mk_list_false n) by easy. 
           rewrite cons_app. rewrite app_assoc. 
           rewrite <- (@ashr_skip_n_one_bit n a b false case).
           rewrite ashr_one_bit_append_false. easy.
      * rewrite eqb_false_iff in sign. 
        apply not_false_is_true in sign. subst.
        case a in *.
        ++ now contradict case.
        ++ simpl.
           assert (cons_app: skipn n a ++ true :: mk_list_true n 
           = skipn n a ++ [true] ++ mk_list_true n) by easy. 
           rewrite cons_app. rewrite app_assoc.
           rewrite <- (@ashr_skip_n_one_bit n a b true case).
           rewrite ashr_one_bit_append_true. easy.
    - case_eq ((n <? length a)%nat); intros case2.
      * assert (len : length a = S n).
        { apply Nat.ltb_lt in case2.
          apply Nat.ltb_ge in case. lia. }
        rewrite len. case_eq (eqb b false); intros sign. 
        ++ rewrite eqb_true_iff in sign. rewrite sign. 
           rewrite (@ashr_one_bit_skipn_false n a len).
           now rewrite mk_list_false_cons2.
        ++ rewrite eqb_false_iff in sign. 
           apply not_false_is_true in sign. rewrite sign.
           rewrite (@ashr_one_bit_skipn_true n a len).
           now rewrite mk_list_true_cons2.
      * case_eq (eqb b false); intros sign.
        ++ rewrite eqb_true_iff in sign. rewrite sign. 
           now rewrite ashr_one_bit_all_false.
        ++ rewrite eqb_false_iff in sign. 
           apply not_false_is_true in sign. rewrite sign.
           now rewrite ashr_one_bit_all_true.
Qed.

Theorem bv_ashr_eq: forall (a b : bitvector),
  bv_ashr a b = bv_ashr_a a b.
Proof. 
  intros. unfold bv_ashr, bv_ashr_a.
  case_eq (size a =? size b); intros; try easy.
  unfold ashr_aux. unfold ashr_aux_a. 
  now rewrite bv_ashr_aux_eq.
Qed.



Lemma length_ashr_one_bit: forall a sign, length (ashr_one_bit a sign) = length a.
Proof. intro a. destruct sign.
  + induction a; intros.
    - now simpl.
    - simpl. rewrite <- IHa.
      case_eq a0; easy.
  + induction a; intros.
   - now simpl.
   - simpl. rewrite <- IHa.
     case_eq a0; easy.
  Qed.

Lemma length_ashr_n_bits: forall n a sign, length (ashr_n_bits a n sign) = length a.
Proof.
  intros n.
  induction n; intros; simpl.
  - reflexivity.
  - now rewrite (IHn (ashr_one_bit a sign)), length_ashr_one_bit.
Qed. 

Lemma length_ashr_n_bits_a: forall a n sign, length (ashr_n_bits_a a n sign) = length a.
Proof. intro n.
        induction n; intros.
        - cbn.
           Reconstr.reasy (@RAWBITVECTOR_LIST.length_mk_list_false) (@RAWBITVECTOR_LIST.mk_list_false).
        - cbn. unfold ashr_n_bits_a. cbn.
           case_eq ((n0 <=? length n)%nat); intros.
           + case_eq (eqb sign false); intros.
             rewrite length_app ,length_mk_list_false.
             rewrite length_skipn.
             Reconstr.reasy (@Coq.Arith.Compare_dec.leb_correct_conv, 
              @Coq.Arith.PeanoNat.Nat.sub_add, @Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.ltb_ge) 
             (@RAWBITVECTOR_LIST.shl_n_bits_a, @Coq.Init.Datatypes.length, @Coq.Init.Peano.lt).
             rewrite length_app ,length_mk_list_true.
             rewrite length_skipn.
             Reconstr.reasy (@Coq.Arith.Compare_dec.leb_correct_conv, 
              @Coq.Arith.PeanoNat.Nat.sub_add, @Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.ltb_ge) 
             (@RAWBITVECTOR_LIST.shl_n_bits_a, @Coq.Init.Datatypes.length, @Coq.Init.Peano.lt).
           + case_eq (eqb sign false); intros.
             cbn. now rewrite length_mk_list_false.
             cbn. now rewrite length_mk_list_true.
Qed.

Lemma length_ashr_aux_a: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (ashr_aux_a a b)).
Proof. intros.
        unfold ashr_aux_a. now rewrite length_ashr_n_bits_a.
Qed.

Lemma length_ashr_aux: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (ashr_aux a b)).
Proof.
  intros.
  unfold ashr_aux. now rewrite length_ashr_n_bits.
Qed.

Lemma bv_ashr_size n a b : size a = n -> size b = n -> size (bv_ashr a b) = n.
Proof.
  unfold bv_ashr. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_ashr_aux a b (nat_of_N n)).
  now rewrite N2Nat.id. 
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
  Qed.


Lemma bv_ashr_a_size n a b : size a = n -> size b = n -> size (bv_ashr_a a b) = n.
Proof.
  unfold bv_ashr_a. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_ashr_aux_a a b (nat_of_N n)).
  now rewrite N2Nat.id. 
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
  Qed.

(* here *)
Lemma bv_shr_a_size n a b : size a = n -> size b = n -> size (bv_shr_a a b) = n.
Proof.
  unfold bv_shr_a. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. now rewrite length_shr_n_bits_a.
Qed.


Lemma ashr_shr_false: forall a n, ashr_n_bits_a a n false = shr_n_bits_a a n.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - unfold ashr_n_bits_a, shr_n_bits_a. cbn.
         case_eq ((n <=? length a0)%nat); intros; easy.
Qed.

Lemma ashr_n_shl_a: forall a n b,
   ashr_n_bits_a (shl_n_bits_a (ashr_n_bits_a a n b) n) n b =
   ashr_n_bits_a a n b.
Proof. intros.
       case_eq b; intros.
       - revert n.
         induction a; intros.
         + now cbn.
         + unfold ashr_n_bits_a, shl_n_bits_a.
           case_eq ( (n <? length (a :: a0))%nat); intros.
           * cbn. rewrite !length_app, !length_mk_list_true.
             rewrite !length_skipn.
             assert (Hone: ((length (a :: a0) - n + n))%nat = (length (a :: a0))%nat).
             { apply Nat.ltb_lt in H0.
               Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_le_incl, 
                 @Coq.Arith.PeanoNat.Nat.sub_add) Reconstr.Empty.
             } rewrite Hone. cbn.
             assert (Htwo: (n <=? length a0)%nat = true).
             { Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_antisym, 
                  @Coq.Arith.PeanoNat.Nat.leb_nle, @Coq.Arith.PeanoNat.Nat.ltb_antisym, 
                  @Coq.Bool.Bool.negb_true_iff, @Coq.Arith.Compare_dec.leb_correct) 
                 (@Coq.Init.Nat.ltb, @Coq.Init.Datatypes.length).
             } rewrite Htwo. rewrite !length_app, !length_mk_list_false, !length_firstn.
               case_eq n; intros. cbn.
               Reconstr.reasy (@Coq.Lists.List.firstn_all, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
               subst. cbn. rewrite !length_app. cbn. rewrite !length_mk_list_true.
               rewrite Nat.min_l.
               assert ((n0 + (length a0 - n0))%nat = (length a0)).
               { rewrite Nat.add_comm.
                 rewrite Nat.sub_add. easy.
                 apply Nat.leb_le in Htwo.
                 Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_le_incl) (@Coq.Init.Peano.lt).
               }
               rewrite H. case_eq a0; intros.
               subst. cbn in *. easy.
               subst. cbn in *. rewrite H0.
               case_eq n0; intros. cbn. 
               Reconstr.rcrush (@Coq.Lists.List.app_nil_r, @Coq.Lists.List.firstn_all, 
                  @Coq.Arith.PeanoNat.Nat.sub_diag, @Coq.Lists.List.app_comm_cons, 
                  @Coq.Lists.List.firstn_app) (@Coq.Lists.List.firstn).
               cbn. rewrite skipn_jo.
               rewrite firstn_app, length_skipn.
               assert (firstn (length l - n) (skipn n l) = skipn n l).
               { Reconstr.rsimple (@Coq.Lists.List.firstn_all2, 
                   @Coq.Arith.PeanoNat.Nat.lt_eq_cases,
                   @RAWBITVECTOR_LIST.length_skipn) Reconstr.Empty.
               } rewrite H2.
               assert (((length l - n - (length l - n)))%nat = O).
               { Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty. }
               rewrite H3. cbn. now rewrite app_nil_r.
               Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.le_add_r, 
                 @RAWBITVECTOR_LIST.length_skipn) Reconstr.Empty.
           * cbn. rewrite length_mk_list_true.
             assert ((n <=? length a0)%nat = false).
             { 	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_ge,
                  @Coq.Arith.PeanoNat.Nat.leb_gt) 
                 (@Coq.Init.Peano.lt, @Coq.Init.Datatypes.length).
             } rewrite H1. cbn. now rewrite length_mk_list_false, H1.
       - now rewrite !ashr_shr_false, shr_n_shl_a.
Qed.

Lemma skip_n_one_bit: forall n l b,
((n <? length (b :: l))%nat = true) ->
shr_one_bit (skipn n (b :: l)) =  skipn n l ++ [false].
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. case_eq l; intros. subst. cbn in *.
         now contradict H.
         rewrite <- (IHn l0 b0). easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
Qed.

Lemma mk_list_false_cons: forall n,
mk_list_false n ++ [false] = false :: mk_list_false n.
Proof. intro n.
       induction n; intros.
       now cbn.
       cbn. now rewrite <- IHn.
Qed.

Lemma shr_one_bit_append_false: forall a n,
shr_one_bit (a ++ (mk_list_false n)) = (shr_one_bit a) ++ (mk_list_false n).
Proof. intro a.
       induction a; intros.
       - cbn. case_eq n; intros.
         now cbn. cbn. now rewrite mk_list_false_cons.
       - cbn. repeat rewrite <- app_assoc.
         assert (mk_list_false n ++ [false] = [false] ++ mk_list_false n).
         { cbn. induction n; intros.
           now cbn. cbn.
           now rewrite <- IHn.
         } now rewrite H. 
Qed.

Lemma shr_one_bit_skipn_false1: forall n a,
length a = S n -> shr_one_bit (skipn n a) = [false].
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. subst.
         now contradict H.
         cbn. assert (l = nil).
         subst. cbn in *. inversion H.
         apply length_zero_iff_nil in H1.
         now subst. 
         now rewrite H1, app_nil_l.
       - cbn. case_eq a; intros.
         subst. now contradict H.
         apply IHn. subst. cbn in H. lia.
Qed.

Lemma shr_one_bit_skipn_false: forall n a,
length a = S n ->
shr_one_bit (skipn n a ++ mk_list_false n) = mk_list_false n ++ [false].
Proof. intro n.
       induction n; intros.
       - cbn. rewrite app_nil_r. case_eq a; intros.
         subst. now contradict H.
         subst. cbn in *. inversion H.
         apply length_zero_iff_nil in H1.
         subst. now rewrite app_nil_l. 
       - cbn. case_eq a; intros.
         subst. now contradict H.
         rewrite <- (IHn l).
         rewrite shr_one_bit_append_false.
         assert (false :: mk_list_false n = mk_list_false (S n)).
         { easy. }
         rewrite H1, shr_one_bit_append_false.
         cbn. rewrite shr_one_bit_skipn_false1. easy.
         subst. cbn in *. lia.
         subst. cbn in *. lia.
Qed.

Lemma shr_one_bit_all_false: forall (a: list bool),
shr_one_bit (mk_list_false (length a)) = mk_list_false (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. now rewrite mk_list_false_cons.
Qed.

Theorem bv_shr_aux_eq: forall n a, shr_n_bits a n = shr_n_bits_a a n.
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. now cbn.
         cbn. now rewrite app_nil_r.
       - cbn. rewrite shr_n_shr_one_comm, IHn.
         unfold shr_n_bits_a.
         case_eq ((S n <? length a)%nat); intros.
         assert ((n <? length a)%nat = true).
         { apply Nat.ltb_lt in H.
           apply Nat.ltb_lt. lia.
         }
         rewrite H0. cbn. case_eq a; intros.
         subst. cbn in *. now contradict H.
         cbn.
         assert (skipn n l ++ false :: mk_list_false n = skipn n l ++ [false] ++ mk_list_false n).
         { easy. }
         rewrite H2.
         rewrite app_assoc.
         specialize (@skip_n_one_bit n l b); intros.
         rewrite <- H3.
         rewrite shr_one_bit_append_false. easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
         case_eq ((n <? length a)%nat); intros.
         assert (length a = S n).
         { apply Nat.ltb_lt in H0.
           apply Nat.ltb_ge in H.
           lia.
         } rewrite H1, shr_one_bit_skipn_false; try easy.
         cbn. 
         now rewrite mk_list_false_cons.
         now rewrite shr_one_bit_all_false.
Qed.

Theorem bv_shr_eq: forall (a b : bitvector),
  bv_shr a b = bv_shr_a a b.
Proof. intros.
       unfold bv_shr, bv_shr_a.
       case_eq (size a =? size b); intros; try easy.
       unfold shr_aux. now rewrite bv_shr_aux_eq.
Qed.

Lemma shl_one: forall a, a <> nil -> shl_one_bit a = false :: removelast a.
Proof. intros. unfold shl_one_bit.
       induction a; intros.
       - now contradict H.
       - easy.
Qed.

Lemma shl_one_bit_app: forall a b,
  b <> nil ->
  shl_one_bit (a ++ b) = false :: a ++ removelast b.
Proof. intro a.
       induction a; intros.
       - cbn. rewrite shl_one; easy.
       - cbn. case_eq a0; case_eq b; intros.
         subst. now contradict H.
         subst. rewrite !app_nil_l. easy.
         subst. now contradict H.
         subst. rewrite <- app_comm_cons.
         f_equal. f_equal.
         rewrite <- removelast_app. easy. easy.
Qed.

Lemma removelast_one: forall (a: list bool),
 removelast (firstn 1 a) = nil.
Proof. intro a.
       induction a; intros; now cbn.
Qed.

Lemma shl_one_bit_all_false: forall (a: list bool),
shl_one_bit (mk_list_false (length a)) = mk_list_false (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - Reconstr.rblast (@RAWBITVECTOR_LIST.mk_list_false_cons, 
           @RAWBITVECTOR_LIST.shl_one_b, 
           @Coq.Lists.List.length_zero_iff_nil) 
          (@Coq.Init.Datatypes.length,
           @RAWBITVECTOR_LIST.mk_list_false).
Qed.

Lemma firstn_neq_nil: forall n (a: list bool),
a <> nil -> (n%nat <> 0%nat) -> firstn n a <> [].
Proof. intro n.
       induction n; intros.
       - cbn in *. easy.
       - Reconstr.reasy Reconstr.Empty (@Coq.Lists.List.firstn).
Qed.

Theorem bv_shl_aux_eq: forall n a, shl_n_bits a n = shl_n_bits_a a n.
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. now cbn.
         cbn. now rewrite firstn_all.
       - cbn. rewrite shl_n_shl_one_comm, IHn.
         unfold shl_n_bits_a.
         case_eq ((S n <? length a)%nat); intros.
         assert ((n <? length a)%nat = true).
         { apply Nat.ltb_lt in H.
           apply Nat.ltb_lt. lia.
         }
         rewrite H0. cbn. case_eq a; intros.
         subst. cbn in *. now contradict H.
         rewrite shl_one_bit_app.
         f_equal. f_equal.
         set (m := (length (b :: l) - S n)%nat).
         assert (((length (b :: l) - n)%nat = (S m)%nat)).
         { unfold m in *.
           case_eq n; intros. cbn. now rewrite Nat.sub_0_r.
           cbn. 
           rewrite <- Nat.sub_succ_l. easy.
           rewrite <- H2.
           rewrite H1 in H, H0.
           simpl in H, H0.
           apply PeanoNat.Nat.ltb_lt in H0.
           lia.
         }
         rewrite H2, removelast_firstn. easy.
         unfold m.
         Reconstr.rexhaustive1 (@Coq.Arith.PeanoNat.Nat.le_sub_l) (@Coq.Init.Peano.lt, @m).
         cbn. case_eq n; intros. subst; cbn in *. easy.
         subst. apply Nat.ltb_lt in H. apply Nat.ltb_lt in H0.
         apply firstn_neq_nil. easy.
         Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt,
           @Coq.Arith.PeanoNat.Nat.sub_succ) (@Coq.Init.Datatypes.length).
         case_eq ((n <? length a)%nat); intros.
         assert (length a = S n).
         { apply Nat.ltb_lt in H0.
           apply Nat.ltb_ge in H.
           lia.
         } rewrite H1.
         rewrite shl_one_bit_app.
         assert ((S n - n)%nat = 1%nat) by lia.
         rewrite H2, removelast_one, app_nil_r. easy.
         apply firstn_neq_nil.
         Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length).
         lia.
         now rewrite shl_one_bit_all_false.
Qed.

Lemma ult_list_be_cons_false: forall a b c,
length a = length b ->
ult_list_big_endian (c :: a) (c :: b) = false -> ult_list_big_endian a b = false.
Proof. intro a. 
       induction a; intros.
       - now cbn.
       - case_eq b; intros. subst. now contradict H.
         subst. cbn.
         case_eq a0; intros.
         subst. assert (l = nil) .
         { 	Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length). }
         subst.  cbn in *.
         Reconstr.rsimple Reconstr.Empty (@Coq.Init.Datatypes.negb, 
           @Coq.Init.Datatypes.orb, @Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb).
         rewrite <- H1 in *. cbn in H0.
         case_eq a0; intros.
         subst. now contradict H2.
         subst. rewrite <- H2. 
         assert ( eqb c c = true).
         Reconstr.reasy Reconstr.Empty (@Coq.Bool.Bool.eqb).
         rewrite H1 in H0. 
         assert (negb c && c = false) by 
         Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.negb, @Coq.Init.Datatypes.andb).
         rewrite H3 in H0.
 	       Reconstr.rcrush (@Coq.Bool.Bool.negb_true_iff, @Coq.Bool.Bool.orb_false_iff, 
           @Coq.Bool.Bool.andb_true_l) (@Coq.Init.Datatypes.negb, @Coq.Init.Datatypes.orb, 
           @Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb).
Qed.


Lemma ult_list_big_endian_unf: forall a b c d,
ult_list_big_endian (c :: a) (d :: b) =
orb (andb (Bool.eqb c d) (ult_list_big_endian a b))
    (andb (negb c) d).
Proof. intro a.
       case_eq a; intros.
       + cbn in *. case_eq b; intros. 
         Reconstr.reasy (@Coq.Bool.Bool.andb_false_r) 
          (@Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb, @Coq.Init.Datatypes.orb).
         Reconstr.reasy Reconstr.Empty Reconstr.Empty.
       + cbn in *. case_eq b0; intros; easy.
Qed.

Theorem bv_shl_eq: forall (a b : bitvector),
  bv_shl a b = bv_shl_a a b.
Proof. intros.
       unfold bv_shl, bv_shl_a.
       case_eq (size a =? size b); intros; try easy.
       unfold shl_aux.
       now rewrite bv_shl_aux_eq.
Qed.

Lemma list2N_app_true: forall a,
N.to_nat (list2N (a ++ [true])) = ((N.to_nat (list2N a))%nat + Nat.pow 2 (length a))%nat.
Proof. intro a.
        induction a; intros.
        - cbn. Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
        - cbn. case_eq a; intros.
          + rewrite !N2Nat.inj_succ_double, IHa. cbn.
            rewrite <- !plus_n_O.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_shuffle1) Reconstr.Empty.
          + rewrite !N2Nat.inj_double. rewrite IHa.
            cbn. rewrite <- !plus_n_O.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_shuffle1) Reconstr.Empty.
Qed.

Lemma list2N_app_false: forall a,
N.to_nat (list2N (a ++ [false])) = (N.to_nat (list2N a)).
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq a; intros.
          + rewrite !N2Nat.inj_succ_double, IHa. now cbn.
          + rewrite !N2Nat.inj_double. now rewrite IHa.
Qed.

Lemma ltb_plus: forall (a b n: nat), (a <? b)%nat = (a + n <? b + n)%nat.
Proof. intros. revert a b.
        induction n; intros.
        + now rewrite <- !plus_n_O.
        + cbn. case_eq b; intros.
          cbn. symmetry. rewrite leb_iff_conv. lia. 
          cbn. 
       	  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_succ_r,
            @Coq.Arith.PeanoNat.Nat.leb_antisym, @Coq.Arith.PeanoNat.Nat.ltb_antisym, 
            @Coq.Arith.PeanoNat.Nat.add_succ_l) (@Coq.Init.Nat.ltb).
Qed.

Lemma pow_gt: forall a,
((N.to_nat (list2N a))%nat <? (2 ^ length a)%nat)%nat = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq a; intros.
          + rewrite <- plus_n_O. 
            case_eq ((2 ^ length a0 + 2 ^ length a0)%nat); intros.
            ++ contradict H0.
               Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                  @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
            ++ rewrite !N2Nat.inj_succ_double. cbn.
                case_eq n; intros.
                +++ subst. contradict H0.
                     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_l, 
                        @Coq.Arith.PeanoNat.Nat.add_succ_r,
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                +++ rewrite <- plus_n_O. rewrite H1 in *.
                    assert (((S (S (N.to_nat (list2N a0) + N.to_nat (list2N a0))))%nat <=? (S (S n0))%nat)%nat = true).
                    rewrite <- H0. rewrite Nat.ltb_lt in IHa.
                    rewrite Nat.leb_le. lia.
                    rewrite Nat.leb_le in H2.
                    rewrite Nat.leb_le. 
	                  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_l, 
                      @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Peano.lt).
          + rewrite <- plus_n_O.
            case_eq ((2 ^ length a0 + 2 ^ length a0)%nat); intros.
            ++ contradict H0.
                Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                  @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
            ++ rewrite !N2Nat.inj_double. cbn.
                case_eq n; intros.
                +++ subst. contradict H0.
                     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_l, 
                        @Coq.Arith.PeanoNat.Nat.add_succ_r,
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                +++ rewrite <- plus_n_O. rewrite H1 in *.
                    assert (((S (S (N.to_nat (list2N a0) + N.to_nat (list2N a0))))%nat <=? (S (S n0))%nat)%nat = true).
                    rewrite <- H0. rewrite Nat.ltb_lt in IHa.
                    rewrite Nat.leb_le. lia.
                    rewrite Nat.leb_le in H2.
                    rewrite Nat.leb_le. 
	                  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_l, 
                      @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Peano.lt).
Qed.

(* Axiom bv_ult_nat: forall n a b, (size a) = n -> (size b) = n -> 
  (bv_ult a b) = (bv2nat_a a <? bv2nat_a b)%nat. *)


Lemma bv_ult_nat: forall a b,
    ((size a) =? (size b)) = true ->
    bv_ult a b = (((bv2nat_a a)%nat <? (bv2nat_a b)%nat))%nat.
Proof. intros a b H0. unfold bv_ult, size in *.
        rewrite H0.
        assert (H: length a = length b).
        Reconstr.rcrush (@Coq.setoid_ring.InitialRing.Neqb_ok, 
          @Coq.NArith.Nnat.Nat2N.id) (@RAWBITVECTOR_LIST.bitvector).
        clear H0.
         unfold bv2nat_a, list2nat_be_a, ult_list.
         revert b H.
         induction a using rev_ind; intros.
         - cbn in *.
	         Reconstr.rsimple (@Coq.NArith.Nnat.Nat2N.id, @RAWBITVECTOR_LIST.list2N_mk_list_false)
             (@RAWBITVECTOR_LIST.mk_list_false, @Coq.Init.Datatypes.length, @Coq.NArith.BinNatDef.N.of_nat).
         - induction b using rev_ind; intros.
           + cbn in *. contradict H.
             Reconstr.rcrush Reconstr.Empty 
              (@Coq.Init.Datatypes.length, @Coq.Init.Datatypes.app).
           + rewrite !rev_app_distr. cbn.
             case_eq (rev a); intros.
             ++ assert (rev b = nil).
                 { rewrite !length_app in H. cbn in H.
                   assert (a = nil) by Reconstr.rsimple (@Coq.Lists.List.app_nil_r,
                             @Coq.Lists.List.rev_app_distr, @Coq.Lists.List.rev_involutive)
                             Reconstr.Empty.
                   assert (length b = O). subst. cbn in *. lia.
                   Reconstr.rcrush Reconstr.Empty (@Coq.Init.Datatypes.length).
                   }
                rewrite H1.
                assert (a = nil).
                Reconstr.reasy (@Coq.Lists.List.rev_involutive, @Coq.Lists.List.rev_app_distr, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
                assert (b = nil).
                Reconstr.reasy (@Coq.Lists.List.rev_involutive, @Coq.Lists.List.rev_app_distr, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
                rewrite H2, H3. cbn.
                case_eq x; case_eq x0; intros; cbn; try easy.
             ++ rewrite <- H0, IHa.
                case_eq ((N.to_nat (list2N a) <? N.to_nat (list2N b))%nat); intro HH.
                * case_eq x; case_eq x0; intros.
                  ** cbn. rewrite !list2N_app_true.
                      specialize (ltb_plus (N.to_nat (list2N a)) (N.to_nat (list2N b))
                      (2 ^ length b)); intros. rewrite H3 in HH.
                      case_eq ((N.to_nat (list2N b) + 2 ^ length b)%nat); intros.
                      contradict H4.
                      Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1, 
                        @Coq.Arith.PeanoNat.Nat.pow_nonzero) (@Coq.Init.Nat.add).
                      apply Nat.ltb_lt in HH. rewrite H4 in HH.
                      assert (length a = length b). rewrite !length_app in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                      rewrite H5. 
                    	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le, 
                       @Coq.Arith.PeanoNat.Nat.lt_succ_r, 
                       @Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !length_app in H.
                     cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                       @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4.
                     specialize (pow_gt b); intro Hb.
                     rewrite H3 in Hb.
                     rewrite Nat.ltb_lt in Hb. symmetry.
                     rewrite Nat.leb_gt. lia.
                  ** cbn. rewrite list2N_app_true, list2N_app_false.
                      case_eq ((N.to_nat (list2N b) + 2 ^ length b)%nat); intros.
                      contradict H3.
                    	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1, 
                        @Coq.Arith.PeanoNat.Nat.pow_nonzero) (@Coq.Init.Nat.add).
                      symmetry. rewrite Nat.leb_le. rewrite Nat.ltb_lt in HH.
                     specialize (pow_gt a); intro Ha.
                     assert (S (N.to_nat (list2N a)) <= S n)%nat.
                     rewrite <- H3. rewrite Nat.ltb_lt in Ha.
                      assert (length a = length b). rewrite !length_app in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4 in Ha. lia.
                     lia.
                  ** cbn. rewrite !list2N_app_false.
                      case_eq (N.to_nat (list2N b)); intros.
                      contradict HH. rewrite H3.
                      Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_lt) (@Coq.Init.Peano.lt).
                      symmetry. rewrite Nat.leb_le.
                      rewrite Nat.ltb_lt in HH.
                      Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_r) Reconstr.Empty.
                * case_eq x; case_eq x0; intros.
                  ** cbn. rewrite !list2N_app_true.
                      case_eq ((N.to_nat (list2N b) + 2 ^ length b)%nat); intros.
                      easy.
                      symmetry. rewrite Nat.leb_gt.
                      assert ((S n < S (N.to_nat (list2N a) + 2 ^ length a))%nat).
                      rewrite <- H3.
                      rewrite Nat.ltb_ge in HH.
                      assert (( (N.to_nat (list2N a)) < S (N.to_nat (list2N a)))%nat).
                      lia. 
                      assert (length a = length b). rewrite !length_app in H.
                      cbn in H. Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.add_succ_r, 
                                 @Coq.Init.Peano.plus_n_O) Reconstr.Empty.
                      rewrite H5. lia. lia.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !length_app in H.
                     cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                       @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4.
                     specialize (pow_gt b); intro Hb.
                     rewrite H3 in Hb.
                     rewrite Nat.ltb_lt in Hb. symmetry.
                     rewrite Nat.leb_gt. lia.
                  ** cbn. rewrite list2N_app_true, list2N_app_false.
                      case_eq ((N.to_nat (list2N b) + 2 ^ length b)%nat); intros.
                      contradict H3.
                      specialize (pow_gt b); intro Hb. rewrite Nat.ltb_lt in Hb.
            	        Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                      symmetry. rewrite Nat.leb_le. rewrite Nat.ltb_ge in HH.
                      specialize (pow_gt a); intro Ha.
                      assert (S (N.to_nat (list2N a)) <= S n)%nat.
                      rewrite <- H3. rewrite Nat.ltb_lt in Ha.
                      assert (length a = length b). rewrite !length_app in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                      rewrite H4 in Ha. lia.
                      lia.
                  ** cbn. rewrite !list2N_app_false.
                      case_eq (N.to_nat (list2N b)); intros.
                      easy.
                      symmetry. rewrite Nat.leb_gt.
                      rewrite Nat.ltb_ge in HH.
                      Reconstr.reasy Reconstr.Empty (@Coq.Init.Peano.lt).
                * rewrite !length_app in H. cbn in H. 
                  Reconstr.reasy (@Coq.Init.Peano.plus_n_Sm, @Coq.Init.Peano.plus_n_O) 
                   Reconstr.Empty.
Qed.

Lemma last_mk_list_false: forall n, last (mk_list_false n) false = false.
Proof. intro n.
        induction n; intros.
        - now cbn.
        - cbn. case_eq ( mk_list_false n ); intros.
          + easy.
          + now rewrite <- H.
Qed.

Lemma last_mk_list_true: forall n, (n <> 0)%nat -> last (mk_list_true n) false = true.
Proof. intro n.
        induction n; intros.
        - now cbn.
        - cbn. case_eq ( mk_list_true n ); intros.
          + easy.
          + rewrite <- H0. apply IHn. 
            Reconstr.reasy Reconstr.Empty (@RAWBITVECTOR_LIST.mk_list_true).
Qed.

Lemma last_shl_zeros: forall n,
last (shl_n_bits_a (mk_list_false n) n) false = false.
Proof. intro n.
        induction n; intros.
        + now cbn.
        + cbn. unfold shl_n_bits_a. cbn.
          rewrite length_mk_list_false.
          case_eq n; intros.
          easy.
          assert ((S n0 <=? n0)%nat = false).
          rewrite Nat.leb_gt. lia.
          rewrite H0. cbn.
          case_eq (mk_list_false n0); intros.
          easy. 
          now rewrite <- H1, last_mk_list_false.
Qed.

Lemma last_append: forall (a b: list bool) c, b <> nil -> last (a ++ b) c = last b c.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq (a0 ++ b); intros.
          + contradict H0. 
         	  Reconstr.rsimple Reconstr.Empty (@Coq.Init.Datatypes.app).
          + specialize (IHa b c). rewrite H0 in IHa.
            apply IHa. easy.
Qed.

Lemma last_fristn_skipn: forall a n,
(n <? length a)%nat = true ->
last (firstn (length a - n) (skipn n a)) false = last a false.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq n; intros.
          + cbn. rewrite firstn_all.
            easy.
          + cbn. rewrite IHa.
            case_eq a0; intros.
            ++ cbn in H. subst. now contradict H.
            ++ easy.
            ++ subst.
               Reconstr.reasy (@Nat.succ_lt_mono, @Coq.Arith.PeanoNat.Nat.ltb_lt) 
               (@Coq.Init.Datatypes.length).
Qed.

Lemma last_skipn_false: forall a n,
(n <? length a)%nat = true ->
last (shl_n_bits_a (skipn n a ++ mk_list_false n) n) false = last a false.
Proof. intros.
        unfold shl_n_bits_a.
        assert (length (skipn n a ++ mk_list_false n) = length a).
        rewrite length_app, length_skipn, length_mk_list_false.
        rewrite Nat.ltb_lt in H.
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_add, 
         @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
        rewrite H0, H. rewrite last_append.
        rewrite firstn_app. rewrite length_skipn.
        assert ((length a - n - (length a - n))%nat = O).
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty.
        rewrite H1. cbn. rewrite app_nil_r.
        rewrite last_fristn_skipn. easy.
        easy. rewrite Nat.ltb_lt in H. apply firstn_neq_nil.
     	  Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Init.Peano.le_n,  
          @Coq.Lists.List.length_zero_iff_nil, @RAWBITVECTOR_LIST.length_mk_list_false,
          @Coq.Arith.PeanoNat.Nat.leb_gt) (@Coq.Init.Datatypes.app).
        Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt) Reconstr.Empty.
Qed.

Lemma last_skipn_true: forall a n,
(n <? length a)%nat = true ->
last (shl_n_bits_a (skipn n a ++ mk_list_true n) n) false = last a false.
Proof. intros.
        unfold shl_n_bits_a.
        assert (length (skipn n a ++ mk_list_true n) = length a).
        rewrite length_app, length_skipn, length_mk_list_true.
        rewrite Nat.ltb_lt in H.
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_add, 
         @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
        rewrite H0, H. rewrite last_append.
        rewrite firstn_app. rewrite length_skipn.
        assert ((length a - n - (length a - n))%nat = O).
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty.
        rewrite H1. cbn. rewrite app_nil_r.
        rewrite last_fristn_skipn. easy.
        easy. rewrite Nat.ltb_lt in H. apply firstn_neq_nil.
     	  Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Init.Peano.le_n,  
          @Coq.Lists.List.length_zero_iff_nil, @RAWBITVECTOR_LIST.length_mk_list_false,
          @Coq.Arith.PeanoNat.Nat.leb_gt) (@Coq.Init.Datatypes.app).
        Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt) Reconstr.Empty.
Qed.

Lemma list_lt_false: forall a,
  (N.to_nat (list2N a) <? N.to_nat (list2N (mk_list_false (length a))))%nat = false.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. rewrite list2N_mk_list_false. now cbn.
Qed.

Lemma skip1: forall n (s: list bool) a, skipn n s = skipn (S n) (a :: s).
Proof. intro n.
        induction n; intros.
        - now cbn.
        - cbn. case_eq s; intros; easy.
Qed.


Lemma list_cases_all_true: forall l, 
  l = mk_list_true (length l) \/ l <> mk_list_true (length l).
Proof. induction l; intros.
        - now left.
        - cbn. destruct IHl as [IHl | IHl].
          + case_eq a; intros.
            left. now rewrite IHl at 1.
            now right.
          + case_eq a; intros.
            right. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            right. easy.
Qed.

Lemma list_cases_all_false: forall l, 
  l = mk_list_false (length l) \/ l <> mk_list_false (length l).
Proof. induction l; intros.
        - now left.
        - cbn. destruct IHl as [IHl | IHl].
          + case_eq a; intros.
            now right.
            left. now rewrite IHl at 1.
          + case_eq a; intros.
            right. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            right. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
Qed.

Lemma n_cases_all: forall n, n = O \/ n <> O.
Proof. intro n.
        case_eq n; intros; [ now left | now right ].
Qed.

Lemma n_cases_all_gt: forall n, n = O \/ (0 <? n)%nat = true.
Proof. intros. 
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_lt, 
          @Coq.Arith.PeanoNat.Nat.eq_0_gt_0_cases) Reconstr.Empty.
Qed.

Lemma nm_cases_all: forall n m, (n <? m)%nat = true \/ 
                                    (n =? m)%nat = true \/
                                     (m <? n)%nat = true.
Proof. intro n.
        induction n; intros.
        - case_eq m; intros.
          + right. left. easy.
          + left.
            Reconstr.reasy (@RAWBITVECTOR_LIST.n_cases_all_gt) Reconstr.Empty.
        - case_eq m; intros.
          + right.
            Reconstr.reasy (@RAWBITVECTOR_LIST.n_cases_all_gt) Reconstr.Empty.
          + Reconstr.rcrush (@Nat.eqb_refl, 
               @Coq.Arith.PeanoNat.Nat.add_1_r,
               @Coq.PArith.Pnat.Pos2Nat.inj_1, 
               @RAWBITVECTOR_LIST.ltb_plus,  
               @Nat.eqb_eq) Reconstr.Empty.
Qed.

Lemma skipn_same_mktr: forall n, 
skipn n (mk_list_true n) ++ mk_list_true n = mk_list_true n.
Proof. induction n; intros.
        - now cbn.
        - cbn in *.
          assert (true :: mk_list_true n = mk_list_true n ++ [true]).
	        Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_true_succ, 
            @RAWBITVECTOR_LIST.mk_list_true_app) Reconstr.Empty.
          now rewrite H, app_assoc, IHn.
Qed.

Lemma skipn_gt_false: forall n,
(N.to_nat (list2N (mk_list_true n)) <? 
 N.to_nat (list2N (skipn n (mk_list_true n) ++ mk_list_true n)))%nat = false.
Proof. intros. rewrite skipn_same_mktr.
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_irrefl) 
          Reconstr.Empty.
Qed.

Lemma true_val_list: forall l,
(N.to_nat (list2N (true :: l)) = (N.to_nat (N.succ_double (list2N l))))%nat.
Proof. induction l; intros; now cbn. Qed.

Lemma false_val_list: forall l,
(N.to_nat (list2N (false :: l)) = (N.to_nat (N.double (list2N l))))%nat.
Proof. induction l; intros; now cbn. Qed.


Lemma skipn_nil: forall {A: Type} n, @skipn A n nil = nil.
Proof. intros.
        induction n; intros; now cbn.
Qed.

Lemma skip0: forall {A: Type} l, @skipn A 0 l = l.
Proof. intros. 
        induction l; intros; now cbn.
Qed.

Lemma skipn_true_list: forall n l,
  (skipn n l ++ true :: mk_list_true n) = (skipn n l ++ mk_list_true n) ++ [true].
Proof. intro n.
        induction n; intros.
        - cbn. Reconstr.reasy (@Coq.Lists.List.app_nil_r) Reconstr.Empty.
        - cbn. case_eq l; intros.
          + cbn. Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_true_succ,
                  @RAWBITVECTOR_LIST.mk_list_true_app) Reconstr.Empty.
          + Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_true_app, 
              @RAWBITVECTOR_LIST.mk_list_true_succ, 
              @Coq.Lists.List.app_comm_cons, 
              @Coq.Lists.List.app_assoc) Reconstr.Empty.
Qed.

Lemma skipn_true_val_list: forall n l,
(n <? length l)%nat = true ->
(N.to_nat (list2N (skipn n l ++ true :: mk_list_true n)) = 
 N.to_nat (list2N (skipn n l ++ mk_list_true n)) + Nat.pow  2 (length l))%nat.
Proof. intros. rewrite skipn_true_list, list2N_app_true.
        rewrite length_app, length_skipn, length_mk_list_true.
	      Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_add, 
          @Coq.Arith.PeanoNat.Nat.ltb_lt, 
          @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
Qed.

Lemma skipn_false_list: forall n l,
  (skipn n l ++ false :: mk_list_false n) = (skipn n l ++ mk_list_false n) ++ [false].
Proof. intro n.
        induction n; intros.
        - cbn. Reconstr.reasy (@Coq.Lists.List.app_nil_r) Reconstr.Empty.
        - cbn. case_eq l; intros.
          + cbn. f_equal.
          	Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_false_cons) Reconstr.Empty.
          + cbn. 
            Reconstr.reasy (@Coq.Lists.List.app_assoc, @Coq.Lists.List.app_comm_cons,
              @RAWBITVECTOR_LIST.mk_list_false_cons) Reconstr.Empty.
Qed.

Lemma skipn_false_val_list: forall n l,
(n <? length l)%nat = true ->
(N.to_nat (list2N (skipn n l ++ false :: mk_list_false n)) = 
 N.to_nat (list2N (skipn n l ++ mk_list_false n)))%nat.
Proof. intros.
        now rewrite skipn_false_list, list2N_app_false.
Qed.


Lemma pow_eqb_1: forall n,
((S (N.to_nat (list2N (mk_list_true n))))%nat =? (2 ^ n))%nat = true.
Proof. intros.
        induction n; intros.
        - now cbn.
        - cbn in *.
          case_eq ((2 ^ n)%nat); intros.
          + rewrite H in *. easy.
          + rewrite H in *. cbn.
            rewrite N2Nat.inj_succ_double.
            apply Nat.eqb_eq in IHn.
            rewrite IHn.
            apply Nat.eqb_eq. 
	          Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.add_succ_r, 
              @Coq.Arith.PeanoNat.Nat.mul_1_l,
              @Coq.Arith.PeanoNat.Nat.add_0_r,
              @Coq.Arith.PeanoNat.Nat.mul_succ_l, 
              @Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
Qed.

Lemma pow_eqb_0: forall n,
(((N.to_nat (list2N (mk_list_true n))))%nat = (2 ^ n) - 1)%nat.
Proof. intros. specialize (pow_eqb_1 n); intros.
        rewrite Nat.eqb_eq in H. rewrite <- H.
        cbn. lia.
Qed.

Lemma pow_gtb_1: forall l,
l <> mk_list_true (length l) ->
((S (N.to_nat (list2N l))) <? 2 ^ length l = true)%nat.
Proof. intro l.
        induction l; intros.
        - cbn in *. easy.
        - case_eq a; intros.
          + assert ( l <> mk_list_true (length l)).
            subst. cbn in H.
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            specialize (IHl H1).
            rewrite true_val_list.
            rewrite N2Nat.inj_succ_double.
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in IHl.
            cbn. lia.
          + destruct (list_cases_all_true l).
            * rewrite H1.
              specialize (pow_eqb_1 (length l)); intros.
              rewrite !false_val_list.
              rewrite !N2Nat.inj_double. 
              assert (length (false :: mk_list_true (length l)) = 
                      S (length l)).
              Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_l)
               (@Coq.Init.Datatypes.length, 
                @RAWBITVECTOR_LIST.mk_list_true).
              rewrite H3.
              apply Nat.eqb_eq in H2.
              Reconstr.reasy (@RAWBITVECTOR_LIST.length_mk_list_true, 
                 @Coq.NArith.Nnat.N2Nat.inj_succ_double,
                 @RAWBITVECTOR_LIST.true_val_list,
                 @RAWBITVECTOR_LIST.pow_gt,
                 @RAWBITVECTOR_LIST.mk_list_true_cons) Reconstr.Empty.
            * rewrite !false_val_list.
              rewrite !N2Nat.inj_double.
              assert (length (false :: l) = 
                      S (length l)).
              Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length).
              rewrite H2.
              specialize (IHl H1).
              apply Nat.ltb_lt.
              apply Nat.ltb_lt in IHl. 
              cbn. lia.
Qed.

Lemma skipn_nm: forall n m,
(n <? m)%nat = true ->
(skipn n (mk_list_true m) ++ mk_list_true n) = (mk_list_true m).
Proof. intro n.
        induction n; intros.
        - cbn. now rewrite app_nil_r.
        - cbn. case_eq m; intros.
          + subst. easy. 
          + cbn. rewrite <- IHn at 2.
          	Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.inj_1,
               @RAWBITVECTOR_LIST.ltb_plus, 
               @RAWBITVECTOR_LIST.mk_list_true_app, 
               @RAWBITVECTOR_LIST.mk_list_true_succ, 
               @RAWBITVECTOR_LIST.skipn_true_list, 
               @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_irrefl)
              (@Coq.Init.Nat.leb, @Coq.Init.Nat.ltb).
Qed.

Lemma skipn_nm_false: forall n m,
(n <? m)%nat = true ->
(skipn n (mk_list_false m) ++ mk_list_false n) = (mk_list_false m).
Proof. intro n.
        induction n; intros.
        - cbn. now rewrite app_nil_r.
        - cbn. case_eq m; intros.
          + subst. easy. 
          + cbn. rewrite <- IHn at 2.
    	      Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.inj_1, 
              @RAWBITVECTOR_LIST.ltb_plus, 
              @RAWBITVECTOR_LIST.mk_list_false_cons, 
              @RAWBITVECTOR_LIST.skipn_false_list, 
              @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_irrefl)
              (@Coq.Init.Nat.leb, @Coq.Init.Nat.ltb).
Qed.

Lemma skipn_gt: forall n s,
(n <> 0)%nat ->
(n <? length s)%nat = true ->
s <> mk_list_true (length s) ->
(N.to_nat (list2N s) <? 
 N.to_nat (list2N (skipn n s ++ mk_list_true n)))%nat = true.
Proof. intro n.
        induction n as [ | n IHn ]; intros.
        - simpl in *. easy.
        - simpl in *.
          case_eq s; intros.
          + subst. easy.
          + rewrite skipn_true_val_list.
            specialize (IHn l).
            case_eq b; intros.
            subst. rewrite true_val_list.
            rewrite N2Nat.inj_succ_double.

            destruct (n_cases_all n).
            rewrite H2. rewrite skip0.
            assert (mk_list_true 0 = nil) by easy.
            rewrite H3, app_nil_r.
            specialize (pow_gt l); intros.

            apply Nat.ltb_lt.
            apply Nat.ltb_lt in H4. cbn.
            specialize (@pow_gtb_1 l); intros.
            assert (l <> mk_list_true (length l)).
            cbn in H1.
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            specialize (H5 H6). rewrite <- plus_n_O.
            apply Nat.ltb_lt in H5.
            cbn. lia.

            assert (l <> mk_list_true (length l)).
            cbn in H1.
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            assert ((n <? length l)%nat = true).
            cbn in H0.
         	  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_r,
              @Coq.Arith.PeanoNat.Nat.ltb_lt,
              @Coq.Arith.PeanoNat.Nat.leb_le) Reconstr.Empty.
            specialize (IHn H2 H4 H3).
            specialize (pow_gt l); intros.
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in IHn.
            apply Nat.ltb_lt in H5.
            cbn. lia.

            destruct (list_cases_all_true l).
            rewrite false_val_list.
            rewrite H4.
            rewrite N2Nat.inj_double.
            apply Nat.ltb_lt. rewrite skipn_nm.
            Reconstr.rexhaustive1 (@Coq.NArith.Nnat.N2Nat.inj_succ_double,
              @RAWBITVECTOR_LIST.list2N_app_true, 
              @RAWBITVECTOR_LIST.mk_list_true_app,
              @RAWBITVECTOR_LIST.mk_list_true_cons, 
              @RAWBITVECTOR_LIST.true_val_list, @Coq.Init.Peano.le_n) 
            (@Coq.Init.Peano.lt, @Coq.Init.Datatypes.length).
            simpl in H0.
            Reconstr.reasy (@RAWBITVECTOR_LIST.length_mk_list_true) 
              (@Coq.Init.Datatypes.length,
               @Coq.Init.Nat.leb, @RAWBITVECTOR_LIST.mk_list_true, 
               @Coq.Init.Nat.ltb).
            destruct (n_cases_all n).
            subst.
            rewrite false_val_list.
            rewrite N2Nat.inj_double.
            rewrite skip0.
            assert (mk_list_true 0 = nil) by easy.
            rewrite H2, app_nil_r.
            specialize (pow_gt l); intros.
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in H3.
            cbn. lia.
            rewrite false_val_list.
            assert ((n <? length l)%nat = true).
            subst. cbn in H0. 
	          Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le, 
              @Coq.Arith.PeanoNat.Nat.lt_succ_r,
              @Coq.Arith.PeanoNat.Nat.ltb_lt) Reconstr.Empty.
            specialize (IHn H5 H6 H4).
            specialize (pow_gt l); intros.
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in IHn.
            apply Nat.ltb_lt in H7.
            rewrite N2Nat.inj_double.
            cbn. lia.

            subst. cbn in *. 
            easy.
Qed.

Lemma pow_ltb: forall l,
l <> mk_list_true (length l) ->
(N.to_nat (list2N l) <? 
 N.to_nat (list2N (mk_list_true (length l))) = true)%nat.
Proof. intros. rewrite pow_eqb_0.
        specialize (@pow_gtb_1 l H); intros.
        apply Nat.ltb_lt.
        apply Nat.ltb_lt in H0. lia.
Qed.

Lemma pow_ltb_false: forall l,
(N.to_nat (list2N (mk_list_true (length l))) <?
 N.to_nat (list2N l) = false)%nat.
Proof. intros. rewrite pow_eqb_0.
        destruct (list_cases_all_true l).
        - rewrite H at 2.
	        Reconstr.reasy (@RAWBITVECTOR_LIST.pow_eqb_0, 
            @RAWBITVECTOR_LIST.skipn_same_mktr, 
            @RAWBITVECTOR_LIST.skipn_gt_false) Reconstr.Empty.
        - specialize (@pow_gtb_1 l H); intros.
          apply Nat.ltb_lt in H0.
          Reconstr.rscrush (@Coq.Arith.PeanoNat.Nat.add_1_r, 
           @Coq.Arith.PeanoNat.Nat.ltb_lt, 
           @Coq.Arith.PeanoNat.Nat.neq_0_lt_0, 
           @Coq.Arith.PeanoNat.Nat.pow_nonzero, 
           @Coq.Arith.PeanoNat.Nat.sub_add, 
           @Coq.PArith.Pnat.Pos2Nat.inj_1, 
           @RAWBITVECTOR_LIST.pow_gt,
           @Coq.Arith.Compare_dec.leb_correct_conv) 
          (@Coq.Init.Peano.lt, 
           @RAWBITVECTOR_LIST.list2nat_be_a, 
           @Coq.Init.Nat.ltb).
Qed.

Lemma pow_ltb_false_gen: forall (l s: list bool),
length s = length l ->
(N.to_nat (list2N (mk_list_true (length l))) <?
 N.to_nat (list2N s) = false)%nat.
Proof. intros. rewrite pow_eqb_0.
        Reconstr.reasy (@RAWBITVECTOR_LIST.pow_ltb_false,
         @RAWBITVECTOR_LIST.pow_eqb_0) Reconstr.Empty.
Qed.


Lemma  bv2nat_gt0: forall t a, (a <? bv2nat_a t)%nat = true -> 
t <> mk_list_false (length t).
Proof. intro t.
        induction t; intros.
        - cbn in *. easy.
        - unfold bv2nat_a, list2nat_be_a in *.
          cbn.
          case_eq a; intros.
          + easy.
          + rewrite H0 in *.
            rewrite false_val_list in H.
            rewrite N2Nat.inj_double in H.
            assert ((Nat.div a0 2 <? N.to_nat (list2N t))%nat = true).
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in H.
            specialize(Nat.Div0.div_lt_upper_bound a0 2 (N.to_nat (list2N t))); intro Ha.
            apply Ha.
            easy.
            specialize (IHt (Nat.div a0 2 ) H1).
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
Qed.

Lemma gt0_nmk_list_false: forall l,
  l <> mk_list_false (length l) ->
  (0 <? (N.to_nat (list2N l)))%nat = true.
Proof. intro l.
        induction l; intros.
        - cbn in *. easy.
        - case_eq a; intros.
          + subst. rewrite true_val_list.
            rewrite N2Nat.inj_succ_double.
            easy.
          + subst. rewrite false_val_list.
            assert (l <> mk_list_false (length l)).
            cbn in H. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            specialize (IHl H0).
            rewrite N2Nat.inj_double.
            Reconstr.reasy (@Coq.NArith.Nnat.N2Nat.inj_double) 
              (@Coq.Init.Nat.ltb, @Coq.Init.Nat.mul, 
               @Coq.Init.Nat.leb, 
               @RAWBITVECTOR_LIST.list2N, @Coq.Init.Nat.add).
Qed.

Lemma skipn_lt: forall n s,
(n <> 0)%nat ->
(n <? length s)%nat = true ->
s <> mk_list_false (length s) ->
(N.to_nat (list2N (skipn n s ++ mk_list_false n)) <?
 N.to_nat (list2N s))%nat = true.
Proof. intro n.
        induction n as [ | n IHn ]; intros.
        - simpl in *. easy.
        - simpl in *.
          case_eq s; intros.
          + subst. easy.
          + rewrite skipn_false_val_list.
            specialize (IHn l).
            case_eq b; intros.
            subst. rewrite true_val_list.
            rewrite N2Nat.inj_succ_double.

            destruct (n_cases_all n).
            rewrite H2. rewrite skip0.
            assert (mk_list_false 0 = nil) by easy.
            rewrite H3, app_nil_r.
            apply Nat.ltb_lt.
            cbn.
            lia.
 
            destruct (list_cases_all_false l).
            rewrite H3. rewrite skipn_nm_false.
            Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Init.Peano.le_n, 
              @Coq.NArith.Nnat.N2Nat.inj_double, 
              @Coq.PArith.Pnat.Pos2Nat.inj_1,
              @RAWBITVECTOR_LIST.false_val_list, 
              @RAWBITVECTOR_LIST.list2N_app_false,
              @RAWBITVECTOR_LIST.list2N_mk_list_false, 
              @RAWBITVECTOR_LIST.mk_list_false_cons, 
              @Coq.Arith.PeanoNat.Nat.lt_succ_r) 
             (@Coq.NArith.BinNatDef.N.to_nat).
            cbn in H0.  
            Reconstr.reasy Reconstr.Empty 
              (@Coq.Init.Nat.leb, @Coq.Init.Nat.ltb).
            assert ((n <? length l)%nat = true ).
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_r, 
              @RAWBITVECTOR_LIST.mk_list_true_cons, 
              @Coq.Arith.PeanoNat.Nat.ltb_lt)
             (@Coq.Init.Peano.lt, @Coq.Init.Datatypes.length, 
              @RAWBITVECTOR_LIST.mk_list_true, 
              @RAWBITVECTOR_LIST.mk_list_false).
            specialize (IHn H2 H4 H3).
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in IHn.
            lia.

            rewrite false_val_list.
            rewrite N2Nat.inj_double.
            destruct (n_cases_all n).
            rewrite H4. rewrite skip0.
            assert (mk_list_false 0 = nil) by easy.
            rewrite H5, app_nil_r.
            assert (l <> mk_list_false (length l)).
            subst. cbn in H1.
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            specialize (@gt0_nmk_list_false l H6); intros.
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in H7. 
            lia.

            assert (l <> mk_list_false (length l)).
            cbn in H1.
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
            assert ((n <? length l)%nat = true).
            cbn in H0.
         	  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_r,
              @Coq.Arith.PeanoNat.Nat.ltb_lt,
              @Coq.Arith.PeanoNat.Nat.leb_le) Reconstr.Empty.
            specialize (IHn H4 H6 H5).
            apply Nat.ltb_lt.
            apply Nat.ltb_lt in IHn.
            cbn. lia.

          	Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length,
              @Coq.Init.Nat.ltb, @Coq.Init.Nat.leb).
Qed.

Lemma slt_list_be_ft: forall a b d,
  length a = length b ->
  hd d a = true -> hd d b = false -> slt_list_big_endian a b = true.
Proof. intro a.
        induction a; intros.
        - subst. cbn in *.
           assert (b = nil).
	         Reconstr.reasy (@Coq.Lists.List.length_zero_iff_nil) 
             Reconstr.Empty.
           subst. now cbn in *.
        - case_eq b; intros.
          + subst. cbn in *. easy.
          + subst. cbn.
            case_eq a0; intros.
            * subst. cbn in *.
              case_eq l; intros.
              ++ subst. easy.
              ++ subst. easy.
            * cbn in *. subst. now cbn.
Qed.


Lemma bv_slt_tf: forall a b,
  size a = size b ->
  last a false = true -> last b false = false -> bv_slt a b = true.
Proof. intros.
        unfold bv_slt.
        rewrite H, N.eqb_refl.
        apply slt_list_be_ft with (d := false).
        - Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id, 
             @Coq.Lists.List.length_rev) 
            (@RAWBITVECTOR_LIST.size, @RAWBITVECTOR_LIST.bitvector).
        - now rewrite hd_rev.
        - now rewrite hd_rev.
Qed.

Lemma bv_slt_false_zeros: forall a, bv_slt a (zeros (size a)) = false -> 
  eqb (last a false) false = true.
Proof. intros.
        unfold bv_slt in H. 
        rewrite zeros_size, N.eqb_refl in H.
        unfold slt_list in H.
        induction a using rev_ind; intros.
        - now cbn.
        - cbn in *. case_eq x; intros.
          + subst. assert ((rev (a ++ [true])) = (true :: rev a)).
            Reconstr.reasy (@Coq.Lists.List.rev_unit) Reconstr.Empty.
            rewrite H0 in H.
            assert ((rev (zeros (size (a ++ [true])))) =  (zeros (size (a ++ [true])))).
            Reconstr.reasy (@RAWBITVECTOR_LIST.rev_mk_list_false) (@RAWBITVECTOR_LIST.zeros, @RAWBITVECTOR_LIST.bitvector).
            rewrite slt_list_be_ft with (d := false) in H.
            easy.
            cbn. rewrite !length_rev. unfold zeros.
            rewrite length_mk_list_false. unfold size.
            rewrite Nat2N.id.
            Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_true_app,
               @RAWBITVECTOR_LIST.length_mk_list_true, 
               @Coq.Lists.List.length_app) Reconstr.Empty.
            now cbn.
            rewrite H1. unfold size, zeros.
            rewrite Nat2N.id.
            Reconstr.rsimple (@Coq.NArith.Nnat.Nat2N.id, 
              @Coq.Lists.List.length_zero_iff_nil) 
             (@RAWBITVECTOR_LIST.mk_list_false, 
              @RAWBITVECTOR_LIST.size, 
              @RAWBITVECTOR_LIST.zeros, @Coq.Lists.List.hd).
           + Reconstr.reasy (@RAWBITVECTOR_LIST.last_app) (@Coq.Bool.Bool.eqb).
Qed.

Lemma ult_list_be_nrefl: forall a, ult_list_big_endian a a = false.
Proof. intro a.
       induction a; intros.
       - easy.
       - cbn. case_eq a0; intros.
         + Reconstr.reasy (@Coq.Bool.Bool.andb_negb_r) Reconstr.Empty.
         + rewrite <- H. rewrite IHa. 
           Reconstr.rsimple (@Coq.Bool.Bool.andb_false_r, 
             @Coq.Bool.Bool.negb_true_iff, 
             @Coq.Bool.Bool.andb_false_l, 
             @Coq.Bool.Bool.eqb_reflx) 
            (@Coq.Init.Datatypes.orb, @Coq.Init.Datatypes.negb).
Qed.


Lemma bv_slt_be_nrefl: forall a, slt_list_big_endian a a = false.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq a0; intros.
         + Reconstr.reasy (@Coq.Bool.Bool.andb_negb_r) Reconstr.Empty.
         + rewrite ult_list_be_nrefl. 
           Reconstr.reasy (@Coq.Bool.Bool.andb_false_r,
             @Coq.Bool.Bool.andb_negb_r) (@Coq.Init.Datatypes.is_true, 
             @Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb, @Coq.Init.Datatypes.orb).
Qed.

Lemma bv_slt_nrefl: forall a, bv_slt a a = false.
Proof. intro a.
       unfold bv_slt.
       rewrite N.eqb_refl.
       induction a; intros.
       - easy.
       - unfold slt_list. cbn in *. now rewrite bv_slt_be_nrefl.
Qed.

Lemma mk_list_false_not_true: forall l,
  l <> mk_list_true (length l) -> bv_not l <> mk_list_false (length l).
Proof. intro l.
        induction l; intros.
        - cbn in *. easy.
        - cbn. 
          Reconstr.rsimple (@RAWBITVECTOR_LIST.mk_list_true_cons, 
            @RAWBITVECTOR_LIST.add_neg_list_carry_neg_f, 
            @RAWBITVECTOR_LIST.add_list_carry_empty_neutral_r) 
           (@Coq.Init.Datatypes.negb).
Qed.

Lemma not_mk_list_false: forall l,
  l <> mk_list_false (length l) -> (0 <? N.to_nat (list2N l))%nat = true.
Proof. intro l.
        induction l; intros.
        - cbn in *. easy.
        - cbn in H. 
          Reconstr.reasy (@RAWBITVECTOR_LIST.gt0_nmk_list_false,
            @Coq.Lists.List.app_nil_r)
           (@RAWBITVECTOR_LIST.list2N,
            @RAWBITVECTOR_LIST.mk_list_false, 
            @Coq.Init.Datatypes.length).
Qed.


Lemma last_bv_ashr_gt0: forall t s,
  size t = size s ->
  (0 <? N.to_nat (list2N t))%nat = true -> last (bv_shr_a s t) false = false.
Proof. intros.
        unfold bv_shr_a,shr_n_bits_a,list2nat_be_a.
        rewrite H, N.eqb_refl.
        case_eq ( (N.to_nat (list2N t) <? length s)%nat); intros.
        - rewrite last_append.
          + Reconstr.reasy (@RAWBITVECTOR_LIST.last_mk_list_false) 
              (@RAWBITVECTOR_LIST.bitvector).
          + Reconstr.reasy (@RAWBITVECTOR_LIST.length_mk_list_false,
               @Coq.Arith.PeanoNat.Nat.ltb_irrefl) 
              (@Coq.Init.Datatypes.negb,
               @RAWBITVECTOR_LIST.mk_list_false, 
               @RAWBITVECTOR_LIST.bitvector).
        - Reconstr.reasy (@RAWBITVECTOR_LIST.last_mk_list_false)
            (@RAWBITVECTOR_LIST.bitvector).
Qed.


Lemma pos_pow: forall n: nat, (n > 0)%nat -> (2^n - 1 >= n)%nat. 
Proof. intro n.
       induction n; intros.
       - easy.
       - cbn. rewrite <- plus_n_O.
         case_eq n; intros.
         + cbn. lia.
         + assert ( (n > 0)%nat ). lia.
           specialize (IHn H1). rewrite H0 in IHn.
           cbn in IHn.  rewrite <- plus_n_O in IHn.
           cbn. lia.
Qed.

Lemma mk_list_false_app_unit: forall a n, list2N (a ++ mk_list_false n) = list2N a.
Proof. intro a.
        induction a; intros.
        - cbn. now rewrite list2N_mk_list_false.
        - cbn. case_eq a; intros; now rewrite IHa.
Qed.


Lemma pos_powN: forall n: N, (N.to_nat n > 0)%nat -> (2^(N.to_nat n) - 1 >= (N.to_nat n))%nat.
Proof. intros. Reconstr.rsimple (@RAWBITVECTOR_LIST.pos_pow) Reconstr.Empty.
Qed.



(* For challenge inv cond bvshr_ugt_rtl *)
Lemma rev_skipn : forall (b : bitvector) (n : nat), 
  (n < length b)%nat -> rev (skipn n b) = firstn (length b - n) (rev b).
Proof.
  induction b.
  + intros n len. now contradict len.
  + intros n len. induction n.
    - rewrite skip0. rewrite Nat.sub_0_r. rewrite <- length_rev. 
      rewrite firstn_all. easy.
    - simpl. simpl in len. apply Nat.succ_lt_mono in len. specialize (@IHb n len).
      rewrite IHb. case n in *.
      * rewrite Nat.sub_0_r. rewrite <- length_rev. rewrite firstn_all.
        rewrite firstn_app. rewrite firstn_all. rewrite Nat.sub_diag.
        rewrite firstn_O. rewrite app_nil_r. easy.
      * apply Nat.lt_le_incl in len. 
        assert (gt0 : (0 < S n)%nat).
        { case n.
          + apply Nat.lt_0_1.
          + intros n0. apply (@Nat.lt_0_succ (S n0)). }
        pose proof (@firstn_removelast bool (length b - S n) (rev b ++ [a])).
        assert (length (rev b ++ [a]) = S (length (rev b))).
        { induction (rev b).
          + easy.
          + rewrite length_app. assert (length [a] = 1)%nat by easy.
            rewrite H0. rewrite Nat.add_1_r. easy. }
        pose proof (@Nat.sub_lt (length b) (S n) len gt0).
        rewrite <- length_rev in H1 at 2. apply Nat.lt_lt_succ_r in H1.
        rewrite <- H0 in H1. specialize (@H H1).
        rewrite <- H. rewrite removelast_app. simpl. rewrite app_nil_r. easy.
        easy.
Qed.

Lemma firstn_succ_mlf : forall (s : bitvector) (n : nat),
  firstn (S n) s = mk_list_false (S n) -> 
  firstn  n s = mk_list_false n.
Proof.
  induction s.
  + intros n H1st. easy.
  + Reconstr.scrush.
Qed.

(* size x = size y <-> length x = length y *)
Theorem size_len_eq : forall (x y : bitvector), size x = size y <-> 
  length x = length y.
Proof.
  intros x y. split.
  + intros H. unfold size in H. now apply Nat2N.inj in H.
  + intros H. unfold size. rewrite H. apply eq_refl.
Qed.



(* Burak's solution *)

Lemma list2N_0_implies_mlf : forall (s : bitvector),
  N.to_nat (list2N s) = 0%nat -> s = mk_list_false (length s).
Proof.
  intros s H. induction s.
  + easy.
  + case a in *.
    - simpl in H. contradict H. case (list2N s); easy.
    - simpl in H. 
      assert (Hdouble : forall (n : N), N.double n = 0 -> n = 0).
      { Reconstr.scrush. }
      apply Nat2N.inj_iff in H. rewrite N2Nat.id in H.
      specialize (@Hdouble (list2N s) H). 
      apply N2Nat.inj_iff in Hdouble. specialize (@IHs Hdouble). 
      Reconstr.scrush.
Qed.

Fixpoint list2NR (a: list bool) (n: nat) :=
  match a with
    | []      => n
    | x :: xs => if x then list2NR xs (2 * n + 1) else list2NR xs (2 * n)
  end.

Definition list2NTR (a: list bool) := list2NR a 0.

Lemma true_list2NR:
  forall (s: bitvector),
  list2NR (true :: s) 0 = list2NR s 1.
Proof. simpl. easy. Qed.

Lemma rl_fact2: forall (s: bitvector) (a: bool),
  s <> nil ->
  removelast (a :: s) = a :: removelast s.
Proof. intro s.
       induction s as [ | x xs IHs] using rev_ind.
       - simpl. easy.
       - intros a H. simpl.  
         case_eq (xs ++ [x]); intros.
         + subst. easy.
         + easy.
Qed.

Lemma list2NR_eqT:
  forall(s: bitvector) n,
  list2NR (s ++ [true]) n = S (2 * list2NR s n).
Proof. intro s.
       induction s; intros.
       - simpl. lia.
       - simpl in *.
         rewrite <- !plus_n_O in *.
         case_eq a; intros.
         + rewrite IHs. lia.
         + rewrite IHs. lia.
Qed.

Lemma list2NR_eqF:
  forall(s: bitvector) n,
  list2NR (s ++ [false]) n = (2 * list2NR s n)%nat.
Proof. intro s.
       induction s; intros.
       - simpl. lia.
       - simpl in *.
         rewrite <- !plus_n_O in *.
         case_eq a; intros.
         + rewrite IHs. lia.
         + rewrite IHs. lia.
Qed.

Lemma list2N_eq:
  forall(s: bitvector),
  list2NTR (rev s) = N.to_nat (list2N s).
Proof. intros s.
       unfold list2NTR.
       induction s; intros.
       - simpl. easy.
       - simpl.
         case_eq a; intros.
         + rewrite N2Nat.inj_succ_double.
           rewrite <- IHs.
           rewrite list2NR_eqT.
           easy.
         + rewrite N2Nat.inj_double.
           rewrite <- IHs.
           rewrite list2NR_eqF.
           easy.
Qed.

Lemma list2N_eq2:
  forall(s: bitvector),
  list2NTR s = N.to_nat (list2N (rev s)).
Proof. intros s.
       unfold list2NTR.
       induction s using rev_ind; intros.
       - simpl. easy.
       - simpl.
         rewrite rev_app_distr.
         simpl.
         case_eq x; intros.
         + rewrite N2Nat.inj_succ_double.
           rewrite <- IHs.
           rewrite list2NR_eqT.
           easy.
         + rewrite N2Nat.inj_double.
           rewrite <- IHs.
           rewrite list2NR_eqF.
           easy.
Qed.


Lemma app_false: forall (s : bitvector),
  list2N s = list2N (s ++ [false]).
Proof. intro s.
       induction s as [ | x xs IHs].
       - simpl. easy.
       - simpl. case_eq x; intros.
         + rewrite IHs. easy.
         + rewrite IHs. easy.
Qed.

Lemma lengthS: 
  forall (s: bitvector) x, length (s ++ [x]) = S (length s).
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl. rewrite IHs. easy.
Qed.

Lemma firstN_app: forall m (s: bitvector) x,
  (length s >= m)%nat -> 
  firstn m s = firstn m (s ++ [x]).
Proof. intro m.
       induction m; intros.
       - simpl. easy.
       - simpl. case_eq s; intros.
         + subst. easy.
         + simpl. rewrite <- IHm.
           easy. subst. simpl in *. lia.
Qed.

Lemma firstN_app15:
 forall m s,
  firstn (S m) s = mk_list_false (S m) ->
  firstn m s = mk_list_false m.
Proof. intros m.
       induction m; intros.
       - simpl. easy.
       - simpl.
         case_eq s; intros.
         + subst. easy.
         + subst.
           rewrite firstn_cons in H.
           assert(mk_list_false (S (S m)) = false :: mk_list_false (S m)).
           { simpl. easy. }
           rewrite H0 in H.
           assert (b = false).
           { inversion H. easy. }
           subst.
           f_equal.
           apply IHm.
           inversion H.
           easy.
Qed.

Lemma firstN_app2:
  forall m k s, 
  (m >= k)%nat ->
  firstn m s = mk_list_false m -> 
  firstn (m - k) s = mk_list_false (m - k).
Proof. intro m.
       induction m; intros.
       - simpl. easy.
       - simpl. case_eq k; intros.
         + simpl. easy.
         + apply IHm. lia.
           apply firstN_app15.
           easy.
Qed.

Lemma mklf:
forall (xs: bitvector),
mk_list_false (length xs) ++ [false] = false :: mk_list_false (length xs).
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl. rewrite IHs. easy.
Qed.

Lemma first_bits_zeroA : forall (s : bitvector), 
  (length s >= (list2NTR s))%nat ->
  firstn (length s - (list2NTR s)) s = mk_list_false (length s - (list2NTR s)).
Proof. intros s H.
       induction s as [ | x xs IHs] using (rev_ind).
       - simpl. easy.
       - simpl in *.
         unfold list2NTR in *.
         case_eq x; intros.
         + subst.
           rewrite list2NR_eqT in *.
           simpl.
           rewrite <- !plus_n_O in *.
           rewrite lengthS in *.
           simpl in *.
           rewrite <- !plus_n_O in *.
           simpl in *.
           rewrite <- firstN_app.
           specialize (@firstN_app2 ((length xs) - (list2NR xs 0))%nat
                                   (list2NR xs 0) xs); intro HH.
           rewrite Nat.sub_add_distr.
           apply HH.
           lia.
           apply IHs. lia.
           lia.
         + subst.
           rewrite list2NR_eqF in *.
           simpl.
           rewrite <- !plus_n_O in *.
           rewrite lengthS in *.
           case_eq (list2NR xs 0); intros.
           * subst.
             rewrite plus_O_n.
             rewrite H0 in *.
             rewrite Nat.sub_0_r in *.
             assert(S (length xs) = length(xs ++ [false])).
             { rewrite length_app. simpl. lia. }
             rewrite H1 at 1.
             rewrite firstn_all.
             simpl. rewrite <- IHs.
             rewrite firstn_all.
             rewrite firstn_all in IHs.
             rewrite IHs.
             induction xs; intros.
             ++ simpl. easy.
             ++ simpl. rewrite mklf. easy.
             ++ lia.
             ++ lia.
           * rewrite H0 in *.
             simpl.
             rewrite <- firstN_app.
             assert((length xs - (n + S n))%nat = ((length xs - S n) - n)%nat).
             { simpl. lia. }
             rewrite H1.
             specialize (@firstN_app2 (length xs - S n)%nat n xs); intro HH.
             apply HH.
             lia.
             apply IHs.
             lia. lia.
Qed.

Lemma first_bits_zero : forall (s : bitvector), 
  (N.to_nat (list2N s) < length s)%nat ->
  firstn (length s - N.to_nat (list2N s)) (rev s) = mk_list_false (length s - N.to_nat (list2N s)).
Proof. intros s H.
       rewrite <- list2N_eq.
       specialize(@first_bits_zeroA (rev s)); intro HH.
       rewrite length_rev in HH.
       rewrite HH. easy.
       rewrite <- list2N_eq in H.
       lia.
Qed.
(* Burak's solution *)



(* forall s, toNat(s) < len(s) -> 
first (length s - N.to_nat (list2N s)) = [0..0] *)
(* forall s, k < l -> first (l - k) s = [0...0] *)
(*Lemma first_bits_zero : forall (s : bitvector), 
  (N.to_nat (list2N s) < length s)%nat ->
  firstn (length s - N.to_nat (list2N s)) (rev s) = 
  mk_list_false (length s - N.to_nat (list2N s)).
Proof.*)
  (* Approach 1 - Induction on (l - k): *)
  (* intros s. induction (length s - N.to_nat (list2N s))%nat.
  + easy.
  + intros Hlen. specialize (@IHn Hlen). *)
  (* The issue here is as follows:
     Let l = (length s), k = (list2N s)
     We want to do structural induction on l - k
     so that base case which is easy is:
     - k < l -> firstn 0 (rev s) = MLF 0
     - in the inductive case, we want to assume
       firstn l - (k + 1) bits are 0 and then prove 
       firstn l - k bits are 0.
     Doing mathematical induction on (l - k) doesn't 
     achieve this because it just considers 
     (l - k) = 0 for base case, (l - k) = n for IH, and 
     (l - k) = S n as the inductive proof obligation *)
  
  (* Approach 2 - Induction on l first, then case k: *)
  (*intros s. pose proof (@list2N_0_implies_mlf s) as list2Ns.
  induction (length s).
  + intros Hlt. inversion Hlt.
  + intros Hlt. case_eq (N.to_nat (list2N s)).
    - intros case. rewrite case in *. rewrite Nat.sub_0_r in *.
      apply Nat2N.inj_iff in case. rewrite N2Nat.id in case. 
      simpl in case. specialize (@list2Ns case).
      apply rev_func in list2Ns. 
      rewrite rev_mk_list_false in list2Ns.
      rewrite list2Ns. rewrite <- (@length_mk_list_false (S n)) at 1.
      rewrite firstn_all. easy.
    - intros m. intros case. rewrite case in *.*)
  (* Multiple issues:
     1. We are doing induction on length s.
        We have a lemma "H: list2N s = 0 -> s = mlf (length s)".
        With the induction, we want the equality of each 
        case of induction. For instance, in the base case
        we want as a hypothesis that "lenght s = 0".
        Since there doesn't seem to be a way to do this, 
        I added H to the hypothesis so that induction changes
        the occurence of length s in it. However, this
        adds H to the inductive hypothesis which isn't possible
        to prove.
     2. Assuming we didn't have the problem above, the 
        inductive hypothesis would be (S m < n) -> blah.
        We also have (S m < S n) and our goal is blah2.
        We need (S m < n) so we can use blah to prove blah2.
        But we can't get (S m < n) from what we have. *)

  (* Approach 3 - Induction on l first, then induction k: *)
  (*intros s. induction (length s).
  + intros Hlt. inversion Hlt.
  + intros Hlt. induction (N.to_nat (list2N s)).
    - rewrite Nat.sub_0_r in *. *)
  (* The issue here is that we don't have the value of 
     induction in the hypothesis, we are only able to 
     do that with case. *)
  
  (* Approach 4 - Induction on k first, then case l: *)
  (* Here the problem is that in the base case, 
     Coq sets all occurrences of (N.to_nat (list2N s)) to 
     0. But we want to retain the fact that "(N.to_nat (list2N s)) = 0"
     so that we can use that to prove that firstn n s = mk_list_false n
     which is currently admitted.
     If we did case_eq on (N.to_nat (list2N s)) we would retain this
     fact but we wouldn't have an induction hypothesis, which 
     is integral for the second case. *) 
  (*intros s. induction (N.to_nat (list2N s)).
  + intros Hlt. rewrite Nat.sub_0_r. case_eq (length s).
    - easy.
    - intros n case. admit.
  + intros Hlt. pose proof Hlt as Hlt2. 
    apply Nat.lt_succ_l in Hlt2. specialize (@IHn Hlt2).
    case_eq (length s).
    - intros case. easy.
    - intros m case. rewrite case in *.
    assert ((S m - n)%nat = S (S m - S n)).
    { rewrite Nat.sub_succ. apply lt_n_Sm_le in Hlt2. 
      apply Nat.sub_succ_l. apply Hlt2. }
    rewrite H in IHn. apply firstn_succ_mlf. apply IHn.*)
(* To overcome the issue from above, here we use a trick suggested 
   on StackOverflow but this gives us a problem in the 
   inductive step as mentioned below.
  intros s. generalize (eq_refl (N.to_nat (list2N s))).
  generalize (N.to_nat (list2N s)) at 1.
  induction n.
  + intros H Hlt. rewrite <- H. rewrite Nat.sub_0_r. 
    case_eq (length s).
    - easy.
    - intros n case. apply Nat2N.inj_iff in H. 
      rewrite N2Nat.id in H. simpl in H. 
      pose proof (@list2N_zero_implies_mlf s H) as list2N_zero_implies_mlf. 
      apply rev_func in list2N_zero_implies_mlf.
      rewrite rev_mk_list_false in list2N_zero_implies_mlf.
      rewrite list2N_zero_implies_mlf. rewrite case. 
      apply firstn_mlf.
  + intros H Hlt. rewrite <- H in Hlt. pose proof Hlt as Hlt2. 
    apply Nat.lt_succ_l in Hlt2. 
    Now the problem here is that we have S n = N.to_nat (list2N s)
    but we need to show n = N.to_nat (list2N s) to access the IH*)
(* This part reduces the proof goal to that of last_bits_zero
  intros s Hlen. pose proof (@skipn_firstn_mlf s (N.to_nat (list2N s)) Hlen).
  apply H. apply last_bits_zero. apply Hlen.
Qed.*)

Lemma first_bits_ule : forall (x s : bitvector), size x = size s -> 
  (N.to_nat (list2N s) < length s)%nat -> 
  ule_list_big_endian 
    (firstn (length s - N.to_nat (list2N s)) x)
    (firstn (length s - N.to_nat (list2N s)) (bv_not (rev s))) = true.
Proof.
  intros x s Hsize Hlt. pose proof (@first_bits_zero s Hlt) as Hzero.
  unfold bv_not, bits. rewrite firstn_map. rewrite Hzero.
  pose proof bv_not_false_true as negb_mlf. 
  unfold bv_not, bits in negb_mlf. rewrite negb_mlf.
  assert (len_firstn : length (firstn (length s - N.to_nat (list2N s)) x) = 
          (length s - N.to_nat (list2N s))%nat).
  { pose proof (@firstn_length_le bool x (length s - N.to_nat (list2N s))).
    pose proof Hsize as Hlen. apply size_len_eq in Hlen. rewrite Hlen in H.
    apply Nat.lt_le_incl in Hlt. apply le_minusni_n in Hlt.
    apply H in Hlt. apply Hlt. }
  rewrite <- len_firstn at 2. apply ule_list_big_endian_1.
Qed.



(* forall b, toNat(b) >= 0 *)
Lemma bvgez: forall a: bitvector, (bv2nat_a a = 0%nat) \/ (bv2nat_a a > 0)%nat.
Proof. intro a.
       induction a.
       - cbn. left. easy.
       - case_eq a; intros.
         + right. unfold bv2nat_a, list2nat_be_a.
           simpl. lia.
         + unfold bv2nat_a, list2nat_be_a. destruct IHa.
           * left. 
	           Reconstr.rblast (@Coq.NArith.Nnat.N2Nat.id, @list2N_N2List,
               @Coq.Init.Peano.O_S, @Coq.NArith.Nnat.Nat2N.id) 
              (@Coq.NArith.BinNatDef.N.of_nat, @list2nat_be_a, 
               @bv2nat_a, @Coq.NArith.BinNatDef.N.double, 
               @list2N).
           * right. cbn. 
	           Reconstr.rsimple (@Coq.NArith.Nnat.Nat2N.id, @Coq.PArith.Pnat.Pos2Nat.is_pos, 
              @Coq.Arith.PeanoNat.Nat.lt_irrefl, @list2N_N2List)
             (@list2nat_be_a, @Coq.NArith.BinNatDef.N.to_nat, 
              @Coq.NArith.BinNatDef.N.of_nat,
              @Coq.Init.Peano.gt, @Coq.NArith.BinNatDef.N.double,
              @bv2nat_a).
Qed.


(* 0 << b = 0 *)

Lemma length_cons : forall (t : list bool) (h : bool) , 
  length (h :: t) = S (length t).
Proof.
  induction t; easy.
Qed.

Lemma firstn_mk_list_false : forall (x y: nat), (x < y)%nat ->
  firstn x (mk_list_false y) = mk_list_false x.
Proof.
  intros x y ltxy. induction x.
  + easy.
  + induction y.
    - easy.
    - simpl. pose proof ltxy as ltxy2. apply Nat.succ_lt_mono in ltxy2.
      pose proof ltxy2 as ltxSy. apply Nat.lt_lt_succ_r in ltxSy.
      apply IHx in ltxSy. rewrite <- ltxSy.
      rewrite mk_list_false_app. rewrite firstn_app. rewrite length_mk_list_false.
      assert (forall (n m : nat), (n < m)%nat -> Nat.sub n m = O).
      { induction n.
        + easy.
        + induction m.
          - intros. now contradict H.
          - intros. simpl. apply Nat.succ_lt_mono in H. specialize (@IHn m H). apply IHn.
      }
      specialize (@H x y ltxy2). rewrite H. simpl. rewrite app_nil_r. easy.
Qed.


Lemma succ_minus_succ : forall x y : nat, (y < x)%nat -> S (x - S y) = (x - y)%nat.
Proof.
  intros x y ltyx.
  pose proof (@Nat.sub_succ_r x y). rewrite H.
  pose proof (@Nat.lt_succ_pred O (x - y)).
  pose proof (@lt_minus_O_lt y x ltyx). now apply H0 in H1.
Qed.

Lemma mk_list_false_app_minus : forall x y : nat, (y < x)%nat -> 
  mk_list_false (y) ++ mk_list_false (x - y) = mk_list_false (x).
Proof.
  intros x y ltyx.
  induction y.
  + simpl. now rewrite Nat.sub_0_r.
  + pose proof ltyx as ltyx2. apply Nat.lt_succ_l in ltyx2.
    specialize (@IHy ltyx2). rewrite mk_list_false_app.
    pose proof (@succ_minus_succ x y ltyx2).
    pose proof mk_list_false_app. rewrite <- app_assoc. simpl.
    assert (false :: mk_list_false (x - S y) = mk_list_false (S (x - S y))) by easy.
    rewrite H1. rewrite H. apply IHy.
Qed.

Lemma bvshl_zeros : forall (b : bitvector), 
                    bv_shl (zeros (size b)) b = zeros (size b).
Proof.
  intros b. induction b.
  + easy.
  + rewrite bv_shl_eq in *. unfold bv_shl_a in *.
    rewrite zeros_size in *. rewrite N.eqb_refl in *.
    unfold shl_n_bits_a in *. unfold size in *.
    unfold zeros in *. rewrite Nat2N.id in *.
    case_eq ((list2nat_be_a (a :: b) <? length (mk_list_false (length (a :: b))))%nat);
        intros comp_b_lenb.
    - pose proof firstn_mk_list_false as firstn_mlf.
      destruct (@Nat.eq_0_gt_0_cases (list2nat_be_a (a :: b))).
      * rewrite H. rewrite Nat.sub_0_r. rewrite length_mk_list_false.
        assert (mk_list_false 0 = []) by easy. rewrite H0. rewrite app_nil_l.
        pose proof (@firstn_all bool ((mk_list_false (length (a :: b))))).
        rewrite length_mk_list_false in H1. apply H1.
      * rewrite length_mk_list_false.
        specialize (@firstn_mlf (length (a :: b) - list2nat_be_a (a :: b))%nat 
                                (length (a :: b))).
        assert (lt : (length (a :: b) - list2nat_be_a (a :: b) 
                      < length (a :: b))%nat).
        { pose proof Nat.sub_lt. rewrite Nat.ltb_lt in comp_b_lenb.
          apply Nat.lt_le_incl in comp_b_lenb.
          specialize (@H0 (length (mk_list_false (length (a :: b)))) 
                          (list2nat_be_a (a :: b)) comp_b_lenb).
          rewrite length_mk_list_false in H0. apply H0. easy. }
        specialize (@firstn_mlf lt). rewrite firstn_mlf. apply mk_list_false_app_minus.
        rewrite length_mk_list_false in comp_b_lenb. rewrite Nat.ltb_lt in comp_b_lenb.
        apply comp_b_lenb.
    - now rewrite length_mk_list_false.
Qed.


(* b << 0 = b *)
Lemma length_zero_nil : forall (b : bitvector), 
  0%nat = length b -> [] = b.
Proof.
  intros. induction b; easy.
Qed.

Lemma bvshl_b_zeros : forall (b : bitvector), 
  bv_shl_a b (zeros (size b)) = b.
Proof.
  intros. unfold bv_shl_a. rewrite zeros_size.
  rewrite N.eqb_refl. unfold list2nat_be_a, zeros, size.
  rewrite Nat2N.id. rewrite list2N_mk_list_false.
  simpl. unfold shl_n_bits_a.
  case_eq (0 <? length b)%nat; intros.
  + simpl. rewrite Nat.sub_0_r. now rewrite firstn_all.
  + rewrite Nat.ltb_ge in H. apply (@Nat.le_0_r (length b)) in H.
    rewrite H. simpl. now apply length_zero_nil.
Qed.


Lemma mk_list_false_true_app : forall x y : nat, (y < x)%nat ->
  mk_list_false y ++ mk_list_true (x - y) <> mk_list_false x.
Proof.
  intros x y ltyx.
  induction y.
  + simpl. rewrite Nat.sub_0_r. induction x; easy.
  + pose proof ltyx as ltyx2. apply Nat.lt_succ_l in ltyx2.
    specialize (@IHy ltyx2). unfold not. intros. apply rev_func in H.
    rewrite rev_app_distr in H. rewrite rev_mk_list_false in H.
    rewrite rev_mk_list_false in H. rewrite rev_mk_list_true in H.
    case_eq (x - S y)%nat.
    - intros. apply minus_neq_O in ltyx. unfold not in ltyx. 
      apply ltyx. apply H0. 
    - intros. rewrite H0 in H. simpl in H. induction x.
      * easy.
      * simpl in H. now contradict H.
Qed.

Lemma bvshl_ones_neq_zero : forall (n : nat) (b : bitvector),
  length b = n ->
  bv_ult b (nat2bv (N.to_nat (size b)) (size b)) = true ->
  b <> mk_list_false (length b) ->
  bv_shl (mk_list_true n) b <> mk_list_false n.
Proof.
  intros n b Hb H bnot0. induction n.
  + symmetry in Hb. pose proof (@length_zero_nil b Hb). 
    symmetry in H0. rewrite H0 in *. now contradict H.
  + rewrite bv_shl_eq. unfold bv_shl_a. unfold size. 
    rewrite length_mk_list_true. rewrite Hb. rewrite N.eqb_refl.
    unfold shl_n_bits_a. rewrite length_mk_list_true.
    rewrite <- Hb. 
    pose proof (@bv_ult_nat b (nat2bv (N.to_nat (size b)) (size b))) as ult_eq.
    unfold size in ult_eq at 1. unfold size in ult_eq at 1. 
    rewrite (@length_nat2bv (N.to_nat (size b)) (size b)) in ult_eq.
    unfold size in ult_eq at 1. rewrite Nat2N.id in ult_eq. 
    rewrite N.eqb_refl in ult_eq. assert (true: true = true) by easy.
    specialize (@ult_eq true). rewrite ult_eq in H.
    unfold bv2nat_a, list2nat_be_a, nat2bv in H. rewrite N2Nat.id in H.
    rewrite (@list2N_N2List_eq (size b)) in H. unfold size in H.
    rewrite Nat2N.id in H. unfold list2nat_be_a. rewrite H.
    assert (sub_le : ((length b - N.to_nat (list2N b))%nat < (length b))%nat).
    { rewrite Nat.ltb_lt in H. pose proof H as Hleq. 
      apply Nat.lt_le_incl in Hleq. 
      pose proof (@not_mk_list_false b bnot0). rewrite Nat.ltb_lt in H0.
      pose proof Nat.sub_lt. 
      pose proof (@Nat.sub_lt (length b) (N.to_nat (list2N b)) Hleq H0).
      apply H2. }
      rewrite (@prefix_mk_list_true (length b - N.to_nat (list2N b))%nat 
                       (length b) sub_le).
      apply mk_list_false_true_app. rewrite Nat.ltb_lt in H. apply H.
Qed.

Lemma bv_not_not_eq : forall (h : bool) (t : bitvector), 
  bv_not (h :: t) <> (h :: t).
Proof.
  intros. unfold not. induction h; easy.
Qed.


(* s <u (signed_min (size s)) -> sign(s) = 0 *)

Lemma cons_ult_list_big_endian : forall (b : bool) (l1 l2 : list bool), 
  ult_list_big_endian (b :: l1) (b :: l2) = true ->
  ult_list_big_endian l1 l2 = true.
Proof.
  intros b l1 l2 ult. case b in *.
  + simpl in ult. case l1 in *.
    - case l2 in *; easy.
    - case l2 in *.
      * rewrite orb_true_iff in ult. destruct ult; easy.
      * rewrite orb_true_iff in ult. destruct ult; easy.
  + simpl in ult. case l1 in *.
    - case l2 in *; easy.
    - case l2 in *.
      * rewrite orb_true_iff in ult. destruct ult; easy.
      * rewrite orb_true_iff in ult. destruct ult; easy.
Qed.

Lemma ult_b_signed_min_implies_positive_sign : forall (b : bitvector)
  (n : N), size b = n -> bv_ult b (signed_min n) = true ->
  last b false = false.
Proof.
  intros b n Hb ult.
  unfold bv_ult in ult. rewrite signed_min_size in ult.
  rewrite Hb in ult. rewrite N.eqb_refl in ult. unfold ult_list in ult.
  unfold signed_min in ult. rewrite rev_involutive in ult.
  unfold size in Hb. apply N2Nat.inj_iff in Hb.
  rewrite Nat2N.id in Hb. rewrite <- length_rev in Hb.
  rewrite <- hd_rev. case (rev b) in *.
  + easy.
  + case (N.to_nat n) in *.
    - now contradict Hb.
    - assert (smin_big_endian (S n0) = true :: (mk_list_false n0)) 
      by easy. rewrite H in ult. case b0 in *. 
      * apply cons_ult_list_big_endian in ult. simpl in Hb. 
        apply Nat.succ_inj in Hb. rewrite <- Hb in ult.
        now rewrite not_ult_list_big_endian_x_0 in ult.
      * easy.
Qed.


(* [] >> x = [] *)
Lemma bvashr_nil : forall (b : bitvector), bv_ashr_a nil b = [].
Proof.
  unfold bv_ashr_a. induction b.
  + simpl. easy.
  + simpl. easy.
Qed.


(* sign(s) = 0 -> s >= (s >>a x) *)

Lemma rev_ashr_one_bit :forall (b : bitvector), 
  (rev (ashr_one_bit b false)) = (shl_one_bit (rev b)).
Proof.
  induction b.
  + easy.
  + simpl. rewrite rev_app_distr. simpl. unfold shl_one_bit.
    case_eq (rev b ++ [a]); intros case.
    - case a in *; case (rev b) in *; now contradict case.
    - intros l case2. rewrite <- case2. 
      rewrite removelast_app. simpl. rewrite app_nil_r.
      easy. easy.
Qed.

Lemma rev_ashr_n_bits : forall (n : nat) (b : bitvector),
  rev (ashr_n_bits b n false) = shl_n_bits (rev b) n.
Proof.
  induction n.
  + easy.
  + intros b. simpl. specialize (@IHn (ashr_one_bit b false)).
    rewrite IHn. rewrite rev_ashr_one_bit. easy.
Qed.

Lemma shl_one_implies_uge_list_big_endian : forall (b : bitvector),
  uge_list_big_endian b (shl_one_bit b) = true.
Proof.
  induction b.
  + easy.
  + unfold shl_one_bit. case a.
    - case b; easy.
    - Reconstr.scrush.
  Qed.

Lemma positive_bv_implies_uge_list_big_endian_shl_n_bits : 
  forall (n : nat) (b : bitvector), hd false b = false ->
  uge_list_big_endian b (shl_n_bits b n) = true.
Proof.
  induction n.
  + intros b Hsign. simpl. apply uge_list_big_endian_refl.
  + intros b Hsign. specialize (@IHn b Hsign). simpl.
    pose proof (@shl_one_implies_uge_list_big_endian (shl_n_bits b n)) as shl1.
    pose proof (@uge_list_big_endian_trans 
      b (shl_n_bits b n) (shl_one_bit (shl_n_bits b n))
      IHn shl1) as trans. rewrite <- shl_n_shl_one_comm in trans. 
    apply trans.
Qed.

Lemma positive_bv_implies_uge_bv_ashr : forall (b x: bitvector),
  size x = size b -> last b false = false -> 
  bv_uge b (bv_ashr_a b x) = true.
Proof.
  intros b x Hsize Hsign. case b as [|h t].
  + rewrite bvashr_nil. apply bv_uge_refl.
  + rewrite <- bv_ashr_eq. unfold bv_uge. 
    rewrite (@bv_ashr_size (size (h :: t)) 
                (h :: t) (x) eq_refl Hsize).
    rewrite N.eqb_refl. unfold uge_list. unfold bv_ashr. 
    rewrite Hsize. rewrite N.eqb_refl. unfold ashr_aux.
    unfold list2nat_be_a. rewrite Hsign.
    rewrite rev_ashr_n_bits. rewrite <- hd_rev in Hsign.
    apply positive_bv_implies_uge_list_big_endian_shl_n_bits.
    apply Hsign.
Qed.


(* sign(b) = 1 -> a >= (b >>a x) -> a >= b) *)

Definition ashl_one_bit  (a: list bool) : list bool :=
   match a with
     | [] => []
     | _ => true :: removelast a 
   end.

Fixpoint ashl_n_bits  (a: list bool) (n: nat): list bool :=
    match n with
      | O => a
      | S n' => ashl_n_bits (ashl_one_bit a) n'  
    end.

Lemma ashl_n_ashl_one_comm: forall n a, 
  (ashl_n_bits (ashl_one_bit a) n) = ashl_one_bit (ashl_n_bits a n).
Proof. 
  intro n. induction n; intros.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma rev_ashr_one_bit_true :forall (b : bitvector), 
  (rev (ashr_one_bit b true)) = (ashl_one_bit (rev b)).
Proof.
  induction b.
  + easy.
  + simpl. rewrite rev_app_distr. simpl. unfold ashl_one_bit.
    case_eq (rev b ++ [a]); intros case.
    - case a in *; case (rev b) in *; now contradict case.
    - intros l case2. rewrite <- case2. 
      rewrite removelast_app. simpl. rewrite app_nil_r.
      easy. easy.
Qed.

Lemma rev_ashr_n_bits_true : forall (n : nat) (b : bitvector),
  rev (ashr_n_bits b n true) = ashl_n_bits (rev b) n.
Proof.
  induction n; intros b.
  + easy.
  + simpl. specialize (@IHn (ashr_one_bit b true)).
    rewrite IHn. rewrite rev_ashr_one_bit_true. easy.
Qed.

Lemma ashl_one_implies_uge_list_big_endian : forall (b : bitvector),
  uge_list_big_endian (ashl_one_bit b) b = true.
Proof.
  induction b.
  + easy.
  + unfold ashl_one_bit. case a.
    - Reconstr.scrush.
    - case b; easy.
  Qed.

Lemma negative_bv_implies_ashl_n_bits_uge_list_big_endian : 
  forall (n : nat) (b : bitvector), hd false b = true ->
  uge_list_big_endian (ashl_n_bits b n) b = true.
Proof.
  induction n.
  + intros b Hsign. simpl. apply uge_list_big_endian_refl.
  + intros b Hsign. specialize (@IHn b Hsign). simpl.
    pose proof (@ashl_one_implies_uge_list_big_endian (ashl_n_bits b n)) as ashl1.
    pose proof (@uge_list_big_endian_trans 
      (ashl_one_bit (ashl_n_bits b n)) (ashl_n_bits b n) b 
      ashl1 IHn) as trans. rewrite <- ashl_n_ashl_one_comm in trans. 
    apply trans.
Qed.

Lemma negative_bv_implies_bv_ashr_uge : forall (b x : bitvector),
  size x = size b -> last b false = true ->
  bv_uge (bv_ashr_a b x) b = true.
Proof.
  intros b x Hsize Hsign. case b as [|h t].
  + rewrite bvashr_nil. apply bv_uge_refl.
  + rewrite <- bv_ashr_eq. unfold bv_uge. 
    rewrite (@bv_ashr_size (size (h :: t)) 
                (h :: t) (x) eq_refl Hsize).
    rewrite N.eqb_refl. unfold uge_list. unfold bv_ashr. 
    rewrite Hsize. rewrite N.eqb_refl. unfold ashr_aux.
    unfold list2nat_be_a. rewrite Hsign.
    rewrite rev_ashr_n_bits_true. rewrite <- hd_rev in Hsign.
    apply negative_bv_implies_ashl_n_bits_uge_list_big_endian.
    apply Hsign.
Qed.


(* sign b = 1 -> b >>a (size b) = 11...1 *)
Lemma ashr_size_sign1 : forall (b : bitvector), 
  last b false = true -> 
  bv_ashr_a b (nat2bv (length b) (size b)) = bv_not (zeros (size b)).
Proof.
  intros b sign. unfold bv_ashr_a. rewrite (@nat2bv_size (length b) (size b)). 
  rewrite N.eqb_refl. unfold ashr_aux_a. unfold list2nat_be_a, nat2bv.
  rewrite list2N_N2List_eq. unfold ashr_n_bits_a. unfold size, zeros.
  rewrite Nat2N.id. rewrite Nat.ltb_irrefl. rewrite sign. 
  simpl. rewrite bv_not_false_true. easy.
Qed.


(* sign b = 0 -> b >>a (size b) = 00...0 *)
Lemma ashr_size_sign0 : forall (b : bitvector), 
  last b false = false -> 
  bv_ashr_a b (nat2bv (length b) (size b)) = zeros (size b).
Proof.
  intros b sign. unfold bv_ashr_a. rewrite (@nat2bv_size (length b) (size b)). 
  rewrite N.eqb_refl. unfold ashr_aux_a. unfold list2nat_be_a, nat2bv.
  rewrite list2N_N2List_eq. unfold ashr_n_bits_a. unfold size, zeros.
  rewrite Nat2N.id. rewrite Nat.ltb_irrefl. rewrite sign. 
  simpl. easy.
Qed.


(* 0 <= x *)

Lemma ule_list_big_endian_0 : forall (x : bitvector),
  ule_list_big_endian (mk_list_false (length x)) x = true.
Proof.
  intros x. induction x.
  + easy.
  + case_eq a; intros case.
    - rewrite length_of_tail. rewrite mk_list_false_succ. case x; easy.
    - rewrite length_of_tail. rewrite mk_list_false_succ. 
      apply ule_list_big_endian_cons. apply IHx.
Qed.

Lemma bv_ule_0 : forall (x : bitvector), 
  bv_ule (mk_list_false (length x)) x = true.
Proof.
  intros x. unfold bv_ule. unfold size. rewrite length_mk_list_false.
  rewrite N.eqb_refl. unfold ule_list. rewrite rev_mk_list_false.
  rewrite <- length_rev. apply ule_list_big_endian_0.
Qed.


(* sign(b) = 0 or 1 *)
Lemma sign_0_or_1 : forall (b : bitvector), 
  last b false = false \/ last b false = true.
Proof.
  intros b. case b.
  + now left.
  + intros h t. case (last (h :: t)).
    - now right.
    - now left.
Qed.

(* Signed Less Than *)

(* x < y => y < z => x < z *)
Lemma slt_list_big_endian_trans : forall x y z,
    slt_list_big_endian x y = true ->
    slt_list_big_endian y z = true ->
    slt_list_big_endian x z = true.
Proof.
  intros x y z.
  destruct x.
    + easy.
    + destruct y.
      - easy.
      - destruct z.
        * easy.
        * intros.
          apply orb_prop in H, H0.
          apply orb_true_intro.
          destruct H, H0; apply andb_prop in H, H0; destruct H, H0.
          ++ left.
             apply andb_true_intro.
             split.
             -- apply eqb_prop in H, H0.
                rewrite H, H0.
                apply eqb_reflx.
             -- now apply (@ult_list_big_endian_trans x y z).
          ++ right.
             apply andb_true_intro.
             split.
             -- apply eqb_prop in H.
                now rewrite H.
             -- apply H2.
          ++ right.
             apply andb_true_intro.
             split.
             -- apply H.
             -- apply eqb_prop in H0.
                now rewrite <- H0.
          ++ now rewrite H0 in H1.
Qed. 

Lemma slt_list_trans : forall x y z,
    slt_list x y = true -> slt_list y z = true -> slt_list x z = true.
Proof. unfold slt_list. intros x y z. apply slt_list_big_endian_trans.
Qed.

Lemma bv_slt_trans : forall (b1 b2 b3 : bitvector), 
  bv_slt b1 b2 = true -> bv_slt b2 b3 = true -> bv_slt b1 b3 = true.
Proof.
  intros. unfold bv_slt in *. case_eq (size b1 =? size b2).
  + intros. pose proof H as bv_slt_b1_b2. 
    rewrite H1 in H. case_eq (size b2 =? size b3).
    - intros. pose proof H0 as bv_slt_b2_b3.
      rewrite H2 in H0. case_eq (size b1 =? size b3).
      * intros. pose proof slt_list_trans as slt_list_trans.
        specialize (@slt_list_trans b1 b2 b3 H H0).
        apply slt_list_trans.
      * intros. apply Neqb_ok in H1. apply Neqb_ok in H2. rewrite <- H1 in H2.
        rewrite H2 in H3. pose proof eqb_refl as eqb_refl.
        now rewrite N.eqb_refl in H3. 
    - intros. rewrite H2 in H0. now contradict H0.
  + intros. rewrite H1 in H. now contradict H.
Qed.

(* x <= y <-> (x < y \/ x = y) *)
Lemma sle_list_big_endian_implies_slt_list_big_endian_or_eq : forall (x y : list bool), 
  sle_list_big_endian x y = true -> slt_list_big_endian x y = true \/ (x = y).
Proof.
  intros x y.
  destruct x.
  + destruct y.
    - now right.
    - easy.
  + destruct y.
    - easy.
    - intro.
      apply orb_prop in H.
      destruct H.
      * apply andb_prop in H.
        destruct H.
        apply ule_list_big_endian_implies_ult_list_big_endian_or_eq in H0.
        destruct H0.
        ++ left.
           apply orb_true_intro.
           left.
           now apply andb_true_intro.
        ++ right.
           rewrite H0.
           f_equal.
           now apply eqb_prop.
     * left.
       apply orb_true_intro.
       now right.
Qed.

Lemma slt_list_big_endian_or_eq_implies_sle_list_big_endian : forall (x y : list bool), 
  slt_list_big_endian x y = true \/ (x = y) -> sle_list_big_endian x y = true.
Proof.
  intros x y.
  destruct x.
  + destruct y.
    - easy.
    - intro.
      destruct H.
      * easy.
      * discriminate.
  + destruct y; intro.
    - destruct H.
      * easy.
      * discriminate.
    - apply orb_true_intro.
      destruct H.
      * apply orb_prop in H.
        destruct H.
        ++ left.
           apply andb_prop in H.
           apply andb_true_intro.
           destruct H.
           split.
           -- apply H.
           -- apply ult_list_big_endian_or_eq_implies_ule_list_big_endian.
              now left.
        ++ now right.
      * left.
        apply andb_true_intro.
        injection H.
        intros.
        split.
        ++ rewrite H1.
           apply eqb_reflx.
        ++ rewrite H0.
           apply ule_list_big_endian_refl.
Qed.

Lemma bv_sle_eq : forall (x y : bitvector), bv_sle x y = true <->
  (bv_slt x y = true) \/ (x = y).
Proof.
  intros x y. 
  assert (eq : x = y <-> (rev x) = (rev y)).
  { split.
    + apply rev_func.
    + apply rev_inj.
  }
  split.
  + rewrite eq. unfold bv_sle, bv_slt. 
    case_eq (size x =? size y); intros case. 
    - unfold sle_list, slt_list. intros H. destruct (rev x).
      * destruct (rev y).
        ++ now right.
        ++ easy.
      * destruct (rev y).
        ++ apply sle_list_big_endian_implies_slt_list_big_endian_or_eq. apply H.
        ++ unfold sle_list in H. unfold slt_list. 
           apply sle_list_big_endian_implies_slt_list_big_endian_or_eq. apply H.
    - intros. now contradict H.
  + rewrite eq. unfold bv_sle, bv_slt.
    case_eq (size x =? size y); intros case. 
    - unfold sle_list, slt_list. intros H. destruct (rev x).
      * induction (rev y).
        ++ easy.
        ++ destruct H; easy.
      * induction (rev y);
        apply slt_list_big_endian_or_eq_implies_sle_list_big_endian; apply H.
    - intros. destruct H. 
      * now contradict H.
      * rewrite <- eq in H. rewrite H in case. rewrite N.eqb_refl in case.
        easy.
Qed.

(* x <= y => y < z => x < z *)
Lemma bv_sle_slt_trans : forall (b1 b2 b3 : bitvector), 
  bv_sle b1 b2 = true -> bv_slt b2 b3 = true -> bv_slt b1 b3 = true.
Proof.
  intros.
  destruct (@bv_sle_eq b1 b2).
  apply H1 in H.
  destruct H.
  + now apply (@bv_slt_trans b1 b2 b3).
  + now rewrite H.
Qed.

(* x < y => y <= z => x < z *)
Lemma bv_slt_sle_trans : forall (b1 b2 b3 : bitvector),
    bv_slt b1 b2 = true -> bv_sle b2 b3 = true -> 
    bv_slt b1 b3 = true.
Proof.
  intros b1 b2 b3 Hb1b2 Hb2b3.
  destruct (@bv_sle_eq b2 b3) as (bv_sle_ltr, bv_sle_rtl).
  apply bv_sle_ltr in Hb2b3. destruct Hb2b3.
  + now apply (@bv_slt_trans b1 b2 b3).
  + now rewrite <- H.
Qed.

(* x <= y => y <= z => x <= z *)
Lemma sle_list_big_endian_trans : forall (x y z : bitvector),
  sle_list_big_endian x y = true ->
  sle_list_big_endian y z = true ->
  sle_list_big_endian x z = true.
Proof.
  intros.
  apply sle_list_big_endian_implies_slt_list_big_endian_or_eq in H.
  destruct H.
  + apply sle_list_big_endian_implies_slt_list_big_endian_or_eq in H0.
    apply slt_list_big_endian_or_eq_implies_sle_list_big_endian.
    destruct H0.
    - left.
      now apply (@slt_list_big_endian_trans x y z).
    - left.
      now rewrite <- H0.
  + now rewrite H.
Qed.

(* x <= x *)
Lemma sle_list_big_endian_refl : forall (b : list bool), 
   sle_list_big_endian b b = true.
Proof.
  destruct b.
  + easy.
  + unfold sle_list_big_endian.
    apply orb_true_intro.
    left.
    apply andb_true_intro.
    split.
    - apply eqb_reflx.
    - apply ule_list_big_endian_refl.
Qed.

Lemma bv_sle_refl : forall (b : bitvector), bv_sle b b = true.
Proof.
  intros. unfold bv_sle. 
  rewrite N.eqb_refl. unfold sle_list.
  induction (rev b).
  + easy.
  + rewrite (@sle_list_big_endian_refl (a :: l)). easy.
Qed.

(* x < y <=> ~ (y <= x) *)
Lemma ult_negb_ule_list_big_endian : forall (x y : list bool),
  length x = length y ->
  ult_list_big_endian x y = negb (ule_list_big_endian y x).
Proof.
  intros.
  case_eq (ult_list_big_endian x y); intro.
  + case_eq (ule_list_big_endian y x); intro.
    - apply ult_big_endian_implies_not_uge_big_endian in H0.
      apply ule_list_big_endian_uge_list_big_endian in H1.
      now rewrite H1 in H0.
    - easy.
  + case_eq (ule_list_big_endian y x); intro.
    - easy.
    - apply not_ult_list_big_endian_implies_uge_list_big_endian in H0.
      * apply uge_list_big_endian_ule_list_big_endian in H0.
        now rewrite H1 in H0.
      * unfold size.
        now f_equal.
Qed.

Lemma slt_negb_sle_list_big_endian : forall (x y : list bool),
  length x = length y ->
  slt_list_big_endian x y = negb (sle_list_big_endian y x).
Proof.
  intros.
  destruct x.
  + now destruct y.
  + destruct y.
    - easy.
    - simpl.
      rewrite ult_negb_ule_list_big_endian.
      * destruct b.
        ++ destruct b0.
           -- now destruct (ule_list_big_endian y x).
           -- now destruct (ule_list_big_endian y x).
        ++ destruct b0.
           -- now destruct (ule_list_big_endian y x).
           -- now destruct (ule_list_big_endian y x).
      * simpl in H.
        now injection H.
Qed.

Lemma bv_slt_negb_sle : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  bv_slt x y = negb (bv_sle y x).
Proof.
  intros.
  unfold bv_slt, bv_sle.
  rewrite H, H0.
  rewrite N.eqb_refl.
  unfold slt_list, sle_list.
  apply slt_negb_sle_list_big_endian.
  rewrite !length_rev.
  rewrite <- H0 in H.
  unfold size in H.
  now apply Nat2N.inj.
Qed.

(* signed_min (size x) <= x *)
Lemma smin_sle_big_endian : forall (x : list bool),
  (sle_list_big_endian (smin_big_endian (length x)) x) = true.
Proof.
  intro x.
  destruct x.
  + reflexivity.
  + simpl.
    rewrite ule_list_big_endian_0.
    now destruct b.
Qed.

Lemma signed_min_sle : forall (x : bitvector),
  (bv_sle (signed_min (size x)) x) = true.
Proof.
  intro x.
  unfold bv_sle.
  rewrite signed_min_size, N.eqb_refl.
  unfold sle_list, signed_min.
  rewrite rev_involutive.
  unfold size.
  rewrite Nat2N.id.
  rewrite <- length_rev.
  apply smin_sle_big_endian.
Qed.

(* y >= size (x) => y << x = 0 *)
Lemma shl_ge_size: forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  Nat.leb (N.to_nat n) (list2nat_be_a (bits y)) = true ->
  bv_shl x y = zeros n.
Proof.
  intros n x y Hx Hy H.
  rewrite bv_shl_eq.
  unfold bv_shl_a.
  rewrite Hx.
  rewrite <- Hy.
  rewrite N.eqb_refl.
  unfold shl_n_bits_a.
  assert ((list2nat_be_a y <? length x)%nat = false).
  {
    rewrite (Nat.ltb_antisym).
    rewrite <- Hx in H.
    unfold size in H.
    rewrite Nat2N.id in H.
    unfold bits in H.
    now rewrite H.
  }
  rewrite H0.
  unfold zeros.
  unfold size.
  rewrite <- Hx in Hy.
  unfold size in Hy.
  rewrite Hy.
  now rewrite Nat2N.id.
Qed.

(* y < size x => (signed_min (size x) >> y) << y = signed_min (size x)  *)
Lemma shr_n_bits_smin_le_length : forall (n m : nat),
  (m <= n)%nat ->
  shr_n_bits (mk_list_false n ++ [true]) m = mk_list_false (n - m) ++ [true] ++ mk_list_false m.
Proof.
  intros n m H.
  induction m.
  + now rewrite Nat.sub_0_r.
  + simpl.
    rewrite shr_n_shr_one_comm.
    pose proof H.
    apply le_S in H0.
    apply le_S_n in H0.
    apply IHm in H0.
    rewrite H0.
    assert ((n - m)%nat = S (n - S m)%nat).
    {
      rewrite Nat.sub_succ_r.
      symmetry.
      apply Nat.succ_pred_pos.
      apply Nat.le_succ_l in H.
      apply lt_minus_O_lt.
      now destruct (@Nat.le_succ_l m n).
   }
    rewrite H1.
    simpl.
    replace (true :: mk_list_false m) with ([true] ++ mk_list_false m).
    replace (true :: false :: mk_list_false m) with ([true] ++ [false] ++ mk_list_false m).
    - rewrite <- !app_assoc.
      f_equal.
      f_equal.
      apply mk_list_false_cons.
    - easy.
    - easy.
Qed.

Lemma shl_n_bits_le_length_smin : forall (n m : nat),
  (m <= n)%nat ->
  shl_n_bits (mk_list_false (n - m) ++ [true] ++ mk_list_false m) m = mk_list_false n ++ [true].
Proof.
  intros n m H.
  induction m.
  + now rewrite Nat.sub_0_r.
  + simpl.
    pose proof H.
    apply le_S in H0.
    apply le_S_n in H0.
    apply IHm in H0.
    rewrite <- H0.
    f_equal.
    assert ((n - m)%nat = S (n - S m)%nat).
    {
      rewrite Nat.sub_succ_r.
      symmetry.
      apply Nat.succ_pred_pos.
      apply Nat.le_succ_l in H.
      apply lt_minus_O_lt.
      now destruct (@Nat.le_succ_l m n).
    }
    rewrite H1.
    replace (true :: false :: mk_list_false m) with ([true] ++ false :: mk_list_false m).
    rewrite app_assoc.
    rewrite shl_one_bit_app.
    - rewrite <- mk_list_false_cons.
      rewrite removelast_last.
      rewrite app_assoc.
      easy.
    - discriminate.
    - easy.
Qed.

Lemma shl_n_bits_shr_n_bits_smin_big_endian : forall (n m : nat),
  Nat.leb n m = false ->
  shl_n_bits (shr_n_bits (rev (smin_big_endian n)) m) m =
  rev (smin_big_endian n).
Proof.
  destruct n.
  + easy.
  + unfold smin_big_endian.
    replace (true :: mk_list_false n) with ([true] ++ mk_list_false n).
    - rewrite rev_app_distr.
      rewrite rev_mk_list_false.
      intros.
      assert (m <= n)%nat.
      { apply PeanoNat.lt_n_Sm_le.
        apply Arith.Compare_dec.not_le.
        intro.
        apply Nat.leb_le in H0.
        now rewrite H in H0.
      }
      rewrite shr_n_bits_smin_le_length.
      rewrite shl_n_bits_le_length_smin.
      * reflexivity.
      * apply H0.
      * apply H0.
    - easy.
Qed.

Lemma shl_shr_signed_min : forall (n : N) (x : bitvector),
  size x = n ->
  Nat.leb (N.to_nat n) (list2nat_be_a (bits x)) = false ->
  bv_shl (bv_shr (signed_min n) x) x = signed_min n.
Proof.
  intros n x Hx H.
  unfold bv_shl.
  rewrite Hx.
  rewrite (@bv_shr_size n).
  + { rewrite N.eqb_refl.
      unfold bv_shr.
      rewrite Hx.
      rewrite signed_min_size.
      rewrite N.eqb_refl.
      unfold shl_aux, shr_aux.
      unfold bits in H.
      unfold signed_min.
      now apply shl_n_bits_shr_n_bits_smin_big_endian.
     }
  + apply signed_min_size.
  + apply Hx.
Qed.

(* sign x <<a y = sign x *)
Lemma sign_ashr_one_bit : forall (x : list bool),
  ((last (ashr_one_bit x (last x false)) false) = last x false).
Proof.
  induction x.
  + easy.
  + unfold ashr_one_bit.
    now rewrite last_app.
Qed.

Lemma sign_ashr_n_bits : forall (m : nat) (x : list bool),
  ((last (ashr_n_bits x m (last x false)) false) = last x false).
Proof.
  induction m.
  + easy.
  + intros.
    simpl.
    rewrite <- (@sign_ashr_one_bit x) at 2.
    rewrite (@IHm (ashr_one_bit x (last x false))).
    now apply sign_ashr_one_bit.
Qed.

Lemma sign_bv_ashr : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  last (bv_ashr x y) false = last x false.
Proof.
  intros.
  unfold bv_ashr.
  rewrite H, H0.
  rewrite N.eqb_refl.
  unfold ashr_aux.
  apply sign_ashr_n_bits.
Qed.

(* x <=s y => x >>a z <=s y >>a z *)
Lemma ule_list_big_endian_app_bool : forall (n : nat) (b b0 : bool) (x y: list bool),
  length x = length y ->
  (ule_list_big_endian (x ++ [b]) (y ++ [b0])) = true ->
  (ule_list_big_endian x y) = true.
Proof.
  induction x.
  + now destruct y.
  + destruct y.
    - discriminate.
    - simpl.
      intros.
      apply orb_true_intro.
      apply orb_prop in H0.
      destruct H0.
      * left.
        apply andb_true_intro.
        apply andb_prop in H0.
        destruct H0.
        split.
        ++ apply H0.
        ++ injection H.
           intro.
           now apply (@IHx y).
      * now right.
Qed.

Lemma sle_list_big_endian_last : forall (b b0 : bool) (x y : list bool),
  length x = length y ->
  sle_list_big_endian (x ++ [b]) (y ++ [b0]) = true ->
  sle_list_big_endian ([last (b :: rev x) false] ++ x)
  ([last (b0 :: rev y) false] ++ y) = true.
Proof.
  intros.
  destruct x.
  + now destruct y.
  + destruct y.
    - discriminate.
    - assert ((last (b :: rev (b1 :: x)) false) = b1).
      {
       now rewrite <- (@last_app bool (b :: rev x) b1 false) at 2.
      }
      assert ((last (b0 :: rev (b2 :: y)) false) = b2).
      {
       now rewrite <- (@last_app bool (b0 :: rev y) b2 false) at 2.
      }
      rewrite H1, H2.
      simpl in H0.
      apply orb_true_intro.
      apply orb_prop in H0.
      destruct H0.
      * left.
        apply andb_true_intro.
        apply andb_prop in H0.
        destruct H0.
        split.
        ++ apply H0.
        ++ apply orb_true_intro.
           left.
           apply andb_true_intro.
           split.
           -- apply H0.
           -- apply (@ule_list_big_endian_app_bool (length x) b b0).
              ** simpl in H.
                 now injection H.
              ** apply H3.
      * now right.
Qed.

Lemma sle_list_ashr_one_bit : forall (n : nat) (x y : list bool),
  length x = length y ->
  sle_list x y = true -> sle_list (ashr_one_bit x (last x false))
  (ashr_one_bit y (last y false)) = true.
Proof.
  unfold sle_list.
  intros.
  destruct x.
  + destruct y.
    - easy.
    - assert (rev (b :: y) <> []).
      {
       simpl.
       now destruct (rev y).
      }
      now destruct (rev (b :: y)).
  + destruct y.
    - assert (rev (b :: x) <> []).
      {
       simpl.
       now destruct (rev x).
      }
      now destruct (rev (b :: x)).
    - unfold ashr_one_bit.
      rewrite !rev_app_distr.
      rewrite <- (@rev_involutive bool x) at 1.
      rewrite <- (@rev_involutive bool y) at 1.
      apply (@sle_list_big_endian_last b b0 (rev x) (rev y)).
      * rewrite !length_rev.
        simpl in H.
        now injection H.
      * apply H0.
Qed.

Lemma sle_list_ashr_n_bits : forall (n m : nat) (x y : list bool),
  length x = n -> length y = n ->
  sle_list x y = true -> sle_list (ashr_n_bits x m (last x false))
  (ashr_n_bits y m (last y false)) = true.
Proof.
  intros.
  induction m.
  + easy.
  + simpl.
    rewrite !ashr_n_ashr_one_comm.
    rewrite <- (@sign_ashr_n_bits m x) at 2.
    rewrite <- (@sign_ashr_n_bits m y) at 2.
    apply (@sle_list_ashr_one_bit n).
    - rewrite (@length_ashr_n_bits m x (last x false)).
      rewrite (@length_ashr_n_bits m y (last y false)).
      now rewrite H, H0.
    - apply IHm.
Qed.

Lemma sle_ashr : forall (n : N) (x y z : bitvector),
  size x = n -> size y = n -> size z = n -> 
  bv_sle x y = true -> bv_sle (bv_ashr x z) (bv_ashr y z) = true.
Proof.
  intros.
  unfold bv_sle.
  rewrite (@bv_ashr_size n x z).
  rewrite (@bv_ashr_size n y z).
  + rewrite N.eqb_refl.
    unfold bv_sle in H2.
    rewrite H, H0, N.eqb_refl in H2.
    unfold bv_ashr.
    rewrite H, H0, H1, N.eqb_refl.
    unfold ashr_aux.
    apply (@sle_list_ashr_n_bits (N.to_nat n) (list2nat_be_a z)).
    - rewrite <- Nat2N.id at 1.
      now f_equal.
    - rewrite <- Nat2N.id at 1.
      now f_equal.
    - apply H2.
  + easy.
  + easy.
  + easy.
  + easy.
Qed.

(* 0 <= x <=> sign x = 0 *)
Lemma mk_list_false_sle : forall (x : list bool),
  (sle_list_big_endian (mk_list_false (length x)) x) = negb (last (rev x) false).
Proof.
  destruct x.
  + easy.
  + destruct x.
    - now destruct b.
    - simpl.
      destruct b.
      * now rewrite last_app.
      * destruct b0.
        ++ now rewrite last_app.
        ++ rewrite ule_list_big_endian_0.
           now rewrite last_app.
Qed.

Lemma bv_zeros_sle : forall (x : bitvector),
  bv_sle (zeros (size x)) x = negb (last x false).
Proof.
  intro x.
  unfold bv_sle.
  rewrite zeros_size.
  rewrite N.eqb_refl.
  unfold sle_list.
  unfold zeros.
  rewrite rev_mk_list_false.
  unfold size.
  rewrite Nat2N.id.
  rewrite <- length_rev.
  rewrite <- (@rev_involutive bool x) at 3.
  apply mk_list_false_sle.
Qed.

(* x < 0 <=> sign x = 1 *)
Lemma bv_slt_zeros : forall (x : bitvector),
  bv_slt x (zeros (size x)) = last x false.
Proof.
  intro x.
  rewrite (@bv_slt_negb_sle (size x)).
  + rewrite bv_zeros_sle.
    now rewrite negb_involutive.
  + easy.
  + apply zeros_size.
Qed.

(* x < 0 -> x <=s bv_ashr x y *)
Lemma ule_list_big_endian_ashl_one_bit_true : forall (x : list bool),
  ule_list_big_endian x (removelast (true :: x)) = true.
Proof.
  intros. induction x.
  + easy.
  + unfold ashl_one_bit. case a.
    - assert (forall m n b, ule_list_big_endian m n = true -> 
          ule_list_big_endian (b :: m) (b :: n) = true).
      { intros. simpl. rewrite H. rewrite eqb_reflx. now simpl. }
      apply H. apply IHx. 
    - easy.
Qed.

Lemma sle_list_big_endian_ashl_one_bit_true : forall (x : list bool),
  last (rev x) false = true ->
  sle_list_big_endian x (removelast (true :: x)) = true.
Proof.
  intros.
  destruct x.
  + easy.
  + simpl in H.
    rewrite last_app in H.
    rewrite H.
    apply orb_true_intro.
    left.
    apply andb_true_intro.
    split.
    - easy.
    - apply ule_list_big_endian_ashl_one_bit_true.
Qed.

Lemma ashr_one_bit_neg : forall (x : list bool),
  last x false = true ->
  sle_list_big_endian (rev x) (rev (ashr_one_bit x true)) = true.
Proof.
  intros.
  rewrite rev_ashr_one_bit_true.
  apply sle_list_big_endian_ashl_one_bit_true.
  now rewrite rev_involutive.
Qed.

Lemma ashr_n_bits_neg : forall (m : nat) (x : list bool),
  last x false = true ->
  sle_list_big_endian (rev x) (rev (ashr_n_bits x m true)) = true.
Proof.
  intros.
  induction m.
  + simpl.
    apply sle_list_big_endian_refl.
  + simpl.
    rewrite ashr_n_ashr_one_comm.
    apply (@sle_list_big_endian_trans (rev x) (rev (ashr_n_bits x m true))).
    - apply IHm.
    - apply (@ashr_one_bit_neg (ashr_n_bits x m true)).
      rewrite <- H.
      apply sign_ashr_n_bits.
Qed.

Lemma bv_ashr_neg : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  last x false = true -> (bv_sle x (bv_ashr x y)) = true.
Proof.
  intros.
  unfold bv_sle.
  rewrite H, (@bv_ashr_size n).
  + rewrite N.eqb_refl.
    unfold bv_ashr.
    rewrite H, H0.
    rewrite N.eqb_refl.
    unfold sle_list.
    unfold ashr_aux.
    rewrite H1.
    now apply ashr_n_bits_neg.
  + apply H.
  + apply H0.
Qed.

(* BV -> Z Conversion *)
Fixpoint pow2_int (n: nat): Z :=
  match n with
    | O => 1%Z
    | S n' => (2 * pow2_int n')%Z
  end.

Definition pow2_int_N (n : N) := pow2_int (N.to_nat n).

Lemma pow2_int_succ : forall (n : nat),
  pow2_int (S n) = (2 * pow2_int n)%Z.
Proof.
  easy.
Qed.

Lemma pow2_int_add : forall (n m : nat),
  pow2_int (n + m) = (pow2_int n * pow2_int m)%Z.
Proof.
  intros.
  induction n.
  + now rewrite Z.mul_1_l.
  + rewrite pow2_int_succ.
    rewrite <- Z.mul_assoc.
    now rewrite <- IHn.
Qed.

Lemma zero_lt_pow2_int : forall (n : nat),
  (0 < pow2_int n)%Z.
Proof.
  induction n.
  + easy.
  + rewrite pow2_int_succ.
    now apply Z.mul_pos_pos.
Qed.

Lemma pow2_int_neq_zero : forall (n : nat),
  pow2_int n <> 0%Z.
Proof.
  intro.
  apply Znumtheory.Z_lt_neq.
  apply zero_lt_pow2_int.
Qed.

Definition bool2int (b : bool) : Z :=
  if b then 1%Z else 0%Z.

Fixpoint list2int (a: list bool) :=
  match a with
    | [] => 0%Z
    | h :: t => (2 * list2int t + bool2int h)%Z
  end.

Definition bv2int (a: bitvector) := list2int a.

Lemma list2int_cons : forall (x : list bool) (b : bool),
  list2int (b :: x) = (2 * list2int x + bool2int b)%Z.
Proof.
  easy.
Qed.

Lemma list2int_bool : forall (b : bool),
  list2int [b] = bool2int b.
Proof.
  easy.
Qed.

Lemma list2int_app : forall (x y : list bool),
  list2int (x ++ y) = ((pow2_int (length x)) * list2int y + list2int x)%Z.
Proof.
  induction x; intros.
  + rewrite Z.mul_1_l.
    now rewrite Z.add_0_r.
  + rewrite <- app_comm_cons.
    rewrite !list2int_cons.
    rewrite IHx.
    rewrite Z.mul_add_distr_l.
    rewrite <- Z.add_assoc.
    now rewrite Z.mul_assoc.
Qed.

Lemma bv2int_app : forall (x y : bitvector),
  bv2int (bv_concat x y) = ((pow2_int_N (size y)) * bv2int x + bv2int y)%Z.
Proof.
  intros.
  unfold pow2_int_N, size.
  rewrite Nat2N.id.
  apply list2int_app.
Qed.

Lemma list2int_mk_list_false : forall (n : nat),
  list2int (mk_list_false n) = 0%Z.
Proof.
  induction n.
  + easy.
  + replace (mk_list_false (S n)) with (false :: mk_list_false n).
    * rewrite list2int_cons.
      now rewrite IHn.
    * easy.
Qed.

Lemma bv2int_zeros : forall (n : N),
  bv2int (zeros n) = 0%Z.
Proof.
  intro.
  apply list2int_mk_list_false.
Qed.

Lemma list2int_mk_list_one : forall (n : nat),
  list2int (rev (mk_list_one n)) = (1 mod (pow2_int n))%Z.
Proof.
  destruct n.
  + easy.
  + rewrite rev_mk_list_one_succ.
    rewrite list2int_cons.
    rewrite list2int_mk_list_false.
    rewrite Z.add_0_l.
    rewrite pow2_int_succ.
    symmetry.
    apply Z.mod_1_l.
    apply Z.le_succ_l.
    replace (Z.succ 1) with (2 * (Z.succ 0))%Z.
    - apply Z.mul_le_mono_pos_l.
      * easy.
      * apply Z.le_succ_l.
        apply zero_lt_pow2_int.
    - easy.
Qed.

Lemma bv2int_one : forall (n : N),
  bv2int (one n) = (1 mod (pow2_int_N n))%Z.
Proof.
  intro n.
  apply list2int_mk_list_one.
Qed.

Lemma list2int_geq_zero : forall (x : list bool),
  (0 <= list2int x)%Z.
Proof.
  induction x; intros.
  + easy.
  + rewrite list2int_cons.
    apply Z.add_nonneg_nonneg.
    - now apply Z.mul_nonneg_nonneg.
    - now destruct a.
Qed.

Lemma list2int_lt_pow2_int : forall (x : list bool) (n : nat),
  length x = n ->
  (list2int x < pow2_int n)%Z.
Proof.
  induction x; intros.
  + now destruct n.
  + destruct n.
    - easy.
    - apply (@Z.lt_le_trans (list2int (a :: x)) (2 * list2int x + 2) (pow2_int (S n))).
      * rewrite list2int_cons.
        apply Zplus_lt_compat_l.
        now destruct a.
      * replace (2 * list2int x + 2)%Z with (2 * (list2int x + 1))%Z.
        ++ apply (@Z.mul_le_mono_nonneg_l (list2int x + 1) (pow2_int n) 2).
           -- easy.
           -- apply Ztac.Zlt_le_add_1.
              apply IHx.
              now injection H.
        ++ now rewrite Z.mul_add_distr_l.
Qed.

Lemma list2int_mod_pow2_int : forall (x : list bool) (n : nat),
  length x = n ->
  ((list2int x) mod (pow2_int n))%Z = list2int x.
Proof.
  intros.
  apply Zmod_small.
  split.
  + apply list2int_geq_zero.
  + now apply list2int_lt_pow2_int.
Qed.

Lemma list2int_surj : forall (n : nat) (k : Z),
  (0 <= k)%Z -> (k < pow2_int n)%Z ->
  (exists (x : list bool), length x = n /\ list2int x = k).
Proof.
  induction n; intros.
  + exists [].
    split.
    - easy.
    - apply Z.le_antisymm.
      * apply H.
      * now apply Zlt_succ_le.
  + destruct (@Z.lt_ge_cases k (pow2_int n)).
    - destruct (@IHn k).
      * apply H.
      * apply H1.
      * exists (x ++ [false]).
        destruct H2.
        split.
        ++ rewrite length_app.
           rewrite Nat.add_1_r.
           now rewrite H2.
        ++ rewrite list2int_app.
           rewrite Z.mul_0_r.
           now rewrite Z.add_0_l.
    - destruct (@IHn (k - (pow2_int n))%Z).
      * now apply Zle_minus_le_0.
      * apply Z.lt_sub_lt_add_r.
        now rewrite Z.add_diag.
      * exists (x ++ [true]).
        destruct H2.
        split.
        ++ rewrite length_app.
           rewrite Nat.add_1_r.
           now rewrite H2.
        ++ rewrite list2int_app.
           rewrite Z.mul_1_r.
           rewrite H3.
           rewrite H2.
           apply Zplus_minus.
Qed.

Lemma list2int_surj_mod : forall (n : nat) (k : Z),
  (exists (x : list bool), length x = n /\ ((list2int x) mod (pow2_int n) = k mod (pow2_int n))%Z).
Proof.
  intros.
  destruct (@Z_mod_lt k (pow2_int n)).
  + apply Z.lt_gt.
    apply zero_lt_pow2_int.
  + destruct (@list2int_surj n (k mod (pow2_int n))%Z).
    - easy.
    - easy.
    - exists x.
      now rewrite list2int_mod_pow2_int.
Qed.

Lemma bv2int_surj_mod : forall (n : N) (k : Z),
  (exists (x : bitvector), size x = n /\ ((bv2int x) mod (pow2_int_N n) = k mod (pow2_int_N n))%Z).
Proof.
  intros.
  destruct (@list2int_surj_mod (N.to_nat n) k) as (x, (H, H0)).
  exists x.
  split.
  + unfold size.
    rewrite H.
    apply N2Nat.id.
  + apply H0.
Qed.

Lemma list2int_inj : forall (x y : list bool),
  length x = length y ->
  list2int x = list2int y -> x = y.
Proof.
  induction x; intros.
  + now destruct y.
  + destruct y.
    - easy.
    - rewrite !list2int_cons in H0.
      destruct a.
      * destruct b.
        ++ f_equal.
           apply (@IHx y).
           -- now injection H.
           -- apply (@Zmult_reg_l (list2int x) (list2int y) 2).
              ** easy.
              ** apply (@Z.add_reg_l 1).
                 rewrite Z.add_comm.
                 now rewrite (@Z.add_comm 1 (2 * list2int y)).
        ++ assert (1 = 2 * (list2int y - list2int x))%Z.
           {
             rewrite Z.mul_sub_distr_l.
             rewrite Z.add_0_r in H0.
             rewrite <- H0.
             now rewrite Z.add_simpl_l.
           }
           assert (1 mod 2 = 0)%Z.
           {  
             rewrite H1.
             rewrite Z.mul_comm.
             apply Z_mod_mult.
           }
           easy.
      * destruct b.
        ++ assert (1 = 2 * (list2int x - list2int y))%Z.
           {
             rewrite Z.mul_sub_distr_l.
             rewrite Z.add_0_r in H0.
             rewrite H0.
             now rewrite Z.add_simpl_l.
           }
           assert (1 mod 2 = 0)%Z.
           {
             rewrite H1.
             rewrite Z.mul_comm.
             apply Z_mod_mult.
           }
           easy.
        ++ f_equal.
           apply (@IHx y).
           -- now injection H.
           -- rewrite !Z.add_0_r in H0.
              now apply (@Zmult_reg_l (list2int x) (list2int y) 2).
Qed.

Lemma list2int_inj_mod : forall (n : nat) (x y : list bool),
  length x = n -> length y = n ->
  ((list2int x) mod (pow2_int n) = (list2int y) mod (pow2_int n))%Z -> x = y.
Proof.
  intros.
  apply list2int_inj.
  + now rewrite H, H0.
  + rewrite <- (@list2int_mod_pow2_int x n).
    - now rewrite <- (@list2int_mod_pow2_int y n).
    - apply H.
Qed.

Lemma bv2int_inj_mod : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  ((bv2int x) mod (pow2_int_N n) = (bv2int y) mod (pow2_int_N n))%Z -> x = y.
Proof.
  intros.
  apply (@list2int_inj_mod (N.to_nat n)).
  + unfold size in H.
    rewrite <- H.
    now rewrite Nat2N.id.
  + unfold size in H0.
    rewrite <- H0.
    now rewrite Nat2N.id.
  + apply H1.
Qed.

(* bv2int (x * y) = bv2int x * bv2int y (mod 2^n) *)
Lemma list2int_and_with_bool : forall (x : list bool) (b : bool),
  list2int (and_with_bool x b) = (list2int x * bool2int b)%Z.
Proof.
  destruct b.
  + rewrite and_with_true.
    now rewrite Z.mul_1_r.
  + rewrite and_with_false.
    rewrite list2int_mk_list_false.
    now rewrite Z.mul_0_r.
Qed.

Lemma sum_bool2int : forall (a b c : bool),
  (bool2int a + bool2int b + bool2int c = 2 * bool2int (a && b || xorb a b && c)  + bool2int (xorb (xorb a b) c))%Z.
Proof.
  now destruct a; destruct b; destruct c.
Qed.

Lemma list2int_mult_bool_step_k_h_leq_0: forall (a b : list bool) (n : nat) (k : Z) (c : bool),
  length a = n -> length b = n -> (k - 1 <? 0)%Z = true ->
  ((list2int (mult_bool_step_k_h a b c k)) mod (pow2_int n) =
  (list2int b + list2int a + bool2int c) mod (pow2_int n))%Z.
Proof.
  induction a; intros.
  + rewrite <- H.
    now rewrite !Z.mod_1_r.
  + destruct b.
    - now rewrite <- H0 in H.
    - assert ((mult_bool_step_k_h (a :: a0) (b :: b0) c k) = ((xorb (xorb a b) c) :: mult_bool_step_k_h a0 b0 ((a && b) || ((xorb a b) && c)) (k - 1))).
      {
        simpl.
        now rewrite H1.
      }
      rewrite H2.
      rewrite !list2int_cons.
      rewrite <- !Z.add_assoc.
      rewrite (@Z.add_comm (bool2int b)).
      rewrite <- !Z.add_assoc.
      rewrite (@Z.add_comm (bool2int c)).
      rewrite (@Z.add_assoc (bool2int a)).
      rewrite sum_bool2int.
      rewrite !Z.add_assoc.
      rewrite Zplus_mod.
      rewrite (@Zplus_mod (2 * list2int b0 + 2 * list2int a0 + 2 * bool2int (a && b || xorb a b && c))).
      f_equal.
      f_equal.
      rewrite <- !Z.mul_add_distr_l.
      simpl in H, H0.
      rewrite <- H.
      rewrite pow2_int_succ.
      rewrite !Z.mul_mod_distr_l.
      * rewrite IHa.
        ++ easy.
        ++ easy.
        ++ rewrite <- H0 in  H. 
           now injection H.
        ++ apply Z.ltb_lt.
           apply Z.lt_lt_pred.
           now apply Z.ltb_lt.
       * apply pow2_int_neq_zero.
       * easy.
       * apply pow2_int_neq_zero.
       * easy.
Qed.

Lemma list2int_mult_bool_step_k_h : forall (k : nat) (n : nat) (a b : list bool),
  length a = n -> (length b + k = n)%nat ->
  (list2int (mult_bool_step_k_h a b false (Z.of_nat k)) mod (pow2_int n) =
  ((pow2_int k) * list2int b + list2int a) mod (pow2_int n))%Z.
Proof.
  induction k; intros.
  + rewrite Z.mul_1_l.
    rewrite Nat.add_0_r in H0.
    rewrite <- (@Z.add_0_r (list2int b + list2int a)).
    now apply (@list2int_mult_bool_step_k_h_leq_0  a b n 0 false).
  + destruct a.
    - rewrite <- H.
      now rewrite !Z.mod_1_r.
    - destruct b.
      * rewrite mult_bool_step_k_h_nil.
        rewrite Z.mul_0_r.
        now rewrite Z.add_0_l.
      * assert (Z.of_nat (S k) - 1 = Z.of_nat k)%Z.
        {
          rewrite <- Nat.add_1_r.
          rewrite Nat2Z.inj_add.
          apply Z.add_simpl_r.
        }
        assert (Z.of_nat (S k) - 1 <? 0 = false)%Z.
        {
          apply Z.ltb_ge.
          rewrite H1.
          apply Zle_0_nat.
        }
        assert (mult_bool_step_k_h (b0 :: a) (b :: b1) false (Z.of_nat (S k)) = b0 :: mult_bool_step_k_h a (b :: b1) false (Z.of_nat k)).
        {
          unfold mult_bool_step_k_h.
          now rewrite H2, H1.
        }
        rewrite H3.
        rewrite !list2int_cons.
        rewrite Z.add_assoc.
        rewrite Zplus_mod.
        rewrite (@Zplus_mod (pow2_int (S k) * list2int (b :: b1) + 2 * list2int a)).
        f_equal.
        f_equal.
        rewrite pow2_int_succ.
        rewrite <- Z.mul_assoc.
        rewrite <- Z.mul_add_distr_l.
        simpl in H.
        rewrite <- H.
        rewrite pow2_int_succ.
        rewrite !Z.mul_mod_distr_l.
        ++ rewrite (@IHk (length a) a (b :: b1)).
           -- easy.
           -- easy.
           -- rewrite <- H0 in H.
              rewrite Nat.add_succ_r in H.
              now injection H.
        ++ apply pow2_int_neq_zero.
        ++ easy.
        ++ apply pow2_int_neq_zero.
        ++ easy.
Qed.

Lemma list2int_mult_bool_step : forall (n : nat) (k' : nat) (a b : list bool) (res : list bool) (k : nat),
  length a = n -> length b = n -> length res = n -> (1 + k' + k = n)%nat ->
  (list2int (mult_bool_step a b res k k') mod (pow2_int n) =
  (pow2_int k * list2int(firstn (S k') a) * list2int(skipn k b) + (list2int res)) mod (pow2_int n))%Z.
Proof.
  induction k'; intros.
  + assert ((mult_bool_step a b res k 0) = mult_bool_step_k_h res (and_with_bool (List.firstn (S O) a) (nth k b false)) false (Z.of_nat k)).
    {
      easy.
    }
    rewrite H3.
    rewrite list2int_mult_bool_step_k_h.
    - rewrite list2int_and_with_bool.
      rewrite skipn_length_minus_1.
      * rewrite list2int_bool.
        now rewrite Z.mul_assoc.
      * now rewrite <- H2 in H0.
    - apply H1.
    - rewrite and_with_bool_len.
      rewrite firstn_length_le.
      * apply H2.
      * rewrite H.
        rewrite <- H2.
        apply Nat.le_add_r.
  + assert ((mult_bool_step a b res k (S k')) = mult_bool_step a b (mult_bool_step_k_h res (and_with_bool (List.firstn (S (S k')) a) (nth k b false)) false (Z.of_nat k)) (S k) k').
    {
      easy.
    }
    rewrite H3.
    rewrite IHk'.
    - assert (skipn k b = nth k b false :: skipn (S k) b).
      {
        apply nth_cons_skip_n.
        rewrite H0.
        rewrite <- H2.
        apply Nat.lt_add_pos_l.
        apply Nat.lt_0_succ.
      }
      rewrite H4.
      rewrite list2int_cons.
      rewrite Z.mul_add_distr_l.
      assert (firstn (S (S k')) a = firstn (S k') a ++ [nth (S k') a false]).
      {
        apply first_n_app_cons.
        rewrite H.
        rewrite <- H2.
        rewrite Nat.add_shuffle0.
        apply Nat.lt_add_pos_l.
        apply Nat.lt_0_succ.
      }
      rewrite H5.
      rewrite list2int_app.
      rewrite Z.mul_add_distr_l.
      rewrite Z.mul_add_distr_r.
      rewrite !Z.mul_assoc.
      rewrite <- !(@Z.mul_comm 2).
      rewrite !Z.mul_assoc. 
      rewrite (@Z.add_comm (2 * pow2_int k * pow2_int (length (firstn (S k') a)) * list2int [nth (S k') a false] * list2int (skipn (S k) b))).
      rewrite <- !Z.add_assoc.
      rewrite pow2_int_succ.
      rewrite Zplus_mod.
      rewrite (@Zplus_mod (2 * pow2_int k * list2int (firstn (S k') a) * list2int (skipn (S k) b))).
      f_equal.
      f_equal.
      assert (length (firstn (S k') a) = S k').
      {
        apply firstn_length_le.
        rewrite H.
        rewrite <- H2.
        rewrite Nat.add_shuffle0.
        apply Nat.le_add_l.
      }
      rewrite list2int_mult_bool_step_k_h.
      * rewrite and_with_bool_app.
        rewrite list2int_app.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_add_distr_r.
        rewrite !list2int_and_with_bool.
        rewrite and_with_bool_len.
        rewrite !H6.
        assert (pow2_int n = 2 * pow2_int k * pow2_int (S k'))%Z.
        {
        rewrite <- H2.
        rewrite Nat.add_shuffle0.
        now rewrite pow2_int_add.
        }
        rewrite <- H7.
        rewrite <- (@Zplus_mod_idemp_l (pow2_int n * list2int [nth (S k') a false] * list2int (skipn (S k) b))).
        rewrite <- Z.mul_assoc.
        rewrite (@Z.mul_comm (pow2_int n)).
        rewrite Z_mod_mult.
        rewrite Z.add_0_l.
        now rewrite !Z.mul_assoc.
        * apply H1.
        * rewrite and_with_bool_len.
          rewrite length_app.
          rewrite H6.
          now rewrite Nat.add_1_r.
    - apply H.
    - apply H0.
    - now rewrite prop_mult_bool_step_k_h_len.
    - rewrite Nat.add_succ_r.
      rewrite <- Nat.add_succ_l.
      now rewrite <- Nat.add_succ_r.
Qed.

Lemma list2int_mult : forall (n : nat) (x y : list bool),
  length x = n -> length y = n ->
  (list2int (bvmult_bool x y n) mod (pow2_int n) =
  (list2int x) * (list2int y) mod (pow2_int n))%Z.
Proof.
  intros.
  destruct n.
  + now destruct x.
  + destruct n.
    - destruct x.
      * easy.
      * destruct x.
        ++ destruct y.
           -- easy.
           -- destruct y; destruct b; now destruct b0.
        ++ easy.
   - unfold bvmult_bool.
     rewrite list2int_mult_bool_step.
     * assert (pow2_int 1 = 2%Z).
       {
         easy.
       }
       rewrite H1.
       rewrite Zplus_mod.
       assert ((2 * list2int (firstn (S n) x) * list2int (skipn 1 y)) mod pow2_int (S (S n)) =
              (2 * list2int x * list2int (skipn 1 y)) mod pow2_int (S (S n)))%Z.
       {
         rewrite <- (@firstn_skipn bool (S n) x) at 2.
         rewrite list2int_app.
         rewrite Z.mul_add_distr_l.
         rewrite Z.mul_add_distr_r.
         rewrite Zplus_mod.
         rewrite <- Zmod_mod at 1.
         rewrite <- (@Z.add_0_l ((2 * list2int (firstn (S n) x) * list2int (skipn 1 y)) mod pow2_int (S (S n)))%Z) at 1.
         f_equal.
         f_equal.
         rewrite firstn_length_le.
         + rewrite Z.mul_assoc.
           rewrite <- pow2_int_succ.
           rewrite <- Z.mul_assoc.
           rewrite Z.mul_comm.
           now rewrite Z_mod_mult.
         + rewrite H.
           apply Nat.le_succ_diag_r.
       }
       rewrite H2.
       rewrite list2int_and_with_bool.
       rewrite (@Z.mul_comm 2 (list2int x)).
       rewrite Zmult_assoc_reverse.
       rewrite <- Zplus_mod.
       rewrite <- Z.mul_add_distr_l.
       f_equal.
       f_equal.
       now destruct y.
     * apply H.
     * apply H0.
     * now rewrite and_with_bool_len.
     * now rewrite Nat.add_1_r.
Qed.

Lemma bv2int_mult : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  (bv2int (bv_mult x y) mod (pow2_int_N n) =
  bv2int x * bv2int y mod (pow2_int_N n))%Z.
Proof.
  intros.
  unfold bv_mult.
  rewrite H, H0.
  rewrite N.eqb_refl.
  unfold bv2int.
  unfold mult_list.
  assert (length x = N.to_nat n).
  {
    rewrite <- H.
    unfold size.
    now rewrite Nat2N.id.
  }
  rewrite H1.
  apply list2int_mult.
  + apply H1.
  + rewrite <- H0.
    unfold size.
    now rewrite Nat2N.id.
Qed.

Lemma bv2int_exists_bv_mult_eq : forall (n : N) (x y : bitvector),
  size x = n -> size y = n -> iff 
  (exists z : Z, ((z * bv2int x) mod (pow2_int_N n))%Z = (bv2int y mod (pow2_int_N n))%Z)
  (exists z : bitvector, size z = n /\ bv_mult z x = y).
Proof.
  intros.
  split; intro.
  + destruct H1.
    destruct (@bv2int_surj_mod n x0) as (z, (H2, H3)).
    exists z.
    split.
    - apply H2.
    - apply (@bv2int_inj_mod n).
      * apply bv_mult_size.
        ++ apply H2.
        ++ apply H.
      * apply H0.
      * rewrite bv2int_mult.
        ++ rewrite <- Zmult_mod_idemp_l.
           -- rewrite H3.
              now rewrite Zmult_mod_idemp_l.
        ++ apply H2.
        ++ apply H.
  + destruct H1 as (z, (H1, H2)).
    - exists (bv2int z).
      rewrite <- bv2int_mult.
      * now rewrite H2.
      * apply H1.
      * apply H.
Qed.

(* x * 0 = 0 *)
Lemma bv_mult_zeros_l : forall (n : N) (x : bitvector),
  size x = n ->
  bv_mult (zeros n) x = zeros n.
Proof.
  intros.
  apply (@bv2int_inj_mod n).
  + rewrite (@bv_mult_size n).
    - easy.
    - apply zeros_size.
    - apply H.
  + apply zeros_size.
  + rewrite bv2int_mult.
    - rewrite bv2int_zeros.
      now rewrite Z.mul_0_l.
    - apply zeros_size.
    - apply H.
Qed.

(* 0 * x = 0 *)
Lemma bv_mult_zeros_r : forall (n : N) (x : bitvector),
  size x = n ->
  bv_mult x (zeros n) = zeros n.
Proof.
  intros.
  apply (@bv2int_inj_mod n).
  + rewrite (@bv_mult_size n).
    - easy.
    - apply H.
    - apply zeros_size.
  + apply zeros_size.
  + rewrite bv2int_mult.
    - rewrite bv2int_zeros.
      now rewrite Z.mul_0_r.
    - apply H.
    - apply zeros_size.
Qed.

(* 1 * x = x *)
Lemma bv_mult_one_l : forall (n : N) (x : bitvector),
  size x = n ->
  bv_mult (one n) x = x.
Proof.
  intros.
  apply (@bv2int_inj_mod n).
  + rewrite (@bv_mult_size n).
    - easy.
    - apply one_size.
    - apply H.
  + apply H.
  + rewrite bv2int_mult.
    - rewrite bv2int_one.
      rewrite Zmult_mod_idemp_l.
      now rewrite Z.mul_1_l.
    - apply one_size.
    - apply H.
Qed.

(* (x = 00..0 \/ exists z, x = z100..0) *)
Lemma mk_list_false_true_factorization : forall (x : list bool),
  x = mk_list_false (length x) \/ (exists (k : nat) (z : list bool), x = mk_list_false k ++ [true] ++ z).
Proof.
  induction x.
  + now left.
  + destruct a.
    - right.
      exists 0%nat.
      now exists x.
    - destruct IHx.
      * left.
        now rewrite H at 1.
      * right.
        destruct H as (k, (z, H)).
        exists (S k)%nat.
        exists z.
        now rewrite H.
Qed.

Lemma zeros_one_factorization : forall (x : bitvector),
  x = zeros (size x) \/ (exists (k : N) (z : bitvector), x = bv_concat (bv_concat z (one 1)) (zeros k)).
Proof.
  intro.
  unfold zeros, size.
  rewrite Nat2N.id.
  destruct (@mk_list_false_true_factorization x).
  + now left.
  + destruct H as (k, (z, H)).
    right.
    exists (N.of_nat k).
    exists z.
    now rewrite Nat2N.id.
Qed.

(* -(z100..0) = ~z011..1 *)
Lemma map_neg_mk_list_false_true : forall (z : list bool) (k : nat),
  map negb (mk_list_false k ++ [true] ++ z) =
  (mk_list_true k ++ [false] ++ map negb z).
Proof.
  intros.
  rewrite map_app.
  now rewrite not_list_false_true.
Qed.

Lemma add_list_ingr_mk_list_false_true : forall (z : list bool) (k : nat),
  add_list_ingr (mk_list_true k ++ [false] ++ map negb z)
  (mk_list_false k ++ mk_list_false (length [true]) ++ mk_list_false (length z))
  true = mk_list_false k ++ [true] ++ map negb z.
Proof.
  intros.
  induction k.
  + simpl.
    rewrite not_list_length.
    now rewrite add_list_carry_empty_neutral_r.
  + simpl.
    simpl in IHk.
    now rewrite IHk.
Qed.

Lemma twos_complement_mk_list_false_true : forall (z : list bool) (k : nat),
  twos_complement (mk_list_false k ++ [true] ++ z) =
  (mk_list_false k ++ [true] ++ map negb z).
Proof.
  intros.
  unfold twos_complement.
  rewrite map_neg_mk_list_false_true.
  rewrite !length_app.
  rewrite length_mk_list_false.
  rewrite !mk_list_false_plus.
  apply add_list_ingr_mk_list_false_true.
Qed.

Lemma bv_neg_zeros_one : forall (z : bitvector) (k : N),
  bv_neg (bv_concat (bv_concat z (one 1)) (zeros k)) =
  bv_concat (bv_concat (bv_not z) (one 1)) (zeros k).
Proof.
  intros.
  apply twos_complement_mk_list_false_true.
Qed.

(* (~z011..1 | z100..0) = 11..100..0 *)
Lemma map2_or_map_neg_mk_list_false_true : forall (z : list bool) (k : nat),
  map2 orb (mk_list_false k ++ [true] ++ map negb z) (mk_list_false k ++ [true] ++ z) =
  mk_list_false k ++ mk_list_true (length z + 1).
Proof.
  intros.
  rewrite Nat.add_1_r.
  rewrite mk_list_true_succ.
  rewrite map2_or_app.
  + rewrite map2_or_app.
    - rewrite <- length_mk_list_false at 2.
      rewrite map2_or_0_neutral.
      now rewrite map2_or_neg_true.
    - easy.
    - now rewrite <- not_list_length.
  + easy.
  + simpl.
    now rewrite <- not_list_length.
Qed.

Lemma bv_or_neg_zeros_one : forall (z : bitvector) (k : N),
  bv_or (bv_concat (bv_concat (bv_not z) (one 1)) (zeros k)) (bv_concat (bv_concat z (one 1)) (zeros k)) = 
  bv_concat (ones (size z + 1)) (zeros k).
Proof.
  intros.
  unfold bv_or.
  rewrite !(@bv_concat_size (size z + 1) k).
  + rewrite N.eqb_refl.
    unfold ones.
    rewrite N2Nat.inj_add.
    unfold size.
    rewrite Nat2N.id.
    apply map2_or_map_neg_mk_list_false_true.
  + now apply (@bv_concat_size (size z) 1).
  + apply zeros_size.
  + apply (@bv_concat_size (size z) 1).
    - now apply bv_not_size.
    - easy.
  + apply zeros_size.
Qed.

(* 11..100..0 & t = t_n-1 t_n-2 .. t_k 00..0 *)
Lemma map2_and_or_map_neg_mk_list_false_true : forall (y z : list bool) (k : nat),
  (length z + 1 + k)%nat = length y ->
  map2 andb ((mk_list_false k) ++ mk_list_true (length z + 1)) y = mk_list_false k ++ skipn k y.
Proof.
  intros.
  assert (length (firstn k y) = k).
  {
    apply firstn_length_le.
    rewrite <- H.
    apply Nat.le_add_l.
  }
  assert (length (skipn k y) = (length z + 1)%nat).
  {
    rewrite length_skipn.
    rewrite <- H.
    apply Nat.add_sub.
  }
  rewrite <- (@firstn_skipn bool k y) at 1.
  rewrite map2_and_app.
  + rewrite <- H0 at 1.
    rewrite map2_and_comm.
    rewrite map2_and_0_absorb.
    rewrite H0.
    rewrite <- H1.
    rewrite map2_and_comm.
    now rewrite map2_and_1_neutral.
  + rewrite length_mk_list_false.
    now rewrite H0.
  + now rewrite length_mk_list_true.
Qed.

Lemma bv_and_or_neg_zeros_one : forall (y z : bitvector) (k : N),
  size z + 1 + k = size y ->
  bv_and (bv_concat (ones (size z + 1)) (zeros k)) y = bv_concat (skipn (N.to_nat k) y) (zeros k) .
Proof.
  intros.
  unfold bv_and.
  rewrite (@bv_concat_size (size z + 1) k).
  + rewrite H.
    rewrite N.eqb_refl.
    unfold ones.
    rewrite N2Nat.inj_add.
    unfold size.
    rewrite Nat2N.id.
    apply map2_and_or_map_neg_mk_list_false_true.
    apply Nat2N.inj.
    rewrite !Nat2N.inj_add.
    now rewrite N2Nat.id.
  + apply ones_size.
  + apply zeros_size.
Qed.

(* t_n-1 t_n-2 .. t_k 00..0 = t <=> (exists t', t = 2^k * t') *)
Lemma map2_and_or_map_neg_eq_mk_list_false : forall (y : list bool) (k : nat),
  (k <= length y)%nat -> iff
  (mk_list_false k ++ skipn k y = y)
  (exists (x : Z), ((x * pow2_int k) mod (pow2_int (length y)) = (list2int y) mod (pow2_int (length y)))%Z).
Proof.
  intros.
  apply (@iff_trans (mk_list_false k ++ skipn k y = y) (exists (x : Z),  (x * pow2_int k)%Z = list2int y)).
  + split; intro.
    - exists (list2int (skipn k y)).
      rewrite <- H0 at 2.
      rewrite list2int_app.
      rewrite length_mk_list_false.
      rewrite list2int_mk_list_false.
      rewrite Z.add_0_r.
      now rewrite Z.mul_comm.
    - rewrite <- (@firstn_skipn bool k).
      f_equal.
      apply (@list2int_inj_mod k).
      * apply length_mk_list_false.
      * now apply firstn_length_le.
      * rewrite list2int_mk_list_false.
        destruct H0.
        rewrite <- (@firstn_skipn bool k y) in H0.
        rewrite list2int_app in H0.
        rewrite firstn_length_le in H0.
        ++ apply Zplus_minus_eq in H0.
           rewrite (@Z.mul_comm (pow2_int k)) in H0.
           rewrite <- Z.mul_sub_distr_r in H0.
           rewrite H0.
           now rewrite Z_mod_mult.
        ++ apply H.
  + split; intro; destruct H0.
    - exists x.
      now rewrite H0.
    - assert ((list2int y - x * pow2_int k) mod (pow2_int (length y)) = 0)%Z.
      {
        rewrite Zminus_mod.
        rewrite H0.
        now rewrite Z.sub_diag.
      }
      apply Z.mod_divide in H1.
      * destruct H1.
        exists (x0 * pow2_int (length y - k) + x)%Z.
        rewrite Z.mul_add_distr_r.
        rewrite <- Z.mul_assoc.
        rewrite <- pow2_int_add.
        rewrite Nat.sub_add.
        ++ symmetry.
           now apply Z.sub_move_r.
        ++ apply H.
      * apply pow2_int_neq_zero.
Qed.

Lemma bv_and_or_neg_eq_zeros_one : forall (y : bitvector) (k : N),
  k <= size y -> iff
  (bv_concat (skipn (N.to_nat k) y) (zeros k) = y)
  (exists (x : Z), ((x * pow2_int_N k) mod (pow2_int_N (size y)) = (bv2int y) mod (pow2_int_N (size y)))%Z).
Proof.
  intros.
  unfold pow2_int_N, size.
  rewrite Nat2N.id.
  apply map2_and_or_map_neg_eq_mk_list_false.
  apply Nat.max_r_iff.
  rewrite <- (@Nat2N.id (length y)).
  rewrite <- N2Nat.inj_max.
  f_equal.
  now apply N.max_r_iff.
Qed.

(* x odd => x * 2^k | y (mod 2^n) <=> 2^k | y (mod 2^n) *)
Lemma rel_prime_odd_pow2_int : forall (k : nat) (x : Z),
  Z.Odd x -> Znumtheory.rel_prime x (pow2_int k).
Proof.
  intros.
  induction k.
  + apply Znumtheory.rel_prime_sym.
    apply Znumtheory.rel_prime_1.
  + apply Znumtheory.rel_prime_mult.
    - apply Znumtheory.rel_prime_mod_rev.
      * easy.
      * rewrite Zmod_odd.
        destruct (@Z.odd_spec x).
        apply H1 in H.
        rewrite H.
        apply Znumtheory.rel_prime_1.
    - apply IHk.
Qed.

Lemma divide_mod_pow2_int : forall (n k : nat) (x y : Z),
  Z.Odd x -> iff
  (exists (z : Z), (z * pow2_int k mod (pow2_int n) = y mod (pow2_int n))%Z)
  (exists (z : Z), (z * (pow2_int k * x) mod (pow2_int n) = y mod (pow2_int n))%Z).
Proof.
  split; intro; destruct H0.
  + assert (@Z.Bezout x (pow2_int n) 1%Z).
    {
      apply Z.gcd_bezout.
      apply Znumtheory.Zgcd_1_rel_prime.
      now apply rel_prime_odd_pow2_int.
    }
    destruct H1 as (a, (b, H1)).
    exists (x0 * a)%Z.
    rewrite <- Z.mul_assoc.
    rewrite (@Z.mul_assoc a).
    rewrite (@Z.mul_comm a).
    rewrite <- (@Z.mul_assoc (pow2_int k)).
    rewrite Z.mul_assoc.
    rewrite <- Zmult_mod_idemp_r.
    - replace ((a * x) mod pow2_int n)%Z with (1 mod (pow2_int n))%Z.
      * rewrite Zmult_mod_idemp_r.
        now rewrite Z.mul_1_r.
      * rewrite <- H1.
        rewrite <- Zplus_mod_idemp_r.
        rewrite Z_mod_mult.
        now rewrite Z.add_0_r.
  + exists (x0 * x)%Z.
    - rewrite <- Z.mul_assoc.
      now rewrite (@Z.mul_comm x).
Qed.

Lemma divide_mod_pow2_int_N : forall (n k : N) (x y : Z),
  Z.Odd x -> iff
  (exists (z : Z), (z * pow2_int_N k mod (pow2_int_N n) = y mod (pow2_int_N n))%Z)
  (exists (z : Z), (z * (pow2_int_N k * x) mod (pow2_int_N n) = y mod (pow2_int_N n))%Z).
Proof.
  intros.
  now apply divide_mod_pow2_int.
Qed.


(* BV -> Signed Int conversion *)

Definition sbv2int (n : N) (v : bitvector) : Z :=
  if last v false then 
    (bv2int v - pow2_int_N n)%Z
  else 
    (bv2int v)%Z.

Lemma ult_list_big_endian_list2int : forall l1 l2,
  length l1 = length l2 ->
  ult_list_big_endian l1 l2 = true ->
  (list2int (rev l1) < list2int (rev l2))%Z.
Proof.
  induction l1 as [| a l1 IHl1]; intros l2 Hlen Hult.
  - destruct l2 as [| b l2]; [| discriminate Hlen].
    simpl in Hult. discriminate Hult. 
  - destruct l2 as [| b l2]; [discriminate Hlen |].
    simpl in Hlen. injection Hlen as Hlen'.
    rewrite ult_list_big_endian_unf in Hult.
    simpl.
    rewrite !list2int_app.
    simpl.
    destruct a, b.
    + simpl in Hult. 
      rewrite orb_false_r in Hult.
      apply IHl1 in Hult; [| exact Hlen'].
      rewrite !length_rev. rewrite Hlen'.
      lia.
    + simpl in Hult. 
      discriminate Hult.
    + rewrite !length_rev. rewrite Hlen'.
      assert (H_refl : length (rev l1) = length (rev l1)) by reflexivity.
      pose proof (list2int_lt_pow2_int H_refl) as H_bound.
      rewrite length_rev in H_bound.
      assert (H_rev_l2 : (0 <= list2int (rev l2))%Z).
      { apply list2int_geq_zero. }
      change (bool2int false) with 0%Z.
      change (bool2int true) with 1%Z.
      rewrite <- Hlen'.
      lia.
    + simpl in Hult.
      rewrite orb_false_r in Hult.
      apply IHl1 in Hult; [| exact Hlen'].
      rewrite !length_rev. rewrite Hlen'.
      lia.
Qed.

Lemma ult_list_list2int : forall x y : list bool,
  length x = length y ->
  ult_list x y = true ->
  (list2int x < list2int y)%Z.
Proof.
  intros x y Hlen Hult.
  unfold ult_list in Hult.
  apply ult_list_big_endian_list2int in Hult.
  - rewrite !rev_involutive in Hult.
    exact Hult.
  - rewrite !length_rev. 
    exact Hlen.
Qed.

Lemma bv_slt_iff_sbv2int : forall n (x y : bitvector),
  size x = n -> size y = n ->
  bv_slt x y = true <-> (sbv2int n x < sbv2int n y)%Z.
Proof.
  intros n x y Hx Hy.
  unfold bv_slt, sbv2int.
  remember (last x false) as sign_x.
  remember (last y false) as sign_y.
  destruct sign_x; destruct sign_y.
  - assert (H_last_eq : last x false = last y false).
    { rewrite <- Heqsign_x. exact Heqsign_y. }
    rewrite Hx, Hy, N.eqb_refl.
    split; intro H_side.
    + assert (H_slt : bv_slt x y = true).
      { unfold bv_slt. rewrite Hx, Hy, N.eqb_refl. exact H_side. }
      assert (H_ult : bv_ult x y = true).
      { pose proof (bv_slt_ult_last_eq H_last_eq) as H_eq. rewrite <- H_eq. exact H_slt. }
      assert (Hsize_xy: size x = size y). 
      { rewrite Hx, Hy; easy. }
      apply size_len_eq in Hsize_xy.
      assert (H_unsigned_lt : (bv2int x < bv2int y)%Z).
      {
        apply ult_list_list2int.
        - assumption. 
        - unfold bv_ult in H_ult.
          rewrite Hx, Hy, N.eqb_refl in H_ult.
          assumption.
      }
      lia.
    + assert (H_unsigned_lt : (bv2int x < bv2int y)%Z) by lia.
      pose proof (bv_slt_ult_last_eq H_last_eq) as H_swap.
      unfold bv_slt in H_swap.
      rewrite Hx, Hy, N.eqb_refl in H_swap.
      rewrite H_swap.
      destruct (bv_ult x y) eqn:H_ult.
      * reflexivity.
      * assert (H_len : length x = length y).
        { apply size_len_eq. rewrite Hx, Hy. easy. }
        destruct (beq_list x y) eqn:H_eq.
        **
          apply List_eq in H_eq.
          subst x.
          lia.
        ** 
          unfold bv_ult in H_ult.
          rewrite Hx, Hy, N.eqb_refl in H_ult.
          pose proof (nlt_neq_gt H_len H_ult H_eq) as H_y_lt_x.
          symmetry in H_len.
          apply ult_list_list2int in H_y_lt_x; [| exact H_len].
          unfold bv2int in H_unsigned_lt.
          lia.
  - split; intro H.
    + assert (Hlen_x : length x = N.to_nat n).
      { rewrite <- Hx. unfold size. rewrite Nat2N.id. reflexivity. }
      pose proof (list2int_lt_pow2_int Hlen_x) as Hx_upper.
      unfold bv2int.
      assert (Hy_lower : (0 <= list2int y)%Z).
      { apply list2int_geq_zero. }
      unfold pow2_int_N.
      lia.
    + rewrite Hx, Hy. 
      rewrite N.eqb_refl.
      assert (H_slt: bv_slt x y = true).
      {
        apply bv_slt_tf.
        - rewrite Hx. rewrite Hy. reflexivity.
        - symmetry. exact Heqsign_x.
        - symmetry. exact Heqsign_y.
      }
      unfold bv_slt in H_slt.
      rewrite Hx, Hy, N.eqb_refl in H_slt.
      exact H_slt.
  - split; intro H.
    + change (bv_slt x y = true) in H.
      pose proof (bv_slt_zeros y) as Hy_is_neg.
      rewrite <- Heqsign_y in Hy_is_neg.
      rewrite Hy in Hy_is_neg.
      pose proof (bv_slt_trans H Hy_is_neg) as Hx_must_be_neg.
      pose proof (bv_slt_zeros x) as Hx_is_pos.
      rewrite <- Heqsign_x in Hx_is_pos.
      rewrite Hx in Hx_is_pos.
      rewrite Hx_is_pos in Hx_must_be_neg.
      discriminate.
    + rewrite Hx, Hy, N.eqb_refl.
      unfold bv2int in H.
      unfold pow2_int_N in H.
      assert (Hx_lower : (0 <= list2int x)%Z).
      { apply list2int_geq_zero. }
      assert (Hlen_y : length y = N.to_nat n).
      { rewrite <- Hy. unfold size. rewrite Nat2N.id. reflexivity. }
      pose proof (list2int_lt_pow2_int Hlen_y) as Hy_upper.
      lia.
  - rewrite Hx, Hy, N.eqb_refl.
    assert (H_last_eq : last x false = last y false).
    { rewrite <- Heqsign_x. exact Heqsign_y. }
    split; intro H_side.
    + assert (H_slt : bv_slt x y = true).
      { unfold bv_slt. rewrite Hx, Hy, N.eqb_refl. exact H_side. }
      assert (H_ult : bv_ult x y = true).
      { pose proof (bv_slt_ult_last_eq H_last_eq) as H_eq. rewrite <- H_eq. exact H_slt. }
      assert (Hsize_xy: size x = size y).
      { rewrite Hx, Hy. easy. }
      apply size_len_eq in Hsize_xy.
      assert (H_unsigned_lt : (bv2int x < bv2int y)%Z).
      {
        apply ult_list_list2int.
        - assumption. 
        - unfold bv_ult in H_ult.
          rewrite Hx, Hy, N.eqb_refl in H_ult.
          assumption.
      }
      lia.
    + assert (H_unsigned_lt : (bv2int x < bv2int y)%Z) by lia.
      pose proof (bv_slt_ult_last_eq H_last_eq) as H_swap.
      unfold bv_slt in H_swap.
      rewrite Hx, Hy, N.eqb_refl in H_swap.
      rewrite H_swap.
      destruct (bv_ult x y) eqn:H_ult.
      * reflexivity.
      * assert (H_len : length x = length y).
        { apply size_len_eq. rewrite Hx, Hy. easy. }
        destruct (beq_list x y) eqn:H_eq.
        **
          apply List_eq in H_eq.
          subst x.
          lia.
        **
          unfold bv_ult in H_ult.
          rewrite Hx, Hy, N.eqb_refl in H_ult.
          pose proof (nlt_neq_gt H_len H_ult H_eq) as H_y_lt_x.
          symmetry in H_len.
          apply ult_list_list2int in H_y_lt_x; [| exact H_len].
          unfold bv2int in H_unsigned_lt.
          lia.
Qed.

Lemma mod_pow2_step : forall X D M, 
  (M > 0)%Z ->
  (0 <= D < 2)%Z ->
  (2 * (X mod M) + D)%Z = ((2 * X + D) mod (2 * M))%Z.
Proof.
  intros X D M HM HD.
  apply Z.mod_unique with (q := (X / M)%Z).
  - assert (Hgt : (0 < M)%Z) by lia.
    pose proof (Z.mod_pos_bound X M) as Hbound.
    specialize (Hbound Hgt).
    lia.
  - assert (Hneq : M <> 0%Z) by lia.
    pose proof (Z.div_mod X M) as Hdiv.
    specialize (Hdiv Hneq).
    remember (X / M)%Z as q.
    remember (X mod M)%Z as r.
    rewrite Hdiv.
    ring.
Qed.  

Lemma list2int_add_list_ingr : forall bs1 bs2 c,
  length bs1 = length bs2 ->
  list2int (add_list_ingr bs1 bs2 c) = 
  ((list2int bs1 + list2int bs2 + bool2int c) mod pow2_int (length bs1))%Z.
Proof.
  induction bs1 as [| b1 bs1 IH]; intros bs2 c Hlen.
  - destruct bs2; try discriminate Hlen.
    simpl.
    destruct c; reflexivity.
  - destruct bs2 as [| b2 bs2]; try discriminate Hlen.
    simpl in Hlen. injection Hlen as Hlen'.
    simpl add_list_ingr.
    destruct (add_carry b1 b2 c) as [r c0] eqn:Hcarry.
    rewrite !list2int_cons.
    rewrite IH; [| exact Hlen'].
    destruct b1; destruct b2; destruct c.
    inversion Hcarry; subst; clear Hcarry; simpl bool2int.
    + pose proof (zero_lt_pow2_int (length bs1)).
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * lia.
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
    + inversion Hcarry. subst. clear Hcarry.
      simpl bool2int.
      simpl length.
      replace (pow2_int (S (length bs1))) with (2 * pow2_int (length bs1))%Z by (simpl; lia).
      rewrite mod_pow2_step.
      * f_equal. lia.
      * pose proof (zero_lt_pow2_int (length bs1)).
        lia. 
      * lia.
Qed.

Lemma list2int_subst_list : forall bs1 bs2,
  length bs1 = length bs2 ->
  list2int (subst_list' bs1 bs2) = 
  ((list2int bs1 + list2int (twos_complement bs2)) mod pow2_int (length bs1))%Z.
Proof.
  intros bs1 bs2 Hlen.
  unfold subst_list', add_list.
  rewrite list2int_add_list_ingr.
  - simpl bool2int. f_equal. lia.
  - rewrite <- length_twos_complement. easy.
Qed.

Lemma list2int_twos_complement : forall b,
  list2int (twos_complement b) = 
  ((list2int (map negb b) + 1) mod pow2_int (length b))%Z.
Proof.
  intros b; unfold twos_complement; rewrite list2int_add_list_ingr.
  - simpl bool2int; rewrite list2int_mk_list_false, <- not_list_length; f_equal; lia. 
  - rewrite length_map, length_mk_list_false; reflexivity.
Qed. 

Lemma list2int_twos_complement_one : forall n,
  n <> 0%N -> 
  ((1 + list2int (twos_complement (one n))) mod pow2_int_N n)%Z = 0%Z.
Proof.
  intros n Hneq_zero.
  pose proof (add_neg_list_absorb (bits (one n))) as Hzero.
  apply (f_equal list2int) in Hzero. unfold add_list in Hzero.
  rewrite list2int_add_list_ingr in Hzero.
  2:{ apply length_twos_complement. }
  simpl bool2int in Hzero.
  replace (list2int (bits (one n)) + list2int (twos_complement (bits (one n))) + 0)%Z 
    with (1 + list2int (twos_complement (bits (one n))))%Z in Hzero.
  2:{ assert (H: list2int (one n) = 1%Z). 
      { unfold one. rewrite list2int_mk_list_one.
        symmetry. rewrite Z.mod_small. 
        - lia. 
        - destruct (N.to_nat n) as [| m] eqn:Hnat.
          + lia. 
          + rewrite pow2_int_succ. pose proof (zero_lt_pow2_int m) as Hgt_zero.
            lia. }
      replace (list2int (bits (one n))) with 1%Z. lia. }
  replace (list2int (mk_list_false (length (bits (one n))))) with 0%Z in Hzero.
  2:{  rewrite list2int_mk_list_false. reflexivity. }
  replace (pow2_int (length (bits (one n)))) with (pow2_int_N n) in Hzero.
  2:{ unfold pow2_int_N. f_equal. unfold one. unfold bits. 
      rewrite length_mk_list_one. reflexivity. }
  exact Hzero.
Qed.

Lemma list2int_twos_complement_one_exact : forall n,
  n <> 0%N -> list2int (twos_complement (one n)) = (pow2_int_N n - 1)%Z.
Proof.
  intros n Hneq. pose proof (list2int_twos_complement_one Hneq) as Hmod.
  assert (Hbounds : (0 <= list2int (twos_complement (one n)) < pow2_int_N n)%Z).
  { split.
    - apply list2int_geq_zero.
    - replace (pow2_int_N n) with (pow2_int (length (twos_complement (one n)))).
      + apply list2int_lt_pow2_int. reflexivity.
      + unfold pow2_int_N. f_equal. rewrite <- length_twos_complement.
        unfold one. rewrite length_mk_list_one. reflexivity. }
  assert (Hpos : (0 < pow2_int_N n)%Z). { apply zero_lt_pow2_int. }
  assert (Hneq_P : pow2_int_N n <> 0%Z) by lia.
  pose proof (Z.div_mod (1 + list2int (twos_complement (one n))) (pow2_int_N n) Hneq_P) as Hdiv.
  rewrite Hmod in Hdiv.
  remember (((1 + list2int (twos_complement (one n))) / pow2_int_N n)%Z) as q.
  remember (list2int (twos_complement (one n))) as X. remember (pow2_int_N n) as P.
  assert (H_mult_bounds : (1 <= P * q + 0 <= P)%Z) by lia.
  assert (H_q : q = 1%Z) by nia. rewrite H_q in Hdiv. lia.
Qed.

Lemma sbv2int_sub_one : forall n (t : bitvector),
  size t = n -> t <> signed_min n ->
  sbv2int n (bv_subt' t (one n)) = (sbv2int n t - 1)%Z.
Proof.
  intros n t Hsize Hneq; unfold sbv2int, bv_subt', bv2int.
  replace (size t =? size (one n)) with true by (symmetry; apply N.eqb_eq; rewrite one_size; apply Hsize).
  destruct (last (bits t) false) eqn:Hsign_t; destruct (last (subst_list' (bits t) (bits (one n))) false) eqn:Hsign_sub.
  - replace (last t false) with true; rewrite list2int_subst_list.
    2:{ unfold bits; apply size_len_eq; rewrite one_size; apply Hsize. }
    replace (pow2_int (length (bits t))) with (pow2_int_N n) by (unfold pow2_int_N; f_equal; rewrite bits_size, Hsize; reflexivity).
    assert (Hneq_zero : n <> 0%N). 
    { intro Hzero; rewrite Hzero in Hsize; destruct (bits t) eqn:Hbits; [discriminate | ]. assert (Hcontra : length (bits t) = 0%nat) by (rewrite bits_size, Hsize; reflexivity). rewrite Hbits in Hcontra; discriminate. }
    unfold bits; pose proof (list2int_twos_complement_one Hneq_zero) as Hcomp.
    replace (list2int t + list2int (twos_complement (one n)))%Z 
       with (list2int t - 1 + (1 + list2int (twos_complement (one n))))%Z by lia.
    assert (Hpow_pos : (0 < pow2_int_N n)%Z) by apply zero_lt_pow2_int.
    rewrite Z.add_mod by lia; rewrite Hcomp.
    replace (((list2int t - 1) mod pow2_int_N n + 0)%Z) with ((list2int t - 1) mod pow2_int_N n)%Z by lia.
    rewrite Z.mod_mod by lia; rewrite Z.mod_small; [lia | split].
    * assert (Hnot_empty : bits t <> []) by (intros Hempty; rewrite Hempty in Hsign_t; discriminate).
      destruct (exists_last Hnot_empty) as [front [last_bit Hdecomp]].
      assert (Hlast : last_bit = true) by (rewrite Hdecomp, last_app in Hsign_t; exact Hsign_t).
      subst last_bit; unfold bits in Hdecomp; rewrite Hdecomp, list2int_app, list2int_bool; unfold bool2int.
      pose proof list2int_geq_zero as Hfront_pos.
      assert (Hpow_lb : (pow2_int (length front) >= 1)%Z) by (pose proof (zero_lt_pow2_int (length front)); lia).
      specialize (Hfront_pos front); lia.
    * change (list2int t) with (list2int (bits t)).
      set (m := length (bits t)); pose proof (@list2int_lt_pow2_int (bits t) m eq_refl) as Hmax.
      assert (Hm_n : pow2_int m = pow2_int_N n) by (unfold m, pow2_int_N; f_equal; rewrite bits_size, Hsize; reflexivity).
      rewrite Hm_n in Hmax; lia.
  - exfalso.
    assert (Hnot_empty : bits t <> []) by (intros Hempty; rewrite Hempty in Hsign_t; discriminate).
    assert (Hdecomp_t : bits t = removelast (bits t) ++ [true]) by (rewrite <- Hsign_t; apply app_removelast_last; easy).
    assert (Hval_t : list2int (bits t) = (pow2_int (length (removelast (bits t))) + list2int (removelast (bits t)))%Z) 
      by (rewrite Hdecomp_t, list2int_app, list2int_bool; simpl (bool2int true); rewrite <- Hdecomp_t; lia).
    pose proof (@list2int_geq_zero (removelast (bits t))) as Hfront_pos.
    set (sub_list := subst_list' (bits t) (bits (one n))) in *.
    assert (Hlen_sub : length sub_list = length (bits t)) 
      by (unfold sub_list; assert (size_eq: length (bits t) = length (bits (one n))) by (rewrite !bits_size, one_size, Hsize; reflexivity); rewrite <- (subst_list'_length size_eq); reflexivity).
    assert (Hdecomp_sub : sub_list = removelast sub_list ++ [false]). 
    { rewrite <- Hsign_sub; apply app_removelast_last; intro Hempty.
      assert (Hlen0 : length sub_list = 0%nat) by (rewrite Hempty; reflexivity).
      rewrite Hlen_sub in Hlen0; destruct (bits t) eqn:Heq_t; [apply Hnot_empty; reflexivity | discriminate Hlen0]. }
    assert (Hval_sub : list2int sub_list = list2int (removelast sub_list)) 
      by (rewrite Hdecomp_sub, list2int_app, list2int_bool; simpl (bool2int false); rewrite <- Hdecomp_sub; lia).
    pose proof (@list2int_lt_pow2_int (removelast sub_list) (length (removelast sub_list)) eq_refl) as Hsub_upper.
    assert (Hlen_eq : length (bits t) = length (bits (one n))) by (apply size_len_eq; unfold bits; rewrite one_size; easy).
    pose proof (@list2int_subst_list (bits t) (bits (one n)) Hlen_eq) as Hsubst_mod.
    assert (Hlen_t : length (bits t) = S (length (removelast (bits t)))) by (rewrite Hdecomp_t at 1; rewrite length_app; simpl; lia).
    assert (Hpow_t : pow2_int (length (bits t)) = (2 * pow2_int (length (removelast (bits t))))%Z) by (rewrite Hlen_t; apply pow2_int_succ).
    assert (Hlen_sub_S : length sub_list = S (length (removelast sub_list))) by (rewrite Hdecomp_sub at 1; rewrite length_app; simpl; lia).
    assert (Hlen_rem : length (removelast sub_list) = length (removelast (bits t))) by lia.
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z). {
      assert (Hn_neq_0 : n <> 0%N) by (intro Heq; rewrite Heq in Hlen_eq; simpl in Hlen_eq; rewrite Hlen_eq in Hlen_t; discriminate Hlen_t).
      apply (list2int_twos_complement_one_exact Hn_neq_0).
    }
    assert (Hpos_pow : (0 < pow2_int (length (bits t)))%Z) by apply zero_lt_pow2_int.
    assert (Ht_bound : (list2int (bits t) < pow2_int (length (bits t)))%Z) by (apply list2int_lt_pow2_int; reflexivity).
    assert (Ht_val_exact : list2int (bits t) = pow2_int (length (removelast (bits t)))). {
      rewrite Hlen_rem in Hsub_upper; rewrite Htc in Hsubst_mod; Z.div_mod_to_equations.
      assert (H_not_zero : pow2_int (length (bits t)) <> 0%Z) by lia; specialize (H H_not_zero).
      assert (Hr_val : r = list2int (removelast sub_list)) by (rewrite <- Hsubst_mod; exact Hval_sub).
      remember (list2int (bits t)) as X; remember (pow2_int (length (removelast (bits t)))) as P.
      remember (list2int (removelast (bits t))) as Y; remember (list2int (removelast sub_list)) as R_sub.
      assert (Hpow_eq : pow2_int_N n = pow2_int (length (bits t))) by (unfold pow2_int_N; f_equal; rewrite bits_size, Hsize; easy).
      rewrite Hpow_eq, Hpow_t in *; assert (Hq_min : (0 < q)%Z) by nia; assert (Hq_max : (q < 2)%Z) by nia.
      assert (Hq : q = 1%Z) by lia; rewrite Hq in H; lia.
    }
    assert (H_signed_min_val : list2int (bits (signed_min n)) = pow2_int (length (removelast (bits t)))). {
      assert (H_t_n : N.to_nat n = length (bits t)) by (rewrite bits_size, Hsize; easy).
      unfold signed_min; rewrite H_t_n, Hlen_t; unfold smin_big_endian, bits; cbn; rewrite list2int_app; simpl.
      rewrite length_rev.
      assert (Hlen_false : length (mk_list_false (length (removelast t))) = length (removelast t)) by apply length_mk_list_false.
      rewrite Hlen_false.
      assert (Hval_false : list2int (rev (mk_list_false (length (removelast t)))) = 0%Z) by (rewrite rev_mk_list_false; apply list2int_mk_list_false).
      rewrite Hval_false; lia.
    }
    assert (H_same_val : list2int (bits t) = list2int (bits (signed_min n))) by (rewrite Ht_val_exact; symmetry; exact H_signed_min_val).
    apply list2int_inj in H_same_val.
    + contradiction (Hneq H_same_val).
    + apply size_len_eq; unfold bits; rewrite signed_min_size; easy.
  - unfold bits in Hsign_t; rewrite Hsign_t.
    assert (Hlen_eq : length (bits t) = length (bits (one n))) by (unfold bits; apply size_len_eq; rewrite one_size; easy).
    pose proof (list2int_subst_list Hlen_eq) as Hsubst_mod.
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z). {
      assert (Hn_neq_0 : n <> 0%N). {
        intro Heq; rewrite Heq in Hlen_eq; simpl in Hlen_eq.
        destruct (bits t) as [| b bs] eqn:Hbits_t.
        - rewrite Heq in Hsign_sub; compute in Hsign_sub; discriminate Hsign_sub.
        - discriminate Hlen_eq.
      }
      apply (list2int_twos_complement_one_exact Hn_neq_0).
    }
    rewrite Htc in Hsubst_mod; rewrite Hsubst_mod.
    assert (H_t_zero : list2int (bits t) = 0%Z). {
      assert (H_upper : (list2int (bits t) < pow2_int (length (bits t) - 1))%Z). {
        assert (Hnot_empty : bits t <> []). {
          intro Hempty; assert (Hone_empty : bits (one n) = []) by (destruct (bits (one n)); [reflexivity | rewrite Hempty in Hlen_eq; discriminate]).
          rewrite Hempty, Hone_empty in Hsign_sub; discriminate Hsign_sub.
        }
        assert (Hdecomp : bits t = removelast (bits t) ++ [false]) by (rewrite (app_removelast_last false Hnot_empty); unfold bits; rewrite Hsign_t, rl_fact; reflexivity).
        rewrite Hdecomp, list2int_app, list2int_bool; simpl bool2int; rewrite Z.mul_0_r, Z.add_0_l.
        assert (Hlen_rem : (length (bits t) - 1)%nat = length (removelast (bits t))) by (rewrite Hdecomp at 1; rewrite length_app; simpl; lia).
        rewrite length_app; simpl; replace (length (removelast (bits t)) + 1 - 1)%nat with (length (removelast (bits t))) by lia.
        apply list2int_lt_pow2_int; reflexivity.
      }
      assert (H_lower : (pow2_int (length (bits t) - 1) <= list2int (subst_list' (bits t) (bits (one n))))%Z). {
        remember (subst_list' (bits t) (bits (one n))) as sub_list.
        assert (Hnot_empty_sub : sub_list <> []) by (intro Hempty; rewrite Hempty in Hsign_sub; discriminate Hsign_sub).
        assert (Hdecomp_sub : sub_list = removelast sub_list ++ [true]) by (rewrite (app_removelast_last false Hnot_empty_sub) at 1; rewrite Hsign_sub; reflexivity).
        rewrite Hdecomp_sub at 1; rewrite list2int_app, list2int_bool; simpl bool2int; rewrite Z.mul_1_r.
        assert (Hlen_rem_sub : length (removelast sub_list) = (length (bits t) - 1)%nat). {
          assert (Hlen_sub : length sub_list = length (bits t)) by (rewrite Heqsub_list; unfold bits; assert (Hsize_eq: length t = length (one n)) by (apply size_len_eq; rewrite one_size; easy); rewrite (subst_list'_length Hsize_eq); easy).
          assert (Hlen_math : length sub_list = (length (removelast sub_list) + 1)%nat) by (rewrite Hdecomp_sub at 1; rewrite length_app; simpl; lia).
          lia.
        }
        rewrite Hlen_rem_sub; pose proof (@list2int_geq_zero (removelast sub_list)) as Hfront_pos; lia.
      }
      assert (H_t_pos : (0 <= list2int (bits t))%Z) by apply list2int_geq_zero.
      assert (H_half_pos : (0 < pow2_int (length (bits t) - 1))%Z) by apply zero_lt_pow2_int.
      assert (H_pow_split : pow2_int (length (bits t)) = (2 * pow2_int (length (bits t) - 1))%Z). {
        assert (H_length_pos : (0 < (length (bits t)))%nat) by (destruct (bits t) eqn:Heq_bits; [simpl in Hsign_sub; discriminate Hsign_sub | simpl; lia]).
        replace (length (bits t)) with (S (length (bits t) - 1)) at 1 by lia; simpl pow2_int; reflexivity.
      }
      assert (Hpow_eq : pow2_int_N n = pow2_int (length (bits t))) by (unfold pow2_int_N; f_equal; rewrite bits_size, Hsize; easy).
      rewrite Hpow_eq in Hsubst_mod; rewrite Hsubst_mod in H_lower.
      remember (list2int (bits t)) as X; remember (pow2_int (length (bits t) - 1)) as HalfP; rewrite H_pow_split in *; Z.div_mod_to_equations.
      assert (H_2P_pos : (0 < 2 * HalfP)%Z) by lia; assert (H_2P_neq : (2 * HalfP <> 0)%Z) by lia.
      specialize (H H_2P_neq); specialize (H0 H_2P_pos).
      assert (Hq : q = 0%Z) by nia; rewrite Hq in H; lia.
    }
    rewrite H_t_zero; change (list2int t) with (list2int (bits t)); rewrite H_t_zero.
    assert (Hpow_eq : pow2_int (length (bits t)) = pow2_int_N n) by (unfold pow2_int_N; f_equal; rewrite bits_size, Hsize; easy).
    rewrite Hpow_eq, Z.mod_small; [lia | assert (H_P_pos : (0 < pow2_int_N n)%Z) by apply zero_lt_pow2_int; lia].
  - unfold bits in Hsign_t; rewrite Hsign_t.
    assert (Hlen_eq : length (bits t) = length (bits (one n))) by (unfold bits; apply size_len_eq; rewrite one_size; easy).
    rewrite (list2int_subst_list Hlen_eq).
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z). {
      apply list2int_twos_complement_one_exact; intro Hzero.
      assert (Ht_empty : bits t = []) by (destruct (bits t) eqn:Heq_t; [reflexivity | assert (Hlen : length (bits t) = 0%nat) by (rewrite bits_size, Hsize, Hzero; reflexivity); rewrite Heq_t in Hlen; discriminate Hlen]).
      assert (Hsmin_empty : bits (signed_min n) = []) by (destruct (bits (signed_min n)) eqn:Heq_smin; [reflexivity | assert (Hlen : length (bits (signed_min n)) = 0%nat) by (rewrite bits_size, signed_min_size, Hzero; reflexivity); rewrite Heq_smin in Hlen; discriminate Hlen]).
      assert (Hbits_eq : bits t = bits (signed_min n)) by (rewrite Ht_empty, Hsmin_empty; reflexivity).
      unfold bits in Hbits_eq; contradiction.
    }
    rewrite Htc.
    assert (Hpow_eq : pow2_int (length (bits t)) = pow2_int_N n) by (unfold pow2_int_N; f_equal; rewrite bits_size, Hsize; easy).
    rewrite Hpow_eq; replace (list2int (bits t) + (pow2_int_N n - 1))%Z with (list2int (bits t) - 1 + 1 * pow2_int_N n)%Z by lia.
    assert (Hpow_neq_0 : pow2_int_N n <> 0%Z) by (pose proof (zero_lt_pow2_int (length (bits t))); lia).
    rewrite Z.mod_add by exact Hpow_neq_0; rewrite Z.mod_small.
    + change (list2int t) with (list2int (bits t)); lia.
    + split; [| assert (Hlen: length (bits t) = N.to_nat(n)) by (rewrite bits_size, Hsize; reflexivity); pose proof (list2int_lt_pow2_int Hlen) as H_lt; rewrite <- Hlen, Hpow_eq in H_lt; lia].
      assert (H_t_pos : (0 <= list2int (bits t))%Z) by apply list2int_geq_zero.
      assert (Ht_not_zero : list2int (bits t) <> 0%Z). {
        intro Hzero; pose proof (list2int_subst_list Hlen_eq) as Hsub_mod.
        rewrite Htc, Hpow_eq, Hzero, Z.add_0_l in Hsub_mod.
        rewrite Z.mod_small in Hsub_mod; [| pose proof (zero_lt_pow2_int (length (bits t))); lia].
        remember (subst_list' (bits t) (bits (one n))) as sub.
        assert (Hnot_empty : sub <> []). {
          intro Hempty; rewrite Hempty in Hsub_mod; simpl list2int in Hsub_mod; rewrite <- Hpow_eq in Hsub_mod.
          assert (Hlen_0 : length (bits t) = 0%nat) by (destruct (length (bits t)) eqn:Heq_len; [reflexivity | simpl pow2_int in Hsub_mod; pose proof (zero_lt_pow2_int n0); change (match pow2_int n0 with | 0%Z => 0%Z | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0 end) with (2 * pow2_int n0)%Z in Hsub_mod; lia]).
          assert (Ht_empty : bits t = []) by (destruct (bits t); [reflexivity | discriminate Hlen_0]).
          assert (Hsmin_empty : bits (signed_min n) = []) by (destruct (bits (signed_min n)) eqn:Heq_smin; [reflexivity | assert (Hlen_smin : length (bits (signed_min n)) = 0%nat) by (rewrite bits_size, signed_min_size, <- Hsize, <- bits_size, Ht_empty; reflexivity); rewrite Heq_smin in Hlen_smin; discriminate Hlen_smin]).
          assert (Hbits_eq : t = signed_min n) by (unfold bits in Ht_empty, Hsmin_empty; rewrite Hsmin_empty; easy).
          contradiction (Hneq Hbits_eq).
        }
        assert (Hdecomp : sub = removelast sub ++ [false]) by (rewrite (app_removelast_last false Hnot_empty) at 1; rewrite Hsign_sub; reflexivity).
        rewrite Hdecomp, list2int_app, list2int_bool in Hsub_mod; simpl bool2int in Hsub_mod; rewrite Z.mul_0_r, Z.add_0_l in Hsub_mod.
        pose proof (@list2int_lt_pow2_int (removelast sub) (length (removelast sub)) eq_refl) as Hmax.
        assert (Hlen_sub : length sub = length (bits t)) by (rewrite Heqsub, <- (subst_list'_length Hlen_eq); reflexivity).
        assert (Hlen_math : length sub = S (length (removelast sub))) by (rewrite Hdecomp at 1; rewrite length_app; simpl; lia).
        assert (Hpow_split : pow2_int_N n = (2 * pow2_int (length (removelast sub)))%Z) by (rewrite <- Hpow_eq, <- Hlen_sub, Hlen_math; simpl pow2_int; reflexivity).
        rewrite Hsub_mod in Hmax; rewrite Hpow_split in *; assert (H_P_pos : (0 < pow2_int (length (removelast sub)))%Z) by apply zero_lt_pow2_int; lia.
      }
      lia.
Qed.

Lemma sbv2int_pos_iff : forall n (x : bitvector),
  size x = n ->
  (0 <= sbv2int n x)%Z <-> last x false = false.
Proof.
  intros n x Hsize; unfold sbv2int; destruct (last x false) eqn:Hsign.
  - split; intro H; [| discriminate].
    unfold bv2int, pow2_int_N in H.
    assert (H_len : length x = N.to_nat n) by (unfold size in Hsize; lia).
    pose proof (list2int_lt_pow2_int H_len) as H_bound; lia.
  - split; intro H; [reflexivity | unfold bv2int; apply list2int_geq_zero].
Qed.

(*-t = ~t + 1 *)
Lemma bv_neg_is_not_plus_one : forall (a : bitvector) (n : N), 
  size a = n -> 
  bv_neg a = bv_add (bv_not a) (one n).
Proof.
  intros a n Hs. unfold bv_neg. unfold twos_complement. unfold bv_add.
  match goal with
  | [ |- _ = (if ?CHECK then _ else _) ] => replace CHECK with true
  end.
  2: { symmetry. apply N.eqb_eq. apply bv_not_size.
       rewrite one_size. easy. }
  assert (H_zeros: forall m : nat, add_list_ingr (mk_list_false m) (mk_list_false m) false = mk_list_false m).
  { intro m. induction m as [|m' IHm]; simpl.
    - reflexivity.
    - f_equal. exact IHm. }
  assert (H_one: one n = add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true).
  { unfold one. induction (N.to_nat n) as [|k IH].
    - reflexivity.
    - destruct k.
      + reflexivity. 
      + simpl in *. rewrite IH. simpl. f_equal. rewrite (H_zeros k). 
        clear. induction k; simpl; [reflexivity | f_equal; apply IHk]. }
  replace (length a) with (N.to_nat n).
  2: { rewrite <- Hs. unfold size. rewrite Nat2N.id. reflexivity. }
  rewrite H_one. unfold add_list, bv_not. unfold bits in *. 
  replace (add_list_ingr (map negb a) (add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true) false)
     with (add_list_ingr (add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true) (map negb a) false).
  2: { apply add_list_carry_comm. }
  rewrite <- bv_neg_involutive_aux. rewrite H_zeros.
  rewrite add_list_carry_comm. reflexivity.
Qed.

Lemma neg_bvand_neg : forall (x y : bitvector) (n : N), 
  size x = n -> size y = n -> 
  last x false = true ->
  last y false = true ->
  last (bv_and x y) false = true.
Proof.
  intros x y n Hx Hy Hx_neg Hy_neg.
  rewrite <- hd_rev.
  rewrite <- hd_rev in Hx_neg, Hy_neg.
  unfold bv_and.
  rewrite Hx, Hy.
  rewrite N.eqb_refl.
  rewrite rev_map2_and. 
  unfold bits.
  destruct (rev x) as [|hx tx] eqn:Hrx.
  - simpl in Hx_neg.
    discriminate.
  - destruct (rev  y) as [|hy ty] eqn:Hry.
    + simpl in Hy_neg. discriminate Hy_neg.
    + simpl. 
      simpl in Hx_neg, Hy_neg.
      rewrite Hx_neg, Hy_neg.
      reflexivity.
  - unfold bits. 
    apply size_len_eq.
    rewrite Hx, Hy.
    reflexivity.
Qed.

(* MSB(a) = 0 -> MSB(a && b) = 0 *)
Lemma pos_bvand_pos : forall (x y : bitvector) (n : N), 
  size x = n -> size y = n -> last x false = false -> last (bv_and x y) false = false.
Proof.
  intros x y n Hx Hy H. rewrite <- hd_rev in *.
  unfold bv_and. rewrite Hx, Hy. assert (n =? n = true) by apply N.eqb_refl. rewrite H0.
  rewrite rev_map2_and. unfold bits. induction (rev x).
  + induction (rev y).
    - easy.
    - easy.
  + unfold hd in H. rewrite H. unfold hd. induction (rev y).
    - easy.
    - case a0; easy.
  + pose proof bits_size as bits_size.
    rewrite !bits_size. rewrite Hx, Hy. easy.
Qed.

Lemma bv_sle_ule_same_sign : forall (n : N) (a b : bitvector),
  size a = n -> size b = n -> last a false = last b false ->
  bv_sle a b = bv_ule a b.
Proof.
  intros n a b Ha Hb Hsign.
  unfold bv_sle, bv_ule. rewrite Ha, Hb, (N.eqb_refl n).
  unfold sle_list, sle_list_big_endian, ule_list,
  ule_list_big_endian.
  destruct (rev a) as [|xi x'] eqn:Ra;
  destruct (rev b) as [|yi y'] eqn:Rb.
  - reflexivity.
  - exfalso. assert (Hlen : length (rev a) = length (rev b)).
    { rewrite Ra, Rb. simpl. unfold size in Ha, Hb.
      rewrite <- (length_rev a) in Ha.
      rewrite <- (length_rev b) in Hb.
      rewrite Ra in Ha. rewrite Rb in Hb. simpl in Ha.
      subst n. apply (Nat2N.inj_iff (S (length y')) 0) in Hb.
      symmetry. exact Hb. }
    rewrite Ra, Rb in Hlen. simpl in Hlen. discriminate.
  - exfalso. assert (Hlen : length (rev a) = length (rev b)).
    { rewrite Ra, Rb. simpl. unfold size in Ha, Hb.
      rewrite <- (length_rev a) in Ha.
      rewrite <- (length_rev b) in Hb.
      rewrite Ra in Ha. rewrite Rb in Hb. simpl in Ha.
      subst n. simpl in Hb. discriminate Hb. }
    rewrite Ra, Rb in Hlen. simpl in Hlen. discriminate.
  - rewrite <- hd_rev, <- hd_rev, Ra, Rb in Hsign.
    simpl in Hsign. subst xi. destruct yi; simpl;
    reflexivity.
Qed.

Lemma bv_and_neg_sle_itself : forall n (a s : bitvector),
  size a = n -> size s = n ->
  bv_slt s (zeros n) = true ->  
  bv_sle (bv_and a s) a = true.
Proof.
  intros n a s Ha Hs Hs_neg.
  rewrite <- Hs in Hs_neg. 
  rewrite bv_slt_zeros in Hs_neg.
  destruct (last a false) eqn:Ha_sign.
  - assert (H_res_sign : last (bv_and a s) false = true).
    { apply (neg_bvand_neg Ha Hs Ha_sign Hs_neg). }
    rewrite bv_sle_ule_same_sign with (n := n).
    + apply bv_ule_and; rewrite Ha, Hs; reflexivity.
    + apply (bv_and_size Ha Hs).
    + exact Ha.
    + rewrite H_res_sign, Ha_sign. reflexivity.
  - assert (H_res_sign : last (bv_and a s) false = false).
    { apply (pos_bvand_pos Ha Hs). assumption. }
    rewrite bv_sle_ule_same_sign with (n := n).
    + apply bv_ule_and; rewrite Ha, Hs; reflexivity.
    + apply (bv_and_size Ha Hs).
    + exact Ha.
    + rewrite H_res_sign, Ha_sign. reflexivity.
Qed.

Lemma bv_and_pos_sle_1: forall n (a b : bitvector),
  size a = n -> size b = n ->
  last a false = false -> 
  last b false = false ->
  bv_sle (bv_and a b) a = true.
Proof.
  intros.
  rewrite bv_sle_ule_same_sign with (n := n).
  2: { apply bv_and_size. easy. easy. }
  2: { easy. }
  2: { 
      rewrite pos_bvand_pos with (n := n).
      - easy.
      - easy.
      - easy.
      - easy.
  }
  apply bv_ule_and.
  rewrite H, H0. easy.
Qed.

Lemma bv_and_pos_sle_2: forall n (a b : bitvector),
  size a = n -> size b = n ->
  last a false = false -> 
  last b false = false -> 
  bv_sle (bv_and a b) b = true.
Proof.
  intros.
  rewrite (bv_and_comm H H0).
  apply (bv_and_pos_sle_1 H0 H H2 H1).
Qed.

Lemma bv_not_neg_is_subt_one : forall (n : N) (t : bitvector),
  size t = n ->
  bv_not (bv_neg t) = bv_subt' t (one n).
Proof.
  intros n t Ht.
  assert (H_sizes : size (one n) = n /\ size t = n /\ size (bv_not (bv_neg t)) = n).
  { 
    split. apply one_size.
    split. exact Ht.
    apply bv_not_size. apply bv_neg_size. exact Ht.
  }
  apply (proj1 (bvadd_U H_sizes)).
  rewrite <- bv_neg_involutive.
  symmetry. 
  apply bv_neg_is_not_plus_one.
  apply bv_neg_size. exact Ht.
Qed.

Lemma not_signed_min_if_gt : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  bv_slt s t = true ->
  t <> signed_min n.
Proof.
  intros n s t Hs Ht Hs_lt_t.
  intro H_is_min.
  rewrite H_is_min in Hs_lt_t.
  pose proof (signed_min_sle s) as H_imp.
  rewrite Hs in H_imp. 
  rewrite bv_sle_eq in H_imp.  
  destruct H_imp as [H_min_lt_val | H_min_eq_val].
  + pose proof (bv_slt_trans Hs_lt_t H_min_lt_val) as H_cycle.
    rewrite bv_slt_nrefl in H_cycle. 
    discriminate.
  + rewrite <- H_min_eq_val in Hs_lt_t.
    rewrite bv_slt_nrefl in Hs_lt_t.
    discriminate.
Qed.

Lemma bv_not_neg_slt : forall (n : N) (t : bitvector),
  size t = n ->
  t <> signed_min n ->
  bv_slt (bv_not (bv_neg t)) t = true.
Proof.
  intros n t Ht H_not_min.
  rewrite bv_slt_iff_sbv2int with (n := n).
  - rewrite (bv_not_neg_is_subt_one Ht).
    rewrite (sbv2int_sub_one Ht H_not_min).
    lia.
  - apply bv_not_size. 
    apply bv_neg_size.
    exact Ht. 
  - easy.
Qed.

Lemma pos_bv_and : forall (n : N) (x s : bitvector),
  size x = n ->
  size s = n ->
  last s false = false ->
  last (bv_and x s) false = false.
Proof.
  intros n x s Hx_size Hs_size H_s_pos.
  rewrite (bv_and_comm Hx_size Hs_size).
  apply (pos_bvand_pos Hs_size Hx_size H_s_pos).
Qed.

Lemma bv_not_neg_pos_if_gt_zero : forall (n : N) (t : bitvector),
  size t = n ->
  t <> signed_min n ->
  bv_slt (zeros n) t = true ->
  last (bv_not (bv_neg t)) false = false.
Proof.
  intros n t Ht H_not_min H_t_pos.
  assert (H_size : size (bv_not (bv_neg t)) = n).
  { apply bv_not_size. apply bv_neg_size. exact Ht. }
  pose proof (sbv2int_pos_iff H_size) as H_iff.
  apply H_iff.
  rewrite (bv_not_neg_is_subt_one Ht).
  rewrite sbv2int_sub_one with (n := n).
  2: { exact Ht. }
  2: { exact H_not_min. }
  assert (H_zeros_sz : size (zeros n) = n).
  { apply zeros_size. }
  pose proof (@bv_slt_iff_sbv2int n (zeros n) t H_zeros_sz Ht) as H_slt_bridge.
  apply -> H_slt_bridge in H_t_pos. 
  assert (H_zero_val : sbv2int n (zeros n) = 0%Z).
  {
    unfold sbv2int.
    rewrite bv2int_zeros. 
    unfold zeros.
    rewrite last_mk_list_false.
    reflexivity.
  }
  rewrite H_zero_val in H_t_pos.
  lia.
Qed.

(* MSB(a) = 1 -> a & signed_min = signed_min *)
Lemma bv_and_signed_min_neg : forall n v,
  size v = n ->
  (last (bits v) false = true -> bv_and v (signed_min n) = signed_min n).
Proof.
  intros n v Hv Hlast. apply bv_eq_reflect. unfold bv_eq.
  assert (Hsize_and: size (bv_and v (signed_min n)) = n).
  { apply bv_and_size; assumption || apply signed_min_size. }
  rewrite Hsize_and, signed_min_size. rewrite N.eqb_refl.
  unfold bits. unfold bv_and. rewrite Hv, signed_min_size.
  rewrite N.eqb_refl. unfold signed_min.
  destruct (N.to_nat n) eqn:En.
  - simpl. 
    assert (v = nil).
    { assert (n = 0%N).
      { rewrite <- (N2Nat.id n). rewrite En. reflexivity. }
      unfold size in Hv. rewrite H in Hv. simpl in Hv.
      apply length_zero_iff_nil. apply Nat2N.inj.
      rewrite Hv. reflexivity. }
    subst. simpl. reflexivity.
  - simpl.
    assert (Hnot_nil: bits v <> nil).
    { intro Hnil. apply (f_equal (@length bool)) in Hnil.
      simpl in Hnil. rewrite bits_size in Hnil.
      rewrite Hv in Hnil. rewrite En in Hnil.
      discriminate. }
    apply exists_last in Hnot_nil.
    destruct Hnot_nil as [v_prefix [last_bit Heq_v]].
    rewrite Heq_v in *. rewrite last_app in Hlast. 
    subst last_bit. pose proof (bits_size v) as Hlen_v.
    rewrite Heq_v in Hlen_v. rewrite Hv in Hlen_v.
    rewrite En in Hlen_v. rewrite length_app in Hlen_v.
    simpl in Hlen_v. rewrite Nat.add_1_r in Hlen_v.
    injection Hlen_v as Hlen_prefix.
    assert (Heq_lists: map2 andb (v_prefix ++ [true]) (rev (mk_list_false n0) ++ [true]) = rev (mk_list_false n0) ++ [true]).
    {
      apply nth_ext with (d:=false) (d':=false).
      - rewrite length_app. simpl.
        rewrite length_rev, length_mk_list_false. rewrite <- map2_and_length.
        2: { rewrite !length_app. simpl. rewrite Hlen_prefix.
          rewrite length_rev, length_mk_list_false. reflexivity. }
        rewrite length_app. simpl. rewrite Hlen_prefix. reflexivity.
      - intros i Hi. rewrite map2_and_nth_bitOf.
        destruct (lt_dec i n0) as [H_prefix | H_tail].
        + rewrite !app_nth1; try assumption;
            try (rewrite length_rev, length_mk_list_false; assumption);
            try (rewrite Hlen_prefix; assumption).
          assert (Hbit_false: nth i (rev (mk_list_false n0)) false = false).
          { rewrite rev_mk_list_false.
            clear Hi En Hlen_prefix. 
            revert i H_prefix.
            induction n0 as [|n' IH].
            - intros i Hi_bound. inversion Hi_bound.
            - intros i Hi_bound.
            rewrite mk_list_false_succ. destruct i.
               + simpl. reflexivity.
               + simpl. apply IH. simpl in Hi_bound. 
                 apply Nat.succ_lt_mono in Hi_bound. assumption.
          }
          rewrite Hbit_false.
          apply Bool.andb_false_r.
        + assert (Hi_eq: i = n0).
          { rewrite <- map2_and_length in Hi.
            2: { rewrite !length_app. simpl.
                 rewrite Hlen_prefix, length_rev, length_mk_list_false.
                 reflexivity. }
             rewrite length_app in Hi. simpl in Hi.
             rewrite Hlen_prefix in Hi. lia. }
          subst i. rewrite !app_nth2.
          * rewrite length_rev, length_mk_list_false.
            rewrite Hlen_prefix. rewrite Nat.sub_diag. simpl. reflexivity.
          * rewrite length_rev, length_mk_list_false. apply Nat.le_refl.
          * rewrite Hlen_prefix. apply Nat.le_refl.
        + rewrite !length_app. simpl. 
          rewrite Hlen_prefix, length_rev, length_mk_list_false.
          reflexivity.
        + rewrite length_app. simpl. rewrite Hlen_prefix.
          rewrite <- map2_and_length in Hi.
          2: { rewrite !length_app; simpl; rewrite Hlen_prefix, 
               length_rev, length_mk_list_false; reflexivity. }
          rewrite length_app in Hi. simpl in Hi.
          rewrite Hlen_prefix in Hi. lia. }
    unfold bits. rewrite Heq_lists. apply List_eq_refl.
Qed.

(* MSB(a) = 0 -> a * signed_min = 0 *)
Lemma bv_and_signed_min_pos : forall n v,
  size v = n -> (last (bits v) false = false -> 
  bv_and v (signed_min n) = zeros n).
Proof.
  intros n v Hv Hlast. apply bv_eq_reflect. unfold bv_eq.
  assert (Hsize_and: size (bv_and v (signed_min n)) = n).
  { apply bv_and_size; assumption || apply signed_min_size. }
  rewrite Hsize_and. rewrite zeros_size.
  rewrite N.eqb_refl. unfold bits, bv_and, zeros. 
  rewrite Hv, signed_min_size. rewrite N.eqb_refl.
  unfold signed_min. destruct (N.to_nat n) eqn:En.
  - simpl. assert (v = nil).
    { assert (n = 0%N). { rewrite <- (N2Nat.id n), En. reflexivity. }
      unfold size in Hv. rewrite H in Hv. simpl in Hv.
      apply length_zero_iff_nil. apply Nat2N.inj. rewrite Hv. reflexivity. }
    subst. simpl. reflexivity.
  - simpl.
    assert (Hnot_nil: bits v <> nil).
    { intro Hnil. apply (f_equal (@length bool)) in Hnil. simpl in Hnil.
      rewrite bits_size in Hnil. rewrite Hv, En in Hnil. discriminate. }
    apply exists_last in Hnot_nil. 
    destruct Hnot_nil as [v_prefix [last_bit Heq_v]]. rewrite Heq_v in *.
    rewrite last_app in Hlast. subst last_bit.
    pose proof (bits_size v) as Hlen_v.
    rewrite Heq_v, Hv, En in Hlen_v.
    rewrite length_app in Hlen_v. simpl in Hlen_v.
    rewrite Nat.add_1_r in Hlen_v. injection Hlen_v as Hlen_prefix.
    assert (Heq_lists: map2 andb (v_prefix ++ [false]) (rev (mk_list_false n0) ++ [true]) = mk_list_false (S n0)).
    { apply nth_ext with (d:=false) (d':=false).
      - rewrite length_mk_list_false.
        rewrite <- map2_and_length.
        2: { rewrite !length_app. simpl.
             rewrite Hlen_prefix, length_rev, length_mk_list_false. 
             reflexivity. }
        rewrite length_app. simpl. rewrite Hlen_prefix. lia.
      - intros i Hi. rewrite map2_and_nth_bitOf.
        destruct (lt_dec i n0) as [H_prefix | H_tail].
        + rewrite !app_nth1; try assumption;
            try (rewrite length_rev, length_mk_list_false; assumption);
            try (rewrite Hlen_prefix; assumption).
          assert (Hbit_false: nth i (rev (mk_list_false n0)) false = false).
          { rewrite rev_mk_list_false. clear Hi En Hlen_prefix. 
            revert i H_prefix. induction n0 as [|n' IH].
             - intros. inversion H_prefix.
             - intros. rewrite mk_list_false_succ. destruct i.
               + reflexivity.
               + simpl. apply IH. simpl in H_prefix. apply Nat.succ_lt_mono. 
                 assumption. }
          rewrite Hbit_false. rewrite Bool.andb_false_r. symmetry.
          clear Hbit_false H_prefix Hi Hlen_prefix Heq_v En Hv Hsize_and.
          revert i. induction n0 as [|n' IH].
          { intros i. destruct i.
            - simpl. reflexivity.
            - simpl. destruct i; reflexivity. }
          { intros i. rewrite mk_list_false_succ. destruct i.
            - reflexivity.
            - simpl. apply IH. }
        + assert (Hi_eq: i = n0).
          { rewrite <- map2_and_length in Hi.
            2: { rewrite !length_app; simpl; rewrite Hlen_prefix, 
                 length_rev, length_mk_list_false; reflexivity. }
            rewrite length_app in Hi. simpl in Hi. rewrite Hlen_prefix in Hi.
            lia. }
          subst i. rewrite !app_nth2. 
          * rewrite length_rev, length_mk_list_false. rewrite Hlen_prefix.
            rewrite Nat.sub_diag. simpl. symmetry.
            clear Hi H_tail Hlen_prefix Heq_v En Hv Hsize_and.
            induction n0 as [|n' IH].
            { simpl. reflexivity. }
            { rewrite mk_list_false_succ. simpl. apply IH. }
          * rewrite length_rev, length_mk_list_false. apply Nat.le_refl.
          * rewrite Hlen_prefix. apply Nat.le_refl.
        + rewrite !length_app. simpl.
          rewrite Hlen_prefix, length_rev, length_mk_list_false.
          reflexivity.
        + rewrite length_app. simpl.
          rewrite Hlen_prefix.
          rewrite <- map2_and_length in Hi.
          2: { rewrite !length_app; simpl; rewrite Hlen_prefix, length_rev,
               length_mk_list_false; reflexivity. }
          rewrite length_app in Hi. simpl in Hi. rewrite Hlen_prefix in Hi.
          lia. }
    unfold bits. rewrite Heq_lists. apply List_eq_refl.
Qed.

(* Helper: signed_min has MSB = 1 *)
Lemma signed_min_last : forall (n : N),
  (0 < n)%N ->
  last (signed_min n) false = true.
Proof.
  intros n Hn. unfold signed_min.
  destruct (N.to_nat n) eqn:E.
  - assert (n = 0%N).
    { rewrite <- (N2Nat.id n). rewrite E. reflexivity. }
    lia.
  - simpl. destruct n0.
    + simpl. reflexivity.
    + rewrite last_last. reflexivity.
Qed.

(* MSB(x) = 0 -> 0 <=s x *)
Lemma zeros_sle_nonneg : forall (n : N) (t : bitvector),
  size t = n -> last t false = false -> bv_sle (zeros n) t = true.
Proof.
  intros n t Ht Hlast. rewrite <- Ht.
  rewrite bv_zeros_sle. rewrite Hlast. reflexivity.
Qed.

(* Lemma: s >=u signed_min implies s has MSB = 1 *)
Lemma bv_uge_signed_min_implies_msb : forall n s,
  size s = n -> (0 < n)%N -> bv_uge s (signed_min n) = true ->
  last (bits s) false = true.
Proof.
  intros n s Hs Hn Huge. rewrite <- hd_rev. unfold bv_uge in Huge.
  rewrite Hs, signed_min_size in Huge. rewrite N.eqb_refl in Huge.
  unfold uge_list in Huge. destruct (N.to_nat n) eqn:En.
  - assert (n = 0%N) by (rewrite <- (N2Nat.id n), En; reflexivity). lia.
  - unfold signed_min, bits in Huge. unfold bits in *. 
    rewrite rev_involutive in Huge. destruct (rev s) eqn:Erevs.
    + apply (f_equal (@length bool)) in Erevs.
      rewrite length_rev in Erevs. simpl in Erevs.
      pose proof (bits_size s) as Hsize_lemma. unfold bits in Hsize_lemma.
      rewrite Erevs in Hsize_lemma. simpl in Hsize_lemma.
      rewrite Hs in Hsize_lemma. destruct n.
      * lia.
      * simpl in Hsize_lemma. symmetry in Hsize_lemma.
        pose proof (Pos2Nat.is_pos p) as Hpos. rewrite Hsize_lemma in Hpos.
        inversion Hpos.
    + unfold hd. rewrite En in Huge. simpl in Huge. destruct b.
      * reflexivity.
      * simpl in Huge. discriminate.
Qed.

(* MSB(s) = 1 -> s >=u signed_min *)
Lemma bv_msb_implies_uge_signed_min : forall n s, size s = n ->
  (0 < n)%N -> last (bits s) false = true ->
  bv_uge s (signed_min n) = true.
Proof.
  intros n s Hs Hn Hmsb. unfold bv_uge.
  rewrite Hs, signed_min_size. rewrite N.eqb_refl.
  rewrite <- hd_rev in Hmsb. destruct (rev (bits s)) eqn:Erev.
  - simpl in Hmsb.
    discriminate.
  - simpl in Hmsb. subst b.
    unfold signed_min, uge_list.
    destruct (N.to_nat n) eqn:En.
    + assert (n = 0%N). { rewrite <- (N2Nat.id n), En. reflexivity. } lia.
    + unfold smin_big_endian. rewrite rev_involutive.
      replace (rev s) with (rev (bits s)) by reflexivity.
      rewrite Erev. simpl. rewrite Bool.orb_false_r.
      assert (H_uge_zeros: forall l_arb, uge_list_big_endian l_arb (mk_list_false (length l_arb)) = true).
      { intros l_arb. induction l_arb as [|b' l' IH]; simpl.
        - reflexivity.
        - destruct b'; simpl.
        * reflexivity. 
        * rewrite Bool.orb_false_r. apply IH. }
      assert (Hlen: length l = n0).
      { apply (f_equal (@length bool)) in Erev. rewrite length_rev in Erev.
        pose proof (bits_size s) as Hsz. rewrite Hs in Hsz.
        rewrite En in Hsz. rewrite Hsz in Erev.
        simpl in Erev. inversion Erev. reflexivity. }
      rewrite <- Hlen. apply H_uge_zeros.
Qed.

(* forall x, x >=u 0  *)
Lemma bv_uge_zeros : forall n s, size s = n -> bv_uge s (zeros n) = true.
Proof.
  intros n s Hs.
  unfold bv_uge.
  rewrite Hs, zeros_size.
  rewrite N.eqb_refl.
  unfold zeros.
  assert (H_uge_zeros: forall l, uge_list_big_endian l (mk_list_false (length l)) = true).
  { intros l.
    induction l as [|b l' IH].
    - simpl. reflexivity.
    - simpl. destruct b.
      + reflexivity.
      + simpl. rewrite Bool.orb_false_r. apply IH. }
  assert (Hzeros_rev: forall k, rev (mk_list_false k) = mk_list_false k).
  { intro k. induction k.
    - reflexivity.
    - simpl. rewrite IHk.
      clear IHk. induction k.
      * reflexivity.
      * simpl. rewrite IHk. reflexivity. }
  unfold uge_list. rewrite Hzeros_rev.
  assert (Hlen: N.to_nat n = length (rev s)).
  { rewrite length_rev. rewrite <- Hs.
    symmetry. apply bits_size. }
  rewrite Hlen. apply H_uge_zeros.
Qed.

Lemma bv_sle_size_zero : forall s t,
  size s = 0%N -> size t = 0%N -> bv_sle s t = true.
Proof.
  intros s t Hs Ht.
  assert (Heq: s = t).
  { pose proof (bits_size s) as Hbs.
    pose proof (bits_size t) as Hbt.
    rewrite Hs in Hbs. rewrite Ht in Hbt.
    simpl in Hbs, Hbt.
    apply length_zero_iff_nil in Hbs.
    apply length_zero_iff_nil in Hbt.
    apply bv_eq_reflect.
    unfold bv_eq.
    rewrite Hs, Ht.
    rewrite N.eqb_refl.
    rewrite Hbs, Hbt.
    simpl.
    reflexivity. }
  subst. apply bv_sle_refl.
Qed.

(* A positive bitvector cannot be <=s a negative bitvector *)
Lemma bv_sle_pos_neg_absurd : forall (n : N) (a b : bitvector),
  (0 < n)%N -> size a = n -> size b = n ->
  last (bits a) false = false ->
  last (bits b) false = true ->
  bv_sle a b = true -> False.
Proof.
  intros n a b Hn_pos Hsa Hsb Ha_pos Hb_neg H_sle.
  unfold bv_sle in H_sle.
  rewrite Hsa, Hsb, N.eqb_refl in H_sle.
  unfold sle_list in H_sle.
  remember (rev (bits a)) as l_a.
  remember (rev (bits b)) as l_b.
  destruct l_a as [|msb_a rest_a]; destruct l_b as [|msb_b rest_b].
  - apply (f_equal (@length bool)) in Heql_b.
    simpl in Heql_b. rewrite length_rev, bits_size, Hsb in Heql_b. lia.
  - apply (f_equal (@length bool)) in Heql_a.
    simpl in Heql_a. rewrite length_rev, bits_size, Hsa in Heql_a. lia.
  - apply (f_equal (@length bool)) in Heql_b.
    simpl in Heql_b. rewrite length_rev, bits_size, Hsb in Heql_b. lia.
  - rewrite <- (hd_rev (bits a)) in Ha_pos.
    rewrite <- Heql_a in Ha_pos. simpl in Ha_pos.
    rewrite <- (hd_rev (bits b)) in Hb_neg.
    rewrite <- Heql_b in Hb_neg. simpl in Hb_neg.
    subst msb_a msb_b.
    change (rev a) with (rev (bits a)) in H_sle.
    change (rev b) with (rev (bits b)) in H_sle.
    rewrite <- Heql_a in H_sle.
    rewrite <- Heql_b in H_sle.
    simpl in H_sle.
    discriminate H_sle.
Qed.

(* Helper to instantly kill branches where size is 0 but the sign bit is true *)
Lemma size_zero_msb_absurd : forall (n : N) (s : bitvector),
  size s = n -> n = 0%N -> last (bits s) false = true -> False.
Proof.
  intros n s Hsize Hn0 Hmsb.
  subst n.
  pose proof (bits_size s) as Hbs.
  rewrite Hn0 in Hbs; simpl in Hbs.
  apply length_zero_iff_nil in Hbs.
  rewrite Hbs in Hmsb; simpl in Hmsb.
  discriminate.
Qed.

(* Helper to package the entire setup for the positive/negative contradiction *)
Lemma bvand_sle_backward_absurd : forall (n : N) (s t x : bitvector),
  size s = n -> size t = n -> size x = n ->
  last (bits s) false = false ->
  last (bits t) false = true ->
  bv_sle (bv_and x s) t = true -> False.
Proof.
  intros n s t x Hs Ht Hx Hs_pos Ht_neg Hsle.
  assert (Hn_pos: (0 < n)%N).
  { destruct (N.eq_dec n 0) as [Hn0|Hnneq].
    - exfalso. exact (@size_zero_msb_absurd n t Ht Hn0 Ht_neg).
    - apply N.neq_0_lt_0. exact Hnneq. }
  assert (Hxs_pos: last (bits (bv_and x s)) false = false).
  { rewrite (@bv_and_comm n x s Hx Hs).
    eapply pos_bvand_pos; try eassumption. }
  assert (Hsz_xs: size (bv_and x s) = n) by (apply bv_and_size; assumption).
  eapply bv_sle_pos_neg_absurd with (a := bv_and x s) (b := t).
  - exact Hn_pos.
  - exact Hsz_xs.
  - exact Ht.
  - exact Hxs_pos.
  - exact Ht_neg.
  - exact Hsle.
Qed.

(* MSB(s) = 1 -> MSB(s | min_s) = 1 *)
Lemma bv_or_signed_min_neg : forall n s,
  size s = n -> last (bits s) false = true ->
  bv_or s (signed_min n) = s.
Proof.
  intros n s Hs Hlast.
  apply bv_eq_reflect. unfold bv_eq.
  assert (Hsize_or : size (bv_or s (signed_min n)) = size s).
  { apply bv_or_size; [reflexivity | 
    rewrite Hs; apply signed_min_size]. }
  rewrite Hsize_or, N.eqb_refl. unfold bv_or.
  rewrite Hs, signed_min_size, N.eqb_refl. unfold bits.
  destruct (N.to_nat n) eqn:En.
  - assert (Hn0 : n = 0%N).
    { apply (f_equal N.of_nat) in En. 
      rewrite N2Nat.id in En. exact En. }
    assert (s = []).
    { pose proof (bits_size s) as Hlen. unfold bits in Hlen.
      rewrite Hs, Hn0 in Hlen. simpl in Hlen. 
      destruct s; [reflexivity | discriminate Hlen]. }
    subst s n. simpl. reflexivity.
  - unfold signed_min. rewrite En. simpl.
    assert (Hrev_false : rev (mk_list_false n0) = 
      mk_list_false n0) by apply rev_mk_list_false.
    rewrite Hrev_false.
    assert (Hlen_s : length s = S n0).
    { pose proof (bits_size s) as H. unfold bits in H. 
      rewrite Hs, En in H. exact H. }
    assert (Hs_decomp : exists s_init, s = s_init ++ 
      [true] /\ length s_init = n0).
    { destruct s as [| sh st] using rev_ind.
      - simpl in Hlen_s. discriminate Hlen_s.
      - exists st. split.
        + unfold bits in Hlast. rewrite last_last in Hlast. 
          rewrite Hlast. reflexivity.
        + rewrite length_app in Hlen_s. simpl in Hlen_s. 
          lia. }
    destruct Hs_decomp as [s_init [Hs_eq Hlen_init]]. 
    rewrite Hs_eq.
    assert (Hlen_eq : length s_init = 
      length (mk_list_false n0)) by 
      (rewrite length_mk_list_false; exact Hlen_init).
    rewrite map2_or_app.
    + rewrite <- Hlen_init, map2_or_0_neutral. simpl.
      assert (Hbeq_refl: forall l, beq_list l l = true).
      { induction l; [reflexivity | simpl; rewrite IHl; 
        destruct a; reflexivity]. }
      apply Hbeq_refl.
    + exact Hlen_eq.
    + simpl. reflexivity.
Qed.

Lemma bv_or_signed_min_pos : forall n s,
  (0 < n)%N -> size s = n -> last (bits s) false = false ->
  last (bits (bv_or s (signed_min n))) false = true.
Proof.
  intros n s Hn_pos Hs Hlast.
  unfold bv_or. rewrite Hs, signed_min_size, N.eqb_refl. 
  unfold bits. destruct (N.to_nat n) eqn:En.
  - assert (Hn0 : n = 0%N).
    { apply (f_equal N.of_nat) in En. 
      rewrite N2Nat.id in En. exact En. }
    rewrite Hn0 in Hn_pos. lia.
  - unfold signed_min. rewrite En. simpl.
    assert (Hrev_false : rev (mk_list_false n0) = 
      mk_list_false n0) by apply rev_mk_list_false.
    rewrite Hrev_false.
    assert (Hlen_s : length s = S n0).
    { pose proof (bits_size s) as H. unfold bits in H. 
      rewrite Hs, En in H. exact H. }
    assert (Hs_decomp : exists s_init, s = s_init ++ 
      [false] /\ length s_init = n0).
    { destruct s as [| sh st] using rev_ind.
      - simpl in Hlen_s. discriminate Hlen_s.
      - exists st. split.
        + unfold bits in Hlast. rewrite last_last in Hlast. 
          rewrite Hlast. reflexivity.
        + rewrite length_app in Hlen_s. simpl in Hlen_s. 
          lia. }
    destruct Hs_decomp as [s_init [Hs_eq Hlen_init]]. 
    rewrite Hs_eq.
    assert (Hlen_eq : length s_init = 
      length (mk_list_false n0)) by 
      (rewrite length_mk_list_false; exact Hlen_init).
    rewrite map2_or_app.
    + change (map2 orb [false] [true]) with [true]. 
      rewrite last_last. reflexivity.
    + exact Hlen_eq.
    + simpl. reflexivity.
Qed.

Lemma bv_sle_trans : forall a b c,
  bv_sle a b = true ->
  bv_sle b c = true ->
  bv_sle a c = true.
Proof.
  intros a b c Hab Hbc. unfold bv_sle in *.
  destruct (size a =? size b) eqn:Hab_size.
  - destruct (size b =? size c) eqn:Hbc_size.
    + assert (Hac_size : size a = size c).
      { apply N.eqb_eq in Hab_size. 
        apply N.eqb_eq in Hbc_size. 
        rewrite Hab_size, Hbc_size. reflexivity. }
      apply N.eqb_eq in Hac_size. rewrite Hac_size. 
      unfold sle_list in *.
      apply (sle_list_big_endian_trans (y := rev b)); 
      [exact Hab | exact Hbc].
    + discriminate Hbc.
  - discriminate Hab.
Qed.

(* MSB(a) = 1 -> MSB(b) = 0 -> a <=s b *)
Lemma neg_sle_pos : forall n a b,
  size a = n -> size b = n ->
  last (bits a) false = true ->
  last (bits b) false = false ->
  bv_sle a b = true.
Proof.
  intros n a b Ha Hb Hlast_a Hlast_b.
  unfold bv_sle.
  assert (Hsize : size a = size b) by 
    (rewrite Ha, Hb; reflexivity).
  apply N.eqb_eq in Hsize. rewrite Hsize. unfold sle_list.
  destruct (bits a) eqn:Hbits_a; 
    [simpl in Hlast_a; discriminate Hlast_a |].
  destruct (bits b) eqn:Hbits_b.
  - assert (length (bits a) = N.to_nat (size a)) 
      by apply bits_size.
    assert (length (bits b) = N.to_nat (size b)) 
      by apply bits_size.
    rewrite Hbits_a in H. rewrite Hbits_b in H0. 
    simpl in H, H0.
    assert (N.to_nat (size a) = N.to_nat (size b)) by 
      (apply N.eqb_eq in Hsize; rewrite Hsize; reflexivity).
    rewrite <- H, <- H0 in H1. discriminate H1.
  - assert (Hhd_a : hd false (rev (bits a)) = true) by 
      (rewrite hd_rev; rewrite Hbits_a; exact Hlast_a).
    assert (Hhd_b : hd false (rev (bits b)) = false) by 
      (rewrite hd_rev; rewrite Hbits_b; exact Hlast_b).
    rewrite Hbits_a in Hhd_a. rewrite Hbits_b in Hhd_b.
    destruct (rev (b0 :: l)) eqn:Hrev_a.
    * assert (b0 :: l = []) by 
        (apply (f_equal (@rev bool)) in Hrev_a; 
         rewrite rev_involutive in Hrev_a; exact Hrev_a).
      discriminate H.
    * destruct (rev (b1 :: l0)) eqn:Hrev_b.
      -- assert (b1 :: l0 = []) by 
           (apply (f_equal (@rev bool)) in Hrev_b; 
            rewrite rev_involutive in Hrev_b; exact Hrev_b).
         discriminate H.
      -- simpl in Hhd_a, Hhd_b. subst b2 b3. 
         unfold bits in Hbits_a, Hbits_b.
         rewrite Hbits_a, Hbits_b, Hrev_a, Hrev_b. 
         simpl. reflexivity.
Qed.

(* MSB(a) = 1 -> MSB(a | b) = 1 *)
Lemma bv_or_preserves_msb_left : forall n a b,
  size a = n -> size b = n ->
  last (bits a) false = true ->
  last (bits (bv_or a b)) false = true.
Proof.
  intros n a b Ha Hb Hlast_a.
  assert (Hlen: length (bits a) = length (bits b)) by 
    (rewrite (bits_size a), (bits_size b), Ha, Hb; reflexivity).
  unfold bv_or. assert (Hsize_eq : size a =? size b = true) 
    by (apply N.eqb_eq; rewrite Ha, Hb; reflexivity).
  rewrite Hsize_eq. remember (bits a) as la. 
  remember (bits b) as lb.
  destruct la using rev_ind; destruct lb using rev_ind.
  - simpl in Hlast_a. discriminate Hlast_a.
  - simpl in Hlast_a. discriminate Hlast_a.
  - rewrite length_app in Hlen. simpl in Hlen. 
    destruct (length la); discriminate Hlen.
  - rewrite last_last in Hlast_a.
    assert (Hlen_init : length la = length lb) by 
      (do 2 rewrite length_app in Hlen; simpl in Hlen; lia).
    rewrite Hlast_a. rewrite map2_or_app; 
      try exact Hlen_init; try reflexivity.
    unfold bits. simpl. rewrite last_last. reflexivity.
Qed.

Lemma bv_or_preserves_msb_right : forall n a b,
  size a = n -> size b = n ->
  last (bits b) false = true ->
  last (bits (bv_or a b)) false = true.
Proof.
  intros n a b Ha Hb Hlast_b.
  assert (Hlen: length (bits a) = length (bits b)) by 
    (rewrite (bits_size a), (bits_size b), Ha, Hb; reflexivity).
  unfold bv_or. assert (Hsize_eq : size a =? size b = true) 
    by (apply N.eqb_eq; rewrite Ha, Hb; reflexivity).
  rewrite Hsize_eq. remember (bits a) as la. 
  remember (bits b) as lb.
  destruct la using rev_ind; destruct lb using rev_ind.
  - simpl in Hlast_b. discriminate Hlast_b.  
  - rewrite length_app in Hlen. simpl in Hlen. 
    destruct (length lb); discriminate Hlen.
  - simpl in Hlast_b. discriminate Hlast_b.    
  - rewrite last_last in Hlast_b.
    * assert (Hlen_init : length la = length lb) by 
        (do 2 rewrite length_app in Hlen; 
         simpl in Hlen; lia).
      rewrite Hlast_b. rewrite map2_or_app; 
        try exact Hlen_init; try reflexivity.
      unfold bits. simpl. rewrite last_last. 
      destruct x; reflexivity.
Qed.

Lemma bv_sge_iff_sle : forall a b,
  bv_sge a b = bv_sle b a.
Proof.
  intros a b. unfold bv_sge, bv_sle.
  destruct (size a =? size b) eqn:Hsize.
  - apply N.eqb_eq in Hsize.
    assert (Hsize_flipped : (size b =? size a) = true) by 
      (apply N.eqb_eq; symmetry; exact Hsize).
    rewrite Hsize_flipped. unfold sge_list, sle_list.
    assert (Hlen : length (rev a) = length (rev b)).
    { do 2 rewrite length_rev. pose proof (bits_size a) 
      as Hlen_a. pose proof (bits_size b) as Hlen_b.
      rewrite Hsize in Hlen_a. rewrite <- Hlen_b in Hlen_a. 
      exact Hlen_a. }
    destruct (rev a); destruct (rev b); 
      try reflexivity; try discriminate Hlen.
    simpl. match goal with | |- context[eqb ?x ?y] => 
      destruct x; destruct y end.
    * simpl. destruct (uge_list_big_endian _ _) eqn:Huge; 
        destruct (ule_list_big_endian _ _) eqn:Hule; 
        try reflexivity;
        [apply uge_list_big_endian_ule_list_big_endian in Huge; 
         rewrite Huge in Hule; discriminate | 
         apply ule_list_big_endian_uge_list_big_endian in Hule; 
         rewrite Hule in Huge; discriminate].
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct (uge_list_big_endian _ _) eqn:Huge; 
        destruct (ule_list_big_endian _ _) eqn:Hule; 
        try reflexivity;
        [apply uge_list_big_endian_ule_list_big_endian in Huge; 
         rewrite Huge in Hule; discriminate | 
         apply ule_list_big_endian_uge_list_big_endian in Hule; 
         rewrite Hule in Huge; discriminate].
  - apply N.eqb_neq in Hsize.
    assert (Hsize_flipped : (size b =? size a) = false) by 
      (apply N.eqb_neq; intro Hcontra; apply Hsize; 
       symmetry; exact Hcontra).
    rewrite Hsize_flipped. reflexivity.
Qed.

Lemma signed_min_msb : forall n,
  (n > 0)%N -> 
  last (bits (signed_min n)) false = true.
Proof.
  intros n Hpos. unfold signed_min, bits.
  destruct (N.to_nat n) eqn:Hn; [lia |].
  unfold smin_big_endian. simpl. 
  rewrite last_last. reflexivity.
Qed.

Lemma ule_list_big_endian_or : forall (a b : list bool),
  length a = length b ->
  ule_list_big_endian a (map2 orb a b) = true.
Proof.
  intros a. induction a as [|x xs IHa]; intros b Hlen.
  - destruct b; [ | discriminate Hlen ]. simpl. reflexivity.
  - destruct b as [|y ys]; [ discriminate Hlen | ].
    simpl in Hlen. injection Hlen as Hlen_tails. simpl. 
    destruct x, y.
    + rewrite orb_false_r. 
      apply IHa. apply Hlen_tails.
    + rewrite orb_false_r. 
      apply IHa. apply Hlen_tails.
    + reflexivity.
    + rewrite ?orb_false_r. 
      rewrite ?andb_true_r. 
      rewrite ?andb_true_l.
      apply IHa. apply Hlen_tails.
Qed.

(* (s | min_s) <=s (x | s) *)
Lemma bv_or_signed_min_lower_bound : forall n s x,
  n > 0 -> size s = n -> size x = n ->
  bv_sle (bv_or s (signed_min n)) (bv_or x s) = true.
Proof.
  intros n s x Hn_gt_0 Hsize_s Hsize_x.
  assert (Hleft_msb : last (bits (bv_or s (signed_min n))) false = true).
  { apply bv_or_preserves_msb_right with (n := n).
    - exact Hsize_s. - apply signed_min_size.
    - apply signed_min_msb. exact Hn_gt_0. }
  assert (Hlen: length (bits (bv_or s (signed_min n))) = length (bits (bv_or x s))).
  { do 2 rewrite bits_size.
    assert (Hsize_left: size (bv_or s (signed_min n)) = n).
    { apply bv_or_size; [exact Hsize_s | apply signed_min_size]. }
    assert (Hsize_right: size (bv_or x s) = n).
    { apply bv_or_size; [exact Hsize_x | exact Hsize_s]. }
    rewrite Hsize_left, Hsize_right. reflexivity. }
  unfold bv_sle.
  assert (Hsize_eq : (size (bv_or s (signed_min n)) =? size (bv_or x s)) = true).
  { apply N.eqb_eq.
    assert (Hsize_left: size (bv_or s (signed_min n)) = n).
    { apply bv_or_size; [exact Hsize_s | apply signed_min_size]. }
    assert (Hsize_right: size (bv_or x s) = n).
    { apply bv_or_size; [exact Hsize_x | exact Hsize_s]. }
    rewrite Hsize_left, Hsize_right. reflexivity. }
  rewrite Hsize_eq. unfold sle_list.
  remember (bits (bv_or s (signed_min n))) as la.
  remember (bits (bv_or x s)) as lb.
  destruct la using rev_ind; destruct lb using rev_ind.
  - simpl in Hleft_msb. discriminate Hleft_msb.
  - simpl in Hleft_msb. discriminate Hleft_msb.
  - rewrite length_app in Hlen. rewrite Nat.add_comm in Hlen. simpl in Hlen. discriminate Hlen.
  - rewrite last_last in Hleft_msb.
    assert (H_goal : sle_list_big_endian (rev (la ++ [x0])) (rev (lb ++ [x1])) = true).
    { do 2 rewrite rev_unit. rewrite Hleft_msb. simpl. destruct x1; [| reflexivity].
      simpl negb. rewrite andb_true_l. rewrite orb_false_r.
      assert (Hrev_map2_or : forall a b, length a = length b -> rev (map2 orb a b) = map2 orb (rev a) (rev b)).
      { intros a b Hlen_ab. apply nth_ext with (d := false) (d' := false).
        - rewrite length_rev. assert (H1 : length (map2 orb a b) = length a).
          { symmetry. apply map2_or_length. exact Hlen_ab. }
          rewrite H1. symmetry. assert (H2 : length (map2 orb (rev a) (rev b)) = length (rev a)).
          { symmetry. apply map2_or_length. rewrite length_rev, length_rev. exact Hlen_ab. }
          rewrite H2. rewrite length_rev. reflexivity.
        - intros i Hi. assert (Hlen_map2 : length (map2 orb a b) = length a).
          { symmetry. apply map2_or_length. exact Hlen_ab. }
          assert (Hi_bound : (i < length (map2 orb a b))%nat). { rewrite length_rev in Hi. exact Hi. }
          rewrite (rev_nth (map2 orb a b) false Hi_bound).
          assert (Hi_lhs : (length (map2 orb a b) - S i <= length a)%nat). { rewrite Hlen_map2. lia. }
          rewrite map2_or_nth_bitOf. + rewrite Hlen_map2. rewrite map2_or_nth_bitOf.
          * assert (Hi_a : (i < length a)%nat) by lia. assert (Hi_b : (i < length b)%nat) by lia.
            rewrite (rev_nth a false Hi_a). rewrite (rev_nth b false Hi_b). rewrite <- Hlen_ab. reflexivity.
          * rewrite length_rev, length_rev. exact Hlen_ab.
          * rewrite length_rev. lia. + exact Hlen_ab. + lia. }
      assert (Hrev_lb : true :: rev lb = rev (bits (bv_or x s))).
      { assert (H1 : rev (lb ++ [true]) = rev (bits (bv_or x s))) by (f_equal; exact Heqlb).
        rewrite rev_unit in H1. exact H1. }
      assert (Hrev_la : true :: rev la = rev (bits (bv_or s (signed_min n)))).
      { assert (H1 : rev (la ++ [x0]) = rev (bits (bv_or s (signed_min n)))) by (f_equal; exact Heqla).
        rewrite rev_unit in H1. rewrite Hleft_msb in H1. exact H1. }
      assert (H_full_or : true :: rev lb = map2 orb (true :: rev la) (rev (bits x))).
      { rewrite Hrev_lb, Hrev_la.
        assert (Hbv_or_xs : bits (bv_or x s) = map2 orb (bits x) (bits s)).
        { unfold bv_or, bits. rewrite Hsize_x, Hsize_s, N.eqb_refl. reflexivity. }
        assert (Hbv_or_s_min : bits (bv_or s (signed_min n)) = map2 orb (bits s) (bits (signed_min n))).
        { unfold bv_or, bits. rewrite Hsize_s, signed_min_size, N.eqb_refl. reflexivity. }
        rewrite Hbv_or_xs, Hbv_or_s_min.
        assert (Hlen_xs : length (bits x) = length (bits s)).
        { unfold bits. pose proof (bits_size x) as H1. pose proof (bits_size s) as H2.
          unfold bits in H1, H2. rewrite Hsize_x in H1. rewrite Hsize_s in H2. rewrite H1, H2. reflexivity. }
        assert (Hlen_s_min : length (bits s) = length (bits (signed_min n))).
        { unfold bits. pose proof (bits_size s) as H1. pose proof (bits_size (signed_min n)) as H2.
          unfold bits in H1, H2. rewrite Hsize_s in H1. rewrite signed_min_size in H2. rewrite H1, H2. reflexivity. }
        rewrite Hrev_map2_or by exact Hlen_xs. rewrite Hrev_map2_or by exact Hlen_s_min.
        rewrite <- map2_or_assoc. rewrite (map2_or_comm (rev (bits (signed_min n))) (rev (bits x))).
        rewrite map2_or_assoc. rewrite (map2_or_comm (rev (bits x)) (rev (bits s))). symmetry.
        assert (H_xs_neg : last (bits (bv_or x s)) false = true).
        { rewrite <- Heqlb. rewrite last_last. reflexivity. }
        assert (H_or_idem : bv_or (bv_or x s) (signed_min n) = bv_or x s).
        { apply bv_or_signed_min_neg. - assert (Hsize_xs : size (bv_or x s) = n).
          { apply bv_or_size; [exact Hsize_x | exact Hsize_s]. } exact Hsize_xs. - exact H_xs_neg. }
        apply (f_equal bits) in H_or_idem. unfold bits in H_or_idem. unfold bv_or in H_or_idem at 1.
        assert (Hsize_xs : size (bv_or x s) = n). { apply bv_or_size; [exact Hsize_x | exact Hsize_s]. }
        rewrite Hsize_xs, signed_min_size, N.eqb_refl in H_or_idem. rewrite Hbv_or_xs in H_or_idem.
        apply (f_equal (@rev bool)) in H_or_idem.
        assert (Hlen_map2_xs : length (map2 orb (bits x) (bits s)) = length (bits (signed_min n))).
        { assert (H1 : length (map2 orb (bits x) (bits s)) = length (bits x)).
          { symmetry. apply map2_or_length. exact Hlen_xs. } rewrite H1, Hlen_xs. exact Hlen_s_min. }
        rewrite Hrev_map2_or in H_or_idem by exact Hlen_map2_xs.
        rewrite Hrev_map2_or in H_or_idem by exact Hlen_xs.
        change (rev (bv_or x s)) with (rev (bits (bv_or x s))) in H_or_idem.
        rewrite Hbv_or_xs in H_or_idem. rewrite Hrev_map2_or in H_or_idem by exact Hlen_xs.
        rewrite (map2_or_comm (rev (bits x)) (rev (bits s))) in H_or_idem. exact H_or_idem. }
      destruct (rev (bits x)) as [| x_msb x_lower] eqn:Hrev_x.
      { apply (f_equal (@length bool)) in Hrev_x. simpl in Hrev_x.
        rewrite length_rev, bits_size, Hsize_x in Hrev_x. lia. }
      simpl in H_full_or. injection H_full_or as H_lb_structure.
      rewrite H_lb_structure. apply ule_list_big_endian_or.
      assert (Hlen_x : length (x_msb :: x_lower) = N.to_nat n).
      { rewrite <- Hrev_x. rewrite length_rev, bits_size, Hsize_x. reflexivity. }
      assert (Hlen_la : length (la ++ [x0]) = N.to_nat n).
      { rewrite Heqla, bits_size. f_equal. apply bv_or_size; [exact Hsize_s | apply signed_min_size]. }
      rewrite length_app in Hlen_la. simpl in Hlen_la. simpl in Hlen_x. rewrite length_rev. lia. }
    rewrite Heqla in H_goal. rewrite Heqlb in H_goal. exact H_goal.
Qed.

Lemma signed_min_eq_not_smax : forall (n : N),
  (0 < n)%N ->
  signed_min n = bv_not (signed_max n).
Proof.
  intros n H_pos. unfold signed_min, signed_max, bv_not.
  unfold bits. rewrite map_rev. f_equal. 
  destruct (N.to_nat n) as [| n'] eqn:Heq.
  - lia. 
  - simpl. f_equal.
    assert (H_lists : forall k : nat, mk_list_false k = 
      map negb (mk_list_true k)).
    { intro k. induction k as [| k' IHk].
      - reflexivity.
      - simpl. f_equal. apply IHk. }
    apply H_lists.
Qed.

Lemma map_negb_ashr_one_bit : forall (a : list bool) 
  (sign : bool),
  map negb (ashr_one_bit a sign) = 
    ashr_one_bit (map negb a) (negb sign).
Proof.
  intros a sign. destruct a as [| b t].
  - reflexivity.
  - simpl. rewrite map_app. reflexivity.
Qed.

Lemma map_negb_ashr_n_bits : forall (k : nat) 
  (a : list bool) (sign : bool),
  map negb (ashr_n_bits a k sign) = 
    ashr_n_bits (map negb a) k (negb sign).
Proof.
  intros n. induction n as [| n' IHn].
  - intros a sign. reflexivity.
  - intros a sign. simpl. rewrite IHn.
    rewrite map_negb_ashr_one_bit. reflexivity.
Qed.

Lemma shr_n_bits_eq_ashr_false : forall (n : nat) 
  (a : list bool),
  shr_n_bits a n = ashr_n_bits a n false.
Proof.
  intros n. induction n as [| n' IHn].
  - intros a. reflexivity.
  - intros a. simpl.
    assert (H_one_bit: shr_one_bit a = 
      ashr_one_bit a false).
    { destruct a as [| b t].
      - reflexivity.
      - reflexivity. }
    rewrite H_one_bit. apply IHn.
Qed.

Lemma last_signed_min : forall n : N,
  (0 < n)%N -> last (signed_min n) false = true.
Proof.
  intros n H_pos. unfold signed_min. unfold bits. 
  destruct (N.to_nat n) as [| n'] eqn:Heq.
  - lia. 
  - simpl. rewrite last_last. reflexivity.
Qed.

Lemma ashr_smin_eq_not_shr_smax :
  forall (n : N) (s : bitvector),
    (0 < n)%N -> size s = n ->
    bv_ashr (signed_min n) s = 
      bv_not (bv_shr (signed_max n) s).
Proof.
  intros n s H_pos H_size. unfold bv_ashr, bv_shr.
  rewrite signed_min_size. rewrite signed_max_size.
  rewrite H_size. rewrite N.eqb_refl. 
  unfold ashr_aux, shr_aux.
  rewrite shr_n_bits_eq_ashr_false. unfold bv_not.
  unfold bits. rewrite map_negb_ashr_n_bits.
  simpl (negb false). rewrite last_signed_min; auto.
  f_equal. rewrite signed_min_eq_not_smax.
  - unfold bv_not. reflexivity.
  - exact H_pos.
Qed.

Lemma ashr_smin_is_minimal :
  forall (n : N) (x s : bitvector),
    (0 < n)%N -> size x = n -> size s = n ->
    bv_sle (bv_ashr (signed_min n) s) 
      (bv_ashr x s) = true.
Proof.
  intros n x s H_pos H_size_x H_size_s. eapply sle_ashr.
  - apply signed_min_size.
  - exact H_size_x.
  - exact H_size_s.
  - pose proof (signed_min_sle x) as H_min.
    rewrite H_size_x in H_min. exact H_min.
Qed.


Lemma neg_bv_or : forall (n : N) (x s : bitvector),
  size x = n ->
  size s = n ->
  last s false = true ->
  last (bv_or x s) false = true.
Proof.
  intros n x s Hx_size Hn_s Hs_sign.
  unfold bv_or.
  unfold bits.
  assert (Hxs : (size x =? size s)%N = true).
  { rewrite Hx_size, Hn_s. apply N.eqb_refl. }
  rewrite Hxs.
  assert (Hs_not_nil: s <> nil).
  { 
    intro Hnil. subst s. 
    simpl in Hs_sign. discriminate. 
  }
  assert (Hx_not_nil: x <> nil).
  { 
    intro Hnil. subst x.
    rewrite <- Hx_size in Hn_s. 
    destruct s as [| hd tl].
    - simpl in Hs_sign. 
      discriminate Hs_sign.
    - simpl in Hn_s. 
      discriminate Hn_s. 
  }
  rewrite (app_removelast_last false Hx_not_nil) at 1.
  rewrite (app_removelast_last false Hs_not_nil) at 1.
  rewrite map2_or_app.
  2: {
    pose proof (app_removelast_last false Hx_not_nil) as Hx_app.
    pose proof (app_removelast_last false Hs_not_nil) as Hs_app.
    apply (f_equal (@length bool)) in Hx_app.
    apply (f_equal (@length bool)) in Hs_app.
    rewrite length_app in Hx_app.
    rewrite length_app in Hs_app.
    simpl in Hx_app, Hs_app.
    assert (Hlen: length x = length s).
    { 
      assert (Hsize_eq: size x = size s).
      { rewrite Hx_size, Hn_s. reflexivity. }
      apply size_len_eq.
      easy.
    }
    assert (H_removelast_len: length (removelast x) = length (removelast s)).
    { lia. }
    rewrite H_removelast_len. 
    reflexivity.
  }
  * simpl. 
    rewrite last_app.
    rewrite Hs_sign.
    apply orb_true_r.
  * reflexivity.
Qed.

Lemma length_removelast_eq : forall (l1 l2 : bitvector),
  length l1 = length l2 ->
  length (removelast l1) = length (removelast l2).
Proof.
  intros l1 l2 Hlen.
  destruct l1 as [| h1 t1], l2 as [| h2 t2].
  - reflexivity. 
  - discriminate Hlen. 
  - discriminate Hlen. 
  - assert (Hnil1 : h1 :: t1 <> nil) by discriminate.
    assert (Hnil2 : h2 :: t2 <> nil) by discriminate.
    
    pose proof (app_removelast_last false Hnil1) as H1.
    pose proof (app_removelast_last false Hnil2) as H2.
    
    apply (f_equal (@length bool)) in H1.
    apply (f_equal (@length bool)) in H2.
    
    rewrite length_app in H1, H2.
    simpl in *. 
    lia.
Qed.

Lemma bv_or_pos_smax : forall (n : N) (s : bitvector),
  size s = n ->
  last s false = false ->
  bv_or s (signed_max n) = signed_max n.
Proof.
  intros n s Hn_s Hs_sign.
  destruct (N.to_nat n) as [| t'] eqn:Hn_nat.
  - unfold signed_max. rewrite Hn_nat. simpl. apply bv_or_empty_empty1.
  - assert (Hs_not_nil: s <> nil). 
    {
      intro Hs_nil.
      rewrite Hs_nil in Hn_s. 
      rewrite <- Hn_s in Hn_nat.
      discriminate Hn_nat.
    }
    unfold bv_or.
    rewrite Hn_s, signed_max_size. rewrite N.eqb_refl.
    rewrite (app_removelast_last false Hs_not_nil) at 1.
    rewrite Hs_sign.
    unfold signed_max.
    unfold smax_big_endian. 
    rewrite Hn_nat.
    simpl rev. 
    rewrite rev_mk_list_true.
    unfold bits.
    assert (Hlen : length s = S t').
    {
      unfold size in Hn_s.
      rewrite <- Hn_s in Hn_nat.
      rewrite Nat2N.id in Hn_nat. 
      exact Hn_nat.
    }
    rewrite map2_or_app.
    + simpl (map2 orb (false :: nil) (false :: nil)).
      replace t' with (length (removelast s)).
      * rewrite map2_or_1_true.
        reflexivity.
      * rewrite removelast_firstn_len.
        rewrite length_firstn.
        rewrite Hlen.
        simpl.
        apply Nat.min_l.
        lia. 
    + rewrite length_mk_list_true. 
      rewrite removelast_firstn_len.
      rewrite length_firstn.
      rewrite Hlen.
      simpl.
      apply Nat.min_l.
      lia. 
    + easy.
Qed.

Lemma bv_or_sle_or_smax : forall (n : N) (x s : bitvector),
  size x = n ->
  size s = n ->
  bv_sle (bv_or x s) (bv_or s (signed_max n)) = true.
Proof.
  intros n x s Hx_size Hn_s.
  destruct (last s false) eqn:Hs_sign.
  - unfold bv_sle.
    rewrite (bv_or_size Hx_size Hn_s). 
    assert (Hsize_right : size (bv_or s (signed_max n)) = n).
    { apply (bv_or_size Hn_s). apply signed_max_size. } 
    rewrite Hsize_right.
    rewrite N.eqb_refl.
    unfold sle_list. 
    assert (Hnot_nil_left: bv_or x s <> nil).
    {
      intro Hnil.
      assert (Hsize: size (bv_or x s) = n). 
      { apply bv_or_size; assumption. }
      rewrite Hnil in Hsize.
      unfold size in Hsize; simpl in Hsize.
      rewrite <- Hsize in Hn_s.
      destruct s eqn:Hs_eq.
      - simpl in Hs_sign. 
        discriminate Hs_sign.
      - unfold size in Hn_s. simpl in Hn_s. 
        lia. 
    }
    assert (Hnot_nil_right: bv_or s (signed_max n) <> nil).
    {
      intro Hnil.
      rewrite Hnil in Hsize_right.
      unfold size in Hsize_right; simpl in Hsize_right.
      rewrite <- Hsize_right in Hn_s.
      destruct s eqn:Hs_eq.
      - simpl in Hs_sign. 
        discriminate Hs_sign.
      - unfold size in Hn_s. simpl in Hn_s. 
        lia. 
    }
    pose proof (app_removelast_last false Hnot_nil_left) as H_split_left.
    pose proof (app_removelast_last false Hnot_nil_right) as H_split_right.
    rewrite H_split_left.
    rewrite H_split_right.
    rewrite rev_unit.
    rewrite rev_unit.
    rewrite (neg_bv_or Hx_size Hn_s Hs_sign).
    assert (H_smax_size: size (signed_max n) = n). { apply signed_max_size. }
    rewrite (bv_or_comm Hn_s H_smax_size).
    rewrite (neg_bv_or H_smax_size Hn_s Hs_sign).
    simpl.
    rewrite orb_false_r.
    assert (Hs_not_nil: s <> nil).
    { intro Hnil. subst s. simpl in Hs_sign. discriminate. }
    assert (H_all_true : rev (removelast (bv_or s (signed_max n))) = 
                         mk_list_true (length (rev (removelast (bv_or x s))))).
    { 
      assert (Hlen : length (rev (removelast (bv_or x s))) = length (removelast s)).
      { rewrite length_rev. apply length_removelast_eq. apply size_len_eq. 
        rewrite Hn_s. apply (bv_or_size Hx_size Hn_s). }
      rewrite Hlen.
      unfold bv_or.
      rewrite Hn_s. rewrite signed_max_size. rewrite N.eqb_refl.
      unfold signed_max, smax_big_endian.
      destruct (N.to_nat n) as [| t'] eqn:Hnat.
      { destruct s as [| b s'].
        - simpl in Hs_sign. discriminate. 
        - assert (Hn_zero : n = 0%N) by lia.
          rewrite Hn_zero in Hn_s.
          simpl in Hn_s.
          discriminate || lia.
      }
      unfold bits. 
      simpl rev. 
      rewrite rev_mk_list_true. 
      rewrite (app_removelast_last false Hs_not_nil) at 1.
      rewrite map2_or_app.
      - rewrite removelast_app.
        simpl map2.
        simpl removelast.
        rewrite app_nil_r.
        assert (H_len_eq : t' = length (removelast s)).
        {
          assert (Hlen_s_nat : length s = S t').
          {
            rewrite <- Hnat.
            rewrite <- Hn_s.
            rewrite <- bits_size.
            reflexivity. 
          }
          assert (H_s_split : s = removelast s ++ last s false :: nil).
          { 
            apply app_removelast_last. 
            exact Hs_not_nil. 
          }
          rewrite H_s_split in Hlen_s_nat.
          rewrite length_app in Hlen_s_nat.
          simpl in Hlen_s_nat.
          lia.
        }
        rewrite H_len_eq.
        rewrite map2_or_1_true.
        rewrite rev_mk_list_true.
        reflexivity.
        simpl. 
        discriminate.
      - assert (Hlen_true : length (mk_list_true t') = t').
        { apply length_mk_list_true. }
        rewrite Hlen_true.
        assert (Hsplit_s : s = removelast s ++ last s false :: nil).
        { 
          apply app_removelast_last. exact Hs_not_nil. 
        }
        assert (Hlen_s_split : length s = S (length (removelast s))).
        {
          rewrite Hsplit_s at 1.
          rewrite length_app.
          simpl. lia.
        }
        assert (Hlen_s_nat : length s = S t').
        {
          rewrite <- Hnat.
          rewrite <- Hn_s.
          rewrite <- bits_size. 
          unfold bits. 
          reflexivity.
        }
        lia.
      - reflexivity.
    }
    rewrite (bv_or_comm H_smax_size Hn_s).
    rewrite H_all_true.
    apply ule_list_big_endian_1.
  -
    rewrite (bv_or_pos_smax Hn_s Hs_sign).
    unfold bv_sle.
    rewrite (bv_or_size Hx_size Hn_s), signed_max_size. rewrite N.eqb_refl.
    destruct (N.to_nat n) as [| t'] eqn:Hn_nat.
    + unfold signed_max. rewrite Hn_nat. simpl.
      destruct x as [| bx xtail].
      * destruct s as [| bs stail].
        ** reflexivity.
        ** unfold size in Hx_size.
           simpl in Hx_size. 
           rewrite <- Hx_size in Hn_s. 
           unfold size in Hn_s.
           discriminate Hn_s.
      * unfold size in Hx_size.
        rewrite <- Hx_size in Hn_nat.
        simpl in Hn_nat.
        lia.
    + unfold signed_max, smax_big_endian.
      rewrite Hn_nat.
      simpl rev. 
      rewrite rev_mk_list_true.
      remember (bv_or x s) as y.
      assert (Hy_not_nil: y <> nil). 
      {
        intro Hy_nil.
        assert (Hy_size: size y = n).
        {
          rewrite Heqy.
          apply bv_or_size.
          - exact Hx_size.
          - exact Hn_s.
        }
        rewrite Hy_nil in Hy_size.
        unfold size in Hy_size. 
        simpl in Hy_size. 
        rewrite <- Hy_size in Hn_nat.
        simpl in Hn_nat.
        discriminate Hn_nat.
      }
      rewrite (app_removelast_last false Hy_not_nil) at 1.
      unfold sle_list.
      rewrite rev_unit.
      rewrite rev_unit.
      destruct (last y false) eqn:Hy_sign.
      * reflexivity. 
      * simpl.
        rewrite orb_false_r.
        rewrite rev_mk_list_true.
        replace t' with (length (rev (removelast y))).
        ** apply ule_list_big_endian_1.
        ** rewrite length_rev.
           assert (Hy_size: size y = n). 
           { rewrite Heqy. apply bv_or_size; assumption. }
           unfold size in Hy_size.
           rewrite <- Hy_size in Hn_nat.
           simpl in Hn_nat.
           pose proof (app_removelast_last false Hy_not_nil) as H_split.
           apply (f_equal size) in H_split.
           rewrite Nnat.Nat2N.id in Hn_nat.
           rewrite removelast_firstn_len.
           rewrite length_firstn.
           rewrite Hn_nat.
           simpl.
           rewrite Nat.min_l by lia.
           reflexivity.
Qed.

Lemma bv_and_sle_maxs : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  bv_sle (bv_and x y) (bv_and x (signed_max n)) = true.
Proof.
  intros n x y Hx Hy. unfold bv_sle, sle_list. unfold bv_and.
  rewrite Hx, Hy. rewrite (signed_max_size n). rewrite N.eqb_refl.
  unfold bits. replace (size (map2 andb x y)) with n.
  2: { rewrite <- Hx. apply size_len_eq. apply map2_and_length. apply size_len_eq. rewrite Hx, Hy. reflexivity. }
  replace (size (map2 andb x (signed_max n))) with n.
  2: { rewrite <- Hx. apply size_len_eq. apply map2_and_length. 
       apply size_len_eq. rewrite Hx. rewrite (signed_max_size n). easy. }
  rewrite N.eqb_refl. rewrite rev_map2_and; auto.
  rewrite rev_map2_and; auto.
  2: { apply size_len_eq. rewrite (signed_max_size n). easy. }
  remember (rev x) as rx. remember (rev y) as ry.
  remember (rev (signed_max n)) as rmax.
  2: { apply size_len_eq. rewrite Hx, Hy. easy. }
  destruct rmax as [| m_head m_tail].
  { assert (Hn_zero : n = 0%N).
    { apply (f_equal (@length bool)) in Heqrmax. 
      apply size_len_eq in Heqrmax.
      unfold size in Heqrmax. simpl in Heqrmax.
      rewrite length_rev in Heqrmax.
      change (N.of_nat (length (signed_max n))) with (size (signed_max n)) in Heqrmax.
      rewrite signed_max_size in Heqrmax. symmetry. easy. }
    subst n. destruct rx.
    - destruct ry.
      + simpl. reflexivity.
      + apply (f_equal size) in Heqrx. apply (f_equal size) in Heqry.
        rewrite size_rev in Heqry. rewrite Hy in Heqry.
        rewrite Hn_zero in Heqry. unfold size in Heqry. simpl in Heqry.
        discriminate.
    - apply (f_equal size) in Heqrx. rewrite size_rev in Heqrx.
      rewrite Hn_zero in Heqrx. discriminate. }
  assert (Hm_head : m_head = false). 
  { unfold signed_max in Heqrmax. unfold smax_big_endian in Heqrmax.
    rewrite rev_involutive in Heqrmax. destruct (N.to_nat n) as [| k] eqn:Hnat.
    - discriminate.
    - injection Heqrmax as Htail Hhead. subst m_head. easy. }
  subst m_head. destruct rx as [| hx tx].
  - simpl. easy.
  - destruct ry as [| hy ty].
    + exfalso. apply f_equal with (f := size) in Heqrx.
      apply f_equal with (f := size) in Heqry. rewrite size_rev in *. 
      rewrite Hx in Heqrx. rewrite Hy in Heqry.
      rewrite <- Heqry in Heqrx. discriminate.
    + simpl. destruct hx.
      * simpl. destruct hy.
        ** reflexivity.
        ** simpl. rewrite Bool.orb_false_r.
            replace (map2 andb tx m_tail) with tx.
          ***  apply ule_list_big_endian_map2_and.
               apply f_equal with (f := size) in Heqrx.
               apply f_equal with (f := size) in Heqry.
               apply f_equal with (f := N.to_nat) in Heqrx.
               apply f_equal with (f := N.to_nat) in Heqry.
               rewrite non_empty_list_size in Heqrx.
               rewrite non_empty_list_size in Heqry.
               rewrite size_rev in Heqrx.
               rewrite size_rev in Heqry. rewrite Hx in Heqrx.
               rewrite Hy in Heqry. rewrite <- Heqry in Heqrx.
               injection Heqrx as H_size_eq. apply size_len_eq.
               apply N2Nat.inj. easy.
          *** symmetry. replace m_tail with (mk_list_true (length tx)).
            **** apply map2_and_1_neutral.
            **** unfold signed_max in Heqrmax. 
                 unfold smax_big_endian in Heqrmax.
                 rewrite rev_involutive in Heqrmax.
                 apply f_equal with (f := size) in Heqrx.
                 rewrite size_rev in Heqrx.
                 apply f_equal with (f := N.to_nat) in Heqrx.
                 rewrite non_empty_list_size in Heqrx.
                 rewrite Hx in Heqrx.
                 rewrite <- Heqrx in Heqrmax.
                 injection Heqrmax as H_tail_eq. rewrite H_tail_eq.
                f_equal. unfold size. rewrite Nnat.Nat2N.id. easy.
      * simpl. rewrite Bool.orb_false_r.
        replace (map2 andb tx m_tail) with tx.
        ** apply ule_list_big_endian_map2_and.
           apply f_equal with (f:=size) in Heqrx.
           apply f_equal with (f:=size) in Heqry.
           apply f_equal with (f := N.to_nat) in Heqrx.
           apply f_equal with (f := N.to_nat) in Heqry.
           rewrite non_empty_list_size in Heqrx.
           rewrite non_empty_list_size in Heqry.
           rewrite size_rev in Heqrx. rewrite size_rev in Heqry.
           rewrite Hx in Heqrx. rewrite Hy in Heqry.
           rewrite <- Heqry in Heqrx.
           injection Heqrx as H_size_eq. apply size_len_eq.
           apply N2Nat.inj. easy.
        ** symmetry. replace m_tail with (mk_list_true (length tx)).
          **** apply map2_and_1_neutral.
          **** unfold signed_max in Heqrmax. 
               unfold smax_big_endian in Heqrmax.
               rewrite rev_involutive in Heqrmax.
               apply f_equal with (f := size) in Heqrx.
               rewrite size_rev in Heqrx.
               apply f_equal with (f := N.to_nat) in Heqrx.
               rewrite non_empty_list_size in Heqrx.
               rewrite Hx in Heqrx. rewrite <- Heqrx in Heqrmax.
               injection Heqrmax as H_tail_eq.
               rewrite H_tail_eq. f_equal. unfold size.
               rewrite Nnat.Nat2N.id. easy.
Qed.

Lemma map2_orb_app : forall (a b c d : list bool),
  length a = length c ->
  map2 orb (a ++ b) (c ++ d) = map2 orb a c ++ map2 orb b d.
Proof.
  intros a. induction a as [|x xs IH].
  - intros b c d H_len. destruct c as [|y ys].
    + simpl. reflexivity.
    + simpl in H_len. discriminate H_len.
  - intros b c d H_len. destruct c as [|y ys].
    + simpl in H_len. discriminate H_len.
    + simpl in H_len. inversion H_len as [H_len_xs].
      simpl. rewrite (IH b ys d H_len_xs). reflexivity.
Qed.

Lemma rev_map2_orb : forall (a b : list bool),
  length a = length b ->
  rev (map2 orb a b) = map2 orb (rev a) (rev b).
Proof.
  induction a as [|x xs IH].
  - intros b H_len. destruct b as [|y ys].
    + reflexivity.
    + discriminate H_len.
  - intros b H_len. destruct b as [|y ys].
    + discriminate H_len.
    + simpl in H_len. inversion H_len as [H_len_xs].
      simpl. rewrite IH by assumption.
      change [x || y] with (map2 orb [x] [y]).
      rewrite <- map2_orb_app.
      * reflexivity.
      * rewrite length_rev, length_rev. exact H_len_xs.
Qed.

Lemma rev_bv_or : forall (a b : bitvector),
  size a = size b ->
  rev (bv_or a b) = bv_or (rev a) (rev b).
Proof.
  intros a b H_size. unfold bv_or. rewrite H_size.
  rewrite N.eqb_refl. unfold size, bits.
  rewrite !length_rev. unfold size in H_size.
  rewrite H_size, N.eqb_refl. apply rev_map2_orb. lia.
Qed.

(* s >=s (s & t) -> (max_s | s) >=s t *)
Lemma bvor_smax_sge_helper : forall (n : N) (s t: bitvector),
  (0 < n)%N -> size s = n -> size t = n ->
  bv_sge s (bv_and s t) = true ->
  bv_sge (bv_or (signed_max n) s) t = true.
Proof.
  intros n s t H_n_pos H_size_s H_size_t H_sge_and.
  unfold bv_sge. rewrite H_size_t.
  assert (H_size_or: size (bv_or (signed_max n) s) = n).
  { apply bv_or_size; [apply signed_max_size |
    exact H_size_s]. }
  rewrite H_size_or, N.eqb_refl. unfold sge_list.
  unfold bv_sge in H_sge_and.
  assert (H_size_and: size (bv_and s t) = n)
  by (apply bv_and_size; assumption).
  rewrite H_size_s, H_size_and, N.eqb_refl in H_sge_and.
  unfold sge_list in H_sge_and.
  assert (H_nat_pos : (0 < N.to_nat n)%nat) by lia.
  destruct (N.to_nat n) as [| t'] eqn:H_nat_n.
  * inversion H_nat_pos.
  * rewrite rev_bv_or; [| rewrite H_size_s;
    apply signed_max_size].
    unfold signed_max; rewrite rev_involutive, H_nat_n;
    simpl smax_big_endian.
    destruct (rev s) as [| s_sign s_tail] eqn:H_rev_s.
    { assert (H_len_s : length (rev s) = 0%nat)
      by (rewrite H_rev_s; reflexivity).
      rewrite length_rev in H_len_s.
      unfold size in H_size_s; rewrite H_len_s in H_size_s.
      rewrite <- H_size_s in H_nat_n; simpl in H_nat_n;
      discriminate H_nat_n. }
    destruct (rev t) as [| t_sign t_tail] eqn:H_rev_t.
    { assert (H_len_t : length (rev t) = 0%nat)
      by (rewrite H_rev_t; reflexivity).
      rewrite length_rev in H_len_t.
      unfold size in H_size_t; rewrite H_len_t in H_size_t.
      rewrite <- H_size_t in H_nat_n; simpl in H_nat_n;
      discriminate H_nat_n. }
    unfold bv_or.
    assert (H_size_check : size (false :: mk_list_true t')
    = size (s_sign :: s_tail)).
    { unfold size; apply f_equal.
      assert (H_LHS: length (false :: mk_list_true t')
      = S t').
      { simpl; f_equal; clear; induction t'; [reflexivity |
        simpl; f_equal; exact IHt']. }
      rewrite H_LHS.
      assert (H_RHS : length (s_sign :: s_tail) = S t').
      { assert (H_rev_len : length (s_sign :: s_tail) =
        length (rev s)) by (rewrite H_rev_s; reflexivity).
        rewrite H_rev_len, length_rev.
        unfold size in H_size_s; lia. }
      rewrite H_RHS; reflexivity. }
    rewrite H_size_check, N.eqb_refl; try unfold bits;
    simpl.
    try unfold bv_sge in H_sge_and.
    unfold bv_and in H_sge_and.
    rewrite H_size_s, H_size_t, N.eqb_refl in H_sge_and.
    try unfold bits in H_sge_and.
    assert (H_len_st : length s = length t)
    by (unfold size in *; lia).
    rewrite rev_map2_and in H_sge_and by assumption.
    rewrite H_rev_s, H_rev_t in H_sge_and; simpl in
    H_sge_and.
    destruct s_sign eqn:Hs_sign; destruct t_sign
    eqn:Ht_sign.
    -- rewrite orb_false_r.
       assert (H_len_t_tail : length t_tail = t').
       { assert (H_rev_len : length (rev t) =
         length (true :: t_tail)) by (rewrite H_rev_t;
         reflexivity).
         rewrite length_rev in H_rev_len.
         simpl in H_rev_len.
         assert (H_tmp: N.to_nat (N.of_nat (length t)) =
         N.to_nat n) by (f_equal; exact H_size_t).
         rewrite H_nat_n in H_tmp; lia. }
       assert (H_len_s_tail : length s_tail = t').
       { assert (H_rev_len : length (rev s) =
         length (true :: s_tail)) by (rewrite H_rev_s;
         reflexivity).
         rewrite length_rev in H_rev_len.
         simpl in H_rev_len.
         assert (H_tmp: N.to_nat (N.of_nat (length s)) =
         N.to_nat n) by (f_equal; exact H_size_s).
         rewrite H_nat_n in H_tmp; lia. }
       clear -H_len_s_tail H_len_t_tail.
       generalize dependent t_tail.
       generalize dependent s_tail.
       induction t' as [| t'' IHt];
       intros [| b_s s_tail'] H_s [| b_t t_tail'] H_t;
       simpl in *; try reflexivity; try discriminate.
       destruct b_t; simpl; [rewrite orb_false_r;
       apply IHt; lia | reflexivity].
    -- simpl in H_sge_and; discriminate H_sge_and.
    -- reflexivity.
    -- rewrite orb_false_r.
       assert (H_len_t_tail : length t_tail = t').
       { assert (H_rev_len : length (rev t) =
         length (false :: t_tail)) by (rewrite H_rev_t;
         reflexivity).
         rewrite length_rev in H_rev_len.
         simpl in H_rev_len.
         assert (H_tmp: N.to_nat (N.of_nat (length t)) =
         N.to_nat n) by (f_equal; exact H_size_t).
         rewrite H_nat_n in H_tmp; lia. }
       assert (H_len_s_tail : length s_tail = t').
       { assert (H_rev_len : length (rev s) =
         length (false :: s_tail)) by (rewrite H_rev_s;
         reflexivity).
         rewrite length_rev in H_rev_len.
         simpl in H_rev_len.
         assert (H_tmp: N.to_nat (N.of_nat (length s)) =
         N.to_nat n) by (f_equal; exact H_size_s).
         rewrite H_nat_n in H_tmp; lia. }
       clear -H_len_s_tail H_len_t_tail.
       generalize dependent t_tail.
       generalize dependent s_tail.
       induction t' as [| t'' IHt];
       intros [| b_s s_tail'] H_s [| b_t t_tail'] H_t;
       simpl in *; try reflexivity; try discriminate.
       destruct b_t; simpl; [rewrite orb_false_r;
       apply IHt; lia | reflexivity].
Qed.

(* s >=s (s & t) <- (max_s | s) >=s t *)
Lemma bvor_sge_exists_helper : forall (n : N) (s t x :
bitvector), (0 < n)%N -> size s = n -> size t = n ->
size x = n -> bv_sge (bv_or x s) t = true ->
bv_sge s (bv_and s t) = true.
Proof.
  intros n s t x H_n_pos H_size_s H_size_t H_size_x.
  intros H_sge_or. unfold bv_sge. rewrite H_size_s.
  assert (H_size_and : size (bv_and s t) = n)
  by (apply bv_and_size; assumption).
  rewrite H_size_and, N.eqb_refl; unfold sge_list.
  unfold bv_sge in H_sge_or.
  assert (H_size_or : size (bv_or x s) = n)
  by (apply bv_or_size; assumption).
  rewrite H_size_or, H_size_t, N.eqb_refl in H_sge_or.
  unfold sge_list in H_sge_or.
  assert (H_nat_pos : (0 < N.to_nat n)%nat) by lia.
  destruct (N.to_nat n) as [| t'] eqn:H_nat_n.
  * inversion H_nat_pos.
  * unfold bv_and; unfold bv_or in H_sge_or.
    try unfold bits; try unfold bits in H_sge_or.
    assert (H_eqb_st : (size s =? size t)%N = true)
    by (rewrite H_size_s, H_size_t; apply N.eqb_refl).
    rewrite H_eqb_st.
    assert (H_len_st : length s = length t)
    by (unfold size in *; lia).
    rewrite rev_map2_and by assumption.
    assert (H_eqb_xs : (size x =? size s)%N = true)
    by (rewrite H_size_x, H_size_s; apply N.eqb_refl).
    rewrite H_eqb_xs in H_sge_or.
    assert (H_len_xs : length x = length s)
    by (unfold size in *; lia).
    rewrite rev_map2_orb in H_sge_or by assumption.
    destruct (rev s) as [| s_sign s_tail] eqn:H_rev_s.
    { assert (H_len_s : length (rev s) = 0%nat)
      by (rewrite H_rev_s; reflexivity).
      rewrite length_rev in H_len_s.
      unfold size in H_size_s; rewrite H_len_s in H_size_s.
      rewrite <- H_size_s in H_nat_n; simpl in H_nat_n.
      discriminate H_nat_n. }
    destruct (rev t) as [| t_sign t_tail] eqn:H_rev_t.
    { assert (H_len_t : length (rev t) = 0%nat)
      by (rewrite H_rev_t; reflexivity).
      rewrite length_rev in H_len_t.
      unfold size in H_size_t; rewrite H_len_t in H_size_t.
      rewrite <- H_size_t in H_nat_n; simpl in H_nat_n.
      discriminate H_nat_n. }
    destruct (rev x) as [| x_sign x_tail] eqn:H_rev_x.
    { assert (H_len_x : length (rev x) = 0%nat)
      by (rewrite H_rev_x; reflexivity).
      rewrite length_rev in H_len_x.
      unfold size in H_size_x; rewrite H_len_x in H_size_x.
      rewrite <- H_size_x in H_nat_n; simpl in H_nat_n.
      discriminate H_nat_n. }
    simpl; simpl in H_sge_or.
    destruct s_sign eqn:Hs_sign; destruct t_sign
    eqn:Ht_sign.
    -- simpl; rewrite orb_false_r.
       assert (H_len_tails : length s_tail = length t_tail).
       { assert (H_s_len : length (rev s) =
         length (true :: s_tail))
         by (rewrite H_rev_s; reflexivity).
         assert (H_t_len : length (rev t) =
         length (true :: t_tail))
         by (rewrite H_rev_t; reflexivity).
         rewrite length_rev in H_s_len, H_t_len.
         simpl in H_s_len, H_t_len; lia. }
       clear -H_len_tails; generalize dependent t_tail.
       induction s_tail as [| b_s s_tail' IH];
       intros [| b_t t_tail'] H_len; simpl in *;
       try reflexivity; try discriminate.
       destruct b_s; destruct b_t; simpl;
       try (rewrite orb_false_r; apply IH; lia);
       reflexivity.
    -- rewrite orb_true_r in H_sge_or.
       simpl in H_sge_or; discriminate H_sge_or.
    -- simpl; rewrite orb_false_r.
       assert (H_len_tails : length s_tail = length t_tail).
       { assert (H_s_len : length (rev s) =
         length (false :: s_tail))
         by (rewrite H_rev_s; reflexivity).
         assert (H_t_len : length (rev t) =
         length (true :: t_tail))
         by (rewrite H_rev_t; reflexivity).
         rewrite length_rev in H_s_len, H_t_len.
         simpl in H_s_len, H_t_len; lia. }
       clear -H_len_tails; generalize dependent t_tail.
       induction s_tail as [| b_s s_tail' IH];
       intros [| b_t t_tail'] H_len; simpl in *;
       try reflexivity; try discriminate.
       destruct b_s; destruct b_t; simpl;
       try (rewrite orb_false_r; apply IH; lia);
       reflexivity.
    -- simpl; rewrite orb_false_r.
       assert (H_len_tails : length s_tail = length t_tail).
       { assert (H_s_len : length (rev s) =
         length (false :: s_tail))
         by (rewrite H_rev_s; reflexivity).
         assert (H_t_len : length (rev t) =
         length (false :: t_tail))
         by (rewrite H_rev_t; reflexivity).
         rewrite length_rev in H_s_len, H_t_len.
         simpl in H_s_len, H_t_len; lia. }
       clear -H_len_tails; generalize dependent t_tail.
       induction s_tail as [| b_s s_tail' IH];
       intros [| b_t t_tail'] H_len; simpl in *;
       try reflexivity; try discriminate.
       destruct b_s; destruct b_t; simpl;
       try (rewrite orb_false_r; apply IH; lia);
       reflexivity.
Qed.

Lemma firstn_removelast : forall {A : Type} (k : nat) (l : list A),
  (k < length l)%nat -> firstn k (removelast l) = firstn k l.
Proof.
  intros A k l.
  generalize dependent k.
  induction l as [| h t IHl].
  - simpl. intros k H. lia.
  - intros k Hlen.
    destruct t as [| h' t'].
    + simpl in Hlen.
      assert (k = 0)%nat by lia.
      subst k.
      simpl. reflexivity.
    + simpl.
      destruct k.
      * reflexivity.
      * simpl. f_equal.
        apply IHl.
        simpl. simpl in Hlen. lia.
Qed.

Lemma shl_n_bits_low_bits_zero : forall (k : nat) (a : list bool),
  (k <= length a)%nat -> 
  firstn k (shl_n_bits a k) = mk_list_false k.
Proof.
  induction k as [| k' IHk].
  - intros a Hlen.
    simpl. reflexivity.
  - intros a Hlen.
    rewrite <- shl_n_shl_one.
    rewrite shl_n_shl_one_comm.
    rewrite mk_list_false_succ.
    assert (Hne: shl_n_bits a k' <> []).
    { 
      intro H.
      assert (Hlen' : length (shl_n_bits a k') = 0%nat).
      { rewrite H. reflexivity. }
      rewrite length_shl_n_bits in Hlen'.
      lia.
    }
    rewrite shl_one; auto.
    simpl.
    f_equal.
    assert (Hlen': (k' < length (shl_n_bits a k'))%nat).
    {
      rewrite length_shl_n_bits. lia.
    }
    rewrite firstn_removelast; try lia.
    apply IHk.
    lia.
Qed.


Lemma nth_mk_list_false : forall (i n : nat),
  (i < n)%nat -> nth i (mk_list_false n) false = false.
Proof.
  induction i as [| i' IHi].
  - intros n Hn.
    destruct n.
    + lia.
    + rewrite mk_list_false_succ. simpl. reflexivity.
  - intros n Hn.
    destruct n.
    + lia.
    + rewrite mk_list_false_succ. simpl. 
      apply IHi. lia.
Qed.

Lemma nth_firstn : forall {A : Type} (i k : nat) (l : list A) (d : A),
  (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  intros A i k l d Hi.
  generalize dependent l.
  generalize dependent i.
  induction k as [| k' IHk].
  - intros i Hi. lia.
  - intros i Hi l.
    destruct l as [| h t].
    + simpl. destruct i; reflexivity.
    + simpl. destruct i.
      * reflexivity.
      * apply IHk. lia.
Qed.

Lemma shl_n_bits_nth_low_bits_zero : forall (k : nat) (a : list bool) (i : nat),
  (k <= length a)%nat ->
  (i < k)%nat ->
  nth i (shl_n_bits a k) false = false.
Proof.
  intros k a i Hlen Hi.
  assert (H : firstn k (shl_n_bits a k) = mk_list_false k).
  { apply shl_n_bits_low_bits_zero. exact Hlen. }
  assert (Haux : nth i (firstn k (shl_n_bits a k)) false = nth i (shl_n_bits a k) false).
  { apply nth_firstn. exact Hi. }
  rewrite <- Haux.
  rewrite H.
  apply nth_mk_list_false. exact Hi.
Qed.

Lemma skipn_app_le : forall {A : Type} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat ->
  skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  induction k as [| k' IHk].
  - intros l1 l2 Hlen. simpl. reflexivity.
  - intros l1 l2 Hlen.
    destruct l1 as [| h t].
    + simpl in Hlen. lia.
    + simpl. apply IHk. simpl in Hlen. lia.
Qed.

Lemma shr_n_bits_skipn_append : forall (k : nat) (v : list bool),
  (k <= length v)%nat ->
  shr_n_bits v k = skipn k v ++ mk_list_false k.
Proof.
  induction k as [| k' IHk].
  - intros v Hlen. simpl. rewrite app_nil_r. reflexivity.
  - intros v Hlen.
    destruct v as [| b vs].
    + simpl in Hlen. lia.
    + simpl. 
      rewrite IHk.
      * rewrite skipn_app_le.
        -- rewrite <- app_assoc. reflexivity.
        -- simpl in Hlen. lia.
      * rewrite length_app. simpl. simpl in Hlen. lia.
Qed.

Lemma bv_slt_ult_equiv_when_msb_zero : forall (a b : list bool),
  last a false = false ->
  last b false = false ->
  bv_slt a b = bv_ult a b.
Proof.
  intros a b Ha Hb.
  assert (Heq : last a false = last b false).
  { rewrite Ha. rewrite Hb. reflexivity. }
  apply bv_slt_ult_last_eq with (d := false).
  exact Heq.
Qed.

Lemma bv_sle_ule_equiv_when_msb_zero : forall (a b : list bool),
  last a false = false ->
  last b false = false ->
  bv_sle a b = bv_ule a b.
Proof.
  intros a b Ha Hb.
  destruct (bv_sle a b) eqn:Hsle; destruct (bv_ule a b) eqn:Hule.
  - reflexivity.
  - apply bv_sle_eq in Hsle.
    destruct Hsle as [Hslt | Heq].
    + rewrite bv_slt_ult_equiv_when_msb_zero in Hslt by assumption.
      assert (Hule' : bv_ule a b = true).
      { apply bv_ule_eq. left. exact Hslt. }
      rewrite Hule in Hule'. discriminate.
    + subst. rewrite bv_ule_refl in Hule. discriminate.
  - apply bv_ule_eq in Hule.
    destruct Hule as [Hult | Heq].
    + rewrite <- bv_slt_ult_equiv_when_msb_zero in Hult by assumption.
      assert (Hsle' : bv_sle a b = true).
      { apply bv_sle_eq. left. exact Hult. }
      rewrite Hsle in Hsle'. discriminate.
    + subst. rewrite bv_sle_refl in Hsle. discriminate.
  - reflexivity.
Qed.

Lemma last_rev : forall {A : Type} (l : list A) (d : A),
  l <> [] ->
  last (rev l) d = hd d l.
Proof.
  intros A l d Hne.
  destruct l as [| h t].
  - contradiction.
  - simpl. rewrite last_app. reflexivity.
Qed.

Lemma hd_smax_big_endian : forall (n : nat),
  (0 < n)%nat ->
  hd false (smax_big_endian n) = false.
Proof.
  intros n Hn.
  destruct n.
  - lia.
  - simpl. reflexivity.
Qed.

Lemma smax_big_endian_nonempty : forall (n : nat),
  (0 < n)%nat ->
  smax_big_endian n <> [].
Proof.
  intros n Hn.
  destruct n.
  - lia.
  - simpl. discriminate.
Qed.

Lemma last_signed_max_false : forall (n : N),
  (0 < N.to_nat n)%nat ->
  last (signed_max n) false = false.
Proof.
  intros n Hn.
  unfold signed_max.
  rewrite last_rev.
  - apply hd_smax_big_endian. exact Hn.
  - apply smax_big_endian_nonempty. exact Hn.
Qed.

Lemma msb_shl_shr_signed_max_zero : forall (n : N) (k : nat),
  (0 < k)%nat ->
  (k < N.to_nat n)%nat ->
  last (shl_n_bits_a (shr_n_bits (signed_max n) k) k) false = false.
Proof.
  intros n k Hk Hlen.
  rewrite shr_n_bits_skipn_append.
  - rewrite last_skipn_false.
    + apply last_signed_max_false. lia.
    + pose proof (signed_max_size n) as Hsize.
      unfold size in Hsize.
      apply Nat.ltb_lt.
      lia.
  - pose proof (signed_max_size n) as Hsize.
    unfold size in Hsize. lia.
Qed.

Lemma skipn_mk_list_true : forall (k n : nat),
  (k <= n)%nat ->
  skipn k (mk_list_true n) = mk_list_true (n - k).
Proof.
  induction k as [| k' IHk].
  - intros n Hlen. simpl. rewrite Nat.sub_0_r. reflexivity.
  - intros n Hlen.
    destruct n.
    + lia.
    + rewrite mk_list_true_succ.
      simpl.
      rewrite IHk by lia.
      f_equal.
Qed.

Lemma signed_max_structure : forall (n : nat),
  (0 < n)%nat ->
  signed_max (N.of_nat n) = mk_list_true (n - 1) ++ [false].
Proof.
  intros n Hn.
  unfold signed_max.
  rewrite Nat2N.id.
  destruct n.
  - lia.
  - simpl.
    rewrite rev_mk_list_true.
    rewrite Nat.sub_0_r.
    reflexivity.
Qed.

Lemma shr_signed_max_structure : forall (n : nat) (k : nat),
  (0 < n)%nat ->
  (k < n)%nat ->
  shr_n_bits (signed_max (N.of_nat n)) k = skipn k (mk_list_true (n - 1) ++ [false]) ++ mk_list_false k.
Proof.
  intros n k Hn Hk.
  rewrite signed_max_structure by lia.
  rewrite shr_n_bits_skipn_append.
  - reflexivity.
  - rewrite length_app. rewrite length_mk_list_true. simpl. lia.
Qed.

Lemma shr_signed_max_bit_pattern : forall (n : nat) (k : nat),
  (0 < n)%nat ->
  (k < n - 1)%nat ->
  shr_n_bits (signed_max (N.of_nat n)) k = mk_list_true (n - 1 - k) ++ [false] ++ mk_list_false k.
Proof.
  intros n k Hn Hk.
  rewrite shr_signed_max_structure by lia.
  rewrite skipn_app_le by (rewrite length_mk_list_true; lia).
  rewrite skipn_mk_list_true by lia.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma M_bit_pattern : forall (n : nat) (k : nat),
  (0 < n)%nat ->
  (0 < k)%nat ->
  (k < n - 1)%nat ->
  shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) k) k = 
  mk_list_false k ++ mk_list_true (n - 1 - k) ++ [false].
Proof.
  intros n k Hn Hk Hkn.
  rewrite shr_signed_max_bit_pattern by lia.
  unfold shl_n_bits_a.
  assert (Hlen : (k <? length (mk_list_true (n - 1 - k) ++ [false] ++ mk_list_false k))%nat = true).
  { apply Nat.ltb_lt. 
    rewrite length_app. rewrite length_app.
    rewrite length_mk_list_true. rewrite length_mk_list_false.
    simpl. lia. }
  rewrite Hlen.
  rewrite length_app. rewrite length_app.
  rewrite length_mk_list_true. rewrite length_mk_list_false. simpl.
  replace (n - 1 - k + 1 + k - k)%nat with (n - 1 - k + 1)%nat by lia.
  rewrite firstn_app.
  rewrite firstn_all2.
  - rewrite length_mk_list_true.
    replace (n - 1 - k + S k - k - (n - 1 - k))%nat with 1%nat by lia.
    simpl.
    reflexivity.
  - rewrite length_mk_list_true. lia.
Qed.


Lemma nth_last : forall {A : Type} (l : list A) (d : A),
  l <> [] ->
  nth (length l - 1) l d = last l d.
Proof.
  intros A l d Hne.
  induction l as [| h t IHl].
  - contradiction.
  - simpl. destruct t as [| h' t'].
    + simpl. reflexivity.
    + simpl in *. rewrite Nat.sub_0_r in *. apply IHl. discriminate.
Qed.

Lemma M_is_max_signed_in_shifted : forall (n : nat) (k : nat) (v : list bool),
  (0 < n)%nat ->
  (0 < k)%nat ->
  (k < n - 1)%nat ->
  length v = n ->
  firstn k v = mk_list_false k ->
  bv_sle v (shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) k) k) = true.
Proof.
  intros n k v Hn Hk Hkn Hvlen Hvlow.
  set (M := shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) k) k).
  destruct (last v false) eqn:Hvsign.
  - apply bv_sle_eq. left.
    apply bv_slt_tf.
    + unfold size, M.
      rewrite Hvlen, length_shl_n_bits_a, length_shr_n_bits.
      pose proof (signed_max_size (N.of_nat n)) as Hsize.
      unfold size in Hsize. lia.
    + exact Hvsign.
    + apply msb_shl_shr_signed_max_zero; lia.
  - rewrite bv_sle_ule_equiv_when_msb_zero.
    + unfold M. rewrite M_bit_pattern by lia.
      assert (Hmiddle_len : length (firstn (n - 1 - k) (skipn k v)) = (n - 1 - k)%nat).
      { rewrite firstn_length_le. reflexivity. rewrite length_skipn. lia. }
      assert (Hlast_part : skipn (n - 1) v = [last v false]).
      { rewrite skipn_length_minus_1 by lia.
        f_equal. rewrite <- Hvlen. apply nth_last.
        intro Hempty. subst v. simpl in Hvlen. lia. }
      rewrite Hvsign in Hlast_part.
      assert (Hv_decomp : v = firstn k v ++ firstn (n - 1 - k) (skipn k v) ++ skipn (n - 1) v).
      { rewrite <- (firstn_skipn k v) at 1.
        rewrite <- (firstn_skipn (n - 1 - k) (skipn k v)) at 1.
        rewrite skipn_skipn.
        replace (n - 1 - k + k)%nat with (n - 1)%nat by lia.
        reflexivity. }
      rewrite Hv_decomp. rewrite Hvlow. rewrite Hlast_part.
      apply bv_ule_pre_append.
      apply bv_ule_B2P.
      apply bv_uleP_post_append.
      apply bv_ule_B2P.
      pose proof (bv_ule_1_length (firstn (n - 1 - k) (skipn k v))) as Hule.
      rewrite Hmiddle_len in Hule.
      exact Hule.
    + exact Hvsign.
    + apply msb_shl_shr_signed_max_zero; lia.
Qed.

Lemma length_removelast_match : forall {A : Type} (h : A) (t : list A),
  length match t with
        | [] => []
        | _ :: _ => h :: removelast t
        end = length t.
Proof.
  intros A h t.
  induction t as [| h' t' IHt].
  - simpl. reflexivity.
  - simpl. f_equal.
    clear IHt.
    generalize dependent h'.
    induction t' as [| h'' t'' IHt'].
    + intros. simpl. reflexivity.
    + intros. simpl. f_equal. apply IHt'.
Qed.

Lemma list_eq_nth : forall {A : Type} (a b : list A) (d : A),
  length a = length b ->
  (forall i, (i < length a)%nat -> nth i a d = nth i b d) ->
  a = b.
Proof.
  intros A a.
  induction a as [| h t IHa].
  - intros b d Hlen Hnth.
    destruct b.
    + reflexivity.
    + simpl in Hlen. lia.
  - intros b d Hlen Hnth.
    destruct b as [| h' t'].
    + simpl in Hlen. lia.
    + f_equal.
      * specialize (Hnth 0%nat). simpl in Hnth. apply Hnth. simpl. lia.
      * apply IHa with (d := d).
        -- simpl in Hlen. lia.
        -- intros i Hi. specialize (Hnth (S i)). simpl in Hnth. apply Hnth. simpl. lia.
Qed.

Lemma shl_n_bits_0 : forall (a : list bool),
  shl_n_bits a 0 = a.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Lemma bv_shl_eq_shl_n_bits : forall (a s : bitvector),
  size a = size s ->
  bv_shl a s = shl_n_bits a (bv2nat_a s).
Proof.
  intros a s Hsize.
  unfold bv_shl, shl_aux, bv2nat_a.
  rewrite Hsize.
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Lemma bv_shr_eq_shr_n_bits : forall (a s : bitvector),
  size a = size s ->
  bv_shr a s = shr_n_bits a (bv2nat_a s).
Proof.
  intros a s Hsize.
  unfold bv_shr, shr_aux, bv2nat_a.
  rewrite Hsize.
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Lemma shl_n_bits_a_0 : forall (a : list bool),
  shl_n_bits_a a 0 = a.
Proof.
  intros a.
  unfold shl_n_bits_a.
  simpl.
  destruct a.
  - reflexivity.
  - simpl. f_equal. apply firstn_all.
Qed.

Lemma signed_max_is_max : forall (n : N) (x : bitvector),
  size x = n ->
  (0 < N.to_nat n)%nat ->
  bv_sle x (signed_max n) = true.
Proof.
  intros n x Hsize Hn.
  destruct (last x false) eqn:Hxsign.
  - apply bv_sle_eq. left.
    apply bv_slt_tf.
    + rewrite Hsize. symmetry. apply signed_max_size.
    + exact Hxsign.
    + apply last_signed_max_false. lia.
  - rewrite bv_sle_ule_equiv_when_msb_zero.
    + unfold size in Hsize.
      assert (Hlen : length x = N.to_nat n) by lia.
      rewrite <- N2Nat.id with (a := n).
      rewrite signed_max_structure by lia.
      assert (Hlast : x = firstn (length x - 1) x ++ [last x false]).
      {
        destruct x as [| b xs] eqn:Hx.
        - simpl in Hlen. lia.
        - rewrite app_removelast_last with (l := b :: xs) (d := false) at 1 by discriminate.
          f_equal.
          clear Hx Hxsign Hsize Hlen Hn.
          generalize dependent b.
          induction xs as [| c cs IH].
          + reflexivity.
          + intros b. simpl.
            destruct cs as [| d ds].
            * reflexivity.
            * simpl. f_equal. specialize (IH c). simpl in IH.
              injection IH as IH. rewrite IH. reflexivity.
      }
      rewrite Hxsign in Hlast.
      rewrite Hlast.
      rewrite Hlen.
      apply bv_ule_B2P.
      apply bv_uleP_post_append.
      rewrite <- Hlen.
      pose proof (bv_uleP_1_length (firstn (length x - 1) x)) as H.
      rewrite firstn_length_le in H by lia.
      exact H.
    + exact Hxsign.
    + apply last_signed_max_false. lia.
Qed.

Lemma nth_removelast_match : forall (n : nat) (h : bool) (t : list bool),
  (S n < length (h :: t))%nat ->
  nth n match t with
        | [] => []
        | _ :: _ => h :: removelast t
        end false = 
  match n with
  | 0%nat => h
  | S m => nth m t false
  end.
Proof.
  induction n as [| n' IHn].
  - intros h t Hlen.
    destruct t as [| h' t'].
    + simpl in Hlen. lia.
    + simpl. reflexivity.
  - intros h t Hlen.
    destruct t as [| h' t'].
    + simpl in Hlen. lia.
    + simpl. rewrite IHn.
      * reflexivity.
      * simpl in Hlen. simpl. lia.
Qed.

Lemma shl_n_bits_nth_high : forall (k : nat) (a : list bool) (i : nat),
  (k <= length a)%nat ->
  (k <= i)%nat ->
  (i < length a)%nat ->
  nth i (shl_n_bits a k) false = nth (i - k) a false.
Proof.
  induction k as [| k' IHk].
  - intros a i Hlen Hki Hi.
    rewrite shl_n_bits_0.
    rewrite Nat.sub_0_r.
    reflexivity.
  - intros a i Hlen Hki Hi.
    destruct a as [| h t].
    + simpl in Hlen. lia.
    + destruct i as [| i'].
      * lia.
      * simpl.
        rewrite IHk.
        -- destruct t as [| h' t'].
           ++ simpl in Hi. lia.
           ++ assert (Hdiff: (S i' - k' = S (i' - k'))%nat) by lia.
              rewrite Hdiff. simpl.
              destruct (i' - k')%nat eqn:Hjk.
              ** reflexivity.
              ** rewrite nth_removelast_match.
                 --- reflexivity.
                 --- simpl. simpl in Hi. lia.
        -- destruct t as [| h' t'].
           ++ simpl in Hi. lia.
           ++ simpl. rewrite length_removelast_match. simpl in Hlen. lia.
        -- lia.
        -- destruct t as [| h' t'].
           ++ simpl in Hi. lia.
           ++ simpl. rewrite length_removelast_match. simpl in Hi. lia.
Qed.

Lemma shl_n_bits_eq_shl_n_bits_a : forall (k : nat) (a : list bool),
  (k <= length a)%nat ->
  shl_n_bits a k = shl_n_bits_a a k.
Proof.
  intros k a Hlen.
  apply list_eq_nth with (d := false).
  - rewrite length_shl_n_bits. rewrite length_shl_n_bits_a. reflexivity.
  - intros i Hi.
    rewrite length_shl_n_bits in Hi.
    destruct (Nat.ltb_spec i k) as [Hik | Hik].
    + rewrite shl_n_bits_nth_low_bits_zero by lia.
      unfold shl_n_bits_a.
      destruct (k <? length a)%nat eqn:Hka.
      * rewrite app_nth1 by (rewrite length_mk_list_false; lia).
        rewrite nth_mk_list_false by lia.
        reflexivity.
      * rewrite nth_mk_list_false by lia.
        reflexivity.
    + rewrite shl_n_bits_nth_high by lia.
      unfold shl_n_bits_a.
      destruct (k <? length a)%nat eqn:Hka.
      * rewrite app_nth2 by (rewrite length_mk_list_false; lia).
        rewrite length_mk_list_false.
        rewrite nth_firstn by lia.
        f_equal.
      * apply Nat.ltb_ge in Hka. lia.
Qed.

Lemma M_is_max_signed_in_shifted_general : forall (n : nat) (k : nat) (v : list bool),
  (0 < n)%nat ->
  (k <= n)%nat ->
  length v = n ->
  firstn k v = mk_list_false k ->
  bv_sle v (shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) k) k) = true.
Proof.
  intros n k v Hn Hkn Hlen Hfirst.
  destruct (Nat.eq_dec k 0) as [Hk0 | Hkne0].
  - subst k. simpl.
    rewrite shl_n_bits_a_0.
    apply signed_max_is_max.
    + unfold size. rewrite Hlen. reflexivity.
    + rewrite Nat2N.id. exact Hn.
  - destruct (Nat.ltb_spec k (n - 1)) as [Hklt | Hkge].
    + apply M_is_max_signed_in_shifted.
      * exact Hn.
      * lia.
      * exact Hklt.
      * exact Hlen.
      * exact Hfirst.
    + assert (Hcases: (k = n - 1 \/ k = n)%nat) by lia.
      destruct Hcases as [Hkn1 | Hkn2].
      * subst k.
        assert (Hv: v = mk_list_false (n - 1) ++ [last v false]).
        { apply list_eq_nth with (d := false).
          - rewrite length_app. rewrite length_mk_list_false. simpl. lia.
          - intros i Hi.
            destruct (Nat.ltb_spec i (n - 1)) as [Hilt | Hige].
            + rewrite app_nth1 by (rewrite length_mk_list_false; lia).
              rewrite nth_mk_list_false by lia.
              assert (Hfi: nth i (firstn (n - 1) v) false = false).
              { rewrite Hfirst. rewrite nth_mk_list_false by lia. reflexivity. }
              rewrite nth_firstn in Hfi by lia.
              exact Hfi.
            + assert (Hi2: (i = n - 1)%nat) by lia. subst i.
              rewrite app_nth2 by (rewrite length_mk_list_false; lia).
              rewrite length_mk_list_false. rewrite Nat.sub_diag. simpl.
              rewrite <- Hlen.
              rewrite nth_last.
              * reflexivity.
              * intro Hcontra. rewrite Hcontra in Hlen. simpl in Hlen. lia.
        }
        rewrite Hv.
        destruct (last v false) eqn:Hlast.
        -- assert (HM_msb: last (shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) (n - 1)) (n - 1)) false = false).
           { apply msb_shl_shr_signed_max_zero; lia. }
           apply bv_sle_eq.
           left.
           apply bv_slt_tf.
           ++ unfold size.
              rewrite length_app. rewrite length_mk_list_false. simpl.
              rewrite length_shl_n_bits_a. rewrite length_shr_n_bits.
              assert (Hsm: size (signed_max (N.of_nat n)) = N.of_nat n) by apply signed_max_size.
              unfold size in Hsm. apply Nat2N.inj in Hsm. rewrite Hsm.
              f_equal. lia.
           ++ rewrite last_app. reflexivity.
           ++ exact HM_msb.
        -- assert (Hv2: mk_list_false (n - 1) ++ [false] = mk_list_false n).
           { rewrite <- mk_list_false_app. f_equal. lia. }
           rewrite Hv2.
           assert (Hsm_len: length (signed_max (N.of_nat n)) = n).
           { assert (Hsm: size (signed_max (N.of_nat n)) = N.of_nat n) by apply signed_max_size.
             unfold size in Hsm. apply Nat2N.inj in Hsm. exact Hsm. }
           assert (HM_len: length (shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) (n - 1)) (n - 1)) = n).
           { rewrite length_shl_n_bits_a. rewrite length_shr_n_bits. exact Hsm_len. }
           set (M := shl_n_bits_a (shr_n_bits (signed_max (N.of_nat n)) (n - 1)) (n - 1)) in *.
           rewrite bv_sle_ule_equiv_when_msb_zero.
           ++ assert (Heq: mk_list_false n = mk_list_false (length M)) by (rewrite HM_len; reflexivity).
              rewrite Heq.
              apply bv_ule_0.
           ++ apply last_mk_list_false.
           ++ unfold M. apply msb_shl_shr_signed_max_zero; lia.
      * subst k.
        assert (Hv: v = mk_list_false n).
        { apply list_eq_nth with (d := false).
          - rewrite length_mk_list_false. exact Hlen.
          - intros i Hi.
            rewrite nth_mk_list_false by lia.
            assert (Hfi: nth i (firstn n v) false = false).
            { rewrite Hfirst. rewrite nth_mk_list_false by lia. reflexivity. }
            rewrite firstn_all2 in Hfi by lia.
            exact Hfi.
        }
        rewrite Hv.
        unfold shl_n_bits_a.
        assert (Hshr_len: length (shr_n_bits (signed_max (N.of_nat n)) n) = n).
        { rewrite length_shr_n_bits.
          assert (Hsm: size (signed_max (N.of_nat n)) = N.of_nat n) by apply signed_max_size.
          unfold size in Hsm. apply Nat2N.inj in Hsm. exact Hsm. }
        destruct (n <? length (shr_n_bits (signed_max (N.of_nat n)) n))%nat eqn:Hlt.
        -- apply Nat.ltb_lt in Hlt. lia.
        -- rewrite Hshr_len. apply bv_sle_refl.
Qed.

Lemma nth_mk_list_true : forall (i n : nat),
  (i < n)%nat -> nth i (mk_list_true n) false = true.
Proof.
  induction i as [| i' IHi].
  - intros n Hn.
    destruct n.
    + lia.
    + rewrite mk_list_true_succ. simpl. reflexivity.
  - intros n Hn.
    destruct n.
    + lia.
    + rewrite mk_list_true_succ. simpl.
      apply IHi. lia.
Qed.

Lemma nth_skipn_gen : forall {A : Type} (j k : nat) (l : list A) (d : A),
  nth j (skipn k l) d = nth (k + j) l d.
Proof.
  intros A j k.
  generalize dependent j.
  induction k as [| k' IHk].
  - intros j l d. simpl. reflexivity.
  - intros j l d. destruct l as [| h t].
    + simpl. destruct j; reflexivity.
    + simpl. apply IHk.
Qed.

Lemma and_shl_shr_signed_max_eq : forall (n : N) (s : bitvector),
  size s = n ->
  bv_and (bv_shl (signed_max n) s) (signed_max n) =
  bv_shl (bv_shr (signed_max n) s) s.
Proof.
  intros n s Hs.
  set (k := bv2nat_a s).
  set (nn := N.to_nat n).
  pose proof (signed_max_size n) as Hsm_size.
  assert (Hsm_len : length (signed_max n) = nn).
  { unfold nn. unfold size in Hsm_size.
    apply f_equal with (f := N.to_nat) in Hsm_size. rewrite Nat2N.id in Hsm_size.
    exact Hsm_size. }
  assert (Hs_len : length s = nn).
  { unfold nn. unfold size in Hs.
    apply f_equal with (f := N.to_nat) in Hs. rewrite Nat2N.id in Hs.
    exact Hs. }
  destruct (Nat.leb nn k) eqn:Hge.
  - apply Nat.leb_le in Hge.
    assert (Hshl_z : bv_shl (signed_max n) s = zeros n).
    { apply shl_ge_size with (n := n).
      - exact Hsm_size.
      - exact Hs.
      - unfold bits. apply Nat.leb_le. fold k. exact Hge. }
    assert (Hshr_size : size (bv_shr (signed_max n) s) = n).
    { apply bv_shr_size. exact Hsm_size. exact Hs. }
    assert (Hshl_shr_z : bv_shl (bv_shr (signed_max n) s) s = zeros n).
    { apply shl_ge_size with (n := n).
      - exact Hshr_size.
      - exact Hs.
      - unfold bits. apply Nat.leb_le. fold k. exact Hge. }
    rewrite Hshl_z. rewrite Hshl_shr_z.
    assert (Hand_comm : bv_and (zeros n) (signed_max n) = bv_and (signed_max n) (zeros n)).
    { apply bv_and_comm with (n := n).
      - apply zeros_size.
      - exact Hsm_size. }
    rewrite Hand_comm.
    rewrite <- Hsm_size at 2. rewrite bv_and_0_absorb.
    rewrite Hsm_size. reflexivity.
  - apply Nat.leb_gt in Hge.
    assert (Hnn_pos : (0 < nn)%nat) by lia.
    rewrite bv_shl_eq_shl_n_bits
      by (rewrite Hsm_size; symmetry; exact Hs).
    fold k.
    assert (Hshr_size : size (bv_shr (signed_max n) s) = n).
    { apply bv_shr_size. exact Hsm_size. exact Hs. }
    rewrite bv_shl_eq_shl_n_bits
      by (rewrite Hshr_size; symmetry; exact Hs).
    rewrite bv_shr_eq_shr_n_bits
      by (rewrite Hsm_size; symmetry; exact Hs).
    fold k.
    assert (HA_len : length (shl_n_bits (signed_max n) k) = nn).
    { rewrite length_shl_n_bits. exact Hsm_len. }
    assert (HC_len : length (shl_n_bits (shr_n_bits (signed_max n) k) k) = nn).
    { rewrite length_shl_n_bits. rewrite length_shr_n_bits. exact Hsm_len. }
    assert (HA_size : size (shl_n_bits (signed_max n) k) = n).
    { unfold size. rewrite HA_len. unfold nn. rewrite N2Nat.id. reflexivity. }
    assert (Hbv_and_len :
      length (bv_and (shl_n_bits (signed_max n) k) (signed_max n)) = nn).
    { assert (H : size (bv_and (shl_n_bits (signed_max n) k) (signed_max n)) = n).
      { apply bv_and_size with (n := n). exact HA_size. exact Hsm_size. }
      unfold size in H. apply f_equal with (f := N.to_nat) in H. rewrite Nat2N.id in H.
      exact H. }
    assert (Hsm_eq : signed_max n = mk_list_true (nn - 1) ++ [false]).
    { assert (Hn_eq : n = N.of_nat nn).
      { unfold nn. symmetry. apply N2Nat.id. }
      rewrite Hn_eq. apply signed_max_structure. lia. }
    apply list_eq_nth with (d := false).
    + rewrite Hbv_and_len. symmetry. exact HC_len.
    + intros i Hi. rewrite Hbv_and_len in Hi.
      assert (Hand_i :
        nth i (bits (bv_and (shl_n_bits (signed_max n) k) (signed_max n))) false =
        nth i (bits (shl_n_bits (signed_max n) k)) false &&
        nth i (bits (signed_max n)) false).
      { apply (@bv_and_nth_bitOf
          (shl_n_bits (signed_max n) k) (signed_max n) n i
          HA_size Hsm_size).
        rewrite HA_size. lia. }
      unfold bits in Hand_i.
      rewrite Hand_i.
      destruct (Nat.ltb_spec i k) as [Hik | Hik].
      * rewrite shl_n_bits_nth_low_bits_zero by lia.
        simpl.
        symmetry.
        apply shl_n_bits_nth_low_bits_zero.
        -- rewrite length_shr_n_bits. lia.
        -- exact Hik.
      * rewrite shl_n_bits_nth_high by lia.
        rewrite shl_n_bits_nth_high
          by (rewrite ?length_shr_n_bits; lia).
        rewrite shr_n_bits_skipn_append by lia.
        rewrite app_nth1 by (rewrite length_skipn; lia).
        rewrite nth_skipn_gen.
        replace (k + (i - k))%nat with i by lia.
        destruct (Nat.eq_dec k 0) as [Hk0 | Hkne0].
        -- rewrite Hk0. replace (i - 0)%nat with i by lia.
           apply Bool.andb_diag.
        -- assert (Htrue : nth (i - k) (signed_max n) false = true).
           { rewrite Hsm_eq.
             rewrite app_nth1 by (rewrite length_mk_list_true; lia).
             apply nth_mk_list_true. lia. }
           rewrite Htrue. reflexivity.
Qed.

Lemma shl_signed_max_bit_pattern : forall (n : nat) (k : nat),
  (0 < n)%nat ->
  (0 < k)%nat ->
  (k < n)%nat ->
  shl_n_bits (signed_max (N.of_nat n)) k = mk_list_false k ++ mk_list_true (n - k).
Proof.
  intros n k Hn Hk Hkn.
  assert (Hsm_len : length (signed_max (N.of_nat n)) = n).
  { assert (Hsm : size (signed_max (N.of_nat n)) = N.of_nat n) by apply signed_max_size.
    unfold size in Hsm.
    apply f_equal with (f := N.to_nat) in Hsm.
    rewrite !Nat2N.id in Hsm. exact Hsm. }
  assert (Hsm_eq : signed_max (N.of_nat n) = mk_list_true (n - 1) ++ [false]).
  { apply signed_max_structure. lia. }
  apply list_eq_nth with (d := false).
  - rewrite length_shl_n_bits. rewrite Hsm_len.
    rewrite length_app. rewrite length_mk_list_false. rewrite length_mk_list_true.
    lia.
  - intros i Hi.
    rewrite length_shl_n_bits in Hi. rewrite Hsm_len in Hi.
    destruct (Nat.ltb_spec i k) as [Hik | Hik].
    + rewrite shl_n_bits_nth_low_bits_zero by lia.
      rewrite app_nth1 by (rewrite length_mk_list_false; lia).
      rewrite nth_mk_list_false by lia.
      reflexivity.
    + rewrite shl_n_bits_nth_high by lia.
      assert (Hsmbit : nth (i - k) (signed_max (N.of_nat n)) false = true).
      { rewrite Hsm_eq.
        rewrite app_nth1 by (rewrite length_mk_list_true; lia).
        apply nth_mk_list_true. lia. }
      rewrite Hsmbit.
      rewrite app_nth2 by (rewrite length_mk_list_false; lia).
      rewrite length_mk_list_false.
      symmetry. apply nth_mk_list_true. lia.
Qed.

Lemma shr_shl_signed_max_bit_pattern : forall (n : nat) (k : nat),
  (0 < n)%nat ->
  (0 < k)%nat ->
  (k < n)%nat ->
  shr_n_bits (shl_n_bits (signed_max (N.of_nat n)) k) k =
  mk_list_true (n - k) ++ mk_list_false k.
Proof.
  intros n k Hn Hk Hkn.
  rewrite shl_signed_max_bit_pattern by lia.
  rewrite shr_n_bits_skipn_append.
  - rewrite skipn_jo. reflexivity.
  - rewrite length_app. rewrite length_mk_list_false. rewrite length_mk_list_true.
    lia.
Qed.

Lemma shr_n_bits_high_bits_false : forall (k : nat) (v : list bool),
  (k <= length v)%nat ->
  skipn (length v - k) (shr_n_bits v k) = mk_list_false k.
Proof.
  intros k v Hlen.
  rewrite shr_n_bits_skipn_append by lia.
  rewrite skipn_app_le.
  - replace (skipn (length v - k) (skipn k v)) with (@nil bool).
    + simpl. reflexivity.
    + symmetry. apply skipn_all.
      rewrite length_skipn. apply Nat.leb_le. lia.
  - rewrite length_skipn. lia.
Qed.

Lemma M_is_max_for_shr_general : forall (n : nat) (k : nat) (v : list bool),
  (0 < n)%nat ->
  (k <= n)%nat ->
  length v = n ->
  skipn (n - k) v = mk_list_false k ->
  bv_sle v (shr_n_bits (shl_n_bits (signed_max (N.of_nat n)) k) k) = true.
Proof.
  intros n k v Hn Hkn Hlen Hhigh.
  destruct (Nat.eq_dec k 0) as [Hk0 | Hkne0].
  - subst k. simpl.
    apply signed_max_is_max.
    + unfold size. rewrite Hlen. reflexivity.
    + rewrite Nat2N.id. exact Hn.
  - destruct (Nat.eq_dec k n) as [Hkn_eq | Hkn_ne].
    + subst k.
      assert (Hv : v = mk_list_false n).
      { rewrite <- Hhigh. rewrite Nat.sub_diag. reflexivity. }
      rewrite Hv.
      assert (Hsm_len : length (signed_max (N.of_nat n)) = n).
      { assert (Hsm : size (signed_max (N.of_nat n)) = N.of_nat n) by apply signed_max_size.
        unfold size in Hsm.
        apply f_equal with (f := N.to_nat) in Hsm.
        rewrite !Nat2N.id in Hsm. exact Hsm. }
      assert (Heq : mk_list_false n = shr_n_bits (shl_n_bits (signed_max (N.of_nat n)) n) n).
      { apply list_eq_nth with (d := false).
        - rewrite length_mk_list_false. rewrite length_shr_n_bits.
          rewrite length_shl_n_bits. rewrite Hsm_len. reflexivity.
        - intros i Hi.
          rewrite length_mk_list_false in Hi.
          rewrite nth_mk_list_false by lia.
          rewrite shr_n_bits_skipn_append
            by (rewrite length_shl_n_bits; rewrite Hsm_len; lia).
          rewrite app_nth2
            by (rewrite length_skipn; rewrite length_shl_n_bits; rewrite Hsm_len; lia).
          rewrite length_skipn. rewrite length_shl_n_bits. rewrite Hsm_len.
          replace (n - n)%nat with 0%nat by lia. simpl.
          replace (i - 0)%nat with i by lia.
          symmetry. apply nth_mk_list_false. lia. }
      rewrite Heq. apply bv_sle_refl.
    + assert (Hk : (0 < k)%nat) by lia.
      assert (Hklt : (k < n)%nat) by lia.
      rewrite shr_shl_signed_max_bit_pattern by lia.
      assert (Hv_decomp : v = firstn (n - k) v ++ skipn (n - k) v).
      { symmetry. apply firstn_skipn. }
      rewrite Hhigh in Hv_decomp.
      assert (Hfirst_len : length (firstn (n - k) v) = (n - k)%nat).
      { rewrite firstn_length_le. reflexivity. lia. }
      assert (Hv_last : last v false = false).
      { rewrite Hv_decomp.
        rewrite last_append.
        - apply last_mk_list_false.
        - destruct k. lia. rewrite mk_list_false_succ. discriminate. }
      assert (HM_last : last (mk_list_true (n - k) ++ mk_list_false k) false = false).
      { rewrite last_append.
        - apply last_mk_list_false.
        - destruct k. lia. rewrite mk_list_false_succ. discriminate. }
      rewrite bv_sle_ule_equiv_when_msb_zero.
      * rewrite Hv_decomp.
        apply bv_ule_B2P.
        apply bv_uleP_post_append.
        apply bv_ule_B2P.
        pose proof (bv_ule_1_length (firstn (n - k) v)) as Hule.
        rewrite Hfirst_len in Hule.
        exact Hule.
      * exact Hv_last.
      * exact HM_last.
Qed.

Lemma shr_one_bit_mk_list_false : forall (n : nat),
  shr_one_bit (mk_list_false n) = mk_list_false n.
Proof.
  intros n.
  pose proof (shr_one_bit_all_false (mk_list_false n)) as H.
  rewrite length_mk_list_false in H.
  exact H.
Qed.

Lemma shr_n_bits_all_false : forall (k n : nat),
  shr_n_bits (mk_list_false n) k = mk_list_false n.
Proof.
  induction k as [| k' IHk].
  - intros n. simpl. reflexivity.
  - intros n.
    rewrite <- shr_n_shr_one.
    rewrite shr_one_bit_mk_list_false.
    apply IHk.
Qed.

Lemma shr_n_bits_compose : forall (j k : nat) (a : list bool),
  shr_n_bits a (j + k) = shr_n_bits (shr_n_bits a j) k.
Proof.
  induction j as [| j' IHj].
  - intros k a. simpl. reflexivity.
  - intros k a.
    replace (S j' + k)%nat with (S (j' + k))%nat by lia.
    rewrite <- shr_n_shr_one.
    rewrite <- (shr_n_shr_one j' a).
    apply IHj.
Qed.

Lemma shr_n_bits_ge_length : forall (k : nat) (a : list bool),
  (length a <= k)%nat ->
  shr_n_bits a k = mk_list_false (length a).
Proof.
  intros k a Hlen.
  replace k with (length a + (k - length a))%nat by lia.
  rewrite shr_n_bits_compose.
  assert (Hinner : shr_n_bits a (length a) = mk_list_false (length a)).
  { rewrite shr_n_bits_skipn_append by lia.
    rewrite skipn_all by (apply Nat.leb_refl).
    simpl. reflexivity. }
  rewrite Hinner.
  apply shr_n_bits_all_false.
Qed.

Lemma shr_ge_size : forall (n : N) (a s : bitvector),
  size a = n ->
  size s = n ->
  (N.to_nat n <=? bv2nat_a s)%nat = true ->
  bv_shr a s = zeros n.
Proof.
  intros n a s Ha Hs Hge.
  apply Nat.leb_le in Hge.
  assert (Ha_len : length a = N.to_nat n).
  { unfold size in Ha.
    apply f_equal with (f := N.to_nat) in Ha.
    rewrite Nat2N.id in Ha. exact Ha. }
  rewrite bv_shr_eq_shr_n_bits by (rewrite Ha; symmetry; exact Hs).
  rewrite shr_n_bits_ge_length by lia.
  unfold zeros. rewrite Ha_len. reflexivity.
Qed.

Lemma ugt_ult_swap : forall (x y : list bool),
  ugt_list_big_endian x y = ult_list_big_endian y x.
Proof.
  intros x y.
  destruct (ugt_list_big_endian x y) eqn:Hugt.
  - symmetry. apply ugt_list_big_endian_ult_list_big_endian. exact Hugt.
  - destruct (ult_list_big_endian y x) eqn:Hult.
    + apply ult_list_big_endian_ugt_list_big_endian in Hult. rewrite Hult in Hugt. discriminate.
    + reflexivity.
Qed.

Lemma bv_sgt_slt_equiv : forall (a b : bitvector), bv_sgt a b = bv_slt b a.
Proof.
  intros a b.
  unfold bv_sgt, bv_slt, sgt_list, slt_list.
  rewrite N.eqb_sym.
  destruct (size b =? size a); [|reflexivity].
  destruct (rev a) eqn:Hra; destruct (rev b) eqn:Hrb; simpl; try reflexivity.
  replace (eqb b0 b1) with (eqb b1 b0) by (destruct b0; destruct b1; reflexivity).
  rewrite ugt_ult_swap.
  rewrite andb_comm with (b1 := negb b0) (b2 := b1).
  reflexivity.
Qed.

Lemma uge_ule_swap : forall (x y : list bool),
  uge_list_big_endian x y = ule_list_big_endian y x.
Proof.
  intros x y.
  destruct (uge_list_big_endian x y) eqn:Huge.
  - symmetry. apply uge_list_big_endian_ule_list_big_endian. exact Huge.
  - destruct (ule_list_big_endian y x) eqn:Hule.
    + apply ule_list_big_endian_uge_list_big_endian in Hule. rewrite Hule in Huge. discriminate.
    + reflexivity.
Qed.

Lemma bv_sge_sle_equiv : forall (a b : bitvector), bv_sge a b = bv_sle b a.
Proof.
  intros a b.
  unfold bv_sge, bv_sle, sge_list, sle_list.
  rewrite N.eqb_sym.
  destruct (size b =? size a); [|reflexivity].
  destruct (rev a) eqn:Hra; destruct (rev b) eqn:Hrb; simpl; try reflexivity.
  replace (eqb b0 b1) with (eqb b1 b0) by (destruct b0; destruct b1; reflexivity).
  rewrite uge_ule_swap.
  rewrite andb_comm with (b1 := negb b0) (b2 := b1).
  reflexivity.
Qed.

Lemma signed_max_sle_any : forall (n : N) (t : bitvector),
  size t = n -> (0 < N.to_nat n)%nat ->
  bv_sle t (signed_max n) = true.
Proof.
  intros n t Ht Hpos.
  apply signed_max_is_max.
  - exact Ht.
  - lia.
Qed.

Lemma zeros_bv2nat_a_pos : forall (n : N) (s : bitvector),
  size s = n -> bv_eq s (zeros n) = false -> (0 < bv2nat_a s)%nat.
Proof.
  intros n s Hs Hsne.
  assert (Hs_len : length s = N.to_nat n).
  { unfold size in Hs.
    apply f_equal with (f := N.to_nat) in Hs.
    rewrite Nat2N.id in Hs. exact Hs. }
  assert (Hs_neq_mlf : s <> mk_list_false (length s)).
  { intro Hcontra.
    assert (s = zeros n).
    { rewrite Hcontra. unfold zeros. rewrite Hs_len. reflexivity. }
    rewrite H in Hsne.
    rewrite bv_eq_refl in Hsne. discriminate. }
  apply gt0_nmk_list_false in Hs_neq_mlf.
  apply Nat.ltb_lt in Hs_neq_mlf.
  unfold bv2nat_a, list2nat_be_a. lia.
Qed.

Lemma shr_ones_is_max_sle : forall (n : N) (x s : bitvector),
  size x = n -> size s = n ->
  bv_eq s (zeros n) = false ->
  bv_sle (bv_shr x s) (bv_shr (bv_not (zeros n)) s) = true.
Proof.
  intros n x s Hx Hs Hsne.
  set (k := bv2nat_a s).
  destruct (Nat.leb (N.to_nat n) k) eqn:Hshift.
  - apply Nat.leb_le in Hshift.
    rewrite shr_ge_size with (n := n) (a := x).
    + rewrite shr_ge_size with (n := n) (a := bv_not (zeros n)).
      * apply bv_sle_refl.
      * apply bv_not_size. apply zeros_size.
      * exact Hs.
      * apply Nat.leb_le. exact Hshift.
    + exact Hx.
    + exact Hs.
    + apply Nat.leb_le. exact Hshift.
  - apply Nat.leb_gt in Hshift.
    rewrite bv_shr_eq_shr_n_bits by (rewrite Hx; symmetry; exact Hs).
    assert (Hones_size : size (bv_not (zeros n)) = n).
    { apply bv_not_size. apply zeros_size. }
    rewrite bv_shr_eq_shr_n_bits
      by (rewrite Hones_size; symmetry; exact Hs).
    fold k.
    assert (Hx_len : length x = N.to_nat n).
    { unfold size in Hx.
      apply f_equal with (f := N.to_nat) in Hx.
      rewrite Nat2N.id in Hx. exact Hx. }
    assert (Hones_len : length (bv_not (zeros n)) = N.to_nat n).
    { unfold size in Hones_size.
      apply f_equal with (f := N.to_nat) in Hones_size.
      rewrite Nat2N.id in Hones_size. exact Hones_size. }
    assert (Hk_pos : (0 < k)%nat).
    { unfold k. eapply zeros_bv2nat_a_pos; eassumption. }
    assert (Hv_last : last (shr_n_bits x k) false = false).
    { rewrite shr_n_bits_skipn_append by lia.
      rewrite last_append.
      - apply last_mk_list_false.
      - destruct k; [lia | rewrite mk_list_false_succ; discriminate].
    }
    assert (HM_last : last (shr_n_bits (bv_not (zeros n)) k) false = false).
    { rewrite shr_n_bits_skipn_append by lia.
      rewrite last_append.
      - apply last_mk_list_false.
      - destruct k; [lia | rewrite mk_list_false_succ; discriminate].
    }
    rewrite bv_sle_ule_equiv_when_msb_zero by assumption.
    rewrite shr_n_bits_skipn_append by lia.
    rewrite shr_n_bits_skipn_append by lia.
    assert (Hones_eq : bv_not (zeros n) = mk_list_true (N.to_nat n)).
    { unfold zeros. rewrite bv_not_false_true. reflexivity. }
    rewrite Hones_eq.
    rewrite skipn_mk_list_true by lia.
    apply bv_ule_B2P.
    apply bv_uleP_post_append.
    apply bv_ule_B2P.
    assert (Hskip_len : length (skipn k x) = (N.to_nat n - k)%nat).
    { rewrite length_skipn. lia. }
    pose proof (bv_ule_1_length (skipn k x)) as Hule.
    rewrite Hskip_len in Hule.
    exact Hule.
Qed.

(* Converse of ult_b_signed_min_implies_positive_sign:
   MSB = false implies bv_ult b (signed_min n) *)
Lemma nonneg_ult_signed_min : forall (n : N) (b : bitvector),
  (0 < n)%N -> size b = n -> last b false = false ->
  bv_ult b (signed_min n) = true.
Proof.
  intros n b Hn Hb Hlast.
  destruct (bv_ult b (signed_min n)) eqn:Hult.
  - reflexivity.
  - exfalso.
    apply not_bv_ult_implies_bv_uge in Hult.
    + apply bv_uge_signed_min_implies_msb in Hult.
      * unfold bits in Hult. rewrite Hult in Hlast. discriminate.
      * exact Hb.
      * exact Hn.
    + rewrite Hb. symmetry. apply signed_min_size.
Qed.

(* Shift by zero is identity *)
Lemma bv_shr_zeros_is_self : forall (n : N) (a : bitvector),
  size a = n -> bv_shr a (zeros n) = a.
Proof.
  intros n a Ha.
  rewrite bv_shr_eq_shr_n_bits by (rewrite Ha; symmetry; apply zeros_size).
  assert (H : bv2nat_a (zeros n) = 0%nat).
  { unfold bv2nat_a, list2nat_be_a, zeros.
    rewrite list2N_mk_list_false. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* Logical right shift by a positive amount gives MSB = false *)
Lemma last_bv_shr_pos : forall (n : N) (a s : bitvector),
  size a = n -> size s = n -> (0 < bv2nat_a s)%nat ->
  last (bv_shr a s) false = false.
Proof.
  intros n a s Ha Hs Hpos.
  rewrite bv_shr_eq_shr_n_bits by (rewrite Ha; symmetry; exact Hs).
  assert (Ha_len : length a = N.to_nat n).
  { unfold size in Ha. apply f_equal with (f := N.to_nat) in Ha.
    rewrite Nat2N.id in Ha. exact Ha. }
  destruct (Nat.leb (N.to_nat n) (bv2nat_a s)) eqn:Hle.
  - apply Nat.leb_le in Hle.
    rewrite shr_n_bits_ge_length by lia.
    apply last_mk_list_false.
  - apply Nat.leb_gt in Hle.
    rewrite shr_n_bits_skipn_append by lia.
    rewrite last_append.
    + apply last_mk_list_false.
    + intro Hempty.
      apply (f_equal (@length bool)) in Hempty.
      rewrite length_mk_list_false in Hempty. simpl in Hempty. lia.
Qed.

(* If shifting t right by 0 < k < n gives zeros, then MSB of t is false *)
Lemma bv_shr_pos_zeros_implies_last_false : forall (n : N) (t s : bitvector),
  size t = n -> size s = n ->
  (0 < bv2nat_a s)%nat -> (bv2nat_a s < N.to_nat n)%nat ->
  bv_shr t s = zeros n ->
  last t false = false.
Proof.
  intros n t s Ht Hs Hpos Hlt Hshr.
  assert (Ht_len : length t = N.to_nat n).
  { unfold size in Ht. apply f_equal with (f := N.to_nat) in Ht.
    rewrite Nat2N.id in Ht. exact Ht. }
  rewrite bv_shr_eq_shr_n_bits in Hshr by (rewrite Ht; symmetry; exact Hs).
  rewrite shr_n_bits_skipn_append in Hshr by lia.
  unfold zeros in Hshr.
  assert (Hskipn : skipn (bv2nat_a s) t = mk_list_false (N.to_nat n - bv2nat_a s)).
  { apply app_inv_tail with (l := mk_list_false (bv2nat_a s)).
    rewrite Hshr. symmetry.
    rewrite <- mk_list_false_plus. f_equal. lia. }
  rewrite <- firstn_skipn with (n := bv2nat_a s) (l := t).
  rewrite last_append.
  - rewrite Hskipn. apply last_mk_list_false.
  - rewrite Hskipn.
    intro Hempty.
    apply (f_equal (@length bool)) in Hempty.
    rewrite length_mk_list_false in Hempty. simpl in Hempty. lia.
Qed.

(* For any nonempty nonzero list s, there exists k < length s such that
   left-shifting s by k positions gives signed_min of the same length *)
Lemma shl_achieves_smin_nonzero_list : forall (s : list bool),
  s <> [] ->
  list2N s <> 0%N ->
  exists k, (k < length s)%nat /\
    shl_n_bits_a s k = mk_list_false (length s - 1) ++ [true].
Proof.
  induction s as [| b s' IH].
  - intros H. contradiction.
  - intros _ Hpos.
    destruct b.
    + (* LSB = true: shift by length s' = n-1 *)
      exists (length s').
      split.
      * simpl. lia.
      * set (n' := length s').
        assert (Hlen : length (true :: s') = S n') by reflexivity.
        assert (Hlt_n : (n' <? S n')%nat = true) by (apply Nat.ltb_lt; lia).
        unfold shl_n_bits_a.
        rewrite Hlen. rewrite Hlt_n.
        assert (Hsub1 : (S n' - n' = 1)%nat).
        { rewrite Nat.sub_succ_l by exact (Nat.le_refl n').
          rewrite Nat.sub_diag. reflexivity. }
        assert (Hsub2 : (S n' - 1 = n')%nat).
        { rewrite Nat.sub_succ_r. rewrite Nat.sub_0_r. apply Nat.pred_succ. }
        rewrite Hsub1. rewrite Hsub2. simpl firstn. reflexivity.
    + (* LSB = false: use induction hypothesis *)
      assert (Hpos' : list2N s' <> 0%N).
      { intro Heq. apply Hpos. simpl. rewrite Heq. reflexivity. }
      assert (Hne' : s' <> []).
      { intro Heq. apply Hpos'. rewrite Heq. reflexivity. }
      destruct (IH Hne' Hpos') as [k' [Hk' IHres]].
      exists k'.
      split.
      * simpl. lia.
      * unfold shl_n_bits_a in *.
        assert (Hlt' : (k' <? length s')%nat = true)
          by (apply Nat.ltb_lt; exact Hk').
        assert (Hlt : (k' <? S (length s'))%nat = true)
          by (apply Nat.ltb_lt; lia).
        rewrite Hlt' in IHres.
        simpl length.
        rewrite Hlt.
        replace (S (length s') - k')%nat with (S (length s' - k'))%nat by lia.
        simpl firstn.
        assert (Hfirstn : firstn (length s' - k')%nat s' =
                          mk_list_false (length s' - 1 - k')%nat ++ [true]).
        { assert (Htmp : mk_list_false k' ++ firstn (length s' - k')%nat s' =
                         mk_list_false k' ++ (mk_list_false (length s' - 1 - k')%nat ++ [true])).
          { rewrite IHres.
            rewrite app_assoc.
            rewrite <- mk_list_false_plus.
            f_equal. f_equal. lia. }
          exact (app_inv_head _ _ _ Htmp). }
        rewrite Hfirstn.
        replace (S (length s') - 1)%nat with (length s') by lia.
        change (false :: (mk_list_false (length s' - 1 - k')%nat ++ [true])) with
          ([false] ++ mk_list_false (length s' - 1 - k')%nat ++ [true]).
        rewrite app_assoc.
        change (mk_list_false k' ++ [false]) with (mk_list_false k' ++ mk_list_false 1).
        rewrite <- mk_list_false_plus.
        rewrite app_assoc.
        rewrite <- mk_list_false_plus.
        f_equal. f_equal. lia.
Qed.

(* Any nonzero bitvector s can be left-shifted to produce signed_min n *)
Lemma nonzero_bv_shl_achieves_smin : forall (n : N) (s : bitvector),
  (0 < n)%N ->
  size s = n ->
  (0 < bv2nat_a s)%nat ->
  exists (x : bitvector), size x = n /\ bv_shl s x = signed_min n.
Proof.
  intros n s Hn Hs Hpos.
  assert (Hs_len : length s = N.to_nat n).
  { unfold size in Hs. apply f_equal with (f := N.to_nat) in Hs.
    rewrite Nat2N.id in Hs. exact Hs. }
  assert (Hne : s <> []).
  { intro Heq. rewrite Heq in Hs_len. simpl in Hs_len.
    assert (Hnn : n = 0%N).
    { apply N2Nat.inj. simpl. lia. }
    rewrite Hnn in Hn. exact (N.lt_irrefl 0%N Hn). }
  assert (Hlist2N : list2N s <> 0%N).
  { intro Heq.
    assert (Hnat0 : N.to_nat (list2N s) = 0%nat) by (rewrite Heq; reflexivity).
    apply list2N_0_implies_mlf in Hnat0.
    unfold bv2nat_a, list2nat_be_a in Hpos.
    rewrite Hnat0 in Hpos.
    rewrite Hs_len in Hpos.
    rewrite list2N_mk_list_false in Hpos.
    simpl in Hpos. lia. }
  destruct (@shl_achieves_smin_nonzero_list s Hne Hlist2N) as [k [Hk IHres]].
  exists (nat2bv k n).
  split.
  - apply nat2bv_size.
  - (* Show bv_shl s (nat2bv k n) = signed_min n *)
    unfold bv_shl, shl_aux.
    rewrite Hs. rewrite nat2bv_size. rewrite N.eqb_refl.
    unfold list2nat_be_a, bv2nat_a, bits.
    (* Show list2N (nat2bv k n) = N.of_nat k *)
    assert (Hbv2nat : list2N (nat2bv k n) = N.of_nat k).
    { unfold nat2bv.
      apply list2N_N2List_s.
      apply Nat.leb_le.
      pose proof (size_gt k) as Hsg.
      apply Nat.leb_le in Hsg.
      lia. }
    rewrite Hbv2nat.
    rewrite Nat2N.id.
    (* Now: shl_n_bits s k = signed_min n *)
    rewrite shl_n_bits_eq_shl_n_bits_a by lia.
    rewrite IHres.
    (* signed_min n = mk_list_false (length s - 1) ++ [true] *)
    unfold signed_min.
    assert (Hn_nat : (0 < N.to_nat n)%nat).
    { destruct n as [| p].
      - exfalso. exact (N.lt_irrefl 0%N Hn).
      - simpl. exact (Pos2Nat.is_pos p). }
    destruct (N.to_nat n) as [| m] eqn:Hm.
    + lia.
    + simpl smin_big_endian.
      simpl rev.
      rewrite rev_mk_list_false.
      rewrite Hs_len.
      replace (S m - 1)%nat with m%nat by lia.
      reflexivity.
Qed.

(* shl_n_bits preserves all-false lists *)
Lemma shl_n_bits_all_false : forall (l k : nat),
  shl_n_bits (mk_list_false l) k = mk_list_false l.
Proof.
  intros l k. induction k.
  - reflexivity.
  - simpl.
    assert (H : shl_one_bit (mk_list_false l) = mk_list_false l).
    { pose proof (shl_one_bit_all_false (mk_list_false l)).
      rewrite length_mk_list_false in H. exact H. }
    rewrite H. exact IHk.
Qed.

(* bv_shl of signed_min by any nonzero shift gives zeros *)
Lemma bv_shl_signed_min_nonzero : forall (n : N) (s : bitvector),
  size s = n -> (0 < bv2nat_a s)%nat ->
  bv_shl (signed_min n) s = zeros n.
Proof.
  intros n s Hs Hpos.
  assert (Hs_len : length s = N.to_nat n).
  { unfold size in Hs. apply f_equal with (f := N.to_nat) in Hs. rewrite Nat2N.id in Hs. exact Hs. }
  assert (Hn_pos : (0 < N.to_nat n)%nat).
  { destruct (N.to_nat n) as [| m].
    - exfalso. assert (s = []) by (apply length_zero_iff_nil; lia). subst.
      unfold bv2nat_a, list2nat_be_a in Hpos. simpl in Hpos. lia.
    - lia. }
  assert (H_smin_shl1 : shl_one_bit (signed_min n) = mk_list_false (N.to_nat n)).
  { unfold signed_min.
    destruct (N.to_nat n) as [| m] eqn:Hm. { lia. }
    simpl smin_big_endian. simpl rev. rewrite rev_mk_list_false.
    rewrite shl_one_b. simpl. reflexivity. }
  assert (Hsm : size (signed_min n) = n) by apply signed_min_size.
  rewrite bv_shl_eq_shl_n_bits by (rewrite Hsm; symmetry; exact Hs).
  destruct (bv2nat_a s) as [| k] eqn:Hk. { lia. }
  simpl shl_n_bits.
  rewrite H_smin_shl1.
  rewrite shl_n_bits_all_false.
  unfold zeros. reflexivity.
Qed.

(* signed_min is strictly less than everything except itself *)
Lemma bv_slt_signed_min_iff : forall (n : N) (t : bitvector),
  size t = n ->
  bv_slt (signed_min n) t = true <-> t <> signed_min n.
Proof.
  intros n t Ht.
  split.
  - intro H. intro Heq. subst t. pose proof (bv_slt_nrefl (signed_min n)) as Hnrefl. rewrite Hnrefl in H. discriminate.
  - intro Hne.
    pose proof (signed_min_sle t) as Hsle. rewrite Ht in Hsle.
    apply bv_sle_eq in Hsle.
    destruct Hsle as [H | H].
    + exact H.
    + exfalso. apply Hne. exact (eq_sym H).
Qed.

(* add_list_ingr of (t ++ [b]) with (zeros ++ [1]) flips the last bit *)
Lemma add_list_ingr_smin_flip_msb : forall (t : list bool) (b : bool),
  add_list_ingr (t ++ [b]) (mk_list_false (length t) ++ [true]) false = t ++ [negb b].
Proof.
  induction t as [| h t IH]; intro b.
  - destruct b; reflexivity.
  - simpl length. simpl mk_list_false. rewrite <- app_comm_cons.
    simpl add_list_ingr.
    destruct h; simpl; rewrite IH; reflexivity.
Qed.

(* bv_add t (signed_min n) flips the MSB of t *)
Lemma bv_add_signed_min_flip_msb : forall (n : N) (t : bitvector),
  size t = n -> (0 < n)%N ->
  bv_add t (signed_min n) = removelast t ++ [negb (last t false)].
Proof.
  intros n t Ht Hn.
  assert (Hsm : size (signed_min n) = n) by apply signed_min_size.
  assert (Ht_len : length t = N.to_nat n).
  { unfold size in Ht. apply f_equal with (f := N.to_nat) in Ht. rewrite Nat2N.id in Ht. exact Ht. }
  assert (Hn_pos : (0 < N.to_nat n)%nat).
  { destruct n as [| p]. { exfalso. exact (N.lt_irrefl 0 Hn). } simpl. exact (Pos2Nat.is_pos p). }
  assert (Ht_ne : t <> []).
  { intro Heq. subst t. cbn in Ht_len. lia. }
  assert (H_smin : signed_min n = mk_list_false (N.to_nat n - 1) ++ [true]).
  { unfold signed_min.
    destruct (N.to_nat n) as [| m] eqn:Hm. { lia. }
    simpl smin_big_endian. simpl rev. rewrite rev_mk_list_false.
    f_equal. f_equal. lia. }
  assert (Hrlen : length (removelast t) = (N.to_nat n - 1)%nat).
  { rewrite (app_removelast_last false Ht_ne) in Ht_len.
    rewrite length_app in Ht_len. simpl in Ht_len. lia. }
  unfold bv_add.
  rewrite Ht. rewrite Hsm. rewrite N.eqb_refl.
  unfold add_list.
  rewrite H_smin.
  rewrite <- Hrlen.
  rewrite (app_removelast_last false Ht_ne) at 1.
  exact (add_list_ingr_smin_flip_msb (removelast t) (last t false)).
Qed.

(* Cancelling the same appended bit in bv_ult *)
Lemma ult_list_be_cancel_head : forall (a b : list bool) (x : bool),
  ult_list_big_endian (x :: a) (x :: b) = ult_list_big_endian a b.
Proof.
  intros a b x.
  destruct a as [| ha ta]; destruct b as [| hb tb];
    simpl; try rewrite Bool.eqb_reflx; simpl;
    destruct x; simpl; try rewrite Bool.orb_false_r; reflexivity.
Qed.

Lemma bv_ult_cancel_app : forall (a b : list bool) (x : bool),
  length a = length b ->
  bv_ult (a ++ [x]) (b ++ [x]) = bv_ult a b.
Proof.
  intros a b x Hlen.
  unfold bv_ult, ult_list.
  assert (Hsize : (size (a ++ [x]) =? size (b ++ [x])) = true).
  { unfold size. rewrite !length_app. simpl. rewrite Hlen. apply N.eqb_refl. }
  assert (Hsizab : (size a =? size b) = true).
  { unfold size. rewrite Hlen. apply N.eqb_refl. }
  rewrite Hsize. rewrite Hsizab.
  rewrite !rev_app_distr. simpl rev.
  exact (ult_list_be_cancel_head (rev a) (rev b) x).
Qed.

(* ult_list_be with true::_ vs false::_ is always false *)
Lemma ult_list_be_true_false_head : forall (a b : list bool),
  ult_list_big_endian (true :: a) (false :: b) = false.
Proof.
  intros a b. destruct a; destruct b; reflexivity.
Qed.

(* bv_ult (signed_min n) (bv_add t (signed_min n)) = bv_slt (zeros n) t *)
Lemma bv_ult_smin_add_smin_eq_slt_zeros : forall (n : N) (t : bitvector),
  size t = n -> (0 < n)%N ->
  bv_ult (signed_min n) (bv_add t (signed_min n)) = bv_slt (zeros n) t.
Proof.
  intros n t Ht Hn.
  rewrite bv_add_signed_min_flip_msb by assumption.
  assert (H_smin : signed_min n = mk_list_false (N.to_nat n - 1) ++ [true]).
  { unfold signed_min.
    assert (Hn_pos : (0 < N.to_nat n)%nat).
    { destruct n as [| p]. { exfalso. exact (N.lt_irrefl 0 Hn). } simpl. exact (Pos2Nat.is_pos p). }
    destruct (N.to_nat n) as [| m] eqn:Hm. { lia. }
    simpl smin_big_endian. simpl rev. rewrite rev_mk_list_false.
    f_equal. f_equal. lia. }
  assert (H_zeros : zeros n = mk_list_false (N.to_nat n - 1) ++ [false]).
  { unfold zeros.
    assert (Hn_pos : (0 < N.to_nat n)%nat).
    { destruct n as [| p]. { exfalso. exact (N.lt_irrefl 0 Hn). } simpl. exact (Pos2Nat.is_pos p). }
    rewrite <- (Nat.succ_pred_pos (N.to_nat n) Hn_pos) at 1.
    assert (Hpred : (N.to_nat n - 1)%nat = Nat.pred (N.to_nat n)) by lia.
    rewrite Hpred. apply mk_list_false_app. }
  assert (Ht_len : length t = N.to_nat n).
  { unfold size in Ht. apply f_equal with (f := N.to_nat) in Ht. rewrite Nat2N.id in Ht. exact Ht. }
  assert (Hrlen : length (removelast t) = (N.to_nat n - 1)%nat).
  { destruct t as [| h tl].
    - unfold size in Ht. simpl in Ht. rewrite <- Ht in Hn. exfalso. exact (N.lt_irrefl 0 Hn).
    - assert (Hne : h :: tl <> []) by discriminate.
      rewrite (app_removelast_last false Hne) in Ht_len.
      rewrite length_app in Ht_len. cbn [length] in Ht_len. lia. }
  rewrite H_smin. rewrite H_zeros.
  assert (Ht_ne : t <> []).
  { intro Heq. subst t. cbn in Ht_len.
    assert (Hn_pos : (0 < N.to_nat n)%nat).
    { destruct n as [| p]. { exfalso. exact (N.lt_irrefl 0 Hn). } simpl. exact (Pos2Nat.is_pos p). }
    lia. }
  destruct (last t false) eqn:Hlast.
  - (* last t = true: LHS = false, RHS = false *)
    simpl negb.
    assert (HLHS : bv_ult (mk_list_false (N.to_nat n - 1) ++ [true]) (removelast t ++ [false]) = false).
    { unfold bv_ult, ult_list.
      assert (Hsz : (size (mk_list_false (N.to_nat n - 1) ++ [true]) =? size (removelast t ++ [false])) = true).
      { unfold size. rewrite !length_app. cbn [length]. rewrite length_mk_list_false. rewrite Hrlen. apply N.eqb_refl. }
      rewrite Hsz. rewrite !rev_app_distr. simpl rev. apply ult_list_be_true_false_head. }
    rewrite HLHS.
    assert (HRHS : bv_slt (mk_list_false (N.to_nat n - 1) ++ [false]) t = false).
    { apply Bool.not_true_is_false. intro Habs.
      assert (Hback : bv_slt t (mk_list_false (N.to_nat n - 1) ++ [false]) = true).
      { apply bv_slt_tf.
        - unfold size. rewrite Ht_len. rewrite length_app. cbn [length]. rewrite length_mk_list_false.
          f_equal. lia.
        - exact Hlast.
        - apply last_app. }
      pose proof (bv_slt_trans Habs Hback) as Htrans.
      pose proof (bv_slt_nrefl (mk_list_false (N.to_nat n - 1) ++ [false])) as Hnrefl.
      rewrite Hnrefl in Htrans. discriminate. }
    rewrite HRHS. reflexivity.
  - (* last t = false: both sides equal bv_ult (mk_list_false ..) (removelast t) *)
    simpl negb.
    rewrite bv_ult_cancel_app by (rewrite length_mk_list_false; exact (eq_sym Hrlen)).
    assert (Hlast_eq : last (mk_list_false (N.to_nat n - 1) ++ [false]) false = last t false).
    { rewrite last_app. exact (eq_sym Hlast). }
    rewrite (bv_slt_ult_last_eq Hlast_eq).
    rewrite (app_removelast_last false Ht_ne) at 2.
    rewrite Hlast.
    rewrite bv_ult_cancel_app by (rewrite length_mk_list_false; exact (eq_sym Hrlen)).
    reflexivity.
Qed.

Lemma size_to_length : forall (n : N) (v : bitvector),
  size v = n -> length v = N.to_nat n.
Proof.
  intros n v Hv.
  unfold size in Hv. apply f_equal with (f := N.to_nat) in Hv. rewrite Nat2N.id in Hv. exact Hv.
Qed.

Lemma n_pos_of_bv2nat_a_pos : forall (n : N) (v : bitvector),
  size v = n -> (0 < bv2nat_a v)%nat -> (0 < n)%N.
Proof.
  intros n v Hv Hpos.
  destruct n as [| p].
  - exfalso.
    pose proof (size_to_length Hv) as Hlen. simpl in Hlen.
    apply length_zero_iff_nil in Hlen. subst v.
    unfold bv2nat_a, list2nat_be_a in Hpos. simpl in Hpos. lia.
  - lia.
Qed.

Lemma bv2nat_a_zero_eq_zeros : forall (n : N) (v : bitvector),
  size v = n -> bv2nat_a v = 0%nat -> v = zeros n.
Proof.
  intros n v Hv H0.
  unfold bv2nat_a, list2nat_be_a in H0.
  apply list2N_0_implies_mlf in H0.
  assert (Hv_len : length v = N.to_nat n).
  { unfold size in Hv. apply f_equal with (f := N.to_nat) in Hv. rewrite Nat2N.id in Hv. exact Hv. }
  unfold zeros. rewrite <- Hv_len. exact H0.
Qed.

Lemma signed_min_struct : forall (n : N),
  (0 < n)%N -> signed_min n = mk_list_false (N.to_nat n - 1) ++ [true].
Proof.
  intros n Hn. unfold signed_min.
  assert (Hn_pos : (0 < N.to_nat n)%nat).
  { destruct n as [| p]. { exfalso. exact (N.lt_irrefl 0 Hn). } simpl. exact (Pos2Nat.is_pos p). }
  destruct (N.to_nat n) as [| k] eqn:Hk. { lia. }
  simpl smin_big_endian. simpl rev. rewrite rev_mk_list_false.
  f_equal. f_equal. lia.
Qed.

Lemma bv_add_smin_smin_eq_zeros : forall (n : N),
  (0 < n)%N -> bv_add (signed_min n) (signed_min n) = zeros n.
Proof.
  intros n Hn.
  rewrite (bv_add_signed_min_flip_msb (signed_min_size n) Hn).
  rewrite (last_signed_min Hn). simpl negb.
  rewrite (signed_min_struct Hn). rewrite removelast_last.
  unfold zeros.
  assert (Hn_pos : (0 < N.to_nat n)%nat).
  { destruct n as [| p]. { exact (False_ind _ (N.lt_irrefl 0 Hn)). } simpl. exact (Pos2Nat.is_pos p). }
  destruct (N.to_nat n) as [| k] eqn:Hk. { lia. }
  simpl. rewrite Nat.sub_0_r. symmetry. apply mk_list_false_app.
Qed.

Lemma bv_add_t_smin_ne_zeros : forall (n : N) (t : bitvector),
  (0 < n)%N -> size t = n -> t <> signed_min n ->
  bv_add t (signed_min n) <> zeros n.
Proof.
  intros n t Hn Ht Hne H.
  rewrite (bv_add_signed_min_flip_msb Ht Hn) in H.
  assert (Ht_len : length t = N.to_nat n).
  { unfold size in Ht. apply f_equal with (f := N.to_nat) in Ht. rewrite Nat2N.id in Ht. exact Ht. }
  assert (Hlast_t : last t false = true).
  { pose proof (last_app (removelast t) (negb (last t false)) false) as Heq.
    rewrite H in Heq. unfold zeros in Heq. rewrite last_mk_list_false in Heq.
    destruct (last t false); [reflexivity | simpl negb in Heq; discriminate]. }
  rewrite Hlast_t in H. simpl negb in H.
  assert (Hmkf : zeros n = mk_list_false (N.to_nat n - 1) ++ (false :: nil)).
  { unfold zeros.
    assert (Hn_pos : (0 < N.to_nat n)%nat).
    { destruct n as [| p]. { exact (False_ind _ (N.lt_irrefl 0 Hn)). } simpl. exact (Pos2Nat.is_pos p). }
    destruct (N.to_nat n) as [| k] eqn:Hk. { lia. }
    simpl. rewrite Nat.sub_0_r. apply mk_list_false_app. }
  rewrite Hmkf in H.
  assert (Hrl : removelast t = mk_list_false (N.to_nat n - 1)).
  { exact (app_inv_tail (false :: nil) (removelast t) (mk_list_false (N.to_nat n - 1)) H). }
  assert (Hn_pos : (0 < N.to_nat n)%nat).
  { destruct n as [| p]. { exact (False_ind _ (N.lt_irrefl 0 Hn)). } simpl. exact (Pos2Nat.is_pos p). }
  assert (Ht_ne : t <> nil) by (intro Heq; subst t; simpl in Ht_len; lia).
  pose proof (app_removelast_last false Ht_ne) as Ht_split.
  rewrite Hlast_t, Hrl in Ht_split.
  apply Hne. rewrite Ht_split. symmetry. apply signed_min_struct. exact Hn.
Qed.

(* last s = false → bv_and s (signed_max n) = s *)
Lemma bv_and_nonneg_smax_eq : forall (n : N) (s : bitvector),
  size s = n -> last s false = false ->
  bv_and s (signed_max n) = s.
Proof.
  intros n s Hn_s Hs_sign.
  destruct (N.to_nat n) as [| t'] eqn:Hn_nat.
  - assert (s = nil). { apply length_zero_iff_nil. unfold size in Hn_s. lia. }
    subst. unfold signed_max, smax_big_endian. rewrite Hn_nat. simpl. reflexivity.
  - assert (Hs_not_nil: s <> nil).
    { intro Hs_nil. rewrite Hs_nil in Hn_s. rewrite <- Hn_s in Hn_nat. discriminate. }
    unfold bv_and.
    rewrite Hn_s, signed_max_size. rewrite N.eqb_refl.
    unfold signed_max, smax_big_endian. rewrite Hn_nat. simpl rev. rewrite rev_mk_list_true.
    unfold bits.
    assert (Hlen : length s = S t').
    { unfold size in Hn_s. rewrite <- Hn_s in Hn_nat. rewrite Nat2N.id in Hn_nat. exact Hn_nat. }
    rewrite (app_removelast_last false Hs_not_nil) at 1. rewrite Hs_sign.
    assert (Hrl : length (removelast s) = t').
    { rewrite removelast_firstn_len. rewrite length_firstn. rewrite Hlen. simpl. apply Nat.min_l. lia. }
    rewrite map2_and_app.
    + simpl (map2 andb (false :: nil) (false :: nil)).
      rewrite <- Hrl. rewrite map2_and_1_neutral.
      symmetry. rewrite <- Hs_sign. exact (app_removelast_last false Hs_not_nil).
    + rewrite length_mk_list_true. exact Hrl.
    + easy.
Qed.

(* last s = true → bv_or s (signed_max n) = ones n *)
Lemma bv_or_neg_smax_ones : forall (n : N) (s : bitvector),
  size s = n -> last s false = true ->
  bv_or s (signed_max n) = ones n.
Proof.
  intros n s Hn_s Hs_sign.
  assert (Hs_not_nil: s <> nil).
  { intro H. subst. simpl in Hs_sign. discriminate. }
  destruct (N.to_nat n) as [| t'] eqn:Hn_nat.
  - exfalso. apply Hs_not_nil. apply length_zero_iff_nil. unfold size in Hn_s. lia.
  - unfold bv_or.
    rewrite Hn_s, signed_max_size. rewrite N.eqb_refl.
    unfold signed_max, smax_big_endian. rewrite Hn_nat. simpl rev. rewrite rev_mk_list_true.
    unfold bits.
    assert (Hlen : length s = S t').
    { unfold size in Hn_s. rewrite <- Hn_s in Hn_nat. rewrite Nat2N.id in Hn_nat. exact Hn_nat. }
    rewrite (app_removelast_last false Hs_not_nil) at 1. rewrite Hs_sign.
    assert (Hrl : length (removelast s) = t').
    { rewrite removelast_firstn_len. rewrite length_firstn. rewrite Hlen. simpl. apply Nat.min_l. lia. }
    rewrite map2_or_app.
    + simpl (map2 orb (true :: nil) (false :: nil)).
      rewrite <- Hrl. rewrite map2_or_1_true. rewrite Hrl.
      unfold ones. rewrite Hn_nat. symmetry. apply mk_list_true_app.
    + rewrite length_mk_list_true. exact Hrl.
    + easy.
Qed.

(* ===== Helper lemmas for bvand_sge ===== *)

(* borrow-subtract single bit equals add with negated b and negated carry *)
Lemma subst_borrow_carry_inv : forall b1 b2 b,
  let (r, c) := subst_borrow b1 b2 b in
  add_carry b1 (negb b2) (negb b) = (r, negb c).
Proof. destruct b1; destruct b2; destruct b; reflexivity. Qed.

(* subst_list_borrow equals add_list_ingr with negated mask and negated carry-in *)
Lemma subst_list_borrow_eq_add_ingr : forall a b c,
  length a = length b ->
  subst_list_borrow a b c = add_list_ingr a (map negb b) (negb c).
Proof.
  induction a as [| a1 as1 IH]; intros b c Hlen.
  - destruct b; simpl; reflexivity.
  - destruct b as [| b1 bs]; [discriminate Hlen |].
    simpl in Hlen. injection Hlen as Hlen.
    simpl subst_list_borrow. simpl add_list_ingr.
    pose proof (subst_borrow_carry_inv a1 b1 c) as Hinv.
    destruct (subst_borrow a1 b1 c) as [r c'] eqn:Hbc.
    rewrite Hinv. f_equal.
    exact (IH bs c' Hlen).
Qed.

(* list2int a + list2int (~a) = 2^n - 1 *)
Lemma list2int_map_negb_sum : forall b,
  (list2int b + list2int (map negb b) = pow2_int (length b) - 1)%Z.
Proof.
  induction b as [| h t IH].
  - reflexivity.
  - rewrite !list2int_cons. simpl (map negb (h :: t)).
    rewrite list2int_cons. simpl length. rewrite pow2_int_succ.
    destruct h; simpl bool2int; lia.
Qed.

(* Integer formula for borrow subtraction: (a - b + 2^n) mod 2^n *)
Lemma list2int_subst_list_formula : forall a b,
  length a = length b ->
  (list2int (subst_list a b) =
   (list2int a - list2int b + pow2_int (length a)) mod pow2_int (length a))%Z.
Proof.
  intros a b Hlen.
  unfold subst_list.
  rewrite (@subst_list_borrow_eq_add_ingr a b false Hlen).
  simpl negb.
  rewrite list2int_add_list_ingr; [| now rewrite length_map].
  simpl bool2int.
  pose proof (list2int_map_negb_sum b) as Hsum.
  replace (list2int (map negb b)) with (pow2_int (length b) - 1 - list2int b)%Z by lia.
  rewrite <- Hlen. f_equal. lia.
Qed.

(* Bitwise inclusion-exclusion: list2int(a&b) + list2int(a|b) = list2int a + list2int b *)
Lemma list2int_map2_and_or_sum : forall a b,
  length a = length b ->
  (list2int (map2 andb a b) + list2int (map2 orb a b) = list2int a + list2int b)%Z.
Proof.
  induction a as [| a1 as1 IH]; intros b Hlen.
  - destruct b; [simpl; lia | discriminate Hlen].
  - destruct b as [| b1 bs]; [discriminate Hlen |].
    simpl in Hlen. injection Hlen as Hlen.
    simpl (map2 andb (a1 :: as1) (b1 :: bs)).
    simpl (map2 orb (a1 :: as1) (b1 :: bs)).
    rewrite !list2int_cons.
    pose proof (IH bs Hlen) as IH'.
    destruct a1; destruct b1; simpl bool2int; lia.
Qed.

(* ule_list implies list2int ≤ *)
Lemma ule_list_list2int : forall x y,
  length x = length y ->
  ule_list x y = true ->
  (list2int x <= list2int y)%Z.
Proof.
  intros x y Hlen H.
  unfold ule_list in H.
  apply ule_list_big_endian_implies_ult_list_big_endian_or_eq in H.
  destruct H as [H | H].
  - apply Z.lt_le_incl.
    assert (Hlenr : length (rev x) = length (rev y)) by (now rewrite !length_rev).
    apply ult_list_big_endian_list2int in H; [| exact Hlenr].
    now rewrite !rev_involutive in H.
  - apply rev_inj in H. subst. lia.
Qed.

(* bv_ult a b = false implies list2int b ≤ list2int a *)
Lemma bv_ult_false_list2int_ge : forall a b,
  size a = size b ->
  bv_ult a b = false ->
  (list2int b <= list2int a)%Z.
Proof.
  intros a b Hsize Hult.
  pose proof (not_bv_ult_implies_bv_uge Hsize Hult) as Huge.
  apply bv_uge_eq in Huge.
  destruct Huge as [Hugt | Heq].
  - apply Z.lt_le_incl.
    apply bv_ugt_bv_ult in Hugt.
    apply ult_list_list2int.
    + apply size_len_eq. now rewrite Hsize.
    + unfold bv_ult in Hugt. rewrite Hsize, N.eqb_refl in Hugt. exact Hugt.
  - subst. lia.
Qed.

(* last v = true implies list2int v >= 2^(length v - 1) *)
Lemma last_true_list2int_lb : forall v,
  v <> [] ->
  last v false = true ->
  (pow2_int (length v - 1) <= list2int v)%Z.
Proof.
  intros v Hne Hlast.
  pose proof (app_removelast_last false Hne) as Hdecomp.
  pose proof (f_equal (@length bool) Hdecomp) as Hlen_eq.
  rewrite length_app in Hlen_eq. simpl in Hlen_eq.
  rewrite Hlast in Hdecomp.
  rewrite Hdecomp.
  rewrite list2int_app. simpl list2int. simpl bool2int. rewrite Z.mul_1_r.
  rewrite length_app. simpl length. rewrite Nat.add_sub.
  pose proof (@list2int_geq_zero (removelast v)) as Hge. lia.
Qed.

(* If a non-neg (last=false) and b neg (last=true): list2int(a&b) <= list2int b - 2^(n-1) *)
Lemma last_false_and_true_submask_bound : forall a b,
  length a = length b ->
  last a false = false ->
  last b false = true ->
  (list2int (map2 andb a b) <= list2int b - pow2_int (length b - 1))%Z.
Proof.
  intros a b Hlen Ha_last Hb_last.
  assert (Hb_ne : b <> []).
  { intro H. subst. simpl in Hb_last. discriminate. }
  assert (Ha_ne : a <> []).
  { intro H. subst. destruct b; [exact (Hb_ne eq_refl) | discriminate Hlen]. }
  pose proof (app_removelast_last false Ha_ne) as Ha_decomp. rewrite Ha_last in Ha_decomp.
  pose proof (app_removelast_last false Hb_ne) as Hb_decomp. rewrite Hb_last in Hb_decomp.
  set (ia := removelast a). set (ib := removelast b).
  assert (Hia_len : length ia = pred (length a)).
  { unfold ia. apply (f_equal (@length bool)) in Ha_decomp.
    rewrite length_app in Ha_decomp. simpl in Ha_decomp. lia. }
  assert (Hib_len : length ib = pred (length b)).
  { unfold ib. apply (f_equal (@length bool)) in Hb_decomp.
    rewrite length_app in Hb_decomp. simpl in Hb_decomp. lia. }
  assert (Hlen_iab : length ia = length ib) by lia.
  assert (Hle_and_ib : (list2int (map2 andb ia ib) <= list2int ib)%Z).
  { apply ule_list_list2int.
    - pose proof (map2_and_length Hlen_iab) as Hmap2_len. lia.
    - rewrite map2_and_comm. apply ule_list_map2_and. lia. }
  assert (Hb_int : (list2int b = list2int ib + pow2_int (length ib))%Z).
  { rewrite Hb_decomp, list2int_app, list2int_bool.
    change (bool2int true) with 1%Z. rewrite Z.mul_1_r. apply Z.add_comm. }
  assert (Handb_int : (list2int (map2 andb a b) = list2int (map2 andb ia ib))%Z).
  { rewrite Ha_decomp, Hb_decomp.
    rewrite map2_and_app; [| exact Hlen_iab | easy].
    simpl (map2 andb [false] [true]).
    rewrite list2int_app, list2int_bool.
    change (bool2int false) with 0%Z. rewrite Z.mul_0_r. rewrite Z.add_0_l. reflexivity. }
  assert (Hpow : pow2_int (length b - 1) = pow2_int (length ib)).
  { f_equal. lia. }
  lia.
Qed.

(* Key lemma for bvand_sge backward direction *)
Lemma bvand_sge_key : forall (n : N) (s t x : bitvector),
  size s = n -> size t = n -> size x = n ->
  bv_slt t (bv_and x s) = true ->
  bv_and s t = t \/ bv_slt t (bv_and (bv_subt t s) s) = true.
Proof.
  intros n s t x Hs Ht Hx Hslt.
  pose proof (@bv_and_size n x s Hx Hs) as Hxs_sz.
  pose proof (@bv_subt_size n t s Ht Hs) as HD_sz.
  pose proof (@bv_and_size n (bv_subt t s) s HD_sz Hs) as HDs_sz.
  pose proof (@size_to_length n s Hs) as Hlen_s.
  pose proof (@size_to_length n t Ht) as Hlen_t.
  pose proof (@size_to_length n x Hx) as Hlen_x.
  pose proof (@size_to_length n (bv_and x s) Hxs_sz) as Hlen_xs.
  pose proof (@size_to_length n (bv_subt t s) HD_sz) as Hlen_D.
  pose proof (@size_to_length n (bv_and (bv_subt t s) s) HDs_sz) as Hlen_Ds.
  rewrite (@bv_slt_iff_sbv2int n t (bv_and x s) Ht Hxs_sz) in Hslt.
  right.
  rewrite (@bv_slt_iff_sbv2int n t (bv_and (bv_subt t s) s) Ht HDs_sz).
  (* Work with unfolded sbv2int *)
  unfold sbv2int in *.
  set (T := bv2int t). set (M := bv2int (bv_and x s)).
  set (S := bv2int s). set (D := bv2int (bv_subt t s)).
  set (Ds := bv2int (bv_and (bv_subt t s) s)).
  set (P := pow2_int_N n).
  (* Key: bv2int = list2int *)
  unfold bv2int in *. fold T M S D Ds P.
  (* Unfold bv operations to list operations *)
  assert (HT_eq : T = list2int t) by (unfold T; reflexivity).
  assert (HM_eq : M = list2int (bv_and x s)) by (unfold M; reflexivity).
  assert (HS_eq : S = list2int s) by (unfold S; reflexivity).
  assert (HD_eq : D = list2int (bv_subt t s)) by (unfold D; reflexivity).
  assert (HDs_eq : Ds = list2int (bv_and (bv_subt t s) s)) by (unfold Ds; reflexivity).
  (* P = pow2_int (N.to_nat n) = pow2_int (length t) *)
  assert (HP_eq : P = pow2_int (length t)) by (unfold P, pow2_int_N; now rewrite Hlen_t).
  (* bv_and x s: unfold to map2 andb *)
  assert (HM_and : list2int (bv_and x s) = list2int (map2 andb x s)).
  { unfold bv_and. rewrite Hx, Hs, N.eqb_refl. unfold bits. reflexivity. }
  assert (HDs_and : list2int (bv_and (bv_subt t s) s) = list2int (map2 andb (subst_list t s) s)).
  { unfold bv_and. rewrite HD_sz, Hs, N.eqb_refl. unfold bits.
    unfold bv_subt. rewrite Ht, Hs, N.eqb_refl. reflexivity. }
  (* subst_list t s integer formula *)
  assert (HLen_ts : length t = length s) by (rewrite Hlen_t, Hlen_s; reflexivity).
  pose proof (@list2int_subst_list_formula t s HLen_ts) as HDform.
  (* Key: list2int s <= list2int (mk_list_true...) = 2^n - 1 *)
  pose proof (@list2int_lt_pow2_int s (length s) eq_refl) as HS_ub.
  pose proof (@list2int_lt_pow2_int t (length t) eq_refl) as HT_ub.
  pose proof (@list2int_geq_zero s) as HS_lb.
  pose proof (@list2int_geq_zero t) as HT_lb.
  (* bv_and x s <=u s *)
  assert (Hlen_xs_eq : length x = length s) by (rewrite Hlen_x, Hlen_s; reflexivity).
  assert (HMleS : (list2int (map2 andb x s) <= list2int s)%Z).
  { apply ule_list_list2int.
    - pose proof (@map2_and_length x s Hlen_xs_eq) as Hml. lia.
    - rewrite map2_and_comm. apply (@ule_list_map2_and s x). lia. }
  (* bv_and Ds s <=u s *)
  assert (HDsleS : (list2int (map2 andb (subst_list t s) s) <= list2int s)%Z).
  { assert (HDs_len : length (subst_list t s) = length s).
    { pose proof (@subst_list_length t s HLen_ts). lia. }
    apply ule_list_list2int.
    - pose proof (@map2_and_length (subst_list t s) s HDs_len) as Hml. lia.
    - rewrite map2_and_comm. apply (@ule_list_map2_and s (subst_list t s)). lia. }
  (* Case split on bv_ult t s *)
  destruct (bv_ult t s) eqn:Hult_ts.
  - (* t <u s: list2int t < list2int s *)
    assert (HT_lt_S : (list2int t < list2int s)%Z).
    { apply ult_list_list2int; [rewrite Hlen_t, Hlen_s; reflexivity |].
      unfold bv_ult in Hult_ts. rewrite Ht, Hs, N.eqb_refl in Hult_ts. exact Hult_ts. }
    (* D formula: (T - S + P) mod P, no wrap since T < S *)
    assert (HD_val : (list2int (subst_list t s) = list2int t - list2int s + pow2_int (length t))%Z).
    { rewrite HDform. apply Z.mod_small.
      split; [rewrite HLen_ts; lia |]. lia. }
    (* Inclusion-exclusion for map2 andb (subst_list t s) s *)
    assert (HIE : length (subst_list t s) = length s).
    { pose proof (@subst_list_length t s HLen_ts). lia. }
    pose proof (@list2int_map2_and_or_sum (subst_list t s) s HIE) as Hincl.
    pose proof (@list2int_lt_pow2_int (map2 orb (subst_list t s) s)
                  (length (map2 orb (subst_list t s) s)) eq_refl) as Hor_ub.
    rewrite <- (@map2_or_length (subst_list t s) s HIE) in Hor_ub.
    rewrite HIE, Hlen_s, <- Hlen_t in Hor_ub. rewrite <- HP_eq in Hor_ub.
    (* list2int (Ds) >= list2int t + 1 *)
    assert (HDs_lb : (list2int (map2 andb (subst_list t s) s) >= list2int t + 1)%Z).
    { rewrite HD_val in Hincl. lia. }
    (* Now case split on signs of t and bv_and (bv_subt t s) s *)
    destruct (last t false) eqn:Ht_sign;
    destruct (last (bv_and (bv_subt t s) s) false) eqn:HDs_sign.
    + (* t neg, Ds neg: sbv2int = list2int - P *)
      lia.
    + (* t neg, Ds non-neg: 0 > t_signed, Ds_signed >= 0 *)
      pose proof (@list2int_geq_zero (bv_and (bv_subt t s) s)) as HDs_ge.
      rewrite HP_eq.
      assert (Ht_neg : (pow2_int (length t - 1) <= list2int t)%Z).
      { apply last_true_list2int_lb.
        - intro H. subst t. simpl in Ht_sign. discriminate.
        - exact Ht_sign. }
      lia.
    + (* t non-neg, Ds neg: contradiction *)
      exfalso.
      (* t non-neg: sbv2int t = T *)
      (* Ds neg means last(bv_and D s) = true, so last D = true and last s = true *)
      assert (HDs_last_raw : last (map2 andb (subst_list t s) s) false = true).
      { unfold bv_and in HDs_sign. rewrite HD_sz, Hs, N.eqb_refl in HDs_sign.
        unfold bv_subt in HDs_sign. rewrite Ht, Hs, N.eqb_refl in HDs_sign.
        unfold bits in HDs_sign. exact HDs_sign. }
      assert (HIElast : length (subst_list t s) = length s) by exact HIE.
      assert (HDs_ne : map2 andb (subst_list t s) s <> []).
      { intro H. rewrite H in HDs_last_raw. simpl in HDs_last_raw. discriminate. }
      assert (HD_last_true : last (subst_list t s) false = true).
      { rewrite <- hd_rev in HDs_last_raw.
        rewrite rev_map2_and in HDs_last_raw; [| exact HIE].
        unfold bits in *.
        destruct (rev (subst_list t s)) as [| hd1 tl1] eqn:Hrx.
        - apply (f_equal (@length bool)) in Hrx. rewrite length_rev in Hrx.
          exfalso. apply HDs_ne.
          assert (HD_nil : subst_list t s = []) by (apply length_zero_iff_nil; exact Hrx).
          rewrite HD_nil. reflexivity.
        - destruct (rev s) as [| hd2 tl2] eqn:Hry.
          + apply (f_equal (@length bool)) in Hry. rewrite length_rev in Hry.
            exfalso. apply HDs_ne.
            assert (HD_nil : subst_list t s = []) by (apply length_zero_iff_nil; rewrite HIE; exact Hry).
            rewrite HD_nil. reflexivity.
          + simpl in HDs_last_raw.
            rewrite andb_true_iff in HDs_last_raw. destruct HDs_last_raw as [H1 _].
            rewrite <- hd_rev. rewrite Hrx. simpl. exact H1. }
      assert (Hs_last_true : last s false = true).
      { rewrite <- hd_rev in HDs_last_raw.
        rewrite rev_map2_and in HDs_last_raw; [| exact HIE].
        unfold bits in *.
        destruct (rev s) as [| hd2 tl2] eqn:Hry.
        - apply (f_equal (@length bool)) in Hry. rewrite length_rev in Hry.
          exfalso. apply HDs_ne.
          assert (HD_nil : subst_list t s = []) by (apply length_zero_iff_nil; rewrite HIE; exact Hry).
          rewrite HD_nil. reflexivity.
        - destruct (rev (subst_list t s)) as [| hd1 tl1] eqn:Hrx.
          + apply (f_equal (@length bool)) in Hrx. rewrite length_rev in Hrx.
            exfalso. apply HDs_ne.
            assert (HD_nil : subst_list t s = []) by (apply length_zero_iff_nil; exact Hrx).
            rewrite HD_nil. reflexivity.
          + simpl in HDs_last_raw.
            rewrite andb_true_iff in HDs_last_raw. destruct HDs_last_raw as [_ H2].
            rewrite <- hd_rev. rewrite Hry. simpl. exact H2. }
      (* last D = true means list2int D >= 2^(n-1) *)
      assert (HD_ne : subst_list t s <> []).
      { intro H. apply HDs_ne. rewrite H. reflexivity. }
      assert (HD_last_lb : (pow2_int (length s - 1) <= list2int (subst_list t s))%Z).
      { pose proof (last_true_list2int_lb HD_ne HD_last_true) as Hlb.
        rewrite HIE in Hlb. exact Hlb. }
      assert (Hpow_double : (pow2_int (length s) = 2 * pow2_int (length s - 1))%Z).
      { assert (Hs_ne' : s <> [])
          by (intro H; rewrite H in Hs_last_true; simpl in Hs_last_true; discriminate).
        destruct s as [| h tl]; [exact (False_ind _ (Hs_ne' eq_refl)) |].
        simpl length.
        rewrite Nat.sub_succ_r, Nat.sub_0_r, Nat.pred_succ.
        apply pow2_int_succ. }
      assert (Hpow_ts : (pow2_int (length t) = pow2_int (length s))%Z).
      { f_equal. exact HLen_ts. }
      rewrite HD_val in HD_last_lb.
      (* T - S + 2^n >= 2^(n-1) => T >= S - 2^(n-1) *)
      assert (HT_ge : (list2int t >= list2int s - pow2_int (length s - 1))%Z) by lia.
      (* s negative, x non-negative: list2int(bv_and x s) <= S - 2^(n-1) *)
      assert (Hx_last_false : last x false = false).
      { (* bv_and x s non-negative (from hypothesis sbv2int > T >= 0) *)
        (* If last x = true, then last(bv_and x s) = last x && last s = true && true = true *)
        (* So bv_and x s would be negative, contradicting hypothesis *)
        destruct (last x false) eqn:Hx_sign; [| reflexivity].
        exfalso.
        assert (Hxs_neg : last (bv_and x s) false = true).
        { exact (@neg_bvand_neg x s n Hx Hs Hx_sign Hs_last_true). }
        rewrite Hxs_neg in Hslt.
        pose proof (@list2int_lt_pow2_int (bv_and x s) (N.to_nat n) Hlen_xs) as Hub.
        unfold pow2_int_N in Hslt. lia. }
      assert (HMleS' : (list2int (map2 andb x s) <= list2int s - pow2_int (length s - 1))%Z).
      { apply last_false_and_true_submask_bound.
        - lia.
        - exact Hx_last_false.
        - exact Hs_last_true. }
      assert (Hxs_pos : last (bv_and x s) false = false).
      { exact (@pos_bvand_pos x s n Hx Hs Hx_last_false). }
      rewrite Hxs_pos in Hslt.
      lia.
    + (* t non-neg, Ds non-neg: list2int t < list2int Ds *)
      lia.
  - (* t >=u s *)
    (* Show t must be negative *)
    assert (HT_ge_S : (list2int s <= list2int t)%Z).
    { apply bv_ult_false_list2int_ge; [rewrite Ht, Hs; reflexivity | exact Hult_ts]. }
    assert (Ht_neg : last t false = true).
    { destruct (last t false) eqn:Ht_sign; [reflexivity | exfalso].
      destruct (last (bv_and x s) false) eqn:Hxs_sign.
      - pose proof (@list2int_lt_pow2_int (bv_and x s) (N.to_nat n) Hlen_xs) as Hub.
        unfold pow2_int_N in Hslt. lia.
      - lia. }
    (* Show bv_and (bv_subt t s) s is non-negative *)
    assert (HDs_nonneg : last (bv_and (bv_subt t s) s) false = false).
    { destruct (last s false) eqn:Hs_sign.
      - (* s negative: need D non-negative *)
        (* T >= S >= 2^(n-1), T < 2^n, so D = T - S in [0, 2^(n-1)-1], D non-neg *)
        assert (HS_neg_lb : (pow2_int (length s - 1) <= list2int s)%Z).
        { apply last_true_list2int_lb.
          - intro H. rewrite H in Hs_sign. simpl in Hs_sign. discriminate.
          - exact Hs_sign. }
        (* D = subst_list t s, D_val = T - S (since T >= S) *)
        assert (HD_formula : (list2int (subst_list t s) = list2int t - list2int s)%Z).
        { rewrite HDform.
          replace (list2int t - list2int s + pow2_int (length t))%Z
            with (list2int t - list2int s + 1 * pow2_int (length t))%Z by ring.
          rewrite Z.mod_add; [| pose proof (zero_lt_pow2_int (length t)); lia].
          apply Z.mod_small. split; lia. }
        (* D_val = T - S < 2^(n-1) since T < 2^n and S >= 2^(n-1) *)
        assert (HD_lt_half : (list2int (subst_list t s) < pow2_int (length t - 1))%Z).
        { rewrite HD_formula.
          assert (HT_neg_lb : (pow2_int (length t - 1) <= list2int t)%Z).
          { apply last_true_list2int_lb.
            - intro H. rewrite H in Ht_neg. simpl in Ht_neg. discriminate.
            - exact Ht_neg. }
          assert (Hpow2_double : (pow2_int (length t) = 2 * pow2_int (length t - 1))%Z).
          { assert (Ht_ne : t <> []) by (intro H; rewrite H in Ht_neg; simpl in Ht_neg; discriminate).
            destruct t as [| h tl]; [exact (False_ind _ (Ht_ne eq_refl)) |].
            simpl length. rewrite Nat.sub_succ_r, Nat.sub_0_r, Nat.pred_succ. apply pow2_int_succ. }
          replace (length s - 1)%nat with (length t - 1)%nat in HS_neg_lb by lia.
          lia. }
        (* D non-negative: list2int D < 2^(n-1) implies last D = false *)
        assert (HD_ne : subst_list t s <> []).
        { intro H. apply (f_equal (@length bool)) in H. simpl in H.
          pose proof (@subst_list_length t s HLen_ts) as Hsl.
          assert (Hls : length s = 0%nat) by lia.
          assert (Hs_nil : s = []) by (apply length_zero_iff_nil; exact Hls).
          rewrite Hs_nil in Hs_sign. simpl in Hs_sign. discriminate. }
        assert (HD_last_false : last (subst_list t s) false = false).
        { destruct (last (subst_list t s) false) eqn:H; [| reflexivity].
          exfalso.
          pose proof (last_true_list2int_lb HD_ne H) as Hlb.
          replace (length (subst_list t s) - 1)%nat with (length t - 1)%nat in Hlb
            by (pose proof (@subst_list_length t s HLen_ts); lia).
          lia. }
        assert (Hbt_last : last (bv_subt t s) false = false).
        { unfold bv_subt. rewrite Ht, Hs, N.eqb_refl. exact HD_last_false. }
        exact (@pos_bvand_pos (bv_subt t s) s n HD_sz Hs Hbt_last).
      - (* s non-negative: bv_and D s non-negative *)
        exact (@pos_bv_and n (bv_subt t s) s HD_sz Hs Hs_sign). }
    (* t neg and bv_and D s non-neg: goal is (if last t false then T-P else T) < (if last Ds-sign then Ds-P else Ds) *)
    rewrite Ht_neg, HDs_nonneg.
    rewrite HT_eq, HDs_eq, HP_eq.
    pose proof (@list2int_geq_zero (bv_and (bv_subt t s) s)) as HDs_ge.
    lia.
Qed.

Lemma last_false_list2int_ub : forall v,
  v <> [] ->
  last v false = false ->
  (list2int v < pow2_int (length v - 1))%Z.
Proof.
  intros v Hne Hlast.
  pose proof (app_removelast_last false Hne) as Hdecomp.
  pose proof (f_equal (@length bool) Hdecomp) as Hlen_eq.
  rewrite length_app in Hlen_eq. simpl length in Hlen_eq.
  rewrite Hlast in Hdecomp. rewrite Hdecomp.
  rewrite list2int_app. rewrite list2int_bool.
  change (bool2int false) with 0%Z. rewrite Z.mul_0_r, Z.add_0_l.
  rewrite length_app. simpl length. rewrite Nat.add_sub.
  apply list2int_lt_pow2_int. reflexivity.
Qed.

Lemma last_map_negb : forall v,
  v <> [] ->
  last (map negb v) false = negb (last v false).
Proof.
  intros v Hne.
  pose proof (app_removelast_last false Hne) as Hdecomp.
  rewrite Hdecomp at 1. rewrite map_app. simpl map.
  rewrite last_app. reflexivity.
Qed.

Lemma last_map2_orb_eq : forall a b,
  length a = length b ->
  a <> [] ->
  last (map2 orb a b) false = orb (last a false) (last b false).
Proof.
  intros a b Hlen Ha_ne.
  assert (Hb_ne : b <> []).
  { intro H. subst. destruct a; [exact (Ha_ne eq_refl) | discriminate Hlen]. }
  pose proof (app_removelast_last false Ha_ne) as Ha_decomp.
  pose proof (app_removelast_last false Hb_ne) as Hb_decomp.
  pose proof (f_equal (@length bool) Ha_decomp) as Halen.
  pose proof (f_equal (@length bool) Hb_decomp) as Hblen.
  rewrite length_app in Halen, Hblen. simpl length in Halen, Hblen.
  rewrite Ha_decomp, Hb_decomp.
  rewrite map2_or_app; [| lia | simpl; lia].
  simpl. rewrite !last_app. reflexivity.
Qed.

Lemma bvor_slt_key : forall (n : N) (s t x : bitvector),
  size s = n -> size t = n -> size x = n ->
  bv_slt (bv_or x s) t = true ->
  bv_slt (bv_or (bv_not (bv_subt s t)) s) t = true.
Proof.
  intros n s t x Hs Ht Hx Hslt.
  pose proof (@bv_or_size n x s Hx Hs) as Hxs_sz.
  pose proof (@bv_subt_size n s t Hs Ht) as HSD_sz.
  pose proof (@bv_not_size n (bv_subt s t) HSD_sz) as HV_sz.
  pose proof (@bv_or_size n (bv_not (bv_subt s t)) s HV_sz Hs) as HVs_sz.
  pose proof (@size_to_length n s Hs) as Hlen_s.
  pose proof (@size_to_length n t Ht) as Hlen_t.
  pose proof (@size_to_length n x Hx) as Hlen_x.
  pose proof (@size_to_length n (bv_subt s t) HSD_sz) as Hlen_D.
  (* Handle n = 0: bv_slt on empty bitvectors is false *)
  destruct s as [| h_s tl_s].
  { exfalso.
    assert (Hn0 : n = 0%N) by (unfold size in Hs; simpl in Hs; exact (eq_sym Hs)).
    assert (Hxl : length x = 0%nat) by (rewrite Hlen_x, Hn0; reflexivity).
    assert (Htl : length t = 0%nat) by (rewrite Hlen_t, Hn0; reflexivity).
    apply length_zero_iff_nil in Hxl, Htl. subst x t.
    unfold bv_or, bv_slt, slt_list, slt_list_big_endian, size, bits in Hslt.
    simpl in Hslt. discriminate. }
  set (s := h_s :: tl_s) in *.
  assert (Hs_ne : s <> []) by (unfold s; discriminate).
  assert (Hs_len_pos : (0 < length s)%nat) by (unfold s; simpl; lia).
  assert (HLen_st : length s = length t) by (rewrite Hlen_s, Hlen_t; reflexivity).
  assert (HLen_Ds : length (subst_list s t) = length s).
  { pose proof (@subst_list_length s t HLen_st). lia. }
  pose proof (@list2int_subst_list_formula s t HLen_st) as HDform.
  assert (HLen_V : length (map negb (subst_list s t)) = length s).
  { rewrite length_map. exact HLen_Ds. }
  assert (HLen_xs : length x = length s) by (rewrite Hlen_x, Hlen_s; reflexivity).
  assert (HV_unfold : bv_not (bv_subt s t) = map negb (subst_list s t)).
  { unfold bv_not, bv_subt. rewrite Hs, Ht, N.eqb_refl. reflexivity. }
  assert (HVs_unfold : bv_or (bv_not (bv_subt s t)) s = map2 orb (map negb (subst_list s t)) s).
  { unfold bv_or. rewrite HV_sz, Hs, N.eqb_refl.
    unfold bits. rewrite HV_unfold. reflexivity. }
  assert (HXs_unfold : bv_or x s = map2 orb x s).
  { unfold bv_or. rewrite Hx, Hs, N.eqb_refl. reflexivity. }
  pose proof Hslt as Hslt_bv.
  rewrite (@bv_slt_iff_sbv2int n (bv_or x s) t Hxs_sz Ht) in Hslt.
  rewrite (@bv_slt_iff_sbv2int n (bv_or (bv_not (bv_subt s t)) s) t HVs_sz Ht).
  unfold sbv2int in *.
  set (T := list2int t). set (S := list2int s).
  set (D := list2int (subst_list s t)).
  set (V := list2int (map negb (subst_list s t))).
  set (Vs := list2int (map2 orb (map negb (subst_list s t)) s)).
  set (Vand := list2int (map2 andb (map negb (subst_list s t)) s)).
  set (Xs := list2int (map2 orb x s)).
  set (P := pow2_int_N n).
  unfold bv2int in *. fold T S D V Vs Vand Xs P.
  rewrite HVs_unfold, HXs_unfold in *.
  assert (HP_eq : P = pow2_int (length s)).
  { unfold P, pow2_int_N. now rewrite Hlen_s. }
  assert (HPt_eq : P = pow2_int (length t)).
  { unfold P, pow2_int_N. now rewrite Hlen_t. }
  assert (HP_pos : (0 < P)%Z).
  { rewrite HP_eq. apply zero_lt_pow2_int. }
  set (Ph := pow2_int (length s - 1)).
  assert (HPh_pos : (0 < Ph)%Z) by (unfold Ph; apply zero_lt_pow2_int).
  assert (HP_2Ph : (P = 2 * Ph)%Z).
  { unfold Ph. rewrite HP_eq.
    destruct s as [| h tl]; [exact (False_ind _ (Hs_ne eq_refl)) |].
    simpl length. rewrite Nat.sub_succ_r, Nat.sub_0_r, Nat.pred_succ. apply pow2_int_succ. }
  pose proof (@list2int_lt_pow2_int s (length s) eq_refl) as HS_ub.
  pose proof (@list2int_lt_pow2_int t (length t) eq_refl) as HT_ub.
  pose proof (@list2int_geq_zero s) as HS_lb.
  pose proof (@list2int_geq_zero t) as HT_lb.
  pose proof (@list2int_geq_zero (map2 andb (map negb (subst_list s t)) s)) as HVand_lb.
  pose proof (@list2int_geq_zero (map2 orb (map negb (subst_list s t)) s)) as HVs_lb.
  pose proof (@list2int_geq_zero x) as HX_lb.
  rewrite <- HP_eq in HS_ub. rewrite <- HPt_eq in HT_ub.
  (* V + D = P - 1 *)
  assert (HVD_sum : (V + D = P - 1)%Z).
  { assert (H : (V + D = pow2_int (length (subst_list s t)) - 1)%Z).
    { unfold V, D. pose proof (@list2int_map_negb_sum (subst_list s t)) as Hsum. lia. }
    rewrite HLen_Ds, <- HP_eq in H. lia. }
  (* Vand + Vs = V + S (inclusion-exclusion) *)
  assert (HIE : (Vand + Vs = V + S)%Z).
  { unfold Vs, Vand, V, S. apply list2int_map2_and_or_sum. exact HLen_V. }
  (* Vand <= S (submask) *)
  assert (HVand_le_S : (Vand <= S)%Z).
  { apply ule_list_list2int.
    - pose proof (@map2_and_length (map negb (subst_list s t)) s HLen_V) as Hml. lia.
    - rewrite map2_and_comm. apply (@ule_list_map2_and s (map negb (subst_list s t))). lia. }
  (* Xs >= S (x|s >=u s) *)
  assert (HXs_ge_S : (S <= Xs)%Z).
  { pose proof (@list2int_map2_and_or_sum x s HLen_xs) as HIE_x.
    assert (HXand_le_X : (list2int (map2 andb x s) <= list2int x)%Z).
    { apply ule_list_list2int.
      - pose proof (@map2_and_length x s HLen_xs) as Hml. lia.
      - apply (@ule_list_map2_and x s). lia. }
    lia. }
  assert (Hst_ne : subst_list s t <> []).
  { intro H. apply (f_equal (@length bool)) in H. simpl in H.
    pose proof (@subst_list_length s t HLen_st). lia. }
  assert (HV_ne : map negb (subst_list s t) <> []).
  { intro H. apply (f_equal (@length bool)) in H. rewrite length_map in H. simpl in H.
    pose proof (@subst_list_length s t HLen_st). lia. }
  assert (HVs_ne : map2 orb (map negb (subst_list s t)) s <> []).
  { intro H. apply (f_equal (@length bool)) in H. simpl in H.
    pose proof (@map2_or_length (map negb (subst_list s t)) s HLen_V). lia. }
  assert (HXs_ne : map2 orb x s <> []).
  { intro H. apply (f_equal (@length bool)) in H. simpl in H.
    pose proof (@map2_or_length x s HLen_xs). lia. }
  assert (Hx_ne : x <> []).
  { intro H. apply Hs_ne. apply length_zero_iff_nil. rewrite <- HLen_xs, H. reflexivity. }
  destruct (bv_ult s t) eqn:Hult_st.
  - (* bv_ult s t: S < T *)
    assert (HS_lt_T : (S < T)%Z).
    { apply ult_list_list2int; [exact HLen_st |].
      unfold bv_ult in Hult_st. rewrite Hs, Ht, N.eqb_refl in Hult_st. exact Hult_st. }
    assert (HD_val : (D = S - T + P)%Z).
    { unfold D, S, T. rewrite HDform. rewrite <- HP_eq. apply Z.mod_small.
      split; lia. }
    assert (HV_val : (V = T - S - 1)%Z) by lia.
    assert (HVs_val : (Vs = T - 1 - Vand)%Z) by lia.
    assert (HVs_lt_T : (Vs < T)%Z) by lia.
    (* case split on sign(V|s) and sign(t) *)
    destruct (last (map2 orb (map negb (subst_list s t)) s) false) eqn:HVs_sign;
    destruct (last t false) eqn:Ht_sign.
    + (* both negative: bv2int(V|s) - P < bv2int(t) - P *)
      rewrite HP_eq. lia.
    + (* V|s negative, t nonneg: Vs - P < 0 <= T *)
      rewrite HP_eq. lia.
    + (* V|s nonneg, t negative: need contradiction from Hslt *)
      exfalso.
      (* last s = false (neg_bv_or would give last(V|s)=true, contradicting HVs_sign=false) *)
      assert (Hs_last : last s false = false).
      { destruct (last s false) eqn:H; [| reflexivity]. exfalso.
        pose proof (@neg_bv_or n (bv_not (bv_subt s t)) s HV_sz Hs H) as Hc.
        rewrite HVs_unfold in Hc. rewrite Hc in HVs_sign. discriminate. }
      (* last(V) = false: from last_map2_orb_eq with last s=false *)
      assert (HV_last : last (map negb (subst_list s t)) false = false).
      { destruct (last (map negb (subst_list s t)) false) eqn:H; [| reflexivity]. exfalso.
        pose proof (@last_map2_orb_eq (map negb (subst_list s t)) s HLen_V HV_ne) as Hlast_eq.
        rewrite H, Hs_last in Hlast_eq. simpl in Hlast_eq. rewrite Hlast_eq in HVs_sign. discriminate. }
      (* last(D) = true: from last_map_negb *)
      assert (HD_last : last (subst_list s t) false = true).
      { pose proof (@last_map_negb (subst_list s t) Hst_ne) as H.
        rewrite HV_last in H. symmetry in H. rewrite negb_false_iff in H. exact H. }
      (* D >= Ph *)
      assert (HD_lb : (Ph <= D)%Z).
      { unfold Ph. rewrite <- HLen_Ds.
        apply last_true_list2int_lb; exact Hst_ne || exact HD_last. }
      (* T <= S + Ph (from D = S - T + P and D >= Ph: Ph <= S - T + P = S - T + 2*Ph → T <= S + Ph) *)
      assert (HT_le_SPh : (T <= S + Ph)%Z) by lia.
      (* Vs < Ph (from last(V|s)=false) *)
      assert (HVs_lt_Ph : (Vs < Ph)%Z).
      { assert (Hlen_Vs : length (map2 orb (map negb (subst_list s t)) s) = length s).
        { rewrite <- (@map2_or_length (map negb (subst_list s t)) s HLen_V). exact HLen_V. }
        unfold Vs, Ph. rewrite <- Hlen_Vs.
        apply last_false_list2int_ub; [exact HVs_ne | exact HVs_sign]. }
      (* T <= Ph + Vand (from Vs = T-1-Vand < Ph) *)
      assert (HT_le : (T <= Ph + Vand)%Z) by lia.
      (* Now case on last(x|s) *)
      destruct (last (map2 orb x s) false) eqn:Hxs_sign.
      * (* last(x|s) = true: Xs >= S+Ph, but Xs < T <= Ph+S. Contradiction. *)
        assert (Harith : (list2int (map2 orb x s) - pow2_int_N n < list2int t - pow2_int_N n)%Z).
        { assert (H : (sbv2int n (map2 orb x s) < sbv2int n t)%Z).
          { exact (proj1 (@bv_slt_iff_sbv2int n (map2 orb x s) t Hxs_sz Ht) Hslt_bv). }
          unfold sbv2int in H. rewrite Hxs_sign, Ht_sign in H. simpl in H. exact H. }
        assert (Hx_last : last x false = true).
        { pose proof (@last_map2_orb_eq x s HLen_xs Hx_ne) as Hlast_eq.
          rewrite Hxs_sign, Hs_last in Hlast_eq. rewrite orb_false_r in Hlast_eq.
          exact (eq_sym Hlast_eq). }
        assert (HXand_le : (list2int (map2 andb s x) <= list2int x - Ph)%Z).
        { unfold Ph. rewrite <- HLen_xs.
          apply last_false_and_true_submask_bound; [lia | exact Hs_last | exact Hx_last]. }
        pose proof (@list2int_map2_and_or_sum x s HLen_xs) as HIE_x.
        assert (Hxs_and_comm : list2int (map2 andb x s) = list2int (map2 andb s x)).
        { f_equal. apply map2_and_comm. }
        lia.
      * (* last(x|s) = false, last t = true: 0 <= Xs < T - P < 0. Contradiction. *)
        assert (Harith : (list2int (map2 orb x s) < list2int t - pow2_int_N n)%Z).
        { assert (H : (sbv2int n (map2 orb x s) < sbv2int n t)%Z).
          { exact (proj1 (@bv_slt_iff_sbv2int n (map2 orb x s) t Hxs_sz Ht) Hslt_bv). }
          unfold sbv2int in H. rewrite Hxs_sign, Ht_sign in H. simpl in H. exact H. }
        pose proof (@list2int_geq_zero (map2 orb x s)) as HXs_lb2.
        lia.
    + (* both nonneg: Vs < T *)
      lia.
  - (* bv_ult s t = false: T <= S *)
    assert (HT_le_S : (T <= S)%Z).
    { apply bv_ult_false_list2int_ge; [rewrite Hs, Ht; reflexivity | exact Hult_st]. }
    destruct (last s false) eqn:Hs_sign.
    + (* last s = true: last(V|s) = true always *)
      assert (HVs_neg : last (bv_or (bv_not (bv_subt s t)) s) false = true).
      { apply (@neg_bv_or n (bv_not (bv_subt s t)) s HV_sz Hs Hs_sign). }
      destruct (last t false) eqn:Ht_sign.
      * (* last t = true: contradiction from Hslt (Xs >= S >= T but Xs < T) *)
        exfalso.
        assert (Hxs_neg : last (bv_or x s) false = true).
        { apply (@neg_bv_or n x s Hx Hs Hs_sign). }
        rewrite HXs_unfold in Hxs_neg.
        assert (Harith : (list2int (map2 orb x s) - pow2_int_N n < list2int t - pow2_int_N n)%Z).
        { assert (H : (sbv2int n (map2 orb x s) < sbv2int n t)%Z).
          { exact (proj1 (@bv_slt_iff_sbv2int n (map2 orb x s) t Hxs_sz Ht) Hslt_bv). }
          unfold sbv2int in H. rewrite Hxs_neg, Ht_sign in H. simpl in H. exact H. }
        lia.
      * (* last t = false: Vs is negative, T is non-negative, so Vs - P < 0 <= T *)
        assert (HVs_lt_P : (Vs < P)%Z).
        { unfold Vs. rewrite HP_eq.
          apply (@list2int_lt_pow2_int (map2 orb (map negb (subst_list s t)) s) (length s)).
          exact (eq_trans (eq_sym (@map2_or_length (map negb (subst_list s t)) s HLen_V)) HLen_V). }
        rewrite HVs_unfold in HVs_neg. rewrite HVs_neg. simpl. lia.
    + (* last s = false: T <= S < Ph, last t = false, show last V = true *)
      assert (HS_lt_Ph : (S < Ph)%Z).
      { unfold Ph. apply last_false_list2int_ub; exact Hs_ne || exact Hs_sign. }
      assert (HT_lt_Ph : (T < Ph)%Z) by lia.
      assert (Ht_last_false : last t false = false).
      { destruct (last t false) eqn:H; [| reflexivity]. exfalso.
        assert (Ht_ne : t <> []) by (intro Hnil; subst; simpl in H; discriminate).
        pose proof (@last_true_list2int_lb t Ht_ne H) as HT_lb2.
        rewrite <- HLen_st in HT_lb2. unfold Ph in HT_lt_Ph. lia. }
      assert (HD_val : (D = S - T)%Z).
      { unfold D, S, T. rewrite HDform.
        replace (list2int s - list2int t + pow2_int (length s))%Z
          with (list2int s - list2int t + 1 * pow2_int (length s))%Z by ring.
        rewrite Z.mod_add; [| rewrite <- HP_eq; lia].
        apply Z.mod_small. rewrite <- HP_eq. split; lia. }
      assert (HV_val : (V = P - 1 - S + T)%Z) by lia.
      assert (HV_lb : (Ph <= V)%Z) by lia.
      assert (HV_last : last (map negb (subst_list s t)) false = true).
      { destruct (last (map negb (subst_list s t)) false) eqn:H; [reflexivity |]. exfalso.
        pose proof (@last_false_list2int_ub (map negb (subst_list s t)) HV_ne H) as Hub.
        rewrite length_map, HLen_Ds in Hub. unfold Ph in HV_lb. unfold V in HV_lb. lia. }
      assert (HVs_pos : last (bv_or (bv_not (bv_subt s t)) s) false = true).
      { rewrite (bv_or_comm HV_sz Hs).
        apply (@neg_bv_or n s (bv_not (bv_subt s t)) Hs HV_sz).
        rewrite HV_unfold. exact HV_last. }
      rewrite HVs_unfold in HVs_pos. rewrite HVs_pos, Ht_last_false. simpl. lia.
Qed.

(* M = bv_or(-s, s) = ones|zeros mask, v = t - (M|t): bv_and M v = v *)
Lemma bv_and_mult_subt_idemp : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  bv_and (bv_or (bv_neg s) s)
         (bv_subt t (bv_or (bv_or (bv_neg s) s) t))
  = bv_subt t (bv_or (bv_or (bv_neg s) s) t).
Proof.
  intros n s t Hs Ht.
  assert (HM : size (bv_or (bv_neg s) s) = n).
  { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
  assert (HMt : size (bv_or (bv_or (bv_neg s) s) t) = n).
  { apply bv_or_size; [exact HM | exact Ht]. }
  assert (Hv : size (bv_subt t (bv_or (bv_or (bv_neg s) s) t)) = n).
  { apply bv_subt_size; [exact Ht | exact HMt]. }
  pose proof (@size_to_length n t Ht) as Hlen_t.
  destruct (@zeros_one_factorization s) as [Hzeros | (k, (z, Hfact))].
  - (* s = zeros n: M = zeros n *)
    assert (HM_zero : bv_or (bv_neg s) s = zeros n).
    {
      rewrite Hzeros, Hs, bv_neg_zeros_zeros.
      pose proof (bv_or_0_neutral (zeros n)) as H.
      rewrite zeros_size in H. exact H.
    }
    rewrite HM_zero.
    assert (HMt_eq : bv_or (zeros n) t = t).
    {
      rewrite (bv_or_comm (zeros_size n) Ht).
      pose proof (bv_or_0_neutral t) as H.
      rewrite Ht in H. exact H.
    }
    rewrite HMt_eq.
    (* bv_subt t t = zeros n *)
    assert (Hsubt_tt : bv_subt t t = zeros n).
    {
      apply list2int_inj.
      + pose proof (@size_to_length n (bv_subt t t) (bv_subt_size Ht Ht)) as Hlensubt.
        pose proof (@size_to_length n (zeros n) (zeros_size n)) as Hlenz.
        lia.
      + unfold bv_subt. rewrite N.eqb_refl.
        pose proof (@list2int_subst_list_formula t t eq_refl) as Hform.
        rewrite Z.sub_diag, Z.add_0_l in Hform.
        pose proof (zero_lt_pow2_int (length t)) as Hlt.
        rewrite Z.mod_same in Hform; [| lia].
        unfold zeros. rewrite list2int_mk_list_false.
        exact Hform.
    }
    rewrite Hsubt_tt.
    apply bv_and_idem.
  - (* s = bv_concat(bv_concat z (one 1))(zeros k) *)
    assert (H_M_eq : bv_or (bv_neg s) s = bv_concat (ones (size z + 1)) (zeros k)).
    {
      rewrite Hfact, bv_neg_zeros_one. apply bv_or_neg_zeros_one.
    }
    assert (Hn_eq : n = size z + 1 + k).
    {
      rewrite <- Hs, Hfact.
      apply (@bv_concat_size (size z + 1) k).
      + now apply (@bv_concat_size (size z) 1).
      + apply zeros_size.
    }
    pose proof (@size_to_length n (bv_or (bv_neg s) s) HM) as Hlen_M.
    (* set v first so it folds into goal and Hv before H_M_eq rewrites the goal *)
    set (v := bv_subt t (bv_or (bv_or (bv_neg s) s) t)).
    rewrite H_M_eq.
    assert (H_and_eq : bv_and (bv_concat (ones (size z + 1)) (zeros k)) v
                       = bv_concat (skipn (N.to_nat k) v) (zeros k)).
    { apply bv_and_or_neg_zeros_one.
      assert (Hv' : size v = n) by exact Hv.
      rewrite Hv', Hn_eq. ring. }
    rewrite H_and_eq.
    (* Use bv_and_or_neg_eq_zeros_one backward: suffices to provide witness x s.t. x*Pk ≡ bv2int v mod P *)
    assert (Hkv : k <= size v).
    { assert (Hv' : size v = n) by exact Hv.
      rewrite Hv', Hn_eq. apply N.le_add_l. }
    apply (proj2 (@bv_and_or_neg_eq_zeros_one v k Hkv)).
    (* Integer abbreviations *)
    set (Pk := pow2_int_N k) in *.
    set (P := pow2_int_N n) in *.
    set (T := list2int t).
    set (Tk := list2int (skipn (N.to_nat k) t)).
    (* Witness: Tk + 1 *)
    exists (Tk + 1)%Z.
    (* Unfold bv2int v to list2int (subst_list t (map2 orb M t)) *)
    assert (Hv_eq : bv2int v = list2int (subst_list t (map2 orb (bv_or (bv_neg s) s) t))).
    {
      unfold v, bv2int, bv_subt.
      rewrite Ht, HMt, N.eqb_refl.
      unfold bv_or at 1. rewrite HM, Ht, N.eqb_refl. reflexivity.
    }
    rewrite Hv_eq.
    (* Length of map2 orb M t *)
    assert (Hlen_Mt : length (map2 orb (bv_or (bv_neg s) s) t) = length t).
    {
      assert (H : length (bv_or (bv_neg s) s) = length t) by (rewrite Hlen_M, Hlen_t; reflexivity).
      pose proof (@map2_or_length (bv_or (bv_neg s) s) t H) as Hml.
      rewrite Hlen_M in Hml. lia.
    }
    (* list2int of M = P - Pk *)
    assert (HM_int : list2int (bv_or (bv_neg s) s) = (P - Pk)%Z).
    {
      change (list2int (bv_or (bv_neg s) s)) with (bv2int (bv_or (bv_neg s) s)).
      rewrite H_M_eq, bv2int_app, bv2int_zeros, Z.add_0_r.
      unfold ones, bv2int, Pk, P, pow2_int_N.
      rewrite zeros_size.
      pose proof (@list2int_map_negb_sum (mk_list_false (N.to_nat (size z + 1)))) as Hsum.
      rewrite not_list_false_true, list2int_mk_list_false, length_mk_list_false in Hsum.
      assert (HPn : pow2_int (N.to_nat n) = (pow2_int (N.to_nat (size z + 1)) * pow2_int (N.to_nat k))%Z).
      { rewrite Hn_eq. rewrite N2Nat.inj_add at 1. rewrite pow2_int_add. ring. }
      lia.
    }
    (* list2int of (M & t) = Pk * Tk *)
    assert (HMt_and_int : list2int (map2 andb (bv_or (bv_neg s) s) t) = (Pk * Tk)%Z).
    {
      assert (Heq : bv_and (bv_or (bv_neg s) s) t = map2 andb (bv_or (bv_neg s) s) t).
      { unfold bv_and. rewrite HM, Ht, N.eqb_refl. reflexivity. }
      assert (Hcond : size z + 1 + k = size t) by (rewrite Ht; lia).
      change (list2int (map2 andb (bv_or (bv_neg s) s) t))
        with (bv2int (map2 andb (bv_or (bv_neg s) s) t)).
      rewrite <- Heq, H_M_eq.
      rewrite (bv_and_or_neg_zeros_one Hcond).
      rewrite bv2int_app, bv2int_zeros, Z.add_0_r.
      unfold Pk, Tk, pow2_int_N. rewrite zeros_size. reflexivity.
    }
    (* list2int of (M | t) = P - Pk + T - Pk*Tk via inclusion-exclusion *)
    assert (HMt_or_int : list2int (map2 orb (bv_or (bv_neg s) s) t) = (P - Pk + T - Pk * Tk)%Z).
    {
      pose proof (@list2int_map2_and_or_sum (bv_or (bv_neg s) s) t) as HIE.
      rewrite Hlen_M, Hlen_t in HIE.
      specialize (HIE eq_refl).
      rewrite HMt_and_int in HIE.
      unfold bv2int in HM_int. rewrite HM_int in HIE. lia.
    }
    (* Subtraction formula: list2int(subst_list t (M|t)) = (T - (P-Pk+T-Pk*Tk) + P) mod P = Pk*(Tk+1) mod P *)
    rewrite list2int_subst_list_formula; [| exact (eq_sym Hlen_Mt)].
    rewrite HMt_or_int.
    assert (Hsize_v : size v = n) by exact Hv.
    unfold P, Pk, pow2_int_N. rewrite Hlen_t, Hsize_v.
    assert (Hnum : (list2int t - (pow2_int (N.to_nat n) - pow2_int (N.to_nat k) + T
                               - pow2_int (N.to_nat k) * Tk) + pow2_int (N.to_nat n))%Z
                 = ((Tk + 1) * pow2_int (N.to_nat k))%Z) by (unfold T, Tk; ring).
    rewrite Hnum.
    rewrite Z.mod_mod by (pose proof (zero_lt_pow2_int (N.to_nat n)); lia).
    reflexivity.
Qed.

(* Forward direction of bvmult_sgt: s nonzero, t <s x*s -> t <s bv_subt t (M|t) *)
Lemma bvmult_sgt_fwd_key : forall (n : N) (z : bitvector) (k : N) (t x_s : bitvector),
  size t = n -> size x_s = n ->
  n = size z + 1 + k ->
  bv_and (bv_concat (ones (size z + 1)) (zeros k)) x_s = x_s ->
  bv_slt t x_s = true ->
  bv_slt t (bv_subt t (bv_or (bv_concat (ones (size z + 1)) (zeros k)) t)) = true.
Proof.
  intros n z k t x_s Ht Hxs Hn_eq HXinM Hslt.
  assert (HMsz : size (bv_concat (ones (size z + 1)) (zeros k)) = n).
  { rewrite Hn_eq. apply bv_concat_size; [apply ones_size | apply zeros_size]. }
  assert (HMOtsz : size (bv_or (bv_concat (ones (size z + 1)) (zeros k)) t) = n).
  { apply bv_or_size; [exact HMsz | exact Ht]. }
  assert (Hvsz : size (bv_subt t (bv_or (bv_concat (ones (size z + 1)) (zeros k)) t)) = n).
  { apply bv_subt_size; [exact Ht | exact HMOtsz]. }
  set (v := bv_subt t (bv_or (bv_concat (ones (size z + 1)) (zeros k)) t)).
  pose proof (size_to_length Ht) as Hlen_t.
  pose proof (size_to_length Hxs) as Hlen_xs.
  pose proof (size_to_length Hvsz) as Hlen_v.
  set (h := N.to_nat (size z + 1)).
  set (kn := N.to_nat k).
  set (hk := (h + kn)%nat).
  assert (Hh_pos : (1 <= h)%nat).
  { unfold h. rewrite N.add_1_r. rewrite N2Nat.inj_succ. lia. }
  assert (Hlen_eq : length t = hk).
  { unfold hk, h, kn. rewrite <- N2Nat.inj_add, <- Hn_eq. exact Hlen_t. }
  assert (Hlen_xs_eq : length x_s = hk). { lia. }
  assert (Hlen_v_eq : length v = hk). { unfold v. rewrite Hlen_v, <- Hlen_t. exact Hlen_eq. }
  set (Pk := pow2_int kn).
  set (Ph := pow2_int h).
  set (P := pow2_int hk).
  assert (HP_split : P = (Pk * Ph)%Z).
  { unfold P, Pk, Ph, hk. rewrite pow2_int_add. ring. }
  assert (HPk_pos : (0 < Pk)%Z) by apply zero_lt_pow2_int.
  assert (HPh_pos : (0 < Ph)%Z) by apply zero_lt_pow2_int.
  assert (HP_pos : (0 < P)%Z) by lia.
  assert (HPow_n : pow2_int_N n = P).
  { unfold P, pow2_int_N, hk, h, kn. rewrite Hn_eq, N2Nat.inj_add. reflexivity. }
  assert (HPow_k : pow2_int_N k = Pk).
  { unfold Pk, pow2_int_N, kn. reflexivity. }
  assert (Hhk_pos : (1 <= hk)%nat) by (unfold hk; lia).
  assert (HPk_Ph1 : (Pk * pow2_int (h - 1)%nat = pow2_int (hk - 1)%nat)%Z).
  { unfold Pk, hk. rewrite <- pow2_int_add. f_equal. lia. }
  assert (HPow2_double : (2 * pow2_int (hk - 1)%nat = P)%Z).
  { unfold P. rewrite <- pow2_int_succ. f_equal. lia. }
  set (Tk := list2int (skipn kn t)).
  set (T_lo := list2int (firstn kn t)).
  set (T := list2int t).
  set (V := list2int v).
  set (Xu := list2int (skipn kn x_s)).
  set (X := list2int x_s).
  assert (HT_lb : (0 <= T)%Z) by (unfold T; apply list2int_geq_zero).
  assert (HT_ub : (T < P)%Z).
  { unfold T, P. apply list2int_lt_pow2_int. lia. }
  assert (HV_lb : (0 <= V)%Z) by (unfold V; apply list2int_geq_zero).
  assert (HV_ub : (V < P)%Z).
  { unfold V, P. apply list2int_lt_pow2_int. lia. }
  assert (HX_lb : (0 <= X)%Z) by (unfold X; apply list2int_geq_zero).
  assert (HX_ub : (X < P)%Z).
  { unfold X, P. apply list2int_lt_pow2_int. lia. }
  assert (HTk_lb : (0 <= Tk)%Z) by (unfold Tk; apply list2int_geq_zero).
  assert (HTk_ub : (Tk < Ph)%Z).
  { unfold Tk, Ph. apply list2int_lt_pow2_int.
    rewrite length_skipn. lia. }
  assert (HT_lo_lb : (0 <= T_lo)%Z) by (unfold T_lo; apply list2int_geq_zero).
  assert (HT_lo_ub : (T_lo < Pk)%Z).
  { unfold T_lo, Pk. apply list2int_lt_pow2_int.
    rewrite firstn_length_le; lia. }
  assert (HXu_lb : (0 <= Xu)%Z) by (unfold Xu; apply list2int_geq_zero).
  assert (HXu_ub : (Xu < Ph)%Z).
  { unfold Xu, Ph. apply list2int_lt_pow2_int.
    rewrite length_skipn. lia. }
  (* T = Pk*Tk + T_lo *)
  assert (HT_split : T = (Pk * Tk + T_lo)%Z).
  { unfold T, Tk, T_lo, Pk.
    rewrite <- (firstn_skipn kn t) at 1.
    rewrite list2int_app.
    rewrite firstn_length_le; [ring | lia]. }
  (* X = Pk*Xu (lower k bits of x_s are all zero) *)
  assert (HX_concat : bv_concat (skipn kn x_s) (zeros k) = x_s).
  { assert (Hcond : size z + 1 + k = size x_s). { rewrite Hxs. exact (eq_sym Hn_eq). }
    exact (eq_trans (eq_sym (bv_and_or_neg_zeros_one Hcond)) HXinM). }
  assert (HX_val : X = (Pk * Xu)%Z).
  { unfold X, Xu, Pk. rewrite <- HX_concat at 1.
    change (list2int (bv_concat (skipn kn x_s) (zeros k)))
      with (bv2int (bv_concat (skipn kn x_s) (zeros k))).
    change (list2int (skipn kn x_s)) with (bv2int (skipn kn x_s)).
    rewrite bv2int_app, bv2int_zeros, zeros_size, Z.add_0_r.
    unfold kn, pow2_int_N. reflexivity. }
  (* Compute list2int(M) = P - Pk *)
  assert (HM_int : list2int (bv_concat (ones (size z + 1)) (zeros k)) = (P - Pk)%Z).
  { change (list2int _) with (bv2int (bv_concat (ones (size z + 1)) (zeros k))).
    rewrite bv2int_app, bv2int_zeros, Z.add_0_r.
    unfold ones, bv2int. rewrite zeros_size.
    pose proof (@list2int_map_negb_sum (mk_list_false (N.to_nat (size z + 1)))) as Hsum.
    rewrite not_list_false_true, list2int_mk_list_false, length_mk_list_false in Hsum.
    unfold Pk, P, hk. rewrite pow2_int_add. unfold h, kn, pow2_int_N. nia. }
  (* Compute list2int(M & t) = Pk*Tk *)
  assert (HMt_and_int : list2int (map2 andb (bv_concat (ones (size z + 1)) (zeros k)) t) = (Pk * Tk)%Z).
  { assert (Hcond : size z + 1 + k = size t). { rewrite Ht. exact (eq_sym Hn_eq). }
    change (list2int (map2 andb _ t)) with
           (bv2int (map2 andb (bv_concat (ones (size z + 1)) (zeros k)) t)).
    assert (Heq : bv_and (bv_concat (ones (size z + 1)) (zeros k)) t
                  = map2 andb (bv_concat (ones (size z + 1)) (zeros k)) t).
    { unfold bv_and. rewrite HMsz, Ht, N.eqb_refl. reflexivity. }
    rewrite <- Heq, (bv_and_or_neg_zeros_one Hcond).
    rewrite bv2int_app, bv2int_zeros, zeros_size, Z.add_0_r.
    unfold Pk, Tk, pow2_int_N. reflexivity. }
  (* Compute list2int(M | t) = P - Pk + T - Pk*Tk by inclusion-exclusion *)
  assert (Hlen_Mt : length (map2 orb (bv_concat (ones (size z + 1)) (zeros k)) t) = length t).
  { assert (HlenM : length (bv_concat (ones (size z + 1)) (zeros k)) = length t).
    { pose proof (size_to_length HMsz). lia. }
    pose proof (@map2_or_length (bv_concat (ones (size z + 1)) (zeros k)) t HlenM) as Hml.
    rewrite HlenM in Hml. lia. }
  assert (HMt_or_int : list2int (map2 orb (bv_concat (ones (size z + 1)) (zeros k)) t) = (P - Pk + T - Pk * Tk)%Z).
  { pose proof (@list2int_map2_and_or_sum (bv_concat (ones (size z + 1)) (zeros k)) t) as HIE.
    assert (HlenM : length (bv_concat (ones (size z + 1)) (zeros k)) = length t).
    { pose proof (size_to_length HMsz). lia. }
    specialize (HIE HlenM).
    rewrite HMt_and_int in HIE.
    change (list2int (bv_concat (ones (size z + 1)) (zeros k))) with
           (bv2int (bv_concat (ones (size z + 1)) (zeros k))) in HM_int.
    unfold bv2int in HM_int. rewrite HM_int in HIE. lia. }
  (* V = Pk*(Tk+1) mod P *)
  assert (HV_formula : V = ((Pk * (Tk + 1)) mod P)%Z).
  { unfold V, v, bv_subt.
    rewrite Ht, HMOtsz, N.eqb_refl.
    assert (Hbvor : bv_or (bv_concat (ones (size z + 1)) (zeros k)) t
                  = map2 orb (bv_concat (ones (size z + 1)) (zeros k)) t).
    { unfold bv_or. rewrite HMsz, Ht, N.eqb_refl. reflexivity. }
    rewrite Hbvor. unfold bits.
    rewrite list2int_subst_list_formula; [| exact (eq_sym Hlen_Mt)].
    rewrite HMt_or_int.
    fold T.
    replace (pow2_int (length t)) with P by (unfold P; f_equal; exact (eq_sym Hlen_eq)).
    assert (Hnum : (T - (P - Pk + T - Pk * Tk) + P)%Z = (Pk * (Tk + 1))%Z) by (unfold T; ring).
    rewrite Hnum. reflexivity. }
  (* Convert Hxs and goal using bv_slt_iff_sbv2int *)
  rewrite (@bv_slt_iff_sbv2int n t x_s Ht Hxs) in Hslt.
  rewrite (@bv_slt_iff_sbv2int n t v Ht Hvsz).
  unfold sbv2int in *.
  rewrite HPow_n in *.
  change (bv2int t) with T in *.
  change (bv2int v) with V in *.
  change (bv2int x_s) with X in *.
  (* Non-empty witnesses *)
  assert (Hskip_t_ne : skipn kn t <> []).
  { intro H. apply length_zero_iff_nil in H. rewrite length_skipn in H. lia. }
  assert (Hskip_xs_ne : skipn kn x_s <> []).
  { intro H. apply length_zero_iff_nil in H. rewrite length_skipn in H. lia. }
  assert (Hv_ne : v <> []).
  { intro H. apply length_zero_iff_nil in H. lia. }
  assert (Ht_ne : t <> []).
  { intro H. apply length_zero_iff_nil in H. lia. }
  assert (Hxs_ne : x_s <> []).
  { intro H. apply length_zero_iff_nil in H. lia. }
  (* last(skipn kn t) = last t *)
  assert (Hlast_t_skip : last (skipn kn t) false = last t false).
  { rewrite <- (firstn_skipn kn t) at 2.
    rewrite last_append; [reflexivity | exact Hskip_t_ne]. }
  assert (Hlast_xs_skip : last (skipn kn x_s) false = last x_s false).
  { rewrite <- (firstn_skipn kn x_s) at 2.
    rewrite last_append; [reflexivity | exact Hskip_xs_ne]. }
  (* Case split on last t and last v *)
  destruct (last t false) eqn:Hlast_t; destruct (last v false) eqn:Hlast_v.
  - (* last t = true, last v = true: need T - P < V - P, i.e., T < V *)
    destruct (Z.lt_ge_cases (Pk * (Tk + 1)) P) as [HPlt | HPge].
    + assert (HV_eq : V = (Pk * (Tk + 1))%Z).
      { rewrite HV_formula. apply Z.mod_small. lia. }
      lia.
    + assert (HPge_eq : (Pk * (Tk + 1) = P)%Z) by nia.
      assert (HV_eq : V = 0%Z).
      { rewrite HV_formula, HPge_eq. apply Z.mod_same. lia. }
      pose proof (last_true_list2int_lb Hv_ne Hlast_v) as HV_half.
      rewrite Hlen_v_eq in HV_half. fold V in HV_half.
      lia.
  - (* last t = true, last v = false: T - P < V since T - P < 0 ≤ V *)
    lia.
  - (* last t = false, last v = true: contradiction from Hxs *)
    exfalso.
    pose proof (last_false_list2int_ub Ht_ne Hlast_t) as HT_half.
    rewrite Hlen_eq in HT_half. fold T in HT_half.
    (* Pk*(Tk+1) ≤ Pk*pow2_int(h-1) = pow2_int(hk-1) *)
    assert (HTk_ub2 : (Tk < pow2_int (h - 1)%nat)%Z) by nia.
    assert (HPk_Tk1_ub : (Pk * (Tk + 1) <= pow2_int (hk - 1)%nat)%Z).
    { rewrite <- HPk_Ph1. nia. }
    assert (HPk_Tk1_lt_P : (Pk * (Tk + 1) < P)%Z) by lia.
    assert (HV_eq : V = (Pk * (Tk + 1))%Z).
    { rewrite HV_formula. apply Z.mod_small. lia. }
    pose proof (last_true_list2int_lb Hv_ne Hlast_v) as HV_half.
    rewrite Hlen_v_eq in HV_half. fold V in HV_half.
    destruct (last x_s false) eqn:Hlast_xs.
    + (* last x_s = true: X - P < 0 ≤ T, but Hxs says T < X - P *)
      lia.
    + (* last x_s = false: Xu < pow2_int(h-1) *)
      pose proof (last_false_list2int_ub Hskip_xs_ne) as HXu_half.
      rewrite length_skipn, Hlen_xs_eq in HXu_half.
      specialize (HXu_half Hlast_xs_skip).
      assert (HhkSub : (hk - kn = h)%nat) by (unfold hk; lia).
      rewrite HhkSub in HXu_half. fold Xu in HXu_half.
      (* HXu_half : Xu < pow2_int(h-1) *)
      (* Hxs: T < X = Pk*Xu (last t=false, last x_s=false) *)
      nia.
  - (* last t = false, last v = false: T < V *)
    pose proof (last_false_list2int_ub Ht_ne Hlast_t) as HT_half.
    rewrite Hlen_eq in HT_half. fold T in HT_half.
    assert (HTk_ub2 : (Tk < pow2_int (h - 1)%nat)%Z) by nia.
    assert (HPk_Tk1_ub : (Pk * (Tk + 1) <= pow2_int (hk - 1)%nat)%Z).
    { rewrite <- HPk_Ph1. nia. }
    assert (HPk_Tk1_lt_P : (Pk * (Tk + 1) < P)%Z) by lia.
    assert (HV_eq : V = (Pk * (Tk + 1))%Z).
    { rewrite HV_formula. apply Z.mod_small. lia. }
    nia.
Qed.

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
  (bv2nat_a (bv_mult s t) = (bv2nat_a s * bv2nat_a t) mod 2^(N.to_nat n))%nat.
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
    apply Nat2Z.inj_lt. exact (bv2nat_a_lt_pow2 (bv_mult_size Hs Ht)).
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

Lemma bv_udiv_zeros : forall (n : N) (s : bitvector),
  size s = n -> bv_udiv s (zeros n) = ones n.
Proof.
  intros n s Hs.
  unfold bv_udiv. rewrite Hs, zeros_size, N.eqb_refl.
  unfold udiv_list, zeros. rewrite length_mk_list_false, List_eq_refl.
  unfold ones. rewrite (size_to_length Hs). reflexivity.
Qed.

Lemma bv2nat_a_ones : forall (n : N),
  (bv2nat_a (ones n) = 2^(N.to_nat n) - 1)%nat.
Proof.
  intro n. unfold bv2nat_a, list2nat_be_a, ones. apply pow_eqb_0.
Qed.

Lemma bv2nat_a_zeros_eq : forall (n : N),
  (bv2nat_a (zeros n) = 0)%nat.
Proof.
  intro n. unfold bv2nat_a, list2nat_be_a, zeros.
  rewrite list2N_mk_list_false. reflexivity.
Qed.

Lemma bv2nat_a_one : forall (n : N),
  (0 < N.to_nat n)%nat -> (bv2nat_a (one n) = 1)%nat.
Proof.
  intros n Hn.
  unfold bv2nat_a, list2nat_be_a, one.
  assert (H : N.to_nat n = S (N.to_nat n - 1)) by lia.
  rewrite H. rewrite rev_mk_list_one_succ. simpl.
  rewrite listE. reflexivity.
Qed.

Lemma bv_udiv_one : forall (n : N) (s : bitvector),
  size s = n -> (0 < N.to_nat n)%nat -> bv_udiv s (one n) = s.
Proof.
  intros n s Hs Hn.
  pose proof (size_to_length Hs) as Hlen_s.
  pose proof (size_to_length (one_size n)) as Hlen_one.
  assert (Hone_val : list2N (one n) = 1%N).
  { pose proof (bv2nat_a_one Hn) as H.
    unfold bv2nat_a, list2nat_be_a in H.
    apply N2Nat.inj. simpl. exact H. }
  assert (Hne : one n <> zeros n).
  { intro Heq. apply (f_equal bv2nat_a) in Heq.
    rewrite bv2nat_a_one, bv2nat_a_zeros_eq in Heq. discriminate. exact Hn. }
  unfold bv_udiv. rewrite Hs, one_size, N.eqb_refl.
  unfold udiv_list.
  assert (Hbeq : beq_list (one n) (mk_list_false (length (one n))) = false).
  { apply List_neq2. rewrite Hlen_one. unfold zeros in Hne. exact Hne. }
  rewrite Hbeq, Hone_val, N.div_1_r.
  apply N2List_list2N.
Qed.

Lemma bv2nat_a_shr_one : forall (n : N) (s : bitvector),
  size s = n -> (0 < N.to_nat n)%nat ->
  (bv2nat_a (bv_shr s (one n)) = bv2nat_a s / 2)%nat.
Proof.
  intros n s Hs Hn.
  pose proof (size_to_length Hs) as Hlen_s.
  rewrite bv_shr_eq_shr_n_bits by (rewrite Hs; symmetry; apply one_size).
  rewrite (bv2nat_a_one Hn).
  rewrite bv_shr_aux_eq.
  unfold bv2nat_a, list2nat_be_a, shr_n_bits_a.
  destruct (1 <? length s)%nat eqn:Hltb.
  - destruct s as [| b rest].
    + simpl in Hltb. discriminate.
    + simpl skipn. simpl (mk_list_false 1).
      pose proof (list2N_app_false rest) as Happ.
      rewrite Happ.
      assert (Hdiv : list2N rest = N.div (list2N (b :: rest)) 2).
      { destruct b; simpl list2N.
        - rewrite <- N.div2_div. symmetry. apply N.div2_succ_double.
        - rewrite <- N.div2_div. symmetry. apply N.div2_double. }
      rewrite Hdiv. rewrite N2Nat.inj_div. simpl (N.to_nat 2). reflexivity.
  - rewrite listE. simpl.
    destruct s as [| b [| b2 rest]].
    + simpl in Hlen_s. lia.
    + destruct b; simpl; lia.
    + simpl in Hltb. discriminate.
Qed.

Lemma bv2nat_a_nat2bv_two : forall (n : N),
  (2 <= N.to_nat n)%nat -> (bv2nat_a (nat2bv 2 n) = 2)%nat.
Proof.
  intros n Hn.
  unfold bv2nat_a, list2nat_be_a, nat2bv.
  rewrite list2N_N2List_s.
  - reflexivity.
  - apply Nat.leb_le. simpl. exact Hn.
Qed.

Lemma bv_sle_udiv_nonneg : forall (n : N) (s x : bitvector),
  size s = n -> size x = n -> last s false = false ->
  bv_sle (bv_udiv s x) s = true.
Proof.
  intros n s x Hs Hx Hlast_s.
  destruct (N.eq_dec n 0) as [Hn0 | Hn0].
  - rewrite Hn0 in Hs, Hx. pose proof (size_to_length Hs) as Hls. simpl in Hls.
    apply length_zero_iff_nil in Hls. subst s.
    pose proof (size_to_length (bv_udiv_size Hs Hx)) as Hludiv.
    simpl in Hludiv. apply length_zero_iff_nil in Hludiv.
    rewrite Hludiv. apply bv_sle_refl.
  - assert (Hn : (0 < N.to_nat n)%nat).
    { destruct n. contradiction. simpl. lia. }
    destruct (bv_eq x (zeros n)) eqn:Hxzero.
    + apply bv_eq_reflect in Hxzero. subst x.
      rewrite bv_udiv_zeros by exact Hs.
      apply neg_sle_pos with (n := n).
      * apply ones_size.
      * exact Hs.
      * unfold ones. apply last_mk_list_true. lia.
      * exact Hlast_s.
    + assert (Hx_ne : x <> zeros n).
      { intro Heq. rewrite Heq, bv_eq_refl in Hxzero. discriminate. }
      pose proof (bv2nat_a_udiv_nonzero Hs Hx Hx_ne) as Hudiv_eq.
      assert (Hudiv_le : (bv2nat_a (bv_udiv s x) <= bv2nat_a s)%nat).
      { rewrite Hudiv_eq.
        destruct (bv2nat_a x).
        - simpl. lia.
        - transitivity (bv2nat_a s / 1)%nat.
          + apply Nat.div_le_compat_l. lia.
          + rewrite Nat.div_1_r. lia. }
      destruct (last (bv_udiv s x) false) eqn:Hlast_udiv.
      * apply neg_sle_pos with (n := n).
        -- exact (bv_udiv_size Hs Hx).
        -- exact Hs.
        -- exact Hlast_udiv.
        -- exact Hlast_s.
      * rewrite (bv_sle_ule_equiv_when_msb_zero Hlast_udiv Hlast_s).
        apply not_bv_ugt_implies_bv_ule.
        -- rewrite (bv_udiv_size Hs Hx). symmetry. exact Hs.
        -- apply Bool.not_true_is_false. intro Hugt.
           apply bv_ugt_bv_ult in Hugt.
           rewrite bv_ult_nat in Hugt.
           ++ apply Nat.ltb_lt in Hugt. lia.
           ++ apply N.eqb_eq. rewrite (bv_udiv_size Hs Hx). exact Hs.
Qed.

Lemma bv_sle_udiv_shr : forall (n : N) (s x : bitvector),
  size s = n -> size x = n -> (0 < N.to_nat n)%nat ->
  last s false = true ->
  bv_sle (bv_udiv s x) (bv_shr s (one n)) = true.
Proof.
  intros n s x Hs Hx Hn Hlast_s.
  assert (Hlast_shr : last (bv_shr s (one n)) false = false).
  { apply last_bv_shr_pos with (n := n).
    - exact Hs.
    - apply one_size.
    - rewrite bv2nat_a_one by exact Hn. lia. }
  pose proof (bv_shr_size Hs (one_size n)) as Hshr_size.
  destruct (bv_eq x (zeros n)) eqn:Hxzero.
  - apply bv_eq_reflect in Hxzero. subst x.
    rewrite bv_udiv_zeros by exact Hs.
    apply neg_sle_pos with (n := n).
    + apply ones_size.
    + exact Hshr_size.
    + unfold ones. apply last_mk_list_true. lia.
    + exact Hlast_shr.
  - assert (Hx_ne : x <> zeros n).
    { intro Heq. rewrite Heq, bv_eq_refl in Hxzero. discriminate. }
    pose proof (bv2nat_a_udiv_nonzero Hs Hx Hx_ne) as Hudiv_eq.
    assert (Hshr_val : (bv2nat_a (bv_shr s (one n)) = bv2nat_a s / 2)%nat)
      by (apply bv2nat_a_shr_one; [exact Hs | exact Hn]).
    destruct (last (bv_udiv s x) false) eqn:Hlast_udiv.
    + apply neg_sle_pos with (n := n).
      * exact (bv_udiv_size Hs Hx).
      * exact Hshr_size.
      * exact Hlast_udiv.
      * exact Hlast_shr.
    + (* Both non-negative. Need bv2nat_a(udiv) ≤ bv2nat_a(shr) = S/2.
         Since udiv is non-negative: bv2nat_a(udiv) = S/X < 2^(n-1).
         Since s is negative: bv2nat_a(s) >= 2^(n-1).
         So S/X < 2^(n-1) <= S, hence X >= 2, hence S/X <= S/2. *)
      rewrite (bv_sle_ule_equiv_when_msb_zero Hlast_udiv Hlast_shr).
      apply not_bv_ugt_implies_bv_ule.
      * rewrite (bv_udiv_size Hs Hx), Hshr_size. reflexivity.
      * apply Bool.not_true_is_false. intro Hugt.
        apply bv_ugt_bv_ult in Hugt.
        rewrite bv_ult_nat in Hugt.
        -- apply Nat.ltb_lt in Hugt.
           (* Hugt : bv2nat_a(shr) < bv2nat_a(udiv), i.e. S/2 < S/X *)
           (* But S/X <= S/2: we need X <= 2... *)
           (* bv2nat_a(udiv) = S/X. bv2nat_a(shr) = S/2. S/2 < S/X means X < 2, so X = 1. *)
           (* X = 1 means udiv = s (last = true), contradicting Hlast_udiv = false. *)
           assert (Hbv2_x : (bv2nat_a x = 1)%nat).
           { rewrite Hudiv_eq in Hugt. rewrite Hshr_val in Hugt.
             assert (Hxne0 : (bv2nat_a x <> 0)%nat).
             { intro H0. apply Hx_ne.
               apply bv2nat_a_inj with (n := n); [exact Hx | apply zeros_size |].
               rewrite bv2nat_a_zeros_eq. exact H0. }
             remember (bv2nat_a x) as xv eqn:Hxv.
             destruct xv as [| [| k]].
             - contradiction.
             - reflexivity.
             - exfalso.
               assert (Hle : (bv2nat_a s / S (S k) <= bv2nat_a s / 2)%nat).
               { apply Nat.div_le_compat_l. lia. }
               lia. }
           (* bv2nat_a x = 1 means x = one n... but wait, we have bv2nat_a(udiv) = S/1 = S *)
           (* and last(s) = true but last(udiv) = false. But bv_udiv s x = N2list(S/1)(n) = N2list(S)(n) = s *)
           (* And last(s) = true, contradicting Hlast_udiv = false. *)
           assert (Heq : bv_udiv s x = s).
           { apply bv2nat_a_inj with (n := n).
             - exact (bv_udiv_size Hs Hx).
             - exact Hs.
             - rewrite Hudiv_eq, Hbv2_x, Nat.div_1_r. reflexivity. }
           rewrite Heq in Hlast_udiv. rewrite Hlast_s in Hlast_udiv. discriminate.
        -- apply N.eqb_eq. rewrite (bv_udiv_size Hs Hx), Hshr_size. reflexivity.
Qed.

(* bv2int of bv_not: P - 1 - bv2int a *)
Lemma bv2int_bv_not : forall n (a : bitvector),
  size a = n ->
  (bv2int (bv_not a) = pow2_int_N n - 1 - bv2int a)%Z.
Proof.
  intros n a Ha.
  unfold bv2int, bv_not, bits.
  pose proof (list2int_map_negb_sum a) as Hsum.
  assert (Hlen : pow2_int (length a) = pow2_int_N n).
  { unfold pow2_int_N. f_equal. unfold size in Ha. lia. }
  lia.
Qed.

(* bv2int of bv_neg: (P - bv2int a) mod P *)
Lemma bv2int_bv_neg : forall (a : bitvector),
  (bv2int (bv_neg a) = (pow2_int_N (size a) - bv2int a) mod pow2_int_N (size a))%Z.
Proof.
  intro a.
  unfold bv2int, bv_neg, bits.
  rewrite list2int_twos_complement.
  pose proof (list2int_map_negb_sum a) as Hsum.
  assert (Hlen : pow2_int (length a) = pow2_int_N (size a)).
  { unfold pow2_int_N, size. rewrite Nat2N.id. reflexivity. }
  rewrite Hlen in Hsum |- *.
  assert (H : (list2int (map negb a) + 1)%Z = (pow2_int_N (size a) - list2int a)%Z) by lia.
  rewrite H. reflexivity.
Qed.

(* bv2int of signed_min: 2^(n-1) *)
Lemma bv2int_signed_min : forall (n : N),
  (0 < n)%N ->
  (bv2int (signed_min n) = pow2_int_N (n - 1)%N)%Z.
Proof.
  intros n Hn.
  pose proof (signed_min_struct Hn) as Hstruct.
  unfold bv2int. rewrite Hstruct.
  rewrite list2int_app. simpl list2int. simpl bool2int.
  rewrite list2int_mk_list_false. simpl (0 + _)%Z.
  unfold pow2_int_N.
  assert (HN : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat).
  { rewrite N2Nat.inj_sub. simpl N.to_nat. lia. }
  rewrite HN.
  rewrite length_mk_list_false. ring.
Qed.

(* a <=u (a | b) *)
Lemma bv_ule_bv_or_l : forall n (a b : bitvector),
  size a = n -> size b = n ->
  bv_ule a (bv_or a b) = true.
Proof.
  intros n a b Ha Hb.
  assert (Hlen : length a = length b) by (apply size_len_eq; rewrite Ha, Hb; reflexivity).
  assert (Hlen_map2 : length (map2 orb a b) = length a) by (symmetry; apply map2_or_length; exact Hlen).
  assert (Hrev_eq : rev (map2 orb a b) = map2 orb (rev a) (rev b)).
  { apply nth_ext with (d := false) (d' := false).
    - rewrite length_rev, Hlen_map2.
      assert (H2 : length (map2 orb (rev a) (rev b)) = length (rev a))
        by (symmetry; apply map2_or_length; rewrite !length_rev; exact Hlen).
      rewrite H2, length_rev. reflexivity.
    - intros i Hi.
      assert (Hi_bound : (i < length (map2 orb a b))%nat)
        by (rewrite length_rev in Hi; exact Hi).
      rewrite (rev_nth (map2 orb a b) false Hi_bound).
      assert (Hi_lhs : (length (map2 orb a b) - S i <= length a)%nat)
        by (rewrite Hlen_map2; lia).
      rewrite (@map2_or_nth_bitOf a b (length (map2 orb a b) - S i)%nat Hlen Hi_lhs).
      rewrite Hlen_map2.
      assert (Hi_rhs_len : length (rev a) = length (rev b))
        by (rewrite !length_rev; exact Hlen).
      assert (Hi_rhs_bound : (i <= length (rev a))%nat)
        by (rewrite length_rev; rewrite length_rev in Hi; lia).
      rewrite (@map2_or_nth_bitOf (rev a) (rev b) i Hi_rhs_len Hi_rhs_bound).
      assert (Hi_a : (i < length a)%nat) by (rewrite length_rev in Hi; lia).
      rewrite (rev_nth a false Hi_a).
      assert (Hi_b : (i < length b)%nat) by lia.
      rewrite (rev_nth b false Hi_b), <- Hlen. reflexivity. }
  unfold bv_ule, bv_or, bits.
  rewrite Ha, Hb, N.eqb_refl.
  assert (Hbvor_size : (n =? size (map2 orb a b)) = true).
  { apply N.eqb_eq. unfold size. rewrite Hlen_map2. unfold size in Ha. lia. }
  rewrite Hbvor_size.
  unfold ule_list.
  rewrite Hrev_eq.
  apply ule_list_big_endian_or.
  rewrite !length_rev. exact Hlen.
Qed.

(* bv_urem x (zeros n) = x *)
Lemma bv_urem_zeros_s : forall n (x : bitvector),
  size x = n -> bv_urem x (zeros n) = x.
Proof.
  intros n x Hx.
  unfold bv_urem, urem_list, bits.
  rewrite Hx, zeros_size, N.eqb_refl.
  assert (Hbeq : beq_list (zeros n) (mk_list_false (length (zeros n))) = true).
  { unfold zeros. rewrite length_mk_list_false. apply List_eq_refl. }
  rewrite Hbeq. reflexivity.
Qed.

(* bv_urem (zeros n) s = zeros n *)
Lemma bv_urem_zeros_l : forall n (s : bitvector),
  size s = n -> bv_urem (zeros n) s = zeros n.
Proof.
  intros n s Hs.
  unfold bv_urem, urem_list, bits.
  rewrite zeros_size, Hs, N.eqb_refl. simpl.
  destruct (beq_list s (mk_list_false (length s))) eqn:Hbeq.
  - reflexivity.
  - unfold zeros. rewrite listE. rewrite N.Div0.mod_0_l.
    unfold N2list. simpl. rewrite length_mk_list_false. reflexivity.
Qed.

(* bv2nat_a of bv_urem when s ≠ zeros *)
Lemma bv2nat_a_urem_nonzero : forall (n : N) (x s : bitvector),
  size x = n -> size s = n -> s <> zeros n ->
  (bv2nat_a (bv_urem x s) = bv2nat_a x mod bv2nat_a s)%nat.
Proof.
  intros n x s Hx Hs Hsne.
  unfold bv2nat_a, list2nat_be_a, bv_urem, urem_list.
  pose proof (size_to_length Hx) as Hlen_x.
  pose proof (size_to_length Hs) as Hlen_s.
  rewrite Hx, Hs, N.eqb_refl.
  assert (Hbeq : beq_list s (mk_list_false (length s)) = false).
  { apply List_neq2. intro Heq. apply Hsne. unfold zeros. now rewrite <- Hlen_s. }
  rewrite Hbeq, Hlen_x.
  assert (Hs_ne : list2N s <> 0%N).
  { intro H. apply Hsne. unfold zeros. rewrite <- Hlen_s.
    apply list2N_0_implies_mlf. rewrite H. reflexivity. }
  rewrite list2N_N2List_s; [rewrite N2Nat.inj_mod; reflexivity |].
  apply Nat.leb_le. apply N_size_le_nat.
  apply Nat.le_lt_trans with (m := N.to_nat (list2N x)).
  - rewrite N2Nat.inj_mod. apply Nat.Div0.mod_le.
  - pose proof (pow_gt x) as Hpg. apply Nat.ltb_lt in Hpg.
    rewrite Hlen_x in Hpg. exact Hpg.
Qed.

(* bv_urem x s <_u s when s ≠ zeros *)
Lemma bv_urem_ult_s : forall (n : N) (x s : bitvector),
  size x = n -> size s = n -> s <> zeros n ->
  bv_ult (bv_urem x s) s = true.
Proof.
  intros n x s Hx Hs Hsne.
  pose proof (bv_urem_size Hx Hs) as Hurem_size.
  rewrite bv_ult_nat; [| rewrite Hurem_size, Hs; apply N.eqb_refl].
  apply Nat.ltb_lt.
  rewrite (bv2nat_a_urem_nonzero Hx Hs Hsne).
  apply Nat.mod_upper_bound.
  intro H. apply Hsne.
  apply bv2nat_a_inj with (n := n); [exact Hs | apply zeros_size |].
  rewrite H, bv2nat_a_zeros_eq. reflexivity.
Qed.

(* last of bv_neg is true when input is positive-nonzero *)
Lemma last_bv_neg_pos : forall n (s : bitvector),
  size s = n -> (0 < n)%N ->
  last s false = false -> s <> zeros n ->
  last (bv_neg s) false = true.
Proof.
  intros n s Hs Hn Hlast_s Hsne.
  assert (Hs_ne : s <> []) by (intro H; rewrite H in Hs; unfold size in Hs; simpl in Hs; lia).
  assert (Hneg_size : size (bv_neg s) = n) by (apply bv_neg_size; exact Hs).
  assert (Hneg_ne : bv_neg s <> [])
    by (intro H; rewrite H in Hneg_size; unfold size in Hneg_size; simpl in Hneg_size; lia).
  assert (Hlen_s : length s = N.to_nat n) by (apply size_to_length; exact Hs).
  assert (Hneg_len : length (bv_neg s) = N.to_nat n)
    by (apply size_to_length; exact Hneg_size).
  assert (Hge : (0 <= bv2int s)%Z) by (unfold bv2int; apply list2int_geq_zero).
  assert (Hub : (bv2int s < pow2_int (N.to_nat n - 1))%Z).
  { pose proof (last_false_list2int_ub Hs_ne Hlast_s) as Htmp.
    rewrite Hlen_s in Htmp. exact Htmp. }
  assert (Hne0 : bv2int s <> 0%Z).
  { intro H. apply Hsne.
    apply bv2nat_a_inj with (n := n); [exact Hs | apply zeros_size |].
    apply Nat2Z.inj.
    rewrite <- (bv2int_eq_Z_of_nat_bv2nat_a s), <- (bv2int_eq_Z_of_nat_bv2nat_a (zeros n)).
    rewrite H. symmetry. apply bv2int_zeros. }
  assert (Hn_nat : (N.to_nat n = S (N.to_nat n - 1))%nat) by lia.
  assert (Hpow_split : pow2_int_N n = (2 * pow2_int (N.to_nat n - 1))%Z).
  { unfold pow2_int_N. rewrite Hn_nat at 1. apply pow2_int_succ. }
  assert (Hlt_pow : (bv2int s < pow2_int_N n)%Z) by lia.
  assert (Hbv2int_neg : (bv2int (bv_neg s) = pow2_int_N n - bv2int s)%Z).
  { pose proof (bv2int_bv_neg s) as H. rewrite Hs in H.
    rewrite H. apply Z.mod_small. split; lia. }
  destruct (last (bv_neg s) false) eqn:Hlast_neg; [reflexivity |].
  exfalso.
  assert (Hfub : (bv2int (bv_neg s) < pow2_int (N.to_nat n - 1))%Z).
  { pose proof (last_false_list2int_ub Hneg_ne Hlast_neg) as Htmp.
    rewrite Hneg_len in Htmp. exact Htmp. }
  set (P := pow2_int (N.to_nat n - 1)) in *.
  lia.
Qed.

(* last of bv_neg is false when input is negative and not signed_min *)
Lemma last_bv_neg_neg_nonmin : forall n (s : bitvector),
  size s = n -> (0 < n)%N ->
  last s false = true -> s <> signed_min n ->
  last (bv_neg s) false = false.
Proof.
  intros n s Hs Hn Hlast_s Hne_min.
  assert (Hs_ne : s <> []) by (intro H; rewrite H in Hs; unfold size in Hs; simpl in Hs; lia).
  assert (Hneg_size : size (bv_neg s) = n) by (apply bv_neg_size; exact Hs).
  assert (Hneg_ne : bv_neg s <> [])
    by (intro H; rewrite H in Hneg_size; unfold size in Hneg_size; simpl in Hneg_size; lia).
  assert (Hlen_s : length s = N.to_nat n) by (apply size_to_length; exact Hs).
  assert (Hneg_len : length (bv_neg s) = N.to_nat n)
    by (apply size_to_length; exact Hneg_size).
  assert (HNN : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat).
  { rewrite N2Nat.inj_sub. simpl N.to_nat. lia. }
  assert (Hpow_split : pow2_int_N n = (2 * pow2_int (N.to_nat n - 1))%Z).
  { unfold pow2_int_N. assert (Hn_nat : N.to_nat n = S (N.to_nat n - 1)) by lia.
    rewrite Hn_nat at 1. apply pow2_int_succ. }
  assert (Hlt_pow : (bv2int s < pow2_int_N n)%Z).
  { unfold bv2int, pow2_int_N. rewrite <- Hlen_s. apply list2int_lt_pow2_int. reflexivity. }
  assert (Hlb : (pow2_int (N.to_nat n - 1) <= bv2int s)%Z).
  { pose proof (last_true_list2int_lb Hs_ne Hlast_s) as Htmp.
    rewrite Hlen_s in Htmp. exact Htmp. }
  assert (Hbv2int_ne : bv2int s <> pow2_int (N.to_nat n - 1)).
  { intro Heq. apply Hne_min.
    apply bv2nat_a_inj with (n := n); [exact Hs | apply signed_min_size |].
    apply Nat2Z.inj.
    rewrite <- (bv2int_eq_Z_of_nat_bv2nat_a s), <- (bv2int_eq_Z_of_nat_bv2nat_a (signed_min n)).
    pose proof (bv2int_signed_min Hn) as Hsmin.
    rewrite Heq, Hsmin. unfold pow2_int_N. rewrite HNN. reflexivity. }
  assert (Hgt : (pow2_int (N.to_nat n - 1) < bv2int s)%Z) by lia.
  assert (Hbv2int_neg : (bv2int (bv_neg s) = pow2_int_N n - bv2int s)%Z).
  { pose proof (bv2int_bv_neg s) as H. rewrite Hs in H.
    rewrite H. apply Z.mod_small. split; lia. }
  destruct (last (bv_neg s) false) eqn:Hlast_neg; [| reflexivity].
  exfalso.
  assert (Htlb : (pow2_int (N.to_nat n - 1) <= bv2int (bv_neg s))%Z).
  { pose proof (last_true_list2int_lb Hneg_ne Hlast_neg) as Htmp.
    rewrite Hneg_len in Htmp. exact Htmp. }
  set (P := pow2_int (N.to_nat n - 1)) in *.
  lia.
Qed.

(* sbv2int of bv_not: -(sbv2int t) - 1 *)
Lemma sbv2int_bv_not : forall n (t : bitvector),
  size t = n -> (0 < n)%N ->
  (sbv2int n (bv_not t) = -sbv2int n t - 1)%Z.
Proof.
  intros n t Ht Hn.
  assert (Hne : t <> []) by (intro H; rewrite H in Ht; unfold size in Ht; simpl in Ht; lia).
  assert (Hlast_not : last (bv_not t) false = negb (last t false)).
  { unfold bv_not, bits. apply last_map_negb. exact Hne. }
  unfold sbv2int. rewrite Hlast_not, (bv2int_bv_not Ht).
  destruct (last t false); simpl; ring.
Qed.

(* sbv2int of bv_neg when t ≠ signed_min: exact negation *)
Lemma sbv2int_bv_neg_nonmin : forall n (t : bitvector),
  size t = n -> (0 < n)%N -> t <> signed_min n ->
  (sbv2int n (bv_neg t) = -sbv2int n t)%Z.
Proof.
  intros n t Ht Hn Hne_min.
  assert (Ht_ne : t <> []) by (intro H; rewrite H in Ht; unfold size in Ht; simpl in Ht; lia).
  assert (Hneg_size : size (bv_neg t) = n) by (apply bv_neg_size; exact Ht).
  assert (Hlen_t : length t = N.to_nat n) by (apply size_to_length; exact Ht).
  assert (Hlt_pow : (bv2int t < pow2_int_N n)%Z).
  { unfold bv2int, pow2_int_N. rewrite <- Hlen_t. apply list2int_lt_pow2_int. reflexivity. }
  assert (HNN : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat).
  { rewrite N2Nat.inj_sub. simpl N.to_nat. lia. }
  assert (Hpow_split : pow2_int_N n = (2 * pow2_int (N.to_nat n - 1))%Z).
  { unfold pow2_int_N. assert (Hn_nat : N.to_nat n = S (N.to_nat n - 1)) by lia.
    rewrite Hn_nat at 1. apply pow2_int_succ. }
  unfold sbv2int.
  destruct (last t false) eqn:Hlast_t.
  - (* t is negative: last t = true *)
    assert (Hlb : (pow2_int (N.to_nat n - 1) <= bv2int t)%Z).
    { pose proof (last_true_list2int_lb Ht_ne Hlast_t) as Htmp.
      rewrite Hlen_t in Htmp. exact Htmp. }
    assert (Hbv2int_ne : bv2int t <> pow2_int (N.to_nat n - 1)).
    { intro Heq. apply Hne_min.
      apply bv2nat_a_inj with (n := n); [exact Ht | apply signed_min_size |].
      apply Nat2Z.inj.
      rewrite <- (bv2int_eq_Z_of_nat_bv2nat_a t), <- (bv2int_eq_Z_of_nat_bv2nat_a (signed_min n)).
      pose proof (bv2int_signed_min Hn) as Hsmin.
      rewrite Heq, Hsmin. unfold pow2_int_N. rewrite HNN. reflexivity. }
    assert (Hgt : (pow2_int (N.to_nat n - 1) < bv2int t)%Z) by lia.
    assert (Hmod_eq : ((pow2_int_N n - bv2int t) mod pow2_int_N n = pow2_int_N n - bv2int t)%Z).
    { apply Z.mod_small. split; lia. }
    pose proof (bv2int_bv_neg t) as Hneg_eq.
    rewrite Ht in Hneg_eq. rewrite Hmod_eq in Hneg_eq.
    rewrite (last_bv_neg_neg_nonmin Ht Hn Hlast_t Hne_min).
    rewrite Hneg_eq. ring.
  - (* t is non-negative: last t = false *)
    destruct (Z.eq_dec (bv2int t) 0) as [Hzero | Hpos_ne].
    + (* bv2int t = 0 → t = zeros n *)
      assert (Ht_zeros : t = zeros n).
      { apply bv2nat_a_inj with (n := n); [exact Ht | apply zeros_size |].
        apply Nat2Z.inj.
        rewrite <- (bv2int_eq_Z_of_nat_bv2nat_a t), <- (bv2int_eq_Z_of_nat_bv2nat_a (zeros n)).
        rewrite Hzero. symmetry. apply bv2int_zeros. }
      rewrite Ht_zeros, bv_neg_zeros_zeros.
      assert (Hlz : last (zeros n) false = false) by (unfold zeros; apply last_mk_list_false).
      rewrite Hlz. simpl. rewrite bv2int_zeros. ring.
    + (* bv2int t ≠ 0 → t ≠ zeros n *)
      assert (Ht_ne_zeros : t <> zeros n).
      { intro Heq. apply Hpos_ne. rewrite Heq. apply bv2int_zeros. }
      assert (Hge : (0 <= bv2int t)%Z) by (unfold bv2int; apply list2int_geq_zero).
      assert (Hub : (bv2int t < pow2_int (N.to_nat n - 1))%Z).
      { pose proof (last_false_list2int_ub Ht_ne Hlast_t) as Htmp.
        rewrite Hlen_t in Htmp. exact Htmp. }
      assert (Hmod_eq : ((pow2_int_N n - bv2int t) mod pow2_int_N n = pow2_int_N n - bv2int t)%Z).
      { apply Z.mod_small. split; lia. }
      pose proof (bv2int_bv_neg t) as Hneg_eq.
      rewrite Ht in Hneg_eq. rewrite Hmod_eq in Hneg_eq.
      rewrite (last_bv_neg_pos Ht Hn Hlast_t Ht_ne_zeros).
      rewrite Hneg_eq. ring.
Qed.

(* bv_neg of signed_min is signed_min (overflow) *)
Lemma bv_neg_signed_min : forall n, (0 < n)%N -> bv_neg (signed_min n) = signed_min n.
Proof.
  intros n Hn.
  apply bv2nat_a_inj with (n := n);
    [apply bv_neg_size; apply signed_min_size | apply signed_min_size |].
  apply Nat2Z.inj.
  rewrite <- !bv2int_eq_Z_of_nat_bv2nat_a.
  pose proof (bv2int_bv_neg (signed_min n)) as Hneg.
  rewrite signed_min_size in Hneg. rewrite Hneg.
  pose proof (bv2int_signed_min Hn) as Hmin.
  assert (HNN : N.to_nat (n - 1)%N = (N.to_nat n - 1)%nat).
  { rewrite N2Nat.inj_sub. simpl N.to_nat. lia. }
  assert (Hpow_n : (pow2_int_N n = 2 * pow2_int_N (n - 1)%N)%Z).
  { unfold pow2_int_N. rewrite HNN.
    assert (Hn_nat : (N.to_nat n = S (N.to_nat n - 1))%nat) by lia.
    rewrite Hn_nat at 1. apply pow2_int_succ. }
  pose proof (zero_lt_pow2_int (N.to_nat (n - 1)%N)) as Hgt.
  unfold pow2_int_N in Hgt.
  rewrite Hmin, Hpow_n.
  replace (2 * pow2_int_N (n - 1) - pow2_int_N (n - 1))%Z
    with (pow2_int_N (n - 1)%N) by ring.
  apply Z.mod_small.
  unfold pow2_int_N. rewrite HNN in Hgt |- *.
  split.
  - apply Z.lt_le_incl. exact Hgt.
  - lia.
Qed.

(* list2int of bv_add t t = (2 * list2int t) mod pow2_int n *)
Lemma list2int_bv_add_twice : forall (n : N) (t : bitvector),
  size t = n ->
  (list2int (bv_add t t) = (2 * list2int t) mod pow2_int (N.to_nat n))%Z.
Proof.
  intros n t Ht.
  unfold bv_add. rewrite Ht, N.eqb_refl. unfold add_list.
  rewrite list2int_add_list_ingr; [| reflexivity].
  simpl bool2int. rewrite Z.add_0_r.
  rewrite (size_to_length Ht).
  replace (list2int t + list2int t)%Z with (2 * list2int t)%Z by ring.
  reflexivity.
Qed.

(* list2int of bv_subt a b = (list2int a - list2int b + pow2_int n) mod pow2_int n *)
Lemma list2int_bv_subt : forall (n : N) (a b : bitvector),
  size a = n -> size b = n ->
  (list2int (bv_subt a b) = (list2int a - list2int b + pow2_int (N.to_nat n)) mod pow2_int (N.to_nat n))%Z.
Proof.
  intros n a b Ha Hb.
  unfold bv_subt. rewrite Ha, Hb, N.eqb_refl. unfold bits.
  assert (Hlen : length a = length b).
  { pose proof (size_to_length Ha) as H1. pose proof (size_to_length Hb) as H2. lia. }
  rewrite <- (size_to_length Ha).
  apply list2int_subst_list_formula. exact Hlen.
Qed.

(* Inclusion-exclusion: list2int(bv_and a b) + list2int(bv_or a b) = list2int a + list2int b *)
Lemma list2int_bv_and_or_sum : forall (n : N) (a b : bitvector),
  size a = n -> size b = n ->
  (list2int (bv_and a b) + list2int (bv_or a b) = list2int a + list2int b)%Z.
Proof.
  intros n a b Ha Hb.
  assert (Hlen : length a = length b).
  { pose proof (size_to_length Ha) as H1. pose proof (size_to_length Hb) as H2. lia. }
  unfold bv_and, bv_or. rewrite Ha, Hb, N.eqb_refl. unfold bits.
  apply list2int_map2_and_or_sum. exact Hlen.
Qed.

(* bv2nat_a of bv_subt when t <=u s *)
Lemma bv2nat_a_subt_ule : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  bv_ule t s = true ->
  (bv2nat_a (bv_subt s t) = bv2nat_a s - bv2nat_a t)%nat.
Proof.
  intros n s t Hs Ht Hule.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_sub.
  - rewrite <- !bv2int_eq_Z_of_nat_bv2nat_a. unfold bv2int.
    rewrite (list2int_bv_subt Hs Ht).
    assert (HTS_le : (list2int t <= list2int s)%Z).
    { apply ule_list_list2int.
      - pose proof (size_to_length Hs) as H1. pose proof (size_to_length Ht) as H2. lia.
      - unfold bv_ule in Hule. rewrite Ht, Hs, N.eqb_refl in Hule. exact Hule. }
    pose proof (@list2int_geq_zero t) as HT_ge.
    assert (HS_lt : (list2int s < pow2_int (N.to_nat n))%Z)
      by (apply list2int_lt_pow2_int with (n := N.to_nat n); apply size_to_length; exact Hs).
    assert (HP_ne : pow2_int (N.to_nat n) <> 0%Z)
      by (pose proof (zero_lt_pow2_int (N.to_nat n)); lia).
    replace (list2int s - list2int t + pow2_int (N.to_nat n))%Z
      with (list2int s - list2int t + 1 * pow2_int (N.to_nat n))%Z by ring.
    rewrite Z.mod_add; [| exact HP_ne].
    apply Z.mod_small. lia.
  - apply Nat2Z.inj_le.
    rewrite <- !bv2int_eq_Z_of_nat_bv2nat_a. unfold bv2int.
    apply ule_list_list2int.
    + pose proof (size_to_length Hs) as H1. pose proof (size_to_length Ht) as H2. lia.
    + unfold bv_ule in Hule. rewrite Ht, Hs, N.eqb_refl in Hule. exact Hule.
Qed.

(* bv_ule a b = true ↔ bv2nat_a a ≤ bv2nat_a b *)
Lemma bv2nat_a_ule_iff : forall (n : N) (a b : bitvector),
  size a = n -> size b = n ->
  bv_ule a b = true <-> (bv2nat_a a <= bv2nat_a b)%nat.
Proof.
  intros n a b Ha Hb. split.
  - intros Hule.
    apply bv_ule_bv_uge in Hule.
    apply bv_uge_implies_not_bv_ult in Hule.
    rewrite bv_ult_nat in Hule; [| rewrite Hb, Ha; apply N.eqb_refl].
    apply Nat.ltb_ge. exact Hule.
  - intros Hle.
    apply bv_uge_bv_ule.
    apply not_bv_ult_implies_bv_uge; [congruence |].
    rewrite bv_ult_nat; [| rewrite Hb, Ha; apply N.eqb_refl].
    apply Nat.ltb_nlt. lia.
Qed.

(* bv_uge a b = true ↔ bv2nat_a b ≤ bv2nat_a a *)
Lemma bv2nat_a_uge_iff : forall (n : N) (a b : bitvector),
  size a = n -> size b = n ->
  bv_uge a b = true <-> (bv2nat_a b <= bv2nat_a a)%nat.
Proof.
  intros n a b Ha Hb. split.
  - intros Huge. apply bv_uge_bv_ule in Huge.
    apply (bv2nat_a_ule_iff Hb Ha). exact Huge.
  - intros Hle. apply bv_ule_bv_uge.
    apply (bv2nat_a_ule_iff Hb Ha). exact Hle.
Qed.

(* Inclusion-exclusion: bv2nat_a(bv_and a b) + bv2nat_a(bv_or a b) = bv2nat_a a + bv2nat_a b *)
Lemma bv2nat_a_bv_and_or_add : forall (n : N) (a b : bitvector),
  size a = n -> size b = n ->
  (bv2nat_a (bv_and a b) + bv2nat_a (bv_or a b) = bv2nat_a a + bv2nat_a b)%nat.
Proof.
  intros n a b Ha Hb.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add, <- !bv2int_eq_Z_of_nat_bv2nat_a. unfold bv2int.
  exact (list2int_bv_and_or_sum Ha Hb).
Qed.

(* list2int of bv_subt (bv_add t t) s = (2*T - S) mod P, useful for bvurem_reverse_eq *)
Lemma list2int_bv_subt_2t_s : forall (n : N) (s t : bitvector),
  size t = n -> size s = n ->
  (list2int (bv_subt (bv_add t t) s) = (2 * list2int t - list2int s) mod pow2_int (N.to_nat n))%Z.
Proof.
  intros n s t Ht Hs.
  assert (Hatt : size (bv_add t t) = n) by (apply bv_add_size; exact Ht; exact Ht).
  rewrite (list2int_bv_subt Hatt Hs), (list2int_bv_add_twice Ht).
  pose proof (zero_lt_pow2_int (N.to_nat n)) as HP_pos.
  assert (HP_ne : pow2_int (N.to_nat n) <> 0%Z) by lia.
  assert (HS_ge : (0 <= list2int s)%Z) by exact (@list2int_geq_zero s).
  assert (HS_lt : (list2int s < pow2_int (N.to_nat n))%Z)
    by (apply list2int_lt_pow2_int with (n := N.to_nat n); apply size_to_length; exact Hs).
  replace (2 * list2int t mod pow2_int (N.to_nat n) - list2int s + pow2_int (N.to_nat n))%Z
    with (2 * list2int t mod pow2_int (N.to_nat n) - list2int s + 1 * pow2_int (N.to_nat n))%Z
    by ring.
  rewrite Z.mod_add; [| exact HP_ne].
  rewrite (Zminus_mod (2 * list2int t) (list2int s) (pow2_int (N.to_nat n))).
  rewrite (Z.mod_small (list2int s) (pow2_int (N.to_nat n))); [| split; lia].
  reflexivity.
Qed.

Lemma bv_slt_not_zeros_nonneg : forall (n : N) (x : bitvector),
  (0 < n)%N -> size x = n ->
  bv_slt (bv_not (zeros n)) x = negb (last x false).
Proof.
  intros n x Hn Hx.
  assert (Hones_eq : bv_not (zeros n) = ones n).
  { unfold bv_not, zeros, ones, bits. apply not_list_false_true. }
  assert (Hones_sz : size (ones n) = n) by apply ones_size.
  assert (Hn_nat : (0 < N.to_nat n)%nat)
    by (destruct n; [simpl in Hn; lia | simpl; lia]).
  assert (Hlast_ones : last (ones n) false = true).
  { unfold ones. apply last_mk_list_true. lia. }
  rewrite Hones_eq, (bv_slt_negb_sle Hones_sz Hx).
  f_equal.
  destruct (last x false) eqn:Hlast_x.
  - assert (Hsign_eq : last x false = last (ones n) false)
      by (rewrite Hlast_x, Hlast_ones; reflexivity).
    rewrite (bv_sle_ule_same_sign Hx Hones_sz Hsign_eq).
    apply not_bv_ugt_implies_bv_ule.
    + rewrite Hx, Hones_sz. reflexivity.
    + unfold bv_ugt. rewrite Hx, Hones_sz, N.eqb_refl.
      rewrite <- Hones_eq, <- Hx. apply not_ugt_list_ones.
  - apply Bool.not_true_is_false. intro Hsle.
    exact (bv_sle_pos_neg_absurd Hn Hx Hones_sz Hlast_x Hlast_ones Hsle).
Qed.

(* bv2nat_a (bv_urem s x) <= bv2nat_a s for any x *)
Lemma bv2nat_a_urem_le_s : forall (n : N) (s x : bitvector),
  size s = n -> size x = n ->
  (bv2nat_a (bv_urem s x) <= bv2nat_a s)%nat.
Proof.
  intros n s x Hs Hx.
  destruct (bv_eq x (zeros n)) eqn:Hxeq.
  - apply bv_eq_reflect in Hxeq. subst x.
    rewrite bv_urem_zeros_s by exact Hs. lia.
  - assert (Hxne : x <> zeros n).
    { intro Heq. rewrite Heq, bv_eq_refl in Hxeq. discriminate. }
    rewrite (bv2nat_a_urem_nonzero Hs Hx Hxne).
    apply Nat.Div0.mod_le.
Qed.

(* If last s = false then last (bv_urem s x) = false *)
Lemma last_bv_urem_nonneg : forall (n : N) (s x : bitvector),
  size s = n -> size x = n -> (0 < n)%N ->
  last s false = false -> last (bv_urem s x) false = false.
Proof.
  intros n s x Hs Hx Hn Hlast_s.
  assert (Hurem_sz : size (bv_urem s x) = n) by exact (bv_urem_size Hs Hx).
  assert (Hult_s : bv_ult s (signed_min n) = true)
    by exact (nonneg_ult_signed_min Hn Hs Hlast_s).
  assert (Hs_lt : (bv2nat_a s < bv2nat_a (signed_min n))%nat).
  { rewrite bv_ult_nat in Hult_s; [| rewrite Hs, signed_min_size; apply N.eqb_refl].
    apply Nat.ltb_lt. exact Hult_s. }
  assert (Hurem_le : (bv2nat_a (bv_urem s x) <= bv2nat_a s)%nat)
    by exact (bv2nat_a_urem_le_s Hs Hx).
  assert (Hult_urem : bv_ult (bv_urem s x) (signed_min n) = true).
  { rewrite bv_ult_nat; [| rewrite Hurem_sz, signed_min_size; apply N.eqb_refl].
    apply Nat.ltb_lt. lia. }
  exact (ult_b_signed_min_implies_positive_sign Hurem_sz Hult_urem).
Qed.

(* When s is negative, bv2nat_a ((s-1)>>1) = (bv2nat_a s - 1) / 2 *)
Lemma bv2nat_a_shr_subt_one : forall (n : N) (s : bitvector),
  size s = n -> (0 < N.to_nat n)%nat -> last s false = true ->
  (bv2nat_a (bv_shr (bv_subt s (one n)) (one n)) = (bv2nat_a s - 1) / 2)%nat.
Proof.
  intros n s Hs Hn Hlast_s.
  assert (Hsubt_sz : size (bv_subt s (one n)) = n)
    by exact (bv_subt_size Hs (one_size n)).
  rewrite (bv2nat_a_shr_one Hsubt_sz Hn).
  assert (Hs_ne : s <> zeros n).
  { intro Heq. rewrite Heq in Hlast_s.
    unfold zeros in Hlast_s. rewrite last_mk_list_false in Hlast_s. discriminate. }
  assert (Hs_pos : (0 < bv2nat_a s)%nat).
  { destruct (bv2nat_a s) eqn:H0; [| lia].
    exfalso. apply Hs_ne.
    apply bv2nat_a_inj with (n := n); [exact Hs | apply zeros_size |].
    rewrite H0; symmetry; apply bv2nat_a_zeros_eq. }
  assert (Hone_le_s : bv_ule (one n) s = true).
  { apply (bv2nat_a_ule_iff (one_size n) Hs).
    rewrite bv2nat_a_one by exact Hn. lia. }
  rewrite (bv2nat_a_subt_ule Hs (one_size n) Hone_le_s).
  rewrite bv2nat_a_one by exact Hn. reflexivity.
Qed.

End RAWBITVECTOR_LIST.

Module BITVECTOR_LIST <: BITVECTOR.
  Declare Scope bv_scope.
  Include RAW2BITVECTOR(RAWBITVECTOR_LIST).

  Notation "x |0" := (cons false x) (left associativity, at level 73, format "x |0"): bv_scope.
  Notation "x |1" := (cons true x) (left associativity, at level 73, format "x |1"): bv_scope.
  Notation "'b|0'" := [false] (at level 70): bv_scope.
  Notation "'b|1'" := [true] (at level 70): bv_scope.
  Notation "# x |" := (@of_bits x) (no associativity, at level 1, format "# x |"): bv_scope.
  Notation "v @ p" := (bitOf p v) (at level 1, format "v @ p ") : bv_scope.


End BITVECTOR_LIST.

(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)
