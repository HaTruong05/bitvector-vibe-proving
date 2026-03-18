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
    { intros n. rewrite -> rev_length. rewrite -> rev_length. induction n as [ | n'' IHn'].
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
  + rewrite rev_length in *. simpl.
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
  + rewrite rev_length in *. simpl.
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
  rewrite app_length, Nat2N.inj_add, H0, H1; now rewrite N.add_comm.
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
       rewrite app_assoc_reverse.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma mk_list_false_equiv: forall t acc, mk_list_false_acc t acc = (List.rev (mk_list_false t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt. 
       rewrite app_assoc_reverse.
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
       rewrite !map_length, H, N.eqb_refl.
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
       intros. rewrite <- H0. now rewrite map_length.
       rewrite map_length.
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
  rewrite <- rev_length. apply not_ult_list_big_endian_x_0.
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
  rewrite H. rewrite <- rev_length.
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
  apply rev_uneq in H. rewrite <- rev_length in *.
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
  rewrite rev_mk_list_true. rewrite <- rev_length. apply (@ule_list_big_endian_1 (rev b)).
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
  now rewrite !rev_length.
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
    rewrite (@map_length bool bool negb b) in H. 
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
       now rewrite pos2list_acc, app_length.
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
       rewrite pos2list_acc, app_length.
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
           * rewrite firstn_length. rewrite length_pos2list_nil, H.
            	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.min_l,
               @Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Arith.PeanoNat.Nat.succ_le_mono)
              (@Coq.Init.Nat.min, @Coq.Init.Peano.lt).
           * rewrite app_length, length_pos2list_nil, H, length_mk_list_false.
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
         rewrite app_length, length_mk_list_false.
         rewrite firstn_length. apply Nat.ltb_lt in H.
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
        { rewrite rev_length. pose proof firstn_length_le as firstn_length_le.
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
        { rewrite rev_length. pose proof firstn_length_le as firstn_length_le.
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
    rewrite <- rev_length in Hxy.
    rewrite <- (@rev_length bool y) in Hxy.
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
    rewrite <- rev_length in Hxy.
    rewrite <- (@rev_length bool y) in Hxy.
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
    unfold size in H. rewrite <- rev_length in H. 
    rewrite <- (@rev_length bool y) in H. apply Neqb_ok in H. 
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
         { rewrite length_shl_n_bits_a, app_length, length_mk_list_false, length_skipn.
           apply Nat.ltb_lt in H.
           lia.
         } 
         rewrite H0, H.
         unfold shl_n_bits_a.
         assert ((length (skipn n (a :: a0) ++ mk_list_false n) = length (a :: a0))).
         { rewrite app_length, length_skipn, length_mk_list_false.
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
          rewrite !app_length, !length_mk_list_false, !firstn_length.
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
            rewrite app_length, firstn_length, length_mk_list_false.
            rewrite Nat.min_l, Nat.sub_add.
            easy. 
            apply Nat.ltb_lt in H. lia.
            lia.
          }
          rewrite H0, H.
          f_equal.
          rewrite firstn_app, length_skipn, app_length, length_mk_list_false.
          assert ((n + length (firstn (length (a :: a0) - n) (a :: a0)) - n)%nat = 
                  (length (a :: a0) - n)%nat).
          { rewrite firstn_length.
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
         cbn. rewrite app_length. f_equal. easy.
       - unfold shr_n_bits_a.
         case_eq ( (S n <? length a)%nat); intros. cbn.
         case_eq a; intros. subst. cbn in *.
         now contradict H.
         unfold shr_n_bits_a. subst.
         rewrite !app_length. cbn.
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
  + simpl. rewrite !app_assoc_reverse.
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
  + simpl. rewrite !app_assoc_reverse.
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
             rewrite app_length ,length_mk_list_false.
             rewrite length_skipn.
             Reconstr.reasy (@Coq.Arith.Compare_dec.leb_correct_conv, 
              @Coq.Arith.PeanoNat.Nat.sub_add, @Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.ltb_ge) 
             (@RAWBITVECTOR_LIST.shl_n_bits_a, @Coq.Init.Datatypes.length, @Coq.Init.Peano.lt).
             rewrite app_length ,length_mk_list_true.
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
           * cbn. rewrite !app_length, !length_mk_list_true.
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
             } rewrite Htwo. rewrite !app_length, !length_mk_list_false, !firstn_length.
               case_eq n; intros. cbn.
               Reconstr.reasy (@Coq.Lists.List.firstn_all, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
               subst. cbn. rewrite !app_length. cbn. rewrite !length_mk_list_true.
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
       - cbn. rewrite !app_assoc_reverse.
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
                 { rewrite !app_length in H. cbn in H.
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
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                      rewrite H5. 
                    	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le, 
                       @Coq.Arith.PeanoNat.Nat.lt_succ_r, 
                       @Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !app_length in H.
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
                      assert (length a = length b). rewrite !app_length in H.
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
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.add_succ_r, 
                                 @Coq.Init.Peano.plus_n_O) Reconstr.Empty.
                      rewrite H5. lia. lia.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !app_length in H.
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
                      assert (length a = length b). rewrite !app_length in H.
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
                * rewrite !app_length in H. cbn in H. 
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
        rewrite app_length, length_skipn, length_mk_list_false.
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
        rewrite app_length, length_skipn, length_mk_list_true.
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
        - cbn. Reconstr.reasy (@Coq.Lists.List.app_nil_end) Reconstr.Empty.
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
 N.to_nat (list2N (skipn n l ++ mk_list_true n)) + Nat.pow 2 (length l))%nat.
Proof. intros. rewrite skipn_true_list, list2N_app_true.
        rewrite app_length, length_skipn, length_mk_list_true.
	      Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_add, 
          @Coq.Arith.PeanoNat.Nat.ltb_lt, 
          @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
Qed.

Lemma skipn_false_list: forall n l,
  (skipn n l ++ false :: mk_list_false n) = (skipn n l ++ mk_list_false n) ++ [false].
Proof. intro n.
        induction n; intros.
        - cbn. Reconstr.reasy (@Coq.Lists.List.app_nil_end) Reconstr.Empty.
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
             @Coq.Lists.List.rev_length) 
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
            cbn. rewrite !rev_length. unfold zeros.
            rewrite length_mk_list_false. unfold size.
            rewrite Nat2N.id.
            Reconstr.reasy (@RAWBITVECTOR_LIST.mk_list_true_app,
               @RAWBITVECTOR_LIST.length_mk_list_true, 
               @Coq.Lists.List.app_length) Reconstr.Empty.
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
    - rewrite skip0. rewrite Nat.sub_0_r. rewrite <- rev_length. 
      rewrite firstn_all. easy.
    - simpl. simpl in len. apply Nat.succ_lt_mono in len. specialize (@IHb n len).
      rewrite IHb. case n in *.
      * rewrite Nat.sub_0_r. rewrite <- rev_length. rewrite firstn_all.
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
          + rewrite app_length. assert (length [a] = 1)%nat by easy.
            rewrite H0. rewrite Nat.add_1_r. easy. }
        pose proof (@Nat.sub_lt (length b) (S n) len gt0).
        rewrite <- rev_length in H1 at 2. apply Nat.lt_lt_succ_r in H1.
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
             { rewrite app_length. simpl. lia. }
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
       rewrite rev_length in HH.
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
  rewrite Nat2N.id in Hb. rewrite <- rev_length in Hb.
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
  rewrite <- rev_length. apply ule_list_big_endian_0.
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
  bv_slt b1 b2 = true -> bv_sle b2 b3 = true -> bv_slt b1 b3 = true.
Proof.
  intros b1 b2 b3 H_slt H_sle.
  destruct (@bv_sle_eq b2 b3) as [H_eq_fwd _].
  apply H_eq_fwd in H_sle.
  destruct H_sle as [H_strict | H_eq].
  + now apply (@bv_slt_trans b1 b2 b3).
  + now rewrite <- H_eq.
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

(* Start: bvand_slt *)
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
  - rewrite <- length_twos_complement.
    easy.
Qed.

Lemma list2int_twos_complement : forall b,
  list2int (twos_complement b) = 
  ((list2int (map negb b) + 1) mod pow2_int (length b))%Z.
Proof.
  intros b.
  unfold twos_complement.
  rewrite list2int_add_list_ingr.
  - simpl bool2int. 
    rewrite list2int_mk_list_false.
    f_equal. lia. rewrite <- not_list_length. reflexivity. 
  - rewrite length_map. 
    rewrite length_mk_list_false.
    reflexivity.
Qed. 

Lemma list2int_twos_complement_one : forall n,
  n <> 0%N -> 
  ((1 + list2int (twos_complement (one n))) mod pow2_int_N n)%Z = 0%Z.
Proof.
  intros n Hneq_zero.
  pose proof (add_neg_list_absorb (bits (one n))) as Hzero.
  apply (f_equal list2int) in Hzero.
  unfold add_list in Hzero.
  rewrite list2int_add_list_ingr in Hzero.
  2:{ apply length_twos_complement. }
  simpl bool2int in Hzero.
  replace (list2int (bits (one n)) + list2int (twos_complement (bits (one n))) + 0)%Z 
    with (1 + list2int (twos_complement (bits (one n))))%Z in Hzero.
  2:{
    assert (H: list2int (one n) = 1%Z). {
      unfold one.
      rewrite list2int_mk_list_one.
      symmetry. 
      rewrite Z.mod_small. 
      - lia. 
      - destruct (N.to_nat n) as [| m] eqn:Hnat.
        + lia. 
        + rewrite pow2_int_succ.
          pose proof (zero_lt_pow2_int m) as Hgt_zero.
          lia.
    }
    replace (list2int (bits (one n))) with 1%Z.
    lia. 
  }
  replace (list2int (mk_list_false (length (bits (one n))))) with 0%Z in Hzero.
  2:{ 
    rewrite list2int_mk_list_false. 
    reflexivity. 
  }
  replace (pow2_int (length (bits (one n)))) with (pow2_int_N n) in Hzero.
  2:{ 
    unfold pow2_int_N. 
    f_equal. 
    unfold one. unfold bits. 
    rewrite length_mk_list_one. 
    reflexivity. 
  }
  exact Hzero.
Qed.

Lemma list2int_twos_complement_one_exact : forall n,
  n <> 0%N ->
  list2int (twos_complement (one n)) = (pow2_int_N n - 1)%Z.
Proof.
  intros n Hneq.
  pose proof (list2int_twos_complement_one Hneq) as Hmod.
  assert (Hbounds : (0 <= list2int (twos_complement (one n)) < pow2_int_N n)%Z).
  {
    split.
    - apply list2int_geq_zero.
    - replace (pow2_int_N n) with (pow2_int (length (twos_complement (one n)))).
      + apply list2int_lt_pow2_int.
        reflexivity.
      + unfold pow2_int_N.
        f_equal. 
        rewrite <- length_twos_complement.
        unfold one.
        rewrite length_mk_list_one.
        reflexivity.
  }
  assert (Hpos : (0 < pow2_int_N n)%Z).
  { apply zero_lt_pow2_int. }
  assert (Hneq_P : pow2_int_N n <> 0%Z) by lia.
  pose proof (Z.div_mod (1 + list2int (twos_complement (one n))) (pow2_int_N n) Hneq_P) as Hdiv.
  rewrite Hmod in Hdiv.
  remember (((1 + list2int (twos_complement (one n))) / pow2_int_N n)%Z) as q.
  remember (list2int (twos_complement (one n))) as X.
  remember (pow2_int_N n) as P.
  assert (H_mult_bounds : (1 <= P * q + 0 <= P)%Z) by lia.
  assert (H_q : q = 1%Z) by nia.
  rewrite H_q in Hdiv.
  lia.
Qed.

Lemma sbv2int_sub_one : forall n (t : bitvector),
  size t = n ->
  t <> signed_min n ->
  sbv2int n (bv_subt' t (one n)) = (sbv2int n t - 1)%Z.
Proof.
  intros n t Hsize Hneq.
  unfold sbv2int, bv_subt'.
  unfold bv2int.
  replace (size t =? size (one n)) with true.
  2:{ symmetry. apply N.eqb_eq. rewrite one_size. apply Hsize. }
  destruct (last (bits t) false) eqn:Hsign_t;
  destruct (last (subst_list' (bits t) (bits (one n))) false) eqn:Hsign_sub.
  - replace (last t false) with true.
    rewrite list2int_subst_list.
    2:{ unfold bits. apply size_len_eq. rewrite one_size. apply Hsize. }
    replace (pow2_int (length (bits t))) with (pow2_int_N n).
    2:{ unfold pow2_int_N. f_equal. rewrite bits_size. rewrite Hsize. reflexivity. }
    assert (Hneq_zero : n <> 0%N). {
      intro Hzero.
      rewrite Hzero in Hsize.
      destruct (bits t) eqn:Hbits.
      - simpl in Hsign_t. 
        discriminate.
      - assert (Hcontra : length (bits t) = 0%nat). {
          rewrite bits_size.
          rewrite Hsize. 
          reflexivity.
        }
        rewrite Hbits in Hcontra.
        simpl in Hcontra.
        discriminate.
    }
    unfold bits.
    pose proof (list2int_twos_complement_one Hneq_zero) as Hcomp.
    replace (list2int t + list2int (twos_complement (one n)))%Z 
       with (list2int t - 1 + (1 + list2int (twos_complement (one n))))%Z by lia.
    assert (Hpow_pos : (0 < pow2_int_N n)%Z). { apply zero_lt_pow2_int. }
    rewrite Z.add_mod.
    2:{ lia. }
    rewrite Hcomp.
    replace (((list2int t - 1) mod pow2_int_N n + 0)%Z) 
       with ((list2int t - 1) mod pow2_int_N n)%Z by lia.
    rewrite Z.mod_mod.
    2:{ lia. }
    rewrite Z.mod_small.
    + lia.
    + split.
      * assert (Hnot_empty : bits t <> []).
        {
          intros Hempty.
          rewrite Hempty in Hsign_t.
          simpl in Hsign_t.
          discriminate.
        }
        destruct (exists_last Hnot_empty) as [front [last_bit Hdecomp]].
        rewrite Hdecomp in Hsign_t.
        assert (Hlast : last_bit = true).
        { 
          rewrite last_app in Hsign_t.
          simpl in Hsign_t. 
          assumption. 
        }
        subst last_bit.
        unfold bits in Hdecomp.
        rewrite Hdecomp.
        rewrite list2int_app.
        rewrite list2int_bool.
        unfold bool2int.
        pose proof list2int_geq_zero as Hfront_pos.
        assert (Hpow_lb : (pow2_int (length front) >= 1)%Z).
        { pose proof (zero_lt_pow2_int (length front)) as Hpow_lb. lia. }
        specialize (Hfront_pos front).
        lia.
      * change (list2int t) with (list2int (bits t)).
        set (m := length (bits t)).
        pose proof (@list2int_lt_pow2_int (bits t) m eq_refl) as Hmax.
        assert (Hm_n : pow2_int m = pow2_int_N n).
        {
          unfold m, pow2_int_N.
          f_equal.
          rewrite bits_size.
          rewrite Hsize.
          reflexivity.
        }
        rewrite Hm_n in Hmax.
        lia.
  - exfalso.
    assert (Hnot_empty : bits t <> []).
    {
      intros Hempty.
      rewrite Hempty in Hsign_t.
      simpl in Hsign_t.
      discriminate.
    }
    assert (Hdecomp_t : bits t = removelast (bits t) ++ [true]).
    {
      rewrite <- Hsign_t.
      apply app_removelast_last.
      easy.
    }
    assert (Hval_t : list2int (bits t) = (pow2_int (length (removelast (bits t))) + list2int (removelast (bits t)))%Z).
    {
      rewrite Hdecomp_t.
      rewrite list2int_app.
      rewrite list2int_bool.
      simpl (bool2int true).
      rewrite <- Hdecomp_t.
      lia.
    }
    pose proof (@list2int_geq_zero (removelast (bits t))) as Hfront_pos.
    set (sub_list := subst_list' (bits t) (bits (one n))) in *.
    assert (Hlen_sub : length sub_list = length (bits t)).
    {
      unfold sub_list.
      assert (size_eq: length (bits t) = length (bits (one n))). {
        rewrite !bits_size.
        rewrite one_size.
        rewrite Hsize.
        reflexivity.
      }
      rewrite <- (subst_list'_length size_eq).
      reflexivity.
    }
    assert (Hdecomp_sub : sub_list = removelast sub_list ++ [false]).
    {
      rewrite <- Hsign_sub.
      apply app_removelast_last.
      intro Hempty.
      assert (Hlen0 : length sub_list = (0)%nat) by (rewrite Hempty; reflexivity).
      rewrite Hlen_sub in Hlen0.
      destruct (bits t) eqn:Heq_t.
      - apply Hnot_empty. reflexivity.
      - discriminate Hlen0.
    }
    assert (Hval_sub : list2int sub_list = list2int (removelast sub_list)).
    {
      rewrite Hdecomp_sub.
      rewrite list2int_app.
      rewrite list2int_bool.
      simpl (bool2int false).
      rewrite <- Hdecomp_sub.
      lia.
    }
    pose proof (@list2int_lt_pow2_int (removelast sub_list) (length (removelast sub_list)) eq_refl) as Hsub_upper.
    assert (Hlen_eq : length (bits t) = length (bits (one n))).
    {
      apply size_len_eq.
      unfold bits.
      rewrite one_size.
      easy.
    }
    pose proof (@list2int_subst_list (bits t) (bits (one n)) Hlen_eq) as Hsubst_mod.
    assert (Hlen_t : length (bits t) = S (length (removelast (bits t)))).
    {
      rewrite Hdecomp_t at 1. 
      rewrite length_app. 
      simpl. 
      lia. 
    }
    assert (Hpow_t : pow2_int (length (bits t)) = (2 * pow2_int (length (removelast (bits t))))%Z).
    { rewrite Hlen_t. apply pow2_int_succ. }
    assert (Hlen_sub_S : length sub_list = S (length (removelast sub_list))).
    { rewrite Hdecomp_sub at 1. rewrite length_app. simpl. lia. }
    
    assert (Hlen_rem : length (removelast sub_list) = length (removelast (bits t))) by lia.
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z).
    {
      assert (Hn_neq_0 : n <> 0%N).
      {
        intro Heq.
        rewrite Heq in Hlen_eq.
        simpl in Hlen_eq. 
        rewrite Hlen_eq in Hlen_t.
        discriminate Hlen_t.
      }
      apply (list2int_twos_complement_one_exact Hn_neq_0).
    }
    assert (Hpos_pow : (0 < pow2_int (length (bits t)))%Z).
    { apply zero_lt_pow2_int. }
    assert (Ht_bound : (list2int (bits t) < pow2_int (length (bits t)))%Z).
    { apply list2int_lt_pow2_int. reflexivity. }
    assert (Ht_val_exact : list2int (bits t) = pow2_int (length (removelast (bits t)))).
    {
      rewrite Hlen_rem in Hsub_upper.
      rewrite Htc in Hsubst_mod.
      Z.div_mod_to_equations.
      assert (H_not_zero : pow2_int (length (bits t)) <> 0%Z) by lia.
      specialize (H H_not_zero).
      assert (Hr_val : r = list2int (removelast sub_list)).
      { rewrite <- Hsubst_mod. exact Hval_sub. }
      remember (list2int (bits t)) as X.
      remember (pow2_int (length (removelast (bits t)))) as P.
      remember (list2int (removelast (bits t))) as Y.
      remember (list2int (removelast sub_list)) as R_sub.
      assert (Hpow_eq : pow2_int_N n = pow2_int (length (bits t))).
      {
        unfold pow2_int_N.
        f_equal.
        rewrite bits_size.
        rewrite Hsize.
        easy.
      }
      rewrite Hpow_eq in *.
      rewrite Hpow_t in *.
      assert (Hq_min : (0 < q)%Z) by nia.
      assert (Hq_max : (q < 2)%Z) by nia.
      assert (Hq : q = 1%Z) by lia.
      rewrite Hq in H.
      lia.
    }
    assert (H_signed_min_val : list2int (bits (signed_min n)) = pow2_int (length (removelast (bits t)))).
    {
      assert (H_t_n : N.to_nat n = length (bits t)).
      { rewrite bits_size, Hsize; easy. }
      unfold signed_min.
      rewrite H_t_n.
      rewrite Hlen_t.
      unfold smin_big_endian.
      unfold bits.
      cbn.
      rewrite list2int_app. 
      simpl.
      rewrite length_rev.
      assert (Hlen_false : length (mk_list_false (length (removelast t))) = length (removelast t)).
      {
        rewrite length_mk_list_false.
        reflexivity.
      }
      rewrite Hlen_false.
      assert (Hval_false : list2int (rev (mk_list_false (length (removelast t)))) = 0%Z).
      { 
        rewrite rev_mk_list_false.
        apply list2int_mk_list_false.
      }
      rewrite Hval_false.
      lia.
    }
    assert (H_same_val : list2int (bits t) = list2int (bits (signed_min n))).
    {
      rewrite Ht_val_exact.
      symmetry.
      exact H_signed_min_val.
    }
    apply list2int_inj in H_same_val.
    + contradiction (Hneq H_same_val).
    + apply size_len_eq.
      unfold bits.
      rewrite signed_min_size.
      easy.
  - unfold bits in Hsign_t.
    rewrite Hsign_t.
    assert (Hlen_eq : length (bits t) = length (bits (one n))).
    { 
      unfold bits.
      apply size_len_eq.
      rewrite one_size.
      easy.
    }
    pose proof (list2int_subst_list Hlen_eq) as Hsubst_mod.
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z).
    { 
      assert (Hn_neq_0 : n <> 0%N).
      {
        intro Heq.
        rewrite Heq in Hlen_eq.
        simpl in Hlen_eq.
        destruct (bits t) as [| b bs] eqn:Hbits_t.
        - rewrite Heq in Hsign_sub.
          compute in Hsign_sub. 
          discriminate Hsign_sub.
        - discriminate Hlen_eq.
      }
      apply (list2int_twos_complement_one_exact Hn_neq_0).
    }
    rewrite Htc in Hsubst_mod.
    rewrite Hsubst_mod.
    assert (H_t_zero : list2int (bits t) = 0%Z).
    {
      assert (H_upper : (list2int (bits t) < pow2_int (length (bits t) - 1))%Z).
      {
        assert (Hnot_empty : bits t <> []).
        {
          intro Hempty.
          assert (Hone_empty : bits (one n) = []).
          {
            destruct (bits (one n)).
            - reflexivity.
            - rewrite Hempty in Hlen_eq. 
              simpl in Hlen_eq. 
              discriminate.
          }
          rewrite Hempty in Hsign_sub.
          rewrite Hone_empty in Hsign_sub.
          simpl in Hsign_sub.
          discriminate Hsign_sub.
        }
        assert (Hdecomp : bits t = removelast (bits t) ++ [false]).
        {
          rewrite (app_removelast_last false Hnot_empty).
          unfold bits.
          rewrite Hsign_t.
          rewrite rl_fact.
          reflexivity.
        }
        rewrite Hdecomp.
        rewrite list2int_app.
        rewrite list2int_bool.
        simpl bool2int.
        rewrite Z.mul_0_r.
        rewrite Z.add_0_l.
        assert (Hlen_rem : (length (bits t) - 1)%nat = length (removelast (bits t))).
        {
          rewrite Hdecomp at 1.
          rewrite length_app.
          simpl (length [false]).
          lia.
        }
        rewrite length_app.
        simpl (length [false]).
        replace (length (removelast (bits t)) + 1 - 1)%nat 
         with (length (removelast (bits t))) by lia.
        apply list2int_lt_pow2_int.
        reflexivity.
      }
      assert (H_lower : (pow2_int (length (bits t) - 1) <= list2int (subst_list' (bits t) (bits (one n))))%Z).
      {
        remember (subst_list' (bits t) (bits (one n))) as sub_list.
        assert (Hnot_empty_sub : sub_list <> []).
        {
          intro Hempty.
          rewrite Hempty in Hsign_sub.
          simpl in Hsign_sub.
          discriminate Hsign_sub.
        }
        assert (Hdecomp_sub : sub_list = removelast sub_list ++ [true]).
        {
          rewrite (app_removelast_last false Hnot_empty_sub) at 1.
          rewrite Hsign_sub.
          reflexivity.
        }
        rewrite Hdecomp_sub at 1.
        rewrite list2int_app.
        rewrite list2int_bool.
        simpl bool2int.
        rewrite Z.mul_1_r.
        assert (Hlen_rem_sub : length (removelast sub_list) = (length (bits t) - 1)%nat).
        {
          assert (Hlen_sub : length sub_list = length (bits t)).
          {
            rewrite Heqsub_list.
            unfold bits.
            assert (Hsize_eq: length t = length (one n)). 
            { apply size_len_eq. rewrite one_size. easy. }
            rewrite (subst_list'_length Hsize_eq).
            easy.
          }
          assert (Hlen_math : length sub_list = (length (removelast sub_list) + 1)%nat).
          {
            rewrite Hdecomp_sub at 1.
            rewrite length_app.
            simpl (length [true]).
            lia.
          }
          lia.
        }
        rewrite Hlen_rem_sub.
        pose proof (@list2int_geq_zero (removelast sub_list)) as Hfront_pos.
        lia.
      }
      assert (H_t_pos : (0 <= list2int (bits t))%Z).
      { apply list2int_geq_zero. }
      assert (H_half_pos : (0 < pow2_int (length (bits t) - 1))%Z).
      { apply zero_lt_pow2_int. }
      assert (H_pow_split : pow2_int (length (bits t)) = (2 * pow2_int (length (bits t) - 1))%Z).
      {
        assert (H_length_pos : (0 < (length (bits t)))%nat).
        {
          destruct (bits t) eqn:Heq_bits.
          - simpl in Hsign_sub.
            discriminate Hsign_sub.
          - simpl.
            lia.
        }
        replace (length (bits t)) with (S (length (bits t) - 1)) at 1 by lia.
        simpl pow2_int.
        reflexivity.
      }
      assert (Hpow_eq : pow2_int_N n = pow2_int (length (bits t))).
      {
        unfold pow2_int_N.
        f_equal.
        rewrite bits_size.
        rewrite Hsize.
        easy.
      }
      rewrite Hpow_eq in Hsubst_mod.
      rewrite Hsubst_mod in H_lower.
      remember (list2int (bits t)) as X.
      remember (pow2_int (length (bits t) - 1)) as HalfP.
      rewrite H_pow_split in *.
      Z.div_mod_to_equations.
      assert (H_2P_pos : (0 < 2 * HalfP)%Z) by lia.
      assert (H_2P_neq : (2 * HalfP <> 0)%Z) by lia.
      specialize (H H_2P_neq).
      specialize (H0 H_2P_pos).
      assert (Hq : q = 0%Z) by nia.
      rewrite Hq in H.
      lia.
    }
    rewrite H_t_zero.
    change (list2int t) with (list2int (bits t)).
    rewrite H_t_zero.
    assert (Hpow_eq : pow2_int (length (bits t)) = pow2_int_N n).
    {
      unfold pow2_int_N.
      f_equal.
      rewrite bits_size.
      rewrite Hsize.
      easy.
    }
    rewrite Hpow_eq.
    rewrite Z.mod_small.
    + lia.
    + assert (H_P_pos : (0 < pow2_int_N n)%Z).
      { apply zero_lt_pow2_int. }
      lia.   
  - unfold bits in Hsign_t.
    rewrite Hsign_t.
    assert (Hlen_eq : length (bits t) = length (bits (one n))).
    { 
      unfold bits.
      apply size_len_eq.
      rewrite one_size.
      easy. 
    }
    rewrite (list2int_subst_list Hlen_eq).
    assert (Htc : list2int (twos_complement (bits (one n))) = (pow2_int_N n - 1)%Z).
    { 
      apply list2int_twos_complement_one_exact.
      intro Hzero.
      assert (Ht_empty : bits t = []).
      {
        destruct (bits t) eqn:Heq_t.
        - reflexivity.
        - assert (Hlen : length (bits t) = 0%nat).
          { rewrite bits_size, Hsize, Hzero. reflexivity. }
          rewrite Heq_t in Hlen. 
          discriminate Hlen.
      }
      assert (Hsmin_empty : bits (signed_min n) = []).
      {
        destruct (bits (signed_min n)) eqn:Heq_smin.
        - reflexivity.
        - assert (Hlen : length (bits (signed_min n)) = 0%nat).
          { rewrite bits_size, signed_min_size, Hzero. reflexivity. }
          rewrite Heq_smin in Hlen. 
          discriminate Hlen.
      }
      assert (Hbits_eq : bits t = bits (signed_min n)).
      {
        rewrite Ht_empty.
        rewrite Hsmin_empty.
        reflexivity.
      }
      unfold bits in Hbits_eq.
      contradiction.
    }
    rewrite Htc.
    assert (Hpow_eq : pow2_int (length (bits t)) = pow2_int_N n).
    { 
      unfold pow2_int_N.
      f_equal.
      rewrite bits_size.
      rewrite Hsize.
      easy.
    }
    rewrite Hpow_eq.
    replace (list2int (bits t) + (pow2_int_N n - 1))%Z 
       with (list2int (bits t) - 1 + 1 * pow2_int_N n)%Z by lia.
    assert (Hpow_neq_0 : pow2_int_N n <> 0%Z). 
    { pose proof (zero_lt_pow2_int (length (bits t))); lia. }
    rewrite Z.mod_add by exact Hpow_neq_0.
    rewrite Z.mod_small.
    + change (list2int t) with (list2int (bits t)).
      lia.
    + split.
      * assert (H_t_pos : (0 <= list2int (bits t))%Z).
        { apply list2int_geq_zero. }
        assert (Ht_not_zero : list2int (bits t) <> 0%Z).
        {
          intro Hzero.
          pose proof (list2int_subst_list Hlen_eq) as Hsub_mod.
          rewrite Htc in Hsub_mod.
          rewrite Hpow_eq in Hsub_mod.
          rewrite Hzero in Hsub_mod.
          rewrite Z.add_0_l in Hsub_mod.
          rewrite Z.mod_small in Hsub_mod.
          2: { pose proof (zero_lt_pow2_int (length (bits t))). lia. }
          remember (subst_list' (bits t) (bits (one n))) as sub.
          assert (Hnot_empty : sub <> []).
          {
            intro Hempty.
            rewrite Hempty in Hsub_mod.
            simpl list2int in Hsub_mod.
            rewrite <- Hpow_eq in Hsub_mod.
            assert (Hlen_0 : length (bits t) = 0%nat).
            {
              destruct (length (bits t)) eqn:Heq_len.
              - reflexivity.
              - simpl pow2_int in Hsub_mod.
                pose proof (zero_lt_pow2_int n0).
                change (match pow2_int n0 with
                        | 0%Z => 0%Z
                        | Z.pos y' => Z.pos y'~0
                        | Z.neg y' => Z.neg y'~0
                        end) with (2 * pow2_int n0)%Z in Hsub_mod.
                lia.
            }
            assert (Ht_empty : bits t = []).
            { 
              destruct (bits t).
              - reflexivity.
              - discriminate Hlen_0. 
            }
            assert (Hsmin_empty : bits (signed_min n) = []).
            {
              destruct (bits (signed_min n)) eqn:Heq_smin.
              - reflexivity.
              - assert (Hlen_smin : length (bits (signed_min n)) = 0%nat).
                {
                  rewrite bits_size, signed_min_size, <- Hsize, <- bits_size.
                  rewrite Ht_empty. 
                  reflexivity. 
                }
                rewrite Heq_smin in Hlen_smin. 
                discriminate Hlen_smin.
            }
            assert (Hbits_eq : t = signed_min n).
            {
              unfold bits in Ht_empty, Hsmin_empty.
              rewrite Hsmin_empty.
              easy.
            }
            contradiction (Hneq Hbits_eq).
          }
          assert (Hdecomp : sub = removelast sub ++ [false]).
          {
            rewrite (app_removelast_last false Hnot_empty) at 1.
            rewrite Hsign_sub.
            reflexivity.
          }
          rewrite Hdecomp in Hsub_mod.
          rewrite list2int_app in Hsub_mod.
          rewrite list2int_bool in Hsub_mod.
          simpl bool2int in Hsub_mod.
          rewrite Z.mul_0_r in Hsub_mod.
          rewrite Z.add_0_l in Hsub_mod.
          pose proof (@list2int_lt_pow2_int (removelast sub) (length (removelast sub)) eq_refl) as Hmax.
          assert (Hlen_sub : length sub = length (bits t)).
          {
            rewrite Heqsub.
            rewrite <- (subst_list'_length Hlen_eq).
            reflexivity.
          }
          assert (Hlen_math : length sub = S (length (removelast sub))).
          { 
            rewrite Hdecomp at 1. 
            rewrite length_app. 
            simpl. 
            lia. 
          }
          assert (Hpow_split : pow2_int_N n = (2 * pow2_int (length (removelast sub)))%Z).
          {
            rewrite <- Hpow_eq.
            rewrite <- Hlen_sub.
            rewrite Hlen_math.
            simpl pow2_int. 
            reflexivity.
          }
          rewrite Hsub_mod in Hmax.
          rewrite Hpow_split in *.
          assert (H_P_pos : (0 < pow2_int (length (removelast sub)))%Z).
          { apply zero_lt_pow2_int. }
          lia.
        }
        lia.
      * assert (Hlen: length (bits t) = N.to_nat(n)). 
        { rewrite bits_size. rewrite Hsize. reflexivity. }
        pose proof (list2int_lt_pow2_int Hlen) as H_lt.
        rewrite <- Hlen in H_lt.
        rewrite Hpow_eq in H_lt.
        lia.
Qed. 
  
Lemma sbv2int_pos_iff : forall n (x : bitvector),
  size x = n ->
  (0 <= sbv2int n x)%Z <-> last x false = false.
Proof.
  intros n x Hsize.
  unfold sbv2int.
  destruct (last x false) eqn:Hsign.
  - split; intro H.
    + unfold bv2int, pow2_int_N in H.
      assert (H_len : length x = N.to_nat n).
      { unfold size in Hsize. lia. }
      pose proof (list2int_lt_pow2_int H_len) as H_bound.
      lia.
    + discriminate.
  - split; intro H.
    + reflexivity. 
    + unfold bv2int.
      apply list2int_geq_zero.
Qed.

(*-t = ~t + 1 *)
Lemma bv_neg_is_not_plus_one : forall (a : bitvector) (n : N), 
  size a = n -> 
  bv_neg a = bv_add (bv_not a) (one n).
Proof.
  intros a n Hs.
  unfold bv_neg.
  unfold twos_complement.
  unfold bv_add.
  match goal with
  | [ |- _ = (if ?CHECK then _ else _) ] => replace CHECK with true
  end.
  2: {
      symmetry. 
      apply N.eqb_eq.
      apply bv_not_size.
      rewrite one_size. easy.
  }
  assert (H_zeros: forall m : nat, add_list_ingr (mk_list_false m) (mk_list_false m) false = mk_list_false m).
  {
    intro m. induction m as [|m' IHm]; simpl.
    - reflexivity.
    - f_equal. exact IHm.
  }
  assert (H_one: one n = add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true).
  {
    unfold one.
    induction (N.to_nat n) as [|k IH].
    - reflexivity.
    - destruct k.
      + reflexivity. 
      + simpl in *.
        rewrite IH.
        simpl.
        f_equal.
        rewrite (H_zeros k).
        clear. induction k; simpl; [reflexivity | f_equal; apply IHk].
  }
  replace (length a) with (N.to_nat n).
  2: {
      rewrite <- Hs.
      unfold size.
      rewrite Nat2N.id.
      reflexivity.
  }
  rewrite H_one.
  unfold add_list, bv_not.
  unfold bits in *. 
  replace (add_list_ingr (map negb a) (add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true) false)
     with (add_list_ingr (add_list_ingr (mk_list_false (N.to_nat n)) (mk_list_false (N.to_nat n)) true) (map negb a) false).
  2: { apply add_list_carry_comm. }
  rewrite <- bv_neg_involutive_aux.
  rewrite H_zeros.
  rewrite add_list_carry_comm.
  reflexivity.
Qed.

(* Break: bvand_slt *)

(* MSB(a) = 0 -> MSB(a && b) = 0
   In other words, anding with a positive number returns a positive number *)

Lemma pos_bvand_pos : forall (x y : bitvector) (n : N), size x = n -> size y = n -> last x false = false -> last (bv_and x y) false = false.
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

(* Continue: bvand_slt *)

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

Lemma bv_sle_ule_same_sign : forall (n : N) (a b : bitvector),
  size a = n ->
  size b = n ->
  last a false = last b false ->
  bv_sle a b = bv_ule a b.
Proof.
  intros n a b Ha Hb Hsign.
  unfold bv_sle, bv_ule.
  rewrite Ha, Hb.
  rewrite (N.eqb_refl n).
  unfold sle_list.
  unfold sle_list_big_endian.
  unfold ule_list.
  unfold ule_list_big_endian.
  destruct (rev a) as [|xi x'] eqn:Ra;
  destruct (rev b) as [|yi y'] eqn:Rb.
  - reflexivity.
  - exfalso. 
    assert (Hlen : length (rev a) = length (rev b)).
    { 
      rewrite Ra, Rb. simpl.
      unfold size in Ha, Hb.
      rewrite <- (length_rev a) in Ha.
      rewrite <- (length_rev b) in Hb.
      rewrite Ra in Ha.
      rewrite Rb in Hb.
      simpl in Ha.
      subst n.
      apply (Nat2N.inj_iff (S (length y')) 0) in Hb.
      symmetry.
      exact Hb.
    }
    rewrite Ra, Rb in Hlen.
    simpl in Hlen.
    discriminate Hlen.
  - exfalso. 
    assert (Hlen : length (rev a) = length (rev b)).
    { 
      rewrite Ra, Rb. simpl. 
      unfold size in Ha, Hb. 
      rewrite <- (length_rev a) in Ha.
      rewrite <- (length_rev b) in Hb.
      rewrite Ra in Ha.
      rewrite Rb in Hb.
      simpl in Ha.
      subst n.
      simpl in Hb.
      discriminate Hb.
    }
    rewrite Ra, Rb in Hlen.
    simpl in Hlen.
    discriminate Hlen.
  - rewrite <- hd_rev in Hsign.
    rewrite <- hd_rev in Hsign.
    rewrite Ra, Rb in Hsign.
    simpl in Hsign. 
    subst xi.
    destruct yi.
    * simpl. 
      reflexivity.
    * simpl.
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

(* End: bvand_slt *)

(* Start: bvor_sgt *)

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
  - reflexivity. (* Both are nil: 0 = 0 *)
  - discriminate Hlen. (* l1 is nil, l2 is not: impossible *)
  - discriminate Hlen. (* l1 is not nil, l2 is: impossible *)
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
    Search last mk_list_true.
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
          (* Based on your earlier logic: *)
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
(* End: bvor_sgt *)

(* Start: bvand_sgt *)

Lemma size_rev : forall (l : bitvector), size (rev l) = size l.
Proof.
  intros l.
  unfold size. 
  rewrite length_rev.
  reflexivity.
Qed.

Lemma bv_and_sle_maxs : forall (n : N) (x y : bitvector),
  size x = n -> size y = n ->
  bv_sle (bv_and x y) (bv_and x (signed_max n)) = true.
Proof.
  intros n x y Hx Hy.
  unfold bv_sle, sle_list.
  unfold bv_and.
  rewrite Hx, Hy. rewrite (signed_max_size n). rewrite N.eqb_refl.
  unfold bits.
  replace (size (map2 andb x y)) with n.
  2: { rewrite <- Hx. apply size_len_eq. apply map2_and_length. apply size_len_eq. rewrite Hx, Hy. reflexivity. }
  replace (size (map2 andb x (signed_max n))) with n.
  2: 
    { 
     rewrite <- Hx. apply size_len_eq. apply map2_and_length. 
     apply size_len_eq. rewrite Hx. rewrite (signed_max_size n). easy. 
    }
  rewrite N.eqb_refl.
  rewrite rev_map2_and; auto.
  rewrite rev_map2_and; auto. 
  
  2: { apply size_len_eq. rewrite (signed_max_size n). easy. }
  
  remember (rev x) as rx.
  remember (rev y) as ry.
  remember (rev (signed_max n)) as rmax.

  2: { apply size_len_eq. rewrite Hx, Hy. easy. }
  destruct rmax as [| m_head m_tail].
  {
    assert (Hn_zero : n = 0%N).
    {
      apply (f_equal (@length bool)) in Heqrmax. 
      apply size_len_eq in Heqrmax.
      unfold size in Heqrmax.
      simpl in Heqrmax.
      rewrite length_rev in Heqrmax.
      change (N.of_nat (length (signed_max n))) with (size (signed_max n)) in Heqrmax.
      rewrite signed_max_size in Heqrmax.
      symmetry.
      easy.
    }
    subst n.
    destruct rx.
    -
      destruct ry.
      + 
        simpl. reflexivity.
      + 
        apply (f_equal size) in Heqrx.
        apply (f_equal size) in Heqry.
        rewrite size_rev in Heqry. 
        rewrite Hy in Heqry.
        rewrite Hn_zero in Heqry.
        unfold size in Heqry. simpl in Heqry.
        discriminate.
    -
      apply (f_equal size) in Heqrx.
      rewrite size_rev in Heqrx.
      rewrite Hn_zero in Heqrx.
      discriminate.

  }
  assert (Hm_head : m_head = false). {
  unfold signed_max in Heqrmax.
  unfold smax_big_endian in Heqrmax.
  rewrite rev_involutive in Heqrmax.
  destruct (N.to_nat n) as [| k] eqn:Hnat.
  - discriminate.
  -
    injection Heqrmax as Htail Hhead.
    subst m_head.
    easy.
  }
  subst m_head.
  destruct rx as [| hx tx].
  - simpl. easy.
  -
    destruct ry as [| hy ty].
    +
      exfalso.
      apply f_equal with (f := size) in Heqrx.
      apply f_equal with (f := size) in Heqry.
      rewrite size_rev in *. 
      rewrite Hx in Heqrx.
      rewrite Hy in Heqry.
      rewrite <- Heqry in Heqrx.
      discriminate.
    + 
      simpl.
      destruct hx.
      *
        simpl.
        destruct hy.
        ** reflexivity.
        ** 
          simpl.
          rewrite Bool.orb_false_r.
          replace (map2 andb tx m_tail) with tx.
          *** 
            apply ule_list_big_endian_map2_and.
            apply f_equal with (f := size) in Heqrx.
            apply f_equal with (f := size) in Heqry.
            apply f_equal with (f := N.to_nat) in Heqrx.
            apply f_equal with (f := N.to_nat) in Heqry.
            rewrite non_empty_list_size in Heqrx.
            rewrite non_empty_list_size in Heqry.
            rewrite size_rev in Heqrx.
            rewrite size_rev in Heqry.
            rewrite Hx in Heqrx.
            rewrite Hy in Heqry.
            rewrite <- Heqry in Heqrx.
            injection Heqrx as H_size_eq.
            apply size_len_eq.
            apply N2Nat.inj.
            easy.
          *** 
            symmetry.
            replace m_tail with (mk_list_true (length tx)).
            **** apply map2_and_1_neutral.
            **** 
              unfold signed_max in Heqrmax. 
              unfold smax_big_endian in Heqrmax.
              rewrite rev_involutive in Heqrmax.
              apply f_equal with (f := size) in Heqrx.
              rewrite size_rev in Heqrx.
              apply f_equal with (f := N.to_nat) in Heqrx.
              rewrite non_empty_list_size in Heqrx.
              rewrite Hx in Heqrx.
              rewrite <- Heqrx in Heqrmax.
              injection Heqrmax as H_tail_eq.
              rewrite H_tail_eq.
              f_equal.
              unfold size.
              rewrite Nnat.Nat2N.id.
              easy.
      * 
        simpl. 
        rewrite Bool.orb_false_r.
        replace (map2 andb tx m_tail) with tx.
        **
          apply ule_list_big_endian_map2_and.
          apply f_equal with (f:=size) in Heqrx.
          apply f_equal with (f:=size) in Heqry.
          apply f_equal with (f := N.to_nat) in Heqrx.
          apply f_equal with (f := N.to_nat) in Heqry.
          rewrite non_empty_list_size in Heqrx.
          rewrite non_empty_list_size in Heqry.
          rewrite size_rev in Heqrx.
          rewrite size_rev in Heqry.
          rewrite Hx in Heqrx. 
          rewrite Hy in Heqry.
          rewrite <- Heqry in Heqrx.
          injection Heqrx as H_size_eq.
          apply size_len_eq.
          apply N2Nat.inj.
          easy.
        **
          symmetry.
          replace m_tail with (mk_list_true (length tx)).
          **** apply map2_and_1_neutral.
          **** 
            unfold signed_max in Heqrmax. 
            unfold smax_big_endian in Heqrmax.
            rewrite rev_involutive in Heqrmax.
            apply f_equal with (f := size) in Heqrx.
            rewrite size_rev in Heqrx.
            apply f_equal with (f := N.to_nat) in Heqrx.
            rewrite non_empty_list_size in Heqrx.
            rewrite Hx in Heqrx.
            rewrite <- Heqrx in Heqrmax.
            injection Heqrmax as H_tail_eq.
            rewrite H_tail_eq.
            f_equal.
            unfold size.
            rewrite Nnat.Nat2N.id.
            easy.
Qed.

(* End: bvand_sgt *)

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
