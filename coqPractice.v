From BV Require Import BVList.

Import RAWBITVECTOR_LIST.

Open Scope nat_scope.

Theorem everything : 42 = 42.
Proof.
  reflexivity.
Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.      (* Simplifies 0 + n to n *)
  reflexivity.
Qed.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn].
  - reflexivity.            (* Base case: 0 = 0 + 0 *)
  - simpl.                  (* Inductive step: S n' = S (n' + 0) *)
    rewrite <- IHn.         (* Use inductive hypothesis *)
    reflexivity.
Qed.

From Coq Require Import ZArith.
Open Scope Z_scope.

Theorem Z_plus_comm : forall a b : Z, a + b = b + a.
Proof.
  intros a b.
  apply Z.add_comm. (* Uses a pre-existing lemma from the Z library *)
Qed.

Require Import List.
Import ListNotations.
Open Scope N_scope.

Lemma test : forall (b : bitvector) (n : N), 
size b = n -> bv_ule (zeros n) b = true.
Proof.
intros. induction b.
+ rewrite <- H. 
  assert (size [] = 0). { reflexivity. }
  rewrite H0. 
  assert (zeros 0 = []). { reflexivity. }
  rewrite H1. reflexivity.
+ case a.
(* 
This is actually not easy to prove at all,
but it might be instructive in understanding
the nature of challenges that you may face moving 
forward.
`case a` gives two goals:
  bv_ule (zeros n) (true :: b) = true      -(1)
  bv_ule (zeros n) (false :: b) = true     -(2)
These would both be easy to prove if I had instead:
bv_ule (zeros (n + 1)) (true :: b) = true  -(a)
bv_ule (zeros (n + 1)) (false :: b) = true -(b)
Then, in principle, I could maybe reduce the goal to:
`bv_ule (false :: zeros n) (true :: b) = true`
which I could then reduce to:
`bv_ule (zeros n) b = true`
that I can use from my hypothesis IHb, after I prove to it that
`size b = n` (which you may notice is hard to do because
the hypothesis H says that 
  `size (a :: b) = n`                      -(3)
I would expect H to instead say:
  `size (a :: b) = n + 1`                  -(c)
which would make it straightforward to prove that 
`size b = n`.
All these problems occur because we've done induction on 
`b` which is a list of Booleans, but haven't done 
induction on `n`, the length of `b`. Which is why we
have (a), (b), and (c) instead of (1), (2), and 
(3) that we expect. If we were writing this proof
on white board, we might just assume that (1), (2), 
and (3) are true and move along with our proof. But
you don't get these for free with Coq, you need to do a 
lot more work.
*)