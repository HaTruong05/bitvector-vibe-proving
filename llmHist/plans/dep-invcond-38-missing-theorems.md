# Plan: Fill missing theorems in DepInvCond.v

## Context

`DepInvCond.v` lifts the bitvector invertibility condition proofs from `InvCond.v` into Coq's
dependent type system. `bitvector n` is a sigma type `{v : bitvector // size v = n}`, so
size proofs are carried in the type and witnesses are wrapped with `@MkBitvector n x Hx`.

`InvCond.v` has 64 proved theorems. `DepInvCond.v` has 28. This plan adds the remaining 38.

## Approach

All 38 use the same mechanical lift pattern. Proofs never touch the underlying math — they
only unwrap sigma types, delegate to the untyped theorem from `InvCond`, and rewrap witnesses.

**Standard proof template:**
```coq
Theorem foo : forall (n : N), forall (s t : bitvector n),
  iff LHS (exists (x : bitvector n), P s t x).
Proof. intros.
  destruct s as (s, Hs). destruct t as (t, Ht).
  unfold relevant_ops, bv in *. cbn in *.
  specialize (InvCond.foo n s t Hs Ht); intros.
  destruct H as (H, Ha). split; intros.
  + specialize (H H0). destruct H as (x, (Hx, p)).
    exists (@MkBitvector n x Hx). apply p.    (* or bv_eq_reflect *)
  + apply Ha. destruct H0 as ((x, Hx), H0). now exists x.
Qed.
```

When `exists` is on the **left** of the iff (e.g. `bvmult_slt`, `bvudiv_uge`):
flip which branch calls `H` vs `Ha`.

For **boolean equality** (`bv_eq ... = true`): apply `RAWBITVECTOR_LIST.bv_eq_reflect` to
convert between the raw `bv_eq` bool used in InvCond.v and structural equality where needed.

For **structural equality** in InvCond.v statements (e.g., `bv_and s t = t`, `bv_mult x s = t`):
write `bv_eq ... = true` in the DepInvCond.v statement; use `RAWBITVECTOR_LIST.bv_eq_reflect`
in the proof for conversion.

## 38 Missing Theorems (in InvCond.v order)

### bvand group (lines 125–219)
- `bvand_sgt` — standard template; exists on right
- `bvand_sle` — standard template
- `bvand_sge` — LHS has `bv_and s t = t` (list eq); write `bv_eq (bv_and s t) t = true` in dep stmt; use `bv_eq_reflect` in proof

### bvor group (lines 242–370)
- `bvor_slt` — standard template
- `bvor_sgt` — **iff directions reversed**: InvCond has `(exists...) <-> condition`; dep stmt keeps same order
- `bvor_sle` — standard template
- `bvor_sge` — standard template

### bvshl group (lines 548–984)
- `bvshl_slt` — standard template
- `bvshl_sgt` — standard template
- `bvshl_sle` — standard template
- `bvshl_sge` — standard template
- `bvshl_slt2` — standard template
- `bvshl_sle2` — **extra `(0 < n)%N` hypothesis**: `Theorem bvshl_sle2 : forall (n : N), (0 < n)%N -> forall (s t : bitvector n), iff ...`; pass `Hn` to `InvCond.bvshl_sle2 n Hn s t Hs Ht`

### bvshr group (lines 1088–1200)
- `bvshr_sgt` — standard template
- `bvshr_sge` — standard template

### bvashr group (lines 1380–2500)
- `bvashr_slt` — standard template
- `bvashr_sle` — **argument order flipped**: InvCond has `(t s : bitvector)` not `(s t)`; in dep stmt use `forall (s t : bitvector n)` but call `InvCond.bvashr_sle n t s Ht Hs`
- `bvashr_slt2` — standard template
- `bvashr_sgt2` — standard template
- `bvashr_sle2` — standard template

### bvadd group (line 2515)
- `bvadd_e_dep` — **not an iff**, just existence: `forall (s t : bitvector n), exists x : bitvector n, bv_eq (bv_add x s) t = true`; witness = `bv_subt' t s`; proof: destruct s, t; call `InvCond.bvadd_e`; reconstruct `@MkBitvector n x Hx`; apply `bv_eq_reflect`

### bvmult group (lines 2532–2961)
- `bvmult_eq` — LHS in InvCond uses list equality `bv_and (bv_or (bv_neg s) s) t = t`; dep stmt: `bv_eq (bv_and (bv_or (bv_neg s) s) t) t = true`; RHS: `exists x, bv_eq (bv_mult x s) t = true`; use `bv_eq_reflect` throughout
- `bvmult_neq` — standard template
- `bvmult_ugt` — standard template
- `bvmult_uge` — standard template
- `bvmult_slt` — **exists on left** of iff
- `bvmult_sgt` — **exists on left** of iff
- `bvmult_sle` — standard template
- `bvmult_sge` — standard template

### bvudiv group (lines 2962–3387)
- `bvudiv_uge` — **exists on left** of iff; RHS has `bv_eq (bv_and ...) s = true` (boolean, no conversion needed)
- `bvudiv_reverse_neq` — standard template; RHS has `if N.eq_dec n 1 then ... else ...` — copy verbatim
- `bvudiv_reverse_sgt` — standard template; RHS has `if N.eq_dec n 1 then ... else ...` — copy verbatim
- `bvudiv_reverse_sge` — standard template

### bvurem group (lines 3388–4280)
- `bvurem_slt` — standard template; exists on right
- `bvurem_sle` — standard template
- `bvurem_reverse_eq` — **exists on left** of iff
- `bvurem_reverse_sgt` — **exists on left** of iff
- `bvurem_reverse_sge` — **exists on left** of iff

## Implementation Steps

1. Append each group to `DepInvCond.v` after the `bvadd_dep` theorem
2. Run `make DepInvCond.vo` after each group to catch errors
3. Fix any `bv_eq_reflect` or unfold issues before the next group

## Verification

```bash
make DepInvCond.vo                # must pass
grep "Admitted" DepInvCond.v      # must return nothing
```
