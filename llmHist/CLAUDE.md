# CLAUDE.md

## Project

Formally verifying cvc5's bit-vector invertibility conditions (Niemetz) in Coq 8.20.0.
Invertibility conditions have the form `(∃x. f(x) op t) ↔ g(s, t)` over bitvectors.

**Only two files matter:**

- `BVList.v` — bitvector library (14k+ lines). Helper lemmas go here, added toward the end but before `End RAWBITVECTOR_LIST.`
- `InvCond.v` — the invertibility condition proofs. All IC work goes here.

## Build

Run from the repo root:

```bash
make InvCond.vo   # fast: recompile InvCond.v only
make              # full build
```

`_CoqProject` registers files under the `BV` namespace. Imports look like:

```coq
From BV Require Import BVList.
```

## Core Principle

**Build incrementally, structure before solving, trust the type checker.**
Success = `make InvCond.vo` passes + zero `Admitted` + no new `Axiom`s.

Proof workflow:

1. **Structure first.** Sketch the argument with `assert`/`pose proof` before writing tactics.
2. **Helper lemmas in BVList.v.** If an inline subproof exceeds ~20 lines, extract it there.
3. **One `Admitted` at a time.** Fill one hole, compile, stop on error.
4. **Reflect after each theorem.** Update CLAUDE.md with any non-obvious _patterns_ or _error fixes_.

## Implicit Arguments

**`BVList.v` line 33: `Set Implicit Arguments`.** All `forall (x : bitvector)` and `forall (n : N)` args are implicit — pass only proofs, bitvectors are inferred. Error symptom: `"s" has type "bitvector" while expected "bv_sle ?a ?b = true"`. Fix: drop the bitvector args, or prefix with `@` to make them explicit again.

**Watch out for list arguments made implicit.** `list2int_geq_zero`, `list2int_lt_pow2_int`, and `bv_and_idem2` all have their list/bitvector argument implicit. When the argument can't be inferred from the goal, Coq reports "Unable to find an instance for n" or a type mismatch. Use `@` to pass explicitly:

```coq
pose proof (@list2int_geq_zero l) as H.
pose proof (@list2int_lt_pow2_int l (length l) eq_refl) as H.
exact (@bv_and_idem2 x s n Hx Hs).
```

## N_scope Infects Tactic Terms and Lemma Statements

**`Local Open Scope N_scope` (BVList.v line 27)** means bare `-`, `+`, `*` inside tactic arguments (`replace`, `assert`, `ring`) are parsed as `N` operations — even when the values are `Z` or `nat`. Error symptom: `"list2int t" has type "Z" while it is expected to have type "N"`. Fix: always annotate with `%Z` or `%nat`:

```coq
replace (a - b + c)%Z with (a - b + 1 * c)%Z by ring.
assert (Hls : length s = 0%nat) by lia.
replace (length t - 1)%nat with (length s - 1)%nat in H by lia.
```

**This also affects lemma statement conclusions.** If you write a helper lemma in BVList.v whose conclusion has bare `*`, `mod`, or `^` over `nat` values, they'll be parsed as `N` operators. Fix: wrap the conclusion with `%nat`:

```coq
(* Wrong — * and mod parsed as N operators *)
bv2nat_a (bv_mult s t) = (bv2nat_a s * bv2nat_a t) mod 2^(N.to_nat n).
(* Right *)
(bv2nat_a (bv_mult s t) = (bv2nat_a s * bv2nat_a t) mod 2^(N.to_nat n))%nat.
```

## Helper Lemmas in BVList.v Inherit Implicit Arguments

When inserting helper lemmas into BVList.v, `Set Implicit Arguments` (line 33) makes bitvector/N forall-args implicit when they can be inferred from a proof argument. A call like `bv2nat_a_lt_pow2 n x Hx` in test_scratch.v (where args are explicit) must become `bv2nat_a_lt_pow2 Hx` in InvCond.v (which imports the lemma from BVList.v). Error symptom: `"n" has type "N" while expected "size ?a = ?n"` — you're passing a bitvector/N where a proof is expected.

## Integer Bridges (critical for signed arithmetic)

| Bridge      | Type                | Meaning                                         |
| ----------- | ------------------- | ----------------------------------------------- |
| `bv2nat_a`  | `bitvector → nat`   | Unsigned natural number                         |
| `bv2int`    | `bitvector → Z`     | Unsigned Z (0..2ⁿ-1)                            |
| `sbv2int n` | `N → bitvector → Z` | Signed two's-complement Z (-2^(n-1)..2^(n-1)-1) |

`sbv2int n v = bv2int v - 2ⁿ` if MSB=1, else `bv2int v`.

## Finding Lemmas in BVList.v

**NEVER `cat BVList.v` or read the full file.** It is 14,000+ lines.

**Step 1 — Grep for candidate names:**

```bash
grep -n "Lemma\|Theorem" BVList.v | grep -i "keyword"
```

**Step 2 — Read only the relevant line range:**
Use the line number from grep to read ~30 lines around the lemma.

**Keyword index** — seed your searches with these names:

Operations: `bv_and`, `bv_or`, `bv_xor`, `bv_not`, `bv_neg`, `bv_add`, `bv_subt'`,
`bv_mult`, `bv_shl`, `bv_shr`, `bv_shl_a`, `bv_concat`, `bv_udiv`, `bv_urem`

Comparisons: `bv_ult`, `bv_ule`, `bv_ugt`, `bv_uge`, `bv_slt`, `bv_sle`, `bv_sgt`, `bv_sge`

Constants: `zeros`, `one`, `signed_min`, `signed_max`, `mk_list_false`, `mk_list_true`

Bridges: `bv2nat_a`, `bv2int`, `sbv2int`, `pow2_int_N`

Sizes: `{operation}_size`

## Checklist Before Claiming a Proof Done

```bash
make InvCond.vo                  # must succeed
grep "Admitted" InvCond.v        # must return nothing
```

If any non-obvious patterns or recurring errors were encountered during the proof, add them to CLAUDE.md now — before reporting done. If nothing surprising came up, skip this step.

## `subst n` Destroys Hypotheses in InvCond.v

**`subst n` after `N.eq_dec n 1` mysteriously drops hypotheses** (e.g., `Hs : size s = n` vanishes). Fix: use `rewrite Hn in Hs, Ht, Hx |- *` explicitly to substitute n=1 only where needed. This also makes `vm_compute` work (concrete n, not abstract).

## nat Case Splits: Use Unqualified `lt_dec`

`Nat.lt_dec` and `Nat.le_or_lt` do **not** exist in Coq 8.20. Use unqualified `lt_dec` (from `Coq.Arith.Compare_dec`, auto-imported):

```coq
destruct (lt_dec (bv2nat_a s) (2^(N.to_nat n) - 1)) as [Hlt | Hge].
```

## Converting N ≥ 2 to N.to_nat n ≥ 2

`N2Nat.inj_le` does not exist. Use the `inj_add` trick:

```coq
assert (Hn_eq : (n = 2 + (n - 2))%N) by lia.
rewrite Hn_eq, N2Nat.inj_add. simpl. lia.
```

## Proving 1 ≤ 2^k (nat)

`Nat.one_le_pow` does not exist. Use `Nat.pow_nonzero`:

```coq
assert (H2ne : (2 <> 0)%nat) by lia.
pose proof (Nat.pow_nonzero 2 k H2ne) as Hne. lia.
```

## Theorem Statements With `else True` for n=0

`else True` is wrong when n=0 makes the LHS (exists x. ...) **false**: `False ↔ True` is unprovable. Use `else (0 < n)%N` or the actual n=0 condition.

## `have` Syntax Fails; Use `assert`

`have X : T by tac` is invalid in this context. Always use `assert (X : T) by tac`.

## Lemmas About `last` and `zeros`

`last_mk_list_false` expects `last (mk_list_false k) false` — it does NOT match `last (zeros n) false` directly. Add `unfold zeros` first. Likewise, `bv_neg_zeros_zeros` rewrites to `zeros n`, not `mk_list_false`, so `unfold zeros` is needed after both rewrites before applying `last_mk_list_false`.

## `last_bv_neg_neg_nonmin` Needs `s ≠ signed_min n`, NOT `s ≠ zeros n`

When trying to show `last (-t) false = false` from `last t false = true`, the lemma `last_bv_neg_neg_nonmin` requires `t ≠ signed_min n`. If you only have `t ≠ zeros n`, case-split on `t = signed_min n`:

- If `t = signed_min n`: use `Hrhs` for the contradiction (RHS contains `bv_slt (bv_not t) ...` = `bv_slt (signed_max n) ...`, but `signed_max_sle_any` + `bv_slt_negb_sle` give `False`).
- If `t ≠ signed_min n` and `last t false = true`: `last_bv_neg_neg_nonmin` gives `last (-t) = false`, contradicting `Hlast_neg_t`.

Key helper chain: `bv_not (signed_min n) = signed_max n` via `signed_min_eq_not_smax` + `bv_not_involutive`. Then `signed_max_sle_any` gives `bv_sle (bv_or ...) (signed_max n) = true`, and `bv_slt_negb_sle` makes the contradiction.

## Bridging list2int and bv2nat_a

`last_true_list2int_lb` and `last_false_list2int_ub` return bounds on `list2int v`. To connect with `Z.of_nat (bv2nat_a v)`: use `change (list2int v) with (bv2int v) in H` then `rewrite bv2int_eq_Z_of_nat_bv2nat_a in H`.

## Subagents

Do NOT spawn subagents for proof work. All Coq proof attempts must be done inline in the main conversation.

## Current Open Problem

All bvurem IC stubs complete as of 2026-05-17. Run `grep -n "Admitted" InvCond.v` to find the next open stub.
