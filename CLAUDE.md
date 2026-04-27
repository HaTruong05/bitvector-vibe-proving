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

## N_scope Infects Tactic Terms

**`Local Open Scope N_scope` (BVList.v line 27)** means bare `-`, `+`, `*` inside tactic arguments (`replace`, `assert`, `ring`) are parsed as `N` operations — even when the values are `Z` or `nat`. Error symptom: `"list2int t" has type "Z" while it is expected to have type "N"`. Fix: always annotate with `%Z` or `%nat`:

```coq
replace (a - b + c)%Z with (a - b + 1 * c)%Z by ring.
assert (Hls : length s = 0%nat) by lia.
replace (length t - 1)%nat with (length s - 1)%nat in H by lia.
```

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
`bv_mult`, `bv_shl`, `bv_shr`, `bv_shl_a`, `bv_concat`

Comparisons: `bv_ult`, `bv_ule`, `bv_ugt`, `bv_uge`, `bv_slt`, `bv_sle`, `bv_sgt`, `bv_sge`

Constants: `zeros`, `one`, `signed_min`, `signed_max`, `mk_list_false`, `mk_list_true`

Bridges: `bv2nat_a`, `bv2int`, `sbv2int`, `pow2_int_N`

Sizes: `bv_shl_size`, `bv_add_size`, `signed_min_size`, `bv_neg_size`, `bv_not_size`

## Checklist Before Claiming a Proof Done

```bash
make InvCond.vo                  # must succeed
grep "Admitted" InvCond.v        # must return nothing
```

If any non-obvious patterns or recurring errors were encountered during the proof, add them to CLAUDE.md now — before reporting done. If nothing surprising came up, skip this step.

## Current Open Problem

**`bvmult_sgt`** (InvCond.v line 2805)
