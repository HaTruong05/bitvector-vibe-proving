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
4. **Clean context.** `clear` irrelevant hypotheses before calling `nia`/`lia`.

## Implicit Arguments

**`BVList.v` line 33: `Set Implicit Arguments`.** All `forall (x : bitvector)` and `forall (n : N)` args are implicit — pass only proofs, bitvectors are inferred. Error symptom: `"s" has type "bitvector" while expected "bv_sle ?a ?b = true"`. Fix: drop the bitvector args, or prefix with `@` to make them explicit again.

## Integer Bridges (critical for signed arithmetic)

| Bridge      | Type                | Meaning                                         |
| ----------- | ------------------- | ----------------------------------------------- |
| `bv2nat_a`  | `bitvector → nat`   | Unsigned natural number                         |
| `bv2int`    | `bitvector → Z`     | Unsigned Z (0..2ⁿ-1)                            |
| `sbv2int n` | `N → bitvector → Z` | Signed two's-complement Z (-2^(n-1)..2^(n-1)-1) |

`sbv2int n v = bv2int v - 2ⁿ` if MSB=1, else `bv2int v`.

Key bridge lemma: `bv_slt_iff_sbv2int` — connects `bv_slt` to `<` on Z via `sbv2int`.
For unsigned arithmetic, prefer `bv_ult_nat` (connects `bv_ult` to `<?` on nat).

## Finding Lemmas in BVList.v

**NEVER `cat BVList.v` or read the full file.** It is 14,000+ lines.

**Step 1 — Grep for candidate names:**

```bash
grep -n "Lemma\|Theorem" BVList.v | grep -i "keyword"
```

**Step 2 — Read only the relevant line range:**
Use the line number from grep to read ~30 lines around the lemma.

**Step 3 — For type-guided search, use a temp file:**

```coq
(* temp_search.v *)
From BV Require Import BVList.
Search bv_shl bv_slt.
SearchPattern (bv_slt _ _ = true).
SearchRewrite (sbv2int (bv_shl _ _)).
```

Compile with `coqc temp_search.v`, then delete the file.

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

## Remaining Admitted Theorems (2)

In file order:

1. **`bvand_sge`** (line 196): `(s & t = t) ∨ (t <s (t - s) & s) ↔ ∃x. x & s ≥s t`
2. **`bvor_slt`** (line 224): `~(s - t) | s <s t ↔ ∃x. x | s <s t`
