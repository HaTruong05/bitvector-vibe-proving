---
name: Proof patterns
description: Key tactics and gotchas for the bitvector invertibility condition Coq proofs
type: feedback
originSessionId: fe24c107-d527-4d84-8e07-079534026e0b
---
**proj1/proj2 direction for bvmult_eq:**
`bvmult_eq : iff (bv_and M t = t) (∃x. x*s = t)`.
`proj1` = bv_and hypothesis → exists witness. `proj2` = exists → bv_and.
Confusing these is a common mistake.

**Why:** iff is `(A→B) ∧ (B→A)`, proj1 is the forward direction A→B.
**How to apply:** Always double-check which direction you need before writing proj1/proj2.

**N_scope not open in InvCond.v:**
InvCond.v has no `Open Scope N_scope`. Bare `+` in `assert` types defaults to nat.
Use `%N` annotation: `assert (H : n = (size z + 1 + k)%N)`.

**Why:** `Local Open Scope N_scope` is only in BVList.v. The N_scope warning in CLAUDE.md is specifically about BVList.v tactics, but InvCond.v has the same issue in assert types.
**How to apply:** Any N arithmetic in assert types in InvCond.v needs `%N`.

**Implicit args for lemmas defined with Set Implicit Arguments:**
All of n, s, t in bvmult_eq and helpers like bv_and_mult_subt_idemp are implicit.
Use `@bvmult_eq n s T Hs HT` when passing bitvectors explicitly.
Use `bv_and_mult_subt_idemp Hs Ht` (no n/s/t) when they can be inferred.

**Why:** Set Implicit Arguments (BVList.v line 33) makes everything implicit; passing explicit args without @ causes type errors.
**How to apply:** If Coq says "term X has type bitvector while expected size ?a = ?n", you're passing a bitvector where a proof is expected.

**bv_sge_sle_equiv for sge/sle conversion:**
`bv_sge_sle_equiv : bv_sge a b = bv_sle b a`. Use `rewrite bv_sge_sle_equiv in H |- *` to convert.

**bvmult_sgt proof strategy:**
- Forward s=0: x*s=0 and Hxs gives 0<s t; rewrite M to zeros, subt t t = zeros, exact Hxs.
- Forward s≠0: use bvmult_sgt_fwd_key with H_M_eq and HXinM from bvmult_eq.
- Backward: bv_and_mult_subt_idemp gives bv_and M v = v, then bvmult_eq gives witness.

**bvmult_sle proof strategy:**
- Forward: rewrite s=zeros, x*s=zeros, then bv_slt_negb_sle contradicts bv_sle + bv_slt of same pair.
- Backward s=0: bv_slt t (zeros n) = false → last t false = false → zeros_sle_nonneg → witness x=zeros.
- Backward s≠0: MSB of M is 1 (from H_M_neg via bv_slt_zeros) → bv_and_signed_min_neg → signed_min achievable → signed_min_sle.

**bvmult_sge proof strategy:**
- Forward: bv_and_sle_maxs + HXinM (from bvmult_eq) + bv_sle_trans.
- Backward: bv_and M (bv_and M max) = bv_and M max (by bv_and_assoc + bv_and_idem) → max achievable → bvmult_eq witness.

**bvudiv_uge proof strategy (2026-05-09, complete):**
- Core insight: `(∃x. x/s ≥u t) ↔ s*t < 2^n` (no overflow), which equals `bv_and(s*t/t, s) = s`.
- Forward (s=0): `bv_and_0_absorb` + `bv_eq_refl`. Forward (t=0): `Hudiv00` + `bv_and_1_neutral`.
- Forward (s,t≠0): show `S*T ≤ X < 2^n`, so `bv_mult s t = S*T` (mod_small), then `(S*T)/T = S`.
- Backward: extract `bv_ule s (udiv(s*t,t))` from `bv_and(udiv(s*t,t),s) = s` via `bv_ule_and`.
- Convert `bv_ule → bv_uge → not_bv_ult → bv_ult_nat → Nat.ltb_ge` to get nat ≤.
- 8 helper lemmas needed: list2int_eq_Z_of_N_list2N, bv2int_eq_Z_of_nat_bv2nat_a, pow2_int_eq_Z_of_nat_pow2, bv2nat_a_lt_pow2, bv2nat_a_mult_mod, N_size_le_nat, bv2nat_a_udiv_nonzero, bv2nat_a_inj (all in BVList.v).

**Helper lemmas in BVList.v get Set Implicit Arguments:**
When inserting helper lemmas into BVList.v, `Set Implicit Arguments` (line 33) makes bitvector/N args implicit for those lemmas too. So calls like `bv2nat_a_lt_pow2 n x Hx` in InvCond.v must become `bv2nat_a_lt_pow2 Hx`. Also, N_scope means lemma STATEMENTS need `%nat` on conclusions with bare `*`, `mod`, `^`.

**Why:** BVList.v has both `Local Open Scope N_scope` and `Set Implicit Arguments` at the module level. These apply to all lemmas defined inside.
**How to apply:** When moving proofs from test_scratch.v to BVList.v: (1) add `%nat` to conclusions using nat arithmetic, (2) drop explicit bitvector/N args from calls to those same helpers inside InvCond.v.

**`subst n` destroys hypotheses in InvCond.v:**
After `destruct (N.eq_dec n 1) as [Hn1 | Hn1]`, doing `subst n` mysteriously drops hypotheses like `Hs : size s = n` from context. Fix: use `rewrite Hn1 in Hs, Ht, Hx |- *` to substitute n=1 explicitly only where needed. This also makes vm_compute work (concrete n).

**Why:** Unknown Coq 8.20 interaction with how subst handles N-typed variables in this context.
**How to apply:** Never use `subst n` after N.eq_dec — always rewrite into specific hypotheses.

**nat case splits: use unqualified `lt_dec`:**
`Nat.lt_dec` and `Nat.le_or_lt` do not exist in Coq 8.20. Use unqualified `lt_dec` (from Compare_dec, auto-imported):
`destruct (lt_dec (bv2nat_a s) (2^(N.to_nat n) - 1)) as [Hlt | Hge].`

**N to nat conversion for n ≥ 2:**
`N2Nat.inj_le` does not exist. Use the inj_add trick:
`assert (Hn_eq : (n = 2 + (n - 2))%N) by lia. rewrite Hn_eq, N2Nat.inj_add. simpl. lia.`

**Proving 1 ≤ 2^k in nat:**
`Nat.one_le_pow` does not exist. Use `Nat.pow_nonzero`:
`assert (H2ne : (2 <> 0)%nat) by lia. pose proof (Nat.pow_nonzero 2 k H2ne) as Hne. lia.`

**`else True` wrong in theorem with n=0 making LHS false:**
If a theorem has `else True` and for n=0 the LHS (∃x. ...) is false, then False ↔ True is unprovable. Fix: use `else (0 < n)%N` or the concrete n=0 condition.

**bvudiv_reverse_sge n=1 theorem statement was wrong (2026-05-11):**
The original stub lacked a special n=1 case. For n=1, s=-1 (negative), bv_udiv s x = -1 for ALL x, but bv_shr s (one 1) = 0 which is ≥s everything. So ∃x. s/x ≥s 0 is false but RHS was true — contradiction. Fix: add `if N.eq_dec n 1 then bv_sge s t else (...)`, analogous to bvudiv_reverse_sgt.
**Pattern:** Any udiv IC stub with `(s<0 → s>>1 op t)` in the RHS (without n=1 special case) is likely wrong for n=1 negative s. Check stubs before proving.

**bvudiv backward proof — witness strategy:**
- s≥0: witness x = one n. Needs n>0 (use bv_udiv_one). For n=0: vm_compute shows bv_sge/bv_sgt is false/true and handle separately.
- s<0: witness x = nat2bv 2 n. Needs n≥2 (fails for n=1, handle via brute force).
- n=1 cases: brute-force destruct on single-bit bitvectors + vm_compute in *.

**bv_zeros_sle has explicit arg:**
`bv_zeros_sle : forall x : bitvector, bv_sle (zeros (size x)) x = negb (last x false)`.
NOT made implicit by Set Implicit Arguments. Call as `exact (bv_zeros_sle s)`, not `exact bv_zeros_sle`.

**`apply lemma; [exact A | ...]` fails when n not in conclusion:**
`apply lemma` followed by explicit proof args fails with "Unable to find an instance for the variable n" when `n` doesn't appear in the lemma's conclusion (e.g., `bv_urem_ult_s`, `last_bv_neg_pos`, `pos_bvand_pos`, `neg_bvand_neg`). Coq can't infer `n` from the goal alone before the proofs are provided.
Fix: Use `exact (lemma A B C)` instead of `apply lemma; [exact A | exact B | exact C]`. The `exact` form lets Coq infer implicit args from the types of A, B, C at application time.
**Why:** `apply` tries to infer all implicit args from the goal BEFORE generating subgoals; `exact (f args)` infers them from the argument types.
**How to apply:** Whenever you get "Unable to find an instance for n" with apply, switch to `exact (lemma args...)`.

**`[]` causes N_scope parse error in InvCond.v assertions:**
`assert (H : s = [])` fails with "Syntax error: [term] expected after '='" because under N_scope, `[` after `=` is misparse. Use `nil` instead: `assert (H : s = nil)`.
**Why:** Even though InvCond.v doesn't open N_scope, BVList.v's N_scope may affect parsing in some contexts after imports.
**How to apply:** Use `nil` instead of `[]` in theorem statements, assert types, and anywhere `[]` follows `=` or `<>` in InvCond.v.

**`subst n` inside n=0 destruct drops hypotheses (confirmed again):**
Even with `Hn0 : n = 0%N` (not `n = 1`), `subst n` inside a `{...}` focus block drops/renames hypotheses. Fix: Don't subst n at all. Use `rewrite Hn0 in ...` for specific hypotheses, and `rewrite Hn0` in goals. E.g., `split; [exact Hn0 | ...]` instead of `[left; reflexivity | ...]` after subst.
**Why:** Same mysterious Coq 8.20 behavior as documented for n=1 subst.

**signed_min_msb requires (n > 0)%N not (0 < n)%N:**
`signed_min_msb : (n > 0)%N -> last (bits (signed_min n)) false = true`. The `(n > 0)%N` notation differs from `(0 < n)%N` (N.gt vs N.lt). Use `lia` to bridge: `apply signed_min_msb; lia`.

**n=0 theorem with split needs +/- bullets, not nested {}:**
Inside a `{...}` focused block, `split.` followed by `{...}` for subgoals fails to parse (Syntax error). Use `+` bullets inside the outer `{...}`: `{ split. + ... + ... }`. Similarly, `-` bullets inside `{...}` also fail — only `+`, `*`, `**` levels work there.

**`replace` rewrites ALL occurrences — use before inj_sub to avoid contaminating denominator:**
When proving `a mod (a - b) = b` via Z.mod_add, do `rewrite Nat2Z.inj_mod` first (not inj_sub), then `replace (Z.of_nat a)%Z with (Z.of_nat b + 1 * Z.of_nat (a-b))%Z by (rewrite Nat2Z.inj_sub; [ring | lia])`. If you first rewrite `inj_sub`, Z.of_nat a appears in the denominator too, and `replace` would corrupt it.
**Why:** `replace` replaces every syntactic occurrence. After `rewrite Nat2Z.inj_sub`, denominator becomes `Z.of_nat s - Z.of_nat t` and numerator is `Z.of_nat s` — they share `Z.of_nat s`, so replace would transform both.

**Z.mod_unique has 3 subgoals: b≠0, range (with Z.abs), equation. Prefer Z.mod_add+Z.mod_small:**
`apply Z.mod_unique with (q := ...)` generates 3 subgoals: (1) b ≠ 0, (2) 0 ≤ r < |b| (conjunction with Z.abs), (3) a = b*q+r. The Z.abs in (2) is awkward. Prefer the pattern: `replace numerator; rewrite Z.mod_add; apply Z.mod_small`.

**`rewrite Hq0 in HdivS` fails after `destruct ... eqn:Hq0` on compound term:**
`destruct (bv2nat_a s / bv2nat_a x) eqn:Hq0` does NOT substitute in hypotheses. Fix: use `set (q := bv2nat_a s / bv2nat_a x)` to name the expression, then `fold q in HdivS`, then `destruct q as [|q']`. In the 0 case, `simpl in HdivS` gives the simplified form, and `lia` derives contradiction.

**`apply (f_equal Z.of_nat) in H` to convert nat equality to Z equality:**
`Nat2Z.inj` goes Z→nat (wrong direction for injecting). For nat→Z, use `apply (f_equal Z.of_nat) in H`. Then `rewrite !Nat2Z.inj_add in H` expands the coerced sums.

**`set` let-binding generates expanded form after `apply`:**
`set (X := expr)` + `apply (bv2nat_a_ule_iff Hx_sz Hs)` generates goal with `expr` expanded, not `X`. So `rewrite Hval` (which mentions `X`) fails. Fix: use the defining lemma directly inside `apply`, e.g., `apply (bv2nat_a_ule_iff Hshr_sz Hs). rewrite (bv2nat_a_shr_subt_one Hs Hn_nat Hlast_s). pose proof (Nat.div_mod ...); lia.`
**Why:** `apply` unifies implicit args from goal before generating subgoals; the implicit arg comes from the SIZE hypothesis (built before `set`), so the goal is produced with the expanded form.
**How to apply:** Whenever `apply` produces a goal with a let-binding expanded and `rewrite Hval` fails, inline the computation that produced `Hval`.

**`Nat2Z.inj_lt` direction: `(n < m)%nat <-> Z.of_nat n < Z.of_nat m`:**
`proj1 (Nat2Z.inj_lt n m)` goes nat→Z. `proj2` goes Z→nat. To prove `Z.of_nat D < Z.of_nat (S-D)` from `HD_lt_SD : D < S-D`, use `exact (proj1 (Nat2Z.inj_lt D (S-D)) HD_lt_SD)`.
**Why:** The iff has nat form on the LHS, Z form on the RHS (opposite of what intuition might suggest).

**`zeros_size` is NOT implicit; `neg_sle_pos` uses `last (bits a)` not `last a`:**
`zeros_size n : size (zeros n) = n` — the `n` is explicit (no later proof arg to infer from). Call as `zeros_size n`. Also, `neg_sle_pos` requires `last (bits a) false = true/false`, but `bits a = a` definitionally. Pass `last a false = true/false` directly — Coq accepts it by definitional equality.

**`bv_sle_trans` and `bv_sle_trans` have fully implicit bitvector args:**
Call as `bv_sle_trans Hab Hbc` where `Hab : bv_sle a b = true` and `Hbc : bv_sle b c = true`. Do NOT pass `a`, `b`, `c` explicitly.
**Why:** Set Implicit Arguments makes all bitvector forall-args implicit when they appear in proof types.

**`bv_msb_implies_uge_signed_min` for negative bitvectors:**
`bv_msb_implies_uge_signed_min Hs Hn_pos Hlast_s : bv_uge s (signed_min n) = true` when `last s false = true`. Combine with `bv2nat_a_uge_iff` to get `bv2nat_a (signed_min n) ≤ bv2nat_a s`. Combine with `nonneg_ult_signed_min` + `bv_ult_nat` for the t side to prove T < S when s<0 and t≥0.
