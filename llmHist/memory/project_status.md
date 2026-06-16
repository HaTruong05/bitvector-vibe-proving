---
name: Project status
description: Current completion state of the bitvector invertibility condition proofs
type: project
originSessionId: fe24c107-d527-4d84-8e07-079534026e0b
---
As of 2026-05-17:
- bvudiv_uge proved (2026-05-09): 8 helper lemmas in BVList.v.
- bvudiv_reverse_neq proved (2026-05-10): 3 helper lemmas (bv_udiv_zeros, bv2nat_a_ones, bv2nat_a_zeros_eq).
- bvudiv_reverse_sgt proved (2026-05-10): 6 helper lemmas (bv2nat_a_one, bv_udiv_one, bv2nat_a_shr_one, bv2nat_a_nat2bv_two, bv_sle_udiv_nonneg, bv_sle_udiv_shr).
- bvudiv_reverse_sge proved (2026-05-11): THEOREM STATEMENT FIXED — added n=1 special case (bv_sge s t) analogous to bvudiv_reverse_sgt. The original stub was wrong (false for n=1, s=-1, t=0). Proof reuses same helpers.
- bvurem_slt proved (2026-05-15): helper lemma bv_neg_signed_min added to BVList.v. Proof covers n=0 case, forward (3 sub-cases) and backward (3 sub-cases).
- bvurem_sle proved (2026-05-15): THEOREM STATEMENT FIXED — added `n = 0%N \/` disjunct. Helper lemma bv_slt_not_zeros_nonneg added to BVList.v.
- bvurem_reverse_eq proved (2026-05-16): 7 helper lemmas in BVList.v (list2int_bv_add_twice, list2int_bv_subt, list2int_bv_and_or_sum, bv2nat_a_subt_ule, bv2nat_a_ule_iff, bv2nat_a_uge_iff, bv2nat_a_bv_and_or_add, list2int_bv_subt_2t_s). Key techniques: inclusion-exclusion (M+OR=A+S), Z.mod_add+Z.mod_small for forward, bv_subt s t witness for backward (S>2T case), zeros n witness for s=t case.
- bvurem_reverse_sgt proved (2026-05-17): 3 helper lemmas in BVList.v (bv2nat_a_urem_le_s, last_bv_urem_nonneg, bv2nat_a_shr_subt_one). Key: when s<0, max achievable non-negative urem is (S-1)/2, achieved by x = S - (S-1)/2. Forward uses 2r < S (from q ≥ 1) to bound urem ≤ (S-1)/2. `set` let-binding with `apply` generates expanded goal — use the lemma directly in apply rather than rewriting.
- bvurem_reverse_sge proved (2026-05-17): No new BVList.v helpers (reuses sgt helpers). Key differences from sgt: (1) s≥0 forward uses bv_sle_trans instead of bv_slt_sle_trans; (2) backward s<0 t<0: witness x=one n gives urem=zeros n ≥s t (negative); (3) backward s<0 t≥0: need T ≤ (S-1)/2 from bv_ugt(s-t,t) via signed_min bounds (bv_msb_implies_uge_signed_min + nonneg_ult_signed_min) to show T < S.

**DepInvCond.v completed (2026-06-02):** All 38 missing dependent-type theorems added — bvand_sgt/sle/sge, bvor_slt/sgt/sle/sge, bvshl_slt/sgt/sle/sge/slt2/sle2, bvshr_sgt/sge, bvashr_slt/sle/slt2/sgt2/sle2, bvadd_e_dep, bvmult_eq/neq/ugt/uge/slt/sgt/sle/sge, bvudiv_uge/reverse_neq/sgt/sge, bvurem_slt/sle/reverse_eq/sgt/sge. DepInvCond.v now has 66 theorems, zero Admitted. Full build passes.

**Next open problems:** InvCond.v complete (zero Admitted); DepInvCond.v complete (zero Admitted). No more known open work.

**CLAUDE.md moved (2026-06-15):** CLAUDE.md, HANDOFF.md, and .claudeignore were moved to llmHist/. CLAUDE.md is no longer at the project root and will NOT be auto-loaded by Claude Code. Load it manually if needed: `llmHist/CLAUDE.md`.

**Why:** DepInvCond.v lifts InvCond.v proofs to Coq dependent bitvector types.
**How to apply:** Start each session by grepping for Admitted in both InvCond.v and DepInvCond.v.
