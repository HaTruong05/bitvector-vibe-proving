# Handoff: bvmult_sgt

## Current state

`bvmult_sgt` is `Admitted` at InvCond.v line 2805. `bvmult_sle` (2815) and `bvmult_sge` (2825) also Admitted.

**BVList.v has uncommitted changes — does NOT compile.** Two helper lemmas were added:
- `bv_and_mult_subt_idemp` (line 15873) — compiles fine
- `bvmult_sgt_fwd_key` (line 16018) — one compile error at line 16043

---

## Step 0: Fix BVList.v (one line)

Error at line 16043:
```
The term "Hlen_t" has type "length t = N.to_nat n"
while it is expected to have type "length t = N.to_nat (size z + 1 + k)".
```

Fix: change line 16043 from:
```coq
  { unfold hk, h, kn. rewrite <- N2Nat.inj_add. exact Hlen_t. }
```
to:
```coq
  { unfold hk, h, kn. rewrite <- N2Nat.inj_add, <- Hn_eq. exact Hlen_t. }
```

Then `make BVList.vo` must pass before touching InvCond.v.

---

## The theorem (InvCond.v line 2805)

```coq
Theorem bvmult_sgt: forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  iff
    (exists (x : bitvector), size x = n /\ bv_slt t (bv_mult x s) = true)
    (bv_slt t (bv_subt t (bv_or (bv_or s t) (bv_neg s))) = true).
```

Let `M = bv_or (bv_neg s) s`, `v = bv_subt t (bv_or M t)`.
First rewrite RHS: `bv_or(bv_or s t)(bv_neg s) = bv_or M t` via `bv_or_comm + bv_or_assoc`.

---

## Two helper lemmas in BVList.v

### 1. `bv_and_mult_subt_idemp` (line 15873) — compiles

```coq
Lemma bv_and_mult_subt_idemp : forall (n : N) (s t : bitvector),
  size s = n -> size t = n ->
  bv_and (bv_or (bv_neg s) s) (bv_subt t (bv_or (bv_or (bv_neg s) s) t))
  = bv_subt t (bv_or (bv_or (bv_neg s) s) t).
```

Says `bv_and M v = v`. Used by the **backward direction** of `bvmult_sgt`:
`bv_and M v = v` → `bvmult_eq` gives `∃x, x*s = v` → `t <s x*s = v`. Done.

### 2. `bvmult_sgt_fwd_key` (line 16018) — needs line 16043 fix

```coq
Lemma bvmult_sgt_fwd_key : forall (n : N) (z : bitvector) (k : N) (t x_s : bitvector),
  size t = n -> size x_s = n ->
  n = size z + 1 + k ->
  bv_and (bv_concat (ones (size z + 1)) (zeros k)) x_s = x_s ->
  bv_slt t x_s = true ->
  bv_slt t (bv_subt t (bv_or (bv_concat (ones (size z + 1)) (zeros k)) t)) = true.
```

Used by the **forward direction** (s ≠ 0 case): given `t <s x*s` and `bv_and M (x*s) = x*s`,
produce `t <s v`. Proof uses full integer arithmetic + 4-way case split on last(t)/last(v).

The proof is complete and ~200 lines. It establishes:
- `X = Pk*Xu` (from `bv_and M (x*s) = x*s` + `bv_and_or_neg_zeros_one`)
- `V = Pk*(Tk+1) mod P` (from `list2int_subst_list_formula` + inclusion-exclusion)
- Then `bv_slt_iff_sbv2int` + `unfold sbv2int` + case split on MSBs + `lia`

Abbreviations used: `h = N.to_nat(size z+1)`, `kn = N.to_nat k`, `hk = h+kn`,
`Pk = pow2_int kn`, `Ph = pow2_int h`, `P = pow2_int hk`,
`T = list2int t`, `V = list2int v`, `X = list2int x_s`,
`Tk = list2int(skipn kn t)`, `Xu = list2int(skipn kn x_s)`, `T_lo = list2int(firstn kn t)`

---

## bvmult_sgt proof skeleton (InvCond.v)

```coq
Proof.
  intros n s t Hs Ht.
  assert (HM  : size (bv_or (bv_neg s) s) = n).
  { apply bv_or_size; [apply bv_neg_size|]; exact Hs. }
  assert (HMt : size (bv_or (bv_or (bv_neg s) s) t) = n).
  { apply bv_or_size; [exact HM | exact Ht]. }
  assert (Hv  : size (bv_subt t (bv_or (bv_or (bv_neg s) s) t)) = n).
  { apply bv_subt_size; [exact Ht | exact HMt]. }
  (* Rearrange RHS *)
  assert (HMt_eq : bv_or (bv_or s t) (bv_neg s) = bv_or (bv_or (bv_neg s) s) t).
  { (* bv_or_comm + bv_or_assoc *) ... }
  rewrite HMt_eq. split.

  (* FORWARD: exists x, t <s x*s -> t <s v *)
  - intros (x, (Hx, Hxs)).
    destruct (@zeros_one_factorization s) as [Hzeros | (k, (z, Hfact))].
    + (* s = zeros: x*s = zeros, v = bv_subt t t = zeros, goal = Hxs *)
      rewrite Hzeros, Hs in Hxs. rewrite (@bv_mult_zeros_r n x Hx) in Hxs.
      (* show bv_or(zeros n)t = t, then bv_subt t t = zeros n, then exact Hxs *)
      ...
    + (* s != 0: use bvmult_sgt_fwd_key *)
      assert (H_M_eq : bv_or (bv_neg s) s = bv_concat (ones (size z+1)) (zeros k)).
      { rewrite Hfact, bv_neg_zeros_one. apply bv_or_neg_zeros_one. }
      assert (Hn_eq : n = size z + 1 + k).
      { rewrite <- Hs, Hfact. apply bv_concat_size; [apply bv_concat_size|apply zeros_size];
        [apply zeros_size | apply ones_size]. }  (* or similar *)
      (* bv_and M (x*s) = x*s from bvmult_eq *)
      assert (HXinM : bv_and (bv_or (bv_neg s) s) (bv_mult x s) = bv_mult x s).
      { apply (proj2 (bvmult_eq n s (bv_mult x s) Hs (bv_mult_size Hx Hs))).
        exists x. split; [exact Hx | reflexivity]. }
      rewrite H_M_eq in HXinM.
      (* rewrite goal to use bv_concat M form *)
      rewrite <- H_M_eq.
      apply (bvmult_sgt_fwd_key n z k t (bv_mult x s)
               Ht (bv_mult_size Hx Hs) Hn_eq HXinM Hxs).

  (* BACKWARD: t <s v -> exists x, t <s x*s *)
  - intro H.
    pose proof (bv_and_mult_subt_idemp n s t Hs Ht) as Hidemp.
    destruct (proj1 (bvmult_eq n s _ Hs Hv) Hidemp) as (x, (Hx, Hx_eq)).
    exists x. split. exact Hx. rewrite Hx_eq. exact H.
Qed.
```

---

## Key lemmas

**Sizes:** `bv_or_size`, `bv_and_size`, `bv_subt_size`, `bv_mult_size`, `bv_neg_size`,
`bv_concat_size`, `zeros_size`, `ones_size`, `size_to_length`

**Structure:** `bv_or_comm n a b Ha Hb`, `bv_or_assoc n a b c Ha Hb Hc`,
`bv_or_0_neutral`, `bv_and_0_absorb`, `bv_neg_zeros_zeros`, `bv_neg_zeros_one`,
`bv_or_neg_zeros_one`, `bv_and_or_neg_zeros_one`, `bv_and_or_neg_eq_zeros_one`

**Multiplication:** `bvmult_eq n s t Hs Ht` (InvCond.v 2532), `bv_mult_zeros_r n x Hx`

**Signed:** `bv_slt_iff_sbv2int n x y Hx Hy`, `bv_sle_slt_trans`, `bv_slt_sle_trans`,
`bv_slt_nrefl`, `not_signed_min_if_gt`, `bv_not_neg_slt`, `bv_and_neg_sle_itself`

**Integer:** `list2int_subst_list_formula`, `list2int_map2_and_or_sum`,
`list2int_map_negb_sum`, `list2int_inj`, `list2int_mk_list_false`,
`bv2int_app`, `bv2int_zeros`, `pow2_int_add`, `zero_lt_pow2_int`, `not_list_false_true`,
`last_true_list2int_lb` (line 15291), `last_false_list2int_ub` (line 15594),
`last_append` (line 7601), `length_skipn`, `firstn_length_le`

**Factorization:** `zeros_one_factorization`

---

## Critical gotchas

- **Implicit args** (`Set Implicit Arguments`, BVList.v line 33): drop bitvector/N args;
  use `@` when Coq can't infer. E.g. `@bv_mult_zeros_r n x Hx`, `@list2int_geq_zero l`.
- **N_scope infection**: bare `+`,`-`,`*` in tactic args are N ops. Always `%Z`/`%nat`.
- **bv2int = list2int**: use `change`/`unfold bv2int` to switch between them.
- **bv_subt unfolds**: `bv_subt a b = if size a =? size b then subst_list a b else a`.
  After `unfold bv_subt`, use `rewrite N.eqb_refl` to reduce.
- **set (v := e) folding**: `set` folds syntactically. If `bv_or` is written differently in
  goal vs hypothesis, `set` may not fold uniformly — use `unfold v` to re-expand if needed.
- **sbv2int**: `sbv2int n v = if last v false then (bv2int v - pow2_int_N n)%Z else bv2int v`
- **pow2_int_N vs pow2_int**: `pow2_int_N n = pow2_int (N.to_nat n)`. Bridge: `N2Nat.inj_add`.
- **list2int_subst_list_formula** arg order: `length a = length b` (not `length b = length a`).
  Use `eq_sym` if needed.
