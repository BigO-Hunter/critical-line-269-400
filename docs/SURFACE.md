# SURFACE.md — Lean/Mathlib surface survey for the H ≥ 269/400 analytic plugs

Partition **P2** of the darkhipo Lean-lemma build. Anchor: `/tmp/clz_lemma/NUMBERS.md`.
Every theorem name below is backed by a **successful `#check`** whose verbatim output is pasted
here and whose full transcript is in `probes/`. Names recalled from memory appear nowhere.

- **Workspace:** `/tmp/clz_lemma/p2-surface/ws/` — APFS clone (`cp -c -R`, rc=0, 67 s) of
  `/tmp/clz_prebuild/formal-math`. `/tmp/clz_prebuild` was never written to.
- **Pins surveyed (native):** Lean `leanprover/lean4:v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
- **Run recipe:** `cd ws/zeta23 && LEAN_NUM_THREADS=3 lake env lean <probe>.lean`.
  (`lake` here has **no** `-j` flag; parallelism is the Lean runtime thread pool.)
- **Host load:** 68–76 throughout (threshold 110 never reached). No aborts.
- **Pin column convention.** `native` = `#check`-verified at Lean v4.33.0-rc2 + Mathlib 51e6992e (the
  column every receipt below is in). `d13f23b7` = **source-verified only** (grep + signature read at
  `Mathlib d13f23b7…`, no compiled `#check`) — see §7.

**Headline result: the analytic plugs are not just locatable, they are PROVED.** `probes/p6_feasible_full.lean`
compiles with zero errors and zero warnings, and proves all three of:

```
P2Feas.A_bound_N4 : |Real.sin P2Feas.U / P2Feas.U - 37043 / 40320| ≤ 1 / 5806080
P2Feas.cos_bound_N4 : |Real.cos P2Feas.U - 4379 / 5760| ≤ 1 / 645120
P2Feas.target_331_A_ge_400_B : 400 * Real.cos P2Feas.U ≤ 331 * (Real.sin P2Feas.U / P2Feas.U)

'P2Feas.A_bound_N4' depends on axioms: [propext, Classical.choice, Quot.sound]
'P2Feas.cos_bound_N4' depends on axioms: [propext, Classical.choice, Quot.sound]
'P2Feas.target_331_A_ge_400_B' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. These are exactly NUMBERS.md steps 1 and the `331*A ≥ 400*B` target, with the
arguments NUMBERS.md chose (`A_part = 37043/40320`, `B_part = 4379/5760`,
`A_err = 1/5806080`, `B_err = 1/645120`) — so P1's certificate and P3's skeleton need **no renumbering**.

---

## 1. The surface table

`#check` output is verbatim from the transcripts. Pin column: `native` = v4.33.0-rc2 + 51e6992e.

### 1a. Target 1 — the sin/cos power series

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| sin series | `Real.hasSum_sin` | native | `Real.hasSum_sin : ∀ (r : ℝ), HasSum (fun n => (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1).factorial) (Real.sin r)` | `HasSum` over `ℕ` indexed by **k** (the term carries `2n+1`), not by exponent. This is the spelling the Leibniz lemmas want. |
| cos series | `Real.hasSum_cos` | native | `Real.hasSum_cos : ∀ (r : ℝ), HasSum (fun n => (-1) ^ n * r ^ (2 * n) / ↑(2 * n).factorial) (Real.cos r)` | Same shape, `2n`. |
| sin as tsum | `Real.sin_eq_tsum` | native | `Real.sin_eq_tsum : ∀ (r : ℝ), Real.sin r = ∑' (n : ℕ), (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1).factorial` | Only if an equation form is needed; prefer the `HasSum` form because the Leibniz lemmas take a `Tendsto` of partial sums. |
| cos as tsum | `Real.cos_eq_tsum` | native | `Real.cos_eq_tsum : ∀ (r : ℝ), Real.cos r = ∑' (n : ℕ), (-1) ^ n * r ^ (2 * n) / ↑(2 * n).factorial` | ditto |
| complex variants | `Complex.hasSum_sin`, `Complex.hasSum_cos` | native | `Complex.hasSum_sin : ∀ (z : ℂ), HasSum (fun n => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1).factorial) (Complex.sin z)` | Not needed; the real forms exist directly. |

**Gotcha:** there is no lemma indexed by the *exponent*. Every route must convert
`r ^ (2n+1)` into something with `r^2` factored out — see §2 step 2.

### 1b. Target 2 — the truncation bound. **Mathlib HAS a Leibniz truncation bound.**

Location: `Mathlib/Analysis/SpecificLimits/Normed.lean`, section *"Partial sum bounds on alternating
convergent series"* (~line 783). Four lemmas, one per parity/sign combination:

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| antitone, **even** count → **lower** bound | `Antitone.alternating_series_le_tendsto` | native | `@Antitone.alternating_series_le_tendsto : ∀ {E : Type u_1} [inst : Ring E] [inst_1 : PartialOrder E] [IsOrderedRing E] [inst_3 : TopologicalSpace E] [OrderClosedTopology E] {l : E} {f : ℕ → E}, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i) Filter.atTop (nhds l) → Antitone f → ∀ (k : ℕ), ∑ i ∈ Finset.range (2 * k), (-1) ^ i * f i ≤ l` | **THE workhorse.** `2*k` terms, antitone ⇒ lower bound. This is the one that gives `cos u ≥ S₄` and `sin u/u ≥ S₄`. |
| antitone, **odd** count → **upper** bound | `Antitone.tendsto_le_alternating_series` | native | `@Antitone.tendsto_le_alternating_series : ∀ {E : Type u_1} [inst : Ring E] [inst_1 : PartialOrder E] [IsOrderedRing E] [inst_3 : TopologicalSpace E] [OrderClosedTopology E] {l : E} {f : ℕ → E}, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i) Filter.atTop (nhds l) → Antitone f → ∀ (k : ℕ), l ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * f i` | `2*k+1` terms ⇒ upper bound. Gives `cos u ≤ S₅` and `sin u/u ≤ S₅`. |
| monotone, even → upper | `Monotone.tendsto_le_alternating_series` | native | `@Monotone.tendsto_le_alternating_series : … Monotone f → ∀ (k : ℕ), l ≤ ∑ i ∈ Finset.range (2 * k), (-1) ^ i * f i` | Not needed here (our `f` is antitone). |
| monotone, odd → lower | `Monotone.alternating_series_le_tendsto` | native | `@Monotone.alternating_series_le_tendsto : … Monotone f → ∀ (k : ℕ), ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * f i ≤ l` | Not needed here. |
| convergence existence | `Antitone.tendsto_alternating_series_of_tendsto_zero` | native | `@Antitone.tendsto_alternating_series_of_tendsto_zero : ∀ {f : ℕ → ℝ}, Antitone f → Filter.Tendsto f Filter.atTop (nhds 0) → ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i) Filter.atTop (nhds l)` | **Not needed** — we already have the limit from `Real.hasSum_*`. |
| antitonicity idiom | `antitone_nat_of_succ_le` | native | `@antitone_nat_of_succ_le : ∀ {α : Type u_1} [inst : Preorder α] {f : ℕ → α}, (∀ (n : ℕ), f (n + 1) ≤ f n) → Antitone f` | How the `Antitone` hypothesis is discharged. |
| (mirror) | `monotone_nat_of_le_succ` | native | `@monotone_nat_of_le_succ : ∀ {α : Type u_1} [inst : Preorder α] {f : ℕ → α}, (∀ (n : ℕ), f n ≤ f (n + 1)) → Monotone f` | unused |

**How the absolute Leibniz error bound is obtained from these two.** Mathlib gives the *sandwich*
`S_{2k} ≤ l ≤ S_{2k+1}` but **not** the gap bound directly. The gap is one line:

```
| l − S_{2k} | ≤ S_{2k+1} − S_{2k} = f (2k)     -- the first omitted term
```

which is `abs_le.2 ⟨by linarith [lower], by linarith [upper]⟩` once `S_{2k+1}` is rewritten as
`S_{2k} + f(2k)`. **This is the exact primitive NUMBERS.md's `A_err`/`B_err` are defined from**, and
it is what §2 uses.

### 1c. Target 3 — tan / cot

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| tan is a function ℝ→ℝ | `Real.tan` | native | `Real.tan : ℝ → ℝ` | matches zeta23's `cMT` verbatim. |
| cot | `Real.cot` | native | `Real.cot : ℝ → ℝ` | `Real.cot` exists and is `ℝ → ℝ`. |
| tan split | `Real.tan_eq_sin_div_cos` | native | `Real.tan_eq_sin_div_cos : ∀ (x : ℝ), Real.tan x = Real.sin x / Real.cos x` | **exact name as guessed.** Rewrites left-to-right. |
| cot split | `Real.cot_eq_cos_div_sin` | native | `Real.cot_eq_cos_div_sin : ∀ (x : ℝ), x.cot = Real.cos x / Real.sin x` | **exact name as guessed.** Note the statement renders as `x.cot`; as a `rw` lemma it works, but as a **term** it needs the argument: `Real.cot_eq_cos_div_sin _`. |
| tan positivity | `Real.tan_pos_of_pos_of_lt_pi_div_two` | native | `@Real.tan_pos_of_pos_of_lt_pi_div_two : ∀ {x : ℝ}, 0 < x → x < Real.pi / 2 → 0 < Real.tan x` | needed for the `s = u·tan u > 0` leg. |
| x < tan x | `Real.lt_tan` | native | `@Real.lt_tan : ∀ {x : ℝ}, 0 < x → x < Real.pi / 2 → x < Real.tan x` | available; **not used** by the recommended route. |

`Real.cot` definition (source, `Mathlib/Analysis/Complex/Trigonometric.lean:88`):
`nonrec def cot (x : ℝ) : ℝ := cos x / sin x`. `Real.cot_pos_of_pos_of_lt_pi`
**does not exist** (negative result, §4).

### 1d. Target 4 — positivity / monotonicity on (0, π/2), and π bounds

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| sin > 0 | `Real.sin_pos_of_pos_of_lt_pi` | native | `@Real.sin_pos_of_pos_of_lt_pi : ∀ {x : ℝ}, 0 < x → x < Real.pi → 0 < Real.sin x` | **exact name as guessed.** |
| sin > 0 (Ioo) | `Real.sin_pos_of_mem_Ioo` | native | `@Real.sin_pos_of_mem_Ioo : ∀ {x : ℝ}, x ∈ Set.Ioo 0 Real.pi → 0 < Real.sin x` | |
| cos > 0 | `Real.cos_pos_of_mem_Ioo` | native | `@Real.cos_pos_of_mem_Ioo : ∀ {x : ℝ}, x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) → 0 < Real.cos x` | **exact name as guessed.** The interval is the *negative* one too, so `u < π/2` must be supplied by hand. |
| π > 0 | `Real.pi_pos` | native | `Real.pi_pos : 0 < Real.pi` | |
| π > 3 | `Real.pi_gt_three` | native | `Real.pi_gt_three : 3 < Real.pi` | exactly as guessed. |
| π decimals | `Real.pi_gt_d2` / `Real.pi_lt_d2` / `Real.pi_gt_d6` / `Real.pi_lt_d6` | native | `Real.pi_gt_d2 : 3.14 < Real.pi` · `Real.pi_lt_d2 : Real.pi < 3.15` · `Real.pi_gt_d6 : 3.141592 < Real.pi` · `Real.pi_lt_d6 : Real.pi < 3.141593` | the naming scheme is **`pi_gt_d{N}` / `pi_lt_d{N}`** (N = decimal places), up to `pi_gt_d20`/`pi_lt_d20`. |
| sin monotone | `Real.strictMonoOn_sin` | native | `Real.strictMonoOn_sin : StrictMonoOn Real.sin (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))` | |
| sin monotone (usable form) | `Real.sin_lt_sin_of_lt_of_le_pi_div_two` | native | `@Real.sin_lt_sin_of_lt_of_le_pi_div_two : ∀ {x y : ℝ}, -(Real.pi / 2) ≤ x → y ≤ Real.pi / 2 → x < y → Real.sin x < Real.sin y` | |
| tan monotone | `Real.strictMonoOn_tan` | native | `Real.strictMonoOn_tan : StrictMonoOn Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))` | exists (good news). |

`Real.strictMonoOn_cos` **does not exist** (negative result, §4) — use
`Real.cos_lt_cos_of_nonneg_of_le_pi_div_two`.

### 1e. Target 5 — sqrt-2 algebra

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| square the sqrt | `Real.sq_sqrt` | native | `@Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x` | needs the nonneg side condition: `Real.sq_sqrt (by norm_num)`. |
| sqrt positive | `Real.sqrt_pos` | native | `@Real.sqrt_pos : ∀ {x : ℝ}, 0 < √x ↔ 0 < x` | `Real.sqrt_pos.2 (by norm_num)` |
| sqrt nonneg | `Real.sqrt_nonneg` | native | `Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x` | |
| compare sqrt | `Real.sqrt_lt` | native | `@Real.sqrt_lt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (√x < y ↔ x < y ^ 2)` | |
| compare sqrt' | `Real.lt_sqrt` | native | `@Real.lt_sqrt : ∀ {x y : ℝ}, 0 ≤ x → (x < √y ↔ x ^ 2 < y)` | |
| **1 < √2** | `Real.one_lt_sqrt_two` | native | `Real.one_lt_sqrt_two : 1 < √2` | **the lemma `norm_num` cannot replace.** |
| √2 < 3/2 | `Real.sqrt_two_lt_three_halves` | native | `Real.sqrt_two_lt_three_halves : √2 < 3 / 2` | |
| division flip | `div_lt_iff₀` / `div_le_iff₀` | native | `@div_lt_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, 0 < c → (b / c < a ↔ b < a * c)` | root namespace, **no `Real.` prefix**, subscript **`₀`**. |

### 1f. Target 6 — finite-sum splitting

| Purpose | Theorem | Pin | `#check` output (verbatim) | Usage note |
|---|---|---|---|---|
| partial + tail | `HasSum.sum_range_add` | native | `@HasSum.sum_range_add : ∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] {m : M} [ContinuousAdd M] {f : ℕ → M} {k : ℕ}, HasSum (fun n => f (n + k)) m → HasSum f (∑ i ∈ Finset.range k, f i + m)` | `@[to_additive]` off `HasProd.prod_range_mul`. **This is the real name** for "partial sum + tail". |
| tail form | `hasSum_nat_add_iff` | native | `@hasSum_nat_add_iff : ∀ {G : Type u_1} [inst : AddCommGroup G] {g : G} [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ), HasSum (fun n => f (n + k)) g ↔ HasSum f (g + ∑ i ∈ Finset.range k, f i)` | `iff` form when the splitting has to go *backwards*. |
| partial sums tend to the sum | `HasSum.tendsto_sum_nat` | native | `@HasSum.tendsto_sum_nat : ∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] {m : M} {f : ℕ → M}, HasSum f m → Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop (nhds m)` | **required to feed the Leibniz lemmas**, which want `Tendsto (fun n => ∑ i ∈ range n, …) atTop (nhds l)`. For `Real` use `.tendsto_sum_nat`. |
| one-step | `HasSum.zero_add` | native | `@HasSum.zero_add : ∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] {m : M} [ContinuousAdd M] {f : ℕ → M}, HasSum (fun n => f (n + 1)) m → HasSum f (f 0 + m)` | |
| reindex by scalar | `HasSum.div_const` | native | `@HasSum.div_const : ∀ {ι : Type u_1} {α : Type u_2} {L : SummationFilter ι} [inst : DivisionSemiring α] [inst_1 : TopologicalSpace α] [IsTopologicalSemiring α] {f : ι → α} {a : α}, HasSum f a L → ∀ (b : α), HasSum (fun i => f i / b) (a / b) L` | **this is how the `sin u / u` series is produced** from `Real.hasSum_sin`. |
| scale | `HasSum.mul_left` | native | `@HasSum.mul_left : ∀ {ι : Type u_1} {α : Type u_2} {L : SummationFilter ι} [inst : NonUnitalNonAssocSemiring α] [inst_1 : TopologicalSpace α] [IsTopologicalSemiring α] {f : ι → α} {a₁ : α} (a₂ : α), HasSum f a₁ L → HasSum (fun i => a₂ * f i) (a₂ * a₁) L` | |
| unfold tsum | `HasSum.tsum_eq` | native | `@HasSum.tsum_eq : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β} {f : β → α} {a : α} [T2Space α] [L.NeBot], HasSum f a L → ∑'[L] (b : β), f b = a` | |
| uniqueness | `HasSum.unique` | native | `@HasSum.unique : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β} {f : β → α} [T2Space α] [L.NeBot] {a₁ a₂ : α}, HasSum f a₁ L → HasSum f a₂ L → a₁ = a₂` | |

### 1g. Target 7 — zeta23 side (Chunk D). **EPS-FORM CONFIRMED MATCHING NUMBERS.md STEP 4.**

Run from `ws/zeta23` with `import Challenge` (the `cMT` definition and the theorems both live there;
**do not also `import ChallengeDeps` — the two packages collide on `NdistL`**; see §4).

```
cMT : ℝ
def cMT : ℝ :=
√2 * Real.tan (1 / √2) / (1 + 1 / √2 * Real.tan (1 / √2))

montgomery_taylor_on_critical_line : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * ↑(Ncount T (2 * T)) ≤ ↑(N0star T (2 * T))
montgomery_taylor_simple_on_critical_line_mult : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * ↑(Ncount T (2 * T)) ≤ ↑(N0simple T (2 * T))
montgomery_taylor_simple_on_critical_line_mult_cumulative : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * ↑(Ncount 0 T) ≤ ↑(N0simple 0 T)
montgomery_taylor_distinct_mult : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * ↑(Ncount T (2 * T)) ≤ ↑(Ndist T (2 * T))
montgomery_taylor_distinct_mult_cumulative : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * ↑(Ncount 0 T) ≤ ↑(Ndist 0 T)

Ncount : ℝ → ℝ → ℕ     N0star : ℝ → ℝ → ℕ     N0simple : ℝ → ℝ → ℕ
Ndist  : ℝ → ℝ → ℕ     zerosIn : ℝ → ℝ → Set ℂ   zeroMult : ℂ → ℕ
```

| Purpose | Theorem | Pin | Usage note |
|---|---|---|---|
| cMT constant | `cMT` (root ns, `Challenge.lean:119`) | native | Def is **already in the `Real.tan` form** NUMBERS.md needs — no `cot` rewrite is required to *state* anything. |
| **Theorem D, cumulative, simple zeros** | `montgomery_taylor_simple_on_critical_line_mult_cumulative` | native | **This is the right row.** `(2 - 1/cMT - ε) * Ncount 0 T ≤ N0simple 0 T`. |
| Theorem D, dyadic window | `montgomery_taylor_simple_on_critical_line_mult` | native | Same constant, `T < Im ρ ≤ 2T`. Not the row to use (NUMBERS.md step 4 is cumulative). |
| Theorem D, distinct | `montgomery_taylor_distinct_mult_cumulative` | native | `(3/2 - cMT⁻¹/2 - ε)` — the `Ndist` row, different constant. |

**Confirmation requested by the brief:** NUMBERS.md step 4 says the bridge is
"Theorem D cumulative (kappa* ≥ H in eps-form)". The `#check` output above confirms **exactly** that
shape: `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 - 1/cMT - ε) * ↑(Ncount 0 T) ≤ ↑(N0simple 0 T)`. Multiplicative
(no division by `Ncount`), so `Ncount = 0` cannot make it vacuous, matching the existing
`Race.bound` adapter's convention. **Match: yes, verbatim.**

Consequence for the integration: to get `Race.bound (269/400)` you need
`269/400 < 2 − 1/cMT`, i.e. `1/cMT < 531/400`, i.e. `cMT > 400/531` — which is NUMBERS.md's chain
and is what `target_331_A_ge_400_B` (proved above) feeds once `cMT = 2s/(1+s)` with `s = u tan u`.

---

## 2. RECOMMENDED PROOF ROUTE — **series/alternating (Leibniz sandwich), NOT Taylor**

**Recommendation: the alternating-series route, at N = 4, exactly as NUMBERS.md specifies.**
It is proved and compiling (`probes/p6_feasible_full.lean`, 0 errors, 0 warnings, standard axioms).

### Why the series route beats Taylor-Lagrange — measured, not argued

NUMBERS.md's error budget consumes **83%** of the available signal. Concretely:
`331·A_part − 400·B_part = 8.1845e-04` while `331·A_err + 400·B_err = 6.7705e-04`, leaving
`821/5806080 = 1.414e-04`. So the bound must be within a factor of ~1.2 of the true error. I
computed three error models (`p2_arith.py`, exact rationals):

| error model | N=4 verdict | first N that passes | margin there |
|---|---|---|---|
| **Leibniz / alternating (NUMBERS.md)** | **PASS**, margin `+1.414e-04` | **4** | exactly `821/5806080` |
| Taylor–Lagrange, `C = 1` (`taylor_mean_remainder_bound`) | **FAIL**, `−5.41e-02` | 6 | `+2.56e-04` |
| `Real.exp_bound` (the lemma `sin_bound`/`cos_bound` are built on) | FAIL at 4 | ≥ 5 | (not pursued) |

The Taylor–Lagrange bound at the same N is **~102× looser** than the Leibniz bound (ratio
`(2N)(2N+1)/u`). To rescue it you must go to **N = 6**, which changes the partial sums to
`A_part = 391174153/425779200`, `B_part = 88280819/116121600` — i.e. it **invalidates P1's
certificate and P3's chosen constants** for no benefit. The series route reproduces NUMBERS.md's
numbers exactly. That is decisive; **use the series route.**

### The exact working template (copy this into P3)

Imports: `import Mathlib`. Namespace-local `abbrev U : ℝ := 1 / Real.sqrt 2`.

1. **`U_sq : U ^ 2 = 1 / 2`** — `rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]`.
   Do **not** append `norm_num`; the rewrite already closes the goal (it errors "No goals to be solved").
2. **`U_pow : ∀ n, U ^ (2 * n) = (1 / 2 : ℝ) ^ n`** — `intro n; rw [pow_mul, U_sq]`.
   This single lemma is what turns the trig series into a **pure rational** alternating series.
3. **Term sequences.** `bterm n = (1/2)^n / (2n)!` for cos, `aterm n = (1/2)^n / (2n+1)!` for
   `sin u / u`.
4. **Transfer the `HasSum`.**
   - cos: `Real.hasSum_cos U`, then `funext` + `rw [U_pow n, mul_div_assoc]` + `rwa [hfun] at h`.
   - sin: `(Real.hasSum_sin U).div_const U`, then `funext` + `rw [pow_succ, U_pow n]` + `field_simp`.
5. **`Antitone`** via `antitone_nat_of_succ_le`. Recipe that works: rewrite
   `(2*(n+1))! = ((2n+2)*(2n+1)) * (2n)!` (`Nat.factorial_succ` twice, then `push_cast; ring`),
   then `rw [hB, div_le_iff₀ (by positivity), hsplit, pow_succ]`, then `nlinarith` with
   `pow_pos` and `Nat.cast_nonneg`. For `aterm` the factorisation is
   `(2*(n+1)+1)! = ((2n+3)*(2n+2)) * (2n+1)!`.
6. **Sandwich at `k = 2`.**
   `Antitone.alternating_series_le_tendsto h.tendsto_sum_nat hanti 2` → lower (`range 4`),
   `Antitone.tendsto_le_alternating_series h.tendsto_sum_nat hanti 2` → upper (`range 5`).
7. **The rationals.** `simp [bterm, Finset.sum_range_succ, Nat.factorial]; norm_num` reproduces
   `4379/5760`, `4379/5760 + 1/645120`, `37043/40320`, `37043/40320 + 1/5806080` — all four
   verified.
8. **Close.** `rw [abs_le]; constructor <;> linarith`.

### The exact tail-bounding primitive, stated once

> **Leibniz gap bound.** If `f : ℕ → ℝ` is `Antitone`, `l = ∑' n, (-1)^n f n`, then for every `k`:
> `|l − ∑_{i<2k} (-1)^i f i| ≤ f (2k)` — the **first omitted term**.

Obtained by applying the two Mathlib sandwich lemmas at the same `k` and subtracting. This is
precisely `A_err = (1/2)^4/9! = 1/5806080` and `B_err = (1/2)^4/8! = 1/645120`. **No custom
alternating-series machinery has to be built.** (Mathlib's own module docstring at
`NatInt.lean:18` claims a `sum_add_tsum_nat_add` lemma — it does not exist at this pin; the real
name is `HasSum.sum_range_add`. Do not chase the docstring.)

### Taylor route: what it would need, if a later mind insists

`taylor_mean_remainder_bound` **does** exist and **is** general in `n`:

```
@taylor_mean_remainder_bound : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {f : ℝ → E}
  {a b C x : ℝ} {n : ℕ},
  a ≤ b → ContDiffOn ℝ (↑n + 1) f (Set.Icc a b) → x ∈ Set.Icc a b →
    (∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin (n + 1) f (Set.Icc a b) y‖ ≤ C) →
      ‖f x - taylorWithinEval f n (Set.Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / ↑n.factorial
```

So an N=6 variant is *sound*, but it costs: `ContDiffOn` plumbing, an `iteratedDerivWithin` sup bound,
and unfolding `taylorWithinEval` to an explicit polynomial (the painful part — sin's derivatives
alternate `0, 1, 0, -1`, so half the `taylorWithinEval` summands must be killed by hand). All of
that to reach a *worse* margin with *different* constants. Not recommended.

Also available if ever needed: `Real.exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
|exp x − ∑ m ∈ range n, x^m/m!| ≤ |x|^n * (n.succ / (n.factorial * n))` — this is the lemma
`Complex.sin_bound`/`Real.sin_bound` are actually built from (`Mathlib/Analysis/Complex/Trigonometric.lean:545,561`),
and it is general in `n`. `Real.sin_bound` / `Real.cos_bound` themselves are **order-2 only**
(`sin x ≈ x − x³/6`, `cos x ≈ 1 − x²/2`), so they cannot be used for a 4-term plug.

---

## 3. Arithmetic verification (`p2_arith.py`, exact rationals)

Reproduces NUMBERS.md exactly:

```
A_part = 37043/40320      == NUMBERS.md ✓
B_part = 4379/5760        == NUMBERS.md ✓
A_err  = 1/5806080        == NUMBERS.md ✓
B_err  = 1/645120         == NUMBERS.md ✓
exact margin = 821/5806080                  == NUMBERS.md ✓
true 331*A − 400*B          = 2.5859525107e-04
N=4 Leibniz verdict         = +1.414e-04  PASS
```

---

## 4. Negative results (names that do NOT exist / do NOT work at the native pin)

These cost real time if a later mind assumes them. All verified by failed `#check`/compile.

1. **`Real.cot_pos_of_pos_of_lt_pi` — does not exist.** Derive from `cot_eq_cos_div_sin` +
   `Real.cos_pos_of_mem_Ioo` + `Real.sin_pos_of_pos_of_lt_pi` + `div_pos`.
2. **`Real.strictMonoOn_cos` — does not exist.** Use
   `Real.cos_lt_cos_of_nonneg_of_le_pi_div_two` or `Real.cos_lt_cos_of_nonneg_of_le_pi`
   (source-verified at `Trigonometric/Basic.lean:565,570`).
3. **`sum_add_tsum_nat_add` — does not exist**, despite Mathlib's own module docstring naming it
   (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:18`). Real name: **`HasSum.sum_range_add`**.
   Only `NNReal` has a `sum_add_tsum_nat_add` (`Topology/Instances/NNReal/Lemmas.lean:196`).
4. **`tsum_eq_zero_add` — does not exist.** Use `HasSum.zero_add`.
5. **`norm_num` does NOT prove `1 < Real.sqrt 2`** (unsolved goal). Use `Real.one_lt_sqrt_two`.
   Similarly `Real.sqrt 2 < 2` needs `nlinarith [Real.sq_sqrt …]`, not bare `norm_num`.
6. **`div_le_div_iff` / `div_lt_div_iff` — do not exist.** The working names are
   **`div_le_iff₀` / `div_lt_iff₀`** (root namespace, subscript `₀`, `GroupWithZero`).
   Related but different: `div_le_div_iff_right`, `div_le_div_iff'` (`Algebra/Order/Group/Unbundled/Basic.lean`).
7. **`import Challenge` + `import ChallengeDeps` together fails**: `environment already contains 'NdistL'`.
   Import `Challenge` alone (it has both `cMT` and the theorem statements).
8. **`Real.pi_gt_3141592` / `Real.pi_lt_3141593` — do not exist.** The scheme is
   `Real.pi_gt_d6` / `Real.pi_lt_d6`.
9. **`Real.contDiffOn_sin`, `iteratedDeriv_sin`, `iteratedDeriv_cos` — do not exist.**
   Use `Real.contDiff_sin` (+`.contDiffOn`) and `Real.iteratedDeriv_add_one_sin`,
   `Real.iteratedDeriv_add_one_cos`, `Real.iteratedDeriv_even_sin`, `Real.iteratedDeriv_odd_cos`.
10. There is **no** `AlternatingSeries` module; the Leibniz lemmas live in `Analysis/SpecificLimits/Normed.lean`.

---

## 5. What remains for P3 / the integration (honest gap list)

Proved by this partition: both analytic plugs and `331·A ≥ 400·B`. **Not** proved here (out of P2's brief):

- **The algebraic chain** (NUMBERS.md step 2–3): `cot = cos/sin`, `tan = sin/cos`, `s = u·tan u`,
  `cMT = 2s/(1+s)`, and monotonicity of `s ↦ 2s/(1+s)` on `s > −1`. All the pieces are named in
  §1c/§1d. The one non-trivial sub-goal is `cMT = √2·tan(1/√2)/(1 + (1/√2)·tan(1/√2)) = 2s/(1+s)`
  with `s = u·tan u`, `u = 1/√2` — pure `field_simp`/`ring` + `Real.sq_sqrt`, needing `1 + u tan u ≠ 0`.
- **The bridge to `Race.bound`**: NUMBERS.md step 4 → step 5 eps-bookkeeping. `cMT > 400/531` follows
  from `331·A ≥ 400·B` (proved) plus the algebraic chain; then `2 − 1/cMT > 269/400` is `linarith`.
- **`Real.tan` vs `Real.cot` statement mismatch**: zeta23 states `H` as `2 − 1/cMT` (tan form);
  the page states it as `3/2 − u·cot u`. The identity between them is NUMBERS.md step 2 and is
  numeric-only so far (60-digit agreement in `p0_anchor.py`); it is **not** yet formal.

---

## 6. Files

| Path | What it is |
|---|---|
| `SURFACE.md` | this document |
| `p2_arith.py` | exact-rational comparison of the three error models; reproduces NUMBERS.md |
| `probes/p1_series_alt.lean` + `.transcript` | series + Leibniz + sum-splitting `#check`s (rc=0, 0 errors) |
| `probes/p2_trig.lean` + `.transcript` | tan/cot, positivity, π bounds, sqrt-2, tactic capability tests (rc=0, 0 errors) |
| `probes/p3_taylor.lean` + `.transcript` | Taylor/exp_bound surface (rc=0, 0 errors) |
| `probes/p4_zeta23.lean` + `.transcript` | zeta23 `cMT` + Theorem D eps-forms (rc=0, 0 errors) |
| `probes/p5_feasible_cos.lean` + `.transcript` | first feasibility increment: `cos_bound_N4` only (clean compile) |
| **`probes/p6_feasible_full.lean` + `.transcript`** | **THE certificate**: both plugs + `target_331_A_ge_400_B`, axiom-audited. `p5` is subsumed by this. |
| `ws/` | APFS-cloned working copy of the prebuilt workspace |

**`#check` receipts: 90 successful lines** across the six transcripts (p1: 24, p2: 26, p3: 23,
p4: 13, p5: 1, p6: 3), plus 4 `#print axioms` audits and 1 `def cMT` body print. **Zero `error`
lines in every transcript.**

---

## 7. Cross-pin check — Mathlib `d13f23b7` (site pins v4.34.1)

**Method and limit, stated honestly:** this column is **source-verified, not `#check`-verified.**
I grepped and read signatures in the read-only warm tree at
`/tmp/sssp_audit/build/.lake/packages/mathlib` (confirmed `rev = d13f23b723b8a846827a245b89c10fc7d3f11612`
from its `.git/HEAD`). I did **not** compile against it, so the `#check` receipts in §1 are
native-pin-only. A downstream mind that must be certain at the site pins should clone-and-`#check`
(~10 min with the warm oleans) rather than trust this column.

**Result: every name the recommended route depends on is present at d13f23b7, with the same
statement shape.** No drift found.

| Name | d13f23b7 status | Evidence |
|---|---|---|
| `Antitone.alternating_series_le_tendsto` | **present, signature identical** | `Analysis/SpecificLimits/Normed.lean:1010`; read the full statement — `(hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1)^i * f i) atTop (𝓝 l)) (hfa : Antitone f) (k : ℕ) : ∑ i ∈ range (2*k), … ≤ l` — character-identical to native. |
| `Antitone.tendsto_le_alternating_series` | **present, signature identical** | same file, `:1024` |
| `Real.hasSum_cos` / `Real.hasSum_sin` | **present, identical** | `Analysis/SpecialFunctions/Trigonometric/Series.lean:100,105` — term shape `(-1)^n * r^(2n)/(2n)!` unchanged. |
| `HasSum.tendsto_sum_nat` | **present** (generated) | `NatInt.lean:47-49`: `@[to_additive /-- If `f : ℕ → M` has sum `m`, then the partial sums … converge to `m`. -/] theorem HasProd.tendsto_prod_nat`. Same generation as native. |
| `HasSum.sum_range_add` | **present** (generated) | `NatInt.lean:67-68`: `@[to_additive] theorem prod_range_mul`. Same generation as native. |
| `div_le_iff₀` / `div_lt_iff₀` | **both present** | `Algebra/Order/GroupWithZero/Basic.lean:1133,1141` — same `(hc : 0 < c)` signatures. |
| `Real.tan_eq_sin_div_cos`, `Real.cot_eq_cos_div_sin` | **present** | `Analysis/Complex/Trigonometric.lean` |
| `Real.pi_gt_three` | **present** | `Analysis/Real/Pi/Bounds.lean` |
| `Real.one_lt_sqrt_two` | **present** | `Analysis/Real/Sqrt.lean` |
| `Real.sq_sqrt` | **present** | `Analysis/Real/Sqrt.lean` |
| `antitone_nat_of_succ_le` | **present** | `Order/Monotone/Basic.lean` |
| `taylor_mean_remainder_bound`, `exists_taylor_mean_remainder_bound` | **present** | `Analysis/Calculus/Taylor.lean` |
| `Real.cos_pos_of_mem_Ioo`, `Real.sin_pos_of_pos_of_lt_pi` | **present** | `Complex/PhragmenLindelof.lean`, `Trigonometric/Chebyshev/RootsExtrema.lean` (usages; defs unchanged) |

**One addition, not a break:** d13f23b7 has a lemma native lacks —
`Summable.tendsto_alternating_series_tsum {f : ℕ → E} (hfs : Summable f) :
Tendsto (fun n => ∑ i ∈ range n, (-1)^i * f i) atTop (𝓝 (∑' i, (-1)^i * f i))`
(`SpecificLimits/Normed.lean`, right after the two we use). This would let a site-pin proof skip the
`HasSum.tendsto_sum_nat` step. It is **not** required and its absence at native means the portable
spelling is still `h.tendsto_sum_nat`.

**Recommendation:** write P3 against the native spelling (it is the strict subset — every lemma used
exists at both pins). Do not adopt `Summable.tendsto_alternating_series_tsum`.

---

## 8. Bottom line for the orchestrator

- **Route: series/alternating (Leibniz sandwich), N = 4.** Proved, compiling, axiom-clean, and it
  reproduces NUMBERS.md's exact rationals. Taylor-Lagrange is a dead end at N = 4 (fails by `−5.41e-02`)
  and only works from N = 6 with *different* constants.
- **Tail-bounding primitive:** `Antitone.alternating_series_le_tendsto` +
  `Antitone.tendsto_le_alternating_series` at the same `k`, subtracted — giving
  `|l − S_{2k}| ≤ f(2k)`, the first omitted term.
- **Nothing blocking.** The remaining work for P3 is the algebraic chain (`cot`/`tan` rewrites,
  `cMT = 2s/(1+s)`) and the eps-bookkeeping bridge, both of which have every needed name listed above.
