# P3 STATUS — Lean skeleton for H ≥ 269/400 (2 sorries, both analytic)

Partition P3 of the darkhipo/clz_lemma build. Anchor: `/tmp/clz_lemma/NUMBERS.md`.
Writes confined to `/tmp/clz_lemma/p3-skeleton/` (workspace `ws/` = `cp -c -R` of
`/tmp/clz_prebuild/formal-math/zeta23`, native pins Lean v4.33.0-rc2 / Mathlib 51e6992efd).
Nothing was written to `/tmp/clz_prebuild`, `/tmp/clz_lemma/p1-cert`, `p2-surface`,
`/tmp/qr_rebuild`, `/tmp/omr_prebuild`, or `/Users/dmitri.arkhipov/MultiAgency`.

## 1. What compiles

Command (from `ws/`, host load ~72–75, `LEAN_NUM_THREADS=3`, no `-j`):

```
rm -rf .lake/build/lib/lean/Scratch .lake/build/ir/Scratch       # full clean rebuild of my layer
LEAN_NUM_THREADS=3 lake build Scratch.Bridge269
```

Result, verbatim tail:

```
⚠ [8888/8889] Built Scratch.HGe269 (112s)
warning: Scratch/HGe269.lean:47:8: declaration uses `sorry`
warning: Scratch/HGe269.lean:51:8: declaration uses `sorry`
Build completed successfully (8889 jobs).      ← exit code 0
```

- **rc = 0.** All 8889 jobs (Mathlib + Zeta23 + comparator layer + my three modules) succeed.
- **Warnings from my files: exactly 2**, both `declaration uses 'sorry'` (Lean cites the
  declaration lines 47 and 51; the `sorry` terms themselves sit on lines 48 and 52).
  No unused-variable / deprecation / linter warnings from `Scratch/`.
- Every file also compiles standalone: `LEAN_NUM_THREADS=3 lake env lean Scratch/HGe269.lean` → rc 0.
- One workspace change was required for the cross-module import, appended to `ws/lakefile.toml`
  (original saved at `/tmp/clz_lemma/p3-skeleton/lakefile.toml.orig`):

```toml
[[lean_lib]]
name = "Scratch"
roots = ["Scratch.HGe269", "Scratch.Bridge269", "Scratch.adapter.RaceBound"]
```

Layout in `ws/Scratch/`:

| file | role |
|---|---|
| `adapter/RaceBound.lean` | verbatim copy of `/tmp/clz_prebuild/adapter/RaceBound.lean` (`Race.bound`, `bound_two_thirds`) — proves 2/3 clean |
| `HGe269.lean` | the skeleton: defs, 2 plugs, whole algebraic spine proved, `h_ge_269_400` |
| `Bridge269.lean` | `Race.bound (269/400)`, two provings (Solution-sourced and Zeta23-sourced) |

## 2. Sorry inventory — exactly 2, no third

```
HGe269.lean:47  theorem plug_A : |Real.sin u / u - A_part| ≤ A_err
HGe269.lean:51  theorem plug_B : |Real.cos u - B_part| ≤ B_err
```

Goal states, folded (`u`, `A_part`, … are `def`s) and unfolded — **both forms verified to
typecheck** by `example … := plug_A` / `:= plug_B` at the end of the file:

```
plug_A (folded)    : |Real.sin u / u - A_part| ≤ A_err
plug_A (unfolded)  : |Real.sin (1 / Real.sqrt 2) / (1 / Real.sqrt 2) - 37043 / 40320| ≤ 1 / 5806080
plug_B (folded)    : |Real.cos u - B_part| ≤ B_err
plug_B (unfolded)  : |Real.cos (1 / Real.sqrt 2) - 4379 / 5760| ≤ 1 / 645120
```

with `u : ℝ := 1 / Real.sqrt 2`, `A_part := 37043/40320`, `A_err := 1/5806080`,
`B_part := 4379/5760`, `B_err := 1/645120`.

**Why one-sided forms were NOT used** (deviation from the brief, deliberate): the chain needs
`cos u > 0` as well as `cos u ≤ B_part + B_err`, and `cos u > 0` follows free from the *abs*
form (`B_part − B_err > 0` by `norm_num`). Abs form keeps this at exactly two sorries; the
one-sided pair would have forced either a third sorry or `Real.pi` bounds. Each abs statement
is literally "|exact − partial sum| ≤ first omitted term", the canonical analytic statement.

**The identity step (f) is PROVED, not escalated.** No `Real.pi` bounds anywhere in the file:
`sin u > 0` and `cos u > 0` are derived *from the plugs* (`A_lower`, `B_lower`), which is what
keeps `H_eq` to `field_simp; ring` + the single use of `u^2 = 1/2` in `u_cot_eq`.

## 3. Certificate / arithmetic actually checked by the kernel

| lemma | statement | axioms |
|---|---|---|
| `margin_exact` | `331*(A_part − A_err) − 400*(B_part + B_err) = 821/5806080` | clean |
| `margin` | `400*(B_part + B_err) < 331*(A_part − A_err)` | clean |
| `u_sq` | `u^2 = 1/2` | clean |
| `sqrt2_eq_two_mul_u` | `Real.sqrt 2 = 2*u` | clean |
| `cMT_eq` | `cMT = 2*sval/(1 + sval)` | clean |
| `key_ineq` | `331*(sin u / u) ≥ 400*cos u` | via plugs |
| `s_ge` | `sval = u*tan u ≥ 200/331` | via plugs |
| `cMT_diff_nonneg` / `cMT_ge` | `0 ≤ 2s/(1+s) − 400/531`, `cMT ≥ 400/531` | via plugs |
| `u_cot_eq` | `u * cot u = 1/(2*sval)` | via plugs (needs `sin u ≠ 0`, `cos u ≠ 0`) |
| `H_eq` | `3/2 − (1/√2)·cot(1/√2) = 2 − 1/cMT` | via plugs |
| `H_cMT_ge` | `2 − 1/cMT ≥ 269/400` | via plugs |
| `h_ge_269_400` | `3/2 − (1/√2)·cot(1/√2) ≥ 269/400` | via plugs |

`#print axioms` (verbatim, from the build log):

```
u_sq                : [propext, Classical.choice, Quot.sound]
sqrt2_eq_two_mul_u  : [propext, Classical.choice, Quot.sound]
margin              : [propext, Classical.choice, Quot.sound]
margin_exact        : [propext, Classical.choice, Quot.sound]
cMT_eq              : [propext, Classical.choice, Quot.sound]
sin_pos             : [propext, sorryAx, Classical.choice, Quot.sound]
cos_pos             : [propext, sorryAx, Classical.choice, Quot.sound]
key_ineq            : [propext, sorryAx, Classical.choice, Quot.sound]
s_ge                : [propext, sorryAx, Classical.choice, Quot.sound]
cMT_ge              : [propext, sorryAx, Classical.choice, Quot.sound]
u_cot_eq            : [propext, sorryAx, Classical.choice, Quot.sound]
H_eq                : [propext, sorryAx, Classical.choice, Quot.sound]
H_cMT_ge            : [propext, sorryAx, Classical.choice, Quot.sound]
h_ge_269_400        : [propext, sorryAx, Classical.choice, Quot.sound]
Race.bound_269_400       : [propext, sorryAx, Classical.choice, Quot.sound]
Race.bound_269_400_zeta23: [propext, sorryAx, Classical.choice, Quot.sound]
Race.bound_two_thirds    : [propext, Classical.choice, Quot.sound]   ← untouched adapter, clean
```

Read this precisely: **`sorryAx` has exactly two sources**, `plug_A` and `plug_B`. Every lemma
listed as "via plugs" acquires it only by *consuming* the plugs (e.g. `H_eq` needs
`sin u ≠ 0`/`cos u ≠ 0`, which come from the plugs). No hidden third sorry exists — Lean would
have emitted a third `declaration uses 'sorry'` warning. The algebra-only lemmas
(`u_sq`, `sqrt2_eq_two_mul_u`, `margin`, `margin_exact`, `cMT_eq`) are kernel-clean.

Independent exact-arithmetic cross-check (Python `Fraction`, 40-term series, no floats in the
decision): `|A − A_part| = 1.7145287002508583e-07 ≤ A_err = 1.7223324514991183e-07` ✔;
`|B − B_part| = 1.541520074595698e-06 ≤ B_err = 1.5500992063492063e-06` ✔;
`margin = 821/5806080 > 0` ✔; `s ≥ 200/331` ✔; `cMT ≥ 400/531` ✔;
`H − 269/400 = 7.036794116457344e-07 > 0` ✔. **Both plugs are true**, so the skeleton is not
vacuously satisfiable — but the two margins are thin (≈5% of A_err, ≈1% of B_err), so the plugs
must be proved essentially as stated.

## 4. Integration notes for P4 (who fills the plugs)

**4.1 The analytic content, exactly.** With `u^2 = 1/2`:

```
A = sin u / u = Σ_k (−1)^k (1/2)^k / (2k+1)!     A_part = Σ_{k=0..3}   A_err = k=4 term = 1/5806080
B = cos u     = Σ_k (−1)^k (1/2)^k / (2k)!       B_part = Σ_{k=0..3}   B_err = k=4 term = 1/645120
```

So `A_err` and `B_err` are **exactly the first omitted terms** — the tightest possible Leibniz
bounds, zero slack. Equivalent route: Taylor–Lagrange, `A_err = (1/√2)^9/9!`,
`B_err = (1/√2)^8/8!` (same numbers). **Do not enlarge `A_err`**: the certificate margin is
`821/5806080`, and `331*A_err` is 220× the natural slack there — a materially weaker bound
breaks `margin`.

**4.2 Landing the files.** `HGe269.lean` needs only `import ChallengeDeps` (Mathlib + the trusted
def layer; `cMT` comes from there) — drop it anywhere that can see `ChallengeDeps`.
If the assembly must instead live *inside* the `Zeta23` lib (which does not import
`ChallengeDeps`), then restate the constant against `Zeta23.ThmD.cStar 1` / `HD 1` and transport
the identity with `Solution.cStar_one_eq_cMT` (2 lines); nothing else in the file touches
ChallengeDeps except `cMT`.

**4.3 The bridge has two provings; use whichever fits.**

- `Race.bound_269_400` — from `montgomery_taylor_simple_on_critical_line_mult_cumulative`
  (root namespace, `Solution.lean:88`). Requires `import Solution`.
- `Race.bound_269_400_zeta23` — from `Zeta23.ThmD.thmD₀_simple_mult_cumulative` +
  `Zeta23.ThmD.HD_one`. **Needs no comparator import** — prefer this one if landing in Zeta23.

ε-bookkeeping is trivial and needs no halving: the theorem is instantiated at the *same* `ε`,
because `269/400 ≤ 2 − 1/cMT` holds outright and the multiplier comparison happens pointwise
against `Ncount 0 T ≥ 0` (`Nat.cast_nonneg`).

**4.4 Two gotchas that cost compile rounds, already fixed — keep the fixes.**

1. `linarith` compares atoms *syntactically*, and `Zeta23.Ncount` / `Ncount` are only *defeq*.
   `bound_269_400_zeta23` therefore opens with
   `change ((269:ℝ)/400 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0simple 0 T : ℝ)`
   to move the whole goal into Zeta23's atoms. `exact` (defeq) works across the namespaces;
   `linarith` does not.
2. `rw [one_div]` is a trap: it rewrites `1/cMT` too, and then `exact H_eq` fails on
   `cMT⁻¹` vs `1/cMT` (not definitional — `1/a` is `1 * a⁻¹`). The working move is
   `have h : (Real.sqrt 2)⁻¹ = 1 / Real.sqrt 2 := (one_div _).symm; rw [h]`.

**4.5 `Race.bound` is defined once.** `Bridge269.lean` *imports* the adapter copy
(`Scratch.adapter.RaceBound`) instead of redefining `bound`. Do not import two files that both
declare `Race.bound`. If the adapter is already in your tree under another module name, change
the `import` line and delete `Scratch/adapter/RaceBound.lean` — nothing else depends on it
except `bound_two_thirds`, which is the prebuild's own theorem.

**4.6 Statement shapes are deliberate.** `H_eq` and `h_ge_269_400` are stated with the literal
`(1/Real.sqrt 2) * Real.cot (1/Real.sqrt 2)` (not the `u` def) so that `rw [H_eq]` matches
syntactically inside the theorem the deliverable asked for. Keep that if you refactor.

## 5. Exact goal states P4 will see (paste-ready)

```lean
-- HGe269.lean:47
⊢ |Real.sin u / u - A_part| ≤ A_err

-- HGe269.lean:51
⊢ |Real.cos u - B_part| ≤ B_err
```

## 6. Files

- `/tmp/clz_lemma/p3-skeleton/HGe269.lean` — copy of `ws/Scratch/HGe269.lean` (255 lines)
- `/tmp/clz_lemma/p3-skeleton/Bridge269.lean` — copy of `ws/Scratch/Bridge269.lean` (67 lines)
- `/tmp/clz_lemma/p3-skeleton/ws/` — the compiled workspace (incl. `Scratch/adapter/RaceBound.lean`)
- `/tmp/clz_lemma/p3-skeleton/lakefile.toml.orig` — pre-edit lakefile, for diffing the `Scratch` lib addition
- this file
