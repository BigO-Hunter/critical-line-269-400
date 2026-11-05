/-
RaceBound.lean — the rational-bound adapter for the
https://bigospeedrun.com/other/critical-line-zeros board (kappa* = liminf
N0simple(T)/N(T), zeros with 0 < Im rho <= T, N counted WITH multiplicity,
N0simple counted as simple zeros ON the critical line; HIGHER is better).

Definitions are IMPORTED, not redefined: `Ncount`, `N0simple`, `zeroMult`,
`zerosIn` come from zeta23's trusted Mathlib-only definition layer
(ChallengeDeps.lean, root namespace; all defined from Mathlib's `riemannZeta`
and `analyticOrderAt`). The proof term is zeta23's OWN proved Theorem B
cumulative, `Zeta23.thmB₀_mult_cumulative` (Zeta23/FinalMult.lean:365), which
Solution.lean delegates to under the comparator name
`two_thirds_simple_on_critical_line_cumulative`.

Board quantity: N(T) = Ncount 0 T (window (0,T]), N0simple(T) = N0simple 0 T.

Compile: cd zeta23 && lake env lean adapter/RaceBound.lean
-/
import ChallengeDeps
import Zeta23.FinalMult

namespace Race

/-- `bound c` — the board's proportion bound at rational constant c, in the
eventual multiplied (no-division) ε-form:

    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε) · N(T) ≤ N₀ˢ(T)

This IS "liminf_{T→∞} N₀ˢ(T)/N(T) ≥ c" without naming liminf, and it is
character-for-character the ε-form zeta23 uses for its own statements
(README.md: "'liminf_{T→∞} X(T)/N(T) ≥ c' is formalized in the ε-form
∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)"). Multiplicative form, so
N(T) = 0 can never make a fraction vacuous. -/
def bound (c : ℚ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ((c : ℝ) - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ)

/-- The c = 2/3 instance: zeta23's Theorem B, cumulative form.

The only Lean work is bridging the rational literal `((2/3 : ℚ) : ℝ)` to
the real division `(2 : ℝ) / 3` that Theorem B is stated with; `norm_num`
closes that equality, and the rest is `exact`.

Arithmetic (exact): 2/3 = 0.6666... < 2 − 1/c₁* = 0.6725007037... (the
page's Anthropic row H = 3/2 − (1/√2)·cot(1/√2); the README gives the same
constant as 2 − 1/cMT with 1/cMT = 1/2 + 2^(−1/2)·cot(2^(−1/2))), and
6725/10000 = 0.6725 < 0.6725007037... So a Theorem-B row at 2/3 is a valid
but SUBOPTIMAL board row: the page's own claimed H sits strictly above it,
and zeta23 also proves the higher cumulative bound
`montgomery_taylor_simple_on_critical_line_mult_cumulative`
(∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 − 1/cMT − ε)·Ncount 0 T ≤ N0simple 0 T)
whose constant is irrational — it does not fit `bound (c : ℚ)` directly, but
any rational c < 2 − 1/cMT (e.g. 6725/10000) follows from it by monotonicity. -/
theorem bound_two_thirds : bound (2 / 3) := by
  rw [bound]
  have hcast : ((2 / 3 : ℚ) : ℝ) = (2 : ℝ) / 3 := by norm_num
  rw [hcast]
  exact Zeta23.thmB₀_mult_cumulative

#print axioms bound_two_thirds

end Race
