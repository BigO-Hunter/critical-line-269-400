/-
Bridge269.lean — `Race.bound (269/400)` for the bigospeedrun critical-line board.

`Race.bound` is the adapter's definition (Scratch/adapter/RaceBound.lean, verbatim copy of
the zeta23 adapter): the eventual multiplied ε-form
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ N₀ˢ(T).
The zeta23 side is Theorem D cumulative (simple, with multiplicity)
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 − 1/cMT − ε)·N(T) ≤ N₀ˢ(T),
with cMT the Montgomery–Taylor constant. The bridge is pure ε-bookkeeping: use the SAME ε
(no halving needed), because the two multipliers are compared pointwise on N(T) ≥ 0 and
269/400 ≤ 2 − 1/cMT holds outright (HGe269.H_cMT_ge, i.e. the page bound through the
identity 3/2 − (1/√2)cot(1/√2) = 2 − 1/cMT).
-/
import Scratch.adapter.RaceBound
import Scratch.HGe269
import Solution
import Zeta23.ThmD.Mult

namespace Race

/-- **The board row at 269/400**: liminf N₀ˢ(T)/N(T) ≥ 269/400, in the adapter's ε-form. -/
theorem bound_269_400 : bound (269 / 400) := by
  rw [bound]
  have hcast : ((269 / 400 : ℚ) : ℝ) = (269 : ℝ) / 400 := by norm_num
  rw [hcast]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := montgomery_taylor_simple_on_critical_line_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hD := hT₀ T hT
  have hN : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have hle : (269 : ℝ) / 400 - ε ≤ 2 - 1 / cMT - ε := by
    have hH := H269.H_cMT_ge
    linarith
  have hmul := mul_le_mul_of_nonneg_right hle hN
  linarith [hD]

/-- The same row sourced from the Zeta23 library directly (`ThmD.thmD₀_simple_mult_cumulative`
with the constant rewritten by `ThmD.HD_one`), so a landing inside the Zeta23 development needs
no import of the comparator's `Solution` layer. -/
theorem bound_269_400_zeta23 : bound (269 / 400) := by
  rw [bound]
  have hcast : ((269 / 400 : ℚ) : ℝ) = (269 : ℝ) / 400 := by norm_num
  rw [hcast]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_simple_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  -- the challenge's counting functions are character-for-character Zeta23's (defeq), but
  -- `linarith` compares atoms syntactically, so restate the goal in Zeta23's atoms first.
  change ((269 : ℝ) / 400 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0simple 0 T : ℝ)
  have hD := hT₀ T hT
  have hpage : Zeta23.ThmD.HD 1 = 2 - 1 / cMT := by
    rw [Zeta23.ThmD.HD_one, ← Real.cot_eq_cos_div_sin]
    have h : (Real.sqrt 2)⁻¹ = 1 / Real.sqrt 2 := (one_div _).symm
    rw [h]
    exact H269.H_eq
  rw [hpage] at hD
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have hle : (269 : ℝ) / 400 - ε ≤ 2 - 1 / cMT - ε := by
    have hH := H269.H_cMT_ge
    linarith
  have hmul := mul_le_mul_of_nonneg_right hle hN
  linarith [hD]

#print axioms bound_269_400
#print axioms bound_269_400_zeta23

end Race
