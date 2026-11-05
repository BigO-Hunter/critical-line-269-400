/-
HGe269.lean — the page constant of the bigospeedrun critical-line board

    H = 3/2 − (1/√2)·cot(1/√2) ≥ 269/400

proved from exactly TWO analytic plugs (the alternating-series remainder bounds for
A = sin u / u and B = cos u at u = 1/√2, N = 4 terms each), and pure algebra otherwise.

Chain (all positive quantities):
    331·A ≥ 400·B  ⇒  s = u·tan u ≥ 200/331  ⇒  cMT = 2s/(1+s) ≥ 400/531  ⇒  H ≥ 269/400
plus the identity H = 2 − 1/cMT linking the page form to zeta23's Theorem-D form.

N = 4 certificate (exact rationals):
    A_part = 37043/40320,  A_err = 1/5806080
    B_part = 4379/5760,    B_err = 1/645120
    331·(A_part − A_err) − 400·(B_part + B_err) = 821/5806080 > 0
-/
import ChallengeDeps
import Scratch.P2Plugs

noncomputable section
open Real

namespace H269

/-- u = 1/√2 — the paper's window parameter ϑ = λ/√2 at λ = 1. -/
def u : ℝ := 1 / Real.sqrt 2

/-- N = 4 partial sum of A = sin u / u = Σ_k (−1)^k (1/2)^k/(2k+1)!. -/
def A_part : ℝ := 37043 / 40320
/-- Alternating-series remainder bound for A at N = 4. -/
def A_err : ℝ := 1 / 5806080
/-- N = 4 partial sum of B = cos u = Σ_k (−1)^k (1/2)^k/(2k)!. -/
def B_part : ℝ := 4379 / 5760
/-- Alternating-series remainder bound for B at N = 4. -/
def B_err : ℝ := 1 / 645120

/-- s = u·tan u (the quantity the Montgomery–Taylor constant is written through). -/
def sval : ℝ := u * Real.tan u

/-! ## The two analytic plugs (SORRY 1 and SORRY 2)

Both are the standard alternating-series remainder bound: the exact value differs from
the N = 4 partial sum by at most the first omitted term.  u² = 1/2 makes every term an
exact rational, so the bounds are exact rational inequalities once the series is in hand. -/

/-- SORRY 1 (analytic): |sin u / u − A_part| ≤ A_err.
    FILLED (P4): P2Feas.A_bound_N4 — Mathlib Leibniz sandwich
    (Antitone.alternating_series_le_tendsto / tendsto_le_alternating_series at k=2)
    over the rational series for sin U / U with U = 1/√2. Abs form is direction-safe
    by construction (P1 trap §11): the chain consumes (abs_le.mp ·).1 = the LOWER side. -/
theorem plug_A : |Real.sin u / u - A_part| ≤ A_err := by
  unfold u A_part A_err
  exact P2Feas.A_bound_N4

/-- SORRY 2 (analytic): |cos u − B_part| ≤ B_err.
    FILLED (P4): P2Feas.cos_bound_N4 — same Leibniz sandwich for cos U.
    The chain consumes (abs_le.mp ·).2 = the UPPER side. -/
theorem plug_B : |Real.cos u - B_part| ≤ B_err := by
  unfold u B_part B_err
  exact P2Feas.cos_bound_N4

/-! ## Elementary facts about u -/

theorem sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := by positivity

theorem u_pos : 0 < u := by
  unfold u
  positivity

theorem u_ne : u ≠ 0 := ne_of_gt u_pos

theorem u_sq : u ^ 2 = 1 / 2 := by
  unfold u
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- √2 = 2·u — this is what turns cMT's √2·tan u into 2·s. -/
theorem sqrt2_eq_two_mul_u : Real.sqrt 2 = 2 * u := by
  unfold u
  have h2 : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## Consequences of the plugs -/

theorem A_lower : A_part - A_err ≤ Real.sin u / u := by
  have h := (abs_le.mp plug_A).1
  linarith

theorem B_upper : Real.cos u ≤ B_part + B_err := by
  have h := (abs_le.mp plug_B).2
  linarith

theorem B_lower : B_part - B_err ≤ Real.cos u := by
  have h := (abs_le.mp plug_B).1
  linarith

theorem A_pos : (0 : ℝ) < A_part - A_err := by
  unfold A_part A_err
  norm_num

theorem B_pos : (0 : ℝ) < B_part - B_err := by
  unfold B_part B_err
  norm_num

theorem cos_pos : 0 < Real.cos u := by
  linarith [B_lower, B_pos]

theorem sin_pos : 0 < Real.sin u := by
  have hu0 : u ≠ 0 := u_ne
  have hq : 0 < Real.sin u / u := by linarith [A_lower, A_pos]
  have heq : Real.sin u = u * (Real.sin u / u) := by field_simp
  rw [heq]
  exact mul_pos u_pos hq

/-- The exact N = 4 margin: 331·(A_part − A_err) > 400·(B_part + B_err). -/
theorem margin : 400 * (B_part + B_err) < 331 * (A_part - A_err) := by
  unfold A_part A_err B_part B_err
  norm_num

/-- The certificate value: 331·(A_part − A_err) − 400·(B_part + B_err) = 821/5806080. -/
theorem margin_exact :
    331 * (A_part - A_err) - 400 * (B_part + B_err) = 821 / 5806080 := by
  unfold A_part A_err B_part B_err
  norm_num

/-- Step (b): 331·(sin u / u) ≥ 400·cos u, from the plugs plus `margin`. -/
theorem key_ineq : 331 * (Real.sin u / u) ≥ 400 * Real.cos u := by
  have h1 : 331 * (A_part - A_err) ≤ 331 * (Real.sin u / u) := by linarith [A_lower]
  have h2 : 400 * Real.cos u ≤ 400 * (B_part + B_err) := by linarith [B_upper]
  linarith [margin]

/-! ## The chain s ≥ 200/331 ≥ ... -/

/-- s written as u·sin u / cos u. -/
theorem sval_eq : sval = u * Real.sin u / Real.cos u := by
  unfold sval
  rw [Real.tan_eq_sin_div_cos]
  ring

theorem sval_cos : sval * Real.cos u = u * Real.sin u := by
  have hcos_ne : Real.cos u ≠ 0 := ne_of_gt cos_pos
  rw [sval_eq]
  field_simp

/-- Step (c): s = u·tan u ≥ 200/331. -/
theorem s_ge : sval ≥ 200 / 331 := by
  have hu0 : u ≠ 0 := u_ne
  have hsin : u * (Real.sin u / u) = Real.sin u := by field_simp
  have hmul1 : 400 * (u * Real.cos u) ≤ 331 * Real.sin u := by
    have hm : u * (400 * Real.cos u) ≤ u * (331 * (Real.sin u / u)) :=
      mul_le_mul_of_nonneg_left key_ineq (le_of_lt u_pos)
    calc 400 * (u * Real.cos u) = u * (400 * Real.cos u) := by ring
      _ ≤ u * (331 * (Real.sin u / u)) := hm
      _ = 331 * (u * (Real.sin u / u)) := by ring
      _ = 331 * Real.sin u := by rw [hsin]
  have hmul2 : 200 * Real.cos u ≤ 331 * sval * Real.cos u := by
    have hm : u * (400 * (u * Real.cos u)) ≤ u * (331 * Real.sin u) :=
      mul_le_mul_of_nonneg_left hmul1 (le_of_lt u_pos)
    calc 200 * Real.cos u = 400 * u ^ 2 * Real.cos u := by rw [u_sq]; norm_num
      _ = u * (400 * (u * Real.cos u)) := by ring
      _ ≤ u * (331 * Real.sin u) := hm
      _ = 331 * (sval * Real.cos u) := by rw [sval_cos]; ring
      _ = 331 * sval * Real.cos u := by ring
  have h3 : 200 ≤ 331 * sval := le_of_mul_le_mul_right hmul2 cos_pos
  linarith

theorem sval_pos : 0 < sval := by
  have h : (0 : ℝ) < 200 / 331 := by norm_num
  linarith [s_ge]

theorem sval_ne : sval ≠ 0 := ne_of_gt sval_pos

theorem one_add_sval_pos : 0 < 1 + sval := by linarith [sval_pos]

theorem one_add_sval_ne : 1 + sval ≠ 0 := ne_of_gt one_add_sval_pos

/-- cMT = 2s/(1+s) — the Montgomery–Taylor constant in the s-parameterisation. -/
theorem cMT_eq : cMT = 2 * sval / (1 + sval) := by
  have hu : (1 : ℝ) / Real.sqrt 2 = u := rfl
  unfold cMT sval
  rw [hu, sqrt2_eq_two_mul_u]
  ring

/-- Step (d), difference form: 2s/(1+s) − 400/531 = (662s − 400)/(531(1+s)) ≥ 0. -/
theorem cMT_diff_nonneg : 0 ≤ 2 * sval / (1 + sval) - (400 : ℝ) / 531 := by
  have hnum : 0 ≤ 662 * sval - 400 := by linarith [s_ge]
  have hden : (0 : ℝ) < 531 * (1 + sval) :=
    mul_pos (by norm_num) one_add_sval_pos
  have h1s_ne : 1 + sval ≠ 0 := one_add_sval_ne
  have heq : 2 * sval / (1 + sval) - (400 : ℝ) / 531
      = (662 * sval - 400) / (531 * (1 + sval)) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg hnum (le_of_lt hden)

/-- Step (d): cMT ≥ 400/531. -/
theorem cMT_ge : cMT ≥ (400 : ℝ) / 531 := by
  rw [cMT_eq]
  linarith [cMT_diff_nonneg]

theorem cMT_pos : 0 < cMT := by
  have h : (0 : ℝ) < (400 : ℝ) / 531 := by norm_num
  linarith [cMT_ge]

/-! ## The identity linking the page form to zeta23's Theorem-D form -/

/-- u·cot u = 1/(2s) — the one place u² = 1/2 enters. -/
theorem u_cot_eq : u * Real.cot u = 1 / (2 * sval) := by
  have hu0 : u ≠ 0 := u_ne
  have hsin_ne : Real.sin u ≠ 0 := ne_of_gt sin_pos
  have hcos_ne : Real.cos u ≠ 0 := ne_of_gt cos_pos
  rw [Real.cot_eq_cos_div_sin, sval_eq]
  field_simp
  nlinarith [u_sq]

/-- Step (f): the page's H equals zeta23's 2 − 1/cMT. -/
theorem H_eq : (3 : ℝ) / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) = 2 - 1 / cMT := by
  have hu : (1 : ℝ) / Real.sqrt 2 = u := rfl
  have h2s_ne : (2 : ℝ) * sval ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 sval_ne
  have hsval_ne : sval ≠ 0 := sval_ne
  have h1s_ne : 1 + sval ≠ 0 := one_add_sval_ne
  rw [hu, u_cot_eq, cMT_eq]
  field_simp
  ring

/-- Step (e): 2 − 1/cMT ≥ 269/400, from cMT ≥ 400/531. -/
theorem H_cMT_ge : 2 - 1 / cMT ≥ (269 : ℝ) / 400 := by
  have hinv : 1 / cMT ≤ 531 / 400 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (400 : ℝ) / 531) cMT_ge
    have he : (1 : ℝ) / ((400 : ℝ) / 531) = 531 / 400 := by norm_num
    linarith [h, he]
  linarith

/-- **The page bound**: H = 3/2 − (1/√2)·cot(1/√2) ≥ 269/400. -/
theorem h_ge_269_400 :
    (3 : ℝ) / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) ≥ (269 : ℝ) / 400 := by
  rw [H_eq]
  exact H_cMT_ge

#print axioms u_sq
#print axioms sqrt2_eq_two_mul_u
#print axioms sin_pos
#print axioms cos_pos
#print axioms margin
#print axioms margin_exact
#print axioms key_ineq
#print axioms s_ge
#print axioms cMT_eq
#print axioms cMT_ge
#print axioms u_cot_eq
#print axioms H_eq
#print axioms H_cMT_ge
#print axioms h_ge_269_400

/-- The two sorry goal states, folded and unfolded, for the mind that fills them. -/
example : |Real.sin u / u - A_part| ≤ A_err := plug_A
example : |Real.cos u - B_part| ≤ B_err := plug_B
example : |Real.sin (1 / Real.sqrt 2) / (1 / Real.sqrt 2) - 37043 / 40320| ≤ 1 / 5806080 :=
  plug_A
example : |Real.cos (1 / Real.sqrt 2) - 4379 / 5760| ≤ 1 / 645120 := plug_B

end H269
