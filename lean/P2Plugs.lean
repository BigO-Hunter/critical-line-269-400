/-
P2 probe 6 — FEASIBILITY, complete: BOTH analytic plugs at N=4, plus the final
rational step `331*A >= 400*B` from NUMBERS.md.

  |sin u / u - 37043/40320| <= 1/5806080     (A_err)
  |cos u     - 4379/5760 | <= 1/645120      (B_err)
  331*(sin u / u) >= 400*cos u              (the target inequality)

with u = 1/sqrt 2. Built entirely from Mathlib's Leibniz partial-sum bounds.
-/
import Mathlib

open Finset

namespace P2Feas

noncomputable section

abbrev U : ℝ := 1 / Real.sqrt 2

theorem U_sq : U ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

theorem U_pos : 0 < U := by positivity

theorem U_pow : ∀ n : ℕ, U ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
  intro n
  rw [pow_mul, U_sq]

/-! ## The cos half (B) -/

def bterm (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (2 * n).factorial

theorem hasSum_cos_rational : HasSum (fun n => (-1) ^ n * bterm n) (Real.cos U) := by
  have h := Real.hasSum_cos U
  have hfun : (fun n => (-1) ^ n * U ^ (2 * n) / (2 * n).factorial)
            = (fun n => (-1) ^ n * bterm n) := by
    funext n
    simp only [bterm]
    rw [U_pow n, mul_div_assoc]
  rwa [hfun] at h

/-- Generic antitone helper: `q^(n+1)/(2(n+1))! <= q^n/(2n)!` for `0 <= q <= 1`. -/
theorem bterm_antitone : Antitone bterm := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hfac : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
  have hB : ((2 * (n + 1)).factorial : ℝ) = ((2 * n + 2) * (2 * n + 1)) * (2 * n).factorial := by
    rw [hfac, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsplit : ((1 / 2 : ℝ) ^ n / (2 * n).factorial) * (((2 * n + 2) * (2 * n + 1)) * (2 * n).factorial)
      = (1 / 2 : ℝ) ^ n * ((2 * n + 2) * (2 * n + 1)) := by
    field_simp
  simp only [bterm]
  rw [hB, div_le_iff₀ (by positivity), hsplit, pow_succ]
  have hp : (0:ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hge : (1 / 2 : ℝ) ≤ ((2 * n + 2) * (2 * n + 1) : ℝ) := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

theorem cos_lower : ∑ i ∈ range 4, (-1) ^ i * bterm i ≤ Real.cos U :=
  Antitone.alternating_series_le_tendsto hasSum_cos_rational.tendsto_sum_nat bterm_antitone 2

theorem cos_upper : Real.cos U ≤ ∑ i ∈ range 5, (-1) ^ i * bterm i :=
  Antitone.tendsto_le_alternating_series hasSum_cos_rational.tendsto_sum_nat bterm_antitone 2

theorem sum4 : ∑ i ∈ range 4, (-1) ^ i * bterm i = 4379 / 5760 := by
  simp [bterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem sum5 : ∑ i ∈ range 5, (-1) ^ i * bterm i = 4379 / 5760 + 1 / 645120 := by
  simp [bterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem cos_bound_N4 : |Real.cos U - 4379 / 5760| ≤ 1 / 645120 := by
  have h1 : 4379 / 5760 ≤ Real.cos U := by rw [← sum4]; exact cos_lower
  have h2 : Real.cos U ≤ 4379 / 5760 + 1 / 645120 := by rw [← sum5]; exact cos_upper
  rw [abs_le]
  constructor <;> linarith

/-! ## The sin half (A) — same sandwich, but divided through by u -/

def aterm (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (2 * n + 1).factorial

/-- The series for `sin u / u`, obtained from `Real.hasSum_sin` via `HasSum.div_const`
and `U^(2n+1)/U = U^(2n) = (1/2)^n`. -/
theorem hasSum_sin_rational : HasSum (fun n => (-1) ^ n * aterm n) (Real.sin U / U) := by
  have h := (Real.hasSum_sin U).div_const U
  have hfun : (fun n => (-1) ^ n * U ^ (2 * n + 1) / (2 * n + 1).factorial / U)
            = (fun n => (-1) ^ n * aterm n) := by
    funext n
    simp only [aterm]
    rw [pow_succ, U_pow n]
    field_simp
  rwa [hfun] at h

theorem aterm_antitone : Antitone aterm := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hfac : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  have hB : ((2 * (n + 1) + 1).factorial : ℝ) = ((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial := by
    rw [hfac, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsplit : ((1 / 2 : ℝ) ^ n / (2 * n + 1).factorial) * (((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial)
      = (1 / 2 : ℝ) ^ n * ((2 * n + 3) * (2 * n + 2)) := by
    field_simp
  simp only [aterm]
  rw [hB, div_le_iff₀ (by positivity), hsplit, pow_succ]
  have hp : (0:ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hge : (1 / 2 : ℝ) ≤ ((2 * n + 3) * (2 * n + 2) : ℝ) := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

theorem sin_lower : ∑ i ∈ range 4, (-1) ^ i * aterm i ≤ Real.sin U / U :=
  Antitone.alternating_series_le_tendsto hasSum_sin_rational.tendsto_sum_nat aterm_antitone 2

theorem sin_upper : Real.sin U / U ≤ ∑ i ∈ range 5, (-1) ^ i * aterm i :=
  Antitone.tendsto_le_alternating_series hasSum_sin_rational.tendsto_sum_nat aterm_antitone 2

theorem asum4 : ∑ i ∈ range 4, (-1) ^ i * aterm i = 37043 / 40320 := by
  simp [aterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem asum5 : ∑ i ∈ range 5, (-1) ^ i * aterm i = 37043 / 40320 + 1 / 5806080 := by
  simp [aterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem A_bound_N4 : |Real.sin U / U - 37043 / 40320| ≤ 1 / 5806080 := by
  have h1 : 37043 / 40320 ≤ Real.sin U / U := by rw [← asum4]; exact sin_lower
  have h2 : Real.sin U / U ≤ 37043 / 40320 + 1 / 5806080 := by rw [← asum5]; exact sin_upper
  rw [abs_le]
  constructor <;> linarith

/-! ## THE TARGET INEQUALITY from the two plugs — NUMBERS.md's rational margin -/

/-- **331 * (sin u / u) >= 400 * cos u**, i.e. `s = A/(2B) >= 200/331`.
This is NUMBERS.md's step `331*A >= 400*B`, and it is where the whole reduction lives:
the exact rational margin is 821/5806080 > 0. -/
theorem target_331_A_ge_400_B : 400 * Real.cos U ≤ 331 * (Real.sin U / U) := by
  have hA : 37043 / 40320 - 1 / 5806080 ≤ Real.sin U / U := by
    linarith [(abs_le.1 A_bound_N4).1]
  have hB : Real.cos U ≤ 4379 / 5760 + 1 / 645120 := by
    linarith [(abs_le.1 cos_bound_N4).2]
  have hA' : (331 : ℝ) * (37043 / 40320 - 1 / 5806080) ≤ 331 * (Real.sin U / U) := by
    linarith
  have hB' : 400 * Real.cos U ≤ 400 * (4379 / 5760 + 1 / 645120) := by linarith
  nlinarith [hA', hB']

end
end P2Feas

/-! ## Receipts: verbatim statements + axiom audit of the three proved targets -/

#check @P2Feas.A_bound_N4
#check @P2Feas.cos_bound_N4
#check @P2Feas.target_331_A_ge_400_B
#print axioms P2Feas.A_bound_N4
#print axioms P2Feas.cos_bound_N4
#print axioms P2Feas.target_331_A_ge_400_B
