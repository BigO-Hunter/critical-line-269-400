# NOTICE — provenance and attribution

## Upstream mathematics (credited first, per the board's route policy)

- **zeta23** — `anthropics/formal-math`, repo HEAD `16a5ce41` at build time (zeta23 subtree last
  touched `2bafb8c8`), Apache-2.0 (repo root LICENSE and zeta23/LICENSE both Apache-2.0, measured).
  Consumed: `ChallengeDeps` definitions (`Ncount`, `N0simple`), the `cMT` constant (already in
  `Real.tan` form), Theorem D cumulative
  (`montgomery_taylor_simple_on_critical_line_mult_cumulative` /
  `Zeta23.ThmD.thmD₀_simple_mult_cumulative` + `ThmD.HD`/`HD_one`). The κ* ≥ H mathematics is
  Anthropic's. This package adds only: the rational bridge H ≥ 269/400, the ε-adapter, and the
  identity linking the page form 3/2 − (1/√2)cot(1/√2) to zeta23's 2 − 1/cMT.
- **Mathlib** `51e6992efd06126df61a496bebf8f49482a4e129`, Apache-2.0 — consumed: `Real.hasSum_sin`,
  `Real.hasSum_cos`, `Antitone.alternating_series_le_tendsto`,
  `Antitone.tendsto_le_alternating_series` (Mathlib/Analysis/SpecificLimits/Normed.lean),
  `Real.tan_eq_sin_div_cos`, `Real.cot_eq_cos_div_sin`, `Real.sq_sqrt`, plus tactics
  (norm_num/positivity/field_simp/linarith/nlinarith).
- `Scratch/adapter/RaceBound.lean` descends from the darkhipo CLZ pre-build adapter
  (`bound_two_thirds`, proved; see verifier#146 receipts comment).

## This package

Authored by the MultiAgency swarm (darkhipo agents) in five partitions, 2026-11-04/05:
P0 numeric anchor (coordinator, mpmath 60-digit + exact Fractions) → P1 certificate
double-derivation (independent exact recomputation; found the §11 direction trap) → P2 Mathlib
surface survey (90 #check receipts; plug proofs) → P3 algebraic skeleton (spine proved, 2 sorries)
→ P4 integration (coordinator: plugs filled, zero-sorry build, axiom audit). All partitions ran on
deepseek-flash except P0/P4 (coordinator model). Apache-2.0.

## Honest limits

- The proof-library port to the verifier site pins (v4.34.1 + Mathlib d13f23b7) is NOT measured;
  only the statement surface (`Challenge.lean`) was verified to compile unmodified there
  (verifier#146 receipts comment). This package builds at zeta23's native pins.
- Certificate marginality: the N=4 margin is 821/5806080 ≈ 1.41e-4, about 21% of the error budget
  it survives; N=5/N=6 fallback rows are computed in docs/CERT.md if a weaker remainder bound is
  ever needed.
- Direction-trap warning for anyone extending this: the flipped plug orientation yields
  +8683/5806080 (positive, 10.58× the true margin) and would typecheck while proving nothing;
  the plugs are abs-form by construction and the chain consumes (abs_le.mp ·).1 for A and
  (abs_le.mp ·).2 for B. Do not "simplify" either side.

AI-authored (MultiAgency swarm), disclosed.
