# critical-line-269-400 — a Lean proof that H ≥ 269/400 for the critical-line-zeros board

**Status: READY-FOR-ROUTE.** The bigospeedrun `critical-line-zeros` route is not open yet; the
maintainer is building it themselves (verifier#146: statement from the zeta23 Challenge surface,
Anthropic's proof rerun first, that row credited to Anthropic). **Nothing here is a submission.**
When the route opens, this repo's row target gets scoped against the maintainer's first row (the
tie rule: a rerun at the same value as an existing row starts no run), and only then filed.

## What is proved

The board scores κ* = liminf N₀ˢ(T)/N(T) (simple zeros on the critical line over zeros with
multiplicity, 0 < Im ≤ T, unconditional; **higher is better**). The board's Anthropic-breakthrough
row is the constant

    H = 3/2 − (1/√2)·cot(1/√2) = 2 − 1/cMT ≈ 0.6725007036794116457…

This repo proves, in Lean (Mathlib, zeta23's native pins):

1. `H269.h_ge_269_400 : 3/2 − (1/√2)·cot(1/√2) ≥ 269/400` — the page constant bounded below by
   the exact rational **269/400 = 0.6725** (margin 7.04e-7; the certificate is genuinely marginal
   by design — see docs/NUMBERS.md).
2. `Race.bound_269_400` and `Race.bound_269_400_zeta23` — the board-row form
   `Race.bound (269/400 : ℚ)` (ε-form: ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (269/400 − ε)·N(T) ≤ N₀ˢ(T)),
   bridged from zeta23's Theorem D cumulative (`montgomery_taylor_simple_on_critical_line_mult_cumulative`),
   in two sourcings (comparator `Solution` layer; pure `Zeta23` library).

Axiom audit (receipts/build-final.log): every theorem above depends on exactly
`[propext, Classical.choice, Quot.sound]` — zero `sorryAx`, zero custom axioms.

## How (the reduction)

u = 1/√2 makes u² = 1/2 exact, so sin(u) = u·A and cos(u) = B with **A, B pure rational
alternating series** ((1/2)^k/(2k+1)! and (1/2)^k/(2k)!). The chain (docs/NUMBERS.md, all steps
exact):

    331·A ≥ 400·B  ⟹  s = u·tan u ≥ 200/331  ⟹  cMT = 2s/(1+s) ≥ 400/531  ⟹  H = 2 − 1/cMT ≥ 269/400

with the boundary exact (2 − 531/400 = 269/400). The two analytic facts are N=4 alternating-series
truncations via Mathlib's Leibniz bounds (`Antitone.alternating_series_le_tendsto` /
`Antitone.tendsto_le_alternating_series`): |sin u/u − 37043/40320| ≤ 1/5806080 and
|cos u − 4379/5760| ≤ 1/645120; exact margin 331·(A₄−e_A) − 400·(B₄+e_B) = **821/5806080 > 0**.
Everything else is field algebra + norm_num. The plugs are stated in ABS form — deliberately: a
one-sided mis-orientation would typecheck while proving nothing (docs/CERT.md §11 direction trap;
the flipped direction yields +8683/5806080, 10.58× the true margin).

## Credits (per the board's route policy: construction/theorems first, package second)

- **zeta23** — `anthropics/formal-math` @ `16a5ce41` (zeta23 tree last touched `2bafb8c8`),
  Apache-2.0: the Challenge surface (17 statements + 15 definitions), Theorem D cumulative, and
  the cMT constant. **The κ* ≥ H mathematics is Anthropic's; this repo adds only the rational
  bridge H ≥ 269/400 and the board adapter.** Any row filed from this work names zeta23's authors
  first.
- Board context: bigospeedrun `critical-line-zeros` (κ* rows; H row Claimed via zeta23; verifier#146).
- This package: MultiAgency swarm (darkhipo agents), partition build P0–P4 (numeric anchor,
  certificate double-derivation, Mathlib surface survey, algebraic skeleton, integration).

## Build

Native pins (zeta23's own): Lean **v4.33.0-rc2** / Mathlib **51e6992efd06126df61a496bebf8f49482a4e129**.
See BUILD.md — the lean/ directory is a `Scratch/` layer dropped into a zeta23 checkout; one
`lake build Scratch.Bridge269`. The statement surface also compiles unmodified at the verifier site
pins v4.34.1 + d13f23b7 (proof-library port at site pins: unmeasured, disclosed).

— AI-authored (MultiAgency swarm), disclosed.
