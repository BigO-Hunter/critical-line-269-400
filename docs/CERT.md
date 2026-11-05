# P1 CERTIFICATE — H ≥ 269/400 via the rational-series inequality 331·A ≥ 400·B

**Partition:** P1 (certificate double-derivation)
**Method:** full independent re-derivation. Every rational quantity is an exact
`fractions.Fraction`; transcendentals are `mpmath` at 60 decimal digits.
Nothing was copied from `p0_anchor.py` except the *claims being tested*.
**Artifacts:** this file, `CERT.json` (machine-readable), `p1_exact.py` (generator).

## 0. Status summary

| Claim from P0 | Verdict |
|---|---|
| `A_part(N=4) = 37043/40320`, `A_err = 1/5806080` | **CONFIRMED** exactly |
| `B_part(N=4) = 4379/5760`, `B_err = 1/645120` | **CONFIRMED** exactly |
| N=4 margin `= 821/5806080` | **CONFIRMED** exactly (two independent integer paths) |
| `2 − 531/400 = 269/400` (chain tight at boundary) | **CONFIRMED** exactly |
| `s = A/(2B) = u·tan u`; `cMT = 2s/(1+s)` | **CONFIRMED** exactly (u² = 1/2) |
| `H1 − 269/400 = 7.036794116e-7 > 0` | **CONFIRMED** (recomputed `7.03679411646e-7`) |
| `cMT − 400/531 = 3.993061648e-7` | **CONFIRMED** (`3.99306164839e-7`) |
| `s − 200/331 = 5.138178805e-7` | **CONFIRMED** (`5.13817880474e-7`) |
| `331A − 400B = 2.585952511e-4` | **CONFIRMED** (`2.58595251092e-4`) |
| `|H1 − H2| < 1e-55` | **EXCEEDED** — the identity is *exact algebra* (see §8); the 2.33e-61 residual is pure mpmath rounding |

No mismatches found. One strengthening: §8 upgrades P0's 60-digit numeric check of
`H1 = H2` to a formal field identity that holds exactly, requiring only `u² = ½`.

## 1. Setting

Let `u = 1/√2`, so `u² = 1/2` **exactly** (this single fact is what makes every
series coefficient rational and the whole certificate machine-checkable).

```
sin(u) = u·A,   A = Σ_{k≥0} (−1)^k (1/2)^k / (2k+1)!
cos(u) =   B,   B = Σ_{k≥0} (−1)^k (1/2)^k / (2k)!
s     =  A/(2B)
cMT   =  2s/(1+s)
H1    =  2 − 1/cMT          (zeta23 Theorem-D form)
H2    =  3/2 − u·cot(u)     (page form)
TARGET:  H ≥ 269/400
```

Terms (all exact rationals):

```
t^A_k = (−1)^k / (2^k · (2k+1)!)
t^B_k = (−1)^k / (2^k · (2k)!)
```

## 2. Decrease lemma — PROVED EXACTLY (no proof obligation left for Lean)

Both series satisfy the alternating-series hypotheses:

1. **Alternating:** sign `t_k = (−1)^k` by construction.
2. **Strictly decreasing in absolute value, all k ≥ 0.** The exact ratios are

```
A:  |t^A_{k+1}| / |t^A_k| = 1 / ( 2·(2k+2)·(2k+3) )     ≤ 1/12   (k = 0)
B:  |t^B_{k+1}| / |t^B_k| = 1 / ( 2·(2k+1)·(2k+2) )     ≤ 1/4    (k = 0)
```

Both numerators are 1, and the denominators are `≥ 12` (A) and `≥ 4` (B) — so every ratio is
`< 1`. The ratios are also *decreasing in k*, so the supremum is the k = 0 value: `1/12` for A,
`1/4` for B. Verified exactly for k = 0…9 by `assert a_ratio == ratioA(k)`.
3. **Terms → 0.** Denominator grows super-exponentially; immediate from the ratio bound
   `|t_k| ≤ |t_0|·(1/12)^k` (resp. `(1/4)^k`).

Consequently the tail is bounded by the first omitted term, with the *sign* of the error
equal to the sign of that term:

```
| Σ_{k≥N} t^A_k | ≤ |t^A_N| = A_err(N)
| Σ_{k≥N} t^B_k | ≤ |t^B_N| = B_err(N)
A ∈ [A_part − A_err, A_part + A_err]
B ∈ [B_part − B_err, B_part + B_err]
```

## 3. THE TWO ANALYTIC PLUGS — the only real proof obligations for Lean

Everything else in this certificate is exact rational arithmetic. The Lean development
must discharge exactly **two** lemmas:

```
PLUG-A:   |A − A_part(N)| ≤ A_err(N)
PLUG-B:   |B − B_part(N)| ≤ B_err(N)
```

Both are the standard alternating-series (Leibniz) tail bound, whose hypotheses are
already established in §2 — in Lean this is one lemma applied twice, with the
decrease proof `1/(2(2k+2)(2k+3)) < 1` and `1/(2(2k+1)(2k+2)) < 1` discharged by
`norm_num` for each k, or by a single monotonicity argument on the ratio formula.

Exact plug data (all Fractions):

### N = 4  (RECOMMENDED — smallest certifying, cheapest proof)
```
A_part =  37043/40320        = 0.9187251984126984…
A_err  =  1/5806080          = 1.722332451499118e-07
B_part =  4379/5760          = 0.7602430555555556…
B_err  =  1/645120           = 1.550099206349206e-06
   A_lo =  5334191/5806080   = 0.9187250261794533…
   B_hi =  163483/215040     = 0.7602446056547619…
```
Terms, exact (k = 0,1,2,3):
```
A:  1,  −1/12,  1/480,  −1/40320                  (first omitted: +1/5806080)
B:  1,  −1/4,   1/96,   −1/5760                   (first omitted: +1/645120)
```

### N = 5
```
A_part =  5334193/5806080    = 0.9187253706459436…
A_err  =  1/1277337600       = 7.828783870450538e-10
B_part =  163483/215040      = 0.7602446056547619…
B_err  =  1/116121600        = 8.61166225749559e-09
   A_lo =  391174153/425779200
   B_hi =  88280821/116121600
```

### N = 6
```
A_part =  391174153/425779200          = 0.9187253698630652…
A_err  =  1/398529331200               = 2.509225599503377e-12
B_part =  88280819/116121600           = 0.7602445970430997…
B_err  =  1/30656102400                = 3.261993279354391e-11
   A_lo =  366139007207/398529331200
   B_hi =  3329448031/4379443200
```

Plug validation (not a proof; it only catches a *reversed* bound — see §11 for why that is
not sufficient): the *true* values were checked to lie inside the exact intervals, and the
residual slack was negative for all three N (e.g. N=4: `|A−A_part| − A_err = −7.80e-10`,
`|B−B_part| − B_err = −8.58e-09`).

## 4. Certificate data — exact margin

The certification inequality is

```
margin(N) := 331·(A_part − A_err) − 400·(B_part + B_err)  >  0
```

i.e. a *lower* bound on A against an *upper* bound on B — the rigorous direction.

| N | margin (exact) | ≈ | sliver over 269/400 |
|---|---|---|---|
| 1 | −2359/12 | −1.965833e+02 | fail |
| 2 | −691/480 | −1.439583e+00 | fail |
| 3 | −5567/40320 | −1.380704e-01 | fail |
| **4** | **821/5806080** | **1.414035e-04** | `821/2133676400` = 3.848e-07 |
| 5 | 321529/1277337600 | 2.517181e-04 | `321529/469408983600` = 6.850e-07 |
| 6 | 103057117/398529331200 | 2.585936e-04 | `103057117/146455602882800` = 7.037e-07 |
| 7 | 43284260849/167382319104000 | 2.585952e-04 | — |
| 8 | 941865776909/3642239263703040 | 2.585953e-04 | — |
| ∞ (true) | — | 2.58595251092e-04 | 7.03679411646e-07 |

N = 4 is the **smallest** N that certifies at all (N ≤ 3 fail), and it already clears the
1e-4 safety threshold by a factor 1.414. N = 6 is the best cost/accuracy point if the
Lean proof wants the widest margin (2.5859e-4, within 0.001 % of the true margin).

**N=4 margin by two independent paths** (guards against a `Fraction` bug):
1. `Fraction` arithmetic → `821/5806080`.
2. Hand integer arithmetic on the common denominator 5806080:
   `A_lo = (37043·144 − 1)/5806080 = 5334191/5806080`,
   `B_hi = (4379·112 + 1)/645120 = 490449/645120`, and `5806080/645120 = 9`, so
   `margin = (331·5334191 − 400·490449·9)/5806080 = (1765617221 − 1765616400)/5806080 = 821/5806080`. ✔

## 5. The chain — every step exact

### (a) 331·A ≥ 400·B  ⟺  s ≥ 200/331

`B > 0` is immediate from the exact lower bound `B ≥ B_part − B_err = 490447/645120 > 0`
(N=4; denominators and numerators are positive integers). Then dividing by `2B > 0`:

```
331·A ≥ 400·B  ⟺  A/B ≥ 400/331  ⟺  A/(2B) ≥ 200/331  ⟺  s ≥ 200/331.
```

Certified with `A_lo`, `B_hi`: `331·A_lo − 400·B_hi = margin ≥ 0` **is** the assertion
`s_lo = A_lo/(2·B_hi) ≥ 200/331` multiplied through by `2·B_hi > 0` (verified as an
equivalence, not two separate checks). For N=4: `s_lo = 5334191/8828082 = 0.6042298882… ≥ 0.6042296072… = 200/331`. ✔

### (b) s ≥ 200/331  ⇒  cMT = 2s/(1+s) ≥ 400/531

Exact algebra (this is the whole proof):

```
2s/(1+s) − 400/531 = (2s·531 − 400(1+s)) / (531(1+s))
                   = (1062s − 400 − 400s) / (531(1+s))
                   = (662s − 400) / (531(1+s))
                   = 662·(s − 200/331) / (531(1+s))        [because 662·200/331 = 400]
```

So the sign of `cMT − 400/531` equals the sign of `s − 200/331`, provided `531(1+s) > 0`.
`1 + s > 0` holds since `s ≥ 200/331 > 0`. Verified: `b_identity_residual = 0` exactly,
`b_one_plus_s_positive = True`, and `cMT_lo = 10668382/14162273 = 0.7532958868… ≥ 0.7532956685… = 400/531`. ✔

(Monotonicity note for Lean: `2s/(1+s)` is increasing on `s > −1` since
`d/ds = 2/(1+s)² > 0`; equivalently, the algebra above makes monotonicity unnecessary —
the sign identity is the sharper statement.)

### (c) cMT ≥ 400/531  ⇒  H1 = 2 − 1/cMT ≥ 269/400

Exact algebra:

```
H1 − 269/400 = (2 − 269/400) − 1/cMT = 531/400 − 1/cMT = (531·cMT − 400)/(400·cMT)
```

Sign equals sign of `cMT − 400/531` for `cMT > 0` (and `cMT ≥ 400/531 > 0`). Verified:
`c_identity_residual = 0` exactly. Certified bound for N=4:

```
H1_lo = 2 − 1/cMT_lo = 7174491/10668382 = 0.6725003847818722…
H1_lo − 269/400      = 821/2133676400   = 3.847818722651664e-07 > 0
```

### (d) H2 = 3/2 − u·cot(u) equals H1 — EXACTLY, not merely numerically

See §8.

## 6. Boundary tightness — CONFIRMED

```
2 − 531/400 = (800 − 531)/400 = 269/400   EXACTLY.
```

So the chain is *tight at the boundary*: `cMT = 400/531` gives `H1 = 269/400` with zero
slack. The strictness of the final result therefore comes **entirely** from the strictness
of the margin `821/5806080 > 0` — there is no hidden slack anywhere in the chain. This is
the ideal shape for a Lean proof: the only quantitative input is one positive rational.

## 7. Zero-slack remainder

Because of §6, the entire analytic content of the proof is:

```
331·(A_part − A_err) − 400·(B_part + B_err) > 0        [N = 4: 821/5806080 > 0]
```

Everything downstream is field algebra plus positivity of explicit rationals. A Lean
development can therefore close with `norm_num` on the single fact
`7174491/10668382 ≥ 269/400` once the two plugs are in hand.

## 8. H1 = H2 — exact field identity (strengthens P0)

P0 verified `|H1 − H2| = 2.3336e-61 < 1e-55` numerically. That residual is pure mpmath
rounding at 60 dps; the identity is **exact**, via `u² = 1/2` alone:

```
s      = u·tan u = u·(sin u / cos u) = u·(uA/B) = u²·A/B = (1/2)·A/B = A/(2B)
cMT    = 2s/(1+s)
1/cMT  = (1+s)/(2s)
H1     = 2 − (1+s)/(2s) = (4s − 1 − s)/(2s) = (3s − 1)/(2s) = 3/2 − 1/(2s)
1/(2s) = (1/(2u))·cot u            [since s = u·tan u ⇒ 1/s = cot(u)/u]
       = u·cot u                    [since 1/(2u) = u ⟺ 2u² = 1 ⟺ u = 1/√2]
H1     = 3/2 − u·cot u = H2.   ∎
```

The pivotal step `1/(2u) = u` is exactly `2u² = 1`, i.e. `u = 1/√2` — verified exactly on
rationals (`2·(1/2) == 1`). The symbolic form `2 − (1+s)/(2s) = (3s−1)/(2s)` was also
checked on an arbitrary rational stand-in (`s = 3/7`), so it is a genuine field identity,
not an artifact of the specific s.

**Consequence for the Lean side:** step 2 of P0's obligation list ("algebraic identity
H2 = ... with cMT = √2·tan u/(1+u·tan u)") is *already discharged* by this derivation —
it needs `u² = 1/2` plus `cot = cos/sin`, `tan = sin/cos`, and no case analysis.
Note also `√2·tan u = 2u·tan u` since `2u = √2`, so the two forms of cMT coincide.

## 9. Sanity gauntlet (all PASS at 40 significant digits)

| check | residual |
|---|---|
| `A_part(24 terms)` vs `sin(u)/u` | `0.0` (< 1e-39) |
| `B_part(24 terms)` vs `cos(u)` | `0.0` (< 1e-39) |
| `tan(u)` vs `u·A/B` | `0.0` (< 1e-39) |
| `s = A/(2B)` vs `u·tan u` | `7.78e-62` |
| `2s/(1+s)` vs `cMT` | `1.56e-61` |
| `√2·tan u/(1+u·tan u)` vs `2s/(1+s)` | `1.56e-61` |
| `2u` vs `√2` | `< 1e-39` |

Reference values at 60 dps (45 significant digits shown, verbatim from `CERT.json`):
```
u     = 0.707106781186547524400844362104849039284835938
tan u = 0.854510432009601892519413018903170702440424904
cMT   = 0.75329606785607067721658462826972768229573956
H1    = 0.672500703679411645734379790803295188593403029
H2    = 0.672500703679411645734379790803295188593403029
A     = 0.91872536986556843778423152512466175181017248
B     = 0.760244597075630151253547198623274394617583171
s     = 0.60423012106863576097699738611215165304192295
331A − 400B = 2.58595251092e-4
331A − 400B − margin(N=4) = 1.1719176e-4
```
The certificate's own decomposition (why it is positive at all):

```
331·A_part − 400·B_part = 11/13440      = 8.184524e-04    (untruncated partial-sum margin)
331·A_err  + 400·B_err  = 3931/5806080  = 6.770489e-04    (total error cost)
                     ─────────────────────────────────
331·(A_part−A_err) − 400·(B_part+B_err) = 821/5806080 = 1.414035e-04  ✔
```

Note `400·B_err = 6.20e-4` alone is **2.4× the true margin** `2.586e-4` — the errors are not
small relative to the target. The certificate survives only because the raw partial-sum
inequality `331·A_part ≥ 400·B_part` carries `8.18e-4` of slack, enough to absorb `6.77e-4` of
error cost. Had N=3 been used, the raw slack would have been negative.

Second decomposition — how much worse the certificate is than the truth (`δA = A − A_part`,
`δB = B − B_part`, both > 0 at N=4):

```
331A − 400B − margin = 331·(δA + A_err) − 400·(δB − B_err)
                     = 331·3.43686115e-7  − 400·(−8.5791e-9)
                     = 1.137600e-4        + 3.4316e-6        = 1.17192e-4  ✔
```

The loss is dominated by the A side (both `δA` and `A_err` count against us there); the B
side is nearly free because `δB` almost exactly cancels `B_err` (leaving `8.6e-9`). This is
luck of the sign, not something the proof relies on — the certificate is valid either way.

## 10. Proof-obligation ledger for the Lean integrator

| # | Obligation | Status |
|---|---|---|
| 1 | Decrease lemma for both series (exact ratio formulas, ratios < 1) | **DONE here** (§2); Lean restates as `norm_num` facts |
| 2 | PLUG-A: `|A − A_part| ≤ A_err` | **Lean must prove** (Leibniz bound + §2) |
| 3 | PLUG-B: `|B − B_part| ≤ B_err` | **Lean must prove** (Leibniz bound + §2) |
| 4 | `B > 0` | exact rational, `norm_num` |
| 5 | `331A ≥ 400B ⟺ s ≥ 200/331` (divide by `2B > 0`) | **DONE here** (§5a) |
| 6 | `cMT − 400/531 = 662(s − 200/331)/(531(1+s))`, `1+s > 0` | **DONE here** (§5b), exact identity |
| 7 | `H1 − 269/400 = (531·cMT − 400)/(400·cMT)`, `cMT > 0` | **DONE here** (§5c), exact identity |
| 8 | `2 − 531/400 = 269/400` (boundary tight) | **DONE here** (§6), exact |
| 9 | `H1 = 3/2 − u·cot u = H2` given `u² = 1/2` | **DONE here** (§8), exact field identity |
| 10 | Bridge to zeta23 Theorem D / `Race.bound (269/400)` | out of P1 scope |

Recommended integration point: **N = 4**, whose single quantitative fact is
`821/5806080 > 0`, and whose final Lean-target numerator is
`H1_lo = 7174491/10668382 ≥ 269/400` (sliver `821/2133676400`).

## 11. ⚠ TRAP for the Lean integrator — plug direction cannot be caught numerically

Comparisons of the two interval directions (exact Fractions):

| N | admissible `(A_lo, B_hi)` | INADMISSIBLE `(A_hi, B_lo)` | wrong/correct |
|---|---|---|---|
| 2 | −691/480 | **+3971/480** | — |
| 3 | −5567/40320 | **+139/8064** = +1.72e-2 | — |
| **4** | **+821/5806080** = 1.414e-4 | **+8683/5806080** = 1.496e-3 | **10.58×** |
| 5 | +321529/1277337600 | +330991/1277337600 | 1.029× |
| 6 | +103057117/398529331200 | +103068179/398529331200 | 1.0001× |

The inadmissible direction is **positive at every N ≥ 2**, including N = 3 where the
*admissible* direction is negative. Two consequences, and they are severe:

* A Lean proof that used `A ≥ A_part + A_err` (or `B ≤ B_part − B_err`) would **typecheck,
  its final `norm_num` would succeed, and the theorem would still be unproved.**
* At N = 3 a direction-flipped proof would *succeed where the correct proof fails* — the
  only visible symptom would be the wrong constant. Numeric positivity therefore cannot
  validate the proof at any N in this range; only the *structure* of the plug application can.

Positive controls for the Lean development: the appearing constant must be exactly
`821/5806080` (not `8683/5806080`), and the certified bound reaching `269/400` must be
exactly `H1_lo = 7174491/10668382` (not the N=5 or N=6 value). Both plugs must be stated with
an absolute value on the correct side, i.e. exactly `|A − A_part| ≤ A_err`, nothing weaker
and nothing reversed.

Why this trap exists: the errors are *not* small relative to the target (`400·B_err = 6.20e-4`
alone exceeds the true margin `2.586e-4`), yet the raw partial-sum slack `8.18e-4` absorbs the
combined error cost `6.77e-4` and still leaves `1.41e-4` positive. Both interval directions
therefore land on positive numbers — flinging the sign the wrong way is numerically invisible.
The certificate is genuinely marginal: the admissible margin is only 21 % of the error cost it
survives, so the direction is load-bearing, not hygiene.


## 12. Negative controls

`p1_negative_controls.py` demonstrates that every check above can fail and does reject
corrupted input: negative-margin rejection (N=3), the plug-direction trap (§11), the
non-vacuity of `531/400` (perturbing it to `531/401` or `530/400` breaks the identity), the
`662` coefficient in the sign identity (a `663` variant is rejected), the tightness of the
ratio bound (`ratio < 1/100` is false, so the decrease claim is not loose), and that
`H1_lo` is a strict lower bound on a truncated true `H1`.

---
*Generated by `/tmp/clz_lemma/p1-cert/p1_exact.py`; data in `CERT.json`.
All arithmetic exact except the explicitly labelled 60-digit mpmath cross-checks.*
