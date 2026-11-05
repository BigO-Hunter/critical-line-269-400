# NUMBERS.md — H >= 269/400 reduction anchor (P0, 60-digit + exact)

u = 1/sqrt(2)      = 0.7071067811865475244008443621048490392848
tan(u)             = 0.8545104320096018925194130189031707024404
cMT (zeta23 form)  = 0.7532960678560706772165846282697276822957
H1 = 2 - 1/cMT     = 0.6725007036794116457343797908032951885934
H2 = 3/2 - u*cot u = 0.6725007036794116457343797908032951885934
|H1 - H2|          = 2.3336e-61   (identity check; expect < 1e-55)
269/400            = 0.6725
H1 - 269/400       = 7.036794116e-7   (must be > 0)

## Equivalence chain (each step iff, all positive quantities)
H >= 269/400  <=>  1/cMT <= 531/400  <=>  cMT >= 400/531 = 0.75329566854990583804143126177
   cMT - 400/531 = 3.993061648e-7
cMT = 2s/(1+s), s = u*tan(u) = 0.604230121068635760976997386112;  cMT >= 400/531 <=> s >= 200/331 = 0.604229607250755287009063444109
   s - 200/331 = 5.138178805e-7
   cross-check cMT from s: 2s/(1+s) = 0.75329606785607067721658462827 vs cMT (must match)

## Rational-series form (u^2 = 1/2 exact)
sin(u) = u*A, A = sum_k (-1)^k (1/2)^k/(2k+1)!   (rational alternating)
cos(u) = B,     B = sum_k (-1)^k (1/2)^k/(2k)!   (rational alternating)
A = sin(u)/u = 0.9187253698655684377842315251246617518102
B = cos(u)   = 0.7602445970756301512535471986232743946176
s = A/(2B) check: 0.604230121068635760976997386112 vs s above
TARGET INEQUALITY: 331*A >= 400*B
   331*A = 304.0980974255031529065806348162630398492
   400*B = 304.097838830252060501418879449309757847
   331*A - 400*B = 0.0002585952511   (must be > 0; margin ~2.5e-4 expected)

### N=4 terms each: 331*(A_part-A_err) - 400*(B_part+B_err) = 1.414035e-04  (PASS >0)
A_part = 37043/40320 (= 0.918725198412698), A_err = 1/5806080 (= 1.722e-07)
B_part = 4379/5760 (= 0.760243055555556), B_err = 1/645120 (= 1.550e-06)
exact margin numerator/denominator: 821 / 5806080

## What the Lean proof needs (integration target)
1. Analytic plugs (2): |A - A_part| <= A_err and |B - B_part| <= B_err, via alternating-series
   bound or Taylor-Lagrange; terms are exact rationals (u^2 = 1/2), N as chosen above.
2. Algebraic identity: H2 = 3/2 - u*cot(u) equals 2 - 1/cMT with cMT = sqrt2*tan(u)/(1+u*tan(u))
   (field algebra, positivity of denominators; also cot = cos/sin, tan = sin/cos).
3. Chain: 331*A >= 400*B => s >= 200/331 => cMT >= 400/531 => H >= 269/400 (each step monotone,
   positives; cMT = 2s/(1+s) increasing in s on s > -1).
4. Bridge to zeta23: Theorem D cumulative (kappa* >= H in eps-form) + H >= 269/400 gives
   Race.bound (269/400) in the #146 adapter's eps-form (eps-bookkeeping, trivial).
5. NOTE: zeta23 states H via 2 - 1/cMT; the page states 3/2 - u*cot(u); identity in step 2
   must be formal, numeric agreement verified here to 60 digits.
