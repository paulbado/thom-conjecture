# Numerical evidence on the principal target

**Status: heuristic evidence, not a proof.** Nothing here is used in the Lean development.

Target: `∑_{n≥1} c_n² < ∞` with `c_n = τ(T_n(A/4))` (Lean: `ThomBridge.PrincipalTarget`).

## Method

* `moments.py N` — exact integer counts `m_n = τ(Aⁿ)` (closed zero-area walks) by dynamic
  programming over `(x, y, area)`; output for `n ≤ 120` in `moments_exact_n120.txt`.
  It reproduces `m_6 = 232` (Lean: `moment_six`, kernel-checked).
* `cheb.py` — exact rational `c_n = ∑_k [Xᵏ]T_n · 4⁻ᵏ m_k` from the exact moments.
* `vec.py M` — floating-point `c_n` for `n ≤ 2M` from the stable recursion
  `v_{m+1} = (A/2)v_m − v_{m−1}` on `ℓ²(H₃)`, using `c_{2m} = 2‖v_m‖² − 1` and
  `c_{2m+1} = 2⟨v_m, v_{m+1}⟩`. It agrees with the exact values for `n ≤ 120` to about 1e-12.
  Output for `n ≤ 170` is in `cheb_coeffs_n170.txt`.

Odd coefficients vanish (bipartite Cayley graph).

## Results

| n | c_n | ∑_{k ≤ n} c_k² |
|---|-----|----------------|
| 10 | -0.20703 | 0.35689 |
| 20 | +0.02314 | 0.37458 |
| 30 | -0.00642 | 0.40604 |
| 40 | +0.02060 | 0.43226 |
| 50 | -0.01128 | 0.43685 |
| 60 | +0.04520 | 0.44009 |
| 70 | -0.04236 | 0.45439 |
| 80 | +0.00127 | 0.46074 |
| 90 | -0.03187 | 0.46377 |
| 100 | +0.05973 | 0.46937 |
| 110 | -0.06143 | 0.47689 |
| 120 | +0.02529 | 0.48180 |
| 130 | -0.00807 | 0.48318 |
| 140 | +0.02151 | 0.49138 |
| 150 | -0.01512 | 0.49886 |
| 160 | +0.03742 | 0.50158 |
| 170 | -0.05059 | 0.50551 |
* The average of `n·c_n²` over even `n` in windows `[20,50)`, `[50,80)`, `[80,110)`, `[110,140)`,
  `[140,170)` is about `0.13, 0.11, 0.08, 0.15, 0.12`. It shows no decay.
* Least-squares fit on `40 ≤ n ≤ 170`: the partial sums grow like `0.054 · log n`.
* The Abel means `1 + 2∑ c_n rⁿ cos(nθ)` (the smoothed density with respect to arcsine)
  peak at `E = 0`. The peak is 2.53 at `r = 0.95` and 3.66 at `r = 0.98`, and it keeps growing as `r → 1`.

## Reading

Up to `n = 170` the data are **consistent with `c_n² ≍ 1/n`, which would make `∑ c_n²`
diverge logarithmically**. The growth seems to come from a concentration of `μ_A` at
`E = 0`. If so, `μ_A` would have **no** `L²(arcsine)` density. By the Lean theorem
`principalTarget_iff_L2`, the principal target would then be false. That would still not
rule out absolute continuity, a local `L^p` density with `1 < p < 2`, or a local `L²` density
away from `E = 0`. 170 coefficients cannot settle a logarithmic question, so this needs
confirmation by larger computations or by analysis.

## Round 3: weighted energies, atom at zero, local singularities (n ≤ 256)

**Status: heuristic evidence, not a proof. Finite computations cannot decide convergence.**

New data: `cheb_coeffs_n256.txt` (`vec32.py 128`, float32 storage with float64 accumulation;
it agrees with the float64 run to `2.4e-8` for `n ≤ 200`). Scripts: `common.py` (loader,
`d_n`, Jackson kernel), `blocks.py`, `peaks.py`, `lpnorm.py`, `christoffel.py`.
Here `d_n = (c_{n-2} + 2c_n + c_{n+2})/4` are the Chebyshev coefficients of `ν = (E²/16)μ_A`
(Lean: `ThomChebyshev.chebCoeff_weighted`).

### Dyadic blocks (`python3 blocks.py cheb_coeffs_n256.txt`)

| j | block | sum c_n^2 | sum d_n^2 | D_j/D_{j-1} |
|---|---|---|---|---|
| 2 | [4,8) | 0.01953 | 3.232e-02 |  |
| 3 | [8,16) | 0.09006 | 9.653e-03 | 0.299 |
| 4 | [16,32) | 0.04645 | 4.355e-03 | 0.451 |
| 5 | [32,64) | 0.03982 | 1.859e-03 | 0.427 |
| 6 | [64,128) | 0.03704 | 5.887e-04 | 0.317 |
| 7 | [128,255) (partial) | 0.04346 | 1.318e-03 | 2.238 |

* The original block energies `∑_{B_j} c_n²` stay near `0.04` per octave (log divergence of `∑ c_n²`).
* The weighted block energies decrease up to `[64,128)` and then **increase**: the block
  `[128,255)` has `∑ d_n² = 1.32e-3`, more than twice the previous block. The individual `|d_n|`
  stay around `3e-3 – 9e-3` for `60 ≤ n ≤ 254` with no visible decay. The partial sums
  `0.0443, 0.0486, 0.0493, 0.0497, 0.0503` (n = 20, 40, 80, 120, 168) look convergent, but
  the block view shows that they are not evidence of convergence. If `|d_n|` does not decay,
  `∑ d_n²` diverges and the weighted target is false.

### Atom at zero

* Cesàro atom means `A_N = (N+1)⁻¹ ∑_{j≤N} (−1)^j c_{2j}` (Lean: `tendsto_atomMean`, so
  `A_N → μ_A{0}` exactly): `0.171, 0.115, 0.074, 0.059, 0.051, 0.045, 0.040, 0.039` for
  `n = 2N = 20, …, 254`. They decrease roughly like `N^{-1/2}`.
* `N⁻¹ ∑_{n<N} c_n²` decreases like `1.5/N` (Lean: `atom_eq_zero_of_energy` turns
  `→ 0` into `μ_A{0} = 0`).
* Christoffel bounds `λ_n(0) = min_{p(0)=1} ∫ p² dμ_A` (Lean: `atom_le_tau` gives `μ_A{0} ≤ λ_n(0)`
  once the moments are exact): `0.215 (n=8), 0.096 (32), 0.054 (98), 0.047 (126)`, again
  `≈ n^{-1/2}`. This is what a Lebesgue density `≈ |E|^{-1/2}` near `0` would give.

### Where the singular behaviour sits (`python3 peaks.py cheb_coeffs_n256.txt`)

Local maxima of the Jackson-smoothed density of `μ_A` (relative to arcsine), at degrees 63, 126, 252:

| E | f_63 | f_126 | f_252 |
|---|---|---|---|
| 0.000 | 2.992 | 3.994 | 5.549 |
| 0.718 | 1.612 | 1.874 | 2.226 |
| 1.104 | 1.218 | 1.221 | 1.353 |
| 1.694 | 1.343 | 1.269 | 1.325 |
| 1.949 | 1.620 | 1.845 | 2.202 |
| 2.151 | 1.622 | 1.458 | 1.494 |
| 2.572 | 2.541 | 3.004 | 3.369 |

Besides `E = 0`, the smoothed density grows with the degree near `E ≈ ±0.72`, `±1.95` and
`±2.57`. The first two are close to the band edges `±(√3 − 1) ≈ ±0.732` and `±2` of the
flux-`1/3` Harper operator (Chambers polynomial `E³ − 6E`). The weight `E²` does not vanish
there, which explains why the weighted energies do not decay. This points to an obstruction
that is not located at `E = 0`.

### `L^p` norms of smoothed densities (`python3 lpnorm.py cheb_coeffs_n256.txt`)

| N | μ: p=1.25 | 1.5 | 1.75 | 2 | entropy | ν/ν(ℝ): p=1.5 | 2 |
|---|---|---|---|---|---|---|---|
| 24 | 1.0823 | 1.1491 | 1.2042 | 1.2505 | 0.3668 | 1.2156 | 1.3916 |
| 48 | 1.0944 | 1.1724 | 1.2382 | 1.2947 | 0.4179 | 1.2681 | 1.4961 |
| 96 | 1.1025 | 1.1895 | 1.2651 | 1.3324 | 0.4484 | 1.2954 | 1.5579 |
| 192 | 1.1082 | 1.2024 | 1.2867 | 1.3639 | 0.4683 | 1.3083 | 1.5894 |
| 252 | 1.1100 | 1.2066 | 1.2940 | 1.3751 | 0.4743 | 1.3112 | 1.5965 |

For `p ≤ 1.75` the increments per doubling of the degree shrink by a factor of about 0.7–0.8,
compatible with bounded `L^p(arcsine)` norms. For `p = 2` the norm keeps growing (log).
The `L²` norm of the smoothed `ν`-density grows slowly; the Jackson kernel damps the top
coefficients, so this column does not contradict the block table.
This supports the `L^q` duality target with `q > 2`, i.e. an `L^p` density with `p < 2`
(Lean: `ThomConclusions.LqTarget`, `muA_ac_of_LqTarget`).

## Round 4: exact flux averages and the singularity at `E = 0`

### Method (`flux_average.py`)

The centre of `H₃(ℤ)` gives `μ_A = ∫_0^1 N_α dα`, where `N_α` is the density of states of
Harper's operator `(Hψ)_j = ψ_{j+1} + ψ_{j-1} + 2cos(2π(αj+θ))ψ_j` (averaged over `θ`). The
measures `ν_Q = Q⁻¹ ∑_{p<Q} N_{p/Q}` have moments `τ(Aⁿ)` for `n < N_Q` (Lean:
`ThomHeisenberg.avg_fluxTrace_opA_pow` and `ThomLean/Heisenberg/Threshold.lean`). For `α = p/q`
reduced, Chambers' relation `D(E) = 2cos k + 2cos(2πqθ)` makes `N_{p/q}` explicit: on the band
`j` the distribution function increases by `G(D(E))` or `1 − G(D(E))`, where `G` is the
distribution function of `2cos φ₁ + 2cos φ₂`. Band edges are eigenvalues of two `q × q` Bloch
matrices. This gives the distribution function of `ν_Q` **exactly** (up to floating point and
the tabulation of `G`), with no smoothing and no truncation of moments.

Check (`Q = 12, 40`): `∫ Eⁿ dν_Q` agrees with the exact walk counts `τ(Aⁿ)` to `≤ 1e-5`
relative error (the binning error of the check) for all `n ≤ N_Q`. The Chebyshev coefficients
of `ν_293` agree with `cheb_coeffs_n256.txt` to `1e-6` for `n ≤ 68`.

### Fejér norms (`fejer_lp.py`, output `out_fejer_lp.txt`)

`F_N` (Lean: `ThomFejer.fejerA`) is positive (min `≈ 1.5/N`, Lean: `fejer_nonneg`), and
`∫ F_N^{3/2} dρ = 1.228, 1.266, 1.295, 1.309, 1.318` for `N = 32, 64, 128, 192, 256`,
`∫ F_N² dρ = 1.574, 1.687, 1.783, 1.835, 1.872`. Both still grow; on their own these numbers do
not decide anything.

### The mass at `E = 0` (`flux_local.py`, output `out_flux_local.txt`)

Average density `ν_Q([−h,h])/(2h)`, `h = 2^{-j}`:

| j | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|
| Q = 101 | 0.476 | 0.880 | 2.260 | 5.801 | 15.20 | 42.90 | 125.2 | 313.5 |
| Q = 199 | 0.450 | 0.938 | 2.212 | 5.209 | 15.18 | 41.46 | 113.2 | 358.6 |
| Q = 293 | 0.451 | 0.956 | 2.098 | 5.116 | 14.24 | 40.89 | 125.4 | 365.9 |

The three values of `Q` agree at every scale. For `Q = 293`,
`ν_Q([−h,h]) · log²(1/h) = 0.43, 0.52, 0.50, 0.48, 0.48, 0.47, 0.47, 0.44` for
`j = 4, 6, …, 18`: the mass behaves like `≈ 0.47 / log²(1/h)` over 15 octaves, while
`ν_Q([−h,h]) / h^{1/3}` turns upward after `j ≈ 9` (`0.097 → 0.179`).

**Mechanism** (`zero_level.py`, output `out_zero_level_q401.txt`). For `α = 1/2 + δ`, exactly
`2|δ|q` bands of `N_α` sit within `w(δ)` of `E = 0`, separated by a gap of order `1` from the
next band (the relativistic zero Landau level of the Dirac cone of the half-flux operator), and
`log w(δ) ≈ −0.30/|δ| + O(1)` (for example `w = 1.2e-6` at `|δ| = 0.021`, `w = 5.2e-3` at
`|δ| = 0.051`). Averaging over `α`, the fluxes with `w(δ) < h` contribute
`≈ ∫_{|δ| < 0.3/log(1/h)} 2|δ| dδ ≈ 0.18/log²(1/h)` to `μ_A([−h,h])`; other even-denominator
fluxes add to the constant.

**Consequences, if this persists as `Q → ∞` and `h → 0`** (it is stable in `Q` here, but
these are finite computations):

* the density of `μ_A` behaves like `1/(|E| log³(1/|E|))` at `0`: integrable, so compatible
  with absolute continuity and with `μ_A{0} = 0` (now a theorem, `ThomNoAtoms.muA_no_atoms`),
* but it is in **no** `L^p`, `p > 1`. By `ThomFejer.muA_le_of_lqTarget`, `LqTarget q` forces
  `μ_A([−h,h]) = O(h^{1/q})`, so `LqTarget q` fails for every `q < ∞`. Hence `FejerTarget p`
  fails for every `p > 1` (in particular the `L^{3/2}` target), and so does `PrincipalTarget`;
* the Chebyshev coefficients follow `c_n ≈ (−1)^{n/2} a_n` with `a_n` of size `1/log² n`
  (`c_100 = 0.060`, `c_200 = 0.006`, `c_250 = −0.020`), which explains the slow growth of
  `∑ c_n²`, and the Cesàro atom means decay only like `1/log`.

This corrects the round-3 reading: the growth of the smoothed density at `E = 0` is the main
singularity. Near `E ≈ ±0.72, ±1.95, ±2.57` the exact averages give bounded average densities
(`0.12 – 0.42` at every scale `h ≥ 2·10⁻³` for `Q = 101, 199, 293`), so the round-3 peaks there are smoothing
artifacts at band edges rather than singularities (finer scales need larger `Q`).

### The weight `E²` removes the singularity (`flux_analysis.py`, output `out_flux_dyadic.txt`)

Binned `∫ f_w² dρ` for the weighted density `f_w = (E²/16) dν_Q/dρ`, `2^k` bins:

| k | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| Q = 199 | 0.1598 | 0.1624 | 0.1657 | 0.1745 | 0.1930 |
| Q = 293 | 0.1603 | 0.1627 | 0.1647 | 0.1670 | 0.1808 |

Up to `k = 8` the values for the two `Q` agree and grow by about `0.002` per level; at finer
`k` the finite-`Q` gaps dominate and the values decrease with `Q`. The binned weighted
`L^{3/2}` norms behave the same way (`0.1880, 0.1893, 0.1902, 0.1916`). This is compatible with
the **weighted** `L^q` target (`ThomFejer.WeightedLqTarget`, `q ≥ 2`), which together with the
absence of atoms gives `μ_A ≪ Lebesgue` (`ThomFejer.muA_ac_of_weightedLqTarget`). It does not
prove it.

## Round 5: dyadic entropy, Fejér entropy, weighted energies, transfer audit

Scripts: `dyadic_entropy.py K Q…` (outputs `out_dyadic_entropy.txt` for `Q = 53…401`, and
`out_dyadic_entropy_large.txt` for `Q = 601`), `gauss_lower.py` (output `out_gauss_lower.txt`).
`λ = θ_*ν_Q`, `θ = arccos(E/4)/π`; cell masses at level 16 are exact differences of the exact
distribution function. Lean counterparts: `ThomDyadic.dyEnt`, `dyDisc`, `ThomChebyshev.fejEnt`.

| k | H_k Q=199 | H_k Q=293 | H_k Q=401 | H_k Q=601 | D_k Q=199 | D_k Q=293 | D_k Q=401 | D_k Q=601 | wL² Q=401 | wL² Q=601 |
|---|---|---|---|---|---|---|---|---|---|---|
| 4 | 0.42651 | 0.43016 | 0.42662 | 0.42897 | 0.0327 | 0.0262 | 0.0297 | 0.0288 | 0.1444 | 0.1453 |
| 5 | 0.44310 | 0.44343 | 0.44163 | 0.44353 | 0.0392 | 0.0399 | 0.0398 | 0.0382 | 0.1509 | 0.1518 |
| 6 | 0.46295 | 0.46364 | 0.46180 | 0.46289 | 0.0387 | 0.0345 | 0.0366 | 0.0349 | 0.1557 | 0.1563 |
| 7 | 0.48259 | 0.48112 | 0.48032 | 0.48056 | 0.0408 | 0.0307 | 0.0279 | 0.0253 | 0.1611 | 0.1614 |
| 8 | 0.50384 | 0.49702 | 0.49458 | 0.49344 | 0.0723 | 0.0470 | 0.0311 | 0.0284 | 0.1643 | 0.1634 |
| 9 | 0.54479 | 0.52321 | 0.51138 | 0.50820 | 0.1123 | 0.0788 | 0.0720 | 0.0411 | 0.1678 | 0.1667 |
| 10 | 0.61102 | 0.56927 | 0.55288 | 0.53103 | 0.1518 | 0.1046 | 0.0890 | 0.0730 | 0.1770 | 0.1707 |
| 11 | 0.69898 | 0.63011 | 0.60472 | 0.57347 | 0.1634 | 0.1446 | 0.1133 | 0.0950 | 0.1941 | 0.1820 |
| 12 | 0.79354 | 0.71408 | 0.67111 | 0.62883 | 0.2374 | 0.1829 | 0.1473 | 0.1237 | 0.2233 | 0.2029 |
| 13 | 0.93570 | 0.82143 | 0.75629 | 0.69991 | 0.3111 | 0.2495 | 0.2024 | 0.1573 | 0.2735 | 0.2363 |

| N | H_N Q=199 | H_N Q=293 | H_N Q=401 | H_N Q=601 | ∫F_N² Q=601 |
|---|---|---|---|---|---|
| 16 | 0.27363 | 0.27363 | 0.27363 | 0.27363 | 1.4505 |
| 32 | 0.34456 | 0.34455 | 0.34456 | 0.34456 | 1.5743 |
| 64 | 0.39732 | 0.39732 | 0.39732 | 0.39732 | 1.6865 |
| 128 | 0.43427 | 0.43415 | 0.43415 | 0.43414 | 1.7833 |
| 256 | 0.46085 | 0.46015 | 0.45998 | 0.45997 | 1.8719 |
| 512 | 0.48353 | 0.48046 | 0.47934 | 0.47871 | 1.9580 |
| 1024 | 0.51603 | 0.50262 | 0.49707 | 0.49399 | 2.0499 |

Values are converged in `Q` (to about `10⁻³`) up to level 8 for `Q = 601`; deeper levels and
`N = 1024` are still moving with `Q`. *(Corrected in round 6: these unconverged values are not
automatically upper bounds on the limit; they decrease with `Q` here, which is evidence only.)*

* **Dyadic entropy (N).** Converged increments `H_{k+1} − H_k`: `0.019, 0.018, 0.013, 0.013` for
  `k = 5…8` (`Q = 601`). `D_k` ≈ `0.025–0.04` at the same levels. No decay is visible yet, and
  no growth either. Within `|θ − 1/2| < 2⁻⁶` (3% of `[0,1]`), `D_k`'s share is 34–50% at
  `k = 6–8` and about 5% for `k ≥ 12` (the latter in the unconverged range). At resolved scales
  the discrepancy is **not** concentrated at `E = 0`. The summability of `D_k` is undecided.
* **Fejér entropy (N).** `H_N` is converged for `N ≤ 256` and nearly converged at `N = 512`.
  Its increments per doubling are `0.071, 0.053, 0.037, 0.026, 0.019` (`N = 16 → 512`), a ratio
  of ≈ 0.72. At `N = 1024` the increment is `≤ 0.015` and still decreasing with `Q`. In
  contrast, `∫F_N² dρ` grows by `0.124, 0.112, 0.097, 0.089, 0.086, 0.092`: no decay, consistent
  with an `L²` divergence. If the ratio persisted, `sup H_N ≈ 0.53`. This is evidence for
  `FejerEntropyTarget`, not a proof.
* **Weighted `L²` energy (N).** The binned energy of `(E²/16)ν_Q` at level `k` is converged
  up to `k = 9`: `0.1518, 0.1563, 0.1614, 0.1634, 0.1667` for `k = 5…9`, increments
  `0.005, 0.005, 0.002, 0.003`. This is compatible with `WeightedTarget` but does not decide it
  (a logarithmic divergence of `≈ 0.003` per level is also compatible).
* **Contributions near `0` (N).** The round-4 local masses (`out_flux_local.txt`) are stable in
  `Q` down to `h = 2⁻¹⁸`, because the zero band of `N_{1/2+δ}` has width `e^{−0.3/|δ|}`, and
  `|δ| ≥ 1/Q` resolves `h ≥ e^{−0.3Q}`. So the local law at `0` is resolved far below the
  dyadic resolution limit, while global dyadic quantities are limited by the narrow bands
  everywhere else.
* **Certified bound (U, computer-assisted).** `μ_A((−0.196, 0.196)) ≥ 0.0696`
  (`out_gauss_lower.txt`; `n = 59` Gauss nodes, exact rational recurrence coefficients).
* Q = 809 was started and stopped, because the run would take about 35 minutes; the table stops
  at `Q = 601`.

**Resolution rule.** At fixed `Q` the dyadic quantities agree with larger `Q` only up to level
`≈ log₂ Q + 1` to `2`. Past that level `H_k` grows by about `0.25` per level for every `Q`: an
artefact of the narrow bands of the individual `N_{p/q}`, not of `μ_A`.

**Transfer audit.** Moment matching (degree `< N_Q`) certifies nothing below scale `≈ 12/n`
(Gauss-node spacing at `0`). The only rigorous lower bound at `0` from the 121 exact moments is
`μ_A((−0.196, 0.196)) ≥ 0.0696`. The log² law at `h ≤ 2⁻⁴` rests on the stability in `Q` of the
exact `ν_Q`, not on moments.

## Round 6: cross-flux structure of the finite chiral model (`cross_flux.py`)

`python3 cross_flux.py N [Kmax]` (`N` prime) computes the spectra of the chain operators
`H_{p,0}` of `ThomZeroLevel.Chain` for every flux `p/N` (for `p ≠ 0` the spectrum does not depend
on `t`), so `σ_N = N⁻¹ ∑_p ν_p` is an explicit flux average. Outputs: `out_cross_flux_401.txt`
(`Kmax = 66`) and `out_cross_flux_1009.txt` (`Kmax = 130`). Set `CROSS_FLUX_CACHE=file.npz` to
cache the spectra.

* (A) The moments of `σ_N` equal the zero-area walk counts (`k ≤ 12`), a check of the
  decomposition `A F^{p,t}_ξ = F^{p,t}_{Hξ}`.
* (B) `σ_N([−h,h])·log²(1/h) ≈ 0.50` for `2⁻⁶ ≤ h ≤ 2⁻¹⁰`. The share of this mass coming from
  fluxes within `0.05` of `1/2` rises from 6% (`h = 1/8`) to about 37% (`h = 2⁻¹⁰`, `N = 1009`).
* (C, D) Fejér entropy and weighted Fejér energy of flux-window averages. By convexity these
  bound the values of `σ_N` (exact inequality). Windows of fixed width keep the increments
  decreasing; flux-wise (width `1/N`) the increments grow.

These are finite-`N` computations: degrees above `≈ 2√N` are not moments of `μ_A`, and finite-`N`
entropies are not upper bounds on the limiting ones.

## Round 7: continuous-flux Dirichlet model (`dirichlet.py`, `dirichlet_joint.py`, `dirichlet_moments.py`)

Model: `H_L(α,θ)`, `L×L`, off-diagonal `1`, diagonal `2cos(2π(θ+jα))` (README §10).

* `python3 dirichlet_moments.py L kmax`: exact `(α,θ)`-averaged moments (product midpoint rule,
  exact for trigonometric polynomials of the relevant degree). Output `out_dirichlet_moments.txt`:
  `L(τ(Aᵏ) − m_k(L)) = 2, 26, 296, 3386, 40152` (`k = 2..10`) for `L = 20, 40, 80`, i.e. the
  boundary error is exactly `b_k/L`, as in the proposition of §10.3.
* `python3 dirichlet.py L samples gridfactor`: Hellmann–Feynman derivatives, actual level
  multiplicities `M_L(θ,E)` (Sturm counts on an `α`-grid of `gridfactor·L²` points), the coarea
  entropy bound `R_L(θ)`, the ratio distribution `M/(L|∂αE|)`, exceptional sets and a binned
  entropy of `g_{L,θ}`. Output `out_dirichlet.txt` (`L = 16, 32, 64, 128`: `400 6`; `L = 256`:
  `200 3`).
* `python3 dirichlet_joint.py L samples gridfactor`: quantiles and correlation of `|∂αE|/L` and
  `|∂θE|`, joint small sets, and `R_L` split by energy band. Output `out_dirichlet_joint.txt`.

Findings (Monte Carlo, error on `R_L` ≈ ±0.1):
* `M_L/L ≈ 0.9√L`, far below `L(L+1)`.
* `|∂αE|` does not decay (median ≈ 13–17), while `|∂θE|` decays roughly like `1/L`.
* `R_L` rises from `−1.15` (`L = 16`) to `−0.64` (`L = 256`).
* The exceptional share (ratio > 10) grows `1.3% → 7%` and is over-represented near `E = 0`.
* The binned entropy of `g_{L,θ}` is flat at `≈ −1.85`.

These are evidence only: they do not bound the entropy of `μ_A` in either direction.

## Round 8: Fejér entropies of the Dirichlet model at its own scale (`strip_entropy.py`)

* `python3 strip_entropy.py samples`: for `n = 8, …, 128` and `W = n/2`, estimates the Chebyshev
  coefficients of the Dirichlet model `σ_W`, `σ_{2W}` on a randomly shifted
  `√samples × √samples` grid in `(α,θ)`. It computes the Fejér entropies `H_n(σ_{2W})` and
  `H_n(μ_A)` (exact `c_m`, `cheb_coeffs_n256.txt`). It also checks the Lean two-scale identity
  `c_m(μ_A) = 2c_m(σ_{2W}) − c_m(σ_W)`. Output `out_strip_entropy.txt` (`samples = 90000`).
* `python3 strip_deficit.py` (deficit check): `b_k = ∑_{zero-area closed w} width(w)` equals
  `2, 26, 296, 3386, 40152` for `k = 2, …, 10`. These are exactly the values found in round 7.

Findings:
* The two-scale identity holds to `1e−16` wherever the grid resolves the degree (`n ≤ 32`; `8e−9` at
  `n = 64`).
* `H_n(σ_{2W})` and `H_n(μ_A)` agree to within `0.02` (`n = 8`) and to within `0.0004` (`n = 128`).
* `H_n(μ_A) = 0.187, 0.274, 0.345, 0.397, 0.434` for `n = 8, 16, 32, 64, 128`.

Evidence only. Lean proves `H_n(μ_A) ≤ 2H_n(σ_{2W}) + 2log2 + 1`. No uniform bound on either side is proved.

## Round 9: coarea ratios with dyadic velocity classes (`velocity_classes.py`)

* `python3 velocity_classes.py L samples [g]` samples `(θ, α, k)` for the round-7 Dirichlet model. It finds all crossings of the level `E = E_k(α,θ)` at fixed θ (Sturm counts on an α-grid of size `g·L²`, then bisection) and their velocities `−∂_αp/∂_Ep` (checked against Hellmann–Feynman). It prints the tails `P(R > K)` for `K ∈ {10,…,1000}` of the plain ratio `M_L/(L|∂_αE|)` and of the class ratio `M_{L,j}/(a_j L|∂_αE|)`, globally and on `|E| ≥ 0.5, 1`.
* `out_velocity_classes.txt`: `L = 16, …, 128` with 400 samples, and `L = 256` with 120 samples. `out_velocity_classes_large.txt`: `L = 32` with 3000 samples and `L = 64` with 1500 samples.
* Findings:
  - `M_L ≈ L^{1.4}`;
  - median `R_L` rises slowly, from 0.25 to 0.45;
  - the global `K = 10` tail grows, from 0.012 to 0.042, mostly near 0;
  - away from 0 the `K = 10` tail is flat at about 0.01–0.02;
  - the tails at large K are not resolved.
* No tightness is inferred.
