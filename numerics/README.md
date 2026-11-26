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
