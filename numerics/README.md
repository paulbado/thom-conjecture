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
