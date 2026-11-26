# thom-conjecture: Lean 4 formalization of the Heisenberg model (Bado–Pittet)

[![Lean build and axiom audit](https://github.com/paulbado/thom-conjecture/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/paulbado/thom-conjecture/actions/workflows/lean.yml)
![Lean v4.36.0](https://img.shields.io/badge/Lean-v4.36.0-blue)
![Mathlib v4.36.0](https://img.shields.io/badge/Mathlib-v4.36.0-blue)
![sorry: 0](https://img.shields.io/badge/sorry-0-brightgreen)
![custom axioms: 0](https://img.shields.io/badge/custom%20axioms-0-brightgreen)

This repository is a Lean 4 / Mathlib formalization that accompanies the Bado–Pittet work on
canonical spectral measures. It studies the self-adjoint element `A = x + x⁻¹ + y + y⁻¹` of the
group ring of the discrete Heisenberg group `H₃(ℤ)` and its spectral measure `μ_A`.

**Scope.** The repository does **not** prove Thom's conjecture. It does **not** yet prove that
`μ_A` is absolutely continuous: that statement is reduced to explicitly named open propositions.
Even a complete solution of this Heisenberg model would not settle the general question for
torsion-free groups.

## What is proved

* **The spectral measure exists and is unique.** `ThomExistence.muA` is built without von Neumann
  algebras, from the finite quotients `H₃(ℤ/N)` (matrix spectral theorem, exact moment matching
  for `(k+1)² ≤ N`, Prokhorov compactness). `isSpectralMeasureA_iff` shows it is the only
  probability measure on `[-4,4]` with moments `τ(Aᵏ)`.
* **Moments are walk counts.** `τ(Aⁿ)` counts closed lattice walks of zero algebraic area, the
  rational-flux moments agree with them exactly below the sharp threshold `N_Q = 2⌈2√Q⌉`.
* **Chebyshev analysis.** Orthonormal basis of `L²(arcsine)`, Parseval, uniqueness from moments,
  the `L²` criterion and its converse, a weighted criterion away from `0`, an exact formula for
  the atom at `0`, and an `L^q` duality criterion for absolute continuity.
* **Conditional absolute continuity.** Each open target below implies `μ_A ≪ Lebesgue`
  (`ThomConclusions.muA_ac_of_principal`, `muA_ac_of_weighted`, `muA_ac_of_LqTarget`).

## Open targets (named as `def … : Prop`, never assumed)

| Target | Lean name | Consequence proved in Lean | Numerical status |
|---|---|---|---|
| `∑ τ(T_n(A/4))² < ∞` | `ThomBridge.PrincipalTarget` | `μ_A ≪ dE` with `L²(arcsine)` density (equivalence) | likely false (log growth) |
| `∑ (c_{n-2}+2c_n+c_{n+2})² < ∞` | `ThomBridge.WeightedTarget` | `μ_A` off `0` is a.c. with locally `L²` density | doubtful (block energy grows on `[128,256)`) |
| `μ_A{0} = 0` | `ThomConclusions.NoAtomTarget` | with the weighted target, `μ_A ≪ dE` | supported (estimates `≈ n^{-1/2}`) |
| `abs τ(P(A/4)) ≤ K‖P(·/4)‖_{L^q(arcsine)}`, some `q > 2` | `ThomConclusions.LqTarget` | `μ_A ≪ dE`, no atom hypothesis | plausible (`L^p` norms, `p ≤ 1.75`, look bounded) |

## Verification

Every push to `main` runs the GitHub Actions workflow
[`.github/workflows/lean.yml`](.github/workflows/lean.yml). It

1. installs the pinned toolchain and the Mathlib cache, then runs `lake build`;
2. runs [`scripts/check_axioms.sh`](scripts/check_axioms.sh): it fails if the sources contain
   `sorry`, `admit` or an `axiom` declaration, or if any theorem listed in `Audit.lean` depends on
   an axiom other than `propext`, `Classical.choice`, `Quot.sound`;
3. runs [`scripts/module_status.sh`](scripts/module_status.sh), which builds each module separately
   and publishes the table below in the run summary, together with the full axiom audit
   (also uploaded as the `verification-report` artifact).

The badge at the top shows the result for the latest commit on `main`.

To reproduce locally:

```bash
lake exe cache get                 # optional: download the Mathlib build cache
lake build                         # compile everything
scripts/check_axioms.sh audit.txt  # sorry / axiom scan + #print axioms on 100 theorems
scripts/module_status.sh           # per-module build table
```

### Status of each module

Last local verification on commit `101c6cd`: full `lake build` succeeds (6376 jobs), 100 theorems
audited, all depending only on `propext`, `Classical.choice`, `Quot.sound` (some only on `propext`).
The live status of every module is in the summary of the latest workflow run.

| Module | File | Build | Theorems/lemmas | Audited in Audit.lean |
|---|---|---|---|---|
| `ThomLean.Chebyshev` | `ThomLean/Chebyshev.lean` | ✅ passing | 2 | 2 |
| `ThomLean.Chebyshev.Arcsine` | `ThomLean/Chebyshev/Arcsine.lean` | ✅ passing | 31 | 8 |
| `ThomLean.Chebyshev.Criterion` | `ThomLean/Chebyshev/Criterion.lean` | ✅ passing | 8 | 2 |
| `ThomLean.Chebyshev.Lebesgue` | `ThomLean/Chebyshev/Lebesgue.lean` | ✅ passing | 8 | 3 |
| `ThomLean.Heisenberg.Group` | `ThomLean/Heisenberg/Group.lean` | ✅ passing | 15 | 2 |
| `ThomLean.Heisenberg.Moments` | `ThomLean/Heisenberg/Moments.lean` | ✅ passing | 9 | 6 |
| `ThomLean.Heisenberg.Isoperimetric` | `ThomLean/Heisenberg/Isoperimetric.lean` | ✅ passing | 14 | 2 |
| `ThomLean.Heisenberg.Threshold` | `ThomLean/Heisenberg/Threshold.lean` | ✅ passing | 19 | 5 |
| `ThomLean.Heisenberg.Examples` | `ThomLean/Heisenberg/Examples.lean` | ✅ passing | 10 | 3 |
| `ThomLean.Reductions.Collision` | `ThomLean/Reductions/Collision.lean` | ✅ passing | 8 | 5 |
| `ThomLean.Bridge` | `ThomLean/Bridge.lean` | ✅ passing | 12 | 8 |
| `ThomLean.Chebyshev.Weighted` | `ThomLean/Chebyshev/Weighted.lean` | ✅ passing | 25 | 12 |
| `ThomLean.Chebyshev.Atom` | `ThomLean/Chebyshev/Atom.lean` | ✅ passing | 14 | 4 |
| `ThomLean.WeightedBridge` | `ThomLean/WeightedBridge.lean` | ✅ passing | 9 | 9 |
| `ThomLean.Existence` | `ThomLean/Existence.lean` | ✅ passing | 27 | 11 |
| `ThomLean.Conclusions` | `ThomLean/Conclusions.lean` | ✅ passing | 14 | 13 |
| `ThomLean.Chebyshev.Duality` | `ThomLean/Chebyshev/Duality.lean` | ✅ passing | 2 | 1 |

| File | Content |
|---|---|
| `ThomLean/Chebyshev.lean` | finite energies, abstract obstruction, target names |
| `ThomLean/Chebyshev/Arcsine.lean` | arcsine law, orthonormal basis, completeness, Parseval |
| `ThomLean/Chebyshev/Criterion.lean` | `L²` criterion, uniqueness from moments |
| `ThomLean/Chebyshev/Lebesgue.lean` | Lebesgue density, absolute continuity, local `L²` |
| `ThomLean/Chebyshev/Weighted.lean` | weighted measure `(E²/16)μ`, three-term identity, criterion away from `0` |
| `ThomLean/Chebyshev/Atom.lean` | Cesàro formula for the atom at `0`, energy-growth criterion |
| `ThomLean/Chebyshev/Duality.lean` | `L^q` duality criterion for absolute continuity |
| `ThomLean/Heisenberg/Group.lean` | `H₃(ℤ)`, words, walks, algebraic area |
| `ThomLean/Heisenberg/Moments.lean` | group ring, trace, flux traces, character filter |
| `ThomLean/Heisenberg/Isoperimetric.lean` | discrete isoperimetric inequality |
| `ThomLean/Heisenberg/Threshold.lean` | `N_Q`, exact moment matching, sharpness |
| `ThomLean/Heisenberg/Examples.lean` | kernel-checked small values |
| `ThomLean/Reductions/Collision.lean` | Poisson kernel, collision identity |
| `ThomLean/Bridge.lean` | `τ(T_n(A/4))`, principal target equivalences |
| `ThomLean/WeightedBridge.lean` | weighted target, flux reformulation, Christoffel bound |
| `ThomLean/Existence.lean` | finite quotients `H₃(ℤ/N)`, existence of `μ_A` |
| `ThomLean/Conclusions.lean` | consequences for `μ_A`, `L^q` targets |
| `Audit.lean` | `#print axioms` for the principal theorems |
| `numerics/` | Python scripts and data, not part of the proofs |

## Detailed status of the statements

### Status legend

* **U**: unconditional theorem.
* **C**: conditional implication. The hypotheses are stated explicitly and none is equivalent
  to the target.
* **P**: an open proposition. It is named only and never assumed.
* **N**: not formalized.

### 1. Chebyshev analytical framework (`ThomLean/Chebyshev/…`)

| Statement | Lean name | Status |
|---|---|---|
| Arcsine law `ρ = π⁻¹ (x ↦ 4x)_* measureT`, a probability measure on `[-4,4]` | `arcsine`, `instIsProbabilityMeasureRealArcsine`, `arcsine_compl_Icc` | U |
| `∫ g dρ = π⁻¹ ∫₀^π g(4 cos θ) dθ` | `integral_arcsine_eq_cos` | U |
| Lebesgue density `ρ = (π√(16−E²))⁻¹ 𝟙_{(-4,4]} dE` | `arcsine_eq_withDensity` | U |
| Orthogonality and exact normalisation of `T_n(E/4)` (values 1 and 1/2) | `integral_cheb_mul_cheb_of_ne`, `integral_cheb_zero_sq`, `integral_cheb_sq_of_ne_zero` | U |
| `1, √2 T_n(E/4)` is orthonormal in `L²(ρ)` | `orthonormal_chebL2` | U |
| Every polynomial lies in the span of the `T_n` | `mem_span_T` | U |
| **Completeness** (Weierstrass approximation plus density of bounded continuous functions) | `chebL2_span_dense`, `chebBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 ρ)` | U |
| **Parseval identity** | `parseval` | U |
| Uniqueness: two measures on `[-4,4]` with the same Chebyshev moments are equal | `eq_of_integral_cheb_eq` | U |
| **Criterion**: `∑ c_n² < ∞` ⇒ `μ = fρ` with `0 ≤ f ∈ L²(ρ)` and `‖f‖² = 1 + 2∑c_n²` | `exists_density_of_summable` | C |
| `∑ c_n² < ∞` ⇒ `μ ≪ Lebesgue` | `absolutelyContinuous_of_summable` | C |
| `∑ c_n² < ∞` ⇒ Lebesgue density in `L²([a,b])` for every `-4<a≤b<4` | `exists_lebesgue_density_of_summable` | C |
| Converse (Bessel inequality): an `L²(ρ)` density ⇒ `∑ c_n² < ∞` | `ThomBridge.summable_of_L2_density` | C |
| `weightedEnergy ≤ squareEnergy` (finite sums) | `weightedEnergy_le_squareEnergy` | U |
| The weighted condition does not imply the `L²` condition (witness `c_n = n^{-1/2}`) | `weighted_not_imp_L2` | U |

### 2. Heisenberg spectral model (`ThomLean/Heisenberg/…`)

| Statement | Lean name | Status |
|---|---|---|
| `H₃(ℤ)` with `(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')` is a group | `H3`, `H3.instGroup` | U |
| `xy = zyx`, `[x,y] = z`, `z` is central, `H₃` is torsion-free | `x_mul_y`, `commutator_xy`, `z_central`, `eq_one_of_pow_eq_one` | U |
| Word ↦ (endpoint, algebraic area) | `evalWord_eq` | U |
| A word is trivial iff its walk is closed with zero area | `evalWord_eq_one_iff` | U |
| `Aⁿ = ∑_{w∈Stepⁿ} [w]` in `R[H₃]` | `opA_pow` | U |
| **Canonical trace**: `τ(Aⁿ)` = number of closed walks with zero area (eq. (14)) | `tau_opA_pow` | U |
| Flux trace: `τ_α(Aⁿ) = ∑_{closed γ} e^{2πiα·area γ}` | `fluxTrace_opA_pow` | U |
| Orthogonality of characters of `ℤ/Qℤ` | `rootsOfUnity_filter` | U |
| **Rational-flux moment formula**: `(1/Q)∑_p τ_{p/Q}(Aⁿ) = #{closed γ : Q ∣ area γ}` (eq. (15)) | `avg_fluxTrace_opA_pow` | U |
| Discrete isoperimetric inequality `|area| ≤ r·s`, `16|area| ≤ n²` | `abs_area_le`, `sixteen_abs_area_le` | U |
| `N_Q = 2⌈2√Q⌉` | `kQ_eq_ceil`, `NQ_eq` | U |
| **Exact moment matching** `m_n^{(Q)} = m_n` for `n < N_Q` | `moment_eq_fluxMoment` | U |
| A closed walk of length `N_Q` with area exactly `Q` (polyomino boundary) | `exists_walk_area_eq` | U |
| **Sharpness**: `m_{N_Q} < m_{N_Q}^{(Q)}` for every `Q ≥ 1` | `moment_lt_fluxMoment_NQ` | U |
| Moment discrepancies are nonnegative integers | `moment_le_fluxMoment` | U |
| Kernel-checked values `τ(A⁶) = 232`, `m₆^{(2)} = 256`; first discrepancies 8 (`Q=1²`) and 24 (`Q=1·2`) | `moment_six`, `discrepancy_Q1`, `discrepancy_Q2` | U |
| General first discrepancy `8m` (`Q = m²`) and `8(2m+1)` (`Q = m(m+1)`) | — | **N** (equality case of the isoperimetric inequality; checked only for `m = 1`) |
| Lower bound `2ℓ_Q` on the discrepancy at `N_Q` | — | **N** (only `> 0` is proved) |
| Existence of the spectral measure `μ_A` (via finite quotients `H₃(ℤ/N)` and Prokhorov compactness, see §5) | `ThomExistence.exists_spectralMeasureA`, `muA` | U |
| Identification of `τ_α` with the moments of the Harper density of states `ν_α` | — | **N** |
| Absolute continuity of `μ^{(q)}` (Floquet theory), `W₁` rate `q^{-1/2}` (Jackson) | — | **N** |

### 3. Analytical reductions (`ThomLean/Reductions/Collision.lean`)

| Statement | Lean name | Status |
|---|---|---|
| Poisson kernel, `∫ P_η = 1` | `poisson`, `integral_poisson` | U |
| `h_η ≤ π P_η` and `P_η(t) ≤ 3 P_η(t−u)` for `|u| ≤ η` (pointwise part of Lemma 3.1) | `box_le_pi_mul_poisson`, `poisson_le_three_mul_shift` | U |
| **Collision identity** `∫ B_η² = (4η²)⁻¹ ∑ w_k w_l (2η − |ξ_k−ξ_l|)₊` for any finite configuration (Lemma 4.2) | `collision_identity` | U |
| `C(η)/(4η) ≤ ∫B_η² ≤ C(2η)/(2η)` (eq. (11)) | `collision_bounds` | U |
| Discretization by Chambers roots, `W₁(ν_{a/q}, σ_{a/q}) ≤ 4π/q²` | — | **N** (needs the Jitomirskaya–Konstantinov–Krasovsky band bound) |
| Theorem 4.3 (`(C)` ⇒ local `L²` density) | — | **N** (needs Young's inequality in `L^p`, the `W₁` transfer and weak compactness) |
| Fourier–Bessel transfer estimate, dyadic Haar energy identity | — | **N** (not in the supplied notes) |

### 4. The principal target (`ThomLean/Bridge.lean`)

* `chebTrace n := τ(T_n(A/4))` in `ℝ[H₃]`. `chebTrace_eq` expresses it through the walk counts. **U**
* `IsSpectralMeasureA μ` says that `μ` is a probability measure on `[-4,4]` with
  `∫Eᵏ dμ = τ(Aᵏ)`. `chebCoeff_eq_chebTrace` and `spectral_unique` are **U** given this hypothesis.
* `PrincipalTarget := Summable (n ↦ τ(T_{n+1}(A/4))²)`. **P**
* `principalTarget_iff_L2`: for the spectral measure, the target holds **if and only if**
  `μ_A` has an `L²(arcsine)` density. **C**
* `ac_of_principalTarget`: the target implies `μ_A ≪ Lebesgue` with a locally `L²` density on `(−4,4)`. **C**
* `fluxCheb_eq_chebTrace`: the rational-flux Chebyshev coefficients `c_n^{(Q)}` are
  *exactly* `τ(T_n(A/4))` for `n < N_Q`. **U**
* `principalTarget_iff_uniform_flux`: the target holds **if and only if**
  `sup_Q ∑_{1≤n<N_Q} (c_n^{(Q)})² < ∞`. Each sum involves finitely many integer walk counts. **U**

#### Remaining unproved statements

1. (**P**, the principal target) `∑_{n≥1} τ(T_n(A/4))² < ∞`. Equivalently, by
   `principalTarget_iff_uniform_flux`, `∃ K, ∀ Q ≥ 1, ∑_{n=1}^{N_Q−1} (∑_k [Xᵏ]T_n · 4⁻ᵏ · m_k^{(Q)})² ≤ K`.
2. (**P**, the alternative target) `∃ p > 1, ∀ J ⋐ (−4,4), sup_{Q≥2} ‖P_{Q^{-1/3}} ∗ μ_Q‖_{L^p(J)} < ∞`.
   This is not formalized because `μ_Q` (the Harper density of states) is not constructed.
3. (**P**, the weighted target, §5) `∑_{n≥2} (c_{n-2}+2c_n+c_{n+2})² < ∞` (`WeightedTarget`).
4. (**P**, the atom at zero, §5) `μ_A{0} = 0`, equivalently `NoAtomTarget`; implied by the
   `EnergyGrowthTarget` `N⁻¹∑_{n<N} c_n² → 0`.
4'. (**P**, the `L^q` duality target, §5) `∃ K, ∀ P, |τ(P(A/4))| ≤ K‖P(·/4)‖_{L^q(arcsine)}` for
   some `q > 2`. It implies `μ_A ≪ dE` with no hypothesis on atoms.
5. (**N**) Harper/Floquet identification of `τ_{p/q}` with `ν_{p/q}`, absolute continuity of
   `μ^{(q)}`, and the `W₁` estimate.
6. (**N**) The exact discrepancies `8m` and `8(2m+1)` for general `m`, through the
   equality case of the isoperimetric inequality.

### 5. Weighted measure, atom at zero, existence of `μ_A` (round 3)

| Statement | Lean name | Status |
|---|---|---|
| `4X²T_m = T_{m+2} + 2T_m + T_{m-2}` in `ℝ[X]`, all `m ∈ ℤ` | `ThomChebyshev.four_X_sq_mul_T` | U |
| `ν = (E²/16)μ`: `d_n = (c_{n-2}+2c_n+c_{n+2})/4` for `n ≥ 2`; `d_0 = (c_0+c_2)/2`, `d_1 = (3c_1+c_3)/4` | `chebCoeff_weighted`, `chebCoeff_weighted_zero`, `chebCoeff_weighted_one` | U |
| Chebyshev criterion for arbitrary finite measures on `[-4,4]` | `ac_of_summable_finite` | C |
| `μ|_{ℝ∖{0}} ≪ ν`, and `ν{0} = 0` always | `restrict_compl_zero_ac_weighted`, `weighted_singleton_zero` | U |
| `∑ d_n² < ∞ ⇒ μ|_{ℝ∖{0}} ≪ dE`; with `μ{0} = 0`, `μ ≪ dE` | `ac_off_zero_of_weighted_summable`, `ac_of_weighted_summable` | C |
| Old `L²` condition ⇒ weighted condition | `weighted_summable_of_summable`, `ThomBridge.weightedTarget_of_principalTarget` | C |
| `WeightedTarget ⇔` uniform bound on finite rational-flux weighted energies `∑_{n<N_Q−4}` | `ThomBridge.weightedTarget_iff_uniform_flux` | U |
| **Atom formula** `μ{0} = lim (N+1)⁻¹ ∑_{j≤N} (−1)^j c_{2j}` (telescoping `4X²S_N = 1+T_2+(−1)^N(T_{2N}+T_{2N+2})` plus dominated convergence) | `four_X_sq_mul_altSum`, `tendsto_atomMean`, `atom_eq_zero_iff` | U |
| `N⁻¹∑_{n<N} c_n² → 0 ⇒ μ{0} = 0` (Cauchy–Schwarz) | `atom_eq_zero_of_energy` | C |
| Christoffel bound `μ{0} ≤ τ(p(A/4)²)` for every `p` with `p(0)=1` | `ThomBridge.atom_le_tau`, `ThomConclusions.muA_atom_le` | U |
| Schreier graph of `H₃(ℤ/N)`: `(Aᵏ)_{pq}` counts words, `A` symmetric, eigenvalues in `[-4,4]` | `ThomExistence.adj_pow_apply`, `adj_symm`, `abs_eigenvalues_le` | U |
| Finite spectral measure `∑_j U_{pj}² δ_{λ_j}` has moments `(Aᵏ)_{pp}` | `adj_pow_diag`, `integral_pow_specMeasure` | U |
| `(k+1)² ≤ N`: a word of length `k` is trivial in `H₃(ℤ/N)` iff trivial in `H₃(ℤ)`, so the moments are exactly `τ(Aᵏ)` | `castH_evalWord_eq_zero_iff`, `quot_adj_pow`, `integral_pow_quotMeasure` | U |
| **Existence**: a cluster point in the compact space `ProbabilityMeasure [-4,4]` is a spectral measure; `μ_A` is canonical | `exists_spectralMeasureA`, `muA`, `isSpectralMeasureA_iff` | U |
| `μ_A{0} = lim (N+1)⁻¹∑(−1)^j τ(T_{2j}(A/4))` | `ThomConclusions.muA_atom_tendsto`, `noAtomTarget_iff` | U |
| `WeightedTarget ⇒ μ_A|_{ℝ∖{0}} ≪ dE` | `muA_off_zero_ac` | C |
| `WeightedTarget ∧ NoAtomTarget ⇒ μ_A ≪ dE`; same with `EnergyGrowthTarget` | `muA_ac_of_weighted`, `muA_ac_of_weighted_energy` | C |
| `PrincipalTarget ⇒ EnergyGrowthTarget`, `PrincipalTarget ⇒ μ_A ≪ dE` | `energyGrowth_of_principal`, `muA_ac_of_principal` | C |
| `ν = (E²/16)μ` with `∑ d_n² < ∞`: `μ|_{ℝ∖{0}} = h dE`, `h ∈ L²([a,b])` for `[a,b] ⊂ (−4,4)∖{0}` | `exists_lebesgue_density_off_zero`, `ThomConclusions.muA_off_zero_local_L2` | C |
| **Duality criterion**: `abs(∫P(E/4)dμ) ≤ K‖P(·/4)‖_{L^q(ρ)}` for all polynomials (`q ≥ 1`) ⇒ `μ ≪ dE` (Weierstrass, Urysohn, regularity) | `ThomChebyshev.ac_of_poly_Lq_bound` | C |
| `LqTarget q ⇒ μ_A ≪ dE`; `PrincipalTarget ⇒ LqTarget 2` | `ThomConclusions.muA_ac_of_LqTarget`, `lqTarget_two_of_principal` | C |
| `μ_A{0} = 0` (in the literature: Linnell's theorem on the Atiyah conjecture, or continuity of the Harper density of states) | — | **P** here, **N** |
| The weighted target itself | — | **P** (numerics now argue against it, see below) |
| `LqTarget q` for some `q > 2` (an `L^p` density, `p < 2`) | — | **P** (numerically plausible) |

## Numerical evidence (see `numerics/README.md`)

Round 3 (`n ≤ 256`, see `numerics/README.md`): the weighted block energy `∑_{[128,256)} d_n²`
is more than twice the one on `[64,128)`, and the smoothed densities develop growing peaks near
`E ≈ ±0.72, ±1.95, ±2.57`, close to band edges of the flux-`1/3` Harper operator. So the
weighted `L²` target is **not** supported by the data, even though its partial sums look
flat. Smoothed `L^p` norms for `p ≤ 1.75` do look bounded, which favours the `L^q` duality
target with `q > 2`. The atom estimates (Cesàro means, Christoffel bounds) decay like
`n^{-1/2}`, consistent with `μ_A{0} = 0`. All of this is heuristic.

Round 2: exact and stable computations of `τ(T_n(A/4))` for `n ≤ 170` suggest `c_n² ≍ 1/n`. The partial
sums grow like `0.054·log n`, and the excess comes from a concentration of `μ_A` at `E = 0`.
If this persists, **the principal target is false**: `μ_A` would have no `L²(arcsine)` density
(by `principalTarget_iff_L2`). This is heuristic, and it does not decide absolute continuity
or local `L^p` regularity for `p < 2`. It suggests moving to targets localized away from `E = 0`,
or to `L^p` targets with `p < 2`.
