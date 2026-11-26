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
* **`μ_A` has no atoms (unconditional).** `ThomNoAtoms.muA_no_atoms : ∀ E, muA {E} = 0`, with the
  quantitative bound `muA_singleton_le : μ_A{E} ≤ 2/L` for every `L ≥ 1`. The proof is a
  unique-continuation estimate along the rows of `H₃(ℤ/N)`, an eigenvalue count, vertex
  transitivity and a passage to the limit; it uses no Chebyshev summability target.
* **Modulus of continuity.** `ThomNoAtoms.muA_Icc_le`: `μ_A([E−h_L/2, E+h_L/2]) ≤ 4/L` with
  `h_L = 1/(L·Dᴸ)`, i.e. `μ_A(I) ≲ 1/log(1/|I|)`.
* **Fejér criterion.** `ThomChebyshev.fejer_nonneg`, `integral_fejer`,
  `tendsto_integral_fejer_mul_poly`, `ac_of_fejer_bounded`: the Fejér densities are positive,
  normalised, converge to `μ` on polynomials, and `sup_N ‖F_N‖_{L^p} < ∞` (`p > 1`) gives the
  `L^q` duality bound and `μ ≪ Lebesgue`.
* **Entropy criteria (round 5).** `ThomChebyshev.ac_of_fejEnt_bounded`: bounded Fejér relative
  entropies `H_N = ∫ F_N log F_N dρ` give uniform integrability of the Fejér densities and
  `μ ≪ Lebesgue`; this criterion contains every Fejér `L^p` criterion and is strictly weaker
  (`fejEnt_le_of_Lp`, `entropy_strictly_weaker`). `ThomDyadic`: the dyadic entropy increment
  identity, `0 ≤ H_{k+1} − H_k ≤ D_k`, and "bounded dyadic entropy (or summable discrepancies)
  ⇒ absolute continuity", transported to `μ_A` by `θ = arccos(E/4)/π`
  (`ThomDyadicTarget.muA_ac_of_summable_dyDisc`).
* **The two weighted targets are one (round 5).** `ThomWeightedL2.weightedLqTarget_two_iff :
  WeightedLqTarget 2 ↔ WeightedTarget`. Localization: `μ_A ≪ dE` iff its restrictions to
  `{abs E ≥ ε}` are absolutely continuous (`muA_ac_iff_local`).
* **Lower bounds at `0` (round 5).** `ThomLowerBound.le_measureReal_of_moments` transfers lower
  bounds on compact sets from moment-matching approximants (such as the rational-flux averages)
  to `μ_A`; `not_lqTarget_of_logSq` shows that `μ_A([−h,h]) ≥ c/log²(1/h)` would refute every
  `LqTarget q`, every Fejér `L^p` target and `PrincipalTarget`. The lower bound itself is open.
* **Conditional absolute continuity.** Each open target below implies `μ_A ≪ Lebesgue`
  (`ThomConclusions.muA_ac_of_principal`, `ThomNoAtoms.muA_ac_of_weightedTarget`,
  `ThomConclusions.muA_ac_of_LqTarget`, `ThomFejer.muA_ac_of_fejerTarget`,
  `ThomFejer.muA_ac_of_weightedLqTarget`).

## Open targets (named as `def … : Prop`, never assumed)

| Target | Lean name | Consequence proved in Lean | Numerical status |
|---|---|---|---|
| `∑ τ(T_n(A/4))² < ∞` | `ThomBridge.PrincipalTarget` | `μ_A ≪ dE` with `L²(arcsine)` density (equivalence) | numerically false (mass `≈ 0.47/log²(1/h)` at `0`, see below) |
| `∑ (c_{n-2}+2c_n+c_{n+2})² < ∞` | `ThomBridge.WeightedTarget` | **alone** gives `μ_A ≪ dE` (`ThomNoAtoms.muA_ac_of_weightedTarget`); **equivalent** to `WeightedLqTarget 2` (`ThomWeightedL2.weightedLqTarget_two_iff`) | inconclusive: binned weighted `L²` energy converged in `Q` up to `2⁹` angular cells, growing `≈ 0.003` per level there |
| `sup_N ∫ abs(F_N)^p dρ < ∞`, `p > 1` (Fejér densities) | `ThomFejer.FejerTarget` | `μ_A ≪ dE`; `p = 3/2` gives `LqTarget 3` | numerically false for every `p > 1` (same reason) |
| `abs τ((A/4)² P(A/4)) ≤ K‖P(·/4)‖_{L^q(arcsine)}` | `ThomFejer.WeightedLqTarget` | with `muA_no_atoms`, `μ_A ≪ dE`; `q = 2` is `WeightedTarget` | compatible with the exact flux averages for `q ≥ 2` |
| `abs τ(P(A/4)) ≤ K‖P(·/4)‖_{L^q(arcsine)}`, some `q < ∞` | `ThomConclusions.LqTarget` | `μ_A ≪ dE`; forces `μ_A([−h,h]) = O(h^{1/q})` (`ThomFejer.muA_le_of_lqTarget`); refuted by `LogSqLowerBound` (`ThomLowerBound.not_lqTarget_of_logSq`) | numerically false for every `q < ∞` |
| `sup_N ∫ F_N log F_N dρ < ∞` (Fejér entropy) | `ThomWeightedL2.FejerEntropyTarget` | `μ_A ≪ dE` (`muA_ac_of_fejerEntropyTarget`); implied by every `FejerTarget p` | **recommended**: compatible with a `1/(abs E log³)` profile at `0`; increments decay by `≈ 0.72` per doubling of `N` up to `N = 512` |
| `∑_k D_k(λ) < ∞`, `λ = θ_*μ_A` (dyadic discrepancies) | `Summable (ThomDyadic.dyDisc ThomDyadicTarget.lam)` | `μ_A ≪ dE` (`ThomDyadicTarget.muA_ac_of_summable_dyDisc`) | undecided: `D_k ≈ 0.03–0.04` at the levels resolved by `Q ≤ 809` |
| `μ_A([−h,h]) ≥ c/log²(1/h)` (a lower bound, not a regularity target) | `ThomLowerBound.LogSqLowerBound` | refutes `LqTarget q` (all `q ≥ 1`), `FejerTarget p` (all `p > 1`), `PrincipalTarget` | numerically true (`≈ 0.47/log²(1/h)`); certified only at `h ≈ 0.2` |

`ThomConclusions.NoAtomTarget` (`μ_A{0} = 0`) is no longer open: it is proved as
`ThomNoAtoms.noAtomTarget`.

"Numerically false" means: exact rational-flux averages `ν_Q` (`Q ≤ 293`, Chambers' formula,
validated against the walk counts) give `ν_Q([−h,h]) · log²(1/h) ≈ 0.47` for
`2⁻¹⁸ ≤ h ≤ 2⁻⁴`, stable in `Q`. The mechanism is the zero Landau level near flux `1/2`
(`2|δ|q` bands within `e^{−0.3/|δ|}` of `0`). This is evidence, not a proof; a proof of the lower
bound `μ_A([−h,h]) ≥ c/log²(1/h)` would refute these targets formally via
`muA_le_of_lqTarget`. See `numerics/README.md`, round 4. Round 5 makes this implication a theorem
(`ThomLowerBound.not_lqTarget_of_logSq`) and audits the transfer from `ν_Q` to `μ_A`: see §8.

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
scripts/check_axioms.sh audit.txt  # sorry / axiom scan + #print axioms on 195 theorems
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
| `ThomLean.Chebyshev.Duality` | `ThomLean/Chebyshev/Duality.lean` | ✅ passing | 3 | 2 |
| `ThomLean.NoAtoms` | `ThomLean/NoAtoms.lean` | ✅ passing | 39 | 24 |
| `ThomLean.Chebyshev.Fejer` | `ThomLean/Chebyshev/Fejer.lean` | ✅ passing | 20 | 15 |
| `ThomLean.FejerTarget` | `ThomLean/FejerTarget.lean` | ✅ passing | 12 | 11 |
| `ThomLean.Chebyshev.Dyadic` | `ThomLean/Chebyshev/Dyadic.lean` | ✅ passing | 29 | 16 |
| `ThomLean.DyadicTarget` | `ThomLean/DyadicTarget.lean` | ✅ passing | 12 | 7 |
| `ThomLean.Chebyshev.Entropy` | `ThomLean/Chebyshev/Entropy.lean` | ✅ passing | 9 | 7 |
| `ThomLean.WeightedL2` | `ThomLean/WeightedL2.lean` | ✅ passing | 9 | 8 |
| `ThomLean.LowerBound` | `ThomLean/LowerBound.lean` | ✅ passing | 6 | 6 |

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
| `ThomLean/NoAtoms.lean` | unconditional absence of atoms of `μ_A`, log modulus of continuity |
| `ThomLean/Chebyshev/Fejer.lean` | Fejér densities, positivity, Fejér criterion |
| `ThomLean/FejerTarget.lean` | Fejér and weighted `L^q` targets for `μ_A`, power decay forced by `LqTarget` |
| `ThomLean/Chebyshev/Dyadic.lean` | dyadic entropy and discrepancy on `[0,1)`, increment identity, criteria |
| `ThomLean/DyadicTarget.lean` | transport `λ = θ_*μ_A`, back-transport of absolute continuity |
| `ThomLean/Chebyshev/Entropy.lean` | Fejér relative entropy, uniform integrability, criterion, strictness |
| `ThomLean/WeightedL2.lean` | `WeightedTarget ⇔ WeightedLqTarget 2`, localization, entropy target |
| `ThomLean/LowerBound.lean` | transfer of lower bounds, `LogSqLowerBound ⇒ ¬LqTarget` |
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
| `μ_A{0} = 0`: now proved, see §6 | `ThomNoAtoms.noAtomTarget` | U |
| The weighted target itself | — | **P** (numerics inconclusive) |
| `LqTarget q` for some `q > 2` (an `L^p` density, `p < 2`) | — | **P** (numerically plausible) |

### 6. No atoms (round 4, `ThomLean/NoAtoms.lean`)

| Statement | Lean name | Status |
|---|---|---|
| Orthonormal eigenvector combinations: `‖∑_{j∈J} β_j u_j‖² = ∑ β_j²`, `A ∑ β_j u_j = ∑ λ_j β_j u_j` | `sum_sq_comb`, `adj_mulVec_comb` | U |
| **Eigenvalue counting**: if `‖v‖² ≤ K‖(A−λ)v‖²` for all `v` vanishing on `S` and `Kh² < 1`, then `#{j : abs(λ_j − λ) ≤ h} ≤ #S` | `card_near_le` | U |
| `∑_p σ_p(g) ≤ #{j : abs(λ_j − λ) ≤ h}` for `g ≤ 1` vanishing off `[λ−h, λ+h]` | `sum_integral_le` | U |
| **Vertex transitivity** of the Schreier graph of `H₃(ℤ/N)` (left multiplication commutes with the right action): `(Aᵏ)_{pp} = (Aᵏ)_{00}`, all `σ_p` coincide | `quot_adj_pow_diag`, `specMeasure_map_eq` | U |
| **Row recurrence**: `e(a+1) ≤ (5λ²+15)(ρ(a) + e(a) + e(a−1))`, with `e`, `ρ` the row energies of `v` and `(A−λ)v` | `rowE_succ_le` | U |
| **Unique continuation**: `v = 0` on the rows `a ≡ 0, −1 (mod L)` ⇒ `‖v‖² ≤ L·Dᴸ‖(A−λ)v‖²`, `D = 3(5λ²+15)` | `rowE_block`, `rowE_le`, `uniqueCont` | U |
| `#{a ∈ ℤ/N : a ≡ t (mod L)}·L = N`; `#S·L ≤ 2N³` | `card_fiber_mul`, `card_Srows_le` | U |
| **Uniform window bound**: `L ∣ N` ⇒ `∫ g dσ_N ≤ 2/L` for `g ≤ 1` vanishing off `[λ−h_L, λ+h_L]`, `h_L = 1/(L·Dᴸ)` | `quot_integral_le` | U |
| Cluster points of `σ_{s(n)}` are `μ_A`; bounds pass to cluster points | `map_eq_muA_of_mapClusterPt`, `integral_le_of_mapClusterPt` | U |
| **`μ_A{E} ≤ 2/L` for all `L ≥ 1`, hence `μ_A{E} = 0` for every `E`**; countable sets are null | `muA_singleton_le`, `muA_no_atoms`, `muA_countable` | U |
| `NoAtomTarget` holds; `WeightedTarget ⇒ μ_A ≪ dE` | `noAtomTarget`, `muA_ac_of_weightedTarget` | U / C |

The argument is elementary and self-contained, in the spirit of the "no eigenvalues for
amenable Cayley graphs with finite quotients" arguments: the row recurrence plays the role of
unique continuation, and the rows `a ≡ 0, −1 (mod L)` form a set of density `2/L` whose removal
forces any approximate eigenvector to be small. The window `h_L` shrinks exponentially in `L`;
this is enough for atoms, but gives no modulus of continuity better than
`μ_A([E−h, E+h]) ≲ 1/log(1/h)`, far from absolute continuity.

### 7. Fejér criterion and weighted `L^q` target (round 4)

| Statement | Lean name | Status |
|---|---|---|
| `F_N(4cos θ) = 1 + 2∑_{n≤N} (1 − n/(N+1)) c_n cos nθ` | `ThomChebyshev.fejer_cos`, `ThomFejer.fejer_muA_cos` | U |
| `∫ F_N T_m(E/4) dρ = (1 − m/(N+1))₊ c_m`; `∫ F_N dρ = 1` | `integral_fejer_mul_cheb`, `integral_fejer` | U |
| **Positivity**: Fejér's identity `(N+1)Φ_N = abs(∑_{k≤N} e^{ikx})²`, `K_N ≥ 0` on `[−4,4]²`, `F_N = ∫K_N dμ ≥ 0`, `‖F_N‖_{L¹(ρ)} = 1` | `fejer_identity`, `fejerKernel_nonneg`, `fejerKern_nonneg`, `fejer_nonneg`, `integral_abs_fejer` | U |
| `∫ F_N P(E/4) dρ → ∫ P(E/4) dμ` for every polynomial | `tendsto_integral_fejer_mul_poly` | U |
| **Fejér criterion**: `sup_N ‖F_N‖_{L^p(ρ)} ≤ M` ⇒ `abs ∫P dμ ≤ M‖P‖_{L^q(ρ)}`; for `p > 1`, `μ ≪ dE` | `lq_bound_of_fejer`, `ac_of_fejer_bounded` | C |
| Converse in dual form: an `L^p(ρ)` density gives the `L^q` bound | `lq_bound_of_Lp_density`, `ThomFejer.lqTarget_of_Lp_density` | C |
| `FejerTarget p ⇒ LqTarget p'`, `FejerTarget (3/2) ⇒ LqTarget 3`, `FejerTarget p ⇒ μ_A ≪ dE` | `lqTarget_of_fejerTarget`, `lqTarget_three_of_fejerTarget`, `muA_ac_of_fejerTarget` | C |
| Quantitative duality: `μ(C) ≤ δ·B` when `C ⊆ U` and `ρ(U) ≤ δ^q` | `ThomChebyshev.measureReal_compact_le_of_poly_Lq_bound` | C |
| `LqTarget q ⇒ μ_A(C) ≤ B·ρ(U)^{1/q}` | `ThomFejer.muA_le_of_lqTarget` | C |
| `WeightedLqTarget q ⇒ μ_A ≪ dE` (with `muA_no_atoms`); `LqTarget q ⇒ WeightedLqTarget q` | `muA_ac_of_weightedLqTarget`, `weightedLqTarget_of_lqTarget` | C |
| The `L^{3/2}` Fejér target | — | **P**, numerically false (see `numerics/README.md`) |
| `WeightedLqTarget q`, `q ≥ 2` | — | **P**, recommended next target |
| The Fejér converse `‖F_N‖_p ≤ ‖f‖_p` (Jensen plus Fubini for the positive kernel) | — | not formalized (classical) |

**Remaining obstruction, stated precisely.** Unconditionally we have `μ_A{E} = 0` and
`μ_A(I) ≲ 1/log(1/|I|)`. Absolute continuity needs `μ_A(I) → 0` uniformly as the Lebesgue
measure of `I` (a finite union of intervals) tends to `0`. The row argument cannot give this:
its window `h_L` shrinks like `D^{−L}`, so it only controls intervals of length `e^{−cL}` by
`2/L`. Any `L^p` route with `p > 1` is blocked at `E = 0` by the zero Landau level near flux
`1/2` (numerically `μ_A([−h,h]) ≈ 0.47/log²(1/h)`). The open question that remains is a
weighted bound, for example `WeightedLqTarget 2`: an `L²` (or `L^p`, `p > 1`) density for
`(E²/16)μ_A`.

### 8. Entropy, dyadic discrepancies, weighted `L²`, lower bounds at `0` (round 5)

| Statement | Lean name | Status |
|---|---|---|
| Dyadic cells `[j2^{-k}, (j+1)2^{-k})`, splitting, disjointness, length `2^{-k}` | `ThomDyadic.cell_split`, `cell_pairwiseDisjoint`, `volume_real_cell` | U |
| **Increment identity** `H_{k+1} − H_k = ∑_I [a log(2a/(a+b)) + b log(2b/(a+b))]`, `a = λ(I₋)`, `b = λ(I₊)` | `dyEnt_succ_sub`, `klTerm_eq` | U |
| **Increment bounds** `0 ≤ H_{k+1} − H_k ≤ D_k = ∑_I (λ(I₋) − λ(I₊))²/λ(I)` (zero-mass terms are `0`) | `dyEnt_succ_sub_nonneg`, `dyEnt_succ_sub_le`, `klTerm_nonneg`, `klTerm_le` | U |
| `H_k ≤ H_0 + ∑_{i<k} D_i`; `H_k` is nondecreasing | `dyEnt_le`, `dyEnt_mono` | U |
| Cells carrying mass more than `M` times their length: `∑_G λ(I) ≤ M·abs(G) + (B+2)/log M` when `H_k ≤ B` | `sum_mass_le` | U |
| **Bounded dyadic entropy ⇒ `λ ≪ dx`**; **summable `D_k` ⇒ `λ ≪ dx`** (finite `λ` carried by `[0,1)`) | `ac_of_dyEnt_bounded`, `ac_of_summable_dyDisc` | C |
| `D_k` is subadditive: `D_k(∑ νᵢ) ≤ ∑ D_k(νᵢ)` (Sedrakyan) | `dyDisc_finset_sum_le` | U |
| `λ = θ_*μ_A`, `θ(E) = arccos(E/4)/π`, is a probability carried by `[0,1)` (uses `μ_A{−4} = 0`) | `ThomDyadicTarget.lam_compl_Ico` | U |
| **Back-transport**: `λ ≪ dx ⇒ μ_A ≪ dE` (`θ` is differentiable on `(−4,4)` and maps null sets to null sets) | `muA_ac_of_lam_ac` | U |
| Dyadic criteria for `μ_A` | `muA_ac_of_dyEnt_bounded`, `muA_ac_of_summable_dyDisc` | C |
| `∫_U F_N dρ ≤ M ρ(U) + (H_N + 1)/log M` | `ThomChebyshev.setIntegral_fejer_le` | U |
| **Bounded Fejér entropy ⇒ uniform integrability of `F_N`** and `μ ≪ dE` | `fejer_uniformlyIntegrable`, `ac_of_fejEnt_bounded` | C |
| `H_N ≤ ‖F_N‖_p^p/(p−1)`: every Fejér `L^p` bound (`p > 1`) gives an entropy bound | `fejEnt_le_of_Lp`, `fejEnt_bounded_of_Lp`, `ThomWeightedL2.fejerEntropyTarget_of_fejerTarget` | U / C |
| **Strictness**: the step profile `v_k = 2^k/k³` on `[2^{-k-1}, 2^{-k})` has convergent entropy series and divergent `L^p` series for **every** `p > 1` | `entropy_strictly_weaker` | U |
| **`WeightedLqTarget 2 ↔ WeightedTarget`** (test `P = ∑ c_n T_n`: `∫P dν = ∑c_n²`, `‖P‖² = ∑c_n²/2`; converse by the `L²` density) | `ThomWeightedL2.summable_of_L2_bound`, `L2_bound_of_summable`, `weightedLqTarget_two_iff` | U |
| **Localization**: `μ_A ≪ dE ⇔ ∀ ε > 0, μ_A abs restricted to {abs E ≥ ε} ≪ dE` | `muA_ac_iff_local` | U |
| Local weighted `L²` bounds on `{abs E ≥ ε}` for each `ε` ⇒ `μ_A ≪ dE` | `muA_ac_of_local_weighted` | C |
| **Transfer of lower bounds**: moment-matching approximants with `c ≤ ν_Q(C)` infinitely often give `c ≤ μ(C)` (`C` compact) | `ThomLowerBound.le_measureReal_of_moments`, `logSqLowerBound_of_approx` | U / C |
| **`μ_A([−h,h]) ≥ c/log²(1/h)` refutes** every `LqTarget q` (`q ≥ 1`), every `FejerTarget p` (`p > 1`) and `PrincipalTarget` | `not_lqTarget_of_logSq`, `not_fejerTarget_of_logSq`, `not_principalTarget_of_logSq` | C |
| `LogSqLowerBound` itself | `ThomLowerBound.LogSqLowerBound` | **P**, numerically true |
| `FejerEntropyTarget`, summable `D_k(λ)` | `ThomWeightedL2.FejerEntropyTarget` | **P**, open |

**Why flux-wise estimates cannot suffice.** `D_k` and `H_k` are convex under mixtures
(`dyDisc_finset_sum_le` for `D_k`). Since `μ_A = ∫_0^1 N_α dα`, any bound of the form
`D_k(μ_A) ≤ ∫ D_k(N_α) dα` with summable right side would need `∑_k D_k(N_α) < ∞` for almost
every `α`, i.e. `N_α ≪ dE`. For the critical almost Mathieu operator the density of states is
singular for every irrational `α` (zero-measure spectrum; Last, Avila–Krikorian), so such
bounds fail. Absolute continuity of `μ_A`, if true, must come from **cancellation across
fluxes**, not from the regularity of individual `N_α`. This is a mathematical remark, not a
Lean theorem (the measures `N_α` are not formalized).

**Transfer audit (Task 1).** The rational-flux averages `ν_Q` agree with `μ_A` in degree
`< N_Q = 2⌈2√Q⌉` only; moments of degree `n` certify nothing below scale `≈ 12/n`. With the
121 exact moments, the Chebyshev–Markov–Stieltjes inequalities give the rigorous bound
`μ_A((−0.196, 0.196)) ≥ 0.0696` (`numerics/gauss_lower.py`), which is far from the scales
`h ≤ 2⁻⁴` of the log² law. Certifying `h = 2⁻¹⁸` that way would need moments of degree
`≈ 3·10⁶`. The weak limit `ν_Q → μ_A` is the correct direction for lower bounds on compact sets
(`le_measureReal_of_moments`), so a proof of `ν_Q([−h,h]) ≥ c/log²(1/h)` for infinitely many `Q`
at each fixed `h` (equivalently, of the zero-Landau-level estimate below for rational fluxes)
would prove `LogSqLowerBound`. The missing estimate is:

> **(ZL)** there are `c₀, δ₀ > 0` such that for every flux `α = 1/2 + δ`, `0 < abs δ < δ₀`, the
> Harper density of states satisfies `N_α([−e^{−c₀/abs δ}, e^{−c₀/abs δ}]) ≥ abs δ`.

(ZL) gives `μ_A([−h,h]) ≥ ∫_{abs δ ≤ c₀/log(1/h)} abs δ dδ = (c₀/log(1/h))²`. Semiclassical
analysis near flux `1/2` (Helffer–Sjöstrand) and the gap labels `α`, `1 − α` around the zero
band are the natural tools; neither is formalized here.

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
