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
  bounds on compact sets from moment-matching approximants to `μ_A`; `not_lqTarget_of_logSq`
  shows that `μ_A([−h,h]) ≥ c/log²(1/h)` refutes every `LqTarget q`, every Fejér `L^p` target
  and `PrincipalTarget`.
* **The logarithmic lower bound at `0` (round 6, unconditional).**
  `ThomZeroLevel.logSqLowerBound : LogSqLowerBound`, i.e. `μ_A([−h,h]) ≥ c/log²(1/h)` for
  `0 < h < 1/3` with the explicit `c = 1/165888000`. The proof uses explicit zero-energy
  quasimodes of the chiral (zero-diagonal) Jacobi operator at flux `1/2 + δ`, embedded in the
  finite quotients `H₃(ℤ/N)`, and a Riemann sum over fluxes (§9). Consequently
  `ThomZeroLevel.not_principalTarget`, `not_lqTarget` (every `q ≥ 1`) and `not_fejerTarget`
  (every `p > 1`): **these targets are false.** Absolute continuity of `μ_A` and the weighted
  targets are not affected.
* **No `L log² L` density (round 7, unconditional).** `ThomZeroLevel.not_integrable_mul_log_sq`:
  if `μ_A = f·ρ` then `∫ f log²(1+f) dρ = ∞`. Round 7 also proves simplicity of the Dirichlet
  eigenvalues (`ThomDirichlet.eig_proportional`) and the Jensen multiplicity inequality behind the
  coarea entropy bound (`ThomDirichlet.sum_mul_log_sum_le`); see §10.
* **The logarithmic upper bound at `0` (round 8, unconditional).**
  `ThomUpper.logUpperBound_explicit`: `μ_A([−h,h]) ≤ 17284 (1 + log log(1/h))³ / log²(1/h)`
  for `0 < h ≤ e^{−121}`. With `logSqLowerBound`, the mass at `0` is `log^{−2}(1/h)` up to the
  factor `(log log)³`. Consequently `ThomUpper.logMoment_finite_iff`: for `s > 0`,
  `∫_{|E|<1} log^s(1/|E|) dμ_A < ∞ ⟺ s < 2`. Absolute continuity is not assumed (§11).
* **Dirichlet strip model (round 8).** `ThomStrip.stripMoment_formula`: the grid-averaged
  Dirichlet model `σ_{W,N}` satisfies `W∫Eᵏ dσ_{W,N} = W τ(Aᵏ) − b_k` exactly, with
  `b_k = ∑ width(w)` over zero-area closed walks (`k ≤ 2W`, `(k+1)² ≤ N`). Hence the two-scale
  identity `∫P dμ_A = 2∫P dσ_{2W} − ∫P dσ_W` (`deg P ≤ 2W`), the Fejér domination
  `0 ≤ F_n^{μ_A} ≤ 2F_n^{σ_{2W}}` and `H_n(μ_A) ≤ 2H_n(σ_{2W}) + 2 log 2 + 1` (§11).
* **Conditional absolute continuity.** Each open target below implies `μ_A ≪ Lebesgue`
  (`ThomConclusions.muA_ac_of_principal`, `ThomNoAtoms.muA_ac_of_weightedTarget`,
  `ThomConclusions.muA_ac_of_LqTarget`, `ThomFejer.muA_ac_of_fejerTarget`,
  `ThomFejer.muA_ac_of_weightedLqTarget`).

## Open targets (named as `def … : Prop`, never assumed)

| Target | Lean name | Consequence proved in Lean | Numerical status |
|---|---|---|---|
| `∑ τ(T_n(A/4))² < ∞` | `ThomBridge.PrincipalTarget` | `μ_A ≪ dE` with `L²(arcsine)` density (equivalence) | **false** (Lean: `ThomZeroLevel.not_principalTarget`) |
| `∑ (c_{n-2}+2c_n+c_{n+2})² < ∞` | `ThomBridge.WeightedTarget` | **alone** gives `μ_A ≪ dE` (`ThomNoAtoms.muA_ac_of_weightedTarget`); **equivalent** to `WeightedLqTarget 2` (`ThomWeightedL2.weightedLqTarget_two_iff`) | inconclusive: binned weighted `L²` energy converged in `Q` up to `2⁹` angular cells, growing `≈ 0.003` per level there |
| `sup_N ∫ abs(F_N)^p dρ < ∞`, `p > 1` (Fejér densities) | `ThomFejer.FejerTarget` | `μ_A ≪ dE`; `p = 3/2` gives `LqTarget 3` | **false** for every `p > 1` (Lean: `ThomZeroLevel.not_fejerTarget`) |
| `abs τ((A/4)² P(A/4)) ≤ K‖P(·/4)‖_{L^q(arcsine)}` | `ThomFejer.WeightedLqTarget` | with `muA_no_atoms`, `μ_A ≪ dE`; `q = 2` is `WeightedTarget` | compatible with the exact flux averages for `q ≥ 2` |
| `abs τ(P(A/4)) ≤ K‖P(·/4)‖_{L^q(arcsine)}`, some `q < ∞` | `ThomConclusions.LqTarget` | `μ_A ≪ dE`; forces `μ_A([−h,h]) = O(h^{1/q})` (`ThomFejer.muA_le_of_lqTarget`); refuted by `LogSqLowerBound` (`ThomLowerBound.not_lqTarget_of_logSq`) | **false** for every `q ≥ 1` (Lean: `ThomZeroLevel.not_lqTarget`) |
| `sup_N ∫ F_N log F_N dρ < ∞` (Fejér entropy) | `ThomWeightedL2.FejerEntropyTarget` | `μ_A ≪ dE` (`muA_ac_of_fejerEntropyTarget`); implied by every `FejerTarget p`; implied by a uniform bound on the strip entropies `H_n(σ_{2n+2})` (`ThomStrip.fejerEntropyTarget_of_strip`, round 8) | **recommended**: not contradicted by the proved lower bound (a profile with `μ([−h,h]) ≍ 1/log²(1/h)` can have finite entropy); increments decay by `≈ 0.72` per doubling of `N` up to `N = 512` |
| `∑_k D_k(λ) < ∞`, `λ = θ_*μ_A` (dyadic discrepancies) | `Summable (ThomDyadic.dyDisc ThomDyadicTarget.lam)` | `μ_A ≪ dE` (`ThomDyadicTarget.muA_ac_of_summable_dyDisc`) | undecided: `D_k ≈ 0.03–0.04` at the levels resolved by `Q ≤ 601` |
| `μ_A([−h,h]) ≥ c/log²(1/h)` (a lower bound, not a regularity target) | `ThomLowerBound.LogSqLowerBound` | refutes `LqTarget q` (all `q ≥ 1`), `FejerTarget p` (all `p > 1`), `PrincipalTarget` | **proved** (`ThomZeroLevel.logSqLowerBound`, `c = 1/165888000`); numerically `≈ 0.47/log²(1/h)` |

`ThomConclusions.NoAtomTarget` (`μ_A{0} = 0`) is no longer open: it is proved as
`ThomNoAtoms.noAtomTarget`.

Rounds 2–5 found these three targets numerically false: the exact rational-flux averages
`ν_Q` give `ν_Q([−h,h]) · log²(1/h) ≈ 0.47` for `2⁻¹⁸ ≤ h ≤ 2⁻⁴`, from the zero Landau level
near flux `1/2`. Round 6 turns this into a proof (§9). The proved constant `c = 1/165888000` is
far from the numerical `0.47`; the constants were not optimized. The lower bound says nothing
about a density profile at `0`: no asymptotic for the density of `μ_A` near `0` is claimed.

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
scripts/check_axioms.sh audit.txt  # sorry / axiom scan + #print axioms on 304 theorems
scripts/module_status.sh           # per-module build table
```

### Status of each module

Last local verification (round 8): full `lake build` succeeds (7684 jobs),
304 theorems audited, all depending only on `propext`, `Classical.choice`, `Quot.sound`.
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
| `ThomLean.ZeroLevel.Count` | `ThomLean/ZeroLevel/Count.lean` | ✅ passing | 13 | 9 |
| `ThomLean.ZeroLevel.Chain` | `ThomLean/ZeroLevel/Chain.lean` | ✅ passing | 4 | 3 |
| `ThomLean.ZeroLevel.Quasimode` | `ThomLean/ZeroLevel/Quasimode.lean` | ✅ passing | 14 | 12 |
| `ThomLean.ZeroLevel.Trig` | `ThomLean/ZeroLevel/Trig.lean` | ✅ passing | 7 | 7 |
| `ThomLean.ZeroLevel.Family` | `ThomLean/ZeroLevel/Family.lean` | ✅ passing | 12 | 11 |
| `ThomLean.ZeroLevel.LogSq` | `ThomLean/ZeroLevel/LogSq.lean` | ✅ passing | 12 | 11 |
| `ThomLean.ZeroLevel.Orlicz` | `ThomLean/ZeroLevel/Orlicz.lean` | ✅ passing | 1 | 1 |
| `ThomLean.Dirichlet.Coarea` | `ThomLean/Dirichlet/Coarea.lean` | ✅ passing | 1 | 1 |
| `ThomLean.Dirichlet.Simple` | `ThomLean/Dirichlet/Simple.lean` | ✅ passing | 2 | 2 |
| `ThomLean.UpperBound.Moment` | `ThomLean/UpperBound/Moment.lean` | ✅ passing | 11 | 4 |
| `ThomLean.UpperBound.Maximal` | `ThomLean/UpperBound/Maximal.lean` | ✅ passing | 7 | 3 |
| `ThomLean.UpperBound.Bad` | `ThomLean/UpperBound/Bad.lean` | ✅ passing | 8 | 1 |
| `ThomLean.UpperBound.Gap` | `ThomLean/UpperBound/Gap.lean` | ✅ passing | 3 | 3 |
| `ThomLean.UpperBound.Decomp` | `ThomLean/UpperBound/Decomp.lean` | ✅ passing | 22 | 7 |
| `ThomLean.UpperBound.Upper` | `ThomLean/UpperBound/Upper.lean` | ✅ passing | 13 | 6 |
| `ThomLean.UpperBound.LogMoment` | `ThomLean/UpperBound/LogMoment.lean` | ✅ passing | 12 | 5 |
| `ThomLean.Dirichlet.Strip` | `ThomLean/Dirichlet/Strip.lean` | ✅ passing | 45 | 23 |

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
| `ThomLean/ZeroLevel/Count.lean` | eigenvalue counting from orthogonal complex quasimodes, `σ_N([−h,h]) = #{abs λ ≤ h}/N³` |
| `ThomLean/ZeroLevel/Chain.lean` | chain vectors in `H₃(ℤ/N)`: intertwining with the chiral Jacobi operator, orthogonality |
| `ThomLean/ZeroLevel/Quasimode.lean` | explicit quasimode, boundary residual identity, `‖Hξ‖² ≤ 16(4/9)^m‖ξ‖²` |
| `ThomLean/ZeroLevel/Trig.lean` | bond moduli `2abs(cos)`, ratio bounds near flux `1/2` |
| `ThomLean/ZeroLevel/Family.lean` | the quasimode family, disjoint bands, eigenvalue count, window counts |
| `ThomLean/ZeroLevel/LogSq.lean` | Riemann sum, transfer, `logSqLowerBound`, refutations, Task 2 in exponential form |
| `ThomLean/ZeroLevel/Orlicz.lean` | no `L log² L` density (round 7) |
| `ThomLean/Dirichlet/Coarea.lean`, `Simple.lean` | Jensen multiplicity inequality, simplicity of Dirichlet eigenvalues (round 7) |
| `ThomLean/UpperBound/Moment.lean` | pairwise independence of the bond logarithms, `∑ log²‖1+ψ‖ ≤ 5N` |
| `ThomLean/UpperBound/Maximal.lean` | dyadic Rademacher–Menshov maximal inequality, counting form |
| `ThomLean/UpperBound/Bad.lean` | bad blocks, centering, `#bad · T² ≤ 320(ℓ+1)²2^ℓN²` |
| `ThomLean/UpperBound/Gap.lean` | chiral block gap `‖η‖² ≤ 4m²e^T‖Jη‖²` |
| `ThomLean/UpperBound/Decomp.lean` | adaptive dyadic decomposition, vanishing sets, coercivity, counts |
| `ThomLean/UpperBound/Upper.lean` | codimension min–max, `σ_N([−h,h])` bound, `logUpperBound_explicit` |
| `ThomLean/UpperBound/LogMoment.lean` | `∫ log^s(1/abs E) dμ_A < ∞ ⟺ s < 2` |
| `ThomLean/Dirichlet/Strip.lean` | strip graph, exact Dirichlet moments, two-scale and Fejér identities, entropy reduction |
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
| `LogSqLowerBound` itself | `ThomLowerBound.LogSqLowerBound` | **U** since round 6: `ThomZeroLevel.logSqLowerBound` (§9) |
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
`≈ 3·10⁶`. *Correction (round 6).* Weak convergence `ν_Q → μ_A` (which holds, since the moments
converge and `μ_A` is determined by its moments) gives `ν_Q(I) → μ_A(I)` for every interval `I`
with `μ_A(∂I) = 0`, and `μ_A` is atomless (`muA_no_atoms`), so interval masses converge in
**both** directions. The Lean theorem `le_measureReal_of_moments` proves the lower-bound
direction on compact sets, which is the one `LogSqLowerBound` needs. So a proof of `ν_Q([−h,h]) ≥ c/log²(1/h)` for infinitely many `Q`
at each fixed `h` (equivalently, of the zero-Landau-level estimate below for rational fluxes)
would prove `LogSqLowerBound`. The missing estimate is:

> **(ZL)** there are `c₀, δ₀ > 0` such that for every flux `α = 1/2 + δ`, `0 < abs δ < δ₀`, the
> Harper density of states satisfies `N_α([−e^{−c₀/abs δ}, e^{−c₀/abs δ}]) ≥ abs δ`.

(ZL) gives `μ_A([−h,h]) ≥ ∫_{abs δ ≤ c₀/log(1/h)} abs δ dδ = (c₀/log(1/h))²`. Round 6 proves a
finite-volume form of (ZL) with explicit quasimodes and closes the argument (§9).

### 9. The logarithmic lower bound at `0`, unconditionally (round 6, `ThomLean/ZeroLevel/…`)

**Theorem** (`ThomZeroLevel.logSqLowerBound : LogSqLowerBound`). For `0 < h < 1/3`,
`μ_A([−h, h]) ≥ c / log² h` with `c = 1/165888000`.

**Corollaries** (U): `ThomZeroLevel.not_principalTarget`, `not_lqTarget (hq : 1 ≤ q)`,
`not_fejerTarget (hp : 1 < p)`. `PrincipalTarget`, every `LqTarget q` (`q ≥ 1`) and every
`FejerTarget p` (`p > 1`) are false. `WeightedTarget`, `WeightedLqTarget q`,
`FejerEntropyTarget`, the dyadic target and absolute continuity of `μ_A` are untouched: the
bound is compatible with all of them, and it gives no density asymptotic at `0`.

The proof avoids infinite-dimensional spectral theory: it runs in the finite quotients
`H₃(ℤ/N)` already used to construct `μ_A`, as allowed by the round-6 plan.

| Step | Statement | Lean name | Status |
|---|---|---|---|
| 1 | **Finite chiral model.** For `N` odd, `ψ(x) = e^{2πix/N}`, `F^{p,t}_ξ(a,b,c) = ξ(−a−b) ψ(pc − pab + ta − p·a(a−1)/2)` satisfies `A F^{p,t}_ξ = F^{p,t}_{Hξ}`, where `(Hξ)(l) = c(l−1)ξ(l−1) + conj(c(l))ξ(l+1)`, `c(n) = 1 + ψ(t + p(n+1))`, `abs c(n) = 2 abs cos(π(t+p(n+1))/N)` | `ThomZeroLevel.cAdj_Fv`, `two_mul_half` | U |
| 2 | **Orthogonality.** `⟨F^{p,t}_ξ, F^{p',t'}_η⟩ = N² [p=p'] [t=t'] ⟨ξ,η⟩` (character sums over `c` and `a`) | `ip_Fv`, `nrm_Fv` | U |
| 3 | **Counting lemma.** Pairwise orthogonal complex vectors `F_i` with `A F_i` pairwise orthogonal and `‖AF_i‖² ≤ ε²‖F_i‖²`, `ε² < h²`, force `#{i} ≤ #{j : abs λ_j ≤ h}` (Parseval in the real eigenbasis plus a kernel-dimension argument) | `card_le_of_quasimodes`, `parseval`, `coef_cAdj`, `nrm_sum` | U |
| 4 | **Spectral mass = eigenvalue count.** `σ_N([−h,h]) · N³ = #{j : abs λ_j ≤ h}` (vertex transitivity) | `quotMeasure_real_Icc`, `specMeasure_real` | U |
| 5 | **Explicit quasimode.** `ξ = ∑_{j≤M} u_j δ_{s+2j}`, `u_0 = 1`, `u_{j+1} = −c_j u_j / conj(d_j)` (`c_j = c(s+2j)`, `d_j = c(s+2j+1)`). **Only the two exterior boundary sites carry residuals**: `Hξ = conj(c(s−1)) u_0 δ_{s−1} + c_M u_M δ_{s+2M+1}` | `chainH_qmXi` | U |
| 6 | Growth `abs u_m ≥ (3/2)^m abs u_0` and decay `abs u_M ≤ (2/3)^m abs u_{M−m}` from the ratio bounds, hence `abs u_0², abs u_M² ≤ (4/9)^m ‖ξ‖²` and `‖Hξ‖² ≤ 16 (4/9)^m ‖ξ‖²`, `‖ξ‖² ≥ 1` | `qmU_growth`, `qmU_decay`, `qm_bound` | U |
| 7 | **Trigonometry near half flux.** With `δ = val p/N − 1/2`, `θ = val(t+p(s+1))/N`: `abs c_j² = 4cos²(π(θ+2jδ))`, `abs d_j² = 4sin²(π(θ+(2j+1)δ))`. For `θ ∈ [1/16,1/8]`, `0 < δ ≤ 1/256`, `2mδ ≤ 1/32`, `2Mδ ≤ 11/32`, `9/32 ≤ 2(M−m+1)δ`: ratios `≥ 3/2` on the first `m` steps (phases in `[1/16, 5/32]`), `≤ 2/3` on the last `m` steps (phases in `[11/32 − 1/128, 15/32]`), all `d_j ≠ 0` | `normSq_ce`, `normSq_co`, `trig_first`, `trig_last`, `qm_of_phase` | U |
| 7′ | **Task 2 as requested.** `m = ⌊1/(64δ)⌋`, `M = ⌊5/(32δ)⌋`, `0 < δ ≤ 2⁻¹⁰`: `‖Hξ‖² ≤ (1/4) e^{−2b/δ} ‖ξ‖²`, i.e. `‖Hξ‖ ≤ (1/2) e^{−b/δ} ‖ξ‖`, with **`b = 1/400`, `δ₀ = 2⁻¹⁰`** | `qm_exp_bound` | U |
| 8 | **The family.** `M = 11m`, `D = 2M+3`, chains at `s_k = 1 + kD` in disjoint bands `[kD, (k+1)D)`, `k < N/D`; fluxes `val p/N ∈ [1/2 + 9/(640m), 1/2 + 1/(64m)]`; phases `θ ∈ [1/16, 1/8]`. All members are mutually orthogonal (different `(p,t)` by step 2, same `(p,t)` by disjoint bands), and so are their images | `good`, `fam`, `qmXi_band`, `chainH_band`, `card_good_le` | U |
| 9 | **Riemann sum over fluxes.** `#family = #P · ⌊N/D⌋ · #T` (the phase condition is a translate in `t`), with `#P ≥ N/(640m) − 1`, `#T ≥ N/16 − 1`; so `σ_N([−h,h]) ≥ 1/(2048000 m²)` for all large odd `N` once `16(4/9)^m < h²` | `card_good`, `card_window`, `nuQ_lower`, `nuQ_lower_explicit` | U |
| 10 | `m = ⌈5 + 3 log(1/h)⌉` gives `16(4/9)^m < h²` and `m ≤ 9 log(1/h)` for `h < 1/3` | `eps_lt`, `one_lt_log_three` | U |
| 11 | **Transfer.** `σ_N` matches `μ_A` on every polynomial of degree `d` once `N > (d+1)²` (`nuQ_moments`); `logSqLowerBound_of_approx` (round 5) passes the bound to `μ_A` | `nuQ_moments`, `logSqLowerBound` | U |

**Relation to the round-6 plan.** The plan's chiral representation on `ℓ²(ℤ)` and its
phase/flux average (Jitomirskaya–Krasovsky, arXiv:1909.04429) are replaced by their exact
finite-volume counterpart: the chain operator `H_{p,t}` on `ℤ/N` *is* the zero-diagonal Jacobi
operator `(Ju)_n = a_{n−1}u_{n−1} + a_n u_{n+1}` at flux `p/N` and phase `t/N` up to a gauge
(`abs c(n) = 2 abs cos(π(θ + nα))`), and the quasimode lives in a band of length `< N`, so it is
the same finitely supported vector as on `ℤ`. The phase average over `θ ∈ [1/16, 1/8]` becomes
the count over `t`, the flux integral over `δ` becomes the sum over `p`, and moment matching
is the exact matching of the quotient measures (round 3) instead of a word expansion. The
constants (`b = 1/400` instead of `1/384`, the factor `16` instead of `8`) differ from the plan
only because the boundary residuals were bounded with `abs(z+w)² ≤ 2abs z² + 2abs w²`.

**Task 3 note.** The plan's projection estimate (`⟨Pv,v⟩ ≥ 3/4`, summed over the sites of
the chain) is replaced by the counting lemma of step 3, which needs no projection and gives one
eigenvalue in `[−h,h]` per quasimode.

#### Documentation corrections (round 6)

* **Weak convergence and interval masses.** Earlier text said that weak convergence is "the
  correct direction" for lower bounds on compact sets. That is true but incomplete: since the
  approximants converge weakly to `μ_A` and `μ_A` is atomless (`muA_no_atoms`), every interval
  is a `μ_A`-continuity set and `ν_Q(I) → μ_A(I)` for **every** interval. Lower *and* upper
  bounds on interval masses pass to the limit. Lean proves the lower-bound direction on compact
  sets (`le_measureReal_of_moments`), which is the one used.
* **Finite-`Q` entropies are not upper bounds.** Round 5 called the unconverged finite-`Q`
  dyadic and Fejér entropies "upper bounds on the limit". They are not automatically: for each
  fixed level, `H_k(ν_Q) → H_k(μ_A)` (cell boundaries are null), but at fixed `Q` the value can
  lie on either side of the limit. The observed decrease in `Q` is evidence only.
* **No density asymptotic.** `LogSqLowerBound` is a lower bound on interval masses. It does not
  give the behaviour of a density of `μ_A` at `0` (which is not even known to exist).

#### Task 5: cross-flux averaging (evidence, no new theorem)

`numerics/cross_flux.py` uses the decomposition of steps 1–2: for `N` prime and `p ≠ 0` the
spectrum of `H_{p,t}` does not depend on `t`, so `σ_N = N⁻¹ ∑_p ν_p` is an explicit flux
average of chain spectra. The exact moments are reproduced (`k ≤ 12`).

* **Flux-window localization (exact inequality).** Fejér smoothing is linear and `x log x` and
  `x²` are convex, so for any partition of the fluxes into windows `W_b`,
  `Ent_K(σ) ≤ ∑_b w_b Ent_K(σ_b)` and `W_K(σ) ≤ ∑_b w_b W_K(σ_b)` (`σ_b` = average over `W_b`,
  `W_K` = weighted Fejér energy of `(E/4)²σ`). The same holds for `μ_A = ∫ N_α dα` with flux
  windows. Window width `1/N` is the flux-wise bound (which fails, §8); width `1` is the target
  itself.
* **Numbers** (`out_cross_flux_401.txt`, `out_cross_flux_1009.txt`; `K` up to `128`; only
  degrees `≲ 2√N` are exact moments of `μ_A`, so large-`K` rows describe `σ_N`). The full
  average has `Ent_K` increments per doubling of `K` of `0.096, 0.076, 0.055, 0.038` (ratio
  `≈ 0.7`, as in round 5). With fixed windows of width `1/4` the increments are `0.13, 0.13,
  0.10, 0.07`; with width `1/16` they are `0.16, 0.20, 0.19, 0.15`; flux-wise they grow
  (`0.16, 0.23, 0.28, 0.32`). For the weighted energy `W_K` (`N = 1009`, `K ≤ 128`) the full
  average grows by `0.024, 0.021, 0.016, 0.010`, windows of width `1/4` by `0.035, 0.040,
  0.039, 0.028`, and the flux-wise bound by `0.044, 0.077, 0.126, 0.204`. So the window inequality is useful only with
  windows of **non-shrinking** width; at these sizes no window of width `o(1)` keeps the bound
  flat.
* **Where the mass at `0` comes from.** The windows `abs(α − 1/2) ≤ 0.05` (10% of the fluxes)
  carry 6% of `σ_N([−1/8,1/8])` but 37% of `σ_N([−2⁻¹⁰, 2⁻¹⁰])` (`N = 1009`), and the windows
  `abs(α − a/4) ≤ 0.02` (`a = 1, 3`, 8% of the fluxes) carry 15%. `σ_N([−h,h])·log²(1/h)`
  stays near `0.50` for `2⁻⁶ ≤ h ≤ 2⁻¹⁰`. This is consistent with even-denominator fluxes
  (`q = 2, 4, …`, where `0` is in the spectrum) driving the concentration at `0`.

**Status of Task 5.** `WeightedTarget` and `FejerEntropyTarget` remain open. The window
inequality is the natural reduction: it would suffice to bound `Ent_K` (or `W_K`) of the flux
averages over a fixed finite family of flux windows, uniformly in `K`. Near the
even-denominator fluxes this needs the zero-level analysis of steps 5–9 with **upper** bounds
on the number of near-zero eigenvalues, which is not done here.

### 10. Orlicz obstruction and the continuous-flux Dirichlet model (round 7)

Status: **[L]** proved in Lean (no `sorry`, standard axioms), **[P]** paper proof, not formalized,
**[N]** numerical evidence only.

#### 10.1 The `f log²(1+f)` obstruction **[L]**

`ThomZeroLevel.not_integrable_mul_log_sq` (`ThomLean/ZeroLevel/Orlicz.lean`): if
`μ_A = f·ρ` (`ρ` the arcsine law, `f ≥ 0` measurable), then `f log²(1+f) ∉ L¹(ρ)`.

The proof follows the suggested split. Take `T = n+3`, `h = T⁻²`. On `[−h,h]` one has
`f ≤ T + 1_{f>T}·f log²(1+f)/log² T`. The first part gives at most `T·ρ([−h,h]) ≲ T·h = 1/T`. The
second is `≤ a_n / log² T`, where `a_n = ∫_{f>n+3} f log²(1+f) dρ → 0` by dominated convergence
if the function were integrable. Then `logSqLowerBound` gives
`c/(4 log² T) ≤ μ_A([−h,h]) ≤ C/T + a_n/log² T`. Multiplying by `log² T` gives
`c/4 ≤ C log² T/T + a_n → 0`, a contradiction. This uses no hypothesis beyond the density
assumption itself, so it says: **if `μ_A` is absolutely continuous, its density is not in the
Orlicz class `L log² L`.** It is consistent with `f ∈ L log L`: a density `≍ 1/(|E| log³(1/|E|))`
at `0` has finite entropy.

#### 10.2 Regularized `log²` energies diverge at least like `log log N` **[P]**

Let `f_n` be the cell averages of `μ_A` on the dyadic partition of `[−4,4]` at mesh `2⁻ⁿ` (in
`E`), and `Φ_n = ∫ φ(f_n) dρ` with `φ(x) = x log²(1+x)`. Note that
`φ''(x) = (2(2+x)log(1+x) + 2x)/(1+x)² > 0`.

**Claim.** `Φ_n ≥ c₁ log n − C₁`. With `N = 2ⁿ`, this is `≳ log log N`.

*Proof.*
1. Let `A_j = {2^{−j−1} < |E| ≤ 2^{−j}}` for `j < n`, let `C_n = [−2⁻ⁿ, 2⁻ⁿ]`, and set
   `m_j = μ_A(A_j)`, `T_j = μ_A([−2^{−j}, 2^{−j}])`. Each set is a union of cells, and
   `ρ(A_j) ≍ 2^{−j}`.
2. Jensen on each set gives `∫_{A_j} φ(f_n) dρ ≥ m_j log²(1 + m_j/ρ(A_j))`.
3. If `m_j ≥ 2^{−j/2}`, this is `≥ m_j (j log 2/2 − C)²`. The indices with `m_j < 2^{−j/2}`
   lose at most `Σ_j 2^{−j/2} j² < ∞`.
4. The central cell contributes `≥ T_n (n log 2 − log(1/T_n) − C)²`. Here
   `log(1/T_n) = O(log n)`, because `T_n ≥ c/(n log 2)²`.
5. Abel summation then gives
   `Φ_n ≥ (log²2/4)(1 − o(1)) Σ_{j<n} T_j (2j − 1) − C`.
6. Inserting `T_j ≥ c/(j log 2)²` gives the claim.

The same lower bound holds for the Fejér `log²` energies, by `F_N(θ) ≥ c N μ̃(θ ± 1/N)` (sketch).
Only a lower bound is proved. Whether `log log N` is the true rate is open.

#### 10.3 The continuous-flux Dirichlet model and its moments **[P]**, **[N]**

`H_L(α,θ)` is the `L×L` Jacobi matrix with off-diagonal entries `1` and diagonal
`d_j = 2cos(2π(θ + jα))`, `1 ≤ j ≤ L`. Set
`m_k(L) = ∫₀¹∫₀¹ L⁻¹ tr H_L(α,θ)ᵏ dα dθ`, and let `σ_L` be the averaged normalized counting
measure.

**Proposition.** For `L ≥ ⌊k/2⌋`,
`m_k(L) = τ(Aᵏ) − b_k/L`, with a constant `0 ≤ b_k ≤ k·τ(Aᵏ)`. In particular
`|m_k(L) − τ(Aᵏ)| ≤ k·4ᵏ/L`, and `σ_L → μ_A` weakly. Since `μ_A` has no atoms, the
distribution functions converge uniformly.

*Proof.*
1. Write `d_m = w z^m + w̄ z^{−m}`, with `w = e^{2πiθ}` and `z = e^{2πiα}`.
2. Expand `(H_Lᵏ)_{jj}` as a sum over paths `j → j` of `k` steps, each in `{−1, 0, +1}`, that
   stay in `[1,L]`. A `0`-step at site `m` carries `w^{ε} z^{εm}`, with `ε = ±1`.
3. Averaging over `θ` kills every term with `Σε ≠ 0`, and averaging over `α` kills every term
   with `Σ ε m ≠ 0`.
4. Read `±1` steps as horizontal moves and `0`-steps as vertical moves by `ε`. The surviving
   terms are then exactly the closed walks in `ℤ²` of length `k` with zero algebraic area, which
   stay in the strip `1 ≤ x ≤ L`.
5. Without the strip these walks number `τ(Aᵏ)` ("moments are walk counts", rounds 2–3).
6. A closed walk has horizontal range at most `⌊k/2⌋`. So for `L ≥ ⌊k/2⌋` no walk leaves through
   both walls, and the deficit `b_k = 2 Σ_{j ≥ 1} #{zero-area walks from x = j that leave x ≥ 1}` does
   not depend on `L`. Only `j ≤ ⌊k/2⌋` contribute, so `b_k ≤ k τ(Aᵏ)`.
7. Supports lie in `[−4,4]`, so moment convergence gives weak convergence (Weierstrass). The
   distribution functions then converge uniformly, by Pólya's theorem and `ThomNoAtoms.muA_no_atoms`.

*Check* (`numerics/dirichlet_moments.py`, exact quadrature). For `L = 20, 40, 80`:
`L(τ(Aᵏ) − m_k(L)) = 2, 26, 296, 3386, 40152` for `k = 2, …, 10`, independent of `L`, exactly as
predicted (`out_dirichlet_moments.txt`).

#### 10.4 Simplicity, analytic branches and the top Laurent coefficient

* **[L]** `ThomDirichlet.eig_proportional`, `eig_eq_zero_of_first` (`Dirichlet/Simple.lean`).
  For any real diagonal, two solutions of the Dirichlet recursion at the same `E` satisfy
  `u₁ v_j = v₁ u_j`, and an eigenvector has `u₁ ≠ 0`. Hence **every eigenvalue of `H_L(α,θ)` is
  simple, for all `(α,θ)`**.
* **[P]** Branches and derivatives.
  - The ordered eigenvalues `E_1 < … < E_L` are simple roots of `det(E − H_L)`, which is
    real-analytic in `(α, θ, E)`. By the implicit function theorem they are real-analytic on the
    whole torus.
  - Hellmann–Feynman gives `∂_α E_k = ⟨u_k, ∂_α H u_k⟩ = −4π Σ_j j sin(2π(θ+jα)) u_k(j)²`, and the
    same without the factor `j` for `∂_θ`.
* **[P]** Top coefficient.
  - Expand `D(z) = det(E − H_L)` over matchings of adjacent pairs:
    `D = Σ_{matchings} (−1)^{#pairs} Π_{j unmatched}(E − d_j)`.
  - The `z`-degree of a term is at most `Σ_{j unmatched} j`. This equals `L(L+1)/2` only for the
    empty matching with the `−w z^j` part chosen at every `j`. So the coefficient of
    `z^{L(L+1)/2}` is `(−w)^L ≠ 0`, and symmetrically that of `z^{−L(L+1)/2}` is `(−w̄)^L`.
  - Hence for every `(θ, E)`, `z^{L(L+1)/2}D` is a polynomial of exact degree `L(L+1)` with
    nonzero constant term. Consequently:
    * `M_L(θ,E) ≤ L(L+1)`;
    * no branch `E_k(·, θ)` is constant on an interval;
    * `{α : ∂_α E_k = 0}` is finite for each `k, θ`.

#### 10.5 Coarea density and the entropy inequality with actual multiplicities

* **[L]** `ThomDirichlet.sum_mul_log_sum_le` (`Dirichlet/Coarea.lean`). For `a_i ≥ 0` on a
  finite set of size `M`: `(Σ a_i) log(Σ a_i) ≤ Σ a_i log(M a_i)`. This is Jensen for `x log x`.
* **[P]** Let `g_{L,θ}` be the density of `L⁻¹ Σ_k (E_k(·,θ))_* dα`. By §10.4 and the 1-d change
  of variables, `g_{L,θ}(E) = L⁻¹ Σ_{(k,α): E_k(α,θ)=E} |∂_α E_k|⁻¹`, a sum of exactly
  `M_L(θ,E)` terms (simplicity: one `k` per `α`). The lemma with `a_i = 1/(L|∂_α E_k|)`, followed
  by the change of variables back, gives
  `∫ g_{L,θ} log g_{L,θ} dE ≤ R_L(θ) := L⁻¹ Σ_k ∫₀¹ log(M_L(θ,E_k)/(L|∂_α E_k|)) dα`.
  More precisely, the gap is exact:
  `R_L(θ) − ∫ g log g = ∫ g(E) (log M_L(θ,E) − H(p_E)) dE ≥ 0`. Here `p_E` is the distribution
  of the `M` preimage weights and `H` its Shannon entropy.
* **[P]** After the `θ` average, `ḡ_L = ∫ g_{L,θ} dθ` is the density of `σ_L`, and by
  convexity `∫ ḡ_L log ḡ_L ≤ ∫ R_L(θ) dθ`. So `sup_L ∫ R_L dθ < ∞` would make `(ḡ_L)` uniformly
  integrable, and with §10.3 it would give `μ_A ≪ dE`. **This bound is not proved, and the
  numerics below suggest it fails.**

#### 10.6 Numerics (Task 5) **[N]**

Script: `numerics/dirichlet.py` and `dirichlet_joint.py`, Monte Carlo, `M_L` counted by Sturm
sequences on an `α`-grid of `6L²` points; for `L = 256`, `3L²` points and 200 samples. Output in
`out_dirichlet.txt`. Monte Carlo error on `R_L` is about `±0.1`.

| `L` | median `max(|∂θE|,|∂αE|/L)` | mean `M_L` | `L(L+1)` | mean `M_L/L` | `θ`-mean `R_L` | ratio `M/(L|∂αE|)` median / 99% | share ratio > 10 |
|---|---|---|---|---|---|---|---|
| 16  | 1.67  | 60   | 272    | 3.8  | −1.15 | 0.28 / 15  | 1.3% |
| 32  | 1.06  | 163  | 1056   | 5.1  | −1.11 | 0.30 / 14  | 2.5% |
| 64  | 0.56  | 438  | 4160   | 6.9  | −0.96 | 0.34 / 22  | 3.0% |
| 128 | 0.22  | 1164 | 16512  | 9.1  | −0.75 | 0.37 / 81  | 4.5% |
| 256 | 0.13  | 2882 | 65792  | 11.3 | −0.64 | 0.41 / 33  | 7% |

* **Multiplicities.** The actual `M_L` is far below the algebraic bound `L(L+1)`:
  `M_L/L ≈ 0.9 √L` (exponent ≈ 0.43 from the five points). Replacing `M_L` by `L(L+1)` would
  add `log L` to the bound and destroy it, so the actual multiplicity is what matters.
* **Joint transversality** (`dirichlet_joint.py`, `L = 16, 32, 64, 128`):
  - The decay of the reported median comes from `∂_θ E` and from the normalization `1/L`. The
    flux derivative itself does **not** decay: the median of `|∂_α E|` is `12.7, 15.7, 16.8, 19.6`.
  - `|∂_θ E|` decays roughly like `1/L`. This is consistent with band widths `≍ 1/q` at critical
    coupling, a heuristic and not proved here. Its 10% quantile drops from `0.09` to `0.0007`.
  - `log|∂_α E|` and `log|∂_θ E|` decorrelate as `L` grows (`0.46, 0.39, 0.24, 0.19`), but the joint
    small set (both below a tenth of the median) grows, then levels off: `1.5%, 2.8%, 4.4%, 4.1%`.
  - So the phase direction cannot supply a uniform transversality. The flux direction is the
    one that carries the density.
* **Away from `0`.** By energy band, the mean of `log(M/(L|∂αE|))` is about `−1.2` on
  `0.25 ≤ |E| < 1` and `−1.0` to `−1.25` on `|E| ≥ 1`, roughly stable for `L = 16..128`.
  The band `|E| < 0.25` is noisy and rising (`−0.54, −0.81, −0.28, −0.08`), carries about 11% of the mass, and
  contributes little to `R_L` in total.
* **Exceptional sets.** The share of samples with ratio `> 10` grows: `1.3%, 2.5%, 3%, 4.5%, 7%` for
  `L = 16..256`. These samples are over-represented near `E = 0`: among them the share with
  `|E| < 0.25` is `22–40%` (not monotone in `L`), against `10–12%` overall. This
  matches the log² mass at `0` (§9).

  Truncating them does not obviously give uniform integrability. The exceptional set is not
  shrinking. A disproportionate part of it sits near `0`, where §10.1 already forbids `L log² L` control.
* **Trend of the bound.** `R_L` increases by about `0.13` per doubling of `L` (`−1.15, −1.11, −0.96, −0.75, −0.64`). Five points, with Monte Carlo error `≈ 0.1`, cannot decide whether `R_L` converges.
  A logarithmic growth `≈ 0.19 log L` fits as well as saturation.
* **Actual entropy.** The binned entropy of `g_{L,θ}` (800 bins, one `θ`; Jensen makes it a
  lower bound for `∫ g log g`) stays at `≈ −1.85` for all `L`. The gap to `R_L` is the Jensen loss
  `∫ g(log M − H(p))`, and it grows with `L`.

#### 10.7 Task 6: status

**No uniform entropy bound and no uniform integrability of the averaged Dirichlet densities is
proved. Absolute continuity of `μ_A` remains open.** What is new and unconditional:
* §10.1 **[L]**;
* §10.2 and §10.3 **[P]**;
* the simplicity and Jensen lemmas **[L]**;
* the top-coefficient argument and the coarea inequality **[P]**.

The obstruction identified by the numerics: the coarea bound loses `∫ g (log M_L − H(p_E))`. Its
growth is driven by `M_L/L ≈ √L` preimages of very unequal weight and by an exceptional set, over-represented near
`E = 0`, that grows with `L`. A proof along these lines would need to control the preimage-weight
entropy `H(p_E)`, not only the count `M_L`. Since the true binned entropy is flat, the numerics
do not contradict a uniform bound for `∫ ḡ_L log ḡ_L` itself. They only indicate that `R_L`
probably does not provide it.

### 11. The logarithmic upper bound at `0` and the two-scale Dirichlet identity (round 8)

Legend as above: **[L]** proved in Lean (standard axioms only), **[P]** paper argument,
**[N]** numerics.

#### 11.1 Audit of the proposed argument

The six-step argument proposed for round 8 was audited before it was formalized. **No
mathematical defect was found.** Three points needed care, and each is handled in the Lean proof:

* *Centering.* `E[X_j] = μ_N` is not zero. The bad-block event uses
  `|∑(−1)^j X_j| > T/4`. The alternating sum cancels `μ_N` up to one term, and `|μ_N| ≤ √5 < 3`
  (`abs_muX_lt`). Absorbing that term needs `T ≥ 24`; the proposal's "T sufficiently large" was
  made explicit.
* *Min–max.* The decomposition is used in codimension form (`card_le_of_coercive`). Each cut
  imposes two vanishing sites, and coercivity holds on the subspace where they vanish. This
  gives `#ι + #{|λ| ≤ h} ≤ #X` directly. It avoids the block-diagonal reduction, which would
  need the cross terms to vanish.
* *Gap constant.* The gap is `e^{−T/2}/(2m)` rather than `e^{−T/2}/m`
  (`chiral_gap: ‖η‖² ≤ 4m² e^T ‖Jη‖²`). This changes only constants.

#### 11.2 Proved theorems **[L]**

| Statement | Lean name |
|---|---|
| `(p,t) ↦ (t+pa, t+pb)` is a bijection of `(ℤ/N)²` when `a−b` is a unit (pairwise independence) | `ThomUpper.pair_bijective`, `sum_pair` |
| `∑_u log²‖1+ψ(u)‖ ≤ 5N` (`N` odd), i.e. `E[X_j²] ≤ 5` | `ThomUpper.sum_lb_sq_le` |
| Dyadic Rademacher–Menshov: `max_{m≤2^r} S_m² ≤ (r+1) Q_r` and `∑ Q_r ≤ (r+1) 2^r V` | `psum_sq_le_Qd`, `sum_Qd_le`, `card_bad_le` |
| `#{bad (p,t)} · T² ≤ 320 (ℓ+1)² 2^ℓ N²` (`N` prime, `T ≥ 24`) | `ThomUpper.card_badB_le` |
| Chiral block gap: on a good block of length `2m`, `‖η‖² ≤ 4m² e^T ‖Jη‖²` | `ThomUpper.chiral_gap`, `block_gap` |
| Adaptive decomposition: `‖ξ‖² ≤ 4^K e^T ‖Hξ‖²` off the vanishing set, with `#Z ≤ 2 + 2·#bad` per level | `Zt_coercive`, `Ztop_coercive`, `card_Ztop_le` |
| `σ_N([−h,h]) ≤ 2/2^K + 640(K+1)³/T² + 2^K/N` (`4^K e^T h² < 1`) | `ThomUpper.nuQ_upper` |
| **`μ_A([−h,h]) ≤ 17284 (1+log log(1/h))³ / log²(1/h)`**, `0 < h ≤ e^{−121}` | `ThomUpper.logUpperBound_explicit`, `logUpperBound` |
| **`∫_{|E|<1} log^s(1/|E|) dμ_A < ∞ ⟺ s < 2`** (`s > 0`) | `ThomUpper.logMoment_finite_iff` |
| Strip graph `[0,W)×ℤ/N×ℤ/N` (Dirichlet walls in `x`): symmetric, spectrum in `[−4,4]`, powers count strip walks | `ThomStrip.sMat_isHermitian`, `abs_eig_sMat_le`, `sMat_pow_apply`, `sWalk_eq_some` |
| **Exact Dirichlet moments**: `W∫Eᵏ dσ_{W,N} = W τ(Aᵏ) − b_k` for `k ≤ 2W`, `(k+1)² ≤ N`, with `b_k = ∑_{w∈Z_k} width(w)`, `0 ≤ 2b_k ≤ k τ(Aᵏ)` | `ThomStrip.stripMoment_formula`, `two_bk_le` |
| **Two-scale identity**: `∫P(E/4) dμ_A = 2∫P(E/4) dσ_{2W,N} − ∫P(E/4) dσ_{W,N}` for `deg P ≤ 2W`, `(2W+1)² ≤ N` | `ThomStrip.two_scale_poly`, `two_scale_cheb` |
| **Fejér identity and domination**: `F_n^{μ_A} = 2F_n^{σ_{2W}} − F_n^{σ_W}` and `0 ≤ F_n^{μ_A} ≤ 2F_n^{σ_{2W}}` on `[−4,4]` (`n ≤ 2W`) | `ThomStrip.fejer_two_scale`, `fejer_dom` |
| **Entropy domination**: `H_n(μ_A) ≤ 2H_n(σ_{2W,N}) + 2 log 2 + 1`; a uniform bound on `H_n(σ_{2n+2,(2n+3)²})` implies `FejerEntropyTarget` | `ThomStrip.fejEnt_two_scale_le`, `fejerEntropyTarget_of_strip` |

Remarks.

* The upper bound uses `muA_no_atoms` and moment matching along odd primes `N`, like the lower bound.
* `logMoment_finite_iff` does not assume a density. The direction `s ≥ 2` uses only
  `logSqLowerBound` and `muA_no_atoms`. The direction `s < 2` uses a layer cake with weights
  `(j+1)^s − j^s` and the upper bound.
* `σ_{W,N}` is the average of the vertex spectral measures at `(j,0,0)`, `j < W`. The proof of
  `stripMoment_formula` identifies its moments with walks: a closed strip walk from `(j,0,0)`
  is a zero-area closed walk of `H₃(ℤ)` whose columns stay in `[0,W)`. The number of admissible
  `j` is `W − width(w)`, since `2·width(w) ≤ k`.

#### 11.3 Paper arguments **[P]**

* *Identification with the round-7 model.* The Fourier transform in `(b,c) ∈ (ℤ/N)²` splits the
  strip graph into the matrices `H_W(α,θ)` with `α, θ ∈ (1/N)ℤ/ℤ`. So `σ_{W,N}` is the
  `N × N` grid average of the round-7 Dirichlet model. The round-7 proof gives the same moments
  for the continuous `(α,θ)` average. Hence `σ_{W,N}` and `σ_W` have the same moments up to
  degree `√N − 1`, and every identity in §11.2 holds for `σ_W` with `N` removed.
  Not formalized: the Fourier splitting. **[N]** check: the deficits `b_2, …, b_10` computed
  as `∑ width` are `2, 26, 296, 3386, 40152`. These are exactly the values of
  `L(τ(Aᵏ) − m_k(L))` found in round 7 by quadrature.
* *Removing the logarithmic losses.* The factor `(1+log log)³` has two sources.
  - The `(ℓ+1)²` comes from Rademacher–Menshov. This step uses only pairwise independence
    (orthogonality), and for general orthogonal systems Rademacher–Menshov is sharp.
  - One more factor `(K+1)` comes from summing over the `K ≍ log T` levels.
  - For three or more indices the bond phases `t + p(j+1)` are not independent: they lie on
    one line in `(ℤ/N)²`. So Doob's inequality and higher-moment (Chebyshev-free) tail bounds
    are not available from the averaging over `(p,t)` alone.
  - Removing all three factors would need a large-deviation bound for the alternating Birkhoff
    sums `∑(−1)^j log|2cos π(t+pj)/N|`. Shifted Sudler-product estimates for badly
    approximable `p/N` are the natural tool. **Not attempted in Lean; open.**
  - We do not know whether the truth is `1/log²` or carries a `log log` power. The lower bound
    `c/log²` and the upper bound differ by `(log log)³`.
* *Local estimates away from `0`.* The decomposition argument localizes at an energy `E₀` only
  through the chiral structure of the chain operator at `E = 0`. Away from `0` the transfer
  matrices are not chiral. The analogue needs Lyapunov-type lower bounds for the cocycle at
  energy `E₀`, uniform over the phases `(p,t)`. No such estimate is proved here. The localization
  `muA_ac_iff_local` (round 5) reduces absolute continuity to these local problems.
* *Cross-flux interactions.* The two-scale identity holds at the level of `(α,θ)`-averages. It
  says nothing about the branch structure of a single flux. Every estimate proved this round
  averages over fluxes first.

#### 11.4 Numerics **[N]** (`numerics/strip_entropy.py`, `out_strip_entropy.txt`)

Fejér entropies `H_n = ∫F_n log F_n dρ`. `H_n(σ_{2W})` uses `300²` grid points in `(α,θ)`;
`H_n(μ_A)` uses the exact coefficients `c_m(μ_A)` (`cheb_coeffs_n256.txt`).

| `n` | `W` | `H_n(μ_A)` | `H_n(σ_{2W})` | `max_m |c_m(μ_A) − (2c_m(σ_{2W}) − c_m(σ_W))|` |
|---|---|---|---|---|
| 8 | 4 | 0.1867 | 0.2072 | `2e−16` |
| 16 | 8 | 0.2736 | 0.2854 | `4e−16` |
| 32 | 16 | 0.3446 | 0.3503 | `3e−16` |
| 64 | 32 | 0.3973 | 0.3994 | `8e−9` |
| 128 | 64 | 0.4341 | 0.4345 | `3e−3` (grid too coarse for `n = 128`) |

* The two-scale identity holds to machine precision wherever the grid resolves the degree. This
  independently checks the Lean identity together with the paper identification of §11.3.
* `H_n(σ_{2W})` tracks `H_n(μ_A)` closely. This is expected: `c_m(σ_{2W}) = c_m(μ_A) − β_m/(2W)`
  with `β_m` the Chebyshev transform of `b_k`.
* The increments of `H_n(μ_A)` per doubling are `0.087, 0.071, 0.053, 0.037`, decaying by a factor
  of about `0.75`, consistent with round 5. This is suggestive of convergence, not evidence of it.

#### 11.5 Status and remaining obstructions

* **Absolute continuity of `μ_A` is not proved.** The logarithmic upper bound controls only the
  mass near `0`. It is compatible with both a density and a singular continuous part.
* The zero level is no longer an obstruction to the entropy target at the level of masses.
  If `μ_A` has a density `f`, Jensen on dyadic shells bounds the shell contribution
  `∑ m_j log(m_j 2^j)` by `∫ log(1/|E|) dμ_A + O(1)`, which is finite (`s = 1`). This is a
  lower-bound obstruction removed, not an upper bound: within-shell regularity of `f` is not
  controlled.
* `fejerEntropyTarget_of_strip` reduces `FejerEntropyTarget` to a statement about the
  finite-dimensional Dirichlet model at its own scale. The numerics show the two entropies are
  nearly equal, so the reduction transfers the difficulty rather than removing it. What it gains
  is structure: the strip model is a family of `2W × 2W` Jacobi matrices with simple, analytic
  eigenvalue branches (§10.4), so coarea and transversality arguments apply to it directly.
  The uncorrected coarea–Jensen bound `R_L` of §10.5 is **not** used anywhere.
* Open: `FejerEntropyTarget`, `WeightedTarget`, the dyadic target, and the strip-entropy
  hypothesis of `fejerEntropyTarget_of_strip`.

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
