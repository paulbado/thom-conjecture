import ThomLean.Existence
import ThomLean.WeightedBridge
import ThomLean.Chebyshev.Atom

/-!
# Consequences for the canonical spectral measure `μ_A`

Now that `μ_A` exists (`ThomExistence.muA`), the conditional statements of `Bridge` and
`WeightedBridge` apply to it directly.

* `muA_atom_tendsto` : `μ_A{0} = lim_N (N+1)⁻¹ ∑_{j=0}^N (-1)^j τ(T_{2j}(A/4))` (exact).
* `NoAtomTarget : Prop` : this Cesàro limit is `0`; `noAtomTarget_iff : NoAtomTarget ↔ μ_A{0} = 0`.
* `EnergyGrowthTarget : Prop` : `N⁻¹ ∑_{n<N} τ(T_n(A/4))² → 0`; it implies `NoAtomTarget`.
* `muA_off_zero_ac` : `WeightedTarget ⇒ μ_A|_{ℝ∖{0}} ≪ Lebesgue`.
* `muA_ac_of_weighted` : `WeightedTarget ∧ NoAtomTarget ⇒ μ_A ≪ Lebesgue`.
* `muA_ac_of_weighted_energy` : `WeightedTarget ∧ EnergyGrowthTarget ⇒ μ_A ≪ Lebesgue`.
* `muA_ac_of_principal` : `PrincipalTarget ⇒ μ_A ≪ Lebesgue` (no extra hypothesis).

The three targets are propositions; none is assumed.
-/

noncomputable section

namespace ThomConclusions

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence MeasureTheory Filter Topology Set

/-- Cesàro means `(N+1)⁻¹ ∑_{j=0}^N (-1)^j τ(T_{2j}(A/4))`. -/
def atomTrace (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (N + 1), (-1 : ℝ) ^ j * chebTrace (2 * j)) / (N + 1)

lemma atomMean_muA : atomMean muA = atomTrace := by
  ext N
  simp only [atomMean, atomTrace, chebCoeff_eq_chebTrace isSpectralMeasureA_muA]

/-- **Exact atom formula for `μ_A`.** -/
theorem muA_atom_tendsto : Tendsto atomTrace atTop (𝓝 (muA {0}).toReal) := by
  have := isSpectralMeasureA_muA.isProb
  rw [← atomMean_muA]
  exact tendsto_atomMean muA isSpectralMeasureA_muA.carried

/-- **No-atom target** (a proposition): the Cesàro means of `(-1)^j τ(T_{2j}(A/4))` tend to `0`. -/
def NoAtomTarget : Prop := Tendsto atomTrace atTop (𝓝 0)

theorem noAtomTarget_iff : NoAtomTarget ↔ muA {0} = 0 := by
  have := isSpectralMeasureA_muA.isProb
  rw [NoAtomTarget, ← atomMean_muA]
  exact (atom_eq_zero_iff muA isSpectralMeasureA_muA.carried).symm

/-- **Energy growth target** (a proposition, much weaker than `PrincipalTarget`):
`N⁻¹ ∑_{n<N} τ(T_n(A/4))² → 0`. -/
def EnergyGrowthTarget : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, chebTrace n ^ 2) / N) atTop (𝓝 0)

theorem noAtomTarget_of_energyGrowth (h : EnergyGrowthTarget) : NoAtomTarget := by
  have := isSpectralMeasureA_muA.isProb
  rw [noAtomTarget_iff]
  refine atom_eq_zero_of_energy muA isSpectralMeasureA_muA.carried ?_
  simpa only [chebCoeff_eq_chebTrace isSpectralMeasureA_muA, EnergyGrowthTarget] using h

/-- The principal target implies the energy growth target. -/
theorem energyGrowth_of_principal (h : PrincipalTarget) : EnergyGrowthTarget := by
  have h0 : Summable fun n => chebTrace n ^ 2 := (summable_nat_add_iff 1).mp h
  set K := ∑' n, chebTrace n ^ 2
  have hb : ∀ N : ℕ, (∑ n ∈ Finset.range N, chebTrace n ^ 2) / N ≤ K * (1 / (N : ℝ)) := by
    intro N
    rw [div_eq_mul_one_div]
    gcongr
    exact h0.sum_le_tsum _ (fun n _ => sq_nonneg _)
  have hpos : ∀ N : ℕ, 0 ≤ (∑ n ∈ Finset.range N, chebTrace n ^ 2) / N := fun N =>
    div_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _) (Nat.cast_nonneg N)
  have hlim : Tendsto (fun N : ℕ => K * (1 / (N : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul K
    rwa [mul_zero] at this
  exact squeeze_zero hpos hb hlim

/-- **Unconditional off-zero statement under the weighted target.** -/
theorem muA_off_zero_ac (h : WeightedTarget) : muA.restrict {0}ᶜ ≪ volume :=
  ac_off_zero_of_weightedTarget isSpectralMeasureA_muA h

/-- **Conditional absolute continuity**: weighted target and no atom at `0`. -/
theorem muA_ac_of_weighted (h : WeightedTarget) (h0 : NoAtomTarget) : muA ≪ volume :=
  ac_of_weightedTarget isSpectralMeasureA_muA (noAtomTarget_iff.mp h0) h

/-- **Conditional absolute continuity**: weighted target and sublinear energy growth. -/
theorem muA_ac_of_weighted_energy (h : WeightedTarget) (hE : EnergyGrowthTarget) :
    muA ≪ volume :=
  muA_ac_of_weighted h (noAtomTarget_of_energyGrowth hE)

/-- The principal target alone gives `μ_A ≪ Lebesgue`. -/
theorem muA_ac_of_principal (h : PrincipalTarget) : muA ≪ volume :=
  (ac_of_principalTarget isSpectralMeasureA_muA h).1

/-- Explicit upper bounds for the atom: `μ_A{0} ≤ τ(p(A/4)²)` whenever `p(0) = 1`. -/
theorem muA_atom_le (p : Polynomial ℝ) (hp : p.eval 0 = 1) :
    (muA {0}).toReal ≤ (p ^ 2).sum fun k a => a * (4⁻¹ : ℝ) ^ k * (moment k : ℝ) :=
  atom_le_tau isSpectralMeasureA_muA p hp

end ThomConclusions
