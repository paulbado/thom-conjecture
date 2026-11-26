import ThomLean.Existence
import ThomLean.WeightedBridge
import ThomLean.Chebyshev.Atom
import ThomLean.Chebyshev.Duality

/-!
# Consequences for the canonical spectral measure `μ_A`

Now that `μ_A` exists (`ThomExistence.muA`), the conditional statements of `Bridge` and
`WeightedBridge` apply to it directly.

* `muA_atom_tendsto` : `μ_A{0} = lim_N (N+1)⁻¹ ∑_{j=0}^N (-1)^j τ(T_{2j}(A/4))` (exact).
* `NoAtomTarget : Prop` : this Cesàro limit is `0`; `noAtomTarget_iff : NoAtomTarget ↔ μ_A{0} = 0`.
* `EnergyGrowthTarget : Prop` : `N⁻¹ ∑_{n<N} τ(T_n(A/4))² → 0`; it implies `NoAtomTarget`.
* `muA_off_zero_ac` : `WeightedTarget ⇒ μ_A|_{ℝ∖{0}} ≪ Lebesgue`;
  `muA_off_zero_local_L2` : its density is `L²` on every `[a,b] ⊂ (-4,4) ∖ {0}`.
* `muA_ac_of_weighted` : `WeightedTarget ∧ NoAtomTarget ⇒ μ_A ≪ Lebesgue`.
* `muA_ac_of_weighted_energy` : `WeightedTarget ∧ EnergyGrowthTarget ⇒ μ_A ≪ Lebesgue`.
* `muA_ac_of_principal` : `PrincipalTarget ⇒ μ_A ≪ Lebesgue` (no extra hypothesis).

* `muA_ac_of_LqTarget` : the `L^q` duality target (`q ≥ 1`) ⇒ `μ_A ≪ Lebesgue`;
  `lqTarget_two_of_principal` : `PrincipalTarget ⇒ LqTarget 2`.

All targets are propositions; none is assumed.
-/

noncomputable section

namespace ThomConclusions

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence MeasureTheory Filter Topology Set
open Polynomial

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

/-- **Weighted target ⇒ local `L²` regularity of `μ_A` away from `0`**: `μ_A|_{ℝ∖{0}} = h dE`
with `h ∈ L²([a,b])` for every `[a,b] ⊂ (-4,4) ∖ {0}`. -/
theorem muA_off_zero_local_L2 (h : WeightedTarget) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ E, 0 ≤ g E) ∧
      muA.restrict {0}ᶜ = volume.withDensity (fun E => ENNReal.ofReal (g E)) ∧
      ∀ a b : ℝ, -4 < a → b < 4 → (0 < a ∨ b < 0) → MemLp g 2 (volume.restrict (Icc a b)) := by
  have := isSpectralMeasureA_muA.isProb
  exact exists_lebesgue_density_off_zero muA isSpectralMeasureA_muA.carried
    ((weightedTarget_iff isSpectralMeasureA_muA).mp h)

/-! ### `L^q` duality targets -/

/-- `τ(p(A/4)) = ∑_k [Xᵏ]p · 4⁻ᵏ · τ(Aᵏ)`, a finite combination of walk counts. -/
def tauPoly (p : ℝ[X]) : ℝ := p.sum fun k a => a * (4⁻¹ : ℝ) ^ k * (moment k : ℝ)

theorem integral_polyFun_muA (p : ℝ[X]) : ∫ E, polyFun p E ∂muA = tauPoly p := by
  have := isSpectralMeasureA_muA.isProb
  show polyIntegral muA isSpectralMeasureA_muA.carried p = _
  rw [linear_eq_sum, tauPoly]
  congr 1; ext k a
  show a * ∫ E, polyFun (X ^ k) E ∂muA = _
  simp only [polyFun, eval_pow, eval_X, div_eq_mul_inv, mul_pow]
  rw [integral_mul_const, isSpectralMeasureA_muA.moments k]; ring

/-- **`L^q` duality target** (a proposition): `|τ(P(A/4))| ≤ K ‖P(·/4)‖_{L^q(arcsine)}` for all
real polynomials `P`. For `q > 2` this is the dual form of an `L^p(arcsine)` density with
`p = q/(q-1) < 2`. -/
def LqTarget (q : ℝ) : Prop :=
  ∃ K : ℝ, ∀ p : ℝ[X], |tauPoly p| ≤ K * (∫ E, |polyFun p E| ^ q ∂arcsine) ^ (1 / q)

/-- **`L^q` target ⇒ absolute continuity** (any `q ≥ 1`). -/
theorem muA_ac_of_LqTarget {q : ℝ} (hq : 1 ≤ q) (h : LqTarget q) : muA ≪ volume := by
  obtain ⟨K, hK⟩ := h
  have := isSpectralMeasureA_muA.isProb
  exact ac_of_poly_Lq_bound muA isSpectralMeasureA_muA.carried hq (K := K) fun p => by
    rw [integral_polyFun_muA]; exact hK p

/-- The principal (`L²`) target implies the `L²` duality target. -/
theorem lqTarget_two_of_principal (h : PrincipalTarget) : LqTarget 2 := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨f, hfm, hf0, hf2, hμf⟩ := (principalTarget_iff_L2 isSpectralMeasureA_muA).mp h
  refine ⟨(∫ E, f E ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ)), fun p => ?_⟩
  rw [← integral_polyFun_muA, hμf, show (fun E => ENNReal.ofReal (f E)) =
      fun E => ((Real.toNNReal (f E) : NNReal) : ENNReal) from rfl,
    integral_withDensity_eq_integral_smul hfm.real_toNNReal]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hf0 _), smul_eq_mul]
  have hP2 : MemLp (fun E => |polyFun p E|) (ENNReal.ofReal 2) arcsine := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    simpa [Real.norm_eq_abs] using (memLp_polyFun p).norm
  have hf2' : MemLp f (ENNReal.ofReal 2) arcsine := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hf2
  calc |∫ E, f E * polyFun p E ∂arcsine| ≤ ∫ E, |polyFun p E| * f E ∂arcsine := by
        refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
        congr 1; ext E; rw [abs_mul, abs_of_nonneg (hf0 E), mul_comm]
    _ ≤ (∫ E, |polyFun p E| ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ)) *
          (∫ E, f E ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
          (ae_of_all _ fun E => abs_nonneg _) (ae_of_all _ fun E => hf0 E) hP2 hf2'
    _ = _ := mul_comm _ _

end ThomConclusions
