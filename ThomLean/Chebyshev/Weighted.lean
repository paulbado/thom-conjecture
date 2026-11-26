import ThomLean.Chebyshev.Lebesgue

/-!
# The weighted spectral measure `dν = (E²/16) dμ`

* `four_X_sq_mul_T` : `4 X² T_m = T_{m+2} + 2 T_m + T_{m-2}` in `ℝ[X]` (all `m : ℤ`).
* `weighted μ := μ.withDensity (E ↦ E²/16)`.
* `chebCoeff_weighted` : for `n ≥ 2`, `d_n = (c_{n-2} + 2 c_n + c_{n+2}) / 4`, stated as
  `d_{n+2} = (c_n + 2 c_{n+2} + c_{n+4}) / 4`; also `d_0 = (c_0 + c_2)/2`, `d_1 = (3c_1 + c_3)/4`.
* `ac_of_summable_finite` : the Chebyshev `L²` criterion for an arbitrary *finite* measure
  carried by `[-4,4]` (by normalisation): `∑ c_{n+1}² < ∞ ⇒ ν ≪ Lebesgue`.
* `restrict_compl_zero_ac_weighted` : `μ|_{ℝ∖{0}} ≪ ν`.
* `ac_off_zero_of_weighted_summable` : `∑ d_{n+1}² < ∞ ⇒ μ|_{ℝ∖{0}} ≪ Lebesgue`.
* `ac_of_weighted_summable` : `∑ d_{n+1}² < ∞` and `μ{0} = 0` ⇒ `μ ≪ Lebesgue`.
* `weighted_summable_of_summable` : the old `L²` condition implies the weighted one.

All results are unconditional theorems or explicit implications.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set
open scoped ENNReal NNReal

/-- **Three-term identity** `4 X² T_m = T_{m+2} + 2 T_m + T_{m-2}`. -/
theorem four_X_sq_mul_T (m : ℤ) :
    4 * X ^ 2 * T ℝ m = T ℝ (m + 2) + 2 * T ℝ m + T ℝ (m - 2) := by
  have h := T_mul_T ℝ m 2
  rw [T_two] at h
  linear_combination h

/-- The weight `E²/16`. -/
def wt (E : ℝ) : ℝ := E ^ 2 / 16

lemma wt_nonneg (E : ℝ) : 0 ≤ wt E := by unfold wt; positivity

lemma continuous_wt : Continuous wt := by unfold wt; fun_prop

lemma measurable_wt : Measurable wt := continuous_wt.measurable

lemma wt_eq_zero_iff (E : ℝ) : wt E = 0 ↔ E = 0 := by
  unfold wt
  constructor
  · intro h
    have : E ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h; simp [h]

/-- The weighted spectral measure `dν(E) = (E²/16) dμ(E)`. -/
def weighted (μ : Measure ℝ) : Measure ℝ := μ.withDensity fun E => ENNReal.ofReal (wt E)

lemma integral_weighted (μ : Measure ℝ) (g : ℝ → ℝ) :
    ∫ E, g E ∂weighted μ = ∫ E, wt E * g E ∂μ := by
  rw [weighted, show (fun E => ENNReal.ofReal (wt E)) = fun E => ((Real.toNNReal (wt E) : ℝ≥0) : ℝ≥0∞)
      from rfl, integral_withDensity_eq_integral_smul measurable_wt.real_toNNReal]
  congr 1; ext E
  simp [NNReal.smul_def, Real.coe_toNNReal _ (wt_nonneg E)]

lemma weighted_ac (μ : Measure ℝ) : weighted μ ≪ μ := withDensity_absolutelyContinuous _ _

lemma carried_weighted {μ : Measure ℝ} (hμ : CarriedBy4 μ) : CarriedBy4 (weighted μ) :=
  weighted_ac μ hμ

lemma isFiniteMeasure_weighted (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) :
    IsFiniteMeasure (weighted μ) :=
  isFiniteMeasure_withDensity_ofReal (integrable_of_continuous hμ continuous_wt).2

/-- Weighted polynomial integrals through `polyIntegral`. -/
lemma integral_weighted_cheb (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) (n : ℕ) :
    chebCoeff (weighted μ) n = polyIntegral μ hμ (X ^ 2 * T ℝ n) := by
  rw [chebCoeff, integral_weighted]
  show _ = ∫ E, polyFun (X ^ 2 * T ℝ n) E ∂μ
  congr 1; ext E
  simp only [polyFun, eval_mul, eval_pow, eval_X, cheb, wt]
  ring

lemma X_sq_mul_T_eq (m : ℤ) :
    X ^ 2 * T ℝ m = (4⁻¹ : ℝ) • (T ℝ (m + 2) + (2 : ℝ) • T ℝ m + T ℝ (m - 2)) := by
  have h := four_X_sq_mul_T m
  have h4 : Polynomial.C (4⁻¹ : ℝ) * (4 : ℝ[X]) = 1 := by
    rw [← map_ofNat Polynomial.C 4, ← Polynomial.C_mul]; norm_num
  have h2 : Polynomial.C (2 : ℝ) = (2 : ℝ[X]) := map_ofNat Polynomial.C 2
  rw [smul_eq_C_mul, smul_eq_C_mul, h2]
  linear_combination Polynomial.C (4⁻¹ : ℝ) * h - X ^ 2 * T ℝ m * h4

/-- **Exact weighted coefficient identity** (`n ≥ 2`):
`d_{n+2} = (c_n + 2 c_{n+2} + c_{n+4}) / 4`. -/
theorem chebCoeff_weighted (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) (n : ℕ) :
    chebCoeff (weighted μ) (n + 2) =
      (chebCoeff μ n + 2 * chebCoeff μ (n + 2) + chebCoeff μ (n + 4)) / 4 := by
  rw [integral_weighted_cheb μ hμ, X_sq_mul_T_eq]
  have e1 : ((n + 2 : ℕ) : ℤ) + 2 = ((n + 4 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((n + 2 : ℕ) : ℤ) - 2 = ((n : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, map_smul, map_add, map_add, map_smul, polyIntegral_T, polyIntegral_T,
    polyIntegral_T, smul_eq_mul, smul_eq_mul]
  ring

/-- `d_0 = (c_0 + c_2)/2`. -/
theorem chebCoeff_weighted_zero (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) :
    chebCoeff (weighted μ) 0 = (chebCoeff μ 0 + chebCoeff μ 2) / 2 := by
  rw [integral_weighted_cheb μ hμ, X_sq_mul_T_eq]
  have e1 : ((0 : ℕ) : ℤ) + 2 = ((2 : ℕ) : ℤ) := by norm_num
  have e2 : T ℝ (((0 : ℕ) : ℤ) - 2) = T ℝ ((2 : ℕ) : ℤ) := by
    rw [show ((0 : ℕ) : ℤ) - 2 = -((2 : ℕ) : ℤ) by norm_num, T_neg]
  rw [e1, e2, map_smul, map_add, map_add, map_smul, polyIntegral_T, polyIntegral_T,
    smul_eq_mul, smul_eq_mul]
  ring

/-- `d_1 = (3 c_1 + c_3)/4`. -/
theorem chebCoeff_weighted_one (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) :
    chebCoeff (weighted μ) 1 = (3 * chebCoeff μ 1 + chebCoeff μ 3) / 4 := by
  rw [integral_weighted_cheb μ hμ, X_sq_mul_T_eq]
  have e1 : ((1 : ℕ) : ℤ) + 2 = ((3 : ℕ) : ℤ) := by norm_num
  have e2 : T ℝ (((1 : ℕ) : ℤ) - 2) = T ℝ ((1 : ℕ) : ℤ) := by
    rw [show ((1 : ℕ) : ℤ) - 2 = -((1 : ℕ) : ℤ) by norm_num, T_neg]
  rw [e1, e2, map_smul, map_add, map_add, map_smul, polyIntegral_T, polyIntegral_T,
    smul_eq_mul, smul_eq_mul]
  ring

/-! ### The criterion for finite measures -/

/-- **Chebyshev criterion for finite measures**: a finite measure carried by `[-4,4]` whose
Chebyshev coefficients are square-summable is absolutely continuous. -/
theorem ac_of_summable_finite (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : CarriedBy4 ν)
    (hc : Summable fun n => chebCoeff ν (n + 1) ^ 2) : ν ≪ volume := by
  rcases eq_zero_or_neZero ν with h0 | h0
  · rw [h0]; exact Measure.AbsolutelyContinuous.zero _
  set s := ν univ with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact (Measure.measure_univ_ne_zero).mpr h0.out
  have hstop : s ≠ ∞ := measure_ne_top ν univ
  let ν' := s⁻¹ • ν
  have hprob : IsProbabilityMeasure ν' := isProbabilityMeasureSMul
  have hν' : CarriedBy4 ν' := by
    unfold CarriedBy4 at hν ⊢; simp [ν', hν]
  have hc' : Summable fun n => chebCoeff ν' (n + 1) ^ 2 := by
    have : (fun n => chebCoeff ν' (n + 1) ^ 2) =
        fun n => (s⁻¹.toReal) ^ 2 * chebCoeff ν (n + 1) ^ 2 := by
      ext n; simp only [chebCoeff, ν', integral_smul_measure, smul_eq_mul]; ring
    rw [this]; exact hc.mul_left _
  have hac := absolutelyContinuous_of_summable ν' hν' hc'
  refine Measure.AbsolutelyContinuous.trans ?_ hac
  refine Measure.AbsolutelyContinuous.mk fun A _ hA => ?_
  have : s⁻¹ * ν A = 0 := by simpa [ν'] using hA
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ENNReal.inv_ne_zero.mpr hstop)
  · exact h

/-! ### Absolute continuity away from zero -/

/-- `μ` restricted to `ℝ ∖ {0}` is absolutely continuous with respect to the weighted measure. -/
theorem restrict_compl_zero_ac_weighted (μ : Measure ℝ) : μ.restrict {0}ᶜ ≪ weighted μ := by
  refine Measure.AbsolutelyContinuous.mk fun A hA h => ?_
  rw [weighted, withDensity_apply_eq_zero' (f := fun E => ENNReal.ofReal (wt E))
    (ENNReal.measurable_ofReal.comp measurable_wt).aemeasurable] at h
  rw [Measure.restrict_apply hA]
  have : {x | ENNReal.ofReal (wt x) ≠ 0} = ({0} : Set ℝ)ᶜ := by
    ext E
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, mem_ofPred_eq, mem_compl_iff,
      mem_singleton_iff]
    constructor
    · intro hE h0; rw [h0] at hE; simp [wt] at hE
    · intro hE; exact lt_of_le_of_ne (wt_nonneg E) (fun h => hE ((wt_eq_zero_iff E).mp h.symm))
  rw [this, inter_comm] at h
  exact h

/-- **Weighted criterion, off zero**: `∑ d_{n+1}² < ∞ ⇒ μ|_{ℝ∖{0}} ≪ Lebesgue`. -/
theorem ac_off_zero_of_weighted_summable (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ)
    (hd : Summable fun n => chebCoeff (weighted μ) (n + 1) ^ 2) :
    μ.restrict {0}ᶜ ≪ volume := by
  have := isFiniteMeasure_weighted μ hμ
  exact (restrict_compl_zero_ac_weighted μ).trans
    (ac_of_summable_finite (weighted μ) (carried_weighted hμ) hd)

/-- **Weighted criterion**: `∑ d_{n+1}² < ∞` and no atom at `0` ⇒ `μ ≪ Lebesgue`. -/
theorem ac_of_weighted_summable (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ)
    (hd : Summable fun n => chebCoeff (weighted μ) (n + 1) ^ 2) (h0 : μ {0} = 0) :
    μ ≪ volume := by
  have hoff := ac_off_zero_of_weighted_summable μ hμ hd
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_singleton (0 : ℝ)),
    add_apply, hoff hvol, add_zero, Measure.restrict_apply hA]
  exact measure_mono_null inter_subset_right h0

/-- Converse direction: with an atom at zero the weighted condition cannot detect it —
`ν{0} = 0` always. -/
theorem weighted_singleton_zero (μ : Measure ℝ) : weighted μ {0} = 0 := by
  rw [weighted, withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_singleton]
  simp [wt]

/-- The old `L²` condition implies the weighted one. -/
theorem weighted_summable_of_summable (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ)
    (hc : Summable fun n => chebCoeff μ (n + 1) ^ 2) :
    Summable fun n => chebCoeff (weighted μ) (n + 1) ^ 2 := by
  rw [← summable_nat_add_iff 1]
  have hc0 : Summable fun n => chebCoeff μ n ^ 2 := (summable_nat_add_iff 1).mp hc
  have h2 : Summable fun n => chebCoeff μ (n + 2) ^ 2 := (summable_nat_add_iff 2).mpr hc0
  have h4 : Summable fun n => chebCoeff μ (n + 4) ^ 2 := (summable_nat_add_iff 4).mpr hc0
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((hc0.add (h2.mul_left 4)).add h4)
  rw [show n + 1 + 1 = n + 2 by ring, chebCoeff_weighted μ hμ]
  nlinarith [sq_nonneg (chebCoeff μ n - chebCoeff μ (n + 2)),
    sq_nonneg (chebCoeff μ n - chebCoeff μ (n + 4)),
    sq_nonneg (chebCoeff μ (n + 2) - chebCoeff μ (n + 4)),
    sq_nonneg (chebCoeff μ n), sq_nonneg (chebCoeff μ (n + 2)), sq_nonneg (chebCoeff μ (n + 4))]

end ThomChebyshev
