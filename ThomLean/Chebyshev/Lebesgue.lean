import ThomLean.Chebyshev.Criterion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue density of the arcsine law and local `L²` regularity

* `arcsine_eq_withDensity` : `ρ = (π √(16 - E²))⁻¹ 𝟙_{(-4,4]}(E) dE`.
* `absolutelyContinuous_of_summable` : the Chebyshev `L²` condition implies `μ ≪ Lebesgue`.
* `exists_lebesgue_density_of_summable` : under the same condition `μ = g dE` with `g ≥ 0`
  and `g ∈ L²([a,b])` for every `-4 < a ≤ b < 4` (local `L²` regularity on `(-4,4)`).

All results are unconditional implications.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set
open scoped ENNReal NNReal

/-- Lebesgue density of the arcsine law. -/
def arcDens (E : ℝ) : ℝ := (Ioc (-4 : ℝ) 4).indicator (fun E => (π * √(16 - E ^ 2))⁻¹) E

lemma arcDens_nonneg (E : ℝ) : 0 ≤ arcDens E := by
  unfold arcDens; apply indicator_nonneg; intro E _; positivity

lemma measurable_arcDens : Measurable arcDens := by
  unfold arcDens
  exact Measurable.indicator (by fun_prop) measurableSet_Ioc

lemma map_scale4_withDensity (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (volume.withDensity h).map scale4 = volume.withDensity (fun E => 4⁻¹ * h (E / 4)) := by
  ext s hs
  rw [Measure.map_apply measurableEmbedding_scale4.measurable hs,
    withDensity_apply _ (measurableEmbedding_scale4.measurable hs), withDensity_apply _ hs]
  set G : ℝ → ℝ≥0∞ := s.indicator fun E => h (E / 4)
  have hG : Measurable G := (hh.comp (measurable_id.div_const 4)).indicator hs
  have h1 : ∫⁻ x in scale4 ⁻¹' s, h x = ∫⁻ x, G (4 * x) := by
    rw [← lintegral_indicator (measurableEmbedding_scale4.measurable hs)]
    congr 1; ext x
    simp only [G, indicator, mem_preimage, scale4]
    by_cases hx : 4 * x ∈ s <;> simp [hx, scale4, show 4 * x / 4 = x by ring]
  have h2 : ∫⁻ x, G (4 * x) = ENNReal.ofReal |(4 : ℝ)⁻¹| * ∫⁻ E, G E := by
    calc ∫⁻ x, G (4 * x) = ∫⁻ E, G E ∂(Measure.map (4 * ·) volume) :=
          (lintegral_map hG (measurable_const_mul 4)).symm
      _ = ∫⁻ E, G E ∂(ENNReal.ofReal |(4 : ℝ)⁻¹| • volume) := by
          rw [Real.map_volume_mul_left (by norm_num : (4 : ℝ) ≠ 0)]
      _ = _ := by rw [lintegral_smul_measure]; rfl
  have h3 : ENNReal.ofReal |(4 : ℝ)⁻¹| = 4⁻¹ := by
    rw [abs_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  rw [h1, h2, h3, ← lintegral_const_mul _ hG, ← lintegral_indicator hs]
  congr 1; ext E
  simp only [G, indicator]; split_ifs <;> simp

/-- **Explicit Lebesgue density** of the arcsine law. -/
theorem arcsine_eq_withDensity :
    arcsine = volume.withDensity fun E => ENNReal.ofReal (arcDens E) := by
  set w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))
  have hw : Measurable w :=
    Measurable.coe_nnreal_ennreal (Measurable.subtype_mk (by fun_prop))
  have hT : measureT = volume.withDensity ((Ioc (-1 : ℝ) 1).indicator w) := by
    rw [withDensity_indicator measurableSet_Ioc, measureT, restrict_withDensity measurableSet_Ioc]
  rw [arcsine, hT, map_scale4_withDensity _ (hw.indicator measurableSet_Ioc),
    ← withDensity_smul _ (by
      exact measurable_const.mul ((hw.indicator measurableSet_Ioc).comp
        (measurable_id.div_const 4)))]
  congr 1; ext E
  simp only [Pi.smul_apply, smul_eq_mul, arcDens, indicator, mem_Ioc]
  have hiff : (-1 < E / 4 ∧ E / 4 ≤ 1) ↔ (-4 < E ∧ E ≤ 4) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hE : -4 < E ∧ E ≤ 4
  · rw [if_pos (hiff.mpr hE), if_pos hE]
    have hsq : √(16 - E ^ 2) = 4 * √(1 - (E / 4) ^ 2) := by
      rw [show 16 - E ^ 2 = 4 ^ 2 * (1 - (E / 4) ^ 2) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    simp only [w]
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk,
      show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 4⁻¹ by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity), hsq]
    congr 1
    rw [mul_inv, mul_inv, Real.sqrt_inv]
  · rw [if_neg (fun h => hE (hiff.mp h)), if_neg hE]; simp

lemma arcsine_ac : arcsine ≪ volume := by
  rw [arcsine_eq_withDensity]; exact withDensity_absolutelyContinuous _ _

/-- **Absolute continuity from the Chebyshev `L²` condition.** -/
theorem absolutelyContinuous_of_summable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CarriedBy4 μ) (hc : Summable fun n => chebCoeff μ (n + 1) ^ 2) : μ ≪ volume := by
  obtain ⟨f, -, -, -, hμf, -⟩ := exists_density_of_summable μ hμ hc
  rw [hμf]
  exact (withDensity_absolutelyContinuous _ _).trans arcsine_ac

lemma arcDens_le {a b : ℝ} (ha : -4 < a) (hb : b < 4) :
    ∃ M, 0 ≤ M ∧ ∀ E ∈ Icc a b, arcDens E ≤ M := by
  set c := max (max (-a) b) 0
  have hc : c < 4 := max_lt (max_lt (by linarith) hb) (by norm_num)
  have hc0 : 0 ≤ c := le_max_right _ _
  have hpos : 0 < 16 - c ^ 2 := by nlinarith
  refine ⟨(π * √(16 - c ^ 2))⁻¹, by positivity, fun E hE => ?_⟩
  have hEc : |E| ≤ c := by
    have h1 := le_max_left (max (-a) b) 0
    have h2 := le_max_left (-a) b
    have h3 := le_max_right (-a) b
    rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
  have hE2 : E ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hEc 2
  unfold arcDens
  by_cases hm : E ∈ Ioc (-4 : ℝ) 4
  · rw [indicator_of_mem hm]
    apply inv_anti₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [indicator_of_notMem hm]; positivity

/-- **Local `L²` regularity.** Under the Chebyshev `L²` condition, `μ` has a Lebesgue density
which is square-integrable on every compact subinterval of `(-4,4)`. -/
theorem exists_lebesgue_density_of_summable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CarriedBy4 μ) (hc : Summable fun n => chebCoeff μ (n + 1) ^ 2) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ E, 0 ≤ g E) ∧
      μ = volume.withDensity (fun E => ENNReal.ofReal (g E)) ∧
      ∀ a b : ℝ, -4 < a → b < 4 → MemLp g 2 (volume.restrict (Icc a b)) := by
  obtain ⟨f, hfm, hf0, hfL2, hμf, -⟩ := exists_density_of_summable μ hμ hc
  refine ⟨fun E => f E * arcDens E, hfm.mul measurable_arcDens,
    fun E => mul_nonneg (hf0 E) (arcDens_nonneg E), ?_, ?_⟩
  · rw [hμf, arcsine_eq_withDensity, ← withDensity_mul _
      (f := fun E => ENNReal.ofReal (arcDens E)) (g := fun E => ENNReal.ofReal (f E))
      (ENNReal.measurable_ofReal.comp measurable_arcDens) (ENNReal.measurable_ofReal.comp hfm)]
    congr 1; ext E
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (arcDens_nonneg E), mul_comm]
  · intro a b ha hb
    obtain ⟨M, hM0, hM⟩ := arcDens_le ha hb
    have hmeas : AEStronglyMeasurable (fun E => f E * arcDens E) (volume.restrict (Icc a b)) :=
      (hfm.mul measurable_arcDens).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    -- `f² · arcDens` is Lebesgue integrable
    have hint : Integrable (fun E => f E ^ 2 * arcDens E) volume := by
      have h := (memLp_two_iff_integrable_sq hfL2.aestronglyMeasurable).mp hfL2
      rw [arcsine_eq_withDensity, integrable_withDensity_iff
        (f := fun E => ENNReal.ofReal (arcDens E)) (ENNReal.measurable_ofReal.comp measurable_arcDens)
        (Filter.Eventually.of_forall fun E => ENNReal.ofReal_lt_top)] at h
      refine h.congr (Filter.Eventually.of_forall fun E => ?_)
      simp [ENNReal.toReal_ofReal (arcDens_nonneg E)]
    refine (hint.restrict.const_mul M).mono' ((hfm.mul measurable_arcDens).pow_const 2
      |>.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun E hE => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hM E hE
    have h2 := arcDens_nonneg E
    have h3 := sq_nonneg (f E)
    calc (f E * arcDens E) ^ 2 = (f E ^ 2 * arcDens E) * arcDens E := by ring
      _ ≤ (f E ^ 2 * arcDens E) * M := mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)
      _ = M * (f E ^ 2 * arcDens E) := by ring

end ThomChebyshev
