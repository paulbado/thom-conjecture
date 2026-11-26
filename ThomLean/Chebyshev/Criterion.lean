import ThomLean.Chebyshev.Arcsine
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Chebyshev `L²` criterion for absolute continuity

Let `μ` be a probability measure carried by `[-4,4]` with Chebyshev coefficients
`c_n = ∫ T_n(E/4) dμ(E)`. If `∑_{n ≥ 1} c_n² < ∞`, then

* `μ = f · ρ` with `0 ≤ f ∈ L²(ρ)`, where `ρ` is the arcsine law (`exists_density_of_summable`);
* `‖f‖²_{L²(ρ)} = 1 + 2 ∑_{n≥1} c_n²` (Parseval identity, same theorem);
* `μ ≪ Lebesgue` (`absolutelyContinuous_of_summable`).

Uniqueness of measures with the same Chebyshev (equivalently polynomial) moments is
`eq_of_integral_cheb_eq`; it is used in place of a separate moment-problem argument.
All results are unconditional implications.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set
open scoped ENNReal NNReal BoundedContinuousFunction

/-- Chebyshev coefficients `c_n = ∫ T_n(E/4) dμ`. -/
def chebCoeff (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ E, cheb n E ∂μ

/-- Carried by `[-4,4]`. -/
def CarriedBy4 (μ : Measure ℝ) : Prop := μ (Icc (-4 : ℝ) 4)ᶜ = 0

lemma ae_mem_of_carried {μ : Measure ℝ} (hμ : CarriedBy4 μ) : ∀ᵐ E ∂μ, E ∈ Icc (-4 : ℝ) 4 := by
  unfold CarriedBy4 at hμ
  rw [ae_iff]; simpa [compl_def] using hμ

/-- Polynomial integrals as a linear functional. -/
def polyIntegral (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ E, polyFun p E ∂μ
  map_add' p q := by
    rw [← integral_add (integrable_of_continuous hμ (continuous_polyFun p))
      (integrable_of_continuous hμ (continuous_polyFun q))]
    congr 1; ext E; simp [polyFun]
  map_smul' c p := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1; ext E; simp [polyFun]

lemma polyIntegral_T (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) (n : ℕ) :
    polyIntegral μ hμ (T ℝ n) = chebCoeff μ n := rfl

/-- If two linear functionals on `ℝ[X]` agree on all `T_n`, they agree everywhere. -/
lemma linearMap_eq_of_T {L₁ L₂ : ℝ[X] →ₗ[ℝ] ℝ} (h : ∀ n : ℕ, L₁ (T ℝ n) = L₂ (T ℝ n))
    (p : ℝ[X]) : L₁ p = L₂ p := by
  have : Submodule.span ℝ (range fun k : ℕ => T ℝ k) ≤ LinearMap.eqLocus L₁ L₂ := by
    rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact h k
  exact this (mem_span_T p)

/-- Approximation step: if `∫ p(E/4) dμ = Λ(p)` for all polynomials, with a functional of the
form `Λ(g) = ∫ g · F dρ`, `F ∈ L¹(ρ)`, then the identity holds for every bounded continuous `g`. -/
lemma integral_eq_of_poly {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    {F : ℝ → ℝ} (hF : Integrable F arcsine)
    (hpoly : ∀ p : ℝ[X], ∫ E, polyFun p E ∂μ = ∫ E, polyFun p E * F E ∂arcsine)
    (g : ℝ →ᵇ ℝ) : ∫ E, g E ∂μ = ∫ E, g E * F E ∂arcsine := by
  have hgF : Integrable (fun E => g E * F E) arcsine := by
    refine hF.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun E => g.norm_coe_le_norm E
  apply eq_of_forall_dist_le
  intro ε hε
  set M := 1 + ∫ E, |F E| ∂arcsine with hMdef
  have hM : 0 < M := by have := integral_nonneg (μ := arcsine) (fun E => abs_nonneg (F E)); linarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => g (4 * x))
    (by fun_prop) (ε / M) (by positivity)
  have hclose : ∀ E ∈ Icc (-4 : ℝ) 4, |polyFun p E - g E| ≤ ε / M := by
    intro E hE
    have h3 : E / 4 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hE.1, hE.2]
    have := hp (E / 4) h3
    rw [show 4 * (E / 4) = E by ring] at this
    exact this.le
  have hpμ := integrable_of_continuous hμ (continuous_polyFun p)
  have hpF : Integrable (fun E => polyFun p E * F E) arcsine := by
    have hpb : ∀ E ∈ Icc (-4 : ℝ) 4, ‖polyFun p E‖ ≤ ‖g‖ + ε / M := by
      intro E hE
      have := hclose E hE
      have hg := g.norm_coe_le_norm E
      rw [Real.norm_eq_abs] at hg ⊢
      have := abs_sub_abs_le_abs_sub (polyFun p E) (g E)
      linarith
    refine hF.bdd_mul (c := ‖g‖ + ε / M) (continuous_polyFun p).aestronglyMeasurable ?_
    filter_upwards [ae_arcsine_mem_Icc] with E hE using hpb E hE
  have h1 : dist (∫ E, g E ∂μ) (∫ E, polyFun p E ∂μ) ≤ ε / M := by
    rw [dist_eq_norm, ← integral_sub (BoundedContinuousFunction.integrable μ g) hpμ]
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := ε / M)
      (f := fun E => g E - polyFun p E) (by
        filter_upwards [ae_mem_of_carried hμ] with E hE
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hclose E hE)
    simpa [measureUnivNNReal, Measure.real, measure_univ] using this
  have h2 : dist (∫ E, polyFun p E * F E ∂arcsine) (∫ E, g E * F E ∂arcsine) ≤
      ε / M * ∫ E, |F E| ∂arcsine := by
    rw [dist_eq_norm, ← integral_sub hpF hgF, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae ?_ ?_ ?_)
    · exact (hpF.sub hgF).norm
    · exact hF.abs.const_mul _
    · filter_upwards [ae_arcsine_mem_Icc] with E hE
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hclose E hE) (abs_nonneg _)
  rw [hpoly p] at h1
  calc dist (∫ E, g E ∂μ) (∫ E, g E * F E ∂arcsine)
      ≤ dist (∫ E, g E ∂μ) (∫ E, polyFun p E * F E ∂arcsine) +
        dist (∫ E, polyFun p E * F E ∂arcsine) (∫ E, g E * F E ∂arcsine) := dist_triangle _ _ _
    _ ≤ ε / M + ε / M * ∫ E, |F E| ∂arcsine := add_le_add h1 h2
    _ = ε / M * (1 + ∫ E, |F E| ∂arcsine) := by ring
    _ = ε := by rw [← hMdef]; field_simp

/-- **Uniqueness**: finite measures carried by `[-4,4]` with the same Chebyshev coefficients
are equal. -/
theorem eq_of_integral_cheb_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : CarriedBy4 μ) (hν : CarriedBy4 ν) (h : ∀ n, chebCoeff μ n = chebCoeff ν n) :
    μ = ν := by
  have hpoly : ∀ p : ℝ[X], ∫ E, polyFun p E ∂μ = ∫ E, polyFun p E ∂ν := fun p =>
    linearMap_eq_of_T (L₁ := polyIntegral μ hμ) (L₂ := polyIntegral ν hν) h p
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  -- approximate `g` uniformly on `[-4,4]` by polynomials, using the two measures
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => g (4 * x))
    (by fun_prop) (ε / 2) (by positivity)
  have hclose : ∀ E ∈ Icc (-4 : ℝ) 4, |g E - polyFun p E| ≤ ε / 2 := by
    intro E hE
    have h3 : E / 4 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hE.1, hE.2]
    have := hp (E / 4) h3
    rw [show 4 * (E / 4) = E by ring, abs_sub_comm] at this
    exact this.le
  have hbound : ∀ (σ : Measure ℝ) [IsProbabilityMeasure σ], CarriedBy4 σ →
      dist (∫ E, g E ∂σ) (∫ E, polyFun p E ∂σ) ≤ ε / 2 := by
    intro σ _ hσ
    rw [dist_eq_norm, ← integral_sub (BoundedContinuousFunction.integrable σ g) (integrable_of_continuous hσ
      (continuous_polyFun p))]
    have := norm_integral_le_of_norm_le_const (μ := σ) (C := ε / 2)
      (f := fun E => g E - polyFun p E) (by
        filter_upwards [ae_mem_of_carried hσ] with E hE
        rw [Real.norm_eq_abs]; exact hclose E hE)
    simpa [Measure.real, measure_univ] using this
  calc dist (∫ E, g E ∂μ) (∫ E, g E ∂ν)
      ≤ dist (∫ E, g E ∂μ) (∫ E, polyFun p E ∂μ) + dist (∫ E, polyFun p E ∂ν) (∫ E, g E ∂ν) := by
        rw [← hpoly p]; exact dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hbound μ hμ) (by rw [dist_comm]; exact hbound ν hν)
    _ = ε := by ring

/-! ### Main criterion -/

/-- The coefficient sequence `a_0 = 1`, `a_n = √2 c_n` (`n ≥ 1`). -/
def coeffSeq (μ : Measure ℝ) (n : ℕ) : ℝ := normConst n * chebCoeff μ n

lemma chebCoeff_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : chebCoeff μ 0 = 1 := by
  simp [chebCoeff, cheb_zero]

lemma summable_coeffSeq_sq (μ : Measure ℝ) (hc : Summable fun n => chebCoeff μ (n + 1) ^ 2) :
    Summable fun n => coeffSeq μ n ^ 2 := by
  rw [← summable_nat_add_iff 1]
  have : (fun n => coeffSeq μ (n + 1) ^ 2) = fun n => 2 * chebCoeff μ (n + 1) ^ 2 := by
    ext n; simp [coeffSeq, normConst, mul_pow]
  rw [this]; exact hc.mul_left 2

/-- **Chebyshev `L²` criterion.** Let `μ` be a probability measure carried by `[-4,4]` with
`∑_{n≥1} c_n² < ∞`. Then `μ = f ρ` for some measurable `f ≥ 0` in `L²(ρ)`, and
`∫ f² dρ = 1 + 2 ∑_{n≥1} c_n²`. -/
theorem exists_density_of_summable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (hc : Summable fun n => chebCoeff μ (n + 1) ^ 2) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ E, 0 ≤ f E) ∧ MemLp f 2 arcsine ∧
      μ = arcsine.withDensity (fun E => ENNReal.ofReal (f E)) ∧
      ∫ E, f E ^ 2 ∂arcsine = 1 + 2 * ∑' n, chebCoeff μ (n + 1) ^ 2 := by
  classical
  -- the element of `L²(ρ)` with prescribed Chebyshev coordinates
  have hmem : Memℓp (coeffSeq μ) 2 := by
    refine memℓp_gen ?_
    simpa [Real.norm_eq_abs, sq_abs] using (summable_coeffSeq_sq μ hc)
  let Fl : Lp ℝ 2 arcsine := chebBasis.repr.symm ⟨coeffSeq μ, hmem⟩
  have hinner : ∀ n, inner ℝ (chebL2 n) Fl = coeffSeq μ n := by
    intro n
    rw [← chebBasis_apply, ← chebBasis.repr_apply_apply]
    simp [Fl]
  -- a strongly measurable representative
  set F : ℝ → ℝ := (Fl : ℝ → ℝ) with hFdef
  have hFm : StronglyMeasurable F := Lp.stronglyMeasurable Fl
  have hFL2 : MemLp F 2 arcsine := Lp.memLp Fl
  have hFL1 : Integrable F arcsine := hFL2.integrable (by norm_num)
  -- Chebyshev moments of `F ρ`
  have hcheb : ∀ n, ∫ E, cheb n E * F E ∂arcsine = chebCoeff μ n := by
    intro n
    have h := hinner n
    rw [show Fl = hFL2.toLp F from (Lp.toLp_coeFn Fl hFL2).symm, chebL2, inner_toLp_eq] at h
    simp only [chebFun, coeffSeq] at h
    have hc0 : normConst n ≠ 0 := by unfold normConst; split_ifs <;> positivity
    simp_rw [mul_assoc] at h
    rw [integral_const_mul] at h
    exact mul_left_cancel₀ hc0 h
  -- polynomial moments of `F ρ`
  have hpoly : ∀ p : ℝ[X], ∫ E, polyFun p E ∂μ = ∫ E, polyFun p E * F E ∂arcsine := by
    let L₂ : ℝ[X] →ₗ[ℝ] ℝ :=
      { toFun := fun p => ∫ E, polyFun p E * F E ∂arcsine
        map_add' := fun p q => by
          rw [← integral_add]
          · congr 1; ext E; simp [polyFun]; ring
          · exact (memLp_polyFun p).integrable_mul hFL2
          · exact (memLp_polyFun q).integrable_mul hFL2
        map_smul' := fun c p => by
          rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
          congr 1; ext E; simp [polyFun]; ring }
    intro p
    exact linearMap_eq_of_T (L₁ := polyIntegral μ hμ) (L₂ := L₂) (fun n => (hcheb n).symm) p
  -- bounded continuous test functions
  have hbcf := integral_eq_of_poly hμ hFL1 hpoly
  -- positive and negative parts
  let fp : ℝ → ℝ≥0 := fun E => Real.toNNReal (F E)
  let fm : ℝ → ℝ≥0 := fun E => Real.toNNReal (-F E)
  have hfp : Measurable fp := hFm.measurable.real_toNNReal
  have hfm : Measurable fm := hFm.measurable.neg.real_toNNReal
  have hfin_p : IsFiniteMeasure (arcsine.withDensity fun E => (fp E : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hFL1.2
  have hfin_m : IsFiniteMeasure (arcsine.withDensity fun E => (fm E : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hFL1.neg.2
  have heq : μ + arcsine.withDensity (fun E => (fm E : ℝ≥0∞)) =
      arcsine.withDensity (fun E => (fp E : ℝ≥0∞)) := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    have hgi : ∀ (h : ℝ → ℝ), Integrable h arcsine → Integrable (fun E => g E * h E) arcsine :=
      fun h hh => hh.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun E => g.norm_coe_le_norm E)
    rw [integral_add_measure (BoundedContinuousFunction.integrable μ g)
      (BoundedContinuousFunction.integrable _ g),
      integral_withDensity_eq_integral_smul hfm, integral_withDensity_eq_integral_smul hfp, hbcf g]
    simp only [NNReal.smul_def, smul_eq_mul, fp, fm, Real.coe_toNNReal']
    rw [← integral_add (hgi F hFL1) ?_, ]
    · congr 1; ext E
      rcases le_total 0 (F E) with h | h
      · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
      · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · refine (hgi (fun E => max (-F E) 0) ?_).congr (Filter.Eventually.of_forall fun E => ?_)
      · exact hFL1.neg.pos_part
      · simp [mul_comm]
  -- the negative part vanishes `ρ`-a.e.
  have hneg : ∀ᵐ E ∂arcsine, 0 ≤ F E := by
    set S := {E | F E < 0}
    have hS : MeasurableSet S := measurableSet_lt hFm.measurable measurable_const
    have h1 : arcsine.withDensity (fun E => (fp E : ℝ≥0∞)) S = 0 := by
      rw [withDensity_apply _ hS]
      apply setLIntegral_eq_zero hS
      intro E hE
      have hle : F E ≤ 0 := le_of_lt hE
      simp [fp, hle]
    have h2 : arcsine.withDensity (fun E => (fm E : ℝ≥0∞)) S = 0 := by
      refine le_antisymm ?_ (zero_le)
      rw [← h1, ← heq, add_apply]
      exact le_add_self
    rw [withDensity_apply _ hS, lintegral_eq_zero_iff (by fun_prop)] at h2
    rw [Filter.EventuallyEq, ae_restrict_iff' hS] at h2
    filter_upwards [h2] with E hE
    by_contra hlt
    push Not at hlt
    have := hE hlt
    simp [fm] at this
    linarith
  have hfm0 : arcsine.withDensity (fun E => (fm E : ℝ≥0∞)) = 0 := by
    rw [← withDensity_zero]
    apply withDensity_congr_ae
    filter_upwards [hneg] with E hE
    simp [fm, hE]
  rw [hfm0, add_zero] at heq
  -- the density
  refine ⟨fun E => max (F E) 0, hFm.measurable.max measurable_const, fun E => le_max_right _ _,
    ?_, ?_, ?_⟩
  · exact hFL2.mono (hFm.measurable.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun E => by
        simp only [Real.norm_eq_abs]
        rcases le_total 0 (F E) with h | h
        · simp [max_eq_left h]
        · simp [max_eq_right h])
  · rw [heq]; congr 1; ext E
    simp only [fp, ENNReal.ofReal]
    congr 1; ext
    simp only [Real.coe_toNNReal']
    rw [max_eq_left (le_max_right _ _)]
  · -- Parseval
    have hP := parseval Fl
    simp_rw [hinner] at hP
    have hnorm : ‖Fl‖ ^ 2 = ∫ E, F E ^ 2 ∂arcsine := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun E => ?_)
      simp [sq, hFdef]
    have hsq : ∫ E, (max (F E) 0) ^ 2 ∂arcsine = ∫ E, F E ^ 2 ∂arcsine := by
      refine integral_congr_ae ?_
      filter_upwards [hneg] with E hE
      simp [max_eq_left hE]
    rw [hsq, ← hnorm, ← hP.tsum_eq, (summable_coeffSeq_sq μ hc).tsum_eq_zero_add]
    simp only [coeffSeq, normConst, ite_true, one_mul, chebCoeff_zero, one_pow,
      Nat.succ_ne_zero, ite_false, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [tsum_mul_left]

end ThomChebyshev
