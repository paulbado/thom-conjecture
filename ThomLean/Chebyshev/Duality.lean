import ThomLean.Chebyshev.Lebesgue
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.Regular

/-!
# A duality criterion for absolute continuity

`ac_of_poly_Lq_bound` : let `μ` be a finite measure carried by `[-4,4]` and `1 ≤ q`. If
`|∫ P(E/4) dμ| ≤ K ‖P(·/4)‖_{L^q(ρ)}` for every real polynomial `P` (`ρ` the arcsine law), then
`μ ≪ Lebesgue`.

For `q = 2` the hypothesis is equivalent to an `L²(ρ)` density (the principal target).
For `q > 2` it is the dual form of an `L^p(ρ)` density with `p = q/(q-1) < 2`, which is the
regime suggested by the numerics. The proof uses only Weierstrass approximation, Urysohn's
lemma and the regularity of finite Borel measures on `ℝ`; no `L^p` duality theory is needed.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Real Set

/-- **Quantitative form of the duality criterion**: a polynomial `L^q(ρ)` bound gives
`μ(C) ≤ δ·B` whenever `C ⊆ U`, `C` compact, `U` open and `ρ(U) ≤ δ^q`. -/
theorem measureReal_compact_le_of_poly_Lq_bound (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) {q K : ℝ}
    (hq : 1 ≤ q)
    (hK : ∀ p : ℝ[X], |∫ E, polyFun p E ∂μ| ≤ K * (∫ E, |polyFun p E| ^ q ∂arcsine) ^ (1 / q)) :
    ∀ C U : Set ℝ, IsCompact C → IsOpen U → C ⊆ U → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      arcsine.real U ≤ δ ^ q → μ.real C ≤ δ * (max K 0 * (2 ^ q + 1) ^ (1 / q) + μ.real univ) := by
  have hq0 : 0 < q := by linarith
  set K' := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hK' : ∀ p : ℝ[X],
      ∫ E, polyFun p E ∂μ ≤ K' * (∫ E, |polyFun p E| ^ q ∂arcsine) ^ (1 / q) := fun p =>
    (le_abs_self _).trans ((hK p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (integral_nonneg fun E => by positivity) _)))
  set m := μ.real univ
  have hm : 0 ≤ m := measureReal_nonneg
  have hcarr : ∀ᵐ E ∂μ, E ∈ Icc (-4 : ℝ) 4 := ae_mem_of_carried hμ
  intro C U hC hU hCU δ hδ hδ1 hρU
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isCompact hC hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hCU)
  set g : ℝ → ℝ := fun E => 1 - f E with hgdef
  have hgc : Continuous g := continuous_const.sub f.continuous
  have hgC : ∀ E ∈ C, g E = 1 := fun E hE => by simp [g, hf0 hE]
  have hgU : ∀ E, E ∉ U → g E = 0 := fun E hE => by
    have : f E = 1 := hf1 (show E ∈ Uᶜ from hE)
    simp [g, this]
  have hg01 : ∀ E, 0 ≤ g E ∧ g E ≤ 1 := fun E =>
    ⟨by simp only [g]; linarith [(hf01 E).2], by simp only [g]; linarith [(hf01 E).1]⟩
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => g (4 * x))
    (hgc.comp (continuous_const.mul continuous_id)).continuousOn δ hδ
  have hPE : ∀ E ∈ Icc (-4 : ℝ) 4, |polyFun P E - g E| < δ := by
    intro E hE
    have := hP (E / 4) ⟨by linarith [hE.1], by linarith [hE.2]⟩
    simpa [polyFun, show 4 * (E / 4) = E by ring] using this
  have hPint : Integrable (polyFun P) μ := integrable_of_continuous hμ (continuous_polyFun P)
  have hgint : Integrable g μ := integrable_of_continuous hμ hgc
  -- (1) `μ(C) ≤ ∫ g dμ`
  have h1 : μ.real C ≤ ∫ E, g E ∂μ := by
    rw [← integral_indicator_one hC.measurableSet]
    refine integral_mono ((integrable_indicator_iff hC.measurableSet).mpr
      (integrableOn_const (measure_ne_top _ _))) hgint fun E => ?_
    by_cases hE : E ∈ C
    · simp [hE, hgC E hE]
    · simp [hE, (hg01 E).1]
  -- (2) `∫ g dμ ≤ ∫ P dμ + δ m`
  have h2 : ∫ E, g E ∂μ ≤ ∫ E, polyFun P E ∂μ + δ * m := by
    have : ∫ E, g E ∂μ ≤ ∫ E, (polyFun P E + δ) ∂μ :=
      integral_mono_ae hgint (hPint.add (integrable_const δ)) (hcarr.mono fun E hE => by
        have := hPE E hE; rw [abs_lt] at this; linarith)
    rwa [integral_add hPint (integrable_const δ), integral_const, smul_eq_mul, mul_comm] at this
  -- (3) `∫ |P|^q dρ ≤ (2^q + 1) δ^q`
  have hδq : 0 ≤ δ ^ q := Real.rpow_nonneg hδ.le q
  have h3 : ∫ E, |polyFun P E| ^ q ∂arcsine ≤ (2 ^ q + 1) * δ ^ q := by
    have hpt : ∀ E ∈ Icc (-4 : ℝ) 4,
        |polyFun P E| ^ q ≤ U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q := by
      intro E hE
      have hb := hPE E hE
      by_cases hU' : E ∈ U
      · have h2' : |polyFun P E| ≤ 2 := by
          rw [abs_lt] at hb; rw [abs_le]
          constructor <;> linarith [(hg01 E).1, (hg01 E).2]
        rw [indicator_of_mem hU']
        have := Real.rpow_le_rpow (abs_nonneg _) h2' hq0.le
        linarith
      · have hg := hgU E hU'
        have h2' : |polyFun P E| ≤ δ := by rw [hg, sub_zero] at hb; exact hb.le
        rw [indicator_of_notMem hU', zero_add]
        exact Real.rpow_le_rpow (abs_nonneg _) h2' hq0.le
    have hint1 : Integrable (fun E => |polyFun P E| ^ q) arcsine :=
      integrable_of_continuous arcsine_compl_Icc
        ((continuous_polyFun P).abs.rpow_const fun _ => Or.inr hq0.le)
    have hint2 : Integrable (fun E => U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q) arcsine :=
      ((integrable_indicator_iff hU.measurableSet).mpr
        (integrableOn_const (measure_ne_top _ _))).add (integrable_const _)
    calc ∫ E, |polyFun P E| ^ q ∂arcsine
        ≤ ∫ E, (U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q) ∂arcsine :=
          integral_mono_ae hint1 hint2 (ae_arcsine_mem_Icc.mono fun E hE => hpt E hE)
      _ = 2 ^ q * arcsine.real U + δ ^ q := by
          rw [integral_add ((integrable_indicator_iff hU.measurableSet).mpr
            (integrableOn_const (measure_ne_top _ _))) (integrable_const _),
            integral_indicator hU.measurableSet, setIntegral_const, integral_const]
          simp [smul_eq_mul, mul_comm]
      _ ≤ 2 ^ q * δ ^ q + δ ^ q := by gcongr
      _ = (2 ^ q + 1) * δ ^ q := by ring
  have h4 : (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) ≤ (2 ^ q + 1) ^ (1 / q) * δ := by
    calc (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q)
        ≤ ((2 ^ q + 1) * δ ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow (integral_nonneg fun E => by positivity) h3 (by positivity)
      _ = (2 ^ q + 1) ^ (1 / q) * δ := by
          rw [Real.mul_rpow (by positivity) hδq, ← Real.rpow_mul hδ.le,
            mul_one_div_cancel hq0.ne', Real.rpow_one]
  calc μ.real C ≤ ∫ E, g E ∂μ := h1
    _ ≤ ∫ E, polyFun P E ∂μ + δ * m := h2
    _ ≤ K' * (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) + δ * m := by linarith [hK' P]
    _ ≤ K' * ((2 ^ q + 1) ^ (1 / q) * δ) + δ * m := by gcongr
    _ = δ * (K' * (2 ^ q + 1) ^ (1 / q) + m) := by ring

/-- **Duality criterion.** A polynomial `L^q(arcsine)` bound on the moment functional implies
absolute continuity. -/
theorem ac_of_poly_Lq_bound (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) {q K : ℝ}
    (hq : 1 ≤ q)
    (hK : ∀ p : ℝ[X], |∫ E, polyFun p E ∂μ| ≤ K * (∫ E, |polyFun p E| ^ q ∂arcsine) ^ (1 / q)) :
    μ ≪ volume := by
  have hq0 : 0 < q := by linarith
  set K' := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hK' : ∀ p : ℝ[X],
      ∫ E, polyFun p E ∂μ ≤ K' * (∫ E, |polyFun p E| ^ q ∂arcsine) ^ (1 / q) := fun p =>
    (le_abs_self _).trans ((hK p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (integral_nonneg fun E => by positivity) _)))
  set m := μ.real univ
  have hm : 0 ≤ m := measureReal_nonneg
  have hcarr : ∀ᵐ E ∂μ, E ∈ Icc (-4 : ℝ) 4 := ae_mem_of_carried hμ
  -- the key estimate for a compact set inside an open set of small arcsine measure
  have key : ∀ C U : Set ℝ, IsCompact C → IsOpen U → C ⊆ U → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      arcsine.real U ≤ δ ^ q → μ.real C ≤ δ * (K' * (2 ^ q + 1) ^ (1 / q) + m) := by
    intro C U hC hU hCU δ hδ hδ1 hρU
    obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isCompact hC hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hCU)
    set g : ℝ → ℝ := fun E => 1 - f E with hgdef
    have hgc : Continuous g := continuous_const.sub f.continuous
    have hgC : ∀ E ∈ C, g E = 1 := fun E hE => by simp [g, hf0 hE]
    have hgU : ∀ E, E ∉ U → g E = 0 := fun E hE => by
      have : f E = 1 := hf1 (show E ∈ Uᶜ from hE)
      simp [g, this]
    have hg01 : ∀ E, 0 ≤ g E ∧ g E ≤ 1 := fun E =>
      ⟨by simp only [g]; linarith [(hf01 E).2], by simp only [g]; linarith [(hf01 E).1]⟩
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => g (4 * x))
      (hgc.comp (continuous_const.mul continuous_id)).continuousOn δ hδ
    have hPE : ∀ E ∈ Icc (-4 : ℝ) 4, |polyFun P E - g E| < δ := by
      intro E hE
      have := hP (E / 4) ⟨by linarith [hE.1], by linarith [hE.2]⟩
      simpa [polyFun, show 4 * (E / 4) = E by ring] using this
    have hPint : Integrable (polyFun P) μ := integrable_of_continuous hμ (continuous_polyFun P)
    have hgint : Integrable g μ := integrable_of_continuous hμ hgc
    -- (1) `μ(C) ≤ ∫ g dμ`
    have h1 : μ.real C ≤ ∫ E, g E ∂μ := by
      rw [← integral_indicator_one hC.measurableSet]
      refine integral_mono ((integrable_indicator_iff hC.measurableSet).mpr
        (integrableOn_const (measure_ne_top _ _))) hgint fun E => ?_
      by_cases hE : E ∈ C
      · simp [hE, hgC E hE]
      · simp [hE, (hg01 E).1]
    -- (2) `∫ g dμ ≤ ∫ P dμ + δ m`
    have h2 : ∫ E, g E ∂μ ≤ ∫ E, polyFun P E ∂μ + δ * m := by
      have : ∫ E, g E ∂μ ≤ ∫ E, (polyFun P E + δ) ∂μ :=
        integral_mono_ae hgint (hPint.add (integrable_const δ)) (hcarr.mono fun E hE => by
          have := hPE E hE; rw [abs_lt] at this; linarith)
      rwa [integral_add hPint (integrable_const δ), integral_const, smul_eq_mul, mul_comm] at this
    -- (3) `∫ |P|^q dρ ≤ (2^q + 1) δ^q`
    have hδq : 0 ≤ δ ^ q := Real.rpow_nonneg hδ.le q
    have h3 : ∫ E, |polyFun P E| ^ q ∂arcsine ≤ (2 ^ q + 1) * δ ^ q := by
      have hpt : ∀ E ∈ Icc (-4 : ℝ) 4,
          |polyFun P E| ^ q ≤ U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q := by
        intro E hE
        have hb := hPE E hE
        by_cases hU' : E ∈ U
        · have h2' : |polyFun P E| ≤ 2 := by
            rw [abs_lt] at hb; rw [abs_le]
            constructor <;> linarith [(hg01 E).1, (hg01 E).2]
          rw [indicator_of_mem hU']
          have := Real.rpow_le_rpow (abs_nonneg _) h2' hq0.le
          linarith
        · have hg := hgU E hU'
          have h2' : |polyFun P E| ≤ δ := by rw [hg, sub_zero] at hb; exact hb.le
          rw [indicator_of_notMem hU', zero_add]
          exact Real.rpow_le_rpow (abs_nonneg _) h2' hq0.le
      have hint1 : Integrable (fun E => |polyFun P E| ^ q) arcsine :=
        integrable_of_continuous arcsine_compl_Icc
          ((continuous_polyFun P).abs.rpow_const fun _ => Or.inr hq0.le)
      have hint2 : Integrable (fun E => U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q) arcsine :=
        ((integrable_indicator_iff hU.measurableSet).mpr
          (integrableOn_const (measure_ne_top _ _))).add (integrable_const _)
      calc ∫ E, |polyFun P E| ^ q ∂arcsine
          ≤ ∫ E, (U.indicator (fun _ => (2 : ℝ) ^ q) E + δ ^ q) ∂arcsine :=
            integral_mono_ae hint1 hint2 (ae_arcsine_mem_Icc.mono fun E hE => hpt E hE)
        _ = 2 ^ q * arcsine.real U + δ ^ q := by
            rw [integral_add ((integrable_indicator_iff hU.measurableSet).mpr
              (integrableOn_const (measure_ne_top _ _))) (integrable_const _),
              integral_indicator hU.measurableSet, setIntegral_const, integral_const]
            simp [smul_eq_mul, mul_comm]
        _ ≤ 2 ^ q * δ ^ q + δ ^ q := by gcongr
        _ = (2 ^ q + 1) * δ ^ q := by ring
    have h4 : (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) ≤ (2 ^ q + 1) ^ (1 / q) * δ := by
      calc (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q)
          ≤ ((2 ^ q + 1) * δ ^ q) ^ (1 / q) :=
            Real.rpow_le_rpow (integral_nonneg fun E => by positivity) h3 (by positivity)
        _ = (2 ^ q + 1) ^ (1 / q) * δ := by
            rw [Real.mul_rpow (by positivity) hδq, ← Real.rpow_mul hδ.le,
              mul_one_div_cancel hq0.ne', Real.rpow_one]
    calc μ.real C ≤ ∫ E, g E ∂μ := h1
      _ ≤ ∫ E, polyFun P E ∂μ + δ * m := h2
      _ ≤ K' * (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) + δ * m := by linarith [hK' P]
      _ ≤ K' * ((2 ^ q + 1) ^ (1 / q) * δ) + δ * m := by gcongr
      _ = δ * (K' * (2 ^ q + 1) ^ (1 / q) + m) := by ring
  -- conclusion
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  have hρA : arcsine A = 0 := arcsine_ac hvol
  set B := K' * (2 ^ q + 1) ^ (1 / q) + m + 1 with hBdef
  have hB : 0 < B := by positivity
  have hle : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → μ.real A ≤ δ * B := by
    intro δ hδ hδ1
    obtain ⟨U, hAU, hU, hρU⟩ := Set.exists_isOpen_lt_of_lt A (ENNReal.ofReal (δ ^ q))
      (by rw [hρA]; exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ q))
    obtain ⟨C, hCA, hC, hμC⟩ := hA.exists_isCompact_lt_add (μ := μ) (measure_ne_top μ A)
      (ENNReal.ofReal_pos.mpr hδ).ne'
    have hρU' : arcsine.real U ≤ δ ^ q := by
      rw [Measure.real]
      exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hδ.le q) hρU.le
    have hk := key C U hC hU (hCA.trans hAU) δ hδ hδ1 hρU'
    have hAC : μ.real A ≤ μ.real C + δ := by
      rw [Measure.real, Measure.real]
      calc (μ A).toReal ≤ (μ C + ENNReal.ofReal δ).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
              hμC.le
        _ = (μ C).toReal + δ := by
            rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
              ENNReal.toReal_ofReal hδ.le]
    rw [hBdef]; nlinarith
  have hA0 : μ.real A ≤ 0 := by
    by_contra h
    push Not at h
    set δ := min 1 (μ.real A / (2 * B))
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have h1 := hle δ hδ (min_le_left _ _)
    have h2 : δ * B ≤ μ.real A / 2 := by
      calc δ * B ≤ μ.real A / (2 * B) * B := by gcongr; exact min_le_right _ _
        _ = μ.real A / 2 := by field_simp
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp (le_antisymm hA0 measureReal_nonneg)

end ThomChebyshev
