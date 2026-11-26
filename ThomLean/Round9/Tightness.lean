import ThomLean.WeightedL2
import ThomLean.LowerBound

/-!
# Round 9, Task 4: local tightness of approximants implies absolute continuity

This file contains the *abstract* (measure-theoretic) half of the truncated-coarea route. The
analytic half, the truncated coarea inequality for the continuous-flux Dirichlet model
`σ_L(B) ≤ K |B| + P_L(E ∈ B, R_L > K)`, is a paper proof (see `round9_report.md`); it is not
formalized, and no instance of the hypothesis `LocalTightBound` is proved here.

* `measureReal_open_le_of_moments` (U): if probability measures `ν_Q` on `[-4,4]` have
  polynomial moments converging to those of `μ`, then upper bounds on an open set pass to the
  limit: `ν_Q(U) ≤ c` eventually implies `μ(U) ≤ c` (lower semicontinuity on open sets).
* `LocalTightBound ν` : for each `ε, η > 0` there is `K` with
  `ν_Q(U) ≤ K |U| + η` eventually, for every open `U ⊆ {ε ≤ |E|} ∩ (-5,5)`.
  This is exactly what the truncated coarea inequality plus local tightness
  `lim_K limsup_L P_L(R_L > K, |E| ≥ ε) = 0` provide (with `η` the tail probability).
* `muA_ac_of_localTight` (C): moment convergence to `μ_A` plus `LocalTightBound` imply
  `μ_A ≪ Lebesgue`. No uniform bound on `E[log R_L]` is required.
-/

noncomputable section

namespace ThomRound9

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence ThomConclusions ThomFejer
open ThomWeightedL2
open MeasureTheory Polynomial Real Set Filter Topology

/-- **Upper bounds on open sets pass to moment limits.** -/
theorem measureReal_open_le_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CarriedBy4 μ) (ν : ℕ → Measure ℝ) [∀ Q, IsProbabilityMeasure (ν Q)]
    (hν : ∀ Q, CarriedBy4 (ν Q))
    (hmom : ∀ P : ℝ[X], Tendsto (fun Q => ∫ E, polyFun P E ∂(ν Q)) atTop
      (𝓝 (∫ E, polyFun P E ∂μ)))
    {U : Set ℝ} (hU : IsOpen U) {c : ℝ} (hc : ∀ᶠ Q in atTop, (ν Q).real U ≤ c) :
    μ.real U ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 4
  have hδ : 0 < δ := by positivity
  -- inner regularity: a compact `C ⊆ U` with `μ U < μ C + δ`
  obtain ⟨C, hCU, hC, hμC⟩ := hU.measurableSet.exists_isCompact_lt_add (μ := μ)
    (measure_ne_top _ _) (ENNReal.ofReal_pos.mpr hδ).ne'
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
  have hev : ∀ᶠ Q in atTop, ∫ E, polyFun P E ∂μ < ∫ E, polyFun P E ∂(ν Q) + δ := by
    have := (hmom P).eventually (Ioo_mem_nhds (show ∫ E, polyFun P E ∂μ - δ <
      ∫ E, polyFun P E ∂μ by linarith) (show ∫ E, polyFun P E ∂μ <
      ∫ E, polyFun P E ∂μ + δ by linarith))
    filter_upwards [this] with Q hQ
    linarith [hQ.1]
  obtain ⟨Q, hQc, hQm⟩ := (hc.and hev).exists
  -- `μ(C) ≤ ∫ g dμ ≤ ∫ P dμ + δ`
  have hgint : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], Integrable g ρ := fun ρ _ =>
    (integrable_const (1 : ℝ)).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun E => by rw [Real.norm_eq_abs, abs_of_nonneg (hg01 E).1]; exact (hg01 E).2)
  have hC1 : μ.real C ≤ ∫ E, g E ∂μ := by
    rw [← integral_indicator_one hC.measurableSet]
    refine integral_mono ((integrable_indicator_iff hC.measurableSet).mpr
      (integrableOn_const (measure_ne_top _ _))) (hgint μ) fun E => ?_
    by_cases hE : E ∈ C
    · simp [hE, hgC E hE]
    · simp [hE, (hg01 E).1]
  have hC2 : ∫ E, g E ∂μ ≤ ∫ E, polyFun P E ∂μ + δ := by
    have hPint : Integrable (polyFun P) μ := integrable_of_continuous hμ (continuous_polyFun P)
    have : ∫ E, g E ∂μ ≤ ∫ E, (polyFun P E + δ) ∂μ :=
      integral_mono_ae (hgint μ) (hPint.add (integrable_const δ))
        ((ae_mem_of_carried hμ).mono fun E hE => by
          have := hPE E hE; rw [abs_lt] at this; linarith)
    rw [integral_add hPint (integrable_const δ), integral_const, smul_eq_mul, probReal_univ,
      one_mul] at this
    exact this
  -- `∫ P dν_Q ≤ ∫ g dν_Q + δ ≤ ν_Q(U) + δ`
  have hQ1 : ∫ E, polyFun P E ∂(ν Q) ≤ (ν Q).real U + δ := by
    have hPint : Integrable (polyFun P) (ν Q) :=
      integrable_of_continuous (hν Q) (continuous_polyFun P)
    have ha : ∫ E, polyFun P E ∂(ν Q) ≤ ∫ E, (g E + δ) ∂(ν Q) :=
      integral_mono_ae hPint ((hgint (ν Q)).add (integrable_const δ))
        ((ae_mem_of_carried (hν Q)).mono fun E hE => by
          have := hPE E hE; rw [abs_lt] at this; linarith)
    rw [integral_add (hgint (ν Q)) (integrable_const δ), integral_const, smul_eq_mul,
      probReal_univ, one_mul] at ha
    have hb : ∫ E, g E ∂(ν Q) ≤ (ν Q).real U := by
      rw [← integral_indicator_one hU.measurableSet]
      refine integral_mono (hgint (ν Q)) ((integrable_indicator_iff hU.measurableSet).mpr
        (integrableOn_const (measure_ne_top _ _))) fun E => ?_
      by_cases hE : E ∈ U
      · simp [hE, (hg01 E).2]
      · simp [hE, hgU E hE]
    linarith
  have hUC : μ.real U ≤ μ.real C + δ := by
    rw [Measure.real, Measure.real]
    calc (μ U).toReal ≤ (μ C + ENNReal.ofReal δ).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
            hμC.le
      _ = (μ C).toReal + δ := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hδ.le]
  have : δ + δ + δ + δ = ε := by simp only [δ]; ring
  linarith

/-- **Local tightness bound** for a sequence of approximants: the conclusion of the truncated
coarea inequality combined with local tightness of the velocity ratios. -/
def LocalTightBound (ν : ℕ → Measure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ U : Set ℝ, IsOpen U →
    U ⊆ {E | ε ≤ |E|} ∩ Ioo (-5) 5 → ∀ᶠ Q in atTop, (ν Q).real U ≤ K * volume.real U + η

/-- **Criterion (C).** Moment convergence to `μ_A` plus `LocalTightBound` give `μ_A ≪ Leb`. -/
theorem muA_ac_of_localTight (ν : ℕ → Measure ℝ) [∀ Q, IsProbabilityMeasure (ν Q)]
    (hν : ∀ Q, CarriedBy4 (ν Q))
    (hmom : ∀ P : ℝ[X], Tendsto (fun Q => ∫ E, polyFun P E ∂(ν Q)) atTop
      (𝓝 (∫ E, polyFun P E ∂muA)))
    (htight : LocalTightBound ν) : muA ≪ volume := by
  have hprob := isSpectralMeasureA_muA.isProb
  have hcar := isSpectralMeasureA_muA.carried
  rw [muA_ac_iff_local]
  intro ε hε
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  rw [Measure.restrict_apply hA]
  set B := A ∩ {E | ε ≤ |E|} ∩ Icc (-4 : ℝ) 4 with hBdef
  have hAB : muA (A ∩ {E | ε ≤ |E|}) = muA B := by
    have h1 : A ∩ {E | ε ≤ |E|} ⊆ B ∪ (Icc (-4 : ℝ) 4)ᶜ := by
      intro E hE
      by_cases h4 : E ∈ Icc (-4 : ℝ) 4
      · exact Or.inl ⟨hE, h4⟩
      · exact Or.inr h4
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc muA (A ∩ {E | ε ≤ |E|}) ≤ muA (B ∪ (Icc (-4 : ℝ) 4)ᶜ) := measure_mono h1
      _ ≤ muA B + muA (Icc (-4 : ℝ) 4)ᶜ := measure_union_le _ _
      _ = muA B := by rw [show muA (Icc (-4 : ℝ) 4)ᶜ = 0 from hcar, add_zero]
  rw [hAB]
  have hBvol : volume B = 0 := measure_mono_null (inter_subset_left.trans inter_subset_left) hvol
  -- `μ_A(B) ≤ η` for every `η > 0`
  have hle : ∀ η : ℝ, 0 < η → muA.real B ≤ 2 * η := by
    intro η hη
    obtain ⟨K, hK0, hK⟩ := htight (ε / 2) (by positivity) η hη
    set δ : ℝ := η / (K + 1)
    have hδ : 0 < δ := by positivity
    obtain ⟨V, hBV, hV, hVvol⟩ := Set.exists_isOpen_lt_of_lt B (volume B + ENNReal.ofReal δ)
      (by rw [hBvol, zero_add]; exact ENNReal.ofReal_pos.mpr hδ)
    set U := V ∩ {E | ε / 2 < |E|} ∩ Ioo (-5 : ℝ) 5 with hUdef
    have hUo : IsOpen U :=
      (hV.inter (isOpen_lt continuous_const continuous_abs)).inter isOpen_Ioo
    have hUsub : U ⊆ {E | ε / 2 ≤ |E|} ∩ Ioo (-5) 5 := fun E hE =>
      ⟨show ε / 2 ≤ |E| from le_of_lt hE.1.2, hE.2⟩
    have hBU : B ⊆ U := by
      intro E hE
      refine ⟨⟨hBV hE, ?_⟩, ?_⟩
      · have : ε ≤ |E| := hE.1.2
        show ε / 2 < |E|; linarith
      · exact ⟨by linarith [hE.2.1], by linarith [hE.2.2]⟩
    have hUvol : volume.real U ≤ δ := by
      have h1 : volume U ≤ ENNReal.ofReal δ := by
        calc volume U ≤ volume V := measure_mono (inter_subset_left.trans inter_subset_left)
          _ ≤ volume B + ENNReal.ofReal δ := hVvol.le
          _ = ENNReal.ofReal δ := by rw [hBvol, zero_add]
      rw [Measure.real]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le h1
    have hμU := measureReal_open_le_of_moments muA hcar ν hν hmom hUo (hK U hUo hUsub)
    have hKd : K * δ ≤ η := by
      simp only [δ]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc muA.real B ≤ muA.real U := measureReal_mono hBU (measure_ne_top _ _)
      _ ≤ K * volume.real U + η := hμU
      _ ≤ K * δ + η := by gcongr
      _ ≤ 2 * η := by linarith
  have h0 : muA.real B = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) measureReal_nonneg
    have := hle (η / 2) (by positivity)
    linarith
  rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0

end ThomRound9
