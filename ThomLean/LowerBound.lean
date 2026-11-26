import ThomLean.FejerTarget

/-!
# Lower bounds at `E = 0`: transfer from approximants and refutation of the `L^q` targets

* `le_measureReal_of_moments` (U, generic): if probability measures `ν_Q` on `[-4,4]` eventually
  agree with `μ` on every polynomial (as the rational-flux averages `ν_Q` agree with `μ_A` in
  degree `< N_Q = 2⌈2√Q⌉`), then lower bounds on compact sets pass to the limit:
  `c ≤ ν_Q(C)` for infinitely many `Q` implies `c ≤ μ(C)`. Upper semicontinuity on compact
  sets is the correct direction for a **lower** bound on `μ_A`.
* `LogSqLowerBound`: `μ_A([-h,h]) ≥ c / log²(1/h)` for `0 < h < h₀`. This is the open estimate
  of Task 1. It is **not** proved here; it is never assumed outside the hypotheses below.
* `logSqLowerBound_of_approx` (C): it follows from the same bound for the approximants,
  frequently in `Q`, at each fixed `h`.
* `not_lqTarget_of_logSq` (C): `LogSqLowerBound ⇒ ¬ LqTarget q` for every `q ≥ 1`. The proof
  uses only `muA_le_of_lqTarget` (power decay `μ_A([-h,h]) = O(h^{1/q})`) and
  `log²(1/h) = o(h^{-s})`.
* `not_fejerTarget_of_logSq`, `not_principalTarget_of_logSq` (C): the same for every Fejér
  `L^p` target (`p > 1`) and for `PrincipalTarget`.

The weighted targets are untouched: `(E²/16) μ_A` puts mass `O(h²/log²)` near `0`.
-/

noncomputable section

namespace ThomLowerBound

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence ThomConclusions ThomFejer
open MeasureTheory Polynomial Real Set Filter Topology

/-- **Transfer of lower bounds on compact sets** from moment-matching approximants. -/
theorem le_measureReal_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (ν : ℕ → Measure ℝ) [∀ Q, IsProbabilityMeasure (ν Q)] (hν : ∀ Q, CarriedBy4 (ν Q))
    (hmom : ∀ P : ℝ[X], ∀ᶠ Q in atTop, ∫ E, polyFun P E ∂(ν Q) = ∫ E, polyFun P E ∂μ)
    {C : Set ℝ} (hC : IsCompact C) {c : ℝ} (hc : ∃ᶠ Q in atTop, c ≤ (ν Q).real C) :
    c ≤ μ.real C := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 3
  have hδ : 0 < δ := by positivity
  obtain ⟨U, hCU, hU, hμU⟩ := Set.exists_isOpen_lt_of_lt C (μ C + ENNReal.ofReal δ)
    (ENNReal.lt_add_right (measure_ne_top _ _) (ENNReal.ofReal_pos.mpr hδ).ne')
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
  obtain ⟨Q, hQc, hQm⟩ := (hc.and_eventually (hmom P)).exists
  -- `ν_Q(C) ≤ ∫ g dν_Q ≤ ∫ P dν_Q + δ`
  have hindC : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], ρ.real C ≤ ∫ E, g E ∂ρ := by
    intro ρ _
    rw [← integral_indicator_one hC.measurableSet]
    refine integral_mono ((integrable_indicator_iff hC.measurableSet).mpr
      (integrableOn_const (measure_ne_top _ _))) ?_ fun E => ?_
    · exact (integrable_const (1 : ℝ)).mono' hgc.aestronglyMeasurable
        (ae_of_all _ fun E => by rw [Real.norm_eq_abs, abs_of_nonneg (hg01 E).1]; exact (hg01 E).2)
    · by_cases hE : E ∈ C
      · simp [hE, hgC E hE]
      · simp [hE, (hg01 E).1]
  have h1 : (ν Q).real C ≤ ∫ E, polyFun P E ∂(ν Q) + δ := by
    have hPint : Integrable (polyFun P) (ν Q) := integrable_of_continuous (hν Q) (continuous_polyFun P)
    have hgint : Integrable g (ν Q) := integrable_of_continuous (hν Q) hgc
    have : ∫ E, g E ∂(ν Q) ≤ ∫ E, (polyFun P E + δ) ∂(ν Q) :=
      integral_mono_ae hgint (hPint.add (integrable_const δ))
        ((ae_mem_of_carried (hν Q)).mono fun E hE => by
          have := hPE E hE; rw [abs_lt] at this; linarith)
    rw [integral_add hPint (integrable_const δ), integral_const, smul_eq_mul, probReal_univ,
      one_mul] at this
    linarith [hindC (ν Q)]
  -- `∫ P dμ ≤ ∫ g dμ + δ ≤ μ(U) + δ`
  have h2 : ∫ E, polyFun P E ∂μ ≤ μ.real U + δ := by
    have hPint : Integrable (polyFun P) μ := integrable_of_continuous hμ (continuous_polyFun P)
    have hgint : Integrable g μ := integrable_of_continuous hμ hgc
    have ha : ∫ E, polyFun P E ∂μ ≤ ∫ E, (g E + δ) ∂μ :=
      integral_mono_ae hPint (hgint.add (integrable_const δ))
        ((ae_mem_of_carried hμ).mono fun E hE => by
          have := hPE E hE; rw [abs_lt] at this; linarith)
    rw [integral_add hgint (integrable_const δ), integral_const, smul_eq_mul, probReal_univ,
      one_mul] at ha
    have hb : ∫ E, g E ∂μ ≤ μ.real U := by
      rw [← integral_indicator_one hU.measurableSet]
      refine integral_mono hgint ((integrable_indicator_iff hU.measurableSet).mpr
        (integrableOn_const (measure_ne_top _ _))) fun E => ?_
      by_cases hE : E ∈ U
      · simp [hE, (hg01 E).2]
      · simp [hE, hgU E hE]
    linarith
  have h3 : μ.real U ≤ μ.real C + δ := by
    rw [Measure.real, Measure.real]
    calc (μ U).toReal ≤ (μ C + ENNReal.ofReal δ).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
            hμU.le
      _ = (μ C).toReal + δ := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hδ.le]
  have : δ + δ + δ = ε := by simp only [δ]; ring
  linarith

/-- **The open estimate of Task 1**: logarithmic concentration of `μ_A` at `0`. -/
def LogSqLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
    c / log h ^ 2 ≤ muA.real (Icc (-h) h)

/-- `LogSqLowerBound` follows from the same bound for moment-matching approximants. -/
theorem logSqLowerBound_of_approx (ν : ℕ → Measure ℝ) [∀ Q, IsProbabilityMeasure (ν Q)]
    (hν : ∀ Q, CarriedBy4 (ν Q))
    (hmom : ∀ P : ℝ[X], ∀ᶠ Q in atTop, ∫ E, polyFun P E ∂(ν Q) = ∫ E, polyFun P E ∂muA)
    (h : ∃ c : ℝ, 0 < c ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ᶠ Q in atTop, c / log h ^ 2 ≤ (ν Q).real (Icc (-h) h)) :
    LogSqLowerBound := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨c, hc, h₀, hh₀, hb⟩ := h
  exact ⟨c, hc, h₀, hh₀, fun h hh hh' =>
    le_measureReal_of_moments muA isSpectralMeasureA_muA.carried ν hν hmom isCompact_Icc
      (hb h hh hh')⟩

/-- The arcsine law of a small symmetric interval is `O(h)`. -/
lemma arcsine_Ioo_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    arcsine.real (Ioo (-(2 * h)) (2 * h)) ≤ M * (4 * h) := by
  obtain ⟨M, hM0, hM⟩ := arcDens_le (a := -2) (b := 2) (by norm_num) (by norm_num)
  refine ⟨M, hM0, fun h hh hh1 => ?_⟩
  have hsub : Ioo (-(2 * h)) (2 * h) ⊆ Icc (-2 : ℝ) 2 := fun E hE =>
    ⟨by linarith [hE.1], by linarith [hE.2]⟩
  have hle : arcsine (Ioo (-(2 * h)) (2 * h)) ≤ ENNReal.ofReal (M * (4 * h)) := by
    rw [arcsine_eq_withDensity, withDensity_apply _ measurableSet_Ioo]
    calc ∫⁻ E in Ioo (-(2 * h)) (2 * h), ENNReal.ofReal (arcDens E)
        ≤ ∫⁻ _ in Ioo (-(2 * h)) (2 * h), ENNReal.ofReal M :=
          setLIntegral_mono measurable_const fun E hE => ENNReal.ofReal_le_ofReal (hM E (hsub hE))
      _ = ENNReal.ofReal M * volume (Ioo (-(2 * h)) (2 * h)) := setLIntegral_const _ _
      _ = ENNReal.ofReal (M * (4 * h)) := by
          rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hM0]; congr 1; ring
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- **The logarithmic lower bound refutes every unweighted `L^q` target.** -/
theorem not_lqTarget_of_logSq (hlog : LogSqLowerBound) {q : ℝ} (hq : 1 ≤ q) : ¬ LqTarget q := by
  intro hL
  obtain ⟨B, hB⟩ := muA_le_of_lqTarget hq hL
  obtain ⟨c, hc, h₀, hh₀, hlow⟩ := hlog
  obtain ⟨M, hM0, hM⟩ := arcsine_Ioo_le
  have hq0 : 0 < q := by linarith
  set r := 1 / q
  have hr : 0 < r := by positivity
  set B' := max B 0
  -- the constant in `c ≤ K x^{-r/2}`
  set K := B' * (M * 4) ^ r * (4 / r) ^ 2
  have hK0 : 0 ≤ K := by
    have : 0 ≤ B' := le_max_right _ _
    positivity
  -- choose `x = 1/h` large
  have hev : ∀ᶠ x : ℝ in atTop, max 2 (1 / h₀) < x ∧ K / c < x ^ (r / 2) :=
    (eventually_gt_atTop _).and ((tendsto_rpow_atTop (by positivity)).eventually_gt_atTop _)
  obtain ⟨x, hx1, hx2⟩ := hev.exists
  have hx2' : 2 < x := lt_of_le_of_lt (le_max_left _ _) hx1
  have hx0 : 0 < x := by linarith
  set h := 1 / x
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [div_le_one hx0]; linarith
  have hhh₀ : h < h₀ := by
    have : 1 / h₀ < x := lt_of_le_of_lt (le_max_right _ _) hx1
    rw [div_lt_iff₀ hh₀] at this
    simp only [h]; rw [div_lt_iff₀ hx0]; linarith
  -- upper bound from `LqTarget`
  have hup : muA.real (Icc (-h) h) ≤ B' * (M * 4) ^ r * h ^ r := by
    have h1 := hB (Icc (-h) h) (Ioo (-(2 * h)) (2 * h)) isCompact_Icc isOpen_Ioo (fun E hE =>
      ⟨by linarith [hE.1], by linarith [hE.2]⟩)
    have hρ0 : 0 ≤ arcsine.real (Ioo (-(2 * h)) (2 * h)) := measureReal_nonneg
    calc muA.real (Icc (-h) h) ≤ B * arcsine.real (Ioo (-(2 * h)) (2 * h)) ^ r := h1
      _ ≤ B' * arcsine.real (Ioo (-(2 * h)) (2 * h)) ^ r :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hρ0 _)
      _ ≤ B' * (M * (4 * h)) ^ r := by
          have hB'0 : 0 ≤ B' := le_max_right _ _
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ0 (hM h hh hh1) hr.le) hB'0
      _ = B' * (M * 4) ^ r * h ^ r := by
          rw [show M * (4 * h) = (M * 4) * h by ring, Real.mul_rpow (by positivity) hh.le]; ring
  -- `log² h ≤ (4/r)² x^{r/2}`
  have hlogx : log h ^ 2 = log x ^ 2 := by
    simp only [h, one_div, Real.log_inv, neg_sq]
  have hlx0 : 0 < log x := log_pos (by linarith)
  have hlx : log x ≤ x ^ (r / 4) / (r / 4) := log_le_rpow_div hx0.le (by positivity)
  have hlx2 : log x ^ 2 ≤ (4 / r) ^ 2 * x ^ (r / 2) := by
    have h1 : log x ^ 2 ≤ (x ^ (r / 4) / (r / 4)) ^ 2 := pow_le_pow_left₀ hlx0.le hlx 2
    have h2 : (x ^ (r / 4)) ^ 2 = x ^ (r / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
    calc log x ^ 2 ≤ (x ^ (r / 4) / (r / 4)) ^ 2 := h1
      _ = (4 / r) ^ 2 * (x ^ (r / 4)) ^ 2 := by field_simp
      _ = (4 / r) ^ 2 * x ^ (r / 2) := by rw [h2]
  have hlow' := hlow h hh hhh₀
  have hL0 : 0 < log h ^ 2 := by rw [hlogx]; positivity
  -- combine: `c ≤ muA(I) log² h ≤ K h^r x^{r/2} = K x^{-r/2}`
  have hhr : h ^ r = (x ^ r)⁻¹ := by simp only [h, one_div]; rw [Real.inv_rpow hx0.le]
  have hxr : x ^ r = x ^ (r / 2) * x ^ (r / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxr2 : 0 < x ^ (r / 2) := Real.rpow_pos_of_pos hx0 _
  have hc1 : c ≤ muA.real (Icc (-h) h) * log h ^ 2 := by
    rwa [div_le_iff₀ hL0] at hlow'
  have hc2 : c ≤ K / x ^ (r / 2) := by
    calc c ≤ muA.real (Icc (-h) h) * log h ^ 2 := hc1
      _ ≤ (B' * (M * 4) ^ r * h ^ r) * ((4 / r) ^ 2 * x ^ (r / 2)) := by
          rw [hlogx]
          exact mul_le_mul hup hlx2 (by positivity) (by
            have : 0 ≤ B' := le_max_right _ _
            positivity)
      _ = K / x ^ (r / 2) := by
          rw [hhr, hxr]; simp only [K]; field_simp
  have : K < x ^ (r / 2) * c := by rwa [div_lt_iff₀ hc] at hx2
  rw [le_div_iff₀ hxr2] at hc2
  linarith

/-- The logarithmic lower bound refutes every Fejér `L^p` target, `p > 1`. -/
theorem not_fejerTarget_of_logSq (hlog : LogSqLowerBound) {p : ℝ} (hp : 1 < p) :
    ¬ FejerTarget p := fun h => by
  have hpq := Real.HolderConjugate.conjExponent hp
  exact not_lqTarget_of_logSq hlog hpq.symm.lt.le (lqTarget_of_fejerTarget hpq h)

/-- The logarithmic lower bound refutes the principal (unweighted `L²`) target. -/
theorem not_principalTarget_of_logSq (hlog : LogSqLowerBound) : ¬ PrincipalTarget := fun h => by
  obtain ⟨f, hfm, hf0, hf2, hμf⟩ := (principalTarget_iff_L2 isSpectralMeasureA_muA).mp h
  have hf2' : MemLp f (ENNReal.ofReal 2) arcsine := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  exact not_lqTarget_of_logSq hlog one_le_two
    (lqTarget_of_Lp_density Real.HolderConjugate.two_two hfm hf0 hf2' hμf)

end ThomLowerBound
