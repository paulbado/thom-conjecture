import ThomLean.Chebyshev.Fejer
import ThomLean.Chebyshev.Dyadic
import ThomLean.Chebyshev.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.PSeries

/-!
# The Fejér relative entropy criterion

For a probability measure `μ` carried by `[-4,4]` let `F_N = fejer μ N` be its Fejér density
with respect to the arcsine law `ρ`, and

  `H_N = ∫ F_N log F_N dρ`  (`fejEnt`; `Real.log 0 = 0`, so `0 log 0 = 0`).

* `setIntegral_fejer_le` (U): `∫_U F_N dρ ≤ M ρ(U) + (H_N + 1)/log M` for every `M > 1`.
* `fejer_uniformlyIntegrable` (C): if `H_N ≤ B` for all `N`, the Fejér densities are uniformly
  integrable: `∀ ε > 0, ∃ η > 0, ∀ N U, ρ(U) ≤ η → ∫_U F_N dρ ≤ ε`.
* `ac_of_fejEnt_bounded` (C): bounded Fejér entropies imply `μ ≪ Lebesgue`.
* `fejEnt_le_of_Lp` (U): `H_N ≤ ‖F_N‖_p^p/(p-1)` for `p > 1`. Hence bounded `L^p` norms
  (`p > 1`) imply bounded entropy: the entropy criterion contains every `L^p` criterion.
* `entropy_strictly_weaker` (U): the dyadic step profile with values `v_k = 2^k/k³` on
  `[2^{-k-1}, 2^{-k})` (masses `1/(2k³)`) has convergent entropy series and divergent `L^p` series
  for **every** `p > 1`. It is the discrete form of the integrable singularity
  `f(x) ≍ 1/(x log³(1/x))`, the profile suggested at `E = 0` for `μ_A` by the round-4 numerics.

(U) = unconditional, (C) = conditional criterion.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Real Set Filter Topology Polynomial

/-- The Fejér relative entropy `H_N = ∫ F_N log F_N dρ`. -/
def fejEnt (μ : Measure ℝ) (N : ℕ) : ℝ := ∫ E, fejer μ N E * log (fejer μ N E) ∂arcsine

lemma mul_log_add_one_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * log x + 1 := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have h1 := one_sub_inv_le_log_of_pos h
    have h2 : x * (1 - x⁻¹) ≤ x * log x := mul_le_mul_of_nonneg_left h1 h.le
    have e : x * (1 - x⁻¹) = x - 1 := by field_simp
    linarith

lemma integrable_fejer_mul_log (μ : Measure ℝ) (N : ℕ) :
    Integrable (fun E => fejer μ N E * log (fejer μ N E)) arcsine :=
  integrable_of_continuous_arcsine (Real.continuous_mul_log.comp (continuous_fejer μ N))

/-- **Entropy controls the mass of small sets** (unconditional). -/
theorem setIntegral_fejer_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (N : ℕ) {U : Set ℝ} (hU : MeasurableSet U) {M : ℝ} (hM : 1 < M) :
    ∫ E in U, fejer μ N E ∂arcsine ≤ M * arcsine.real U + (fejEnt μ N + 1) / log M := by
  have hl : 0 < log M := log_pos hM
  set F := fejer μ N
  have hF : Continuous F := continuous_fejer μ N
  have hint1 : Integrable (U.indicator F) arcsine :=
    (integrable_of_continuous_arcsine hF).indicator hU
  have hint2 : Integrable (fun E => U.indicator (fun _ => M) E +
      (F E * log (F E) + 1) / log M) arcsine :=
    ((integrable_indicator_iff hU).mpr (integrableOn_const (measure_ne_top _ _))).add
      (((integrable_fejer_mul_log μ N).add (integrable_const 1)).div_const _)
  have hpt : ∀ E ∈ Icc (-4 : ℝ) 4,
      U.indicator F E ≤ U.indicator (fun _ => M) E + (F E * log (F E) + 1) / log M := by
    intro E hE
    have hF0 : 0 ≤ F E := fejer_nonneg μ hμ N hE
    have hpos : 0 ≤ (F E * log (F E) + 1) / log M := div_nonneg (mul_log_add_one_nonneg hF0) hl.le
    by_cases hEU : E ∈ U
    · rw [indicator_of_mem hEU, indicator_of_mem hEU]
      exact ThomDyadic.le_of_entropy _ M hF0 hM
    · rw [indicator_of_notMem hEU, indicator_of_notMem hEU]; linarith
  rw [← integral_indicator hU]
  calc ∫ E, U.indicator F E ∂arcsine
      ≤ ∫ E, (U.indicator (fun _ => M) E + (F E * log (F E) + 1) / log M) ∂arcsine :=
        integral_mono_ae hint1 hint2 (ae_arcsine_mem_Icc.mono fun E hE => hpt E hE)
    _ = M * arcsine.real U + (fejEnt μ N + 1) / log M := by
        have hiA : Integrable (fun E => U.indicator (fun _ => M) E) arcsine :=
          (integrable_indicator_iff hU).mpr (integrableOn_const (measure_ne_top _ _))
        have hiB : Integrable (fun E => (F E * log (F E) + 1) / log M) arcsine :=
          ((integrable_fejer_mul_log μ N).add (integrable_const 1)).div_const _
        have e1 : ∫ E, (U.indicator (fun _ => M) E + (F E * log (F E) + 1) / log M) ∂arcsine =
            ∫ E, U.indicator (fun _ => M) E ∂arcsine +
              ∫ E, (F E * log (F E) + 1) / log M ∂arcsine := integral_add hiA hiB
        have e2 : ∫ E, U.indicator (fun _ => M) E ∂arcsine = M * arcsine.real U := by
          rw [integral_indicator hU, setIntegral_const, smul_eq_mul, mul_comm]
        have e3 : ∫ E, (F E * log (F E) + 1) / log M ∂arcsine = (fejEnt μ N + 1) / log M := by
          rw [integral_div, integral_add (integrable_fejer_mul_log μ N) (integrable_const 1),
            integral_const, probReal_univ, smul_eq_mul, mul_one]
          rfl
        rw [e1, e2, e3]

/-- **Uniform integrability of the Fejér densities** under bounded entropy. -/
theorem fejer_uniformlyIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (B : ℝ) (hB : ∀ N, fejEnt μ N ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, ∀ U : Set ℝ, MeasurableSet U →
      arcsine.real U ≤ η → ∫ E in U, fejer μ N E ∂arcsine ≤ ε := by
  intro ε hε
  set c := max (B + 1) 1
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  set M := exp (2 * c / ε)
  have hM : 1 < M := one_lt_exp_iff.mpr (by positivity)
  have hlM : log M = 2 * c / ε := log_exp _
  refine ⟨ε / (2 * M), by positivity, fun N U hU hUη => ?_⟩
  have h := setIntegral_fejer_le μ hμ N hU hM
  have h1 : M * arcsine.real U ≤ ε / 2 := by
    calc M * arcsine.real U ≤ M * (ε / (2 * M)) := by gcongr
      _ = ε / 2 := by field_simp
  have h2 : (fejEnt μ N + 1) / log M ≤ ε / 2 := by
    rw [hlM, div_le_iff₀ (by positivity)]
    have : fejEnt μ N + 1 ≤ c := (by linarith [hB N] : fejEnt μ N + 1 ≤ B + 1).trans (le_max_left _ _)
    calc fejEnt μ N + 1 ≤ c := this
      _ = ε / 2 * (2 * c / ε) := by field_simp
  linarith

/-- The key estimate: for compact `C ⊆ U` open, `μ(C) ≤ M ρ(U) + (B+1)/log M`. -/
theorem measureReal_compact_le_of_fejEnt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CarriedBy4 μ) (B : ℝ) (hB : ∀ N, fejEnt μ N ≤ B) {C U : Set ℝ} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U) {M : ℝ} (hM : 1 < M) :
    μ.real C ≤ M * arcsine.real U + (B + 1) / log M := by
  have hl : 0 < log M := log_pos hM
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 2
  have hδ : 0 < δ := by positivity
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
  have hcarr : ∀ᵐ E ∂μ, E ∈ Icc (-4 : ℝ) 4 := ae_mem_of_carried hμ
  have hPint : Integrable (polyFun P) μ := integrable_of_continuous hμ (continuous_polyFun P)
  have hgint : Integrable g μ := integrable_of_continuous hμ hgc
  -- (1) `μ(C) ≤ ∫ g dμ ≤ ∫ P dμ + δ`
  have h1 : μ.real C ≤ ∫ E, g E ∂μ := by
    rw [← integral_indicator_one hC.measurableSet]
    refine integral_mono ((integrable_indicator_iff hC.measurableSet).mpr
      (integrableOn_const (measure_ne_top _ _))) hgint fun E => ?_
    by_cases hE : E ∈ C
    · simp [hE, hgC E hE]
    · simp [hE, (hg01 E).1]
  have h2 : ∫ E, g E ∂μ ≤ ∫ E, polyFun P E ∂μ + δ := by
    have : ∫ E, g E ∂μ ≤ ∫ E, (polyFun P E + δ) ∂μ :=
      integral_mono_ae hgint (hPint.add (integrable_const δ)) (hcarr.mono fun E hE => by
        have := hPE E hE; rw [abs_lt] at this; linarith)
    rwa [integral_add hPint (integrable_const δ), integral_const, smul_eq_mul, probReal_univ,
      one_mul] at this
  -- (2) `∫ F_N P dρ ≤ ∫_U F_N dρ + δ ≤ M ρ(U) + (B+1)/log M + δ`
  have h3 : ∀ N, ∫ E, fejer μ N E * polyFun P E ∂arcsine ≤
      M * arcsine.real U + (B + 1) / log M + δ := by
    intro N
    set F := fejer μ N
    have hF : Continuous F := continuous_fejer μ N
    have hiF : Integrable F arcsine := integrable_of_continuous_arcsine hF
    have hint1 : Integrable (fun E => F E * polyFun P E) arcsine :=
      integrable_of_continuous_arcsine (hF.mul (continuous_polyFun P))
    have hint2 : Integrable (fun E => U.indicator F E + δ * F E) arcsine :=
      (hiF.indicator hU.measurableSet).add (hiF.const_mul δ)
    have hpt : ∀ E ∈ Icc (-4 : ℝ) 4, F E * polyFun P E ≤ U.indicator F E + δ * F E := by
      intro E hE
      have hF0 : 0 ≤ F E := fejer_nonneg μ hμ N hE
      have hb := hPE E hE
      rw [abs_lt] at hb
      by_cases hEU : E ∈ U
      · rw [indicator_of_mem hEU]
        have : polyFun P E ≤ 1 + δ := by linarith [(hg01 E).2]
        nlinarith
      · rw [indicator_of_notMem hEU]
        have : polyFun P E ≤ δ := by linarith [hgU E hEU]
        nlinarith
    have hU' := setIntegral_fejer_le μ hμ N hU.measurableSet hM
    calc ∫ E, F E * polyFun P E ∂arcsine ≤ ∫ E, (U.indicator F E + δ * F E) ∂arcsine :=
          integral_mono_ae hint1 hint2 (ae_arcsine_mem_Icc.mono fun E hE => hpt E hE)
      _ = ∫ E in U, F E ∂arcsine + δ := by
          rw [integral_add (hiF.indicator hU.measurableSet) (hiF.const_mul δ),
            integral_indicator hU.measurableSet, integral_const_mul, integral_fejer, mul_one]
      _ ≤ M * arcsine.real U + (fejEnt μ N + 1) / log M + δ := by linarith
      _ ≤ M * arcsine.real U + (B + 1) / log M + δ := by
          have : (fejEnt μ N + 1) / log M ≤ (B + 1) / log M :=
            div_le_div_of_nonneg_right (by linarith [hB N]) hl.le
          linarith
  have hlim := tendsto_integral_fejer_mul_poly μ hμ P
  have h4 : ∫ E, polyFun P E ∂μ ≤ M * arcsine.real U + (B + 1) / log M + δ :=
    le_of_tendsto' hlim h3
  have : δ + δ = ε := by simp only [δ]; ring
  linarith

/-- **Fejér entropy criterion**: bounded `H_N` implies `μ ≪ Lebesgue`. -/
theorem ac_of_fejEnt_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (B : ℝ) (hB : ∀ N, fejEnt μ N ≤ B) : μ ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  have hρA : arcsine A = 0 := arcsine_ac hvol
  have step : ∀ M : ℝ, 1 < M → ∀ ε : ℝ, 0 < ε → μ.real A ≤ (B + 1) / log M + ε := by
    intro M hM ε hε
    have hM0 : 0 < M := by linarith
    set η := ε / (2 * M)
    have hη : 0 < η := by positivity
    obtain ⟨U, hAU, hU, hρU⟩ := Set.exists_isOpen_lt_of_lt A (ENNReal.ofReal η)
      (by rw [hρA]; exact ENNReal.ofReal_pos.mpr hη)
    obtain ⟨C, hCA, hC, hμC⟩ := hA.exists_isCompact_lt_add (μ := μ) (measure_ne_top μ A)
      (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
    have key := measureReal_compact_le_of_fejEnt μ hμ B hB hC hU (hCA.trans hAU) hM
    have hρU' : arcsine.real U ≤ η := by
      rw [Measure.real]; exact ENNReal.toReal_le_of_le_ofReal hη.le hρU.le
    have hAC : μ.real A ≤ μ.real C + ε / 2 := by
      rw [Measure.real, Measure.real]
      calc (μ A).toReal ≤ (μ C + ENNReal.ofReal (ε / 2)).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
              hμC.le
        _ = (μ C).toReal + ε / 2 := by
            rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
              ENNReal.toReal_ofReal (by positivity)]
    have : M * arcsine.real U ≤ ε / 2 := by
      calc M * arcsine.real U ≤ M * η := by gcongr
        _ = ε / 2 := by simp only [η]; field_simp
    linarith
  have step2 : ∀ M : ℝ, 1 < M → μ.real A ≤ (B + 1) / log M := fun M hM =>
    le_of_forall_pos_le_add fun ε hε => step M hM ε hε
  have hA0 : μ.real A ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set c := max (B + 1) 1
    have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    set t := 2 * c / μ.real A + 1
    have ht : 0 < t := by positivity
    have hM : 1 < exp t := one_lt_exp_iff.mpr ht
    have h1 := step2 (exp t) hM
    rw [log_exp] at h1
    have h2 : (B + 1) / t ≤ c / t := div_le_div_of_nonneg_right (le_max_left _ _) ht.le
    have h3 : c / t < μ.real A := by
      rw [div_lt_iff₀ ht]
      have : μ.real A * t = 2 * c + μ.real A := by simp only [t]; field_simp
      rw [this]; linarith
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp (le_antisymm hA0 measureReal_nonneg)

/-- **`L^p` bounds give entropy bounds**: `H_N ≤ ∫ |F_N|^p dρ / (p - 1)` for `p > 1`. -/
theorem fejEnt_le_of_Lp (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) {p : ℝ}
    (hp : 1 < p) (N : ℕ) : fejEnt μ N ≤ (∫ E, |fejer μ N E| ^ p ∂arcsine) / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have hF := continuous_fejer μ N
  have hint : Integrable (fun E => |fejer μ N E| ^ p) arcsine :=
    integrable_of_continuous_arcsine (hF.abs.rpow_const fun _ => Or.inr (by linarith))
  rw [← integral_div]
  refine integral_mono_ae (integrable_fejer_mul_log μ N) (hint.div_const _)
    (ae_arcsine_mem_Icc.mono fun E hE => ?_)
  show fejer μ N E * log (fejer μ N E) ≤ |fejer μ N E| ^ p / (p - 1)
  have hF0 : 0 ≤ fejer μ N E := fejer_nonneg μ hμ N hE
  set x := fejer μ N E
  have hlog := log_le_rpow_div hF0 hp1
  rw [abs_of_nonneg hF0]
  calc x * log x ≤ x * (x ^ (p - 1) / (p - 1)) := mul_le_mul_of_nonneg_left hlog hF0
    _ = x ^ p / (p - 1) := by
        rw [mul_div_assoc']
        congr 1
        rcases hF0.eq_or_lt with h | h
        · rw [← h, zero_mul, Real.zero_rpow (by linarith)]
        · rw [← Real.rpow_one_add' h.le (by linarith)]
          · ring_nf
          -- `1 + (p - 1) ≠ 0`
    _ = _ := rfl

/-- Bounded `L^p` Fejér norms (`p > 1`) imply bounded Fejér entropies. -/
theorem fejEnt_bounded_of_Lp (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    {p : ℝ} (hp : 1 < p) (M : ℝ) (hM : ∀ N, ∫ E, |fejer μ N E| ^ p ∂arcsine ≤ M) :
    ∀ N, fejEnt μ N ≤ M / (p - 1) := fun N =>
  (fejEnt_le_of_Lp μ hμ hp N).trans (div_le_div_of_nonneg_right (hM N) (by linarith))

/-! ### Strictness: an integrable logarithmic singularity -/

/-- Values `v_k = 2^k / k³` on the dyadic blocks `[2^{-k-1}, 2^{-k})`, `k ≥ 1`; the block masses
are `m_k = 2^{-k-1} v_k = 1/(2k³)`. -/
def stepVal (k : ℕ) : ℝ := 2 ^ k / (k : ℝ) ^ 3

/-- **Strictly weaker than every `L^p`** (unconditional). For the dyadic step profile, the
entropy series `∑ m_k log v_k` converges, but the `L^p` series `∑ 2^{-k-1} v_k^p` diverges for
every `p > 1`. -/
theorem entropy_strictly_weaker :
    Summable (fun k : ℕ => (1 / (2 * ((k : ℝ) + 1) ^ 3)) * log (stepVal (k + 1))) ∧
    ∀ p : ℝ, 1 < p →
      ¬ Summable (fun k : ℕ => (1 / 2 ^ (k + 2) : ℝ) * stepVal (k + 1) ^ p) := by
  constructor
  · -- `0 ≤ log v_{k+1} ≤ (k+1) log 2 ≤ k + 1`, so the terms are `O(1/(k+1)²)`
    have hs : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      have := (summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      exact ((summable_nat_add_iff 1).mpr this).congr fun k => by push_cast; ring
    refine Summable.of_norm_bounded (hs.mul_left 2) fun k => ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hv : 0 < stepVal (k + 1) := by unfold stepVal; push_cast; positivity
    have hlog_le : |log (stepVal (k + 1))| ≤ 4 * ((k : ℝ) + 1) := by
      unfold stepVal
      push_cast
      rw [log_div (by positivity) (by positivity), log_pow, log_pow]
      have h2 : log 2 ≤ 1 := by
        have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have h20 : 0 ≤ log 2 := log_nonneg (by norm_num)
      have hl1 : 0 ≤ log ((k : ℝ) + 1) := log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
      have hl2 : log ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := (log_le_sub_one_of_pos hk).trans (by linarith)
      rw [abs_le]; push_cast
      constructor <;> nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    calc 1 / (2 * ((k : ℝ) + 1) ^ 3) * |log (stepVal (k + 1))|
        ≤ 1 / (2 * ((k : ℝ) + 1) ^ 3) * (4 * ((k : ℝ) + 1)) := by gcongr
      _ = 2 * (1 / ((k : ℝ) + 1) ^ 2) := by field_simp; ring
  · intro p hp hsum
    have hpos : 0 < p - 1 := by linarith
    set r : ℝ := (2 : ℝ) ^ (p - 1)
    have hr : 1 < r := Real.one_lt_rpow (by norm_num) hpos
    set m : ℕ := ⌈3 * p⌉₊
    have hm : 3 * p ≤ m := Nat.le_ceil _
    have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ m / r ^ (k + 1)) atTop (𝓝 0) := by
      have := (tendsto_pow_const_div_const_pow_of_one_lt m hr).comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    have ht := hsum.tendsto_atTop_zero
    have ev1 := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
    have ev2 := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
    obtain ⟨k, h1, h2⟩ := (ev1.and ev2).exists
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    -- the term is `r^{k+1} / (2 (k+1)^{3p}) ≥ r^{k+1} / (2 (k+1)^m)`
    have hterm : (1 / 2 ^ (k + 2) : ℝ) * stepVal (k + 1) ^ p =
        r ^ (k + 1) / (2 * ((k : ℝ) + 1) ^ (3 * p)) := by
      unfold stepVal
      push_cast
      have e1 : ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 3) ^ p =
          (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * p) / ((k : ℝ) + 1) ^ (3 * p) := by
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast 2 (k + 1),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((k : ℝ) + 1) 3,
          ← Real.rpow_mul hk0.le]
        norm_num
      have e2 : r ^ (k + 1) = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * p) / 2 ^ (k + 1) := by
        simp only [r]
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (p - 1)) (k + 1), ← Real.rpow_mul (by norm_num),
          eq_div_iff (by positivity), ← Real.rpow_natCast 2 (k + 1), ← Real.rpow_add (by norm_num)]
        congr 1; ring
      rw [e1, e2]
      field_simp
      ring
    have hpow : ((k : ℝ) + 1) ^ (3 * p) ≤ ((k : ℝ) + 1) ^ m := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hk1 hm
    have hrpos : 0 < r ^ (k + 1) := by positivity
    have hge : r ^ (k + 1) / (2 * ((k : ℝ) + 1) ^ m) ≤
        (1 / 2 ^ (k + 2) : ℝ) * stepVal (k + 1) ^ p := by
      rw [hterm]
      exact div_le_div_of_nonneg_left hrpos.le (by positivity) (by linarith)
    have h1' : ((k : ℝ) + 1) ^ m < r ^ (k + 1) := by
      rwa [div_lt_one hrpos] at h1
    have : 1 / 2 < r ^ (k + 1) / (2 * ((k : ℝ) + 1) ^ m) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith

end ThomChebyshev
