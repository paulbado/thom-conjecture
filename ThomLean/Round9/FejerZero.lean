import ThomLean.Round9.Kernel
import ThomLean.UpperBound.Upper
import ThomLean.DyadicTarget
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Round 9, Tasks 1–2: Fejér densities of `μ_A` at `0`

* `fejer_ge_mass`, `fejer_zero_le_mass` (generic, for any probability measure on `[-4,4]`).
* `fejer_muA_lower`: `F_N(E) ≥ c (N+1)/log²(N+1)` for `|E| ≤ 1/(2(N+1))`.
* `fejer_muA_zero_upper`: `F_N(0) ≤ C (N+1) (1 + log log (N+1))³ / log²(N+1)`.
* `fejer_muA_Lp_lower`: `∫ F_N^p dρ ≥ c_p (N+1)^{p-1} / log^{2p}(N+1)` (`p ≥ 1`); for `p = 2`,
  `∫ F_N² dρ ≥ c (N+1)/log⁴(N+1)`.
* `central_entropy_le`: for `0 < β < 1`,
  `∫_{|E| ≤ (N+1)^{-β}} F_N log⁺ F_N dρ ≤ C_β (1 + log log (N+1))³ / log (N+1)`.
-/

noncomputable section

namespace ThomRound9

open ThomChebyshev ThomExistence ThomBridge ThomUpper ThomZeroLevel ThomLowerBound
open MeasureTheory Real Set Filter

set_option linter.unusedSectionVars false

lemma continuous_fejerKern (N : ℕ) (E : ℝ) : Continuous (fejerKern N E) := by
  have := continuous_cheb
  unfold fejerKern
  fun_prop

lemma integrable_fejerKern (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (N : ℕ) (E : ℝ) : Integrable (fejerKern N E) μ :=
  integrable_of_continuous hμ (continuous_fejerKern N E)

/-- `F_N(E) ≥ (N+1)/16 · μ([-h_N, h_N])` for `|E| ≤ h_N = 1/(2(N+1))`. -/
theorem fejer_ge_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ)
    {E : ℝ} (hE : |E| ≤ 1 / (2 * (N + 1))) :
    ((N : ℝ) + 1) / 16 * μ.real (Icc (-(1 / (2 * (N + 1)))) (1 / (2 * (N + 1)))) ≤
      fejer μ N E := by
  set h : ℝ := 1 / (2 * (N + 1))
  have hh : 0 < h := by positivity
  have hE4 : E ∈ Icc (-4 : ℝ) 4 := by
    have : h ≤ 4 := by
      simp only [h]; rw [div_le_iff₀ (by positivity)]; nlinarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
    rw [abs_le] at hE; constructor <;> linarith
  rw [fejer_eq_integral_kern μ hμ, mul_comm, ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Icc]
  refine integral_mono_ae ((integrable_const _).indicator measurableSet_Icc)
    (integrable_fejerKern μ hμ N E) ?_
  filter_upwards [ae_mem_of_carried hμ] with E' hE'
  by_cases hI : E' ∈ Icc (-h) h
  · rw [indicator_of_mem hI]
    exact fejerKern_ge N hE (abs_le.2 hI)
  · rw [indicator_of_notMem hI]
    exact fejerKern_nonneg N hE4 hE'

/-- `F_N(0) ≤ (N+1) μ([-r,r]) + 64/((N+1) r²)` for `r > 0`. -/
theorem fejer_zero_le_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    fejer μ N 0 ≤ ((N : ℝ) + 1) * μ.real (Icc (-r) r) + 64 / ((N + 1) * r ^ 2) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [fejer_eq_integral_kern μ hμ]
  have hrhs : ((N : ℝ) + 1) * μ.real (Icc (-r) r) + 64 / ((N + 1) * r ^ 2) =
      ∫ E', ((Icc (-r) r).indicator (fun _ => (N : ℝ) + 1) E' + 64 / ((N + 1) * r ^ 2)) ∂μ := by
    rw [integral_add ((integrable_const _).indicator measurableSet_Icc) (integrable_const _),
      integral_indicator_const _ measurableSet_Icc, integral_const]
    simp [mul_comm]
  rw [hrhs]
  refine integral_mono_ae (integrable_fejerKern μ hμ N 0)
    (((integrable_const _).indicator measurableSet_Icc).add (integrable_const _)) ?_
  filter_upwards [ae_mem_of_carried hμ] with E' hE'
  have h0 : (0 : ℝ) ∈ Icc (-4 : ℝ) 4 := by constructor <;> norm_num
  have hpos : 0 ≤ 64 / ((N + 1) * r ^ 2) := by positivity
  by_cases hI : E' ∈ Icc (-r) r
  · rw [indicator_of_mem hI]
    linarith [fejerKern_le N h0 hE']
  · rw [indicator_of_notMem hI, zero_add]
    have hr2 : r ^ 2 < E' ^ 2 := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hI
      rcases hI with h | h <;> nlinarith
    have hK := sq_mul_fejerKern_le N h0 hE'
    have hK0 := fejerKern_nonneg N h0 hE'
    rw [zero_sub, neg_sq] at hK
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hN] at hK
    nlinarith

/-- `ρ([-h,h]) ≥ h/(2π)` for `0 < h ≤ 1`. -/
lemma arcsine_Icc_ge {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h / (2 * π) ≤ arcsine.real (Icc (-h) h) := by
  have hpi := Real.pi_pos
  have hge : ENNReal.ofReal (h / (2 * π)) ≤ arcsine (Icc (-h) h) := by
    rw [arcsine_eq_withDensity, withDensity_apply _ measurableSet_Icc]
    calc ENNReal.ofReal (h / (2 * π)) = ∫⁻ _ in Icc (-h) h, ENNReal.ofReal (1 / (4 * π)) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp; ring
      _ ≤ ∫⁻ E in Icc (-h) h, ENNReal.ofReal (ThomChebyshev.arcDens E) := by
          refine setLIntegral_mono' measurableSet_Icc fun E hE => ENNReal.ofReal_le_ofReal ?_
          have hE4 : E ∈ Ioc (-4 : ℝ) 4 := ⟨by linarith [hE.1], by linarith [hE.2]⟩
          rw [ThomChebyshev.arcDens, indicator_of_mem hE4]
          have hs : √(16 - E ^ 2) ≤ 4 := by
            rw [show (4 : ℝ) = √16 by rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt (by nlinarith)
          have hs0 : 0 < √(16 - E ^ 2) := Real.sqrt_pos.2 (by nlinarith [hE.1, hE.2])
          rw [one_div, mul_inv, mul_inv, mul_comm (π⁻¹)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs0 hs) (inv_nonneg.2 hpi.le)
  rw [Measure.real]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hge

lemma log_two_mul_le {x : ℝ} (hx : 2 ≤ x) : log (2 * x) ≤ 2 * log x := by
  rw [Real.log_mul (by norm_num) (by linarith)]
  have := Real.log_le_log (by norm_num) hx
  linarith

/-- **Task 1, lower bound.** `F_N(E) ≥ c (N+1)/log²(N+1)` for `|E| ≤ 1/(2(N+1))`, `N ≥ N₀`. -/
theorem fejer_muA_lower : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ E : ℝ,
    |E| ≤ 1 / (2 * (N + 1)) → c * (N + 1) / log (N + 1) ^ 2 ≤ fejer muA N E := by
  obtain ⟨c₀, hc₀, h₀, hh₀, hlow⟩ := logSqLowerBound
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / h₀)
  refine ⟨c₀ / 64, by positivity, max N₀ 1, fun N hN E hE => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hN0 : (N₀ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  set h : ℝ := 1 / (2 * (N + 1)) with hhdef
  have hh : 0 < h := by positivity
  have hhlt : h < h₀ := by
    have h1 : 1 / h₀ < 2 * (N + 1) := by linarith
    rw [hhdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hh₀] at h1; linarith
  have hμ := hlow h hh hhlt
  have hlogh : log h ^ 2 = log (2 * (N + 1)) ^ 2 := by
    rw [hhdef, one_div, Real.log_inv, neg_sq]
  have hL0 : 0 < log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hL : log (2 * ((N : ℝ) + 1)) ^ 2 ≤ 4 * log ((N : ℝ) + 1) ^ 2 := by
    have h1 := log_two_mul_le (x := (N : ℝ) + 1) (by linarith)
    have h2 : 0 ≤ log (2 * ((N : ℝ) + 1)) := Real.log_nonneg (by linarith)
    nlinarith
  have hLpos : 0 < log (2 * ((N : ℝ) + 1)) ^ 2 := by
    have : 0 < log (2 * ((N : ℝ) + 1)) := Real.log_pos (by linarith)
    positivity
  have hμ' : c₀ / (4 * log ((N : ℝ) + 1) ^ 2) ≤ muA.real (Icc (-h) h) := by
    refine le_trans ?_ hμ
    rw [hlogh]
    exact div_le_div_of_nonneg_left hc₀.le hLpos hL
  have hF := fejer_ge_mass muA isSpectralMeasureA_muA.carried N hE
  calc c₀ / 64 * (N + 1) / log (N + 1) ^ 2 = ((N : ℝ) + 1) / 16 * (c₀ / (4 * log (N + 1) ^ 2)) := by
        field_simp; ring
    _ ≤ ((N : ℝ) + 1) / 16 * muA.real (Icc (-h) h) :=
        mul_le_mul_of_nonneg_left hμ' (by positivity)
    _ ≤ fejer muA N E := hF

lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : log x ^ 2 ≤ 4 * x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have h1 : log x = 2 * log √x := by
    rw [← Real.log_rpow hs, show (√x) ^ (2 : ℝ) = x by
      rw [Real.rpow_two, Real.sq_sqrt (by linarith)]]
  have h2 : log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos hs
  have h3 : 0 ≤ log x := Real.log_nonneg hx
  have h4 : log x ≤ 2 * √x := by linarith
  have h5 : (2 * √x) ^ 2 = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
  nlinarith

/-- **Task 1, upper bound at `0`.** `F_N(0) ≤ C (N+1) (1 + log log (N+1))³ / log²(N+1)`. -/
theorem fejer_muA_zero_upper : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    fejer muA N 0 ≤ C * (N + 1) * (1 + log (log (N + 1))) ^ 3 / log (N + 1) ^ 2 := by
  refine ⟨69392, ⌈exp 242⌉₊, fun N hN => ?_⟩
  have hN1 : exp 242 ≤ (N : ℝ) + 1 := by
    have := Nat.le_of_ceil_le hN; linarith
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  set L := log ((N : ℝ) + 1) with hLdef
  have hL : 242 ≤ L := by
    have := Real.log_le_log (exp_pos _) hN1; rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  set r : ℝ := 1 / √((N : ℝ) + 1) with hrdef
  have hsq : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.2 hNpos
  have hr : 0 < r := by positivity
  have hr2 : ((N : ℝ) + 1) * r ^ 2 = 1 := by
    rw [hrdef, div_pow, Real.sq_sqrt hNpos.le]; field_simp
  have hlogr : log r = -(L / 2) := by
    rw [hrdef, one_div, Real.log_inv, Real.log_sqrt hNpos.le]
  have hrsmall : r ≤ exp (-121) := by
    rw [← Real.exp_log hr, hlogr]; exact exp_le_exp.2 (by linarith)
  have hμ := logUpperBound_explicit hr hrsmall
  rw [hlogr, neg_neg, neg_sq] at hμ
  have hloglog : 1 + log (L / 2) ≤ 1 + log L := by
    have := Real.log_le_log (by linarith) (show L / 2 ≤ L by linarith); linarith
  have hll0 : 0 ≤ 1 + log (L / 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ L / 2 by linarith); linarith
  have hlL : 1 ≤ 1 + log L := by have := Real.log_nonneg (show (1 : ℝ) ≤ L by linarith); linarith
  have hμ' : muA.real (Icc (-r) r) ≤ 69136 * (1 + log L) ^ 3 / L ^ 2 := by
    refine le_trans hμ ?_
    have : (1 + log (L / 2)) ^ 3 ≤ (1 + log L) ^ 3 := pow_le_pow_left₀ hll0 hloglog 3
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg L]
  have hF := fejer_zero_le_mass muA isSpectralMeasureA_muA.carried N hr
  rw [hr2, div_one] at hF
  have h64 : (64 : ℝ) ≤ 256 * (N + 1) * (1 + log L) ^ 3 / L ^ 2 := by
    have hL2 := log_sq_le_four_mul (x := (N : ℝ) + 1) (by linarith [add_one_le_exp (242:ℝ)])
    rw [← hLdef] at hL2
    rw [le_div_iff₀ (by positivity)]
    have : 1 ≤ (1 + log L) ^ 3 := one_le_pow₀ hlL
    nlinarith
  calc fejer muA N 0 ≤ ((N : ℝ) + 1) * muA.real (Icc (-r) r) + 64 := hF
    _ ≤ ((N : ℝ) + 1) * (69136 * (1 + log L) ^ 3 / L ^ 2) +
          256 * (N + 1) * (1 + log L) ^ 3 / L ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hμ' hNpos.le) h64
    _ = 69392 * (N + 1) * (1 + log L) ^ 3 / L ^ 2 := by ring

/-- **Task 1, `L^p` divergence.** For `p ≥ 1`,
`∫ F_N^p dρ ≥ c_p (N+1)^{p-1} / log^{2p}(N+1)` for `N ≥ N₀`. -/
theorem fejer_muA_Lp_lower {p : ℝ} (hp : 1 ≤ p) : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * ((N : ℝ) + 1) ^ (p - 1) / log (N + 1) ^ (2 * p) ≤ ∫ E, fejer muA N E ^ p ∂arcsine := by
  obtain ⟨c, hc, N₀, hlow⟩ := fejer_muA_lower
  refine ⟨c ^ p / (4 * π), by positivity, max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  set L := log ((N : ℝ) + 1)
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set h : ℝ := 1 / (2 * (N + 1))
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    simp only [h]; rw [div_le_iff₀ (by positivity)]; linarith
  set a : ℝ := c * (N + 1) / L ^ 2
  have ha : 0 < a := by positivity
  have hcont : Continuous fun E => fejer muA N E ^ p :=
    (continuous_fejer muA N).rpow_const fun _ => Or.inr (by linarith)
  have hint := integrable_of_continuous_arcsine hcont
  have hnn : 0 ≤ᵐ[arcsine] fun E => fejer muA N E ^ p := by
    filter_upwards [ae_arcsine_mem_Icc] with E hE
    exact Real.rpow_nonneg (fejer_nonneg muA isSpectralMeasureA_muA.carried N hE) p
  have h1 : ∫ E in Icc (-h) h, fejer muA N E ^ p ∂arcsine ≤ ∫ E, fejer muA N E ^ p ∂arcsine :=
    setIntegral_le_integral hint hnn
  have h2 : a ^ p * arcsine.real (Icc (-h) h) ≤ ∫ E in Icc (-h) h, fejer muA N E ^ p ∂arcsine := by
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _)) hint.integrableOn
      measurableSet_Icc fun E hE => ?_
    exact Real.rpow_le_rpow ha.le (hlow N (le_trans (le_max_left _ _) hN) E (abs_le.2 hE))
      (by linarith)
  have h3 := arcsine_Icc_ge hh hh1
  have hval : c ^ p / (4 * π) * ((N : ℝ) + 1) ^ (p - 1) / L ^ (2 * p) = a ^ p * (h / (2 * π)) := by
    have e1 : a ^ p = c ^ p * ((N : ℝ) + 1) ^ p / L ^ (2 * p) := by
      simp only [a]
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hc.le hNpos.le,
        Real.rpow_mul hL0.le]
      norm_cast
    rw [e1, Real.rpow_sub_one hNpos.ne']
    simp only [h]
    field_simp
    norm_num
  rw [hval]
  calc a ^ p * (h / (2 * π)) ≤ a ^ p * arcsine.real (Icc (-h) h) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ _ := h2.trans h1

/-- **Task 1, `p = 2`.** `∫ F_N² dρ ≥ c (N+1)/log⁴(N+1)`. -/
theorem fejer_muA_L2_lower : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * ((N : ℝ) + 1) / log (N + 1) ^ 4 ≤ ∫ E, fejer muA N E ^ 2 ∂arcsine := by
  obtain ⟨c, hc, N₀, h⟩ := fejer_muA_Lp_lower (p := 2) (by norm_num)
  refine ⟨c, hc, N₀, fun N hN => ?_⟩
  have := h N hN
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    show (2 : ℝ) * 2 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_two] at this
  exact this

/-! ### Task 2: the central entropy contribution -/

lemma fejer_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ) {E : ℝ}
    (hE : E ∈ Icc (-4 : ℝ) 4) : fejer μ N E ≤ N + 1 := by
  rw [fejer_eq_integral_kern μ hμ]
  calc ∫ E', fejerKern N E E' ∂μ ≤ ∫ _, ((N : ℝ) + 1) ∂μ :=
        integral_mono_ae (integrable_fejerKern μ hμ N E) (integrable_const _)
          ((ae_mem_of_carried hμ).mono fun E' hE' => fejerKern_le N hE hE')
    _ = N + 1 := by simp

/-- `∫_I T_{n+1} dρ`. -/
def tI (I : Set ℝ) (n : ℕ) : ℝ := ∫ E in I, cheb (n + 1) E ∂arcsine

lemma integrableOn_cheb (I : Set ℝ) (n : ℕ) : IntegrableOn (cheb n) I arcsine :=
  (integrable_of_continuous_arcsine (continuous_cheb n)).integrableOn

/-- `G(E') = ∫_I K_N(E,E') dρ(E) = ρ(I) + 2∑ a_n (∫_I T_{n+1}) T_{n+1}(E')`. -/
lemma setIntegral_fejerKern (N : ℕ) (I : Set ℝ) (E' : ℝ) :
    ∫ E in I, fejerKern N E E' ∂arcsine = arcsine.real I +
      2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * (tI I n * cheb (n + 1) E') := by
  have hint : ∀ n, IntegrableOn (fun E => fejMult N (n + 1) * (cheb (n + 1) E * cheb (n + 1) E'))
      I arcsine := fun n => ((integrableOn_cheb I (n + 1)).mul_const _).const_mul _
  unfold fejerKern
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun n _ => hint n).const_mul _),
    integral_const_mul, integral_finsetSum _ fun n _ => hint n]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real]
  congr 2
  · simp [Measure.restrict_apply MeasurableSet.univ]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_mul_const, tI]

lemma setIntegral_fejer (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) (I : Set ℝ) :
    ∫ E in I, fejer μ N E ∂arcsine = arcsine.real I +
      2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * (chebCoeff μ (n + 1) * tI I n) := by
  have hint : ∀ n, IntegrableOn (fun E => fejMult N (n + 1) * chebCoeff μ (n + 1) * cheb (n + 1) E)
      I arcsine := fun n => (integrableOn_cheb I (n + 1)).const_mul _
  unfold fejer
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun n _ => hint n).const_mul _),
    integral_const_mul, integral_finsetSum _ fun n _ => hint n]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real]
  congr 2
  · simp [Measure.restrict_apply MeasurableSet.univ]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, tI]; ring

/-- **Exchange**: `∫_I F_N dρ = ∫ G dμ`. -/
lemma setIntegral_fejer_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ)
    (I : Set ℝ) :
    ∫ E in I, fejer μ N E ∂arcsine = ∫ E', (∫ E in I, fejerKern N E E' ∂arcsine) ∂μ := by
  simp_rw [setIntegral_fejerKern]
  have hint : ∀ n, Integrable (fun E' => fejMult N (n + 1) * (tI I n * cheb (n + 1) E')) μ :=
    fun n => integrable_of_continuous hμ (by have := continuous_cheb (n + 1); fun_prop)
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun n _ => hint n).const_mul _),
    integral_const_mul, integral_finsetSum _ fun n _ => hint n, setIntegral_fejer]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_const_mul, chebCoeff]; ring

lemma integral_fejerKern_left (N : ℕ) (E' : ℝ) : ∫ E, fejerKern N E E' ∂arcsine = 1 := by
  have := setIntegral_fejerKern N univ E'
  rw [Measure.restrict_univ] at this
  rw [this]
  have h0 : ∀ n, tI univ n = 0 := by
    intro n; rw [tI, Measure.restrict_univ, integral_cheb]; simp
  simp [h0, probReal_univ]

lemma continuous_setIntegral_fejerKern (N : ℕ) (I : Set ℝ) :
    Continuous fun E' => ∫ E in I, fejerKern N E E' ∂arcsine := by
  simp_rw [setIntegral_fejerKern]
  have := continuous_cheb
  fun_prop

/-- **Central mass**: `∫_{[-h,h]} F_N dρ ≤ μ([-2h,2h]) + 64 ρ([-h,h])/((N+1)h²)`. -/
theorem setIntegral_fejer_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (hh4 : h ≤ 1) :
    ∫ E in Icc (-h) h, fejer μ N E ∂arcsine ≤
      μ.real (Icc (-(2 * h)) (2 * h)) + arcsine.real (Icc (-h) h) * (64 / ((N + 1) * h ^ 2)) := by
  rw [setIntegral_fejer_eq μ hμ]
  set c := arcsine.real (Icc (-h) h) * (64 / ((N + 1) * h ^ 2))
  have hrhs : μ.real (Icc (-(2 * h)) (2 * h)) + c =
      ∫ E', ((Icc (-(2 * h)) (2 * h)).indicator (fun _ => (1 : ℝ)) E' + c) ∂μ := by
    rw [integral_add ((integrable_const _).indicator measurableSet_Icc) (integrable_const _),
      integral_indicator_const _ measurableSet_Icc, integral_const]
    simp
  rw [hrhs]
  refine integral_mono_ae (integrable_of_continuous hμ (continuous_setIntegral_fejerKern N _))
    (((integrable_const _).indicator measurableSet_Icc).add (integrable_const _)) ?_
  filter_upwards [ae_mem_of_carried hμ] with E' hE'
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  have hc : 0 ≤ c := by positivity
  have hKnn : ∀ᵐ E ∂arcsine, 0 ≤ fejerKern N E E' :=
    ae_arcsine_mem_Icc.mono fun E hE => fejerKern_nonneg N hE hE'
  have hKint : Integrable (fun E => fejerKern N E E') arcsine :=
    integrable_of_continuous_arcsine (by have := continuous_cheb; unfold fejerKern; fun_prop)
  by_cases hI : E' ∈ Icc (-(2 * h)) (2 * h)
  · rw [indicator_of_mem hI]
    have := setIntegral_le_integral (s := Icc (-h) h) hKint hKnn
    rw [integral_fejerKern_left] at this
    linarith
  · rw [indicator_of_notMem hI, zero_add]
    have hfar : ∀ E ∈ Icc (-h) h, fejerKern N E E' ≤ 64 / ((N + 1) * h ^ 2) := by
      intro E hE
      have hE4 : E ∈ Icc (-4 : ℝ) 4 := ⟨by linarith [hE.1], by linarith [hE.2]⟩
      have hd : h ^ 2 ≤ (E - E') ^ 2 := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hI
        rcases hI with h1 | h1 <;> nlinarith [hE.1, hE.2]
      have hK := sq_mul_fejerKern_le N hE4 hE'
      have hK0 := fejerKern_nonneg N hE4 hE'
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hNpos] at hK
      have : fejerKern N E E' * (N + 1) * h ^ 2 ≤ fejerKern N E E' * (N + 1) * (E - E') ^ 2 :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      nlinarith
    calc ∫ E in Icc (-h) h, fejerKern N E E' ∂arcsine
        ≤ ∫ _ in Icc (-h) h, 64 / ((N + 1) * h ^ 2) ∂arcsine :=
          setIntegral_mono_on hKint.integrableOn (integrableOn_const (measure_ne_top _ _))
            measurableSet_Icc hfar
      _ = c := by rw [setIntegral_const, smul_eq_mul]

lemma mul_max_log_le {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    x * max (log x) 0 ≤ x * log M := by
  apply mul_le_mul_of_nonneg_left _ hx
  have hM0 : 0 ≤ log M := Real.log_nonneg hM
  refine max_le ?_ hM0
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact hM0
  · exact Real.log_le_log h0 hxM

/-- **Task 2: central entropy.** For `0 < β < 1` there are `C, N₀` with
`∫_{|E| ≤ (N+1)^{-β}} F_N log⁺ F_N dρ ≤ C (1 + log log(N+1))³ / log(N+1)` for `N ≥ N₀`. -/
theorem central_entropy_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∫ E in Icc (-(((N : ℝ) + 1) ^ (-β))) (((N : ℝ) + 1) ^ (-β)),
        fejer muA N E * max (log (fejer muA N E)) 0 ∂arcsine ≤
      C * (1 + log (log (N + 1))) ^ 3 / log (N + 1) := by
  obtain ⟨M, hM0, hM⟩ := arcsine_Ioo_le
  set ε : ℝ := (1 - β) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨69136 / β ^ 2 + 256 * M / ε ^ 2, ⌈exp (122 / β)⌉₊, fun N hN => ?_⟩
  have hx1 : exp (122 / β) ≤ (N : ℝ) + 1 := by have := Nat.le_of_ceil_le hN; linarith
  set x : ℝ := (N : ℝ) + 1 with hxdef
  have hxpos : 0 < x := by positivity
  set L := log x with hLdef
  have hβL : 122 ≤ β * L := by
    have := Real.log_le_log (exp_pos _) hx1
    rw [Real.log_exp] at this
    rw [div_le_iff₀ hβ0] at this; linarith
  have hL1 : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  have hx1' : 1 ≤ x := by
    have := Real.add_one_le_exp (122 / β); have : 0 < 122 / β := by positivity
    linarith
  set h : ℝ := x ^ (-β) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hxpos _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hlogh : log h = -(β * L) := by rw [hhdef, Real.log_rpow hxpos]; ring
  -- Step A: entropy ≤ L · mass
  have hcont : Continuous fun E => max (fejer muA N E * log (fejer muA N E)) 0 :=
    (Real.continuous_mul_log.comp (continuous_fejer muA N)).max continuous_const
  have heq : EqOn (fun E => max (fejer muA N E * log (fejer muA N E)) 0)
      (fun E => fejer muA N E * max (log (fejer muA N E)) 0) (Icc (-h) h) := by
    intro E hE
    have hE4 : E ∈ Icc (-4 : ℝ) 4 := ⟨by linarith [hE.1], by linarith [hE.2]⟩
    have h0 := fejer_nonneg muA isSpectralMeasureA_muA.carried N hE4
    simp only
    rw [mul_max_of_nonneg _ _ h0, mul_zero]
  have hintA : IntegrableOn (fun E => fejer muA N E * max (log (fejer muA N E)) 0)
      (Icc (-h) h) arcsine :=
    ((integrable_of_continuous_arcsine hcont).integrableOn).congr_fun heq measurableSet_Icc
  have hintF : IntegrableOn (fun E => fejer muA N E * L) (Icc (-h) h) arcsine :=
    ((integrable_of_continuous_arcsine (continuous_fejer muA N)).integrableOn).mul_const _
  have hA : ∫ E in Icc (-h) h, fejer muA N E * max (log (fejer muA N E)) 0 ∂arcsine ≤
      L * ∫ E in Icc (-h) h, fejer muA N E ∂arcsine := by
    rw [mul_comm L, show (∫ E in Icc (-h) h, fejer muA N E ∂arcsine) * L =
      ∫ E in Icc (-h) h, fejer muA N E * L ∂arcsine from (integral_mul_const _ _).symm]
    refine setIntegral_mono_on hintA hintF measurableSet_Icc fun E hE => ?_
    have hE4 : E ∈ Icc (-4 : ℝ) 4 := ⟨by linarith [hE.1], by linarith [hE.2]⟩
    exact mul_max_log_le (fejer_nonneg muA isSpectralMeasureA_muA.carried N hE4)
      (fejer_le muA isSpectralMeasureA_muA.carried N hE4) hx1'
  -- Step B: central mass
  have hB := setIntegral_fejer_le muA isSpectralMeasureA_muA.carried N hh hh1
  have hρ : arcsine.real (Icc (-h) h) ≤ M * (4 * h) := by
    have hsub : Icc (-h) h ⊆ Ioo (-(2 * h)) (2 * h) := fun E hE =>
      ⟨by linarith [hE.1, hh], by linarith [hE.2, hh]⟩
    exact le_trans (measureReal_mono hsub (measure_ne_top _ _)) (hM h hh hh1)
  have hxh : x * h = x ^ (1 - β) := by
    rw [hhdef, show (1 : ℝ) - β = 1 + -β by ring, Real.rpow_add hxpos, Real.rpow_one]
  have hB2 : arcsine.real (Icc (-h) h) * (64 / ((N + 1) * h ^ 2)) ≤ 256 * M / x ^ (1 - β) := by
    rw [← hxh]
    have : arcsine.real (Icc (-h) h) * (64 / (x * h ^ 2)) ≤ M * (4 * h) * (64 / (x * h ^ 2)) :=
      mul_le_mul_of_nonneg_right hρ (by positivity)
    calc _ = arcsine.real (Icc (-h) h) * (64 / (x * h ^ 2)) := by rw [hxdef]
      _ ≤ M * (4 * h) * (64 / (x * h ^ 2)) := this
      _ = 256 * M / (x * h) := by field_simp; ring
  -- Step C: the logarithmic upper bound at `2h`
  have h2h : 0 < 2 * h := by positivity
  have hlog2h : log (2 * h) = log 2 - β * L := by
    rw [Real.log_mul (by norm_num) hh.ne', hlogh]; ring
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos one_lt_two
  have h2hsmall : 2 * h ≤ exp (-121) := by
    rw [← Real.exp_log h2h, hlog2h]; exact exp_le_exp.2 (by linarith)
  have hμ := logUpperBound_explicit h2h h2hsmall
  rw [hlog2h] at hμ
  have hll : 1 + log (-(log 2 - β * L)) ≤ 1 + log L := by
    have := Real.log_le_log (by linarith) (show -(log 2 - β * L) ≤ L by nlinarith)
    linarith
  have hll0 : 0 ≤ 1 + log (-(log 2 - β * L)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ -(log 2 - β * L) by linarith); linarith
  have hsqL : β ^ 2 * L ^ 2 / 4 ≤ (log 2 - β * L) ^ 2 := by nlinarith
  have hlL : 1 ≤ 1 + log L := by have := Real.log_nonneg hL1; linarith
  have hμ' : muA.real (Icc (-(2 * h)) (2 * h)) ≤ 69136 / β ^ 2 * (1 + log L) ^ 3 / L ^ 2 := by
    refine le_trans hμ ?_
    have h3 : (1 + log (-(log 2 - β * L))) ^ 3 ≤ (1 + log L) ^ 3 := pow_le_pow_left₀ hll0 hll 3
    have hQ : 0 ≤ (1 + log L) ^ 3 := by positivity
    have hd0 : 0 < β ^ 2 * L ^ 2 / 4 := by positivity
    calc 17284 * (1 + log (-(log 2 - β * L))) ^ 3 / (log 2 - β * L) ^ 2
        ≤ 17284 * (1 + log L) ^ 3 / (log 2 - β * L) ^ 2 := by gcongr
      _ ≤ 17284 * (1 + log L) ^ 3 / (β ^ 2 * L ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) hd0 hsqL
      _ = 69136 / β ^ 2 * (1 + log L) ^ 3 / L ^ 2 := by field_simp; ring
  -- Step D: the polynomial term beats `L²`
  have hpoly : L ^ 2 ≤ x ^ (1 - β) / ε ^ 2 := by
    have h1 := Real.log_le_rpow_div hxpos.le hε
    have h0 : 0 ≤ L := hL0.le
    have : L ^ 2 ≤ (x ^ ε / ε) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [div_pow, ← Real.rpow_natCast (x ^ ε), ← Real.rpow_mul hxpos.le] at this
    rw [hεdef] at this ⊢
    convert this using 2; push_cast; ring
  have hxb : 0 < x ^ (1 - β) := Real.rpow_pos_of_pos hxpos _
  have hD : L * (256 * M / x ^ (1 - β)) ≤ 256 * M / ε ^ 2 * (1 + log L) ^ 3 / L := by
    rw [le_div_iff₀ hL0]
    have : L * (256 * M / x ^ (1 - β)) * L = 256 * M * (L ^ 2 / x ^ (1 - β)) := by ring
    rw [this]
    have hq : L ^ 2 / x ^ (1 - β) ≤ 1 / ε ^ 2 := by
      rw [div_le_iff₀ hxb]; rw [le_div_iff₀ (by positivity)] at hpoly
      calc L ^ 2 ≤ x ^ (1 - β) / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hpoly
        _ = 1 / ε ^ 2 * x ^ (1 - β) := by ring
    have h3 : 1 ≤ (1 + log L) ^ 3 := one_le_pow₀ hlL
    calc 256 * M * (L ^ 2 / x ^ (1 - β)) ≤ 256 * M * (1 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ 256 * M / ε ^ 2 * (1 + log L) ^ 3 := by
          rw [mul_one_div]; nlinarith [show 0 ≤ 256 * M / ε ^ 2 by positivity]
  calc ∫ E in Icc (-h) h, fejer muA N E * max (log (fejer muA N E)) 0 ∂arcsine
      ≤ L * ∫ E in Icc (-h) h, fejer muA N E ∂arcsine := hA
    _ ≤ L * (muA.real (Icc (-(2 * h)) (2 * h)) + 256 * M / x ^ (1 - β)) :=
        mul_le_mul_of_nonneg_left (by linarith) hL0.le
    _ = L * muA.real (Icc (-(2 * h)) (2 * h)) + L * (256 * M / x ^ (1 - β)) := by ring
    _ ≤ L * (69136 / β ^ 2 * (1 + log L) ^ 3 / L ^ 2) +
          256 * M / ε ^ 2 * (1 + log L) ^ 3 / L :=
        add_le_add (mul_le_mul_of_nonneg_left hμ' hL0.le) hD
    _ = (69136 / β ^ 2 + 256 * M / ε ^ 2) * (1 + log L) ^ 3 / L := by
        field_simp

end ThomRound9
