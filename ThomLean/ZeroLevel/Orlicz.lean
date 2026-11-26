import ThomLean.ZeroLevel.LogSq

/-!
# The `L log² L` obstruction at `E = 0` (round 7, Task 1)

`not_integrable_mul_log_sq`: if `μ_A = f ρ` (`ρ` the arcsine law) with `f ≥ 0` measurable, then
`f log²(1+f)` is **not** `ρ`-integrable, i.e. `∫ f log²(1+f) dρ = +∞`. Unconditional.

Proof (the splitting proposed for round 7). With `T = h^{-1/2}`, pointwise
`f ≤ T + (4/log²(1/h)) · 1_{f > T} f log²(1+f)` (on `{f > T}`, `log(1+f) ≥ log T = ½ log(1/h)`).
Integrating over `[-h,h]`: `μ_A([-h,h]) log²(1/h) ≤ T ρ([-h,h]) log²(1/h) + 4 ∫_{f>T} f log²(1+f) dρ`.
The first term is `O(h^{1/2} log² h)`, the second tends to `0` if `f log²(1+f)` is integrable
(dominated convergence). This contradicts `logSqLowerBound`.

Taking `f` as the Radon–Nikodym density this says: whatever the regularity of `μ_A`, it has no
density in the Orlicz class `L log² L (ρ)`. Absolute continuity is not decided.
-/

noncomputable section

namespace ThomZeroLevel

open MeasureTheory Filter Topology Set Real ThomChebyshev ThomExistence ThomLowerBound

theorem not_integrable_mul_log_sq {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ E, 0 ≤ f E)
    (hμ : muA = arcsine.withDensity fun E => ENNReal.ofReal (f E)) :
    ¬ Integrable (fun E => f E * log (1 + f E) ^ 2) arcsine := by
  intro hG
  set G : ℝ → ℝ := fun E => f E * log (1 + f E) ^ 2 with hGdef
  have hG0 : ∀ E, 0 ≤ G E := fun E => mul_nonneg (hf0 E) (sq_nonneg _)
  obtain ⟨c, hc, h₀, hh₀, hlow⟩ := logSqLowerBound
  obtain ⟨M, hM0, hM⟩ := arcsine_Ioo_le
  -- tails of `G`
  set a : ℕ → ℝ := fun n => ∫ E, {x | (n : ℝ) + 3 < f x}.indicator G E ∂arcsine with ha
  have hmeasT : ∀ n : ℕ, MeasurableSet {x | (n : ℝ) + 3 < f x} :=
    fun n => measurableSet_lt measurable_const hfm
  have hta : Tendsto a atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := arcsine) G
      (F := fun n E => {x | (n : ℝ) + 3 < f x}.indicator G E)
      (fun n => (hG.indicator (hmeasT n)).aestronglyMeasurable) hG
      (fun n => ae_of_all _ fun E => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun x _ => hG0 x) E)]
        exact Set.indicator_le_self' (fun x _ => hG0 x) E)
      (ae_of_all _ fun E => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop ⌈f E⌉₊] with n hn
        have : f E ≤ (n : ℝ) + 3 := by
          have := Nat.le_ceil (f E)
          have : (⌈f E⌉₊ : ℝ) < n := by exact_mod_cast hn
          linarith
        rw [Set.indicator_of_notMem (by simpa using this)])
    simpa [ha] using this
  -- `log²(n+3)/(n+3) → 0`
  have htl : Tendsto (fun n : ℕ => log ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 3)) atTop (𝓝 0) := by
    have := (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (3 : ℝ))))
    refine this.congr fun n => ?_
    simp
  have hsum : Tendsto (fun n : ℕ => 16 * M * (log ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 3)) + 4 * a n)
      atTop (𝓝 0) := by
    simpa using ((htl.const_mul (16 * M)).add (hta.const_mul 4))
  -- choose `n` large
  have hev : ∀ᶠ n : ℕ in atTop, 16 * M * (log ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 3)) + 4 * a n < c ∧
      1 / ((n : ℝ) + 3) ^ 2 < h₀ := by
    refine (hsum.eventually (gt_mem_nhds hc)).and ?_
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3) ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 3) ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (3 : ℝ))))
      refine h1.inv_tendsto_atTop.congr fun n => ?_
      simp
    exact this.eventually (gt_mem_nhds hh₀)
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  set T : ℝ := (n : ℝ) + 3
  have hT : 3 ≤ T := by simp only [T]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set h : ℝ := 1 / T ^ 2
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  set L : ℝ := log T
  have hL : 0 < L := log_pos (by linarith)
  have hlogh : log h ^ 2 = 4 * L ^ 2 := by
    simp only [h, one_div, log_inv, log_pow]; push_cast; ring
  -- `μ_A([-h,h]) = ∫_{[-h,h]} f dρ`
  have hmuI : muA.real (Icc (-h) h) = ∫ E in Icc (-h) h, f E ∂arcsine := by
    rw [hμ, Measure.real, withDensity_apply _ measurableSet_Icc,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun E => hf0 E)
        hfm.aestronglyMeasurable.restrict]
  -- pointwise bound
  have hpt : ∀ E, f E ≤ T + 1 / L ^ 2 * {x | T < f x}.indicator G E := by
    intro E
    by_cases hE : T < f E
    · rw [Set.indicator_of_mem (by simpa using hE)]
      have h1 : L ≤ log (1 + f E) := log_le_log (by linarith) (by linarith)
      have h2 : L ^ 2 ≤ log (1 + f E) ^ 2 := pow_le_pow_left₀ hL.le h1 2
      have : f E ≤ 1 / L ^ 2 * G E := by
        rw [hGdef]; simp only
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 (hf0 E)
      linarith
    · have : 0 ≤ 1 / L ^ 2 * {x | T < f x}.indicator G E :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun x _ => hG0 x) E)
      push Not at hE; linarith
  have hGi : Integrable ({x | T < f x}.indicator G) arcsine :=
    hG.indicator (measurableSet_lt measurable_const hfm)
  have hint : ∫ E in Icc (-h) h, f E ∂arcsine ≤
      T * arcsine.real (Icc (-h) h) + 1 / L ^ 2 * a n := by
    calc ∫ E in Icc (-h) h, f E ∂arcsine
        ≤ ∫ E in Icc (-h) h, (T + 1 / L ^ 2 * {x | T < f x}.indicator G E) ∂arcsine :=
          integral_mono_of_nonneg (ae_of_all _ fun E => hf0 E)
            (Integrable.restrict (f := fun E => T + 1 / L ^ 2 * {x | T < f x}.indicator G E)
              ((integrable_const T).add (hGi.const_mul _)))
            (ae_of_all _ fun E => hpt E)
      _ = T * arcsine.real (Icc (-h) h) +
            1 / L ^ 2 * ∫ E in Icc (-h) h, {x | T < f x}.indicator G E ∂arcsine := by
          rw [integral_add (integrable_const T).integrableOn (hGi.const_mul _).integrableOn,
            setIntegral_const, integral_const_mul, smul_eq_mul, mul_comm]
      _ ≤ T * arcsine.real (Icc (-h) h) + 1 / L ^ 2 * a n := by
          gcongr
          exact setIntegral_le_integral hGi
            (ae_of_all _ fun E => Set.indicator_nonneg (fun x _ => hG0 x) E)
  -- `ρ([-h,h]) ≤ 4 M h`
  have hρ : arcsine.real (Icc (-h) h) ≤ M * (4 * h) := by
    refine le_trans (measureReal_mono (s₁ := Icc (-h) h) (s₂ := Ioo (-(2 * h)) (2 * h))
      (fun E hE => by constructor <;> linarith [hE.1, hE.2]) (measure_ne_top _ _)) (hM h hh hh1)
  -- combine
  have hlow' := hlow h hh hn2
  rw [hlogh, div_le_iff₀ (by positivity)] at hlow'
  have ha0 : 0 ≤ a n := integral_nonneg fun E => Set.indicator_nonneg (fun x _ => hG0 x) E
  have hTh : T * (M * (4 * h)) = 4 * M / T := by simp only [h]; field_simp
  have key : c ≤ (4 * M / T + 1 / L ^ 2 * a n) * (4 * L ^ 2) := by
    calc c ≤ muA.real (Icc (-h) h) * (4 * L ^ 2) := hlow'
      _ ≤ (T * arcsine.real (Icc (-h) h) + 1 / L ^ 2 * a n) * (4 * L ^ 2) := by
          rw [hmuI]; gcongr
      _ ≤ (4 * M / T + 1 / L ^ 2 * a n) * (4 * L ^ 2) := by
          rw [← hTh]; gcongr
  have : (4 * M / T + 1 / L ^ 2 * a n) * (4 * L ^ 2) = 16 * M * (L ^ 2 / T) + 4 * a n := by
    field_simp; ring
  linarith

end ThomZeroLevel
