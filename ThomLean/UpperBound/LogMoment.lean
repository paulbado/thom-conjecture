import ThomLean.UpperBound.Upper
import ThomLean.DyadicTarget
import Mathlib.Analysis.PSeries

/-!
# Round 8, Task 5: logarithmic moments of `μ_A` at `0`

`logMoment_finite_iff`: for `s > 0`,
`∫_{|E|<1} log^s(1/|E|) dμ_A < ∞ ↔ s < 2`.

No absolute continuity is assumed.

* `s < 2`: layer cake. `log^s(1/|E|) ≤ ∑_j w_j 1_{|E| ≤ e^{-j}}` with
  `w_j = (j+1)^s - j^s`. The upper bound `logUpperBound_explicit` gives
  `μ_A([-e^{-j}, e^{-j}]) ≤ C (1+log j)³ / j²`. Reduce to `s ≥ 1`, so that
  `w_j ≤ s (j+1)^{s-1}` by Bernoulli. The series is then summable.
* `s ≥ 2`: if the integral were finite, the measure `ν = F · μ_A|_{(-1,1)}` would be finite.
  Continuity from above would give `ν([-e^{-j}, e^{-j}]) → ν{0} = 0`, using `muA_no_atoms`.
  But on that interval `F ≥ j²`, and `logSqLowerBound` gives `μ_A ≥ c/j²`. So
  `ν ≥ c > 0`, a contradiction.
-/

noncomputable section

namespace ThomUpper

open ThomZeroLevel ThomHeisenberg ThomExistence ThomNoAtoms ThomLowerBound
open Real MeasureTheory Filter

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- The integrand `log^s (1/|E|)`. -/
def logF (s : ℝ) (E : ℝ) : ENNReal := ENNReal.ofReal (log (1 / |E|) ^ s)

/-- Layer weights. -/
def lw (s : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ s - (j : ℝ) ^ s

/-- Dyadic-exponential intervals `[-e^{-j}, e^{-j}]`. -/
def lA (j : ℕ) : Set ℝ := Set.Icc (-exp (-(j : ℝ))) (exp (-(j : ℝ)))

lemma measurableSet_lA (j : ℕ) : MeasurableSet (lA j) := measurableSet_Icc

lemma lw_nonneg {s : ℝ} (hs : 0 ≤ s) (j : ℕ) : 0 ≤ lw s j := by
  unfold lw
  have : (j : ℝ) ^ s ≤ ((j : ℝ) + 1) ^ s :=
    rpow_le_rpow (by positivity) (by linarith) hs
  linarith

lemma mem_lA {E : ℝ} {j : ℕ} : E ∈ lA j ↔ |E| ≤ exp (-(j : ℝ)) := by
  unfold lA; rw [Set.mem_Icc, abs_le]

lemma log_inv_abs_nonneg {E : ℝ} (hE : E ∈ Set.Ioo (-1 : ℝ) 1) : 0 ≤ log (1 / |E|) := by
  rcases eq_or_ne E 0 with h | h
  · simp [h]
  · rw [one_div, log_inv, neg_nonneg]
    exact log_nonpos (abs_nonneg _) (abs_le.2 ⟨hE.1.le, hE.2.le⟩)

/-- Pointwise layer-cake bound. -/
lemma logF_le_tsum {s : ℝ} (hs : 0 < s) {E : ℝ} (hE : E ∈ Set.Ioo (-1 : ℝ) 1) :
    logF s E ≤ ∑' j, (lA j).indicator (fun _ => ENNReal.ofReal (lw s j)) E := by
  rcases eq_or_ne E 0 with h0 | h0
  · simp [logF, h0, zero_rpow hs.ne']
  set L := log (1 / |E|) with hL
  have hL0 : 0 ≤ L := log_inv_abs_nonneg hE
  set n := ⌊L⌋₊
  have hLn : L ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one L).le
  have habs : 0 < |E| := abs_pos.2 h0
  have hlogE : log |E| = -L := by rw [hL, one_div, log_inv, neg_neg]
  have hmem : ∀ j ∈ Finset.range (n + 1), E ∈ lA j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mem_lA]
    have hjL : (j : ℝ) ≤ L := by
      have : j ≤ n := by omega
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hL0)
    calc |E| = exp (log |E|) := (exp_log habs).symm
      _ ≤ exp (-(j : ℝ)) := exp_le_exp.2 (by rw [hlogE]; linarith)
  have htel : ∑ j ∈ Finset.range (n + 1), lw s j = ((n : ℝ) + 1) ^ s := by
    have := Finset.sum_range_sub (fun j : ℕ => ((j : ℝ)) ^ s) (n + 1)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_rpow hs.ne', sub_zero] at this
    rw [← this]; rfl
  calc logF s E = ENNReal.ofReal (L ^ s) := rfl
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ s) :=
        ENNReal.ofReal_le_ofReal (rpow_le_rpow hL0 hLn hs.le)
    _ = ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (lw s j) := by
        rw [← htel, ENNReal.ofReal_sum_of_nonneg (fun j _ => lw_nonneg hs.le j)]
    _ = ∑ j ∈ Finset.range (n + 1), (lA j).indicator (fun _ => ENNReal.ofReal (lw s j)) E := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Set.indicator_of_mem (hmem j hj)]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Bernoulli: `(j+1)^s - j^s ≤ s (j+1)^{s-1}` for `s ≥ 1`. -/
lemma lw_le {s : ℝ} (hs : 1 ≤ s) (j : ℕ) : lw s j ≤ s * ((j : ℝ) + 1) ^ (s - 1) := by
  unfold lw
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hb := one_add_mul_self_le_rpow_one_add
    (show (-1 : ℝ) ≤ -1 / ((j : ℝ) + 1) by
      rw [neg_div, neg_le_neg_iff, div_le_one hj1]; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]) hs
  have heq : (1 : ℝ) + -1 / ((j : ℝ) + 1) = (j : ℝ) / ((j : ℝ) + 1) := by
    field_simp; ring
  rw [heq, div_rpow (Nat.cast_nonneg j) hj1.le] at hb
  have hpos : 0 < ((j : ℝ) + 1) ^ s := rpow_pos_of_pos hj1 s
  have hsub : ((j : ℝ) + 1) ^ (s - 1) = ((j : ℝ) + 1) ^ s / ((j : ℝ) + 1) :=
    rpow_sub_one hj1.ne' s
  rw [le_div_iff₀ hpos] at hb
  rw [hsub]
  have : (1 + s * (-1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1) ^ s
      = ((j : ℝ) + 1) ^ s - s * (((j : ℝ) + 1) ^ s / ((j : ℝ) + 1)) := by
    field_simp; ring
  linarith

/-- `μ_A([-e^{-j}, e^{-j}])` for `j ≥ 121`, from the round-8 upper bound. -/
lemma muA_lA_le {j : ℕ} (hj : 121 ≤ j) :
    muA.real (lA j) ≤ 17284 * (1 + log j) ^ 3 / (j : ℝ) ^ 2 := by
  have h := logUpperBound_explicit (h := exp (-(j : ℝ))) (exp_pos _)
    (exp_le_exp.2 (by have : (121 : ℝ) ≤ j := by exact_mod_cast hj
                      linarith))
  rw [log_exp, neg_neg, neg_sq] at h
  exact h

/-- Summability for `1 ≤ s < 2`. -/
lemma summable_lw_mul {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s < 2) :
    Summable (fun j : ℕ => lw s j * muA.real (lA j)) := by
  set δ : ℝ := (2 - s) / 6 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set C : ℝ := 2 * s * (17284 * (1 + 1 / δ) ^ 3) with hC
  refine Summable.of_norm_bounded_eventually (g := fun j : ℕ => C * (j : ℝ) ^ (s / 2 - 2))
    ((Real.summable_nat_rpow.2 (by linarith)).mul_left C) ?_
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨121, fun j hj => ?_⟩
  have hjR : (121 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hmnn : 0 ≤ muA.real (lA j) := measureReal_nonneg
  rw [Real.norm_of_nonneg (mul_nonneg (lw_nonneg (by linarith) j) hmnn)]
  -- weight bound
  have hw : lw s j ≤ 2 * s * (j : ℝ) ^ (s - 1) := by
    have h1 := lw_le hs1 j
    have h2 : ((j : ℝ) + 1) ^ (s - 1) ≤ (2 * (j : ℝ)) ^ (s - 1) :=
      rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h3 : (2 * (j : ℝ)) ^ (s - 1) = (2 : ℝ) ^ (s - 1) * (j : ℝ) ^ (s - 1) :=
      mul_rpow (by norm_num) hj0.le
    have h4 : (2 : ℝ) ^ (s - 1) ≤ 2 := by
      have := rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show s - 1 ≤ 1 by linarith)
      simpa using this
    have h5 : 0 ≤ (j : ℝ) ^ (s - 1) := by positivity
    calc lw s j ≤ s * ((j : ℝ) + 1) ^ (s - 1) := h1
      _ ≤ s * ((2 : ℝ) ^ (s - 1) * (j : ℝ) ^ (s - 1)) := by
          rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ s * (2 * (j : ℝ) ^ (s - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_right h4 h5
      _ = 2 * s * (j : ℝ) ^ (s - 1) := by ring
  -- measure bound
  have hlog : 1 + log j ≤ (1 + 1 / δ) * (j : ℝ) ^ δ := by
    have h1 := Real.log_le_rpow_div hj0.le hδ0
    have h2 : 1 ≤ (j : ℝ) ^ δ := one_le_rpow (by linarith) hδ0.le
    have : (j : ℝ) ^ δ / δ = (1 / δ) * (j : ℝ) ^ δ := by ring
    nlinarith
  have hlog0 : 0 ≤ 1 + log (j : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ j by linarith); linarith
  have hcube : (1 + log (j : ℝ)) ^ 3 ≤ (1 + 1 / δ) ^ 3 * (j : ℝ) ^ (3 * δ) := by
    have := pow_le_pow_left₀ hlog0 hlog 3
    rw [mul_pow] at this
    have he : ((j : ℝ) ^ δ) ^ 3 = (j : ℝ) ^ (3 * δ) := by
      rw [← rpow_natCast, ← rpow_mul hj0.le]; ring_nf
    rwa [he] at this
  have hm : muA.real (lA j) ≤ 17284 * (1 + 1 / δ) ^ 3 * (j : ℝ) ^ (3 * δ) / (j : ℝ) ^ 2 := by
    refine le_trans (muA_lA_le hj) ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcube (by norm_num)
  have hexp : (j : ℝ) ^ (s / 2 - 2) = (j : ℝ) ^ (s - 1) * (j : ℝ) ^ (3 * δ) / (j : ℝ) ^ 2 := by
    rw [← rpow_natCast (j : ℝ) 2, ← rpow_add hj0, ← rpow_sub hj0]
    congr 1; rw [hδ]; push_cast; ring
  calc lw s j * muA.real (lA j)
      ≤ (2 * s * (j : ℝ) ^ (s - 1)) *
          (17284 * (1 + 1 / δ) ^ 3 * (j : ℝ) ^ (3 * δ) / (j : ℝ) ^ 2) :=
        mul_le_mul hw hm hmnn (by positivity)
    _ = C * (j : ℝ) ^ (s / 2 - 2) := by
        rw [hexp, hC]; ring

/-- Finite moment for `1 ≤ s < 2`. -/
lemma logMoment_lt_top_of_one_le {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s < 2) :
    (∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s E ∂muA) < ⊤ := by
  have hs : 0 < s := by linarith
  calc (∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s E ∂muA)
      ≤ ∫⁻ E in Set.Ioo (-1 : ℝ) 1,
          ∑' j, (lA j).indicator (fun _ => ENNReal.ofReal (lw s j)) E ∂muA :=
        setLIntegral_mono' measurableSet_Ioo (fun E hE => logF_le_tsum hs hE)
    _ ≤ ∫⁻ E, ∑' j, (lA j).indicator (fun _ => ENNReal.ofReal (lw s j)) E ∂muA :=
        setLIntegral_le_lintegral _ _
    _ = ∑' j, ENNReal.ofReal (lw s j) * muA (lA j) := by
        rw [lintegral_tsum (fun j => (measurable_const.indicator (measurableSet_lA j)).aemeasurable)]
        congr 1; funext j
        exact lintegral_indicator_const (measurableSet_lA j) _
    _ = ENNReal.ofReal (∑' j, lw s j * muA.real (lA j)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (lw_nonneg hs.le j) measureReal_nonneg) (summable_lw_mul hs1 hs2)]
        congr 1; funext j
        rw [ENNReal.ofReal_mul (lw_nonneg hs.le j), measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Finite moment for `0 < s < 2`. -/
theorem logMoment_lt_top {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s E ∂muA) < ⊤ := by
  set s' := max s 1
  have h1 : 1 ≤ s' := le_max_right _ _
  have h2 : s' < 2 := max_lt hs2 (by norm_num)
  calc (∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s E ∂muA)
      ≤ ∫⁻ E in Set.Ioo (-1 : ℝ) 1, (1 + logF s' E) ∂muA := by
        refine setLIntegral_mono' measurableSet_Ioo (fun E hE => ?_)
        have hL0 := log_inv_abs_nonneg hE
        unfold logF
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rcases le_total (log (1 / |E|)) 1 with hle | hge
        · have := rpow_le_one hL0 hle hs.le
          have : 0 ≤ log (1 / |E|) ^ s' := by positivity
          linarith
        · have := rpow_le_rpow_of_exponent_le hge (le_max_left s 1)
          linarith
    _ = muA (Set.Ioo (-1 : ℝ) 1) + ∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s' E ∂muA := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, logMoment_lt_top_of_one_le h1 h2⟩

/-- Infinite moment for `s ≥ 2` (uses only `logSqLowerBound` and `muA_no_atoms`). -/
theorem logMoment_eq_top {s : ℝ} (hs : 2 ≤ s) :
    (∫⁻ E in Set.Ioo (-1 : ℝ) 1, logF s E ∂muA) = ⊤ := by
  by_contra hfin
  set ν := (muA.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity (logF s)
  set B : ℕ → Set ℝ := fun j => lA (j + 1)
  have hBm : ∀ j, MeasurableSet (B j) := fun j => measurableSet_lA (j + 1)
  have hBsub : ∀ j, B j ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro j E hE
    have hE' := (mem_lA).1 hE
    have : exp (-((j + 1 : ℕ) : ℝ)) < 1 := by
      calc exp (-((j + 1 : ℕ) : ℝ)) < exp 0 :=
            exp_lt_exp.2 (by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
        _ = 1 := exp_zero
    exact ⟨by linarith [neg_abs_le E], by linarith [le_abs_self E]⟩
  have hνB : ∀ j, ν (B j) = ∫⁻ E in B j, logF s E ∂muA := by
    intro j
    rw [withDensity_apply _ (hBm j), Measure.restrict_restrict_of_subset (hBsub j)]
  have hanti : Antitone B := by
    intro i j hij E hE
    rw [mem_lA] at hE ⊢
    refine le_trans hE (exp_le_exp.2 ?_)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    push_cast; linarith
  have hinter : (⋂ j, B j) = {0} := by
    ext E
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hE
      by_contra h0
      have hpos : 0 < |E| := abs_pos.2 h0
      obtain ⟨j, hj⟩ := exists_nat_gt (-log |E|)
      have := (mem_lA).1 (hE j)
      have h2 : log |E| ≤ -((j + 1 : ℕ) : ℝ) := by
        rw [← log_exp (-((j + 1 : ℕ) : ℝ))]; exact log_le_log hpos this
      push_cast at h2; linarith
    · rintro rfl j
      rw [mem_lA, abs_zero]; exact (exp_pos _).le
  have hfin' : ν (B 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [hνB]
    exact lintegral_mono_set (hBsub 0)
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun j => (hBm j).nullMeasurableSet)
    hanti ⟨0, hfin'⟩
  rw [hinter] at hlim
  have h0 : ν {0} = 0 := by
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    apply setLIntegral_measure_zero
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact measure_mono_null Set.inter_subset_left (muA_no_atoms 0)
  rw [h0] at hlim
  obtain ⟨c, hc, h₀, hh₀, hlow⟩ := logSqLowerBound
  have hev := (tendsto_order.1 hlim).2 (ENNReal.ofReal c) (ENNReal.ofReal_pos.2 hc)
  rw [eventually_atTop] at hev
  obtain ⟨J0, hJ0⟩ := hev
  obtain ⟨J1, hJ1⟩ := exists_nat_gt (-log h₀)
  set j := max J0 J1
  have hj := hJ0 j (le_max_left _ _)
  apply absurd hj
  rw [not_lt]
  show ENNReal.ofReal c ≤ ν (B j)
  rw [hνB]
  set a : ℝ := ((j + 1 : ℕ) : ℝ)
  have ha1 : 1 ≤ a := by simp only [a]; push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hhpos : 0 < exp (-a) := exp_pos _
  have hhlt : exp (-a) < h₀ := by
    have : (J1 : ℝ) ≤ j := by exact_mod_cast le_max_right J0 J1
    calc exp (-a) < exp (log h₀) := exp_lt_exp.2 (by simp only [a]; push_cast; linarith)
      _ = h₀ := exp_log hh₀
  have hmu := hlow _ hhpos hhlt
  rw [log_exp, neg_sq] at hmu
  -- pointwise lower bound on `B j \ {0}`
  have hpt : ∀ E ∈ B j \ {0}, ENNReal.ofReal (a ^ 2) ≤ logF s E := by
    rintro E ⟨hE, hE0⟩
    have hE0' : E ≠ 0 := hE0
    have hpos : 0 < |E| := abs_pos.2 hE0'
    have hEa := (mem_lA).1 hE
    have hL : a ≤ log (1 / |E|) := by
      rw [one_div, log_inv]
      have : log |E| ≤ -a := by rw [← log_exp (-a)]; exact log_le_log hpos hEa
      linarith
    apply ENNReal.ofReal_le_ofReal
    have h1 : log (1 / |E|) ^ (2 : ℝ) ≤ log (1 / |E|) ^ s :=
      rpow_le_rpow_of_exponent_le (by linarith) hs
    rw [rpow_two] at h1
    nlinarith
  have hBj : MeasurableSet (B j \ {0}) := (hBm j).diff (measurableSet_singleton 0)
  calc ENNReal.ofReal c ≤ ENNReal.ofReal (a ^ 2 * muA.real (B j)) := by
        apply ENNReal.ofReal_le_ofReal
        have : c / a ^ 2 * a ^ 2 = c := by field_simp
        calc c = c / a ^ 2 * a ^ 2 := this.symm
          _ ≤ muA.real (B j) * a ^ 2 := mul_le_mul_of_nonneg_right hmu (by positivity)
          _ = a ^ 2 * muA.real (B j) := by ring
    _ = ENNReal.ofReal (a ^ 2) * muA (B j \ {0}) := by
        rw [ENNReal.ofReal_mul (by positivity), measure_diff_null (muA_no_atoms 0),
          measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ∫⁻ E in B j \ {0}, ENNReal.ofReal (a ^ 2) ∂muA := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ E in B j \ {0}, logF s E ∂muA := setLIntegral_mono' hBj hpt
    _ ≤ ∫⁻ E in B j, logF s E ∂muA := lintegral_mono_set Set.diff_subset

/-- **Round 8, Task 5.** For `s > 0`, `∫_{|E|<1} log^s(1/|E|) dμ_A < ∞ ↔ s < 2`.
Unconditional; absolute continuity of `μ_A` is not assumed. -/
theorem logMoment_finite_iff {s : ℝ} (hs : 0 < s) :
    (∫⁻ E in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal (log (1 / |E|) ^ s) ∂muA) < ⊤ ↔ s < 2 := by
  constructor
  · intro h
    by_contra h2
    push Not at h2
    have := logMoment_eq_top h2
    unfold logF at this
    rw [this] at h
    exact lt_irrefl _ h
  · exact logMoment_lt_top hs

end ThomUpper
