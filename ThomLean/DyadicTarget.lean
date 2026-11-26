import ThomLean.NoAtoms
import ThomLean.Chebyshev.Dyadic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The dyadic entropy criterion for `μ_A`

Transport `μ_A` to `[0,1]` by `θ(E) = arccos(E/4)/π` and write `λ = θ_* μ_A` (`lam`).

* `lam` is a probability measure carried by `[0,1)` (`lam_compl_Ico`): the only point sent to
  `1` is `E = -4`, and `μ_A{-4} = 0` by `muA_no_atoms`.
* `muA_ac_of_lam_ac`: `λ ≪ Lebesgue ⇒ μ_A ≪ Lebesgue`. The map `θ` is differentiable on
  `(-4,4)`, so it sends Lebesgue-null sets to Lebesgue-null sets
  (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`); `±4` are `μ_A`-null.
* `muA_ac_of_dyEnt_bounded`, `muA_ac_of_summable_dyDisc`: bounded dyadic entropies of `λ`, or
  summable dyadic discrepancies `D_k(λ) = ∑_I (λ(I₋) - λ(I₊))²/λ(I)`, imply `μ_A ≪ Lebesgue`.

These are **conditional criteria**: neither hypothesis is proved here.
-/

noncomputable section

namespace ThomDyadicTarget

open ThomExistence ThomNoAtoms ThomDyadic MeasureTheory Real Set

/-- `θ(E) = arccos(E/4)/π ∈ [0,1]`. -/
def theta (E : ℝ) : ℝ := arccos (E / 4) / π

lemma continuous_theta : Continuous theta := by
  unfold theta; fun_prop

lemma measurable_theta : Measurable theta := continuous_theta.measurable

/-- The transported measure `λ = θ_* μ_A` on `[0,1]`. -/
def lam : Measure ℝ := muA.map theta

instance : IsProbabilityMeasure muA := isSpectralMeasureA_muA.isProb

instance : IsProbabilityMeasure lam :=
  (Measure.isProbabilityMeasure_map_iff measurable_theta.aemeasurable).mpr inferInstance

lemma theta_nonneg (E : ℝ) : 0 ≤ theta E := div_nonneg (arccos_nonneg _) pi_pos.le

lemma theta_lt_one {E : ℝ} (hE : -4 < E) : theta E < 1 := by
  unfold theta
  rw [div_lt_one pi_pos]
  refine lt_of_le_of_ne (arccos_le_pi _) fun h => ?_
  have := arccos_eq_pi.mp h
  linarith

lemma muA_compl_Icc : muA (Icc (-4 : ℝ) 4)ᶜ = 0 := isSpectralMeasureA_muA.carried

/-- `μ_A` is carried by the open interval `(-4,4)`. -/
lemma muA_compl_Ioo : muA (Ioo (-4 : ℝ) 4)ᶜ = 0 := by
  have hsub : (Ioo (-4 : ℝ) 4)ᶜ ⊆ (Icc (-4 : ℝ) 4)ᶜ ∪ ({-4} ∪ {4}) := by
    intro x hx
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hx
    by_cases h : x ∈ Icc (-4 : ℝ) 4
    · right
      rcases hx with hx | hx
      · left; exact le_antisymm hx h.1
      · right; exact le_antisymm h.2 hx
    · left; exact h
  refine measure_mono_null hsub (measure_union_null muA_compl_Icc
    (measure_union_null (muA_no_atoms _) (muA_no_atoms _)))

/-- `λ` is carried by `[0,1)`. -/
theorem lam_compl_Ico : lam (Ico (0 : ℝ) 1)ᶜ = 0 := by
  unfold lam
  rw [Measure.map_apply measurable_theta measurableSet_Ico.compl]
  refine measure_mono_null (fun E hE => ?_) muA_compl_Ioo
  simp only [mem_preimage, mem_compl_iff, mem_Ico, not_and_or, not_le, not_lt] at hE
  simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt]
  rcases hE with h | h
  · exact absurd h (not_lt.mpr (theta_nonneg E))
  · by_contra hc
    push Not at hc
    exact absurd h (not_le.mpr (theta_lt_one hc.1))

lemma differentiableOn_theta : DifferentiableOn ℝ theta (Ioo (-4 : ℝ) 4) := by
  intro x hx
  have h1 : x / 4 ≠ -1 := by intro h; linarith [hx.1]
  have h2 : x / 4 ≠ 1 := by intro h; linarith [hx.2]
  have hd : DifferentiableAt ℝ arccos (x / 4) := differentiableAt_arccos.mpr ⟨h1, h2⟩
  have hl : DifferentiableAt ℝ (fun y : ℝ => y / 4) x := differentiableAt_id.div_const 4
  have hc : DifferentiableAt ℝ (arccos ∘ fun y : ℝ => y / 4) x :=
    DifferentiableAt.comp (g := arccos) x hd hl
  have h3 : DifferentiableAt ℝ (fun y : ℝ => arccos (y / 4) / π) x := hc.div_const π
  exact h3.differentiableWithinAt

/-- **Back-transport**: `λ ≪ Lebesgue ⇒ μ_A ≪ Lebesgue`. -/
theorem muA_ac_of_lam_ac (h : lam ≪ volume) : muA ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A _ hA => ?_
  set s := A ∩ Ioo (-4 : ℝ) 4
  have hs0 : volume s = 0 := measure_mono_null inter_subset_left hA
  have himg : volume (theta '' s) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (differentiableOn_theta.mono inter_subset_right) hs0
  have hlam : lam (theta '' s) = 0 := h himg
  have hs : muA s = 0 := by
    refine measure_mono_null (subset_preimage_image theta s) ?_
    exact le_antisymm ((Measure.le_map_apply measurable_theta.aemeasurable _).trans hlam.le)
      (by simp)
  have hsub : A ⊆ s ∪ (Ioo (-4 : ℝ) 4)ᶜ := by
    intro x hx
    by_cases h : x ∈ Ioo (-4 : ℝ) 4
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  exact measure_mono_null hsub (measure_union_null hs muA_compl_Ioo)

/-- **Dyadic entropy criterion for `μ_A`** (conditional). -/
theorem muA_ac_of_dyEnt_bounded (h : ∃ B, ∀ k, dyEnt lam k ≤ B) : muA ≪ volume := by
  obtain ⟨B, hB⟩ := h
  exact muA_ac_of_lam_ac (ac_of_dyEnt_bounded lam lam_compl_Ico B hB)

/-- **Dyadic discrepancy criterion for `μ_A`** (conditional): summable
`D_k = ∑_I (λ(I₋) - λ(I₊))²/λ(I)` implies `μ_A ≪ Lebesgue`. -/
theorem muA_ac_of_summable_dyDisc (h : Summable (dyDisc lam)) : muA ≪ volume :=
  muA_ac_of_lam_ac (ac_of_summable_dyDisc lam lam_compl_Ico h)

/-- The entropy increments of `λ` are nonnegative and bounded by the discrepancies
(unconditional). -/
theorem lam_dyEnt_increment (k : ℕ) :
    0 ≤ dyEnt lam (k + 1) - dyEnt lam k ∧ dyEnt lam (k + 1) - dyEnt lam k ≤ dyDisc lam k :=
  ⟨dyEnt_succ_sub_nonneg lam k, dyEnt_succ_sub_le lam k⟩

end ThomDyadicTarget
