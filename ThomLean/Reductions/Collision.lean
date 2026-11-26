import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Measure

/-!
# Poisson regularisation and the collision-energy identity

Harper–Heisenberg note, Lemma 3.1 (pointwise kernel comparisons) and Lemma 4.2.

* `poisson η t = η / (π (t² + η²))`, `integral_poisson : ∫ P_η = 1`.
* `box_le_pi_mul_poisson` : `h_η ≤ π P_η` where `h_η = (2η)⁻¹ 𝟙_{[-η,η]}`.
* `poisson_le_three_mul_shift` : `P_η(t) ≤ 3 P_η(t - u)` for `|u| ≤ η`.
* `collision_identity` : for a finite weighted point configuration `σ = ∑ w_k δ_{ξ_k}`, the
  local average `B_η(E) = (2η)⁻¹ σ([E-η, E+η])` satisfies
  `∫ B_η² = (4η²)⁻¹ ∑_{k,l} w_k w_l (2η - |ξ_k - ξ_l|)₊`.
* `collision_bounds` : `C(η)/(4η) ≤ ∫ B_η² ≤ C(2η)/(2η)` with
  `C(r) = ∑_{k,l} w_k w_l 𝟙{|ξ_k - ξ_l| ≤ r}`.

These are the identities used in the note to reduce `(P_{2,J})` to the correlation bound `(C)`;
they hold for *any* finite configuration (in particular for the Chambers-root measures `σ_Q`).
All results are unconditional.
-/

noncomputable section

namespace ThomReductions

open MeasureTheory Real Set Finset

/-- Poisson kernel. -/
def poisson (η t : ℝ) : ℝ := η / (π * (t ^ 2 + η ^ 2))

/-- Normalised box kernel `(2η)⁻¹ 𝟙_{[-η,η]}`. -/
def box (η t : ℝ) : ℝ := if |t| ≤ η then (2 * η)⁻¹ else 0

lemma poisson_pos {η : ℝ} (hη : 0 < η) (t : ℝ) : 0 < poisson η t := by
  unfold poisson; positivity

theorem integral_poisson {η : ℝ} (hη : 0 < η) : ∫ t, poisson η t = 1 := by
  have h : ∀ t, poisson η t = (π * η)⁻¹ * (1 + (η⁻¹ * t) ^ 2)⁻¹ := by
    intro t
    unfold poisson
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) η⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hη, smul_eq_mul]
  field_simp

theorem box_le_pi_mul_poisson {η : ℝ} (hη : 0 < η) (t : ℝ) : box η t ≤ π * poisson η t := by
  have hπ : π * poisson η t = η / (t ^ 2 + η ^ 2) := by
    unfold poisson; field_simp
  rw [hπ]
  unfold box
  split_ifs with h
  · have ht : t ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) h 2
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · positivity

theorem poisson_le_three_mul_shift {η : ℝ} (hη : 0 < η) {u : ℝ} (hu : |u| ≤ η) (t : ℝ) :
    poisson η t ≤ 3 * poisson η (t - u) := by
  unfold poisson
  have hu2 : u ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have : (t - u) ^ 2 ≤ 2 * t ^ 2 + 2 * u ^ 2 := by nlinarith [sq_nonneg (t + u)]
  have hπ := Real.pi_pos
  nlinarith [mul_pos hπ hη]

/-! ### Collision identity for finite configurations -/

/-- Overlap length of two windows of half-width `η`. -/
lemma volume_window_inter (η x y : ℝ) :
    volume.real (Icc (x - η) (x + η) ∩ Icc (y - η) (y + η)) = max (2 * η - |x - y|) 0 := by
  rw [Icc_inter_Icc, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total x y with h | h
  · rw [max_eq_right (by linarith), min_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), min_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring

variable {ι : Type*} (s : Finset ι) (w ξ : ι → ℝ)

/-- Local average `B_η(E) = (2η)⁻¹ ∑_k w_k 𝟙{|ξ_k - E| ≤ η}`. -/
def localAvg (η E : ℝ) : ℝ := (2 * η)⁻¹ * ∑ k ∈ s, w k * (Icc (ξ k - η) (ξ k + η)).indicator 1 E

/-- Collision kernel sum `∑_{k,l} w_k w_l (2η - |ξ_k - ξ_l|)₊`. -/
def collisionSum (η : ℝ) : ℝ := ∑ k ∈ s, ∑ l ∈ s, w k * w l * max (2 * η - |ξ k - ξ l|) 0

/-- Correlation count `C(r) = ∑_{k,l} w_k w_l 𝟙{|ξ_k - ξ_l| ≤ r}`. -/
def correlation (r : ℝ) : ℝ := ∑ k ∈ s, ∑ l ∈ s, if |ξ k - ξ l| ≤ r then w k * w l else 0

lemma integrable_inter (x y η : ℝ) :
    Integrable ((Icc (x - η) (x + η) ∩ Icc (y - η) (y + η)).indicator (1 : ℝ → ℝ)) volume := by
  rw [integrable_indicator_iff (measurableSet_Icc.inter measurableSet_Icc)]
  refine integrableOn_const ?_
  exact ((measure_mono inter_subset_left).trans_lt (by simp [Real.volume_Icc])).ne

/-- **Collision-energy identity** (Harper note, Lemma 4.2, eq. (10)). -/
theorem collision_identity {η : ℝ} (_hη : 0 < η) :
    ∫ E, localAvg s w ξ η E ^ 2 = (4 * η ^ 2)⁻¹ * collisionSum s w ξ η := by
  have hsq : ∀ E, localAvg s w ξ η E ^ 2 = (2 * η)⁻¹ ^ 2 * ∑ k ∈ s, ∑ l ∈ s,
      w k * w l * (Icc (ξ k - η) (ξ k + η) ∩ Icc (ξ l - η) (ξ l + η)).indicator 1 E := by
    intro E
    unfold localAvg
    rw [mul_pow, pow_two (∑ k ∈ s, w k * (Icc (ξ k - η) (ξ k + η)).indicator 1 E),
      Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [inter_indicator_one]; simp only [Pi.mul_apply]; ring
  simp_rw [hsq]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    · rw [inv_pow, mul_pow]; norm_num
    · unfold collisionSum
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul, integral_indicator_one (measurableSet_Icc.inter measurableSet_Icc),
          volume_window_inter]
      · intro l _
        exact (integrable_inter (ξ k) (ξ l) η).const_mul _
  · intro k _
    exact integrable_finsetSum _ fun l _ => (integrable_inter (ξ k) (ξ l) η).const_mul _

/-- **Collision bounds** (Harper note, eq. (11)): for nonnegative weights,
`C(η)/(4η) ≤ ∫ B_η² ≤ C(2η)/(2η)`. -/
theorem collision_bounds {η : ℝ} (hη : 0 < η) (hw : ∀ k ∈ s, 0 ≤ w k) :
    correlation s w ξ η / (4 * η) ≤ ∫ E, localAvg s w ξ η E ^ 2 ∧
      ∫ E, localAvg s w ξ η E ^ 2 ≤ correlation s w ξ (2 * η) / (2 * η) := by
  rw [collision_identity s w ξ hη]
  have hlow : η * correlation s w ξ η ≤ collisionSum s w ξ η := by
    unfold correlation collisionSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hkl := mul_nonneg (hw k hk) (hw l hl)
    split_ifs with h
    · have : η ≤ max (2 * η - |ξ k - ξ l|) 0 := le_max_of_le_left (by linarith)
      nlinarith
    · simp only [mul_zero]; exact mul_nonneg hkl (le_max_right _ _)
  have hup : collisionSum s w ξ η ≤ 2 * η * correlation s w ξ (2 * η) := by
    unfold correlation collisionSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hkl := mul_nonneg (hw k hk) (hw l hl)
    split_ifs with h
    · have : max (2 * η - |ξ k - ξ l|) 0 ≤ 2 * η :=
        max_le (by linarith [abs_nonneg (ξ k - ξ l)]) (by linarith)
      nlinarith
    · push Not at h
      rw [max_eq_right (by linarith)]; simp
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have : (4 * η ^ 2)⁻¹ * collisionSum s w ξ η * (4 * η) = collisionSum s w ξ η / η := by
      field_simp
    rw [this, le_div_iff₀ hη]; linarith
  · rw [le_div_iff₀ (by positivity)]
    have : (4 * η ^ 2)⁻¹ * collisionSum s w ξ η * (2 * η) = collisionSum s w ξ η / (2 * η) := by
      field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]; linarith

end ThomReductions
