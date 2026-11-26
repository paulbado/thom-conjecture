import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The pointwise inequality behind the coarea entropy bound (round 7, Task 4)

For fixed `θ`, the `α`-averaged spectral density of the Dirichlet Harper matrices is
`g(E) = ∑_{i=1}^{M(E)} a_i(E)`, `a_i = 1/(L |∂_α E_{k_i}(α_i)|)`, a sum over the `M(E)` actual
preimages `(k_i, α_i)` of `E`. By the coarea (change of variables) formula
`∫ φ(E) g(E) dE = L⁻¹ ∑_k ∫_0^1 φ(E_k(α)) dα`, so

`∫ g log g dE ≤ ∫ ∑_i a_i log(M a_i) dE = L⁻¹ ∑_k ∫_0^1 log(M(E_k)/(L|∂_α E_k|)) dα`

follows from the pointwise inequality `S log S ≤ ∑_i a_i log(M a_i)`, `S = ∑_i a_i`, proved here
(`sum_mul_log_sum_le`, Jensen for `x log x` with equal weights `1/M` at the points `M a_i`).
The coarea formula itself is classical and is not formalized.
-/

namespace ThomDirichlet

open Real Finset

/-- `S log S ≤ ∑ a_i log(M a_i)` for `a_i ≥ 0`, `S = ∑ a_i`, `M = #s`. -/
theorem sum_mul_log_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) * log (∑ i ∈ s, a i) ≤ ∑ i ∈ s, a i * log (#s * a i) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hM : (0 : ℝ) < #s := by exact_mod_cast hne.card_pos
  have hJ := convexOn_mul_log.map_sum_le (t := s) (w := fun _ => 1 / (#s : ℝ))
    (p := fun i => #s * a i) (fun i _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.mpr (mul_nonneg hM.le (ha i hi)))
  simp only [smul_eq_mul] at hJ
  have e1 : ∑ i ∈ s, 1 / (#s : ℝ) * (#s * a i) = ∑ i ∈ s, a i :=
    sum_congr rfl fun i _ => by field_simp
  have e2 : ∑ i ∈ s, 1 / (#s : ℝ) * (#s * a i * log (#s * a i)) =
      ∑ i ∈ s, a i * log (#s * a i) := sum_congr rfl fun i _ => by field_simp
  rw [e1, e2] at hJ
  exact hJ

end ThomDirichlet
