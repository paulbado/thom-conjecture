import ThomLean.Heisenberg.Threshold

/-!
# Kernel-checked small values (Bado–Pittet, Remark 3.4)

All values are verified by `decide` (kernel evaluation, no `native_decide`).

* `τ(A²) = 4`, `τ(A⁴) = 28`, `τ(A⁶) = 232`.
* `Q = 1` (`= 1²`, square case `m = 1`): `N_1 = 4` and `m₄^{(1)} - m₄ = 36 - 28 = 8 = 8m`.
* `Q = 2` (`= 1·2`, pronic case `m = 1`): `N_2 = 6` and `m₆^{(2)} - m₆ = 256 - 232 = 24 = 8(2m+1)`.
-/

namespace ThomHeisenberg

set_option maxRecDepth 100000

lemma kQ_eq_of {Q k : ℕ} (h1 : 4 * Q ≤ k ^ 2) (h2 : (k - 1) ^ 2 < 4 * Q) : kQ Q = k := by
  apply le_antisymm (kQ_le h1)
  by_contra h
  push Not at h
  have hle : kQ Q ≤ k - 1 := by omega
  have := kQ_spec Q
  have : kQ Q ^ 2 ≤ (k - 1) ^ 2 := Nat.pow_le_pow_left hle 2
  omega

theorem moment_two : moment 2 = 4 := by decide
theorem moment_four : moment 4 = 28 := by decide
theorem moment_six : moment 6 = 232 := by decide

theorem NQ_one : NQ 1 = 4 := by rw [NQ, kQ_eq_of (k := 2) (by norm_num) (by norm_num)]
theorem NQ_two : NQ 2 = 6 := by rw [NQ, kQ_eq_of (k := 3) (by norm_num) (by norm_num)]

theorem fluxMoment_one_four : fluxMoment 1 4 = 36 := by decide
theorem fluxMoment_two_six : fluxMoment 2 6 = 256 := by decide

/-- First discrepancy for `Q = 1 = 1²`: `8 m` with `m = 1`. -/
theorem discrepancy_Q1 : fluxMoment 1 (NQ 1) - moment (NQ 1) = 8 := by
  rw [NQ_one, fluxMoment_one_four, moment_four]

/-- First discrepancy for `Q = 2 = 1·2`: `8 (2m+1)` with `m = 1`. -/
theorem discrepancy_Q2 : fluxMoment 2 (NQ 2) - moment (NQ 2) = 24 := by
  rw [NQ_two, fluxMoment_two_six, moment_six]

end ThomHeisenberg
