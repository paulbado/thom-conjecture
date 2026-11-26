import Mathlib.Tactic

/-!
# Simplicity of the Dirichlet eigenvalues (round 7, Task 3)

For the `L × L` Jacobi matrix with off-diagonal entries `1` and any real diagonal `d_1, …, d_L`
(in particular `d_j = 2cos(2π(θ + jα))`), a solution of `u_{j-1} + d_j u_j + u_{j+1} = E u_j`,
`1 ≤ j ≤ L`, with `u_0 = 0` is determined by `u_1` (`eig_proportional`). Hence every eigenspace
is one-dimensional and an eigenvector has `u_1 ≠ 0` (`eig_eq_zero_of_first`). This is the
simplicity needed for the analytic branches `E_{k,L}(α, θ)` and the Hellmann–Feynman formulas.
-/

namespace ThomDirichlet

/-- `u` solves the Dirichlet eigenvalue recursion on `1..L` (with `u 0 = 0`). -/
def IsEig (d : ℕ → ℝ) (L : ℕ) (E : ℝ) (u : ℕ → ℝ) : Prop :=
  u 0 = 0 ∧ ∀ j, 1 ≤ j → j ≤ L → u (j - 1) + d j * u j + u (j + 1) = E * u j

/-- **Eigenvectors are proportional**: `u_1 v_j = v_1 u_j` for `j ≤ L + 1`. -/
theorem eig_proportional {d : ℕ → ℝ} {L : ℕ} {E : ℝ} {u v : ℕ → ℝ} (hu : IsEig d L E u)
    (hv : IsEig d L E v) : ∀ j ≤ L + 1, u 1 * v j = v 1 * u j := by
  set w : ℕ → ℝ := fun j => u 1 * v j - v 1 * u j with hw
  suffices h : ∀ j ≤ L, w j = 0 ∧ w (j + 1) = 0 by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := (h 0 (Nat.zero_le _)).1; simp only [hw] at this; linarith
    · have := (h (j - 1) (by omega)).2
      rw [Nat.sub_add_cancel hj0] at this
      simp only [hw] at this; linarith
  intro j hj
  induction j with
  | zero => simp [hw, hu.1, hv.1]; ring
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨h2, ?_⟩
    have eu := hu.2 (j + 1) (by omega) hj
    have ev := hv.2 (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at eu ev
    simp only [hw] at h1 h2 ⊢
    linear_combination (u 1) * ev - (v 1) * eu - h1 + (E - d (j + 1)) * h2

/-- An eigenvector with `u_1 = 0` vanishes on `0..L+1`. -/
theorem eig_eq_zero_of_first {d : ℕ → ℝ} {L : ℕ} {E : ℝ} {u : ℕ → ℝ} (hu : IsEig d L E u)
    (h1 : u 1 = 0) : ∀ j ≤ L + 1, u j = 0 := by
  -- compare with the solution `v` with `v_1 = 1`; proportionality gives `u_j = 0`
  have key : ∀ j ≤ L, u j = 0 ∧ u (j + 1) = 0 := by
    intro j hj
    induction j with
    | zero => exact ⟨hu.1, h1⟩
    | succ j ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨b, ?_⟩
      have := hu.2 (j + 1) (by omega) hj
      simp only [Nat.add_sub_cancel, a, b, mul_zero, add_zero, zero_add] at this
      linarith
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact hu.1
  · have := (key (j - 1) (by omega)).2
    rwa [Nat.sub_add_cancel hj0] at this

end ThomDirichlet
