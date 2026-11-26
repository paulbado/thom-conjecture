import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog

/-!
# Round 9, Task 3: determinants of open chiral chains

An open chiral (zero-diagonal, nearest-neighbour) chain of length `n` with bond amplitudes
`b 0, b 1, …` is the Hermitian tridiagonal matrix `chiral n b` with `J i (i+1) = b i`,
`J (i+1) i = conj (b i)`, all other entries `0`.

* `det_chiral_add_two`: `det J_{n+2}(b) = -|b 0|² det J_n(b ∘ (· + 2))`.
* `det_chiral_even`: `det J_{2m} = (-1)^m ∏_{j<m} |b_{2j}|²`.
* `det_chiral_odd`: `det J_{2m+1} = 0`.
* `prod_norm_one_add_root`: for odd `N`, `∏_{t<N} |1 + e^{2πit/N}| = 2`.
* `avg_logdet_grid`: for odd `N`, even bonds `b_{2j} = 1 + ω^{t + s(j)}` (ω a primitive `N`-th
  root of unity; the chain bonds `c(n) = 1 + ψ(t + p(n+1))` of `ThomZeroLevel.chainH` have this
  form with `s(j) = p(2j+1)`) and arbitrary odd bonds, the phase average of
  `(1/(2m)) log |det J_{2m}|` over the grid `t ∈ {0,…,N-1}` is exactly `log 2 / N`.
-/

noncomputable section

namespace ThomRound9

open Matrix Finset Complex

/-- The open chiral chain. -/
def chiral (n : ℕ) (b : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if (j : ℕ) = i + 1 then b i else if (i : ℕ) = j + 1 then star (b j) else 0

theorem det_chiral_add_two (n : ℕ) (b : ℕ → ℂ) :
    (chiral (n + 2) b).det = -(b 0 * star (b 0)) * (chiral n (fun k => b (k + 2))).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : chiral (n + 2) b 0 0 = 0 := by simp [chiral]
  have hrest : ∀ j : Fin n, chiral (n + 2) b 0 j.succ.succ = 0 := by
    intro j; simp [chiral]
  simp only [h0, hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  have h1 : chiral (n + 2) b 0 (Fin.succ 0) = b 0 := by simp [chiral]
  rw [h1]
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have hc0 : ((chiral (n + 2) b).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove) 0 0 =
      star (b 0) := by
    simp [chiral, Fin.succAbove]
  have hcrest : ∀ i : Fin n,
      ((chiral (n + 2) b).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove) i.succ 0 = 0 := by
    intro i; simp [chiral, Fin.succAbove]
  simp only [hcrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hc0]
  have hsub : (((chiral (n + 2) b).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove).submatrix
      (Fin.succAbove 0) Fin.succ) = chiral n (fun k => b (k + 2)) := by
    ext i j
    simp only [submatrix_apply, Fin.succAbove_zero]
    have : (Fin.succ (0 : Fin (n + 1))).succAbove j.succ = j.succ.succ := by
      rw [Fin.succAbove_of_le_castSucc]
      rw [Fin.le_def]; simp
    rw [this]
    simp only [chiral, Fin.val_succ]
    by_cases h1 : (j : ℕ) = i + 1
    · have h1' : (j : ℕ) + 1 + 1 = i + 1 + 1 + 1 := by omega
      rw [if_pos h1', if_pos h1]
    · have h1' : ¬ ((j : ℕ) + 1 + 1 = i + 1 + 1 + 1) := by omega
      rw [if_neg h1', if_neg h1]
      by_cases h2 : (i : ℕ) = j + 1
      · have h2' : (i : ℕ) + 1 + 1 = j + 1 + 1 + 1 := by omega
        rw [if_pos h2', if_pos h2]
      · have h2' : ¬ ((i : ℕ) + 1 + 1 = j + 1 + 1 + 1) := by omega
        rw [if_neg h2', if_neg h2]
  rw [hsub]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, zero_add, pow_one]
  ring

theorem det_chiral_even (m : ℕ) (b : ℕ → ℂ) :
    (chiral (2 * m) b).det = (-1) ^ m * ∏ j ∈ range m, (b (2 * j) * star (b (2 * j))) := by
  induction m generalizing b with
  | zero => simp [Matrix.det_isEmpty]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, det_chiral_add_two, ih, prod_range_succ']
    simp only [mul_zero]
    have : ∀ j, b (2 * j + 2) = b (2 * (j + 1)) := fun j => by ring_nf
    simp only [this, pow_succ]
    ring

theorem det_chiral_odd (m : ℕ) (b : ℕ → ℂ) : (chiral (2 * m + 1) b).det = 0 := by
  induction m generalizing b with
  | zero =>
    show (chiral 1 b).det = 0
    rw [Matrix.det_unique]; simp [chiral]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, det_chiral_add_two, ih, mul_zero]

/-- `|det J_{2m}| = ∏_{j<m} |b_{2j}|²`. -/
theorem norm_det_chiral_even (m : ℕ) (b : ℕ → ℂ) :
    ‖(chiral (2 * m) b).det‖ = ∏ j ∈ range m, ‖b (2 * j)‖ ^ 2 := by
  rw [det_chiral_even, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [norm_mul, norm_star, sq]

/-- `log |det J_{2m}| = 2 ∑_{j<m} log |b_{2j}|` when the even bonds are nonzero. -/
theorem log_norm_det_chiral_even (m : ℕ) (b : ℕ → ℂ) (hb : ∀ j < m, b (2 * j) ≠ 0) :
    Real.log ‖(chiral (2 * m) b).det‖ = 2 * ∑ j ∈ range m, Real.log ‖b (2 * j)‖ := by
  rw [norm_det_chiral_even, Real.log_prod, mul_sum]
  · refine sum_congr rfl fun j _ => ?_
    rw [Real.log_pow]; push_cast; ring
  · intro j hj
    have := hb j (mem_range.1 hj)
    positivity

/-- For odd `N`, `∏_{t<N} (1 + ω^t) = 2` for a primitive `N`-th root of unity `ω`. -/
theorem prod_one_add_root {N : ℕ} (hN : Odd N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) :
    ∏ t ∈ range N, (1 + ω ^ t) = 2 := by
  have hpos : 0 < N := hN.pos
  have h := X_pow_sub_C_eq_prod hω hpos (α := 1) (a := 1) (one_pow N)
  have he := congrArg (Polynomial.eval (-1 : ℂ)) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, mul_one, hN.neg_one_pow] at he
  have : ∏ t ∈ range N, (-1 - ω ^ t) = (-1) ^ N * ∏ t ∈ range N, (1 + ω ^ t) := by
    have hc : ((-1 : ℂ)) ^ N = ∏ _t ∈ range N, (-1 : ℂ) := by rw [prod_const, card_range]
    rw [hc, ← prod_mul_distrib]
    exact prod_congr rfl fun t _ => by ring
  rw [this, hN.neg_one_pow] at he
  linear_combination he

theorem prod_norm_one_add_root {N : ℕ} (hN : Odd N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) :
    ∏ t ∈ range N, ‖1 + ω ^ t‖ = 2 := by
  rw [← norm_prod, prod_one_add_root hN hω]; simp

theorem one_add_root_ne_zero {N : ℕ} (hN : Odd N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) (t : ℕ) :
    1 + ω ^ t ≠ 0 := by
  intro h
  have h2 := prod_one_add_root hN hω
  have hmem : t % N ∈ range N := mem_range.2 (Nat.mod_lt _ hN.pos)
  have hzero : 1 + ω ^ (t % N) = 0 := by
    rw [← h, ← Nat.div_add_mod t N, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul,
      Nat.div_add_mod]
  rw [prod_eq_zero hmem hzero] at h2
  norm_num at h2

/-- `∑_{t<N} log |1 + ω^t| = log 2` for odd `N`. -/
theorem sum_log_one_add_root {N : ℕ} (hN : Odd N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) :
    ∑ t ∈ range N, Real.log ‖1 + ω ^ t‖ = Real.log 2 := by
  rw [← Real.log_prod, prod_norm_one_add_root hN hω]
  intro t _
  exact norm_ne_zero_iff.2 (one_add_root_ne_zero hN hω t)

/-- Shift invariance of grid sums over `N`-th roots of unity. -/
theorem sum_range_root_shift {N : ℕ} (hN : 0 < N) {ω : ℂ} (hω : ω ^ N = 1) (f : ℂ → ℝ) (s : ℕ) :
    ∑ t ∈ range N, f (ω ^ (t + s)) = ∑ t ∈ range N, f (ω ^ t) := by
  induction s with
  | zero => simp
  | succ s ih =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [← ih]
    have h1 := sum_range_succ' (fun t => f (ω ^ (t + s))) (n + 1)
    have h2 := sum_range_succ (fun t => f (ω ^ (t + s))) (n + 1)
    have hp : ω ^ (n + 1 + s) = ω ^ (0 + s) := by rw [pow_add, hω, one_mul, zero_add]
    simp only [show ∀ t, t + (s + 1) = t + 1 + s from fun t => by ring]
    rw [hp] at h2
    linarith

/-- **Grid average of the normalized log-determinant.** For odd `N`, `ω` a primitive `N`-th root
of unity, `m ≥ 1`, any offsets `s : ℕ → ℕ` and any bonds `b t` whose even entries are
`b t (2j) = 1 + ω^{t + s j}`, the phase average of `(1/(2m)) log|det J_{2m}(b t)|` is
`log 2 / N`. -/
theorem avg_logdet_grid {N : ℕ} (hN : Odd N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) (s : ℕ → ℕ) (m : ℕ)
    (hm : 0 < m) (b : ℕ → ℕ → ℂ) (hb : ∀ t j, b t (2 * j) = 1 + ω ^ (t + s j)) :
    (1 / N : ℝ) * ∑ t ∈ range N, (1 / (2 * m : ℝ)) * Real.log ‖(chiral (2 * m) (b t)).det‖ =
      Real.log 2 / N := by
  have hlog : ∀ t, Real.log ‖(chiral (2 * m) (b t)).det‖ =
      2 * ∑ j ∈ range m, Real.log ‖1 + ω ^ (t + s j)‖ := by
    intro t
    rw [log_norm_det_chiral_even m (b t) (fun j _ => by rw [hb]; exact one_add_root_ne_zero hN hω _)]
    simp only [hb]
  simp only [hlog]
  rw [← mul_sum, ← mul_sum, sum_comm]
  have hs : ∀ j ∈ range m, ∑ t ∈ range N, Real.log ‖1 + ω ^ (t + s j)‖ = Real.log 2 := by
    intro j _
    rw [sum_range_root_shift hN.pos hω.pow_eq_one (fun z => Real.log ‖1 + z‖) (s j)]
    exact sum_log_one_add_root hN hω
  rw [sum_congr rfl hs, sum_const, card_range, nsmul_eq_mul]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

/-- **Continuous-phase model.** The circle average of `log |1 + z|` over `|z| = 1` vanishes
(Mathlib's Jensen-type evaluation `circleAverage_log_norm_add_const_eq_posLog`). Hence for the
continuous-phase model the averaged normalized log-determinant is `0`, against `log 2 / N` on
odd grids. -/
theorem circleAverage_log_one_add :
    Real.circleAverage (fun z : ℂ => Real.log ‖1 + z‖) 0 1 = 0 := by
  have h := circleAverage_log_norm_add_const_eq_posLog (a := (1 : ℂ))
  simp only [norm_one, Real.posLog_one] at h
  simpa [add_comm] using h

end ThomRound9
