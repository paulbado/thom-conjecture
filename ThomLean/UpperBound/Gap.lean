import ThomLean.UpperBound.Bad

/-!
# Round 8, Task 3: spectral gap of a good chiral block

A Dirichlet chiral block of even length `2m` with bonds `b_0, …, b_{2m-1}` acts by
`y_k = b_{k-1} η_{k-1} + conj(b_k) η_{k+1}` (`η_{-1} = η_{2m} = 0`). Reordered by parity it is
`J = [[0, B], [B*, 0]]` with `B` bidiagonal; the even rows determine the odd entries of `η`
forward and the odd rows determine the even entries backward. With `X_k = log|b_k|` and the
alternating sums `S_k = ∑_{j<k} (−1)^j X_j`, the explicit inverse entries are

`(B⁻¹)`-coefficient of `y_{2j}` in `η_{2i+1}` : modulus `e^{S_{2j} − S_{2i+1}}` (`j ≤ i`),
coefficient of `y_{2j+1}` in `η_{2i}` : modulus `e^{S_{2i} − S_{2j+1}}` (`j ≥ i`)

(products of bond moduli, `Π |b_odd| / Π |b_even|`). We prove the corresponding weighted
recursions (`fwd_bound`, `bwd_bound`) instead of manipulating products. For a **good** block,
`|S_k| ≤ T/4` for `k ≤ 2m`, so every coefficient is `≤ e^{T/2}` and

`chiral_gap`: `∑_k |η_k|² ≤ 4 m² e^T ∑_k |y_k|²`, i.e. `min |σ(J)| ≥ e^{−T/2}/(2m)`.

(The requested constant `e^{−T/2}/m` also follows from the coefficient bound with a sharper
Cauchy–Schwarz; the factor `2` is irrelevant below.)
-/

noncomputable section

namespace ThomUpper

open Real Finset ComplexConjugate

section Abstract

variable (b η y : ℕ → ℂ) (X S : ℕ → ℝ)

/-- Forward recursion (odd entries from even rows). -/
lemma fwd_bound (hX : ∀ k, ‖b k‖ = exp (X k)) (hS0 : S 0 = 0)
    (hS : ∀ k, S (k + 1) = S k + (-1) ^ k * X k) (hy0 : y 0 = conj (b 0) * η 1)
    (hy : ∀ k, 1 ≤ k → y k = b (k - 1) * η (k - 1) + conj (b k) * η (k + 1)) :
    ∀ i, ‖η (2 * i + 1)‖ * exp (S (2 * i + 1)) ≤
      ∑ j ∈ range (i + 1), exp (S (2 * j)) * ‖y (2 * j)‖ := by
  intro i
  induction i with
  | zero =>
    simp only [mul_zero, zero_add, range_one, sum_singleton, hS0, exp_zero, one_mul]
    rw [hS 0, hS0, pow_zero, one_mul, zero_add, ← hX 0, hy0, norm_mul, RCLike.norm_conj]
    linarith [mul_comm ‖η 1‖ ‖b 0‖]
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have hrow := hy (2 * (i + 1)) (by omega)
    have e1 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
    have e2 : 2 * (i + 1) + 1 = 2 * (i + 1) + 1 := rfl
    rw [e1] at hrow
    -- `|b_{2i+2}| |η_{2i+3}| ≤ |y_{2i+2}| + |b_{2i+1}| |η_{2i+1}|`
    have hineq : ‖b (2 * (i + 1))‖ * ‖η (2 * (i + 1) + 1)‖ ≤
        ‖y (2 * (i + 1))‖ + ‖b (2 * i + 1)‖ * ‖η (2 * i + 1)‖ := by
      have : conj (b (2 * (i + 1))) * η (2 * (i + 1) + 1) =
          y (2 * (i + 1)) - b (2 * i + 1) * η (2 * i + 1) := by rw [hrow]; ring
      have h := congrArg norm this
      rw [norm_mul, RCLike.norm_conj] at h
      rw [h, ← norm_mul]; exact norm_sub_le _ _
    -- weights
    have hS1 : S (2 * (i + 1)) = S (2 * i + 1) - X (2 * i + 1) := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, hS, (by exact Odd.neg_one_pow ⟨i, rfl⟩ :
        (-1 : ℝ) ^ (2 * i + 1) = -1)]; ring
    have hS2 : S (2 * (i + 1) + 1) = S (2 * (i + 1)) + X (2 * (i + 1)) := by
      rw [hS, (by exact Even.neg_one_pow ⟨i + 1, by ring⟩ : (-1 : ℝ) ^ (2 * (i + 1)) = 1)]; ring
    have w1 : exp (S (2 * (i + 1) + 1)) = exp (S (2 * (i + 1))) * ‖b (2 * (i + 1))‖ := by
      rw [hS2, exp_add, hX]
    have w2 : exp (S (2 * (i + 1))) * ‖b (2 * i + 1)‖ = exp (S (2 * i + 1)) := by
      rw [hS1, hX, ← exp_add]; ring_nf
    have hE := exp_pos (S (2 * (i + 1)))
    calc ‖η (2 * (i + 1) + 1)‖ * exp (S (2 * (i + 1) + 1))
        = exp (S (2 * (i + 1))) * (‖b (2 * (i + 1))‖ * ‖η (2 * (i + 1) + 1)‖) := by
          rw [w1]; ring
      _ ≤ exp (S (2 * (i + 1))) * (‖y (2 * (i + 1))‖ + ‖b (2 * i + 1)‖ * ‖η (2 * i + 1)‖) :=
          mul_le_mul_of_nonneg_left hineq hE.le
      _ = exp (S (2 * (i + 1))) * ‖y (2 * (i + 1))‖ + ‖η (2 * i + 1)‖ * exp (S (2 * i + 1)) := by
          rw [← w2]; ring
      _ ≤ _ := by linarith

/-- Backward recursion (even entries from odd rows), `η_{2m} = 0`. -/
lemma bwd_bound (m : ℕ) (hX : ∀ k, ‖b k‖ = exp (X k))
    (hS : ∀ k, S (k + 1) = S k + (-1) ^ k * X k)
    (hy : ∀ k, 1 ≤ k → y k = b (k - 1) * η (k - 1) + conj (b k) * η (k + 1))
    (hη : η (2 * m) = 0) :
    ∀ d i, i + d = m → ‖η (2 * i)‖ * exp (-S (2 * i)) ≤
      ∑ j ∈ Ico i m, exp (-S (2 * j + 1)) * ‖y (2 * j + 1)‖ := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp only [add_zero] at hi
    subst hi
    simp [hη]
  | succ d ih =>
    intro i hi
    have hlt : i < m := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    have ih' := ih (i + 1) (by omega)
    have hrow := hy (2 * i + 1) (by omega)
    rw [show 2 * i + 1 - 1 = 2 * i by omega, show 2 * i + 1 + 1 = 2 * (i + 1) by ring] at hrow
    have hineq : ‖b (2 * i)‖ * ‖η (2 * i)‖ ≤
        ‖y (2 * i + 1)‖ + ‖b (2 * i + 1)‖ * ‖η (2 * (i + 1))‖ := by
      have : b (2 * i) * η (2 * i) = y (2 * i + 1) - conj (b (2 * i + 1)) * η (2 * (i + 1)) := by
        rw [hrow]; ring
      have h := congrArg norm this
      rw [norm_mul] at h
      rw [h]
      calc ‖y (2 * i + 1) - conj (b (2 * i + 1)) * η (2 * (i + 1))‖
          ≤ ‖y (2 * i + 1)‖ + ‖conj (b (2 * i + 1)) * η (2 * (i + 1))‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, RCLike.norm_conj]
    have hS1 : S (2 * i + 1) = S (2 * i) + X (2 * i) := by
      rw [hS, (by exact Even.neg_one_pow ⟨i, by ring⟩ : (-1 : ℝ) ^ (2 * i) = 1)]; ring
    have hS2 : S (2 * (i + 1)) = S (2 * i + 1) - X (2 * i + 1) := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, hS, (by exact Odd.neg_one_pow ⟨i, rfl⟩ :
        (-1 : ℝ) ^ (2 * i + 1) = -1)]; ring
    have w1 : exp (-S (2 * i + 1)) * ‖b (2 * i)‖ = exp (-S (2 * i)) := by
      rw [hS1, hX, ← exp_add]; ring_nf
    have w2 : exp (-S (2 * i + 1)) * ‖b (2 * i + 1)‖ = exp (-S (2 * (i + 1))) := by
      rw [hS2, hX, ← exp_add]; ring_nf
    have hE := exp_pos (-S (2 * i + 1))
    calc ‖η (2 * i)‖ * exp (-S (2 * i))
        = exp (-S (2 * i + 1)) * (‖b (2 * i)‖ * ‖η (2 * i)‖) := by rw [← w1]; ring
      _ ≤ exp (-S (2 * i + 1)) * (‖y (2 * i + 1)‖ + ‖b (2 * i + 1)‖ * ‖η (2 * (i + 1))‖) :=
          mul_le_mul_of_nonneg_left hineq hE.le
      _ = exp (-S (2 * i + 1)) * ‖y (2 * i + 1)‖ + ‖η (2 * (i + 1))‖ * exp (-S (2 * (i + 1))) := by
          rw [← w2]; ring
      _ ≤ _ := by linarith

/-- **Spectral gap of a good chiral block**: `∑_{k<2m} |η_k|² ≤ 4 m² e^T ∑_{k<2m} |y_k|²`. -/
theorem chiral_gap (m : ℕ) (T : ℝ) (hX : ∀ k, ‖b k‖ = exp (X k)) (hS0 : S 0 = 0)
    (hS : ∀ k, S (k + 1) = S k + (-1) ^ k * X k) (hgood : ∀ k ≤ 2 * m, |S k| ≤ T / 4)
    (hy0 : y 0 = conj (b 0) * η 1)
    (hy : ∀ k, 1 ≤ k → y k = b (k - 1) * η (k - 1) + conj (b k) * η (k + 1))
    (hη : η (2 * m) = 0) :
    ∑ k ∈ range (2 * m), ‖η k‖ ^ 2 ≤ 4 * m ^ 2 * exp T * ∑ k ∈ range (2 * m), ‖y k‖ ^ 2 := by
  set Y1 := ∑ k ∈ range (2 * m), ‖y k‖
  have hY1 : 0 ≤ Y1 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- every entry is at most `e^{T/2} Y1`
  have hent : ∀ k < 2 * m, ‖η k‖ ≤ exp (T / 2) * Y1 := by
    intro k hk
    rcases Nat.even_or_odd k with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- even entry, backward
      have hi : i < m := by omega
      have hb := bwd_bound b η y X S m hX hS hy hη (m - i) i (by omega)
      rw [show i + i = 2 * i by ring]
      have hw : ∀ j ∈ Ico i m, exp (-S (2 * j + 1)) * ‖y (2 * j + 1)‖ ≤
          exp (T / 4) * ‖y (2 * j + 1)‖ := by
        intro j hj
        have := hgood (2 * j + 1) (by have := (Finset.mem_Ico.mp hj).2; omega)
        exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [neg_abs_le (S (2*j+1))]))
          (norm_nonneg _)
      have hsub : ∑ j ∈ Ico i m, ‖y (2 * j + 1)‖ ≤ Y1 := by
        have : ∑ j ∈ Ico i m, ‖y (2 * j + 1)‖ = ∑ k ∈ (Ico i m).image (fun j => 2 * j + 1), ‖y k‖ :=
          (Finset.sum_image (f := fun k => ‖y k‖) (g := fun j => 2 * j + 1)
            (fun a _ b _ h => by simp only at h; omega)).symm
        rw [this]
        exact Finset.sum_le_sum_of_subset_of_nonneg (by
          intro k hk; simp only [Finset.mem_image, Finset.mem_Ico] at hk
          obtain ⟨j, ⟨_, hj⟩, rfl⟩ := hk; simp only [Finset.mem_range]; omega)
          fun _ _ _ => norm_nonneg _
      have hlow : exp (-(T / 4)) ≤ exp (-S (2 * i)) :=
        exp_le_exp.mpr (by have := hgood (2 * i) (by omega); linarith [le_abs_self (S (2 * i))])
      have h1 : ‖η (2 * i)‖ * exp (-(T / 4)) ≤ exp (T / 4) * Y1 := by
        calc ‖η (2 * i)‖ * exp (-(T / 4)) ≤ ‖η (2 * i)‖ * exp (-S (2 * i)) :=
              mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
          _ ≤ _ := hb
          _ ≤ ∑ j ∈ Ico i m, exp (T / 4) * ‖y (2 * j + 1)‖ := Finset.sum_le_sum hw
          _ = exp (T / 4) * ∑ j ∈ Ico i m, ‖y (2 * j + 1)‖ := by rw [Finset.mul_sum]
          _ ≤ exp (T / 4) * Y1 := mul_le_mul_of_nonneg_left hsub (exp_pos _).le
      have : exp (T / 2) = exp (T / 4) * exp (T / 4) := by rw [← exp_add]; ring_nf
      have hE : exp (-(T / 4)) * exp (T / 4) = 1 := by rw [← exp_add]; simp
      have hpos := exp_pos (T / 4)
      calc _ = _ * (exp (-(T / 4)) * exp (T / 4)) := by rw [hE, mul_one]
        _ = (_ * exp (-(T / 4))) * exp (T / 4) := by ring
        _ ≤ (exp (T / 4) * Y1) * exp (T / 4) := mul_le_mul_of_nonneg_right h1 hpos.le
        _ = exp (T / 2) * Y1 := by rw [this]; ring
    · -- odd entry, forward
      have hi : i < m := by omega
      have hf := fwd_bound b η y X S hX hS0 hS hy0 hy i
      have hw : ∀ j ∈ range (i + 1), exp (S (2 * j)) * ‖y (2 * j)‖ ≤ exp (T / 4) * ‖y (2 * j)‖ := by
        intro j hj
        have := hgood (2 * j) (by have := Finset.mem_range.mp hj; omega)
        exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [le_abs_self (S (2 * j))]))
          (norm_nonneg _)
      have hsub : ∑ j ∈ range (i + 1), ‖y (2 * j)‖ ≤ Y1 := by
        have : ∑ j ∈ range (i + 1), ‖y (2 * j)‖ = ∑ k ∈ (range (i + 1)).image (fun j => 2 * j), ‖y k‖ :=
          (Finset.sum_image (f := fun k => ‖y k‖) (g := fun j => 2 * j)
            (fun a _ b _ h => by simp only at h; omega)).symm
        rw [this]
        exact Finset.sum_le_sum_of_subset_of_nonneg (by
          intro k hk; simp only [Finset.mem_image, Finset.mem_range] at hk
          obtain ⟨j, hj, rfl⟩ := hk; simp only [Finset.mem_range]; omega)
          fun _ _ _ => norm_nonneg _
      have hlow : exp (-(T / 4)) ≤ exp (S (2 * i + 1)) :=
        exp_le_exp.mpr (by have := hgood (2 * i + 1) (by omega); linarith [neg_abs_le (S (2 * i + 1))])
      have h1 : ‖η (2 * i + 1)‖ * exp (-(T / 4)) ≤ exp (T / 4) * Y1 := by
        calc ‖η (2 * i + 1)‖ * exp (-(T / 4)) ≤ ‖η (2 * i + 1)‖ * exp (S (2 * i + 1)) :=
              mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
          _ ≤ _ := hf
          _ ≤ ∑ j ∈ range (i + 1), exp (T / 4) * ‖y (2 * j)‖ := Finset.sum_le_sum hw
          _ = exp (T / 4) * ∑ j ∈ range (i + 1), ‖y (2 * j)‖ := by rw [Finset.mul_sum]
          _ ≤ exp (T / 4) * Y1 := mul_le_mul_of_nonneg_left hsub (exp_pos _).le
      have : exp (T / 2) = exp (T / 4) * exp (T / 4) := by rw [← exp_add]; ring_nf
      have hE : exp (-(T / 4)) * exp (T / 4) = 1 := by rw [← exp_add]; simp
      have hpos := exp_pos (T / 4)
      calc _ = _ * (exp (-(T / 4)) * exp (T / 4)) := by rw [hE, mul_one]
        _ = (_ * exp (-(T / 4))) * exp (T / 4) := by ring
        _ ≤ (exp (T / 4) * Y1) * exp (T / 4) := mul_le_mul_of_nonneg_right h1 hpos.le
        _ = exp (T / 2) * Y1 := by rw [this]; ring
  -- Cauchy–Schwarz
  have hCS : Y1 ^ 2 ≤ (2 * m) * ∑ k ∈ range (2 * m), ‖y k‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (range (2 * m)) (fun _ => (1 : ℝ)) (fun k => ‖y k‖)
    simpa [Y1] using this
  have hT : exp (T / 2) ^ 2 = exp T := by rw [← exp_nat_mul]; ring_nf
  calc ∑ k ∈ range (2 * m), ‖η k‖ ^ 2 ≤ ∑ k ∈ range (2 * m), (exp (T / 2) * Y1) ^ 2 :=
        Finset.sum_le_sum fun k hk => pow_le_pow_left₀ (norm_nonneg _) (hent k (mem_range.mp hk)) 2
    _ = (2 * m) * (exp T * Y1 ^ 2) := by simp [mul_pow, hT]
    _ ≤ (2 * m) * (exp T * ((2 * m) * ∑ k ∈ range (2 * m), ‖y k‖ ^ 2)) := by
        gcongr
    _ = 4 * m ^ 2 * exp T * ∑ k ∈ range (2 * m), ‖y k‖ ^ 2 := by ring

end Abstract

end ThomUpper
