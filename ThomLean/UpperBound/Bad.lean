import ThomLean.UpperBound.Maximal

/-!
# Round 8, Task 2 (continued): bad blocks of the chiral chain

For `N` an odd prime, `(p,t)` uniform on `(ℤ/N)²`, the bond logarithms of `H_{p,t}` are
`X_n = log |1 + ψ(t + p(n+1))|` (`Xs`). A block of length `2^ℓ` starting at site `s` is **bad**
(`badB T p t s ℓ`) when some alternating partial sum `|∑_{j<m} (−1)^j X_{s+j}|`, `m ≤ 2^ℓ`,
exceeds `T/4`.

`card_badB_le`: for `2^ℓ ≤ N` and `T ≥ 24`,
`#{(p,t) : bad} · T² ≤ 320 (ℓ+1)² 2^ℓ N²`, i.e. `P(bad block) ≤ 320 L (ℓ+1)²/T²` with `L = 2^ℓ`.

Proof: center (`μ = E X`, `|μ| ≤ √5 < 3`, so a bad block has a centered alternating partial sum
`> T/8` once `T ≥ 24`); the centered `(−1)^j (X_{s+j} − μ)` are orthogonal by `sum_pair`
(pairwise independence) with variance `≤ 5`, and `card_bad_le` (dyadic maximal inequality and
Chebyshev) gives `#bad · (T/8)² ≤ (ℓ+1)² 2^ℓ · 5N²`.
-/

noncomputable section

namespace ThomUpper

open ThomZeroLevel Real Finset

variable {N : ℕ} [NeZero N]
set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- Bond logarithm at site `n` of the chain `H_{p,t}`. -/
def Xs (p t : ZMod N) (n : ℕ) : ℝ := lb (t + p * ((n : ZMod N) + 1))

lemma Xs_eq (p t : ZMod N) (n : ℕ) : Xs p t n = Real.log ‖bond p t n‖ := rfl

/-- Alternating partial sums from site `s`. -/
def altS (p t : ZMod N) (s m : ℕ) : ℝ := ∑ j ∈ range m, (-1 : ℝ) ^ j * Xs p t (s + j)

/-- A bad block. -/
def badB (T : ℝ) (p t : ZMod N) (s ℓ : ℕ) : Prop := ∃ m ≤ 2 ^ ℓ, T / 4 < |altS p t s m|

instance (T : ℝ) (s ℓ : ℕ) : DecidablePred fun pt : ZMod N × ZMod N => badB T pt.1 pt.2 s ℓ :=
  fun _ => Classical.dec _

lemma sum_neg_one_pow (k : ℕ) : ∑ j ∈ range k, (-1 : ℝ) ^ j = if Even k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [Finset.sum_range_succ, ihk]
    rcases Nat.even_or_odd k with hk | hk
    · rw [if_pos hk, hk.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr hk.add_one)]; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr hk), hk.neg_one_pow, if_pos hk.add_one]; ring

lemma abs_sum_neg_one_pow_le (m : ℕ) : |∑ j ∈ range m, (-1 : ℝ) ^ j| ≤ 1 := by
  rw [sum_neg_one_pow]; split_ifs <;> norm_num

lemma natCast_sub_isUnit [Fact N.Prime] {i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j)
    (s : ℕ) : IsUnit ((((s + i : ℕ) : ZMod N) + 1) - (((s + j : ℕ) : ZMod N) + 1)) := by
  rw [isUnit_iff_ne_zero, add_sub_add_right_eq_sub, sub_ne_zero]
  intro h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have : i % N = j % N := Nat.ModEq.add_left_cancel' s h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact hij this

/-- Mean of the bond logarithm. -/
def muX (N : ℕ) [NeZero N] : ℝ := (∑ u : ZMod N, lb u) / N

lemma sum_lb_sub_mu : ∑ u : ZMod N, (lb u - muX N) = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, muX]
  field_simp; ring

lemma sum_lb_sub_mu_sq_le : ∑ u : ZMod N, (lb u - muX N) ^ 2 ≤ ∑ u : ZMod N, lb u ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h1 : ∑ u : ZMod N, (lb u - muX N) ^ 2 =
      ∑ u : ZMod N, lb u ^ 2 - 2 * muX N * ∑ u : ZMod N, lb u + N * muX N ^ 2 := by
    have e : ∀ u : ZMod N, (lb u - muX N) ^ 2 = lb u ^ 2 - 2 * muX N * lb u + muX N ^ 2 :=
      fun u => by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have h2 : ∑ u : ZMod N, lb u = N * muX N := by rw [muX]; field_simp
  rw [h1, h2]; nlinarith [sq_nonneg (muX N)]

lemma abs_muX_lt (hN : Odd N) : |muX N| < 3 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ZMod N => (1 : ℝ)) lb
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one] at hcs
  have h5 := sum_lb_sq_le hN
  have hm : muX N ^ 2 ≤ 5 := by
    rw [muX, div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_lt]; constructor <;> nlinarith

/-- **Probability of a bad block**: `#{(p,t) : bad} · T² ≤ 320 (ℓ+1)² 2^ℓ N²`. -/
theorem card_badB_le [Fact N.Prime] (hN : Odd N) {T : ℝ} (hT : 24 ≤ T) (s ℓ : ℕ)
    (hℓ : 2 ^ ℓ ≤ N) :
    (#{pt : ZMod N × ZMod N | badB T pt.1 pt.2 s ℓ} : ℝ) * T ^ 2 ≤
      320 * (ℓ + 1) ^ 2 * 2 ^ ℓ * N ^ 2 := by
  set μ := muX N
  set f : ZMod N → ℝ := fun u => lb u - μ
  let Y : ℕ → ZMod N × ZMod N → ℝ := fun j pt => (-1 : ℝ) ^ j * f (pt.2 + pt.1 * (((s + j : ℕ) : ZMod N) + 1))
  have horth : ∀ i < 2 ^ ℓ, ∀ j < 2 ^ ℓ, i ≠ j → ∑ pt, Y (0 + i) pt * Y (0 + j) pt = 0 := by
    intro i hi j hj hij
    simp only [zero_add, Y]
    have := sum_pair (natCast_sub_isUnit (by omega) (by omega) hij s) f f
    rw [sum_lb_sub_mu, zero_mul] at this
    calc ∑ pt : ZMod N × ZMod N, (-1 : ℝ) ^ i * f (pt.2 + pt.1 * (((s + i : ℕ) : ZMod N) + 1)) *
          ((-1 : ℝ) ^ j * f (pt.2 + pt.1 * (((s + j : ℕ) : ZMod N) + 1)))
        = (-1 : ℝ) ^ i * (-1) ^ j * ∑ pt : ZMod N × ZMod N,
            f (pt.2 + pt.1 * (((s + i : ℕ) : ZMod N) + 1)) *
              f (pt.2 + pt.1 * (((s + j : ℕ) : ZMod N) + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hV : ∀ j < 2 ^ ℓ, ∑ pt, Y (0 + j) pt ^ 2 ≤ N * (5 * N) := by
    intro j _
    set c : ZMod N := ((s + j : ℕ) : ZMod N) + 1
    have hsq : ∀ pt : ZMod N × ZMod N, Y (0 + j) pt ^ 2 = f (pt.2 + pt.1 * c) ^ 2 := by
      intro pt
      simp only [Y, zero_add, mul_pow, c]
      rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    simp_rw [hsq]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ p : ZMod N, ∑ t : ZMod N, f (t + p * c) ^ 2 = ∑ u : ZMod N, f u ^ 2 :=
      fun p => Fintype.sum_equiv (Equiv.addRight (p * c)) _ _ (fun _ => rfl)
    simp only [hrow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have h1 := sum_lb_sub_mu_sq_le (N := N)
    have h2 := sum_lb_sq_le hN
    have hNp : (0 : ℝ) ≤ N := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hNp
  have hc : (0 : ℝ) ≤ T / 8 := by linarith
  have hbad := card_bad_le Y ℓ 0 horth hV (c := T / 8) hc
  have hsub : ({pt : ZMod N × ZMod N | badB T pt.1 pt.2 s ℓ} : Finset _) ⊆
      ({pt | ∃ m ≤ 2 ^ ℓ, T / 8 < |psum Y 0 m pt|} : Finset _) := by
    intro pt hpt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpt ⊢
    obtain ⟨m, hm, hT4⟩ := hpt
    refine ⟨m, hm, ?_⟩
    have he : psum Y 0 m pt = altS pt.1 pt.2 s m - μ * ∑ j ∈ range m, (-1 : ℝ) ^ j := by
      simp only [psum, Y, zero_add, altS, f, Xs, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have h1 := abs_sum_neg_one_pow_le m
    have h2 := abs_muX_lt hN
    have h3 : |μ * ∑ j ∈ range m, (-1 : ℝ) ^ j| ≤ 3 := by
      rw [abs_mul]; nlinarith [abs_nonneg μ, abs_nonneg (∑ j ∈ range m, (-1 : ℝ) ^ j)]
    rw [he]
    have := abs_sub_abs_le_abs_sub (altS pt.1 pt.2 s m) (μ * ∑ j ∈ range m, (-1 : ℝ) ^ j)
    linarith
  have hcard : (#{pt : ZMod N × ZMod N | badB T pt.1 pt.2 s ℓ} : ℝ) ≤
      #{pt | ∃ m ≤ 2 ^ ℓ, T / 8 < |psum Y 0 m pt|} := by
    exact_mod_cast Finset.card_le_card hsub
  have hT2 : 0 ≤ (T / 8) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right hcard hT2
  nlinarith

end ThomUpper
