import ThomLean.ZeroLevel.Quasimode
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Trigonometric control of the quasimode near half flux

Write `P = val p`, `δ = P/N - 1/2` and `θ = val(t + p(s+1))/N`. Then

`|c_j|² = 4 cos²(π(θ + 2jδ))`, `|d_j|² = 4 sin²(π(θ + (2j+1)δ))`.

For `θ ∈ [1/16, 1/8]`, `0 < δ ≤ 1/256`, `2mδ ≤ 1/32`, `2Mδ ≤ 11/32`, `9/32 ≤ 2(M-m+1)δ`:

* the first `m` ratios satisfy `|c_j| ≥ (3/2)|d_j|` (phases in `[1/16, 5/32]`);
* the last `m` ratios satisfy `|c_j| ≤ (2/3)|d_j|` (phases in `[11/32 - 1/128, 15/32]`);
* every `d_j`, `j < M`, is nonzero (phases in `(0, 1)`).

With `qm_bound` this gives `‖H ξ‖² ≤ 16 (4/9)^m ‖ξ‖²` (`qm_of_phase`). For instance
`m = ⌊1/(64δ)⌋`, `M = ⌊5/(32δ)⌋` satisfy the hypotheses (the choice in the round-6 plan).
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomExistence Finset ComplexConjugate Real

variable {N : ℕ} [NeZero N]

lemma normSq_one_add_psi (x0 p : ZMod N) (k : ℕ) :
    Complex.normSq (1 + ψ (x0 + (k : ZMod N) * p)) =
      4 * cos (π * (((x0.val : ℝ) + k * p.val) / N)) ^ 2 := by
  have hc : x0 + (k : ZMod N) * p = ((x0.val + k * p.val : ℕ) : ZMod N) := by
    push_cast; simp [ZMod.natCast_zmod_val]
  set y : ℝ := π * (((x0.val : ℝ) + k * p.val) / N)
  have he : (2 * (π : ℂ) * Complex.I * ((x0.val + k * p.val : ℕ) : ℂ) / N) =
      ((2 * y : ℝ) : ℂ) * Complex.I := by
    simp only [y]; push_cast; ring
  rw [hc, ψ, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, he, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.add_im,
    Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_add]
  rw [cos_two_mul, sin_two_mul]
  have := sin_sq_add_cos_sq y
  linear_combination (4 * cos y ^ 2) * this

lemma cos_add_nat_mul_pi_sq (x : ℝ) (j : ℕ) : cos (x + j * π) ^ 2 = cos x ^ 2 := by
  rw [cos_add, sin_nat_mul_pi, mul_zero, sub_zero, mul_pow]
  have := sin_sq_add_cos_sq ((j : ℝ) * π)
  rw [sin_nat_mul_pi] at this
  nlinarith

/-- Phase of the chain at start `s`. -/
def theta (p t : ZMod N) (s : ℕ) : ℝ := ((t + p * ((s : ZMod N) + 1)).val : ℝ) / N

/-- Distance of the flux `val p / N` from `1/2`. -/
def dlt (N : ℕ) (p : ZMod N) : ℝ := (p.val : ℝ) / N - 1 / 2

lemma normSq_ce (p t : ZMod N) (s j : ℕ) :
    Complex.normSq (bond p t (xs N s j)) = 4 * cos (π * (theta p t s + 2 * j * dlt N p)) ^ 2 := by
  have h : t + p * (xs N s j + 1) = (t + p * ((s : ZMod N) + 1)) + ((2 * j : ℕ) : ZMod N) * p := by
    simp only [xs]; push_cast; ring
  rw [bond, h, normSq_one_add_psi]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : π * ((((t + p * ((s : ZMod N) + 1)).val : ℝ) + ((2 * j : ℕ) : ℝ) * p.val) / N) =
      π * (theta p t s + 2 * j * dlt N p) + j * π := by
    simp only [theta, dlt]; push_cast; field_simp; ring
  rw [this, cos_add_nat_mul_pi_sq]

lemma normSq_co (p t : ZMod N) (s j : ℕ) :
    Complex.normSq (bond p t (ys N s j)) =
      4 * sin (π * (theta p t s + (2 * j + 1) * dlt N p)) ^ 2 := by
  have h : t + p * (ys N s j + 1) =
      (t + p * ((s : ZMod N) + 1)) + ((2 * j + 1 : ℕ) : ZMod N) * p := by
    simp only [ys]; push_cast; ring
  rw [bond, h, normSq_one_add_psi]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : π * ((((t + p * ((s : ZMod N) + 1)).val : ℝ) + ((2 * j + 1 : ℕ) : ℝ) * p.val) / N) =
      (π * (theta p t s + (2 * j + 1) * dlt N p) + π / 2) + j * π := by
    simp only [theta, dlt]; push_cast; field_simp; ring
  rw [this, cos_add_nat_mul_pi_sq, cos_add_pi_div_two, neg_sq]

/-- First block: `(3/2) sin(πb) ≤ cos(πa)` for phases in `[1/16, 5/32]`. -/
lemma trig_first {a b : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 5 / 32) (hb : 0 ≤ b)
    (hb' : b ≤ 5 / 32 + 1 / 256) : 3 / 2 * sin (π * b) ≤ cos (π * a) := by
  have hπ := pi_lt_d4
  have hπ0 := pi_pos
  have e1 : sin (π * b) ≤ π * b := sin_le (by positivity)
  have e2 : 1 - (π * a) ^ 2 / 2 ≤ cos (π * a) := one_sub_sq_div_two_le_cos
  have e3 : (π * a) ^ 2 ≤ (π * (5 / 32)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ha' hπ0.le) 2
  have e4 : π * b ≤ π * (5 / 32 + 1 / 256) := mul_le_mul_of_nonneg_left hb' hπ0.le
  have e5 : π ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ hπ0.le hπ.le 2
  nlinarith

/-- Last block: `0 ≤ cos(πa) ≤ (2/3) sin(πb)` for phases in `[11/32 - 1/128, 15/32 + 1/256]`. -/
lemma trig_last {a b : ℝ} (ha : 11 / 32 - 1 / 128 ≤ a) (ha' : a ≤ 15 / 32)
    (hb : 11 / 32 - 1 / 128 ≤ b) (hb' : b ≤ 15 / 32 + 1 / 256) :
    0 ≤ cos (π * a) ∧ cos (π * a) ≤ 2 / 3 * sin (π * b) := by
  have hπ := pi_lt_d4
  have hπ0 := pi_pos
  constructor
  · apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith
  have e1 : cos (π * a) = sin (π * (1 / 2 - a)) := by
    rw [← sin_pi_div_two_sub]; congr 1; ring
  have e2 : sin (π * b) = cos (π * (1 / 2 - b)) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  have f1 : sin (π * (1 / 2 - a)) ≤ π * (1 / 2 - a) := sin_le (by nlinarith)
  have f2 : 1 - (π * (1 / 2 - b)) ^ 2 / 2 ≤ cos (π * (1 / 2 - b)) := one_sub_sq_div_two_le_cos
  have f3 : (π * (1 / 2 - b)) ^ 2 ≤ (π * (21 / 128)) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) (mul_le_mul_of_nonneg_left (by linarith) hπ0.le) 2
  have f4 : π * (1 / 2 - a) ≤ π * (21 / 128) := mul_le_mul_of_nonneg_left (by linarith) hπ0.le
  have f5 : π ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ hπ0.le hπ.le 2
  rw [e1, e2]
  nlinarith

/-- **The explicit quasimode at a good phase.** -/
theorem qm_of_phase (p t : ZMod N) {s M m : ℕ} (hsM : s + 2 * M < N)
    (hθ1 : 1 / 16 ≤ theta p t s) (hθ2 : theta p t s ≤ 1 / 8)
    (hδ0 : 0 < dlt N p) (hδ1 : dlt N p ≤ 1 / 256)
    (h1 : 2 * m * dlt N p ≤ 1 / 32) (h2 : 2 * M * dlt N p ≤ 11 / 32)
    (h3 : 9 / 32 ≤ 2 * ((M : ℝ) - m + 1) * dlt N p) :
    nrm (chainH p t (qmXi p t s M)) ≤ 16 * (4 / 9 : ℝ) ^ m * nrm (qmXi p t s M) ∧
      1 ≤ nrm (qmXi p t s M) := by
  set θ := theta p t s
  set δ := dlt N p
  have hπ0 := pi_pos
  have hmM : m ≤ M := by
    by_contra h
    push Not at h
    have : (M : ℝ) + 1 ≤ m := by exact_mod_cast h
    nlinarith
  have hco : ∀ j < M, bond p t (ys N s j) ≠ 0 := by
    intro j hj
    have hjr : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj
    rw [← Complex.normSq_pos, normSq_co]
    have hb0 : 0 < θ + (2 * j + 1) * δ := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hb1 : θ + (2 * j + 1) * δ < 1 := by nlinarith
    have := sin_pos_of_pos_of_lt_pi (mul_pos hπ0 hb0) (by nlinarith)
    positivity
  refine qm_bound p t hsM hmM hco ?_ ?_
  · intro j hj
    have hjr : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [normSq_ce, normSq_co]
    have ht := trig_first (a := θ + 2 * j * δ) (b := θ + (2 * j + 1) * δ)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    have hb0 : 0 ≤ θ + (2 * j + 1) * δ := by positivity
    have hb1 : θ + (2 * j + 1) * δ ≤ 1 := by nlinarith
    have hs : 0 ≤ sin (π * (θ + (2 * j + 1) * δ)) :=
      sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hπ0.le hb0) (mul_le_of_le_one_right hπ0.le hb1)
    nlinarith
  · intro j hj1 hj2
    have hjr : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj2
    have hjm : (M : ℝ) ≤ j + m := by exact_mod_cast (show M ≤ j + m by omega)
    rw [normSq_ce, normSq_co]
    have ht := trig_last (a := θ + 2 * j * δ) (b := θ + (2 * j + 1) * δ)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    nlinarith

end ThomZeroLevel
