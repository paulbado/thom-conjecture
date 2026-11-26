import ThomLean.ZeroLevel.Trig
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Round 8, Task 1: the logarithmic chiral coefficients

For `N = n + 1` odd and `u ∈ ℤ/N`, let `X(u) = log |1 + ψ(u)|` (`lb`), where
`|1 + ψ(u)| = 2|cos(π val(u)/N)|` is the modulus of a bond of the chain operator `H_{p,t}`
(`ThomZeroLevel.bond p t n = 1 + ψ(t + p(n+1))`).

* `pair_bijective`, `sum_pair`: for `a - b` a unit (e.g. `N` prime, `a ≠ b`), the map
  `(p,t) ↦ (t + p a, t + p b)` is a bijection of `(ℤ/N)²`, hence
  `∑_{p,t} f(t + p a) g(t + p b) = (∑ f)(∑ g)`: the bond logarithms at two distinct sites are
  pairwise independent under the uniform law of `(p,t)`.
* `sum_lb_sq_le`: `∑_u X(u)² ≤ 5N`, i.e. `E[X_j²] ≤ 5`. The proof uses
  `4|v/N − 1/2| ≤ 2|cos(πv/N)| ≤ 2`, the elementary bound `log² x ≤ 2.2/√x` on `(0,1]`, and a
  telescoping comparison `∑_v |N − 2v|^{-1/2} ≤ 2√(N+1)` (the discrete analogue of
  `∫ |x|^{-1/2}`), in place of the comparison with `∫₀¹ log² x dx = 2`.
-/

noncomputable section

namespace ThomUpper

open ThomZeroLevel Real Finset

variable {N : ℕ} [NeZero N]
set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- Logarithm of the bond modulus, `X(u) = log |1 + ψ(u)|`. -/
def lb (u : ZMod N) : ℝ := Real.log ‖(1 : ℂ) + ψ u‖

/-! ### Pairwise independence -/

/-- `(p,t) ↦ (t + p a, t + p b)` is bijective when `a - b` is a unit. -/
theorem pair_bijective {a b : ZMod N} (hab : IsUnit (a - b)) :
    Function.Bijective (fun pt : ZMod N × ZMod N => (pt.2 + pt.1 * a, pt.2 + pt.1 * b)) := by
  obtain ⟨w, hw⟩ := hab
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun xy => ((xy.1 - xy.2) * ↑w⁻¹, xy.1 - (xy.1 - xy.2) * ↑w⁻¹ * a), ?_, ?_⟩
  · intro pt
    obtain ⟨p, t⟩ := pt
    have h1 : (t + p * a - (t + p * b)) * ↑w⁻¹ = p := by
      rw [show t + p * a - (t + p * b) = p * (a - b) by ring, ← hw, mul_assoc, Units.mul_inv,
        mul_one]
    simp only [h1]; ext <;> simp
  · intro xy
    obtain ⟨x, y⟩ := xy
    have hw' : (a - b) * ↑w⁻¹ = 1 := by rw [← hw, Units.mul_inv]
    ext
    · simp only; ring
    · simp only
      linear_combination (y - x) * hw'

/-- **Pairwise independence**: `∑_{p,t} f(t + p a) g(t + p b) = (∑ f)(∑ g)` when `a - b` is a
unit. -/
theorem sum_pair {a b : ZMod N} (hab : IsUnit (a - b)) (f g : ZMod N → ℝ) :
    ∑ pt : ZMod N × ZMod N, f (pt.2 + pt.1 * a) * g (pt.2 + pt.1 * b) =
      (∑ u, f u) * ∑ u, g u := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_bijective _ (pair_bijective hab) _ _ fun _ => rfl

/-- Counting form of pairwise independence. -/
theorem card_pair {a b : ZMod N} (hab : IsUnit (a - b)) (A B : Set (ZMod N))
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    (#{pt : ZMod N × ZMod N | pt.2 + pt.1 * a ∈ A ∧ pt.2 + pt.1 * b ∈ B} : ℝ) =
      #{u : ZMod N | u ∈ A} * #{u : ZMod N | u ∈ B} := by
  have := sum_pair hab (fun u => if u ∈ A then 1 else 0) (fun u => if u ∈ B then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_boole] at this
  rw [← this, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun pt _ => ?_
  by_cases h1 : pt.2 + pt.1 * a ∈ A <;> by_cases h2 : pt.2 + pt.1 * b ∈ B <;> simp [h1, h2]

/-! ### The bond modulus -/

lemma norm_one_add_psi (u : ZMod N) : ‖(1 : ℂ) + ψ u‖ = 2 * |cos (π * (u.val / N))| := by
  have h := normSq_one_add_psi u 0 0
  simp only [Nat.cast_zero, zero_mul, add_zero, CharP.cast_eq_zero] at h
  rw [Complex.norm_def, h, show (4 : ℝ) * cos (π * (u.val / N)) ^ 2 =
    (2 * |cos (π * (u.val / N))|) ^ 2 by rw [mul_pow, sq_abs]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- Jordan's inequality in the form `|N - 2v|/N ≤ |cos(πv/N)|` for `v ≤ N`. -/
lemma abs_sub_le_abs_cos {v : ℕ} (hv : v ≤ N) :
    |(N : ℝ) - 2 * v| / N ≤ |cos (π * (v / N))| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  set x : ℝ := π / 2 - π * (v / N)
  have hcos : cos (π * (v / N)) = sin x := by rw [Real.sin_pi_div_two_sub]
  have hvN : (v : ℝ) / N ≤ 1 := by rw [div_le_one hN]; exact_mod_cast hv
  have hv0 : (0 : ℝ) ≤ v / N := by positivity
  have hx : |x| ≤ π / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hvN Real.pi_pos.le
    have h2 := mul_nonneg Real.pi_pos.le hv0
    rw [abs_le]; constructor <;> simp only [x] <;> linarith
  have hxe : |(N : ℝ) - 2 * v| / N = 2 / π * |x| := by
    have : x = π * (N - 2 * v) / (2 * N) := by simp only [x]; field_simp
    rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0:ℝ) < 2 * N)]
    field_simp
  rw [hxe, hcos]
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx ⊢
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]))]
    exact Real.mul_le_sin h0 hx
  · rw [abs_of_neg h0] at hx ⊢
    have hs : sin x ≤ 0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ -x) (by linarith [Real.pi_pos])
      rw [Real.sin_neg] at this; linarith
    rw [abs_of_nonpos hs, ← Real.sin_neg]
    exact Real.mul_le_sin (by linarith) hx

/-- `log² x ≤ 2.2/√x` on `(0,1]`. -/
lemma log_sq_le_inv_sqrt {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : log x ^ 2 ≤ 2.2 / √x := by
  have hs : 0 < √x := Real.sqrt_pos.mpr hx
  have hss : 0 < √(√x) := Real.sqrt_pos.mpr hs
  set z : ℝ := 1 / √(√x)
  have hz : 0 < z := by positivity
  have hlz : log z = -(log x / 4) := by
    simp only [z, one_div, Real.log_inv, Real.log_sqrt hs.le, Real.log_sqrt hx.le]; ring
  have he := Real.exp_one_gt_d9
  have hle : log z ≤ z / exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hz (Real.exp_pos 1))
    rw [Real.log_div hz.ne' (Real.exp_pos 1).ne', Real.log_exp] at this; linarith
  have hlx : log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hz2 : z ^ 2 = 1 / √x := by
    simp only [z, div_pow, one_pow, Real.sq_sqrt hs.le]
  have h1 : -log x ≤ 4 * z / exp 1 := by
    rw [show 4 * z / exp 1 = 4 * (z / exp 1) by ring]; linarith
  have h2 : log x ^ 2 ≤ 16 * z ^ 2 / exp 1 ^ 2 := by
    have h0 : 0 ≤ -log x := by linarith
    have := pow_le_pow_left₀ h0 h1 2
    rw [neg_sq] at this
    calc log x ^ 2 ≤ (4 * z / exp 1) ^ 2 := this
      _ = 16 * z ^ 2 / exp 1 ^ 2 := by ring
  rw [hz2] at h2
  have he2 : (7.38 : ℝ) ≤ exp 1 ^ 2 := by nlinarith
  calc log x ^ 2 ≤ 16 * (1 / √x) / exp 1 ^ 2 := h2
    _ ≤ 16 * (1 / √x) / 7.38 := by gcongr
    _ ≤ 2.2 / √x := by rw [div_le_div_iff₀ (by norm_num) hs]; field_simp; nlinarith

/-- Pointwise bound: `X(u)² ≤ log² 2 + 2.2 √(N/2) / √|N − 2 val u|` for `N` odd. -/
lemma lb_sq_le (hN : Odd N) (u : ZMod N) :
    lb u ^ 2 ≤ log 2 ^ 2 + 2.2 * √(N / 2) / √|(N : ℝ) - 2 * u.val| := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  set v := u.val
  have hvN : v ≤ N := (ZMod.val_lt u).le
  set a : ℝ := |(N : ℝ) - 2 * v|
  have ha1 : 1 ≤ a := by
    obtain ⟨k, hk⟩ := hN
    have : ((N : ℤ) - 2 * v) ≠ 0 := by omega
    have h' : (1 : ℤ) ≤ |(N : ℤ) - 2 * v| := Int.one_le_abs this
    have : (a : ℝ) = ((|(N : ℤ) - 2 * v| : ℤ) : ℝ) := by simp [a]
    rw [this]; exact_mod_cast h'
  set y := ‖(1 : ℂ) + ψ u‖
  have hy : y = 2 * |cos (π * (v / N))| := norm_one_add_psi u
  have hxy : 2 * a / N ≤ y := by
    rw [hy]; have := abs_sub_le_abs_cos (N := N) hvN
    rw [mul_div_assoc]; linarith
  have hx0 : 0 < 2 * a / N := by positivity
  have hy2 : y ≤ 2 := by rw [hy]; nlinarith [abs_cos_le_one (π * (v / N))]
  have hT : 0 ≤ 2.2 * √(N / 2) / √a := by positivity
  rcases le_or_gt 1 y with h1 | h1
  · have h0 : 0 ≤ log y := Real.log_nonneg h1
    have h2 : log y ≤ log 2 := Real.log_le_log (by linarith) hy2
    have : lb u ^ 2 ≤ log 2 ^ 2 := by
      show log y ^ 2 ≤ _; exact pow_le_pow_left₀ h0 h2 2
    linarith
  · have hl : log (2 * a / N) ≤ log y := Real.log_le_log hx0 hxy
    have hly : log y < 0 := Real.log_neg (by linarith) h1
    have hsq : lb u ^ 2 ≤ log (2 * a / N) ^ 2 := by
      show log y ^ 2 ≤ _; nlinarith
    have hb := log_sq_le_inv_sqrt hx0 (by linarith)
    have he : 2.2 / √(2 * a / N) = 2.2 * √(N / 2) / √a := by
      have h2a : 0 < 2 * a := by positivity
      rw [Real.sqrt_div h2a.le, Real.sqrt_div hNpos.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have : 0 < √(2 : ℝ) := by positivity
      have : 0 < √a := Real.sqrt_pos.mpr (by linarith)
      have : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNpos
      field_simp
    have : 0 ≤ log 2 ^ 2 := sq_nonneg _
    linarith [hb, he.le, he.ge]

/-- Signed square root. -/
def ssqrt (x : ℝ) : ℝ := if 0 ≤ x then √x else -√(-x)

lemma inv_sqrt_le_sqrt_sub {x : ℝ} (hx : 1 ≤ x) : 1 / √x ≤ √(x + 1) - √(x - 1) := by
  have hs : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  set a := √(x + 1); set b := √(x - 1); set s := √x
  have ha : a ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hb : b ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = x := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  -- `a + b ≤ 2 s` since `ab ≤ x`
  have hab : a * b ≤ x := by nlinarith [sq_nonneg (a - b)]
  have hsum : a + b ≤ 2 * s := by nlinarith [sq_nonneg (a + b - 2 * s)]
  have hdiff : (a - b) * (a + b) = 2 := by nlinarith
  rw [div_le_iff₀ hs]
  have hab0 : 0 < a + b := by nlinarith
  nlinarith

lemma ssqrt_step {x : ℝ} (hx : 1 ≤ |x|) : 1 / √|x| ≤ ssqrt (x + 1) - ssqrt (x - 1) := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    simp only [ssqrt, if_pos (by linarith : (0:ℝ) ≤ x + 1), if_pos (by linarith : (0:ℝ) ≤ x - 1)]
    exact inv_sqrt_le_sqrt_sub hx
  · rw [abs_of_neg h] at hx ⊢
    have h1 : x - 1 < 0 := by linarith
    simp only [ssqrt, if_neg (not_le.mpr h1)]
    have key := inv_sqrt_le_sqrt_sub hx
    by_cases h0 : 0 ≤ x + 1
    · have : x + 1 = 0 := by linarith
      rw [if_pos h0, this, show -(x - 1) = -x + 1 by ring, show -x - 1 = 0 by linarith] at *
      simp only [Real.sqrt_zero, sub_zero] at key ⊢; linarith
    · rw [if_neg h0]
      rw [show -(x - 1) = -x + 1 by ring, show -(x + 1) = -x - 1 by ring]; linarith

/-- Telescoping: `∑_{v<N} 1/√|N − 2v| ≤ 2√(N+1)` for `N` odd. -/
lemma sum_inv_sqrt_le (hN : Odd N) :
    ∑ v ∈ range N, 1 / √|(N : ℝ) - 2 * v| ≤ 2 * √((N : ℝ) + 1) := by
  set f : ℕ → ℝ := fun v => ssqrt (2 * v - 1 - N)
  have hstep : ∀ v ∈ range N, 1 / √|(N : ℝ) - 2 * v| ≤ f (v + 1) - f v := by
    intro v _
    have hx : 1 ≤ |(2 * v - N : ℝ)| := by
      obtain ⟨k, hk⟩ := hN
      have : ((2 * v : ℤ) - N) ≠ 0 := by omega
      have h' : (1 : ℤ) ≤ |(2 * v : ℤ) - N| := Int.one_le_abs this
      have : |(2 * v - N : ℝ)| = ((|(2 * v : ℤ) - N| : ℤ) : ℝ) := by simp
      rw [this]; exact_mod_cast h'
    have := ssqrt_step hx
    simp only [f]; push_cast
    rw [abs_sub_comm] at this
    convert this using 2 <;> ring_nf
  calc ∑ v ∈ range N, 1 / √|(N : ℝ) - 2 * v| ≤ ∑ v ∈ range N, (f (v + 1) - f v) :=
        Finset.sum_le_sum hstep
    _ = f N - f 0 := Finset.sum_range_sub f N
    _ ≤ 2 * √((N : ℝ) + 1) := by
        simp only [f, ssqrt, Nat.cast_zero, mul_zero, zero_sub]
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
        rw [if_pos (by linarith), if_neg (by linarith)]
        have : √(2 * (N : ℝ) - 1 - N) ≤ √((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
        rw [show -(-1 - (N : ℝ)) = N + 1 by ring]; linarith

/-- **Uniform second moment**: `∑_u X(u)² ≤ 5N`, i.e. `E[X_j²] ≤ 5`, for `N` odd. -/
theorem sum_lb_sq_le (hN : Odd N) : ∑ u : ZMod N, lb u ^ 2 ≤ 5 * N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_neZero N)).symm⟩
  have hsum : ∑ u : ZMod (n + 1), (log 2 ^ 2 + 2.2 * √((n + 1 : ℕ) / 2) /
      √|((n + 1 : ℕ) : ℝ) - 2 * u.val|) = ∑ v ∈ range (n + 1), (log 2 ^ 2 +
      2.2 * √((n + 1 : ℕ) / 2) / √|((n + 1 : ℕ) : ℝ) - 2 * v|) :=
    Fin.sum_univ_eq_sum_range (fun v => log 2 ^ 2 + 2.2 * √((n + 1 : ℕ) / 2) /
      √|((n + 1 : ℕ) : ℝ) - 2 * v|) (n + 1)
  have h1 := Finset.sum_le_sum fun u (_ : u ∈ (Finset.univ : Finset (ZMod (n + 1)))) =>
    lb_sq_le hN u
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul] at h1
  have h2 := sum_inv_sqrt_le hN
  have h3 : ∑ v ∈ range (n + 1), 2.2 * √(((n + 1 : ℕ) : ℝ) / 2) / √|((n + 1 : ℕ) : ℝ) - 2 * v| =
      2.2 * √(((n + 1 : ℕ) : ℝ) / 2) * ∑ v ∈ range (n + 1), 1 / √|((n + 1 : ℕ) : ℝ) - 2 * v| := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [h3] at h1
  set M : ℝ := ((n + 1 : ℕ) : ℝ)
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < log 2 := Real.log_pos (by norm_num)
  have hsq : √(M / 2) * √(M + 1) ≤ M := by
    rw [← Real.sqrt_mul (by positivity)]
    have hM1 : (1 : ℝ) ≤ M := by simp only [M]; exact_mod_cast Nat.le_add_left 1 n
    calc √(M / 2 * (M + 1)) ≤ √(M ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = M := Real.sqrt_sq hNpos.le
  have hS : 0 ≤ √(M / 2) := Real.sqrt_nonneg _
  calc ∑ u : ZMod (n + 1), lb u ^ 2
      ≤ M * log 2 ^ 2 + 2.2 * √(M / 2) * ∑ v ∈ range (n + 1), 1 / √|M - 2 * v| := h1
    _ ≤ M * 0.49 + 2.2 * √(M / 2) * (2 * √(M + 1)) := by
        gcongr
        nlinarith
    _ = M * 0.49 + 4.4 * (√(M / 2) * √(M + 1)) := by ring
    _ ≤ 5 * M := by nlinarith

end ThomUpper
