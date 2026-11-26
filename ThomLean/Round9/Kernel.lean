import ThomLean.Chebyshev.Fejer
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Round 9: pointwise bounds for the Fejér kernel

`Φ_N(x) = 1 + 2∑_{n=1}^N (1 - n/(N+1)) cos nx = |∑_{k≤N} e^{ikx}|²/(N+1)` and
`K_N(4cos θ, 4cos φ) = (Φ_N(θ-φ) + Φ_N(θ+φ))/2`.

* `phi_le`: `Φ_N ≤ N+1`;
* `phi_mul_sin_sq_le`: `Φ_N(x) sin²(x/2) ≤ 1/(N+1)`;
* `phi_ge`: `Φ_N(x) ≥ (N+1)/8` if `N|x| ≤ 1`;
* `fejerKern_le`: `K_N(E,E') ≤ N+1` on `[-4,4]²`;
* `sq_mul_fejerKern_le`: `(E-E')² K_N(E,E') ≤ 64/(N+1)` on `[-4,4]²`;
* `fejerKern_ge`: `K_N(E,E') ≥ (N+1)/16` if `|E|, |E'| ≤ 1/(2(N+1))`.
-/

noncomputable section

namespace ThomRound9

open ThomChebyshev MeasureTheory Real Set Finset

/-- The Fejér kernel on the circle. -/
def phi (N : ℕ) (x : ℝ) : ℝ := 1 + 2 * ∑ n ∈ range N, fejMult N (n + 1) * cos ((n + 1) * x)

lemma phi_eq (N : ℕ) (x : ℝ) :
    phi N x = ((∑ k ∈ range (N + 1), cos (k * x)) ^ 2 +
      (∑ k ∈ range (N + 1), sin (k * x)) ^ 2) / (N + 1) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [← fejer_identity N x, eq_div_iff hN.ne', phi, add_mul, mul_assoc, Finset.sum_mul, one_mul]
  congr 2
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp only [fejMult, show n + 1 ≤ N by omega, ite_true]
  field_simp
  push_cast; ring

lemma phi_nonneg (N : ℕ) (x : ℝ) : 0 ≤ phi N x := fejerKernel_nonneg N x

lemma phi_le (N : ℕ) (x : ℝ) : phi N x ≤ N + 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [phi_eq, div_le_iff₀ hN]
  have h1 := sq_sum_le_card_mul_sum_sq (s := range (N + 1)) (f := fun k : ℕ => cos (k * x))
  have h2 := sq_sum_le_card_mul_sum_sq (s := range (N + 1)) (f := fun k : ℕ => sin (k * x))
  simp only [card_range] at h1 h2
  have h3 : ∑ k ∈ range (N + 1), (cos (k * x) ^ 2 + sin (k * x) ^ 2) = N + 1 := by
    simp [cos_sq_add_sin_sq]
  rw [Finset.sum_add_distrib] at h3
  push_cast at h1 h2
  nlinarith

lemma sum_exp_eq (N : ℕ) (x : ℝ) :
    ‖∑ k ∈ range (N + 1), Complex.exp (Complex.I * (k * x : ℝ))‖ ^ 2 =
      (∑ k ∈ range (N + 1), cos (k * x)) ^ 2 + (∑ k ∈ range (N + 1), sin (k * x)) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hre : (∑ k ∈ range (N + 1), Complex.exp (Complex.I * (k * x : ℝ))).re =
      ∑ k ∈ range (N + 1), cos (k * x) := by
    rw [Complex.re_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have him : (∑ k ∈ range (N + 1), Complex.exp (Complex.I * (k * x : ℝ))).im =
      ∑ k ∈ range (N + 1), sin (k * x) := by
    rw [Complex.im_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  rw [hre, him]; ring

lemma phi_mul_sin_sq_le (N : ℕ) (x : ℝ) : phi N x * sin (x / 2) ^ 2 ≤ 1 / (N + 1) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  set S := ∑ k ∈ range (N + 1), Complex.exp (Complex.I * (k * x : ℝ))
  have hgeom : S * (Complex.exp (Complex.I * x) - 1) =
      Complex.exp (Complex.I * ((N + 1 : ℕ) * x : ℝ)) - 1 := by
    have : ∀ k : ℕ, Complex.exp (Complex.I * (k * x : ℝ)) = Complex.exp (Complex.I * x) ^ k := by
      intro k; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    simp only [S, this]
    rw [geom_sum_mul]
  have hn := congrArg norm hgeom
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (Complex.I * ((N + 1 : ℕ) * x : ℝ)) = Complex.I * (((N + 1 : ℕ) * x : ℝ) : ℂ) by rfl,
    Complex.norm_exp_I_mul_ofReal_sub_one] at hn
  have hle : ‖S‖ * ‖2 * sin (x / 2)‖ ≤ 2 := by
    rw [hn, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := abs_sin_le_one (((N + 1 : ℕ) : ℝ) * x / 2)
    norm_num; push_cast at this ⊢; linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two] at hle
  have hS2 : ‖S‖ ^ 2 * sin (x / 2) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ ‖S‖ * |sin (x / 2)| := by positivity
    have : ‖S‖ * |sin (x / 2)| ≤ 1 := by linarith
    calc ‖S‖ ^ 2 * sin (x / 2) ^ 2 = (‖S‖ * |sin (x / 2)|) ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ 1 := by nlinarith
  rw [phi_eq, ← sum_exp_eq, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN]
  exact hS2

lemma cos_one_ge : (2 : ℝ) / 5 ≤ cos 1 := by
  have h := Real.cos_bound (x := 1) (by norm_num)
  have : |cos 1 - (1 - 1 ^ 2 / 2)| ≤ |(1 : ℝ)| ^ 4 * (5 / 96) := h
  rw [abs_le] at this; norm_num at this; linarith [this.1]

lemma phi_ge (N : ℕ) {x : ℝ} (hx : N * |x| ≤ 1) : ((N : ℝ) + 1) / 8 ≤ phi N x := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hc : (N + 1 : ℝ) * (2 / 5) ≤ ∑ k ∈ range (N + 1), cos (k * x) := by
    have : ∀ k ∈ range (N + 1), (2 : ℝ) / 5 ≤ cos (k * x) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp hk
      have : |(k : ℝ) * x| ≤ 1 := by
        rw [abs_mul, Nat.abs_cast]
        exact le_trans (mul_le_mul_of_nonneg_right hk' (abs_nonneg x)) hx
      calc (2 : ℝ) / 5 ≤ cos 1 := cos_one_ge
        _ ≤ cos |(k : ℝ) * x| := by
            apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
              this
        _ = cos (k * x) := Real.cos_abs _
    have := Finset.sum_le_sum this
    simp only [Finset.sum_const, card_range, nsmul_eq_mul] at this
    push_cast at this; linarith
  rw [phi_eq, le_div_iff₀ hN]
  have h0 : 0 ≤ (N + 1 : ℝ) * (2 / 5) := by positivity
  nlinarith [sq_nonneg (∑ k ∈ range (N + 1), sin (k * x))]

/-- Angle form of the two-variable kernel. -/
lemma fejerKern_cos (N : ℕ) (θ φ : ℝ) :
    fejerKern N (4 * cos θ) (4 * cos φ) = (phi N (θ - φ) + phi N (θ + φ)) / 2 := by
  have key : ∑ n ∈ Finset.range N, fejMult N (n + 1) * (cos (((n + 1 : ℕ) : ℝ) * θ) *
      cos (((n + 1 : ℕ) : ℝ) * φ)) =
        (∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ - φ)) +
          ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ + φ))) / 2 := by
    rw [eq_div_iff two_ne_zero, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_sub, mul_add, cos_sub, cos_add]; push_cast; ring
  rw [fejerKern]
  simp_rw [cheb_four_cos]
  rw [key, phi, phi]
  ring

lemma angle_of_mem {E : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4) : E = 4 * cos (arccos (E / 4)) := by
  rw [cos_arccos (by linarith [hE.1]) (by linarith [hE.2])]; ring

theorem fejerKern_le (N : ℕ) {E E' : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4) (hE' : E' ∈ Icc (-4 : ℝ) 4) :
    fejerKern N E E' ≤ N + 1 := by
  rw [angle_of_mem hE, angle_of_mem hE', fejerKern_cos]
  have := phi_le N (arccos (E / 4) - arccos (E' / 4))
  have := phi_le N (arccos (E / 4) + arccos (E' / 4))
  linarith

theorem sq_mul_fejerKern_le (N : ℕ) {E E' : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4)
    (hE' : E' ∈ Icc (-4 : ℝ) 4) : (E - E') ^ 2 * fejerKern N E E' ≤ 64 / (N + 1) := by
  set θ := arccos (E / 4); set φ := arccos (E' / 4)
  have hEE : (E - E') ^ 2 = 64 * sin ((θ + φ) / 2) ^ 2 * sin ((θ - φ) / 2) ^ 2 := by
    rw [angle_of_mem hE, angle_of_mem hE']
    rw [show 4 * cos θ - 4 * cos φ = 4 * (cos θ - cos φ) by ring, cos_sub_cos]; ring
  rw [hEE, angle_of_mem hE, angle_of_mem hE', fejerKern_cos]
  have s1 := sin_sq_le_one ((θ + φ) / 2)
  have s2 := sin_sq_le_one ((θ - φ) / 2)
  have p1 := phi_mul_sin_sq_le N (θ - φ)
  have p2 := phi_mul_sin_sq_le N (θ + φ)
  have q1 := phi_nonneg N (θ - φ)
  have q2 := phi_nonneg N (θ + φ)
  have hN : (0 : ℝ) < N + 1 := by positivity
  have a1 : 64 * sin ((θ + φ) / 2) ^ 2 * sin ((θ - φ) / 2) ^ 2 * phi N (θ - φ) ≤ 64 / (N + 1) := by
    have : sin ((θ + φ) / 2) ^ 2 * (phi N (θ - φ) * sin ((θ - φ) / 2) ^ 2) ≤ 1 * (1 / (N + 1)) :=
      mul_le_mul s1 p1 (by positivity) zero_le_one
    calc _ = 64 * (sin ((θ + φ) / 2) ^ 2 * (phi N (θ - φ) * sin ((θ - φ) / 2) ^ 2)) := by ring
      _ ≤ 64 * (1 * (1 / (N + 1))) := by linarith
      _ = 64 / (N + 1) := by ring
  have a2 : 64 * sin ((θ + φ) / 2) ^ 2 * sin ((θ - φ) / 2) ^ 2 * phi N (θ + φ) ≤ 64 / (N + 1) := by
    have : sin ((θ - φ) / 2) ^ 2 * (phi N (θ + φ) * sin ((θ + φ) / 2) ^ 2) ≤ 1 * (1 / (N + 1)) :=
      mul_le_mul s2 p2 (by positivity) zero_le_one
    calc _ = 64 * (sin ((θ - φ) / 2) ^ 2 * (phi N (θ + φ) * sin ((θ + φ) / 2) ^ 2)) := by ring
      _ ≤ 64 * (1 * (1 / (N + 1))) := by linarith
      _ = 64 / (N + 1) := by ring
  rw [mul_div_assoc', mul_add, add_div]
  linarith

lemma arccos_mem_of_small {a : ℝ} (ha : |a| ≤ 1 / 2) : arccos a ∈ Icc (π / 3) (2 * π / 3) := by
  have h3 : arccos (1 / 2) = π / 3 := by
    rw [← Real.cos_pi_div_three, arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  have hneg : arccos (-(1 / 2)) = 2 * π / 3 := by rw [arccos_neg, h3]; ring
  rw [abs_le] at ha
  exact ⟨h3 ▸ arccos_le_arccos ha.2, hneg ▸ arccos_le_arccos ha.1⟩

lemma two_thirds_le_sin {y : ℝ} (hy : y ∈ Icc (π / 3) (2 * π / 3)) : (2 : ℝ) / 3 ≤ sin y := by
  have hpi := Real.pi_pos
  rcases le_total y (π / 2) with h | h
  · have := mul_le_sin (by linarith [hy.1]) h
    have : 2 / π * (π / 3) ≤ 2 / π * y := mul_le_mul_of_nonneg_left hy.1 (by positivity)
    have e : 2 / π * (π / 3) = 2 / 3 := by field_simp
    linarith
  · have hs : sin y = sin (π - y) := (sin_pi_sub y).symm
    have := mul_le_sin (x := π - y) (by linarith [hy.2]) (by linarith)
    have : 2 / π * (π / 3) ≤ 2 / π * (π - y) := mul_le_mul_of_nonneg_left (by linarith [hy.2])
      (by positivity)
    have e : 2 / π * (π / 3) = 2 / 3 := by field_simp
    linarith

/-- **Near-diagonal lower bound**: `K_N(E,E') ≥ (N+1)/16` when `|E|, |E'| ≤ 1/(2(N+1))`. -/
theorem fejerKern_ge (N : ℕ) {E E' : ℝ} (hE : |E| ≤ 1 / (2 * (N + 1)))
    (hE' : |E'| ≤ 1 / (2 * (N + 1))) : ((N : ℝ) + 1) / 16 ≤ fejerKern N E E' := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hsmall : 1 / (2 * ((N : ℝ) + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hE4 : E ∈ Icc (-4 : ℝ) 4 := by rw [abs_le] at hE; constructor <;> linarith
  have hE4' : E' ∈ Icc (-4 : ℝ) 4 := by rw [abs_le] at hE'; constructor <;> linarith
  set θ := arccos (E / 4); set φ := arccos (E' / 4)
  have hθ := arccos_mem_of_small (a := E / 4) (by rw [abs_div]; norm_num; linarith)
  have hφ := arccos_mem_of_small (a := E' / 4) (by rw [abs_div]; norm_num; linarith)
  have hpi := Real.pi_pos
  have hsum := two_thirds_le_sin (y := (θ + φ) / 2)
    ⟨by linarith [hθ.1, hφ.1], by linarith [hθ.2, hφ.2]⟩
  have hθφ : |(θ - φ) / 2| ≤ π / 2 := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  have hd := mul_abs_le_abs_sin hθφ
  have hd' : 2 / π * |(θ - φ) / 2| = |θ - φ| / π := by
    rw [abs_div, abs_two]; field_simp
  have hEE : |E - E'| = 8 * sin ((θ + φ) / 2) * |sin ((θ - φ) / 2)| := by
    have h1 : E - E' = 4 * cos θ - 4 * cos φ := by
      rw [← angle_of_mem hE4, ← angle_of_mem hE4']
    rw [h1, show 4 * cos θ - 4 * cos φ = 4 * (cos θ - cos φ) by ring, cos_sub_cos, abs_mul,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_nonneg (by linarith :
        (0:ℝ) ≤ sin ((θ + φ) / 2))]
    norm_num; ring
  have hEE' : |E - E'| ≤ 1 / (N + 1) := by
    have := abs_sub E E'
    have e : 1 / (2 * ((N : ℝ) + 1)) + 1 / (2 * (N + 1)) = 1 / (N + 1) := by field_simp; ring
    linarith
  have hang : |θ - φ| ≤ 3 * π / (16 * (N + 1)) := by
    have : 8 * (2 / 3) * (|θ - φ| / π) ≤ 1 / (N + 1) := by
      calc 8 * (2 / 3) * (|θ - φ| / π) ≤ 8 * sin ((θ + φ) / 2) * |sin ((θ - φ) / 2)| := by
            apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
        _ ≤ 1 / (N + 1) := by rw [← hEE]; exact hEE'
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hN] at this
    field_simp at this
    nlinarith [abs_nonneg (θ - φ)]
  have hNx : (N : ℝ) * |θ - φ| ≤ 1 := by
    have h4 := Real.pi_le_four
    calc (N : ℝ) * |θ - φ| ≤ (N + 1) * (3 * π / (16 * (N + 1))) :=
          mul_le_mul (by linarith) hang (abs_nonneg _) hN.le
      _ = 3 * π / 16 := by field_simp
      _ ≤ 1 := by linarith
  rw [angle_of_mem hE4, angle_of_mem hE4', fejerKern_cos]
  have := phi_ge N hNx
  have := phi_nonneg N (θ + φ)
  linarith

end ThomRound9
