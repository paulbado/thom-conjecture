import ThomLean.ZeroLevel.Family
import ThomLean.LowerBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `LogSqLowerBound`, unconditionally

`logSqLowerBound : LogSqLowerBound`: for `0 < h < 1/3`,

`μ_A([-h, h]) ≥ c / log² h`, `c = 1/165888000`.

Proof.
1. Fix `h` and `m = ⌈5 + 3 log(1/h)⌉`, so that `16 (4/9)^m < h²` (`eps_lt`).
2. For odd `N`, the quasimode family of `ThomZeroLevel.Family` gives
   `σ_N([-h,h]) ≥ #P · ⌊N/D⌋ · #T / N³` (`nuQ_lower`), where `σ_N` is the vertex spectral
   measure of `H₃(ℤ/N)`. This is the Riemann sum over the fluxes `p/N` near `1/2 + δ`,
   `δ ≍ 1/m`, of the per-flux counts `≍ δ`.
3. The explicit window counts give `σ_N([-h,h]) ≥ 1/(2048000 m²)` for all large odd `N`
   (`nuQ_lower_explicit`).
4. `σ_N` has exactly the moments of `μ_A` up to degree `≈ √N` (`nuQ_moments`), so the
   compact-set transfer `le_measureReal_of_moments` passes the bound to `μ_A`.

Consequences (`not_principalTarget`, `not_lqTarget`, `not_fejerTarget`): the unweighted
`L²` target, every `L^q` duality target (`q ≥ 1`) and every Fejér `L^p` target (`p > 1`) are
**false**. The weighted targets and absolute continuity are not affected.
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence ThomNoAtoms ThomConclusions ThomFejer
open ThomLowerBound MeasureTheory Polynomial Filter Set Real
open Finset hiding Icc

/-- The vertex spectral measure of `H₃(ℤ/(n+1))`, on `ℝ`. -/
def nuQ (n : ℕ) : Measure ℝ := (quotMeasure n : Measure S4).map Subtype.val

instance (n : ℕ) : IsProbabilityMeasure (nuQ n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance

lemma nuQ_carried (n : ℕ) : CarriedBy4 (nuQ n) := by
  unfold CarriedBy4 nuQ
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
  have : (Subtype.val ⁻¹' (Icc (-4 : ℝ) 4)ᶜ : Set S4) = ∅ := by ext E; simp
  rw [this, measure_empty]

/-- **Exact moment matching**: `∫ P dσ_N = ∫ P dμ_A` once `N > (deg P + 1)²`. -/
lemma nuQ_moments (P : ℝ[X]) :
    ∀ᶠ n in atTop, ∫ E, polyFun P E ∂nuQ n = ∫ E, polyFun P E ∂muA := by
  have := isSpectralMeasureA_muA.isProb
  refine eventually_atTop.2 ⟨(P.natDegree + 1) ^ 2, fun n hn => ?_⟩
  show polyIntegral (nuQ n) (nuQ_carried n) P = polyIntegral muA isSpectralMeasureA_muA.carried P
  rw [linear_eq_sum, linear_eq_sum]
  unfold Polynomial.sum
  refine Finset.sum_congr rfl fun k hk => ?_
  dsimp only
  congr 1
  have hk' : k ≤ P.natDegree := le_natDegree_of_mem_supp k hk
  have hk2 : (k + 1) ^ 2 ≤ n + 1 := by
    have : (k + 1) ^ 2 ≤ (P.natDegree + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  show ∫ E, polyFun (X ^ k) E ∂nuQ n = ∫ E, polyFun (X ^ k) E ∂muA
  simp only [polyFun, eval_pow, eval_X, div_pow]
  rw [integral_div, integral_div, isSpectralMeasureA_muA.moments k, nuQ,
    integral_map measurable_subtype_coe.aemeasurable (by fun_prop),
    integral_pow_quotMeasure n k hk2]

/-- **Riemann-sum lower bound** at a fixed odd `N = n+1`. -/
theorem nuQ_lower (n : ℕ) (hN : Odd (n + 1)) {h : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 4 ≤ m)
    (hε : 16 * (4 / 9 : ℝ) ^ m < h ^ 2) :
    (#(Pwin (n + 1) m) * ((n + 1) / bandD m : ℕ) * #(Twin (n + 1)) : ℝ) / ((n : ℝ) + 1) ^ 3 ≤
      (nuQ n).real (Icc (-h) h) := by
  have hc := card_good_le (N := n + 1) hN hh hm hε
  rw [card_good] at hc
  have hq := quotMeasure_real_Icc n h
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 := by positivity
  rw [div_le_iff₀ hpos, nuQ, hq]
  exact_mod_cast hc

lemma bandD_le (m : ℕ) (hm : 1 ≤ m) : (bandD m : ℝ) ≤ 25 * m := by
  have : bandD m ≤ 25 * m := by unfold bandD; omega
  exact_mod_cast this

/-- **Explicit lower bound** for all large odd `N`. -/
theorem nuQ_lower_explicit (n : ℕ) (hN : Odd (n + 1)) {h : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 4 ≤ m)
    (hε : 16 * (4 / 9 : ℝ) ^ m < h ^ 2) (hn : 1280 * m + 2 * bandD m + 32 ≤ n + 1) :
    1 / (2048000 * (m : ℝ) ^ 2) ≤ (nuQ n).real (Icc (-h) h) := by
  refine le_trans ?_ (nuQ_lower n hN hh hm hε)
  set N : ℝ := (n : ℝ) + 1
  set D : ℝ := (bandD m : ℝ)
  have hm0 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hD0 : (0 : ℝ) < D := by simp only [D, bandD]; positivity
  have hD := bandD_le m (by omega)
  have hnR : (1280 * m + 2 * bandD m + 32 : ℝ) ≤ N := by
    simp only [N]; exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by positivity
  -- the three window counts
  have hP : N * (1 / (640 * m)) - 1 ≤ #(Pwin (n + 1) m) := by
    have := card_window (n + 1) (α := 1 / 2 + 9 / (640 * m)) (β := 1 / 2 + 1 / (64 * m))
      (by positivity) (by
        have : 9 / (640 * (m : ℝ)) ≤ 1 / (64 * m) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        linarith) (by
        have : 1 / (64 * (m : ℝ)) < 1 / 2 := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
        linarith)
    have e : (1 / 2 + 1 / (64 * (m : ℝ))) - (1 / 2 + 9 / (640 * m)) = 1 / (640 * m) := by
      field_simp; ring
    rw [e] at this
    simpa [Pwin, N] using this
  have hT : N * (1 / 16) - 1 ≤ #(Twin (n + 1)) := by
    have := card_window (n + 1) (α := 1 / 16) (β := 1 / 8) (by norm_num) (by norm_num)
      (by norm_num)
    norm_num at this ⊢
    simpa [Twin, N] using this
  have hK : N / D - 1 ≤ ((n + 1) / bandD m : ℕ) := by
    have h1 := Nat.lt_div_mul_add (a := n + 1) (b := bandD m) (by unfold bandD; omega)
    have h2 : N < (((n + 1) / bandD m : ℕ) : ℝ) * D + D := by
      simp only [N, D]; exact_mod_cast h1
    rw [div_sub_one hD0.ne', div_le_iff₀ hD0]
    linarith
  -- each is at least half its main term
  have hP' : N / (1280 * m) ≤ #(Pwin (n + 1) m) := by
    have : N / (1280 * m) ≤ N * (1 / (640 * m)) - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : N * (1 / (640 * (m : ℝ))) * (1280 * m) = 2 * N := by field_simp; ring
      nlinarith
    linarith
  have hT' : N / 32 ≤ #(Twin (n + 1)) := by nlinarith
  have hK' : N / (2 * D) ≤ ((n + 1) / bandD m : ℕ) := by
    have e : N / D = 2 * (N / (2 * D)) := by field_simp
    have : 1 ≤ N / (2 * D) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hprod : N / (1280 * m) * (N / (2 * D)) * (N / 32) ≤
      (#(Pwin (n + 1) m) * ((n + 1) / bandD m : ℕ) * #(Twin (n + 1)) : ℝ) := by
    gcongr
  calc 1 / (2048000 * (m : ℝ) ^ 2) ≤ 1 / (81920 * m * D) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    _ = N / (1280 * m) * (N / (2 * D)) * (N / 32) / N ^ 3 := by field_simp; ring
    _ ≤ _ := by gcongr

/-- `16 (4/9)^m < h²` for `m ≥ 5 + 3 log(1/h)`. -/
lemma eps_lt {h : ℝ} (hh : 0 < h) (hh1 : h < 1) {m : ℕ} (hm : 5 + 3 * (-log h) ≤ m) :
    16 * (4 / 9 : ℝ) ^ m < h ^ 2 := by
  have hl2 := log_two_gt_d9
  have hL : 0 ≤ -log h := by have := log_neg hh hh1; linarith
  have h1 : (4 / 9 : ℝ) ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have h2 : 16 < h ^ 2 * 2 ^ m := by
    have e1 : h ^ 2 = exp (2 * log h) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, exp_nat_mul, exp_log hh]
    have e2 : (2 : ℝ) ^ m = exp (m * log 2) := by rw [exp_nat_mul, exp_log (by norm_num)]
    have e3 : (16 : ℝ) = exp (4 * log 2) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, exp_nat_mul, exp_log (by norm_num)]; norm_num
    rw [e1, e2, e3, ← exp_add]
    apply exp_lt_exp.mpr
    have : (5 + 3 * (-log h)) * log 2 ≤ m * log 2 :=
      mul_le_mul_of_nonneg_right hm (by linarith)
    nlinarith
  have h3 : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0 : ℝ) < 2 ^ m := by positivity
  have : 16 * (1 / 2 : ℝ) ^ m < h ^ 2 := by
    have : 16 * (1 / 2 : ℝ) ^ m * 2 ^ m < h ^ 2 * 2 ^ m := by
      rw [mul_assoc, h3, mul_one]; exact h2
    exact lt_of_mul_lt_mul_right this h4.le
  linarith

lemma one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  have := exp_one_lt_d9
  linarith

/-- **The logarithmic lower bound** `μ_A([-h,h]) ≥ c / log² h`, unconditionally. -/
theorem logSqLowerBound : LogSqLowerBound := by
  refine logSqLowerBound_of_approx nuQ nuQ_carried nuQ_moments
    ⟨1 / 165888000, by norm_num, 1 / 3, by norm_num, fun h hh hh3 => ?_⟩
  set L := -log h with hLdef
  have hL1 : 1 < L := by
    have : log h < log (1 / 3) := log_lt_log hh hh3
    rw [one_div, log_inv] at this
    linarith [one_lt_log_three]
  set m := ⌈5 + 3 * L⌉₊ with hmdef
  have hm1 : 5 + 3 * L ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < 5 + 3 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hm4 : 4 ≤ m := by
    have : (4 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hε := eps_lt hh (by linarith) hm1
  rw [Filter.frequently_atTop]
  intro n₀
  refine ⟨2 * (n₀ + 1280 * m + 2 * bandD m + 32), by omega, ?_⟩
  have hb := nuQ_lower_explicit (2 * (n₀ + 1280 * m + 2 * bandD m + 32)) ⟨_, rfl⟩ hh.le hm4 hε
    (by omega)
  refine le_trans ?_ hb
  have hlog : log h ^ 2 = L ^ 2 := by rw [hLdef, neg_sq]
  rw [hlog, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (m : ℝ) ≤ 9 * L := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith


/-! ### Task 2 in closed form -/

/-- **Explicit zero-energy quasimode, exponential form** (round-6 Task 2). With
`m = ⌊1/(64δ)⌋`, `M = ⌊5/(32δ)⌋`, `θ ∈ [1/16, 1/8]` and `0 < δ ≤ 2⁻¹⁰`:
`‖H ξ‖² ≤ (1/4) exp(-2b/δ) ‖ξ‖²` with `b = 1/400`, i.e. `‖H ξ‖ ≤ (1/2) e^{-b/δ} ‖ξ‖`. -/
theorem qm_exp_bound {N : ℕ} [NeZero N] (p t : ZMod N) (s : ℕ)
    (hθ1 : 1 / 16 ≤ theta p t s) (hθ2 : theta p t s ≤ 1 / 8)
    (hδ0 : 0 < dlt N p) (hδ1 : dlt N p ≤ 1 / 1024)
    (hsM : s + 2 * ⌊5 / (32 * dlt N p)⌋₊ < N) :
    nrm (chainH p t (qmXi p t s ⌊5 / (32 * dlt N p)⌋₊)) ≤
      1 / 4 * exp (-(2 * (1 / 400)) / dlt N p) * nrm (qmXi p t s ⌊5 / (32 * dlt N p)⌋₊) := by
  set δ := dlt N p
  set m := ⌊1 / (64 * δ)⌋₊
  set M := ⌊5 / (32 * δ)⌋₊
  have hm1 : (m : ℝ) ≤ 1 / (64 * δ) := Nat.floor_le (by positivity)
  have hm2 : 1 / (64 * δ) < m + 1 := Nat.lt_floor_add_one _
  have hM1 : (M : ℝ) ≤ 5 / (32 * δ) := Nat.floor_le (by positivity)
  have hM2 : 5 / (32 * δ) < M + 1 := Nat.lt_floor_add_one _
  have e1 : (m : ℝ) * δ ≤ 1 / 64 := by rw [le_div_iff₀ (by positivity)] at hm1; linarith
  have e2 : (M : ℝ) * δ ≤ 5 / 32 := by rw [le_div_iff₀ (by positivity)] at hM1; linarith
  have e3 : 5 / 32 < ((M : ℝ) + 1) * δ := by rw [div_lt_iff₀ (by positivity)] at hM2; linarith
  have hq := (qm_of_phase p t (m := m) hsM hθ1 hθ2 hδ0 (by linarith) (by nlinarith) (by nlinarith)
    (by nlinarith)).1
  refine hq.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  -- `16 (4/9)^m ≤ 16 (1/2)^m = 16 exp(-m log 2) ≤ (1/4) exp(-2b/δ)`
  have hl2 := log_two_gt_d9
  have hl2' : log 2 < 0.6931471808 := log_two_lt_d9
  have h1 : (4 / 9 : ℝ) ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have h2 : (1 / 2 : ℝ) ^ m = exp (-(m * log 2)) := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num), one_div, inv_pow]
  have h16 : (16 : ℝ) = exp (4 * log 2) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, exp_nat_mul, exp_log (by norm_num)]; norm_num
  have h4 : (1 / 4 : ℝ) = exp (-(2 * log 2)) := by
    rw [exp_neg, two_mul, exp_add, exp_log (by norm_num)]
    norm_num
  have hkey : 4 * log 2 + -(m * log 2) ≤ -(2 * log 2) + -(2 * (1 / 400)) / δ := by
    -- `m > 1/(64δ) - 1` and `1/δ ≥ 1024`
    have hinv : 1024 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have hm3 : 1 / δ / 64 - 1 < m := by
      have : 1 / (64 * δ) = 1 / δ / 64 := by field_simp
      linarith
    have : (1 / δ / 64 - 1) * log 2 ≤ m * log 2 :=
      mul_le_mul_of_nonneg_right hm3.le (by linarith)
    have hd : -(2 * (1 / 400)) / δ = -(1 / 200) * (1 / δ) := by field_simp; norm_num
    rw [hd]
    nlinarith
  calc 16 * (4 / 9 : ℝ) ^ m ≤ 16 * (1 / 2) ^ m := by gcongr
    _ = exp (4 * log 2 + -(m * log 2)) := by rw [h2, h16, exp_add]
    _ ≤ exp (-(2 * log 2) + -(2 * (1 / 400)) / δ) := exp_le_exp.mpr hkey
    _ = 1 / 4 * exp (-(2 * (1 / 400)) / δ) := by rw [exp_add, ← h4]

/-! ### Unconditional refutations -/

/-- The unweighted `L²` target is **false**. -/
theorem not_principalTarget : ¬ PrincipalTarget := not_principalTarget_of_logSq logSqLowerBound

/-- Every `L^q` duality target, `q ≥ 1`, is **false**. -/
theorem not_lqTarget {q : ℝ} (hq : 1 ≤ q) : ¬ LqTarget q := not_lqTarget_of_logSq logSqLowerBound hq

/-- Every Fejér `L^p` target, `p > 1`, is **false**. -/
theorem not_fejerTarget {p : ℝ} (hp : 1 < p) : ¬ FejerTarget p :=
  not_fejerTarget_of_logSq logSqLowerBound hp

end ThomZeroLevel
