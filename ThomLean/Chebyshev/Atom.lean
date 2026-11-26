import ThomLean.Chebyshev.Weighted
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Order.Chebyshev

/-!
# The atom at `0` as a Cesàro limit of Chebyshev coefficients

* `altSum N = ∑_{j=0}^N (-1)^j T_{2j}`, with the telescoping identity
  `4 X² S_N = 1 + T_2 + (-1)^N (T_{2N} + T_{2N+2})` (`four_X_sq_mul_altSum`).
* Hence on `[-1,1]`: `|S_N(x)| ≤ N+1`, `x² |S_N(x)| ≤ 1`, and `S_N(0) = N+1`.
* `tendsto_atomMean` : for every probability measure carried by `[-4,4]`,
  `(N+1)⁻¹ ∑_{j=0}^N (-1)^j c_{2j} → μ{0}` (dominated convergence).
* `atom_eq_zero_of_energy` : if `N⁻¹ ∑_{n<N} c_n² → 0`, then `μ{0} = 0`.

All results are unconditional.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set Filter Topology

/-- `S_N = ∑_{j=0}^N (-1)^j T_{2j}`. -/
def altSum (N : ℕ) : ℝ[X] := ∑ j ∈ Finset.range (N + 1), (-1 : ℝ[X]) ^ j * T ℝ (2 * (j : ℤ))

/-- **Telescoping identity** `4 X² S_N = 1 + T_2 + (-1)^N (T_{2N} + T_{2N+2})`. -/
theorem four_X_sq_mul_altSum (N : ℕ) :
    4 * X ^ 2 * altSum N =
      1 + T ℝ 2 + (-1 : ℝ[X]) ^ N * (T ℝ (2 * (N : ℤ)) + T ℝ (2 * (N : ℤ) + 2)) := by
  induction N with
  | zero =>
    simp only [altSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
      Nat.cast_zero, mul_zero, T_zero, T_two]
    ring
  | succ N ih =>
    rw [altSum, Finset.sum_range_succ, ← altSum, mul_add, ih]
    have h := four_X_sq_mul_T (2 * ((N + 1 : ℕ) : ℤ))
    have e1 : 2 * ((N + 1 : ℕ) : ℤ) + 2 = 2 * ((N + 1 : ℕ) : ℤ) + 2 := rfl
    have e2 : 2 * ((N + 1 : ℕ) : ℤ) - 2 = 2 * (N : ℤ) := by push_cast; ring
    have e3 : 2 * (N : ℤ) + 2 = 2 * ((N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e2] at h
    rw [e3]
    linear_combination (-1 : ℝ[X]) ^ (N + 1) * h

lemma eval_altSum (N : ℕ) (x : ℝ) :
    (altSum N).eval x = ∑ j ∈ Finset.range (N + 1), (-1 : ℝ) ^ j * (T ℝ (2 * (j : ℤ))).eval x := by
  simp [altSum, eval_finsetSum]

lemma eval_T_two_mul_zero (j : ℕ) : (T ℝ (2 * (j : ℤ))).eval 0 = (-1) ^ j := by
  have h := T_real_cos (π / 2) (2 * (j : ℤ))
  rw [cos_pi_div_two] at h
  rw [h, show ((2 * (j : ℤ) : ℤ) : ℝ) * (π / 2) = (j : ℝ) * π by push_cast; ring,
    cos_nat_mul_pi]

lemma eval_altSum_zero (N : ℕ) : (altSum N).eval 0 = N + 1 := by
  rw [eval_altSum]
  simp_rw [eval_T_two_mul_zero, ← pow_add, ← two_mul, pow_mul]
  simp

lemma abs_eval_altSum_le (N : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |(altSum N).eval x| ≤ N + 1 := by
  rw [eval_altSum]
  calc |∑ j ∈ Finset.range (N + 1), (-1 : ℝ) ^ j * (T ℝ (2 * (j : ℤ))).eval x|
      ≤ ∑ j ∈ Finset.range (N + 1), |(-1 : ℝ) ^ j * (T ℝ (2 * (j : ℤ))).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (N + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact abs_eval_T_real_le_one _ hx
    _ = N + 1 := by simp

lemma sq_mul_abs_eval_altSum_le (N : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 * |(altSum N).eval x| ≤ 1 := by
  have h := congrArg (eval x) (four_X_sq_mul_altSum N)
  simp only [eval_mul, eval_pow, eval_X, eval_add, eval_one, eval_neg] at h
  have h1 := abs_eval_T_real_le_one 2 hx
  have h2 := abs_eval_T_real_le_one (2 * (N : ℤ)) hx
  have h3 := abs_eval_T_real_le_one (2 * (N : ℤ) + 2) hx
  have h4 : |(4 : ℝ[X]).eval x| = 4 := by simp
  have hpow : |(-1 : ℝ) ^ N| = 1 := by simp
  have : 4 * (x ^ 2 * |(altSum N).eval x|) ≤ 4 := by
    have hl : |(4 : ℝ[X]).eval x * x ^ 2 * (altSum N).eval x| =
        4 * (x ^ 2 * |(altSum N).eval x|) := by
      rw [abs_mul, abs_mul, h4, abs_of_nonneg (sq_nonneg x)]; ring
    rw [← hl, h]
    simp only [eval_ofNat] at *
    calc |1 + eval x (T ℝ 2) + (-1) ^ N * (eval x (T ℝ (2 * ↑N)) + eval x (T ℝ (2 * ↑N + 2)))|
        ≤ |1 + eval x (T ℝ 2)| + |(-1) ^ N * (eval x (T ℝ (2 * ↑N)) + eval x (T ℝ (2 * ↑N + 2)))| :=
          abs_add_le _ _
      _ ≤ 2 + 2 := by
          gcongr
          · exact (abs_add_le _ _).trans (by rw [abs_one]; linarith)
          · rw [abs_mul, hpow, one_mul]; exact (abs_add_le _ _).trans (by linarith)
      _ = 4 := by norm_num
  linarith

/-- The atom-detecting polynomial `p_N(E) = S_N(E/4) / (N+1)`. -/
def atomPoly (N : ℕ) (E : ℝ) : ℝ := (altSum N).eval (E / 4) / (N + 1)

lemma continuous_atomPoly (N : ℕ) : Continuous (atomPoly N) := by
  unfold atomPoly; fun_prop

lemma atomPoly_zero (N : ℕ) : atomPoly N 0 = 1 := by
  rw [atomPoly, zero_div, eval_altSum_zero]; field_simp

lemma abs_atomPoly_le (N : ℕ) {E : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4) : |atomPoly N E| ≤ 1 := by
  have hx : |E / 4| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
  rw [atomPoly, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N + 1), div_le_one (by positivity)]
  exact abs_eval_altSum_le N hx

lemma tendsto_atomPoly {E : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4) :
    Tendsto (fun N => atomPoly N E) atTop (𝓝 (({0} : Set ℝ).indicator 1 E)) := by
  by_cases h0 : E = 0
  · subst h0; simp [atomPoly_zero]
  · rw [indicator_of_notMem (by simpa using h0)]
    have hx : |E / 4| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
    have hpos : 0 < (E / 4) ^ 2 := by positivity
    have hb : ∀ N : ℕ, |atomPoly N E| ≤ ((E / 4) ^ 2)⁻¹ * (1 / ((N : ℝ) + 1)) := by
      intro N
      have := sq_mul_abs_eval_altSum_le N hx
      rw [atomPoly, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N + 1)]
      rw [div_eq_mul_one_div]
      gcongr
      rw [← one_div, le_div_iff₀ hpos]; linarith [this]
    have hlim : Tendsto (fun N : ℕ => ((E / 4) ^ 2)⁻¹ * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((E / 4) ^ 2)⁻¹
      rwa [mul_zero] at this
    exact squeeze_zero_norm hb hlim

/-- Cesàro means of the alternating even Chebyshev coefficients. -/
def atomMean (μ : Measure ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (N + 1), (-1 : ℝ) ^ j * chebCoeff μ (2 * j)) / (N + 1)

lemma integral_atomPoly (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ) :
    ∫ E, atomPoly N E ∂μ = atomMean μ N := by
  have hint : ∀ j ∈ Finset.range (N + 1),
      Integrable (fun E => (-1 : ℝ) ^ j * (T ℝ (2 * (j : ℤ))).eval (E / 4)) μ :=
    fun j _ => integrable_of_continuous hμ (by fun_prop)
  simp only [atomPoly, atomMean, eval_altSum]
  rw [integral_div, integral_finsetSum _ hint]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, chebCoeff]
  simp only [cheb]
  push_cast; rfl

/-- **Atom formula**: `μ{0} = lim_N (N+1)⁻¹ ∑_{j=0}^N (-1)^j c_{2j}`. -/
theorem tendsto_atomMean (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) :
    Tendsto (atomMean μ) atTop (𝓝 (μ {0}).toReal) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (F := atomPoly)
    (f := ({0} : Set ℝ).indicator 1) (fun _ => 1)
    (fun N => (continuous_atomPoly N).aestronglyMeasurable) (integrable_const 1)
    (fun N => (ae_mem_of_carried hμ).mono fun E hE => by
      rw [Real.norm_eq_abs]; exact abs_atomPoly_le N hE)
    ((ae_mem_of_carried hμ).mono fun E hE => tendsto_atomPoly hE)
  rw [integral_indicator_one (measurableSet_singleton 0)] at h
  simp_rw [integral_atomPoly μ hμ] at h
  exact h

theorem atom_eq_zero_iff (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) :
    μ {0} = 0 ↔ Tendsto (atomMean μ) atTop (𝓝 0) := by
  constructor
  · intro h; have := tendsto_atomMean μ hμ; rwa [h, ENNReal.toReal_zero] at this
  · intro h
    have := tendsto_nhds_unique (tendsto_atomMean μ hμ) h
    rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ _)] at this

/-- **Sufficient condition for no atom at zero**: `N⁻¹ ∑_{n<N} c_n² → 0`. -/
theorem atom_eq_zero_of_energy (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ)
    (h : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, chebCoeff μ n ^ 2) / N) atTop (𝓝 0)) :
    μ {0} = 0 := by
  set a := (μ {0}).toReal
  -- `atomMean² ≤ 2 · (2N+2)⁻¹ ∑_{n<2N+2} c_n²`
  have hbound : ∀ N : ℕ, atomMean μ N ^ 2 ≤
      2 * ((∑ n ∈ Finset.range (2 * N + 2), chebCoeff μ n ^ 2) / ((2 * N + 2 : ℕ) : ℝ)) := by
    intro N
    have hN : (0 : ℝ) < N + 1 := by positivity
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (N + 1))
      (f := fun j => (-1 : ℝ) ^ j * chebCoeff μ (2 * j))
    simp only [Finset.card_range, mul_pow, show ∀ j : ℕ, ((-1 : ℝ) ^ j) ^ 2 = 1 from
      fun j => by rw [← pow_mul, mul_comm, pow_mul]; simp, one_mul] at hcs
    have hsub : ∑ j ∈ Finset.range (N + 1), chebCoeff μ (2 * j) ^ 2 ≤
        ∑ n ∈ Finset.range (2 * N + 2), chebCoeff μ n ^ 2 := by
      have himg := Finset.sum_image (f := fun n => chebCoeff μ n ^ 2) (s := Finset.range (N + 1))
        (g := fun j => 2 * j) (fun a _ b _ hab => by simpa using hab)
      rw [← himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
      intro n hn
      simp only [Finset.mem_image, Finset.mem_range] at hn ⊢
      omega
    rw [atomMean, div_pow]
    have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * (N + 1) := by push_cast; ring
    rw [hcast, div_le_iff₀ (by positivity)]
    have : 2 * ((∑ n ∈ Finset.range (2 * N + 2), chebCoeff μ n ^ 2) / (2 * (↑N + 1))) *
        (↑N + 1) ^ 2 = (N + 1) * ∑ n ∈ Finset.range (2 * N + 2), chebCoeff μ n ^ 2 := by
      field_simp
    rw [this]
    push_cast at hcs
    nlinarith [mul_le_mul_of_nonneg_left hsub hN.le]
  have hlim : Tendsto (fun N : ℕ =>
      2 * ((∑ n ∈ Finset.range (2 * N + 2), chebCoeff μ n ^ 2) / ((2 * N + 2 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 2 * N + 2) atTop atTop := by
      refine tendsto_atTop_mono (fun N => ?_) tendsto_id; simp; omega
    simpa using (h.comp this).const_mul 2
  have hsq : Tendsto (fun N => atomMean μ N ^ 2) atTop (𝓝 (a ^ 2)) :=
    (tendsto_atomMean μ hμ).pow 2
  have ha2 : a ^ 2 ≤ 0 := le_of_tendsto_of_tendsto' hsq hlim hbound
  have ha : a = 0 := by nlinarith [sq_nonneg a]
  rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ _)] at ha

end ThomChebyshev
