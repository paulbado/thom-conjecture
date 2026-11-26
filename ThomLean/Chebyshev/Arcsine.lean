import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The arcsine probability measure on `[-4, 4]` and rescaled Chebyshev polynomials

* `arcsine = π⁻¹ · (x ↦ 4x)_* measureT`, where `measureT = (1-x²)^{-1/2} dx` on `(-1,1]`
  is Mathlib's Chebyshev measure. It is a probability measure supported on `[-4,4]`.
* `integral_arcsine_eq_cos` : `∫ g dρ = π⁻¹ ∫_0^π g(4 cos θ) dθ`.
* `cheb n E = T_n(E/4)`; exact orthogonality and normalisation
  `∫ cheb n * cheb m dρ = δ_{nm} · (1 if n = 0, 1/2 otherwise)`.
* `chebL2 : ℕ → L²(ρ)`, `1, √2 T_1(E/4), √2 T_2(E/4), …`, is orthonormal (`orthonormal_chebL2`)
  and complete (`chebBasis : HilbertBasis ℕ ℝ (L²(ρ))`), via Weierstrass approximation and
  density of bounded continuous functions in `L²`.

All results are unconditional.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set
open scoped ENNReal BoundedContinuousFunction

/-- The scaling map `x ↦ 4x`. -/
def scale4 (x : ℝ) : ℝ := 4 * x

lemma measurableEmbedding_scale4 : MeasurableEmbedding scale4 :=
  measurableEmbedding_mulLeft₀ (by norm_num : (4 : ℝ) ≠ 0)

/-- The normalised arcsine probability on `[-4,4]`, as the pushforward of the Chebyshev
measure under `x ↦ 4x`. -/
def arcsine : Measure ℝ := ENNReal.ofReal π⁻¹ • measureT.map scale4

/-- `∫ g dρ = π⁻¹ ∫ g(4x) dmeasureT`. -/
lemma integral_arcsine (g : ℝ → ℝ) : ∫ E, g E ∂arcsine = π⁻¹ * ∫ x, g (4 * x) ∂measureT := by
  rw [arcsine, integral_smul_measure, measurableEmbedding_scale4.integral_map,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  rfl

/-- `∫ g dρ = π⁻¹ ∫_0^π g(4 cos θ) dθ`. -/
theorem integral_arcsine_eq_cos (g : ℝ → ℝ) :
    ∫ E, g E ∂arcsine = π⁻¹ * ∫ θ in 0..π, g (4 * cos θ) := by
  rw [integral_arcsine, integral_measureT_eq_integral_cos]

lemma measureT_compl_Icc : measureT (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [measureT, Measure.restrict_apply' measurableSet_Ioc]
  have : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioc (-1) 1 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioc, mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩; exact h1 ⟨h2.le, h3⟩
  rw [this, measure_empty]

lemma isFiniteMeasure_measureT : IsFiniteMeasure measureT := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) measureT :=
    integrable_measureT continuousOn_const
  rcases (integrable_const_iff.mp h) with h | h
  · exact absurd h one_ne_zero
  · exact h

lemma measureT_univ : measureT univ = ENNReal.ofReal π := by
  have := isFiniteMeasure_measureT
  have h := integral_eval_T_real_measureT_zero
  simp only [T_zero, eval_one, integral_const, smul_eq_mul, mul_one] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top measureT univ)]
  exact congrArg ENNReal.ofReal h

instance : IsProbabilityMeasure arcsine := by
  constructor
  rw [arcsine, smul_apply, Measure.map_apply measurableEmbedding_scale4.measurable
    MeasurableSet.univ, preimage_univ, measureT_univ, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ Real.pi_ne_zero, ENNReal.ofReal_one]

lemma arcsine_compl_Icc : arcsine (Icc (-4 : ℝ) 4)ᶜ = 0 := by
  rw [arcsine, smul_apply, Measure.map_apply measurableEmbedding_scale4.measurable
    (measurableSet_Icc.compl)]
  have : scale4 ⁻¹' (Icc (-4 : ℝ) 4)ᶜ = (Icc (-1 : ℝ) 1)ᶜ := by
    ext x; simp only [scale4, mem_preimage, mem_compl_iff, mem_Icc]
    constructor <;> intro h h' <;> apply h <;> constructor <;> linarith [h'.1, h'.2]
  rw [this, measureT_compl_Icc, smul_zero]

lemma ae_arcsine_mem_Icc : ∀ᵐ E ∂arcsine, E ∈ Icc (-4 : ℝ) 4 := by
  rw [ae_iff]; simpa [compl_def] using arcsine_compl_Icc

/-- Continuous functions are integrable against any finite measure carried by `[-4,4]`. -/
lemma integrable_of_continuous {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Icc (-4 : ℝ) 4)ᶜ = 0) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g μ := by
  have hres : μ.restrict (Icc (-4 : ℝ) 4) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]; simpa [compl_def] using hμ
  rw [← hres]
  exact hg.continuousOn.integrableOn_compact isCompact_Icc

lemma memLp_two_of_continuous {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Icc (-4 : ℝ) 4)ᶜ = 0) {g : ℝ → ℝ} (hg : Continuous g) : MemLp g 2 μ := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  exact integrable_of_continuous hμ (hg.pow 2)

/-! ### Rescaled Chebyshev polynomials -/

/-- `cheb n E = T_n(E/4)`. -/
def cheb (n : ℕ) (E : ℝ) : ℝ := (T ℝ n).eval (E / 4)

lemma continuous_cheb (n : ℕ) : Continuous (cheb n) := by
  unfold cheb; fun_prop

lemma cheb_zero (E : ℝ) : cheb 0 E = 1 := by simp [cheb]

lemma cheb_scale (n : ℕ) (x : ℝ) : cheb n (4 * x) = (T ℝ n).eval x := by
  simp [cheb, mul_div_cancel_left₀ x (by norm_num : (4 : ℝ) ≠ 0)]

/-- Orthogonality of rescaled Chebyshev polynomials against the arcsine law. -/
theorem integral_cheb_mul_cheb_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ E, cheb n E * cheb m E ∂arcsine = 0 := by
  rw [integral_arcsine]; simp_rw [cheb_scale]
  rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne h, mul_zero]

theorem integral_cheb_zero_sq : ∫ E, cheb 0 E * cheb 0 E ∂arcsine = 1 := by
  rw [integral_arcsine]; simp_rw [cheb_scale]
  rw [show ((0 : ℕ) : ℤ) = 0 from rfl, integral_eval_T_real_mul_self_measureT_zero,
    inv_mul_cancel₀ Real.pi_ne_zero]

theorem integral_cheb_sq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ E, cheb n E * cheb n E ∂arcsine = 1 / 2 := by
  rw [integral_arcsine]; simp_rw [cheb_scale]
  rw [integral_T_real_mul_self_measureT_of_ne_zero hn]
  field_simp

/-- First Chebyshev moment of the arcsine law: `∫ cheb n dρ = [n = 0]`. -/
theorem integral_cheb (n : ℕ) : ∫ E, cheb n E ∂arcsine = if n = 0 then 1 else 0 := by
  have := integral_cheb_mul_cheb_of_ne (n := n) (m := 0)
  split_ifs with hn
  · subst hn; simp [cheb_zero]
  · simpa [cheb_zero] using this hn

/-! ### The orthonormal system in `L²(ρ)` -/

/-- Normalisation constants: `1, √2, √2, …`. -/
def normConst (n : ℕ) : ℝ := if n = 0 then 1 else √2

/-- Orthonormalised rescaled Chebyshev functions. -/
def chebFun (n : ℕ) (E : ℝ) : ℝ := normConst n * cheb n E

lemma continuous_chebFun (n : ℕ) : Continuous (chebFun n) :=
  continuous_const.mul (continuous_cheb n)

lemma memLp_chebFun (n : ℕ) : MemLp (chebFun n) 2 arcsine :=
  memLp_two_of_continuous arcsine_compl_Icc (continuous_chebFun n)

/-- The orthonormal Chebyshev system in `L²(ρ)`. -/
def chebL2 (n : ℕ) : Lp ℝ 2 arcsine := (memLp_chebFun n).toLp _

lemma inner_toLp_eq {f g : ℝ → ℝ} (hf : MemLp f 2 arcsine) (hg : MemLp g 2 arcsine) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ E, f E * g E ∂arcsine := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with E h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [mul_comm]

theorem orthonormal_chebL2 : Orthonormal ℝ chebL2 := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [chebL2, chebL2, inner_toLp_eq]
  simp only [chebFun]
  have : ∀ E, normConst i * cheb i E * (normConst j * cheb j E) =
      (normConst i * normConst j) * (cheb i E * cheb j E) := fun E => by ring
  simp_rw [this]
  rw [integral_const_mul]
  split_ifs with hij
  · subst hij
    by_cases hi : i = 0
    · subst hi; simp [normConst, integral_cheb_zero_sq]
    · rw [integral_cheb_sq_of_ne_zero hi]
      simp only [normConst, hi, ite_false]
      rw [Real.mul_self_sqrt (by norm_num)]; norm_num
  · rw [integral_cheb_mul_cheb_of_ne hij, mul_zero]

/-! ### Polynomials lie in the span of the Chebyshev polynomials -/

lemma X_mul_T_mem (n : ℕ) :
    X * T ℝ n ∈ Submodule.span ℝ (range fun k : ℕ => T ℝ k) := by
  rcases n with _ | n
  · simp only [Nat.cast_zero, T_zero, mul_one]
    exact Submodule.subset_span ⟨1, by simp [T_one]⟩
  · -- `2 X T_{n+1} = T_{n+2} + T_n`
    have h := T_add_two ℝ (n : ℤ)
    have h' : X * T ℝ ((n + 1 : ℕ) : ℤ) =
        (1 / 2 : ℝ) • (T ℝ ((n + 2 : ℕ) : ℤ) + T ℝ (n : ℤ)) := by
      push_cast
      rw [h, sub_add_cancel, mul_assoc, two_mul, ← two_smul ℝ (X * T ℝ ((n : ℤ) + 1)), smul_smul]
      norm_num
    rw [h']
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨n + 2, rfl⟩)
      (Submodule.subset_span ⟨n, rfl⟩))

lemma X_mul_mem_span {p : ℝ[X]} (hp : p ∈ Submodule.span ℝ (range fun k : ℕ => T ℝ k)) :
    X * p ∈ Submodule.span ℝ (range fun k : ℕ => T ℝ k) := by
  induction hp using Submodule.span_induction with
  | mem q hq => obtain ⟨k, rfl⟩ := hq; exact X_mul_T_mem k
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- Every real polynomial is a finite combination of Chebyshev polynomials. -/
theorem mem_span_T (p : ℝ[X]) : p ∈ Submodule.span ℝ (range fun k : ℕ => T ℝ k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
    refine Submodule.smul_mem _ a ?_
    induction n with
    | zero => exact Submodule.subset_span ⟨0, by simp⟩
    | succ n ih => rw [pow_succ', ]; exact X_mul_mem_span ih

/-! ### Completeness -/

/-- Rescaled polynomial `E ↦ p(E/4)`. -/
def polyFun (p : ℝ[X]) (E : ℝ) : ℝ := p.eval (E / 4)

lemma continuous_polyFun (p : ℝ[X]) : Continuous (polyFun p) := by unfold polyFun; fun_prop

lemma memLp_polyFun (p : ℝ[X]) : MemLp (polyFun p) 2 arcsine :=
  memLp_two_of_continuous arcsine_compl_Icc (continuous_polyFun p)

/-- The linear map `ℝ[X] → L²(ρ)`, `p ↦ [E ↦ p(E/4)]`. -/
def polyToLp : ℝ[X] →ₗ[ℝ] Lp ℝ 2 arcsine where
  toFun p := (memLp_polyFun p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    congr 1; ext E; simp [polyFun]
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1; ext E; simp [polyFun]

lemma polyToLp_T (n : ℕ) : polyToLp (T ℝ n) = (normConst n)⁻¹ • chebL2 n := by
  have hc : normConst n ≠ 0 := by unfold normConst; split_ifs <;> positivity
  rw [chebL2, ← MemLp.toLp_const_smul]
  change (memLp_polyFun _).toLp _ = _
  congr 1; ext E
  simp [polyFun, chebFun, cheb, ← mul_assoc, inv_mul_cancel₀ hc]

lemma polyToLp_mem_span (p : ℝ[X]) :
    polyToLp p ∈ Submodule.span ℝ (range chebL2) := by
  have h := mem_span_T p
  have : Submodule.map polyToLp (Submodule.span ℝ (range fun k : ℕ => T ℝ k)) ≤
      Submodule.span ℝ (range chebL2) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    rw [polyToLp_T]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact this ⟨p, h, rfl⟩

/-- Every bounded continuous function lies in the closure of the Chebyshev span. -/
lemma bcf_mem_closure (g : ℝ →ᵇ ℝ) :
    BoundedContinuousFunction.toLp (E := ℝ) 2 arcsine ℝ g ∈
      (Submodule.span ℝ (range chebL2)).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => g (4 * x))
    (by fun_prop) (ε / 2) (by positivity)
  refine ⟨polyToLp p, polyToLp_mem_span p, ?_⟩
  rw [dist_eq_norm]
  have hb := Lp.norm_le_of_ae_bound (μ := arcsine) (p := 2) (C := ε / 2) (by positivity)
    (f := BoundedContinuousFunction.toLp (E := ℝ) 2 arcsine ℝ g - polyToLp p) (by
      filter_upwards [Lp.coeFn_sub (BoundedContinuousFunction.toLp (E := ℝ) 2 arcsine ℝ g)
          (polyToLp p), BoundedContinuousFunction.coeFn_toLp (E := ℝ) (p := 2) (μ := arcsine) ℝ g,
        (memLp_polyFun p).coeFn_toLp, ae_arcsine_mem_Icc] with E h1 h2 h3 h4
      have h3' : (polyToLp p : ℝ → ℝ) E = polyFun p E := h3
      rw [h1, Pi.sub_apply, h2, h3']
      have h5 : E / 4 ∈ Icc (-1 : ℝ) 1 := by
        constructor <;> linarith [h4.1, h4.2]
      have := hp (E / 4) h5
      rw [show 4 * (E / 4) = E by ring] at this
      simp only [polyFun, Real.norm_eq_abs]
      rw [abs_sub_comm]; exact this.le)
  have h1 : measureUnivNNReal arcsine = 1 := by simp [measureUnivNNReal]
  rw [h1, NNReal.coe_one, Real.one_rpow, one_mul] at hb
  linarith

/-- **Completeness**: the closed span of the orthonormal Chebyshev system is all of `L²(ρ)`. -/
theorem chebL2_span_dense : ⊤ ≤ (Submodule.span ℝ (range chebL2)).topologicalClosure := by
  intro F _
  have hd := Lp.boundedContinuousFunction_dense (p := 2) ℝ arcsine (by norm_num)
  have hsub : (Lp.boundedContinuousFunction ℝ 2 arcsine : Set (Lp ℝ 2 arcsine)) ⊆
      (Submodule.span ℝ (range chebL2)).topologicalClosure := by
    intro f hf
    rw [SetLike.mem_coe, Lp.mem_boundedContinuousFunction_iff] at hf
    obtain ⟨g, hg⟩ := hf
    have : f = BoundedContinuousFunction.toLp (E := ℝ) 2 arcsine ℝ g := by
      apply Subtype.ext; rw [← hg]; rfl
    rw [this]; exact bcf_mem_closure g
  exact closure_minimal hsub (Submodule.isClosed_topologicalClosure _) (hd F)

/-- The Chebyshev Hilbert basis of `L²(ρ)`. -/
def chebBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 arcsine) :=
  HilbertBasis.mk orthonormal_chebL2 chebL2_span_dense

@[simp] lemma chebBasis_apply (n : ℕ) : chebBasis n = chebL2 n := by
  simp [chebBasis, HilbertBasis.coe_mk]

/-- **Parseval identity** for `L²(ρ)`: `‖F‖² = ∑ₙ ⟨chebL2 n, F⟩²`. -/
theorem parseval (F : Lp ℝ 2 arcsine) :
    HasSum (fun n => inner ℝ (chebL2 n) F ^ 2) (‖F‖ ^ 2) := by
  have := chebBasis.hasSum_inner_mul_inner F F
  simp only [chebBasis_apply] at this
  rw [real_inner_self_eq_norm_sq] at this
  convert this using 2 with n
  rw [real_inner_comm, sq]

end ThomChebyshev
