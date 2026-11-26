import ThomLean.NoAtoms
import ThomLean.Chebyshev.Fejer

/-!
# The Fejér `L^p` targets for `μ_A`

`F_N^A(θ) = 1 + 2 ∑_{n=1}^N (1 - n/(N+1)) τ(T_n(A/4)) cos nθ` (`fejer_muA_cos`) is an explicit
trigonometric polynomial whose coefficients are finite combinations of zero-area walk counts.

* `FejerTarget p : Prop` : `sup_N (1/π) ∫_0^π |F_N^A(θ)|^p dθ < ∞`, written on `[-4,4]` as
  `sup_N ∫ |F_N^A|^p dρ < ∞` (`integral_fejer_muA_eq_cos` gives the angle form).
* `muA_ac_of_fejerTarget` : `FejerTarget p` with `1 < p` ⇒ `μ_A ≪ Lebesgue`.
* `lqTarget_of_fejerTarget` : `FejerTarget p` ⇒ `LqTarget p'` (`p' = p/(p-1)`), in particular
  `FejerTarget (3/2) ⇒ LqTarget 3` (`lqTarget_three_of_fejerTarget`).
* `lqTarget_of_Lp_density` : an `L^p(ρ)` density of `μ_A` ⇒ `LqTarget p'`.

All targets are propositions; none is assumed.
-/

noncomputable section

namespace ThomFejer

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence ThomConclusions MeasureTheory
open Polynomial Real Set Filter Topology

/-- The Fejér densities of `μ_A`. -/
def fejerA (N : ℕ) (E : ℝ) : ℝ := fejer muA N E

/-- **Explicit form**: the coefficients are the walk-count traces `τ(T_n(A/4))`. -/
theorem fejer_muA_cos (N : ℕ) (θ : ℝ) :
    fejerA N (4 * cos θ) =
      1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * chebTrace (n + 1) * cos ((n + 1) * θ) := by
  rw [fejerA, fejer_cos]
  simp_rw [chebCoeff_eq_chebTrace isSpectralMeasureA_muA]

/-- Angle form of the `L^p` norm: `∫ |F_N|^p dρ = π⁻¹ ∫_0^π |F_N(4cos θ)|^p dθ`. -/
theorem integral_fejer_muA_eq_cos (N : ℕ) (p : ℝ) :
    ∫ E, |fejerA N E| ^ p ∂arcsine = π⁻¹ * ∫ θ in 0..π, |fejerA N (4 * cos θ)| ^ p :=
  integral_arcsine_eq_cos _

/-- `∫ F_N^A dρ = 1`. -/
theorem integral_fejerA (N : ℕ) : ∫ E, fejerA N E ∂arcsine = 1 := by
  have := isSpectralMeasureA_muA.isProb
  exact integral_fejer muA N

/-- **Fejér target** (a proposition): `sup_N ∫ |F_N^A|^p dρ < ∞`. -/
def FejerTarget (p : ℝ) : Prop := ∃ M : ℝ, ∀ N, ∫ E, |fejerA N E| ^ p ∂arcsine ≤ M

/-- **Fejér criterion for `μ_A`.** -/
theorem muA_ac_of_fejerTarget {p : ℝ} (hp : 1 < p) (h : FejerTarget p) : muA ≪ volume := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨M, hM⟩ := h
  exact ac_of_fejer_bounded muA isSpectralMeasureA_muA.carried hp M hM

/-- `FejerTarget p ⇒ LqTarget q` for Hölder conjugate `p, q`. -/
theorem lqTarget_of_fejerTarget {p q : ℝ} (hpq : p.HolderConjugate q) (h : FejerTarget p) :
    LqTarget q := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨M, hM⟩ := h
  have hp0 : 0 < p := hpq.pos
  refine ⟨M ^ (1 / p), fun P => ?_⟩
  rw [← integral_polyFun_muA]
  exact lq_bound_of_fejer muA isSpectralMeasureA_muA.carried hpq _ (fun N =>
    Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) (hM N) (by positivity)) P

lemma holderConjugate_three_halves : (3 / 2 : ℝ).HolderConjugate 3 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

/-- The `L^{3/2}` Fejér target gives the `L³` duality target. -/
theorem lqTarget_three_of_fejerTarget (h : FejerTarget (3 / 2)) : LqTarget 3 :=
  lqTarget_of_fejerTarget holderConjugate_three_halves h

/-- An `L^p(ρ)` density of `μ_A` gives `LqTarget q`. -/
theorem lqTarget_of_Lp_density {p q : ℝ} (hpq : p.HolderConjugate q) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ E, 0 ≤ f E) (hfp : MemLp f (ENNReal.ofReal p) arcsine)
    (hμf : muA = arcsine.withDensity fun E => ENNReal.ofReal (f E)) : LqTarget q := by
  refine ⟨(∫ E, f E ^ p ∂arcsine) ^ (1 / p), fun P => ?_⟩
  rw [← integral_polyFun_muA]
  exact lq_bound_of_Lp_density muA hpq hfm hf0 hfp hμf P

/-! ### The weighted `L^q` target

The numerics of round 4 (`numerics/README.md`) show a concentration
`μ_A([-h,h]) ≈ c / log²(1/h)` at `E = 0`, coming from the zero Landau level near flux `1/2`; it
is incompatible with every `L^p` density, `p > 1`. The weight `E²/16` removes it. Combined with
the unconditional absence of atoms, a weighted `L^q` bound is enough for absolute continuity. -/

/-- **Weighted `L^q` duality target** (a proposition):
`|τ((A/4)² P(A/4))| ≤ K ‖P(·/4)‖_{L^q(ρ)}` for all polynomials `P`. -/
def WeightedLqTarget (q : ℝ) : Prop :=
  ∃ K : ℝ, ∀ P : ℝ[X], |tauPoly (X ^ 2 * P)| ≤ K * (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q)

lemma integral_polyFun_weighted_muA (P : ℝ[X]) :
    ∫ E, polyFun P E ∂weighted muA = tauPoly (X ^ 2 * P) := by
  rw [integral_weighted, ← integral_polyFun_muA]
  congr 1; ext E; simp only [polyFun, wt, eval_mul, eval_pow, eval_X]; ring

/-- **Weighted `L^q` target ⇒ `μ_A ≪ Lebesgue`** (uses `muA_no_atoms`). -/
theorem muA_ac_of_weightedLqTarget {q : ℝ} (hq : 1 ≤ q) (h : WeightedLqTarget q) :
    muA ≪ volume := by
  have := isSpectralMeasureA_muA.isProb
  have hc := isSpectralMeasureA_muA.carried
  have := isFiniteMeasure_weighted muA hc
  obtain ⟨K, hK⟩ := h
  have hν : weighted muA ≪ volume :=
    ac_of_poly_Lq_bound (weighted muA) (carried_weighted hc) hq (K := K) fun P => by
      rw [integral_polyFun_weighted_muA]; exact hK P
  have hoff : muA.restrict {0}ᶜ ≪ volume := (restrict_compl_zero_ac_weighted muA).trans hν
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  rw [← Measure.restrict_add_restrict_compl (μ := muA) (measurableSet_singleton (0 : ℝ)),
    add_apply, hoff hvol, add_zero, Measure.restrict_apply hA]
  exact measure_mono_null inter_subset_right (ThomNoAtoms.muA_no_atoms 0)

/-- `LqTarget q ⇒ WeightedLqTarget q`: the weighted target is weaker. -/
theorem weightedLqTarget_of_lqTarget {q : ℝ} (hq : 0 < q) (h : LqTarget q) :
    WeightedLqTarget q := by
  obtain ⟨K, hK⟩ := h
  refine ⟨max K 0, fun P => ?_⟩
  have hmono : ∫ E, |polyFun (X ^ 2 * P) E| ^ q ∂arcsine ≤ ∫ E, |polyFun P E| ^ q ∂arcsine := by
    refine integral_mono_ae (integrable_of_continuous_arcsine
      ((continuous_polyFun _).abs.rpow_const fun _ => Or.inr hq.le))
      (integrable_of_continuous_arcsine ((continuous_polyFun _).abs.rpow_const
        fun _ => Or.inr hq.le)) (ae_arcsine_mem_Icc.mono fun E hE => ?_)
    have hx : (E / 4) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith [hE.1, hE.2]
    have : |polyFun (X ^ 2 * P) E| ≤ |polyFun P E| := by
      simp only [polyFun, eval_mul, eval_pow, eval_X, abs_mul]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hx
    exact Real.rpow_le_rpow (abs_nonneg _) this hq.le
  calc |tauPoly (X ^ 2 * P)| ≤ K * (∫ E, |polyFun (X ^ 2 * P) E| ^ q ∂arcsine) ^ (1 / q) := hK _
    _ ≤ max K 0 * (∫ E, |polyFun (X ^ 2 * P) E| ^ q ∂arcsine) ^ (1 / q) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (integral_nonneg fun _ => by positivity) hmono (by positivity)) (le_max_right _ _)

/-! ### What an `L^q` target forces on interval masses -/

/-- **`LqTarget q` forces power decay**: `μ_A(C) ≤ B·ρ(U)^{1/q}` for compact `C ⊆ U` open.
In particular `μ_A([-h,h]) = O(h^{1/q})`. The numerics (`numerics/README.md`, round 4) show
`μ_A([-h,h]) ≈ 0.45 / log²(1/h)` down to `h = 2⁻¹⁸`; if that persists, `LqTarget q`
fails for every `q < ∞`, and so do `FejerTarget p` (`p > 1`) and `PrincipalTarget`. -/
theorem muA_le_of_lqTarget {q : ℝ} (hq : 1 ≤ q) (h : LqTarget q) :
    ∃ B : ℝ, ∀ C U : Set ℝ, IsCompact C → IsOpen U → C ⊆ U →
      muA.real C ≤ B * (arcsine.real U) ^ (1 / q) := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨K, hK⟩ := h
  have hK' : ∀ P : ℝ[X], |∫ E, polyFun P E ∂muA| ≤
      K * (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) := fun P => by
    rw [integral_polyFun_muA]; exact hK P
  have key := measureReal_compact_le_of_poly_Lq_bound muA isSpectralMeasureA_muA.carried hq hK'
  set B := max K 0 * (2 ^ q + 1) ^ (1 / q) + muA.real univ with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ max K 0 := le_max_right _ _
    have : 0 ≤ muA.real univ := measureReal_nonneg
    positivity
  have hq0 : 0 < q := by linarith
  refine ⟨B, fun C U hC hU hCU => ?_⟩
  set r := arcsine.real U
  have hr0 : 0 ≤ r := measureReal_nonneg
  have hr1 : r ≤ 1 := by
    have := measureReal_mono (μ := arcsine) (subset_univ U)
    rwa [probReal_univ] at this
  rcases hr0.eq_or_lt with hr | hr
  · -- `ρ(U) = 0`: the bound holds with every `δ > 0`
    rw [← hr, Real.zero_rpow (by positivity), mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ := min 1 (ε / (B + 1))
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have h1 := key C U hC hU hCU δ hδ (min_le_left _ _) (by
      show r ≤ δ ^ q; rw [← hr]; positivity)
    have h2 : δ * B ≤ ε := by
      calc δ * B ≤ ε / (B + 1) * B := by gcongr; exact min_le_right _ _
        _ ≤ ε := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · set δ := r ^ (1 / q)
    have hδ : 0 < δ := Real.rpow_pos_of_pos hr _
    have hδ1 : δ ≤ 1 := Real.rpow_le_one hr0 hr1 (by positivity)
    have hδq : δ ^ q = r := by
      rw [← Real.rpow_mul hr0, one_div_mul_cancel hq0.ne', Real.rpow_one]
    have := key C U hC hU hCU δ hδ hδ1 (show r ≤ δ ^ q from hδq.ge)
    linarith [mul_comm δ B]

end ThomFejer
