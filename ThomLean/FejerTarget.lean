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

end ThomFejer
