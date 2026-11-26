import ThomLean.Bridge
import ThomLean.Chebyshev.Weighted

/-!
# The weighted target for the Heisenberg operator

With `c_n = τ(T_n(A/4))` and `dν = (E²/16) dμ_A`, the Chebyshev coefficients of `ν` are, for
`n ≥ 2`, `d_n = (c_{n-2} + 2 c_n + c_{n+2}) / 4` (`chebCoeff_weighted`).

* `weightedTrace n := (c_n + 2 c_{n+2} + c_{n+4}) / 4` (this is `d_{n+2}`).
* `WeightedTarget : Prop := Summable (n ↦ weightedTrace n ²)` — an open proposition, only named.
* `weightedTarget_iff` : for a spectral measure `μ`, the target is exactly
  `∑ d_{n+1}² < ∞` for `ν = weighted μ`.
* `ac_off_zero_of_weightedTarget` : target ⇒ `μ|_{ℝ∖{0}} ≪ Lebesgue`.
* `ac_of_weightedTarget` : target and `μ{0} = 0` ⇒ `μ ≪ Lebesgue`.
* `weightedTarget_of_principalTarget` : the old target implies the new one.
* `weightedTarget_iff_uniform_flux` : exact reformulation through finitely many
  rational-flux walk counts for each `Q`.
* `atom_le_integral_sq`, `atom_le_tau` : the Christoffel-type bound
  `μ{0} ≤ τ(p(A/4)²)` for every real polynomial with `p(0) = 1`.
-/

noncomputable section

namespace ThomBridge

open ThomHeisenberg ThomChebyshev MeasureTheory Polynomial Polynomial.Chebyshev Set

/-- `d_{n+2} = (c_n + 2 c_{n+2} + c_{n+4}) / 4` computed from the traces. -/
def weightedTrace (n : ℕ) : ℝ := (chebTrace n + 2 * chebTrace (n + 2) + chebTrace (n + 4)) / 4

/-- **Weighted research target** (a proposition, *not* assumed anywhere):
`∑_{n ≥ 2} |c_{n-2} + 2 c_n + c_{n+2}|² < ∞`. -/
def WeightedTarget : Prop := Summable fun n => weightedTrace n ^ 2

theorem chebCoeff_weighted_eq {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) (n : ℕ) :
    chebCoeff (weighted μ) (n + 2) = weightedTrace n := by
  have := hμ.isProb
  rw [chebCoeff_weighted μ hμ.carried, chebCoeff_eq_chebTrace hμ, chebCoeff_eq_chebTrace hμ,
    chebCoeff_eq_chebTrace hμ, weightedTrace]

theorem weightedTarget_iff {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) :
    WeightedTarget ↔ Summable fun n => chebCoeff (weighted μ) (n + 1) ^ 2 := by
  rw [← summable_nat_add_iff 1 (f := fun n => chebCoeff (weighted μ) (n + 1) ^ 2)]
  have : (fun n => chebCoeff (weighted μ) (n + 1 + 1) ^ 2) = fun n => weightedTrace n ^ 2 := by
    ext n; rw [show n + 1 + 1 = n + 2 by ring, chebCoeff_weighted_eq hμ]
  rw [this]; rfl

/-- **Weighted target ⇒ absolute continuity away from zero.** -/
theorem ac_off_zero_of_weightedTarget {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ)
    (h : WeightedTarget) : μ.restrict {0}ᶜ ≪ volume := by
  have := hμ.isProb
  exact ac_off_zero_of_weighted_summable μ hμ.carried ((weightedTarget_iff hμ).mp h)

/-- **Conditional theorem**: for the spectral measure, the weighted target together with the
absence of an atom at `0` gives `μ_A ≪ Lebesgue`. -/
theorem ac_of_weightedTarget {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) (h0 : μ {0} = 0)
    (h : WeightedTarget) : μ ≪ volume := by
  have := hμ.isProb
  exact ac_of_weighted_summable μ hμ.carried ((weightedTarget_iff hμ).mp h) h0

/-- The old target implies the new one. -/
theorem weightedTarget_of_principalTarget (h : PrincipalTarget) : WeightedTarget := by
  have h0 : Summable fun n => chebTrace n ^ 2 := (summable_nat_add_iff 1).mp h
  have h2 : Summable fun n => chebTrace (n + 2) ^ 2 := (summable_nat_add_iff 2).mpr h0
  have h4 : Summable fun n => chebTrace (n + 4) ^ 2 := (summable_nat_add_iff 4).mpr h0
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((h0.add (h2.mul_left 4)).add h4)
  simp only [weightedTrace]
  nlinarith [sq_nonneg (chebTrace n - chebTrace (n + 2)),
    sq_nonneg (chebTrace n - chebTrace (n + 4)),
    sq_nonneg (chebTrace (n + 2) - chebTrace (n + 4)),
    sq_nonneg (chebTrace n), sq_nonneg (chebTrace (n + 2)), sq_nonneg (chebTrace (n + 4))]

/-! ### Exact finite-`Q` reformulation -/

/-- Weighted coefficients of the rational-flux moment sequence. -/
def fluxWeighted (Q n : ℕ) : ℝ :=
  (fluxCheb Q n + 2 * fluxCheb Q (n + 2) + fluxCheb Q (n + 4)) / 4

theorem fluxWeighted_eq {Q n : ℕ} (hQ : 0 < Q) (hn : n + 4 < NQ Q) :
    fluxWeighted Q n = weightedTrace n := by
  rw [fluxWeighted, weightedTrace, fluxCheb_eq_chebTrace hQ (by omega),
    fluxCheb_eq_chebTrace hQ (by omega), fluxCheb_eq_chebTrace hQ hn]

/-- **Exact finite reformulation of the weighted target.** -/
theorem weightedTarget_iff_uniform_flux :
    WeightedTarget ↔ ∃ K : ℝ, ∀ Q : ℕ, 0 < Q →
      ∑ n ∈ Finset.range (NQ Q - 4), fluxWeighted Q n ^ 2 ≤ K := by
  constructor
  · intro h
    refine ⟨∑' n, weightedTrace n ^ 2, fun Q hQ => ?_⟩
    have : ∑ n ∈ Finset.range (NQ Q - 4), fluxWeighted Q n ^ 2 =
        ∑ n ∈ Finset.range (NQ Q - 4), weightedTrace n ^ 2 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      rw [fluxWeighted_eq hQ (by omega)]
    rw [this]
    exact h.sum_le_tsum _ (fun n _ => sq_nonneg _)
  · rintro ⟨K, hK⟩
    refine summable_of_sum_range_le (c := K) (fun n => sq_nonneg _) (fun N => ?_)
    have hQ : 0 < (N + 2) ^ 2 + 1 := by positivity
    have hN := lt_NQ_sq_add_one (N + 2)
    calc ∑ n ∈ Finset.range N, weightedTrace n ^ 2
        ≤ ∑ n ∈ Finset.range (NQ ((N + 2) ^ 2 + 1) - 4), weightedTrace n ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun n _ _ => sq_nonneg _)
      _ = ∑ n ∈ Finset.range (NQ ((N + 2) ^ 2 + 1) - 4),
            fluxWeighted ((N + 2) ^ 2 + 1) n ^ 2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_range] at hn
          rw [fluxWeighted_eq hQ (by omega)]
      _ ≤ K := hK _ hQ

/-! ### Christoffel-type upper bounds for the atom at zero -/

/-- For any finite measure and continuous `f` with `f 0 = 1`: `μ{0} ≤ ∫ f² dμ`. -/
theorem atom_le_integral_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 1) :
    (μ {0}).toReal ≤ ∫ E, f E ^ 2 ∂μ := by
  have hint := integrable_of_continuous hμ (hf.pow 2)
  calc (μ {0}).toReal = ∫ E in ({0} : Set ℝ), f E ^ 2 ∂μ := by
        rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac, hf0]; simp
    _ ≤ ∫ E, f E ^ 2 ∂μ :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun E => sq_nonneg _)

/-- **Computable atom bound**: for a spectral measure and any real polynomial `p` with
`p(0) = 1`, `μ{0} ≤ τ(p(A/4)²) = ∑_k [Xᵏ](p²) · 4⁻ᵏ · τ(Aᵏ)`. -/
theorem atom_le_tau {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) (p : ℝ[X]) (hp : p.eval 0 = 1) :
    (μ {0}).toReal ≤ (p ^ 2).sum fun k a => a * (4⁻¹ : ℝ) ^ k * (moment k : ℝ) := by
  have := hμ.isProb
  have h := atom_le_integral_sq μ hμ.carried (continuous_polyFun p) (by simp [polyFun, hp])
  refine h.trans (le_of_eq ?_)
  have : ∫ E, polyFun p E ^ 2 ∂μ = polyIntegral μ hμ.carried (p ^ 2) := by
    show _ = ∫ E, polyFun (p ^ 2) E ∂μ
    congr 1; ext E; simp [polyFun]
  rw [this, linear_eq_sum]
  congr 1; ext k a
  show a * ∫ E, polyFun (X ^ k) E ∂μ = _
  simp only [polyFun, eval_pow, eval_X, div_eq_mul_inv, mul_pow]
  rw [integral_mul_const, hμ.moments k]; ring

end ThomBridge
