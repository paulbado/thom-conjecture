import ThomLean.Heisenberg.Threshold
import ThomLean.Chebyshev.Lebesgue

/-!
# Bridge: Chebyshev coefficients of the Heisenberg spectral measure

* `chebTrace n = τ(T_n(A/4))`, computed in the real group ring `ℝ[H₃(ℤ)]`.
* `chebTrace_eq` : `τ(T_n(A/4)) = ∑_k [Xᵏ]T_n · 4⁻ᵏ · m_k` with `m_k` the zero-area walk counts.
* `IsSpectralMeasureA μ` : `μ` is a probability measure on `[-4,4]` whose moments are
  `τ(Aⁿ)`. This is the defining property of the canonical spectral measure `μ_A`.
  Its *existence* (spectral theorem in the group von Neumann algebra) is **not** formalized;
  `spectral_unique` proves *uniqueness*.
* `chebCoeff_eq_chebTrace` : for such `μ`, `∫ T_n(E/4) dμ = τ(T_n(A/4))`.
* `PrincipalTarget : Prop := Summable (n ↦ τ(T_{n+1}(A/4))²)` — the open target, only *named*.
* `principalTarget_iff_L2` : for a spectral measure `μ`, the target holds **iff** `μ` has a
  density in `L²(arcsine)` (criterion + Bessel inequality).
* `ac_of_principalTarget` : target ⟹ `μ ≪ Lebesgue` with locally `L²` density on `(-4,4)`.
* `fluxCheb_eq_chebTrace` : the Chebyshev coefficients built from the rational-flux moments
  `m_k^{(Q)}` coincide with `τ(T_n(A/4))` for `n < N_Q` (exact, from the threshold theorem).
* `principalTarget_iff_uniform_flux` : the target is **equivalent** to a uniform bound
  `∑_{1 ≤ n < N_Q} (c_n^{(Q)})² ≤ K` on the finite rational-flux Chebyshev energies.
-/

noncomputable section

namespace ThomBridge

open ThomHeisenberg ThomChebyshev MeasureTheory Polynomial Polynomial.Chebyshev Set

/-- Chebyshev coefficients from a moment sequence: `∑_k [Xᵏ]T_n · 4⁻ᵏ · m_k`. -/
def chebOfMoments (m : ℕ → ℝ) (n : ℕ) : ℝ := (T ℝ n).sum fun k a => a * (4⁻¹ : ℝ) ^ k * m k

/-- Any linear functional on `ℝ[X]` is determined by its values on monomials. -/
lemma linear_eq_sum (Λ : ℝ[X] →ₗ[ℝ] ℝ) (p : ℝ[X]) : Λ p = p.sum fun k a => a * Λ (X ^ k) := by
  conv_lhs => rw [← p.sum_monomial_eq]
  rw [Polynomial.sum, map_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, smul_eq_mul]

lemma chebOfMoments_congr {m m' : ℕ → ℝ} {n : ℕ} (h : ∀ k ≤ n, m k = m' k) :
    chebOfMoments m n = chebOfMoments m' n := by
  unfold chebOfMoments Polynomial.sum
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by
    have := le_natDegree_of_mem_supp k hk
    rwa [natDegree_T ℝ (n : ℤ), Int.natAbs_natCast] at this
  simp only [h k hk']

/-! ### The trace side -/

/-- The canonical trace as an `ℝ`-linear map. -/
def tauL : MonoidAlgebra ℝ H3 →ₗ[ℝ] ℝ where
  toFun := tau ℝ
  map_add' f g := by simp [tau, MonoidAlgebra.coeff_add]
  map_smul' c f := by simp [tau]

/-- `c_n = τ(T_n(A/4))`. -/
def chebTrace (n : ℕ) : ℝ := tau ℝ (aeval ((4⁻¹ : ℝ) • opA ℝ) (T ℝ n))

theorem chebTrace_eq (n : ℕ) : chebTrace n = chebOfMoments (fun k => (moment k : ℝ)) n := by
  let Λ : ℝ[X] →ₗ[ℝ] ℝ := tauL ∘ₗ (aeval ((4⁻¹ : ℝ) • opA ℝ)).toLinearMap
  have h1 : chebTrace n = Λ (T ℝ n) := rfl
  rw [h1, linear_eq_sum, chebOfMoments]
  congr 1; ext k a
  simp only [Λ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, aeval_X, smul_pow,
    map_smul, smul_eq_mul]
  rw [show tauL (opA ℝ ^ k) = tau ℝ (opA ℝ ^ k) from rfl, tau_opA_pow, moment]
  ring

/-! ### Spectral measures -/

/-- `μ` is a spectral measure for `A`: a probability measure carried by `[-4,4]` with
`∫ Eᵏ dμ = τ(Aᵏ)` for all `k`. -/
structure IsSpectralMeasureA (μ : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  carried : CarriedBy4 μ
  moments : ∀ k : ℕ, ∫ E, E ^ k ∂μ = moment k

theorem chebCoeff_eq_chebOfMoments (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (m : ℕ → ℝ) (hm : ∀ k : ℕ, ∫ E, E ^ k ∂μ = m k) (n : ℕ) :
    chebCoeff μ n = chebOfMoments m n := by
  rw [show chebCoeff μ n = polyIntegral μ hμ (T ℝ n) from rfl, linear_eq_sum, chebOfMoments]
  congr 1; ext k a
  show a * ∫ E, polyFun (X ^ k) E ∂μ = _
  simp only [polyFun, eval_pow, eval_X, div_eq_mul_inv, mul_pow]
  rw [integral_mul_const, hm k]; ring

theorem chebCoeff_eq_chebTrace {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) (n : ℕ) :
    chebCoeff μ n = chebTrace n := by
  have := hμ.isProb
  rw [chebCoeff_eq_chebOfMoments μ hμ.carried _ hμ.moments, chebTrace_eq]

/-- **Uniqueness** of the spectral measure. -/
theorem spectral_unique {μ ν : Measure ℝ} (hμ : IsSpectralMeasureA μ) (hν : IsSpectralMeasureA ν) :
    μ = ν := by
  have := hμ.isProb; have := hν.isProb
  exact eq_of_integral_cheb_eq hμ.carried hν.carried fun n => by
    rw [chebCoeff_eq_chebTrace hμ, chebCoeff_eq_chebTrace hν]

/-! ### The principal target -/

/-- **Principal research target** (a proposition; *not* assumed anywhere):
`∑_{n ≥ 1} τ(T_n(A/4))² < ∞`. -/
def PrincipalTarget : Prop := Summable fun n => chebTrace (n + 1) ^ 2

/-- Converse direction (Bessel): an `L²(arcsine)` density forces square-summable
Chebyshev coefficients. -/
theorem summable_of_L2_density (μ : Measure ℝ) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ E, 0 ≤ f E) (hf2 : MemLp f 2 arcsine)
    (hμf : μ = arcsine.withDensity fun E => ENNReal.ofReal (f E)) :
    Summable fun n => chebCoeff μ (n + 1) ^ 2 := by
  have hc : ∀ n, chebCoeff μ n = (normConst n)⁻¹ * inner ℝ (chebL2 n) (hf2.toLp f) := by
    intro n
    have hc0 : normConst n ≠ 0 := by unfold normConst; split_ifs <;> positivity
    rw [chebL2, inner_toLp_eq]
    simp only [chebFun, mul_assoc]
    rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, chebCoeff, hμf,
      show (fun E => ENNReal.ofReal (f E)) = fun E => ((Real.toNNReal (f E) : NNReal) : ENNReal)
        from rfl,
      integral_withDensity_eq_integral_smul hfm.real_toNNReal]
    congr 1; ext E
    simp [NNReal.smul_def, Real.coe_toNNReal _ (hf0 E), mul_comm]
  have hB := orthonormal_chebL2.inner_products_summable (hf2.toLp f)
  rw [← summable_nat_add_iff 1] at hB
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hB
  rw [hc]
  simp only [normConst, Nat.succ_ne_zero, if_false, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  have := sq_nonneg (inner ℝ (chebL2 (n + 1)) (hf2.toLp f))
  nlinarith

/-- **The target is equivalent to an `L²(arcsine)` density** for the spectral measure. -/
theorem principalTarget_iff_L2 {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) :
    PrincipalTarget ↔ ∃ f : ℝ → ℝ, Measurable f ∧ (∀ E, 0 ≤ f E) ∧ MemLp f 2 arcsine ∧
      μ = arcsine.withDensity fun E => ENNReal.ofReal (f E) := by
  have := hμ.isProb
  have hcc : (fun n => chebCoeff μ (n + 1) ^ 2) = fun n => chebTrace (n + 1) ^ 2 := by
    ext n; rw [chebCoeff_eq_chebTrace hμ]
  constructor
  · intro h
    obtain ⟨f, hfm, hf0, hf2, hμf, -⟩ := exists_density_of_summable μ hμ.carried (by rwa [hcc])
    exact ⟨f, hfm, hf0, hf2, hμf⟩
  · rintro ⟨f, hfm, hf0, hf2, hμf⟩
    have := summable_of_L2_density μ hfm hf0 hf2 hμf
    rwa [hcc] at this

/-- **Conditional absolute continuity**: the principal target implies `μ_A ≪ Lebesgue`
with a Lebesgue density that is `L²` on every compact subinterval of `(-4,4)`. -/
theorem ac_of_principalTarget {μ : Measure ℝ} (hμ : IsSpectralMeasureA μ) (h : PrincipalTarget) :
    μ ≪ volume ∧ ∃ g : ℝ → ℝ, Measurable g ∧ (∀ E, 0 ≤ g E) ∧
      μ = volume.withDensity (fun E => ENNReal.ofReal (g E)) ∧
      ∀ a b : ℝ, -4 < a → b < 4 → MemLp g 2 (volume.restrict (Icc a b)) := by
  have := hμ.isProb
  have hc : Summable fun n => chebCoeff μ (n + 1) ^ 2 := by
    have hcc : (fun n => chebCoeff μ (n + 1) ^ 2) = fun n => chebTrace (n + 1) ^ 2 := by
      ext n; rw [chebCoeff_eq_chebTrace hμ]
    rw [hcc]; exact h
  exact ⟨absolutelyContinuous_of_summable μ hμ.carried hc,
    exists_lebesgue_density_of_summable μ hμ.carried hc⟩

/-! ### Exact finite-`Q` reformulation through rational flux -/

/-- Chebyshev coefficients of the rational-flux moment sequence `m^{(Q)}`. -/
def fluxCheb (Q n : ℕ) : ℝ := chebOfMoments (fun k => (fluxMoment Q k : ℝ)) n

/-- Below `N_Q`, the rational-flux Chebyshev coefficients are *exactly* `τ(T_n(A/4))`. -/
theorem fluxCheb_eq_chebTrace {Q n : ℕ} (hQ : 0 < Q) (hn : n < NQ Q) :
    fluxCheb Q n = chebTrace n := by
  rw [chebTrace_eq, fluxCheb]
  apply chebOfMoments_congr
  intro k hk
  rw [moment_eq_fluxMoment hQ (by omega)]

lemma lt_NQ_sq_add_one (N : ℕ) : N + 1 ≤ NQ (N ^ 2 + 1) - 1 := by
  have h := kQ_spec (N ^ 2 + 1)
  have : 2 * N < kQ (N ^ 2 + 1) := by
    by_contra hc
    push Not at hc
    have : kQ (N ^ 2 + 1) ^ 2 ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hc 2
    nlinarith
  unfold NQ; omega

/-- **Exact finite reformulation of the principal target**: it holds iff the rational-flux
Chebyshev energies `∑_{1 ≤ n < N_Q} (c_n^{(Q)})²` are bounded uniformly in `Q`. The right-hand
side involves only finitely many integer walk counts for each `Q`. -/
theorem principalTarget_iff_uniform_flux :
    PrincipalTarget ↔ ∃ K : ℝ, ∀ Q : ℕ, 0 < Q →
      ∑ n ∈ Finset.range (NQ Q - 1), fluxCheb Q (n + 1) ^ 2 ≤ K := by
  constructor
  · intro h
    refine ⟨∑' n, chebTrace (n + 1) ^ 2, fun Q hQ => ?_⟩
    have : ∑ n ∈ Finset.range (NQ Q - 1), fluxCheb Q (n + 1) ^ 2 =
        ∑ n ∈ Finset.range (NQ Q - 1), chebTrace (n + 1) ^ 2 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      rw [fluxCheb_eq_chebTrace hQ (by omega)]
    rw [this]
    exact h.sum_le_tsum _ (fun n _ => sq_nonneg _)
  · rintro ⟨K, hK⟩
    refine summable_of_sum_range_le (c := K) (fun n => sq_nonneg _) (fun N => ?_)
    have hQ : 0 < N ^ 2 + 1 := by positivity
    have hN := lt_NQ_sq_add_one N
    calc ∑ n ∈ Finset.range N, chebTrace (n + 1) ^ 2
        ≤ ∑ n ∈ Finset.range (NQ (N ^ 2 + 1) - 1), chebTrace (n + 1) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun n _ _ => sq_nonneg _)
      _ = ∑ n ∈ Finset.range (NQ (N ^ 2 + 1) - 1), fluxCheb (N ^ 2 + 1) (n + 1) ^ 2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_range] at hn
          rw [fluxCheb_eq_chebTrace hQ (by omega)]
      _ ≤ K := hK _ hQ

end ThomBridge
