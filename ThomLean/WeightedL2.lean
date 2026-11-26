import ThomLean.FejerTarget
import ThomLean.Chebyshev.Entropy

/-!
# `WeightedTarget ⇔ WeightedLqTarget 2`, and localization

Let `ν = (E²/16) μ_A` (`weighted muA`).

* `summable_of_L2_bound` (U, generic): for a finite measure `ν` carried by `[-4,4]`, a bound
  `|∫ P dν| ≤ K ‖P‖_{L²(ρ)}` on polynomials forces `∑ c_n(ν)² ≤ K²/2`. Test it on
  `P = ∑_{1≤n≤N} c_n T_n(·/4)`: then `∫ P dν = ∑ c_n²` and `‖P‖² = ∑ c_n²/2`.
* `L2_bound_of_summable` (U, generic): conversely, square-summable coefficients give an `L²(ρ)`
  density, hence the bound (Cauchy–Schwarz).
* `weightedLqTarget_two_iff` (U): `WeightedLqTarget 2 ↔ WeightedTarget`. The two open targets
  recommended after round 4 are the **same** statement.
* `muA_ac_iff_local` (U): `μ_A ≪ Lebesgue` iff `μ_A` restricted to `{|E| ≥ ε}` is absolutely
  continuous for every `ε > 0`. Local estimates away from `0` suffice; no global `L²` regularity
  is needed. This uses `μ_A{0} = 0`.
* `muA_ac_of_local_weighted` (C): local weighted `L²` bounds
  `|∫ P · 1_{|E|≥ε} dν| ≤ K_ε ‖P‖_{L²(ρ)}`, one for each `ε`, already imply `μ_A ≪ Lebesgue`.
-/

noncomputable section

namespace ThomWeightedL2

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence ThomConclusions ThomFejer ThomNoAtoms
open MeasureTheory Polynomial Polynomial.Chebyshev Real Set Filter Topology Finset

lemma polyFun_chebSum (a : ℕ → ℝ) (N : ℕ) (E : ℝ) :
    polyFun (∑ n ∈ range N, C (a n) * T ℝ ((n + 1 : ℕ) : ℤ)) E =
      ∑ n ∈ range N, a n * cheb (n + 1) E := by
  simp [polyFun, cheb, Polynomial.eval_finsetSum]

lemma integral_chebSum_sq (a : ℕ → ℝ) (N : ℕ) :
    ∫ E, |∑ n ∈ range N, a n * cheb (n + 1) E| ^ (2 : ℝ) ∂arcsine =
      (∑ n ∈ range N, a n ^ 2) / 2 := by
  have hint : ∀ n m : ℕ, Integrable (fun E => a n * cheb (n + 1) E * (a m * cheb (m + 1) E))
      arcsine := fun n m => integrable_of_continuous_arcsine (by
        have := continuous_cheb (n + 1); have := continuous_cheb (m + 1); fun_prop)
  have hexp : ∀ E, |∑ n ∈ range N, a n * cheb (n + 1) E| ^ (2 : ℝ) =
      ∑ n ∈ range N, ∑ m ∈ range N, a n * cheb (n + 1) E * (a m * cheb (m + 1) E) := by
    intro E
    rw [Real.rpow_two, sq_abs, sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m]
  have hin : ∀ n m : ℕ, ∫ E, a n * cheb (n + 1) E * (a m * cheb (m + 1) E) ∂arcsine =
      if n = m then a n ^ 2 / 2 else 0 := by
    intro n m
    have e : (fun E => a n * cheb (n + 1) E * (a m * cheb (m + 1) E)) =
        fun E => (a n * a m) * (cheb (n + 1) E * cheb (m + 1) E) := by ext E; ring
    rw [e, integral_const_mul]
    split_ifs with h
    · subst h; rw [integral_cheb_sq_of_ne_zero (Nat.succ_ne_zero n)]; ring
    · rw [integral_cheb_mul_cheb_of_ne (by omega), mul_zero]
  simp_rw [fun n => integral_finsetSum (range N) fun m _ => hint n m, hin]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_ite_eq (range N) n (fun _ => a n ^ 2 / 2), if_pos hn]

/-- **An `L²(ρ)` bound on polynomials forces square-summable Chebyshev coefficients.** -/
theorem summable_of_L2_bound (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : CarriedBy4 ν) (K : ℝ)
    (hK : ∀ P : ℝ[X], |∫ E, polyFun P E ∂ν| ≤
      K * (∫ E, |polyFun P E| ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ))) :
    Summable fun n => chebCoeff ν (n + 1) ^ 2 := by
  refine summable_of_sum_range_le (c := K ^ 2 / 2) (fun n => sq_nonneg _) fun N => ?_
  set d : ℕ → ℝ := fun n => chebCoeff ν (n + 1)
  set S := ∑ n ∈ range N, d n ^ 2
  set P : ℝ[X] := ∑ n ∈ range N, C (d n) * T ℝ ((n + 1 : ℕ) : ℤ)
  have hPf : polyFun P = fun E => ∑ n ∈ range N, d n * cheb (n + 1) E :=
    funext (polyFun_chebSum d N)
  have h1 : ∫ E, polyFun P E ∂ν = S := by
    rw [hPf, integral_finsetSum _ fun n _ =>
      (integrable_of_continuous hν (continuous_cheb (n + 1))).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]; simp only [d, chebCoeff]; ring
  have h2 : ∫ E, |polyFun P E| ^ (2 : ℝ) ∂arcsine = S / 2 := by
    rw [hPf]; exact integral_chebSum_sq d N
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hK' := hK P
  rw [h1, h2, abs_of_nonneg hS0, ← Real.sqrt_eq_rpow] at hK'
  set t := √(S / 2)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hSt : S = 2 * t ^ 2 := by rw [Real.sq_sqrt (by positivity)]; ring
  show S ≤ K ^ 2 / 2
  rw [hSt] at hK' ⊢
  nlinarith [sq_nonneg (K - 2 * t)]

/-- **Square-summable Chebyshev coefficients give an `L²(ρ)` bound on polynomials.** -/
theorem L2_bound_of_summable (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : CarriedBy4 ν)
    (hc : Summable fun n => chebCoeff ν (n + 1) ^ 2) :
    ∃ K : ℝ, ∀ P : ℝ[X], |∫ E, polyFun P E ∂ν| ≤
      K * (∫ E, |polyFun P E| ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ)) := by
  by_cases h0 : ν = 0
  · exact ⟨0, fun P => by simp [h0]⟩
  have : NeZero ν := ⟨h0⟩
  set ν' := (ν univ)⁻¹ • ν
  have hm : (ν univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(Measure.measure_univ_ne_zero).mpr h0, measure_ne_top _ _⟩
  set c := ((ν univ)⁻¹).toReal
  have hcm : c * (ν univ).toReal = 1 := by
    simp only [c, ENNReal.toReal_inv]; exact inv_mul_cancel₀ hm
  have hint : ∀ g : ℝ → ℝ, ∫ E, g E ∂ν' = c * ∫ E, g E ∂ν := fun g => by
    rw [integral_smul_measure, smul_eq_mul]
  have hν' : CarriedBy4 ν' := by
    unfold CarriedBy4 at hν ⊢
    rw [Measure.smul_apply, hν, smul_zero]
  have hc' : Summable fun n => chebCoeff ν' (n + 1) ^ 2 := by
    refine (hc.mul_left (c ^ 2)).congr fun n => ?_
    simp only [chebCoeff, hint]; ring
  obtain ⟨f, hfm, hf0, hfp, hνf, -⟩ := exists_density_of_summable ν' hν' hc'
  have hfp' : MemLp f (ENNReal.ofReal 2) arcsine := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  refine ⟨(ν univ).toReal * (∫ E, f E ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ)), fun P => ?_⟩
  have hb := lq_bound_of_Lp_density ν' Real.HolderConjugate.two_two hfm hf0 hfp' hνf P
  have he : ∫ E, polyFun P E ∂ν = (ν univ).toReal * ∫ E, polyFun P E ∂ν' := by
    rw [hint, ← mul_assoc, mul_comm (ν univ).toReal c, hcm, one_mul]
  rw [he, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg

/-- **The two weighted targets coincide**: `WeightedLqTarget 2 ↔ WeightedTarget`. -/
theorem weightedLqTarget_two_iff : WeightedLqTarget 2 ↔ WeightedTarget := by
  have hprob := isSpectralMeasureA_muA.isProb
  have hc := isSpectralMeasureA_muA.carried
  have := isFiniteMeasure_weighted muA hc
  have hcw := carried_weighted hc
  rw [weightedTarget_iff isSpectralMeasureA_muA]
  constructor
  · rintro ⟨K, hK⟩
    refine summable_of_L2_bound (weighted muA) hcw K fun P => ?_
    rw [integral_polyFun_weighted_muA]; exact hK P
  · intro h
    obtain ⟨K, hK⟩ := L2_bound_of_summable (weighted muA) hcw h
    exact ⟨K, fun P => by rw [← integral_polyFun_weighted_muA]; exact hK P⟩

/-! ### Localization away from `E = 0` -/

/-- **Localization** (unconditional): `μ_A ≪ Lebesgue` iff its restrictions to `{|E| ≥ ε}` are
absolutely continuous for all `ε > 0`. -/
theorem muA_ac_iff_local :
    muA ≪ volume ↔ ∀ ε : ℝ, 0 < ε → muA.restrict {E | ε ≤ |E|} ≪ volume := by
  constructor
  · intro h ε _; exact Measure.restrict_le_self.absolutelyContinuous.trans h
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
    have hcov : A ⊆ {0} ∪ ⋃ n : ℕ, (A ∩ {E | 1 / ((n : ℝ) + 1) ≤ |E|}) := by
      intro E hE
      by_cases h0 : E = 0
      · exact Or.inl h0
      · right
        have hpos : 0 < |E| := abs_pos.mpr h0
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        exact mem_iUnion.mpr ⟨n, hE, hn.le⟩
    refine measure_mono_null hcov (measure_union_null (muA_no_atoms 0)
      (measure_iUnion_null fun n => ?_))
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hm : MeasurableSet {E : ℝ | 1 / ((n : ℝ) + 1) ≤ |E|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have := h _ hε hvol
    rwa [Measure.restrict_apply hA] at this

/-- **Local weighted `L²` bounds suffice** (conditional): if for each `ε > 0` the functional
`P ↦ ∫_{|E| ≥ ε} P dν` (`ν = (E²/16) μ_A`) is bounded in `L²(ρ)`, then `μ_A ≪ Lebesgue`. -/
theorem muA_ac_of_local_weighted
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ P : ℝ[X],
      |∫ E, polyFun P E ∂((weighted muA).restrict {E | ε ≤ |E|})| ≤
        K * (∫ E, |polyFun P E| ^ (2 : ℝ) ∂arcsine) ^ (1 / (2 : ℝ))) :
    muA ≪ volume := by
  have hprob := isSpectralMeasureA_muA.isProb
  have hc := isSpectralMeasureA_muA.carried
  have := isFiniteMeasure_weighted muA hc
  refine muA_ac_iff_local.mpr fun ε hε => ?_
  set S := {E : ℝ | ε ≤ |E|}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  obtain ⟨K, hK⟩ := h ε hε
  set ν := (weighted muA).restrict S
  have hνc : CarriedBy4 ν := by
    unfold CarriedBy4
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    exact measure_mono_null inter_subset_left (carried_weighted hc)
  have hsum := summable_of_L2_bound ν hνc K hK
  have hνac : ν ≪ volume := ac_of_summable_finite ν hνc hsum
  -- on `S ⊆ {0}ᶜ`, `μ_A|_S ≪ ν`
  have hS0 : S ⊆ {0}ᶜ := by
    intro E hE h0
    have : ε ≤ |E| := hE
    rw [show E = 0 from h0, abs_zero] at this; linarith
  have h1 : muA.restrict S = (muA.restrict {0}ᶜ).restrict S := by
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr hS0]
  rw [h1]
  exact ((restrict_compl_zero_ac_weighted muA).restrict S).trans hνac

/-! ### The Fejér entropy target for `μ_A` -/

/-- **Fejér entropy target**: `H_N = ∫ F_N log F_N dρ` is bounded for `μ_A`. Open. -/
def FejerEntropyTarget : Prop := ∃ B : ℝ, ∀ N, fejEnt muA N ≤ B

/-- `FejerEntropyTarget ⇒ μ_A ≪ Lebesgue` (conditional). -/
theorem muA_ac_of_fejerEntropyTarget (h : FejerEntropyTarget) : muA ≪ volume := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨B, hB⟩ := h
  exact ac_of_fejEnt_bounded muA isSpectralMeasureA_muA.carried B hB

/-- Every Fejér `L^p` target (`p > 1`) implies the entropy target, which is strictly weaker on
the level of densities (`entropy_strictly_weaker`). -/
theorem fejerEntropyTarget_of_fejerTarget {p : ℝ} (hp : 1 < p) (h : FejerTarget p) :
    FejerEntropyTarget := by
  have := isSpectralMeasureA_muA.isProb
  obtain ⟨M, hM⟩ := h
  exact ⟨M / (p - 1), fejEnt_bounded_of_Lp muA isSpectralMeasureA_muA.carried hp M hM⟩

end ThomWeightedL2
