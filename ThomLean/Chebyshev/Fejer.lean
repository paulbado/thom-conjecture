import ThomLean.Chebyshev.Duality

/-!
# The Fejér criterion

For a probability measure `μ` carried by `[-4,4]` with Chebyshev coefficients
`c_n = ∫ T_n(E/4) dμ`, the **Fejér density** is

`F_N(E) = 1 + 2 ∑_{n=1}^N (1 - n/(N+1)) c_n T_n(E/4)`,

i.e. `F_N(4 cos θ) = 1 + 2 ∑_{n=1}^N (1 - n/(N+1)) c_n cos nθ` (`fejer_cos`), the Fejér mean of
the cosine series of the angular pushforward of `μ`.

* `integral_fejer_mul_cheb` : `∫ F_N T_m(E/4) dρ = (1 - m/(N+1))₊ c_m` (`m ≤ N`), `0` otherwise;
  in particular `∫ F_N dρ = 1` (`integral_fejer`).
* `tendsto_integral_fejer_mul_poly` : `∫ F_N P(E/4) dρ → ∫ P(E/4) dμ` for every polynomial `P`
  (weak convergence of `F_N dρ` to `μ` tested on polynomials).
* `lq_bound_of_fejer` : if `sup_N ‖F_N‖_{L^p(ρ)} ≤ M` with `p, q` Hölder conjugate, then
  `|∫ P(E/4) dμ| ≤ M ‖P(·/4)‖_{L^q(ρ)}` for all polynomials `P` (the duality target).
* `ac_of_fejer_bounded` : for `1 < p`, uniformly bounded `∫ |F_N|^p dρ` implies `μ ≪ Lebesgue`.
* `lq_bound_of_Lp_density` : conversely, an `L^p(ρ)` density gives the `L^q` duality bound.
-/

noncomputable section

namespace ThomChebyshev

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set Filter Topology

/-- Continuous functions are in every `L^p(arcsine)`. -/
lemma memLp_of_continuous_arcsine {f : ℝ → ℝ} (hf : Continuous f) (p : ENNReal) :
    MemLp f p arcsine := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_arcsine_mem_Icc.mono fun E hE => hC E hE)

lemma integrable_of_continuous_arcsine {f : ℝ → ℝ} (hf : Continuous f) : Integrable f arcsine :=
  integrable_of_continuous arcsine_compl_Icc hf

/-- Fejér multipliers `(1 - m/(N+1))₊`. -/
def fejMult (N m : ℕ) : ℝ := if m ≤ N then 1 - m / (N + 1) else 0

lemma fejMult_zero (N : ℕ) : fejMult N 0 = 1 := by simp [fejMult]

lemma tendsto_fejMult (m : ℕ) : Tendsto (fun N => fejMult N m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 - (m : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine h.congr' (eventually_atTop.2 ⟨m, fun N hN => ?_⟩)
  simp [fejMult, hN]

/-- **Fejér density** `F_N(E) = 1 + 2 ∑_{n=1}^N (1 - n/(N+1)) c_n T_n(E/4)`. -/
def fejer (μ : Measure ℝ) (N : ℕ) (E : ℝ) : ℝ :=
  1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * chebCoeff μ (n + 1) * cheb (n + 1) E

lemma continuous_fejer (μ : Measure ℝ) (N : ℕ) : Continuous (fejer μ N) := by
  have := continuous_cheb
  unfold fejer
  fun_prop

/-- Angle form: `F_N(4 cos θ) = 1 + 2 ∑_{n=1}^N (1 - n/(N+1)) c_n cos nθ`. -/
theorem fejer_cos (μ : Measure ℝ) (N : ℕ) (θ : ℝ) :
    fejer μ N (4 * cos θ) =
      1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * chebCoeff μ (n + 1) * cos ((n + 1) * θ) := by
  unfold fejer
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cheb_scale]
  have := T_real_cos θ (n + 1 : ℤ)
  push_cast at this ⊢
  rw [this]

/-- **Coefficients of the Fejér density.** -/
theorem integral_fejer_mul_cheb (μ : Measure ℝ) [IsProbabilityMeasure μ] (N m : ℕ) :
    ∫ E, fejer μ N E * cheb m E ∂arcsine = fejMult N m * chebCoeff μ m := by
  have hint : ∀ n, Integrable (fun E => cheb n E * cheb m E) arcsine := fun n =>
    integrable_of_continuous_arcsine ((continuous_cheb n).mul (continuous_cheb m))
  have hsplit : (fun E => fejer μ N E * cheb m E) = fun E => cheb m E +
      ∑ n ∈ Finset.range N, (2 * fejMult N (n + 1) * chebCoeff μ (n + 1)) *
        (cheb (n + 1) E * cheb m E) := by
    ext E
    simp only [fejer, add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit, integral_add (integrable_of_continuous_arcsine (continuous_cheb m))
    (integrable_finsetSum _ fun n _ => (hint (n + 1)).const_mul _),
    integral_finsetSum _ fun n _ => (hint (n + 1)).const_mul _]
  simp_rw [integral_const_mul]
  rw [integral_cheb]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Finset.sum_eq_zero fun n _ => by rw [integral_cheb_mul_cheb_of_ne (by omega), mul_zero]]
    simp [fejMult_zero, chebCoeff_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hval : ∀ n ∈ Finset.range N, 2 * fejMult N (n + 1) * chebCoeff μ (n + 1) *
        ∫ E, cheb (n + 1) E * cheb (k + 1) E ∂arcsine =
          if n = k then fejMult N (k + 1) * chebCoeff μ (k + 1) else 0 := by
      intro n _
      split_ifs with hnk
      · subst hnk; rw [integral_cheb_sq_of_ne_zero (by omega)]; ring
      · rw [integral_cheb_mul_cheb_of_ne (by omega), mul_zero]
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
    simp only [show k + 1 ≠ 0 by omega, ite_false, zero_add, Finset.mem_range]
    split_ifs with hk
    · rfl
    · simp [fejMult, show ¬ k + 1 ≤ N by omega]

/-- **Normalisation**: `∫ F_N dρ = 1`. -/
theorem integral_fejer (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) :
    ∫ E, fejer μ N E ∂arcsine = 1 := by
  have := integral_fejer_mul_cheb μ N 0
  simpa [cheb_zero, fejMult_zero, chebCoeff_zero] using this

/-- The Fejér functional `P ↦ ∫ F_N P(E/4) dρ`. -/
def fejerFunctional (μ : Measure ℝ) (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∫ E, fejer μ N E * polyFun P E ∂arcsine
  map_add' P Q := by
    rw [← integral_add (f := fun E => fejer μ N E * polyFun P E)
      (g := fun E => fejer μ N E * polyFun Q E)
      (integrable_of_continuous_arcsine ((continuous_fejer μ N).mul (continuous_polyFun P)))
      (integrable_of_continuous_arcsine ((continuous_fejer μ N).mul (continuous_polyFun Q)))]
    congr 1; ext E; simp [polyFun]; ring
  map_smul' c P := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1; ext E; simp [polyFun]; ring

/-- **Weak convergence on polynomials**: `∫ F_N P(E/4) dρ → ∫ P(E/4) dμ`. -/
theorem tendsto_integral_fejer_mul_poly (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CarriedBy4 μ) (P : ℝ[X]) :
    Tendsto (fun N => ∫ E, fejer μ N E * polyFun P E ∂arcsine) atTop
      (𝓝 (∫ E, polyFun P E ∂μ)) := by
  let S : Submodule ℝ ℝ[X] :=
    { carrier := {P | Tendsto (fun N => fejerFunctional μ N P) atTop (𝓝 (polyIntegral μ hμ P))}
      add_mem' := fun {P Q} hP hQ => by
        simp only [mem_ofPred_eq, map_add] at hP hQ ⊢; exact hP.add hQ
      zero_mem' := by simp only [mem_ofPred_eq, map_zero]; exact tendsto_const_nhds
      smul_mem' := fun c P hP => by
        simp only [mem_ofPred_eq, map_smul, smul_eq_mul] at hP ⊢; exact hP.const_mul c }
  have hT : ∀ m : ℕ, T ℝ m ∈ S := fun m => by
    show Tendsto (fun N => fejerFunctional μ N (T ℝ m)) atTop (𝓝 (polyIntegral μ hμ (T ℝ m)))
    have h : ∀ N, fejerFunctional μ N (T ℝ m) = fejMult N m * chebCoeff μ m := fun N =>
      integral_fejer_mul_cheb μ N m
    simp_rw [h, polyIntegral_T]
    simpa using (tendsto_fejMult m).mul_const (chebCoeff μ m)
  have hspan : Submodule.span ℝ (range fun k : ℕ => T ℝ k) ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hT k
  exact hspan (mem_span_T P)

/-- **Hölder step**: `|∫ F_N P(E/4) dρ| ≤ ‖F_N‖_p ‖P(·/4)‖_q`. -/
lemma abs_integral_fejer_mul_poly_le (μ : Measure ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (N : ℕ) (P : ℝ[X]) :
    |∫ E, fejer μ N E * polyFun P E ∂arcsine| ≤
      (∫ E, |fejer μ N E| ^ p ∂arcsine) ^ (1 / p) *
        (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) := by
  calc |∫ E, fejer μ N E * polyFun P E ∂arcsine|
      ≤ ∫ E, |fejer μ N E| * |polyFun P E| ∂arcsine := by
        refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
        congr 1; ext E; rw [abs_mul]
    _ ≤ _ := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun _ => abs_nonneg _)
        (ae_of_all _ fun _ => abs_nonneg _)
        (memLp_of_continuous_arcsine (continuous_fejer μ N).abs _)
        (memLp_of_continuous_arcsine (continuous_polyFun P).abs _)

/-- **Fejér criterion, dual form**: uniformly bounded `L^p(ρ)` norms of the Fejér densities give
the `L^q` duality bound for the moment functional. -/
theorem lq_bound_of_fejer (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    {p q : ℝ} (hpq : p.HolderConjugate q) (M : ℝ)
    (hM : ∀ N, (∫ E, |fejer μ N E| ^ p ∂arcsine) ^ (1 / p) ≤ M) (P : ℝ[X]) :
    |∫ E, polyFun P E ∂μ| ≤ M * (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) := by
  have hlim := (tendsto_integral_fejer_mul_poly μ hμ P).abs
  refine le_of_tendsto' hlim fun N => ?_
  refine (abs_integral_fejer_mul_poly_le μ hpq N P).trans ?_
  exact mul_le_mul_of_nonneg_right (hM N)
    (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)

/-- **Fejér criterion**: if `1 < p` and `sup_N ∫ |F_N|^p dρ < ∞`, then `μ ≪ Lebesgue`. -/
theorem ac_of_fejer_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    {p : ℝ} (hp : 1 < p) (M : ℝ) (hM : ∀ N, ∫ E, |fejer μ N E| ^ p ∂arcsine ≤ M) :
    μ ≪ volume := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hq : 1 ≤ p.conjExponent := hpq.symm.lt.le
  have hp0 : 0 < p := by linarith
  refine ac_of_poly_Lq_bound μ hμ hq (K := M ^ (1 / p)) fun P =>
    lq_bound_of_fejer μ hμ hpq (M ^ (1 / p)) (fun N => ?_) P
  exact Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) (hM N) (by positivity)

/-- **Converse, dual form**: an `L^p(ρ)` density gives the `L^q` duality bound (Hölder). -/
theorem lq_bound_of_Lp_density (μ : Measure ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ E, 0 ≤ f E) (hfp : MemLp f (ENNReal.ofReal p) arcsine)
    (hμf : μ = arcsine.withDensity fun E => ENNReal.ofReal (f E)) (P : ℝ[X]) :
    |∫ E, polyFun P E ∂μ| ≤ (∫ E, f E ^ p ∂arcsine) ^ (1 / p) *
      (∫ E, |polyFun P E| ^ q ∂arcsine) ^ (1 / q) := by
  rw [hμf, show (fun E => ENNReal.ofReal (f E)) =
      fun E => ((Real.toNNReal (f E) : NNReal) : ENNReal) from rfl,
    integral_withDensity_eq_integral_smul hfm.real_toNNReal]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hf0 _), smul_eq_mul]
  calc |∫ E, f E * polyFun P E ∂arcsine| ≤ ∫ E, f E * |polyFun P E| ∂arcsine := by
        refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
        congr 1; ext E; rw [abs_mul, abs_of_nonneg (hf0 E)]
    _ ≤ _ := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ hf0)
        (ae_of_all _ fun _ => abs_nonneg _) hfp
        (memLp_of_continuous_arcsine (continuous_polyFun P).abs _)

/-! ### Positivity of the Fejér density -/

/-- **Fejér's identity**: `(N+1) + 2∑_{n<N} (N-n) cos((n+1)x) = |∑_{k≤N} e^{ikx}|²`. -/
theorem fejer_identity (N : ℕ) (x : ℝ) :
    (N + 1 : ℝ) + 2 * ∑ n ∈ Finset.range N, ((N : ℝ) - n) * cos ((n + 1) * x) =
      (∑ k ∈ Finset.range (N + 1), cos (k * x)) ^ 2 +
        (∑ k ∈ Finset.range (N + 1), sin (k * x)) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    set A := ∑ k ∈ Finset.range (N + 1), cos (k * x)
    set B := ∑ k ∈ Finset.range (N + 1), sin (k * x)
    have hcross : A * cos ((N + 1 : ℝ) * x) + B * sin ((N + 1 : ℝ) * x) =
        ∑ n ∈ Finset.range (N + 1), cos ((n + 1) * x) := by
      simp only [A, B, Finset.sum_mul, ← Finset.sum_add_distrib]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [← cos_sub, Nat.cast_sub (by omega), ← cos_neg]
      congr 1; push_cast; ring
    rw [Finset.sum_range_succ (fun k => cos (k * x)), Finset.sum_range_succ (fun k => sin (k * x))]
    push_cast
    have hsc := sin_sq_add_cos_sq ((N + 1 : ℝ) * x)
    have hsum : ∑ n ∈ Finset.range (N + 1), ((N + 1 : ℝ) - n) * cos ((n + 1) * x) =
        ∑ n ∈ Finset.range N, ((N : ℝ) - n) * cos ((n + 1) * x) +
          ∑ n ∈ Finset.range (N + 1), cos ((n + 1) * x) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n : ℕ => cos ((n + 1 : ℝ) * x))]
      have : ∑ n ∈ Finset.range N, ((N + 1 : ℝ) - n) * cos ((n + 1) * x) =
          ∑ n ∈ Finset.range N, ((N : ℝ) - n) * cos ((n + 1) * x) +
            ∑ n ∈ Finset.range N, cos ((n + 1) * x) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => by ring
      rw [this]; ring
    rw [hsum]
    nlinarith [ih, hcross, hsc]

/-- The Fejér kernel `Φ_N(x) = 1 + 2∑_{n=1}^N (1 - n/(N+1)) cos nx` is nonnegative. -/
theorem fejerKernel_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ 1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * x) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have h := fejer_identity N x
  have hrw : 1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * x) =
      ((N + 1 : ℝ) + 2 * ∑ n ∈ Finset.range N, ((N : ℝ) - n) * cos ((n + 1) * x)) / (N + 1) := by
    rw [eq_div_iff hN.ne', add_mul, mul_assoc, Finset.sum_mul, one_mul]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    simp only [fejMult, show n + 1 ≤ N by omega, ite_true]
    field_simp
    push_cast; ring
  rw [hrw, h]
  positivity

/-- The two-variable Fejér kernel `K_N(E,E') = 1 + 2∑ (1 - n/(N+1)) T_n(E/4) T_n(E'/4)`. -/
def fejerKern (N : ℕ) (E E' : ℝ) : ℝ :=
  1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * (cheb (n + 1) E * cheb (n + 1) E')

lemma cheb_four_cos (n : ℕ) (θ : ℝ) : cheb n (4 * cos θ) = cos (n * θ) := by
  rw [cheb_scale]
  have := T_real_cos θ (n : ℤ)
  push_cast at this
  exact this

/-- `K_N ≥ 0` on `[-4,4]²`: `K_N(4cos θ, 4cos φ) = (Φ_N(θ-φ) + Φ_N(θ+φ))/2`. -/
theorem fejerKern_nonneg (N : ℕ) {E E' : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4)
    (hE' : E' ∈ Icc (-4 : ℝ) 4) : 0 ≤ fejerKern N E E' := by
  set θ := arccos (E / 4)
  set φ := arccos (E' / 4)
  have h1 : E = 4 * cos θ := by
    rw [cos_arccos (by linarith [hE.1]) (by linarith [hE.2])]; ring
  have h2 : E' = 4 * cos φ := by
    rw [cos_arccos (by linarith [hE'.1]) (by linarith [hE'.2])]; ring
  have hk : fejerKern N E E' =
      ((1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ - φ))) +
        (1 + 2 * ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ + φ)))) / 2 := by
    have key : ∑ n ∈ Finset.range N, fejMult N (n + 1) * (cos (((n + 1 : ℕ) : ℝ) * θ) *
        cos (((n + 1 : ℕ) : ℝ) * φ)) =
          (∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ - φ)) +
            ∑ n ∈ Finset.range N, fejMult N (n + 1) * cos ((n + 1) * (θ + φ))) / 2 := by
      rw [eq_div_iff two_ne_zero, ← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_sub, mul_add, cos_sub, cos_add]; push_cast; ring
    rw [fejerKern, h1, h2]
    simp_rw [cheb_four_cos]
    rw [key]
    ring
  rw [hk]
  have := fejerKernel_nonneg N (θ - φ)
  have := fejerKernel_nonneg N (θ + φ)
  positivity

/-- `F_N(E) = ∫ K_N(E,E') dμ(E')`. -/
theorem fejer_eq_integral_kern (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ)
    (N : ℕ) (E : ℝ) : fejer μ N E = ∫ E', fejerKern N E E' ∂μ := by
  have hint : ∀ n, Integrable (fun E' => fejMult N (n + 1) * (cheb (n + 1) E * cheb (n + 1) E')) μ :=
    fun n => integrable_of_continuous hμ (by have := continuous_cheb (n + 1); fun_prop)
  unfold fejerKern
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun n _ => hint n).const_mul _),
    integral_const_mul, integral_finsetSum _ fun n _ => hint n]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, fejer]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_const_mul, chebCoeff]
  ring

/-- **Positivity**: `F_N ≥ 0` on `[-4,4]`. -/
theorem fejer_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ)
    {E : ℝ} (hE : E ∈ Icc (-4 : ℝ) 4) : 0 ≤ fejer μ N E := by
  rw [fejer_eq_integral_kern μ hμ]
  exact integral_nonneg_of_ae ((ae_mem_of_carried hμ).mono fun E' hE' => fejerKern_nonneg N hE hE')

/-- `‖F_N‖_{L¹(ρ)} = 1`: the `p = 1` case carries no information. -/
theorem integral_abs_fejer (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CarriedBy4 μ) (N : ℕ) :
    ∫ E, |fejer μ N E| ∂arcsine = 1 := by
  rw [← integral_fejer μ N]
  refine integral_congr_ae (ae_arcsine_mem_Icc.mono fun E hE => ?_)
  exact abs_of_nonneg (fejer_nonneg μ hμ N hE)

end ThomChebyshev
