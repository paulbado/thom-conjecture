import ThomLean.NoAtoms

/-!
# Counting eigenvalues near `0` with complex quasimodes

Let `A` be the (real symmetric) adjacency matrix of a reversible step action on a finite set
`X`, and let `(F_i)_{i ∈ S}` be complex vectors such that

* the `F_i` are pairwise orthogonal, and so are the `A F_i`;
* `‖A F_i‖² ≤ ε² ‖F_i‖²` with `ε² < h²`, and `F_i ≠ 0`.

Then at least `#S` eigenvalues of `A` lie in `[-h, h]` (`card_le_of_quasimodes`).

Proof: otherwise a nonzero combination `v = ∑ β_i F_i` is orthogonal to all eigenvectors with
`|λ| ≤ h`; Parseval in the real orthonormal eigenbasis gives `‖A v‖² ≥ h²‖v‖²`, while the two
orthogonality relations give `‖A v‖² ≤ ε²‖v‖²`.

For the Heisenberg quotient `H₃(ℤ/N)` the vertex spectral measure of `[-h,h]` is exactly
`#{j : |λ_j| ≤ h} / N³` (`quotMeasure_real_Icc`), by vertex transitivity.
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomExistence ThomNoAtoms MeasureTheory Matrix Set ComplexConjugate
open Finset

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Hermitian inner product on `X → ℂ`. -/
def ip (u v : X → ℂ) : ℂ := ∑ p, conj (u p) * v p

/-- Squared norm on `X → ℂ`. -/
def nrm (u : X → ℂ) : ℝ := ∑ p, Complex.normSq (u p)

lemma nrm_nonneg (u : X → ℂ) : 0 ≤ nrm u := Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _

lemma ip_self (u : X → ℂ) : ip u u = (nrm u : ℂ) := by
  simp [ip, nrm, Complex.normSq_eq_conj_mul_self]

/-- Pythagoras for an orthogonal family. -/
lemma nrm_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → ℂ) (F : ι → X → ℂ)
    (ho : ∀ i k, i ≠ k → ip (F i) (F k) = 0) :
    nrm (fun p => ∑ i, β i * F i p) = ∑ i, Complex.normSq (β i) * nrm (F i) := by
  apply Complex.ofReal_injective
  rw [← ip_self]
  push_cast
  have h1 : ip (fun p => ∑ i, β i * F i p) (fun p => ∑ i, β i * F i p) =
      ∑ i, ∑ k, conj (β i) * β k * ip (F i) (F k) := by
    simp only [ip, map_sum, map_mul]
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [ho i k (Ne.symm hk), mul_zero]) (by simp),
    ip_self, Complex.normSq_eq_conj_mul_self]

variable {act : X → Step → X} (hrev : ∀ p s, act (act p s) (stepInv s) = p)

/-- The adjacency operator on complex vectors. -/
def cAdj (act : X → Step → X) (v : X → ℂ) (p : X) : ℂ := ∑ s : Step, v (act p s)

lemma cAdj_eq (v : X → ℂ) (p : X) : cAdj act v p = ∑ q, (adj act p q : ℂ) * v q := by
  simp only [cAdj, adj]
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_ite_eq]; simp

lemma cAdj_sum {ι : Type*} [Fintype ι] (β : ι → ℂ) (F : ι → X → ℂ) :
    cAdj act (fun p => ∑ i, β i * F i p) = fun p => ∑ i, β i * cAdj act (F i) p := by
  funext p
  simp only [cAdj, Finset.mul_sum]
  exact Finset.sum_comm

lemma eigU_row_orth (p q : X) :
    ∑ j, eigU hrev p j * eigU hrev q j = if p = q then 1 else 0 := by
  have := congrFun (congrFun (eigU_mul_star hrev) p) q
  simp only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] at this
  rw [← this]

/-- Real Parseval identity for the orthogonal matrix of eigenvectors. -/
lemma parseval_real (a : X → ℝ) : ∑ j, (∑ p, eigU hrev p j * a p) ^ 2 = ∑ p, a p ^ 2 := by
  have h : ∀ j, (∑ p, eigU hrev p j * a p) ^ 2 =
      ∑ p, ∑ q, a p * a q * (eigU hrev p j * eigU hrev q j) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, eigU_row_orth]
  simp [sq]

/-- Coordinates of a complex vector in the real eigenbasis. -/
def coef (v : X → ℂ) (j : X) : ℂ := ∑ p, (eigU hrev p j : ℂ) * v p

/-- **Parseval**: `∑_j |⟨u_j, v⟩|² = ‖v‖²`. -/
lemma parseval (v : X → ℂ) : ∑ j, Complex.normSq (coef hrev v j) = nrm v := by
  have hre : ∀ j, (coef hrev v j).re = ∑ p, eigU hrev p j * (v p).re := by
    intro j; simp [coef, Complex.re_sum, Complex.re_ofReal_mul]
  have him : ∀ j, (coef hrev v j).im = ∑ p, eigU hrev p j * (v p).im := by
    intro j; simp [coef, Complex.im_sum, Complex.im_ofReal_mul]
  simp only [Complex.normSq_apply, ← sq, hre, him, Finset.sum_add_distrib, parseval_real, nrm]

include hrev in
lemma adj_comm (p q : X) : adj act p q = adj act q p := by
  have := congrFun (congrFun (adj_symm hrev) q) p
  rwa [transpose_apply] at this

/-- `⟨u_j, A v⟩ = λ_j ⟨u_j, v⟩`. -/
lemma coef_cAdj (v : X → ℂ) (j : X) :
    coef hrev (cAdj act v) j = (adj_isHermitian hrev).eigenvalues j * coef hrev v j := by
  have key : ∀ q, ∑ p, adj act p q * eigU hrev p j =
      eigU hrev q j * (adj_isHermitian hrev).eigenvalues j := by
    intro q
    have := congrFun (congrFun (adj_mul_eigU hrev) q) j
    rw [Matrix.mul_apply, mul_diagonal] at this
    rw [← this]
    exact Finset.sum_congr rfl fun p _ => by rw [adj_comm hrev p q]
  simp only [coef, cAdj_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (key q)
  push_cast at hk
  calc ∑ p, (eigU hrev p j : ℂ) * ((adj act p q : ℂ) * v q)
      = (∑ p, (adj act p q : ℂ) * (eigU hrev p j : ℂ)) * v q := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun p _ => by ring
    _ = _ := by rw [hk]; ring

/-- **Eigenvalue counting from orthogonal complex quasimodes.** -/
theorem card_le_of_quasimodes {ι : Type*} [DecidableEq ι] (S : Finset ι) (F : ι → X → ℂ)
    {h ε2 : ℝ} (hh : 0 ≤ h) (hε : ε2 < h ^ 2)
    (hF : ∀ i ∈ S, 0 < nrm (F i))
    (hq : ∀ i ∈ S, nrm (cAdj act (F i)) ≤ ε2 * nrm (F i))
    (ho : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ip (F i) (F k) = 0)
    (hoA : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ip (cAdj act (F i)) (cAdj act (F k)) = 0) :
    #S ≤ #{j | |(adj_isHermitian hrev).eigenvalues j| ≤ h} := by
  set ev := (adj_isHermitian hrev).eigenvalues
  set J : Finset X := {j | |ev j| ≤ h} with hJ
  let G : S → X → ℂ := fun i => F i
  let M : Matrix J S ℂ := fun j i => coef hrev (G i) j
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    set v : X → ℂ := fun p => ∑ i, β i * G i p with hv
    have hcoef : ∀ j, coef hrev v j = ∑ i, β i * coef hrev (G i) j := by
      intro j
      simp only [coef, hv, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
    have hJ0 : ∀ j ∈ J, coef hrev v j = 0 := by
      intro j hj
      have := congrFun hβ ⟨j, hj⟩
      rw [Matrix.mulVecLin_apply] at this
      simp only [mulVec, dotProduct, M, Pi.zero_apply] at this
      rw [hcoef]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hoG : ∀ i k : S, i ≠ k → ip (G i) (G k) = 0 :=
      fun i k hik => ho i i.2 k k.2 fun h => hik (Subtype.ext h)
    have hoAG : ∀ i k : S, i ≠ k → ip (cAdj act (G i)) (cAdj act (G k)) = 0 :=
      fun i k hik => hoA i i.2 k k.2 fun h => hik (Subtype.ext h)
    have hnv : nrm v = ∑ i, Complex.normSq (β i) * nrm (G i) := nrm_sum β G hoG
    have hnAv : nrm (cAdj act v) = ∑ i, Complex.normSq (β i) * nrm (cAdj act (G i)) := by
      rw [hv, cAdj_sum]; exact nrm_sum β _ hoAG
    -- upper bound
    have hup : nrm (cAdj act v) ≤ ε2 * nrm v := by
      rw [hnAv, hnv, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      calc Complex.normSq (β i) * nrm (cAdj act (G i))
          ≤ Complex.normSq (β i) * (ε2 * nrm (G i)) :=
            mul_le_mul_of_nonneg_left (hq i i.2) (Complex.normSq_nonneg _)
        _ = _ := by ring
    -- lower bound
    have hlow : h ^ 2 * nrm v ≤ nrm (cAdj act v) := by
      rw [← parseval hrev v, ← parseval hrev (cAdj act v), Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [coef_cAdj, Complex.normSq_mul, Complex.normSq_ofReal]
      by_cases hj : j ∈ J
      · rw [hJ0 j hj]; simp
      · have hj' : h < |ev j| := by
          rw [hJ, Finset.mem_filter] at hj; push Not at hj; exact hj (Finset.mem_univ _)
        have : h ^ 2 ≤ ev j * ev j := by
          have h2 := pow_le_pow_left₀ hh hj'.le 2
          rw [sq_abs] at h2; nlinarith
        exact mul_le_mul_of_nonneg_right this (Complex.normSq_nonneg _)
    have hv0 : nrm v = 0 := by
      have := nrm_nonneg v
      nlinarith
    rw [hnv] at hv0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Complex.normSq_nonneg (β i)) (nrm_nonneg (G i)))).mp hv0 i (Finset.mem_univ _)
    have hGi : 0 < nrm (G i) := hF i i.2
    have : Complex.normSq (β i) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hGi.ne'
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- The vertex spectral measure of a measurable set. -/
lemma specMeasure_real (p : X) {C : Set ℝ} (hC : MeasurableSet C) :
    ((specMeasure hrev p).map Subtype.val).real C =
      ∑ j, eigU hrev p j ^ 2 * C.indicator 1 ((adj_isHermitian hrev).eigenvalues j) := by
  have hg : Measurable (C.indicator (1 : ℝ → ℝ)) := measurable_one.indicator hC
  rw [← integral_indicator_one hC, integral_map measurable_subtype_coe.aemeasurable
    hg.aestronglyMeasurable, specMeasure, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def,
      Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure_nnreal

end Generic

/-! ### The Heisenberg quotient -/

/-- **Spectral mass of `[-h,h]`** for `H₃(ℤ/N)`, `N = n+1`: `σ_N([-h,h]) · N³ = #{|λ_j| ≤ h}`. -/
theorem quotMeasure_real_Icc (n : ℕ) (h : ℝ) :
    (((quotMeasure n : Measure S4)).map Subtype.val).real (Icc (-h) h) * ((n : ℝ) + 1) ^ 3 =
      #{j | |(adj_isHermitian (quotAct_rev (n + 1))).eigenvalues j| ≤ h} := by
  set hrev := quotAct_rev (n + 1)
  set ev := (adj_isHermitian hrev).eigenvalues
  have hall : ∀ p : QPt (n + 1), ((specMeasure hrev p).map Subtype.val).real (Icc (-h) h) =
      ((quotMeasure n : Measure S4).map Subtype.val).real (Icc (-h) h) := by
    intro p
    show _ = ((specMeasure hrev 0).map Subtype.val).real (Icc (-h) h)
    rw [specMeasure_map_eq]
  have hsum : ∑ p : QPt (n + 1), ((specMeasure hrev p).map Subtype.val).real (Icc (-h) h) =
      #{j | |ev j| ≤ h} := by
    simp_rw [specMeasure_real hrev _ measurableSet_Icc]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hmem : ev j ∈ Icc (-h) h ↔ |ev j| ≤ h := abs_le.symm
    by_cases hj : |ev j| ≤ h
    · rw [Set.indicator_of_mem (hmem.mpr hj)]
      simp only [Pi.one_apply, mul_one]
      rw [eigU_col_sq]; simp [hj]
    · rw [Set.indicator_of_notMem (fun h' => hj (hmem.mp h'))]
      simp [hj]
  rw [← hsum]
  simp_rw [hall]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [QPt, Fintype.card_prod, ZMod.card]
  push_cast; ring

end ThomZeroLevel
