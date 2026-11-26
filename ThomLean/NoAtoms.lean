import ThomLean.Existence
import ThomLean.Conclusions

/-!
# `μ_A` has no atoms (unconditional)

`muA_no_atoms : ∀ E, μ_A {E} = 0`.

The proof uses only the finite quotients `H₃(ℤ/N)` already used to construct `μ_A`
(`ThomExistence`). No Chebyshev summability target is used.

1. **Unique continuation along rows** (`uniqueCont`). Fix `L ∣ N` and let `S ⊂ H₃(ℤ/N)` be the
   set of points whose first coordinate is `≡ 0` or `≡ -1 (mod L)`; `|S| ≤ 2N³/L`. The eigenvalue
   equation `(A - λ)v = r` read in the `x`-direction is a second-order recurrence between the
   rows `a-1, a, a+1`; the `y`-moves only permute the points of a row. Starting from two
   consecutive zero rows, `L` steps give, for every `v` vanishing on `S`,
   `‖v‖² ≤ L·Dᴸ·‖(A-λ)v‖²` with `D = 3(5λ²+15)`.
2. **Eigenvalue counting** (`card_near_le`). If `L·Dᴸ·h² < 1`, the number of eigenvalues in
   `[λ-h, λ+h]` is at most `|S|`: otherwise a nonzero combination of the corresponding
   eigenvectors vanishes on `S` and violates (1).
3. **Transitivity** (`specMeasure_map_eq`). Left multiplication commutes with the right Schreier
   action, so all vertex spectral measures coincide. Summing over the `N³` vertices,
   `∫ g dσ_N ≤ 2/L` for every `0 ≤ g ≤ 1` supported in `[λ-h, λ+h]`, uniformly in `N`
   (`quot_integral_le`).
4. **Limit** (`muA_no_atoms`). Along `N = L(n+1)` the measures `σ_N` have a cluster point, which
   is `μ_A` by uniqueness of moments; the bound passes to it, so `μ_A{λ} ≤ 2/L` for every `L`.
-/

noncomputable section

namespace ThomNoAtoms

open ThomHeisenberg ThomChebyshev ThomBridge ThomExistence MeasureTheory Matrix Filter Topology Set
open Finset
open scoped BoundedContinuousFunction

/-! ### Generic linear algebra -/

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X] {act : X → Step → X}
  (hrev : ∀ p s, act (act p s) (stepInv s) = p)

lemma eigU_col_orth (j k : X) :
    ∑ p, eigU hrev p j * eigU hrev p k = if j = k then 1 else 0 := by
  have := congrFun (congrFun (star_mul_eigU hrev) j) k
  simp only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] at this
  rw [← this]

lemma eigU_col_sq (j : X) : ∑ p, eigU hrev p j ^ 2 = 1 := by
  simpa [sq] using eigU_col_orth hrev j j

/-- Orthonormality of the eigenvectors: `‖∑_{j∈J} β_j u_j‖² = ∑ β_j²`. -/
lemma sum_sq_comb (J : Finset X) (β : J → ℝ) :
    ∑ p, (∑ j : J, eigU hrev p j * β j) ^ 2 = ∑ j : J, β j ^ 2 := by
  have h : ∀ p, (∑ j : J, eigU hrev p j * β j) ^ 2 =
      ∑ j : J, ∑ k : J, β j * β k * (eigU hrev p j * eigU hrev p k) := by
    intro p
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, eigU_col_orth]
  rw [Finset.sum_eq_single j]
  · simp [sq]
  · intro k _ hk
    have : (j : X) ≠ k := fun h => hk (Subtype.ext h).symm
    simp [this]
  · simp

/-- `A (∑ β_j u_j) = ∑ λ_j β_j u_j`. -/
lemma adj_mulVec_comb (J : Finset X) (β : J → ℝ) (p : X) :
    (adj act *ᵥ fun q => ∑ j : J, eigU hrev q j * β j) p =
      ∑ j : J, eigU hrev p j * ((adj_isHermitian hrev).eigenvalues j * β j) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun (adj_mul_eigU hrev) p) j
  rw [Matrix.mul_apply, mul_diagonal] at this
  calc ∑ q, adj act p q * (eigU hrev q j * β j) = (∑ q, adj act p q * eigU hrev q j) * β j := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => by ring
    _ = _ := by rw [this]; ring

/-- **Eigenvalue counting from unique continuation.** -/
theorem card_near_le (S : Finset X) (lam h K : ℝ) (hK0 : 0 ≤ K) (hK : K * h ^ 2 < 1)
    (huc : ∀ v : X → ℝ, (∀ p ∈ S, v p = 0) →
      ∑ p, v p ^ 2 ≤ K * ∑ p, ((adj act *ᵥ v) p - lam * v p) ^ 2) :
    #{j | |(adj_isHermitian hrev).eigenvalues j - lam| ≤ h} ≤ #S := by
  set ev := (adj_isHermitian hrev).eigenvalues
  set J : Finset X := {j | |ev j - lam| ≤ h} with hJ
  let M : Matrix S J ℝ := fun s j => eigU hrev s j
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    set v : X → ℝ := fun q => ∑ j : J, eigU hrev q j * β j with hv
    have hvS : ∀ p ∈ S, v p = 0 := fun p hp => by
      have := congrFun hβ ⟨p, hp⟩
      rw [Matrix.mulVecLin_apply] at this
      exact this
    have h1 := huc v hvS
    rw [hv, sum_sq_comb hrev J β] at h1
    have hr : ∀ p, (adj act *ᵥ v) p - lam * v p =
        ∑ j : J, eigU hrev p j * ((ev j - lam) * β j) := by
      intro p
      rw [hv, adj_mulVec_comb, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ p, ((adj act *ᵥ v) p - lam * v p) ^ 2 ≤ h ^ 2 * ∑ j : J, β j ^ 2 := by
      simp_rw [hr]
      rw [sum_sq_comb hrev J, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj : |ev j - lam| ≤ h := (Finset.mem_filter.mp j.2).2
      have hsq : (ev j - lam) ^ 2 ≤ h ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hj 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    rw [← hv] at h1
    have hs0 : 0 ≤ ∑ j : J, β j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h3 : ∑ j : J, β j ^ 2 ≤ K * h ^ 2 * ∑ j : J, β j ^ 2 := by
      calc _ ≤ _ := h1
        _ ≤ K * (h ^ 2 * ∑ j : J, β j ^ 2) := mul_le_mul_of_nonneg_left h2 hK0
        _ = _ := by ring
    have h4 : ∑ j : J, β j ^ 2 = 0 := by nlinarith
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (β j))).mp h4 j
      (Finset.mem_univ _)
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- The vertex spectral measure, pushed to `ℝ`. -/
lemma integral_specMeasure_map (p : X) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ E, g E ∂(specMeasure hrev p).map Subtype.val =
      ∑ j, eigU hrev p j ^ 2 * g ((adj_isHermitian hrev).eigenvalues j) := by
  rw [integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable, specMeasure,
    integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def,
      Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure_nnreal

/-- `∑_p σ_p(g) ≤ #{j : |λ_j - λ| ≤ h}` for `0 ≤ g ≤ 1` vanishing off `[λ-h, λ+h]`. -/
theorem sum_integral_le (g : ℝ → ℝ) (hg : Continuous g)
    (hg1 : ∀ x, g x ≤ 1) (lam h : ℝ) (hgh : ∀ x, h < |x - lam| → g x = 0) :
    ∑ p, ∫ E, g E ∂(specMeasure hrev p).map Subtype.val ≤
      #{j | |(adj_isHermitian hrev).eigenvalues j - lam| ≤ h} := by
  simp_rw [integral_specMeasure_map hrev _ g hg]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hj
  · calc ∑ p, eigU hrev p j ^ 2 * g ((adj_isHermitian hrev).eigenvalues j)
          ≤ ∑ p, eigU hrev p j ^ 2 * 1 :=
            Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hg1 _) (sq_nonneg _)
      _ = _ := by simp [eigU_col_sq]
  · rw [hgh _ (lt_of_not_ge hj)]; simp

/-- Probability measures on `[-4,4]` with equal moments have equal images in `ℝ`. -/
lemma map_eq_of_moments (μ ν : Measure S4) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, ∫ E, (E : ℝ) ^ k ∂μ = ∫ E, (E : ℝ) ^ k ∂ν) :
    μ.map Subtype.val = ν.map Subtype.val := by
  have carried : ∀ ρ : Measure S4, CarriedBy4 (ρ.map Subtype.val) := by
    intro ρ
    unfold CarriedBy4
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val ⁻¹' (Icc (-4 : ℝ) 4)ᶜ : Set S4) = ∅ := by ext E; simp
    rw [this, measure_empty]
  have hmom : ∀ (ρ : Measure S4) (k : ℕ),
      ∫ E, E ^ k ∂(ρ.map Subtype.val) = ∫ E, (E : ℝ) ^ k ∂ρ := fun ρ k =>
    integral_map measurable_subtype_coe.aemeasurable (by fun_prop)
  have : IsProbabilityMeasure (μ.map Subtype.val) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (ν.map Subtype.val) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  refine eq_of_integral_cheb_eq (carried μ) (carried ν) fun n => ?_
  rw [chebCoeff_eq_chebOfMoments _ (carried μ) _ (hmom μ),
    chebCoeff_eq_chebOfMoments _ (carried ν) (fun k => ∫ E, (E : ℝ) ^ k ∂μ)
      (fun k => (hmom ν k).trans (h k).symm)]

end Generic

/-! ### Transitivity of the quotient Schreier graph -/

section Transitive

variable {N : ℕ}

/-- Left multiplication in `H₃(ℤ/N)`. -/
def lmul (p q : QPt N) : QPt N := (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

lemma quotAct_lmul (p q : QPt N) (s : Step) :
    quotAct N (lmul p q) s = lmul p (quotAct N q s) := by
  cases s <;> simp only [quotAct, lmul, Prod.mk.injEq] <;> (repeat' constructor) <;> ring

lemma walk_lmul (p q : QPt N) (w : List Step) :
    walk (quotAct N) (lmul p q) w = lmul p (walk (quotAct N) q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons s w ih => rw [walk_cons, walk_cons, quotAct_lmul, ih]

lemma lmul_zero (p : QPt N) : lmul p 0 = p := by
  simp [lmul]

lemma lmul_injective (p : QPt N) : Function.Injective (lmul p) := by
  intro q q' h
  simp only [lmul, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : q.1 = q'.1 := add_left_cancel h1
  have e2 : q.2.1 = q'.2.1 := add_left_cancel h2
  have e3 : q.2.2 = q'.2.2 := by rw [e2] at h3; linear_combination h3
  exact Prod.ext e1 (Prod.ext e2 e3)

variable [NeZero N]

/-- **Vertex transitivity**: closed-walk counts do not depend on the base point. -/
theorem quot_adj_pow_diag (k : ℕ) (p : QPt N) :
    (adj (quotAct N) ^ k) p p = (adj (quotAct N) ^ k) 0 0 := by
  rw [adj_pow_apply, adj_pow_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : walk (quotAct N) p (wordList w) = lmul p (walk (quotAct N) 0 (wordList w)) := by
    rw [← walk_lmul, lmul_zero]
  have h2 : lmul p (walk (quotAct N) 0 (wordList w)) = p ↔ walk (quotAct N) 0 (wordList w) = 0 := by
    conv_lhs => rhs; rw [← lmul_zero p]
    exact (lmul_injective p).eq_iff
  rw [h1]
  exact if_congr h2 rfl rfl

/-- All vertex spectral measures of `H₃(ℤ/N)` coincide. -/
theorem specMeasure_map_eq (p : QPt N) :
    (specMeasure (quotAct_rev N) p).map Subtype.val =
      (specMeasure (quotAct_rev N) 0).map Subtype.val :=
  map_eq_of_moments _ _ fun k => by
    rw [integral_pow_specMeasure, integral_pow_specMeasure, quot_adj_pow_diag]

end Transitive

/-! ### Unique continuation along rows -/

section Rows

variable {N : ℕ} [NeZero N]

lemma sum_step (f : Step → ℝ) : ∑ s, f s = f .R + f .L + f .U + f .D := by
  rw [show (Finset.univ : Finset Step) = {Step.R, Step.L, Step.U, Step.D} from rfl]
  simp [Finset.sum_insert]
  ring

/-- Row energy `e(a) = ∑_{b,c} v(a,b,c)²`. -/
def rowE (v : QPt N → ℝ) (a : ZMod N) : ℝ := ∑ q : ZMod N × ZMod N, v (a, q) ^ 2

lemma rowE_nonneg (v : QPt N → ℝ) (a : ZMod N) : 0 ≤ rowE v a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sum_eq_sum_rowE (v : QPt N → ℝ) : ∑ p, v p ^ 2 = ∑ a, rowE v a :=
  Fintype.sum_prod_type _

/-- The residual `(A - λ)v`. -/
def resid (v : QPt N → ℝ) (lam : ℝ) (p : QPt N) : ℝ := (adj (quotAct N) *ᵥ v) p - lam * v p

lemma sum_shift (f : ZMod N × ZMod N → ℝ) (x y : ZMod N) :
    ∑ q : ZMod N × ZMod N, f (q.1 + x, q.2 + y) = ∑ q, f q :=
  Fintype.sum_equiv (Equiv.addRight (x, y)) _ _ fun _ => rfl

/-- The constant of the row recurrence. -/
def rowC (lam : ℝ) : ℝ := 5 * lam ^ 2 + 15

lemma five_sq (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    (x₁ + x₂ - x₃ - x₄ - x₅) ^ 2 ≤ 5 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₃), sq_nonneg (x₁ + x₄), sq_nonneg (x₁ + x₅),
    sq_nonneg (x₂ + x₃), sq_nonneg (x₂ + x₄), sq_nonneg (x₂ + x₅), sq_nonneg (x₃ - x₄),
    sq_nonneg (x₃ - x₅), sq_nonneg (x₄ - x₅)]

/-- **Row recurrence**: `e(a+1) ≤ C (ρ(a) + e(a) + e(a-1))`, `ρ` the row energy of `(A-λ)v`. -/
theorem rowE_succ_le (v : QPt N → ℝ) (lam : ℝ) (a : ZMod N) :
    rowE v (a + 1) ≤ rowC lam * (rowE (resid v lam) a + rowE v a + rowE v (a - 1)) := by
  have hpt : ∀ q : ZMod N × ZMod N, v (a + 1, q) = resid v lam (a, q) + lam * v (a, q)
      - v (a - 1, q) - v (a, (q.1 + 1, q.2 + a)) - v (a, (q.1 + -1, q.2 + -a)) := by
    intro q
    simp only [resid, adj_mulVec, sum_step, quotAct, ← sub_eq_add_neg]
    ring
  have hsum : rowE v (a + 1) ≤ 5 * (rowE (resid v lam) a + lam ^ 2 * rowE v a + rowE v (a - 1)
      + rowE v a + rowE v a) := by
    calc rowE v (a + 1) ≤ ∑ q : ZMod N × ZMod N, 5 * (resid v lam (a, q) ^ 2
          + (lam * v (a, q)) ^ 2 + v (a - 1, q) ^ 2 + v (a, (q.1 + 1, q.2 + a)) ^ 2
          + v (a, (q.1 + -1, q.2 + -a)) ^ 2) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [hpt q]; exact five_sq _ _ _ _ _
      _ = _ := by
          rw [← Finset.mul_sum]
          simp only [Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum]
          rw [sum_shift (fun q => v (a, q) ^ 2), sum_shift (fun q => v (a, q) ^ 2)]
          rfl
  have h1 := rowE_nonneg (resid v lam) a
  have h2 := rowE_nonneg v a
  have h3 := rowE_nonneg v (a - 1)
  have hl := sq_nonneg lam
  unfold rowC
  nlinarith [mul_nonneg hl h1, mul_nonneg hl h3]

variable (L : ℕ) (hLN : L ∣ N)

/-- Reduction mod `L`. -/
def res : ZMod N →+* ZMod L := ZMod.castHom hLN (ZMod L)

/-- The rows `a ≡ 0` and `a ≡ -1 (mod L)`. -/
def Srows : Finset (QPt N) :=
  ({a | res L hLN a = 0 ∨ res L hLN a = -1} : Finset (ZMod N)) ×ˢ Finset.univ

lemma rowE_eq_zero (v : QPt N → ℝ) (hv : ∀ p ∈ Srows L hLN, v p = 0) (a : ZMod N)
    (ha : res L hLN a = 0 ∨ res L hLN a = -1) : rowE v a = 0 := by
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [hv (a, q) (by simp [Srows, ha])]; simp

/-- The growth factor `D = 3C`. -/
def rowD (lam : ℝ) : ℝ := 3 * rowC lam

lemma one_le_rowD (lam : ℝ) : 1 ≤ rowD lam := by
  unfold rowD rowC; nlinarith [sq_nonneg lam]

/-- **Propagation from two zero rows.** -/
theorem rowE_block (v : QPt N → ℝ) (hv : ∀ p ∈ Srows L hLN, v p = 0) (lam : ℝ) (a₀ : ZMod N)
    (h0 : res L hLN a₀ = 0) (k : ℕ) :
    rowE v (a₀ + k) ≤ rowD lam ^ k * ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i) ∧
      rowE v (a₀ + k - 1) ≤ rowD lam ^ k * ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
    refine ⟨(rowE_eq_zero L hLN v hv a₀ (Or.inl h0)).le,
      (rowE_eq_zero L hLN v hv (a₀ - 1) (Or.inr ?_)).le⟩
    rw [map_sub, h0, map_one, zero_sub]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set P := rowD lam ^ k
    set R := ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i)
    set ρ := rowE (resid v lam) (a₀ + k)
    have hP : 1 ≤ P := one_le_pow₀ (one_le_rowD lam)
    have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => rowE_nonneg _ _
    have hρ : 0 ≤ ρ := rowE_nonneg _ _
    have hC : 0 ≤ rowC lam := by unfold rowC; positivity
    rw [Finset.sum_range_succ, pow_succ]
    have hrec := rowE_succ_le v lam (a₀ + k)
    have e1 : (a₀ + ((k + 1 : ℕ) : ZMod N)) = a₀ + k + 1 := by push_cast; ring
    have e2 : a₀ + (k : ZMod N) + 1 - 1 = a₀ + k := by ring
    rw [e1, e2]
    have hD : rowD lam = 3 * rowC lam := rfl
    constructor
    · calc rowE v (a₀ + k + 1) ≤ rowC lam * (ρ + rowE v (a₀ + k) + rowE v (a₀ + k - 1)) := hrec
        _ ≤ rowC lam * (3 * P * (R + ρ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            nlinarith [mul_nonneg (sub_nonneg.mpr hP) hρ, mul_nonneg (zero_le_one.trans hP) hR]
        _ = P * rowD lam * (R + ρ) := by rw [hD]; ring
    · calc rowE v (a₀ + k) ≤ P * R := ih1
        _ ≤ P * rowD lam * (R + ρ) := by
            have h1 : P * R ≤ P * (R + ρ) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            have h2 : P * (R + ρ) ≤ P * rowD lam * (R + ρ) := by
              rw [mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              nlinarith [one_le_rowD lam]
            linarith

variable [NeZero L]

/-- **Row bound**: every row energy is controlled by the `L` preceding residual rows. -/
theorem rowE_le (v : QPt N → ℝ) (hv : ∀ p ∈ Srows L hLN, v p = 0) (lam : ℝ) (a : ZMod N) :
    rowE v a ≤ rowD lam ^ L * ∑ i ∈ Finset.range L, rowE (resid v lam) (a - 1 - i) := by
  set k := (res L hLN a).val with hk
  set a₀ := a - (k : ZMod N)
  have h0 : res L hLN a₀ = 0 := by
    simp only [a₀, map_sub, map_natCast, hk, ZMod.natCast_zmod_val, sub_self]
  have hkL : k < L := ZMod.val_lt _
  have hb := (rowE_block L hLN v hv lam a₀ h0 k).1
  rw [show a₀ + k = a by simp [a₀]] at hb
  have hsum : ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i) ≤
      ∑ i ∈ Finset.range L, rowE (resid v lam) (a - 1 - i) := by
    rw [← Finset.sum_range_reflect]
    have : ∀ j ∈ Finset.range k, rowE (resid v lam) (a₀ + ((k - 1 - j : ℕ) : ZMod N)) =
        rowE (resid v lam) (a - 1 - j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      simp only [a₀]; push_cast; ring
    rw [Finset.sum_congr rfl this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkL.le)
      fun _ _ _ => rowE_nonneg _ _
  have hD : rowD lam ^ k ≤ rowD lam ^ L := pow_le_pow_right₀ (one_le_rowD lam) hkL.le
  have hs0 : 0 ≤ ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i) :=
    Finset.sum_nonneg fun _ _ => rowE_nonneg _ _
  calc rowE v a ≤ _ := hb
    _ ≤ rowD lam ^ L * ∑ i ∈ Finset.range k, rowE (resid v lam) (a₀ + i) :=
        mul_le_mul_of_nonneg_right hD hs0
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
        (pow_nonneg (zero_le_one.trans (one_le_rowD lam)) _)

/-- **Unique continuation**: `‖v‖² ≤ L·Dᴸ·‖(A-λ)v‖²` for `v` vanishing on the rows
`a ≡ 0, -1 (mod L)`. -/
theorem uniqueCont (v : QPt N → ℝ) (hv : ∀ p ∈ Srows L hLN, v p = 0) (lam : ℝ) :
    ∑ p, v p ^ 2 ≤ (L * rowD lam ^ L) * ∑ p, ((adj (quotAct N) *ᵥ v) p - lam * v p) ^ 2 := by
  rw [sum_eq_sum_rowE, show (fun p => ((adj (quotAct N) *ᵥ v) p - lam * v p) ^ 2) =
    fun p => resid v lam p ^ 2 from rfl, sum_eq_sum_rowE]
  calc ∑ a, rowE v a ≤ ∑ a, rowD lam ^ L * ∑ i ∈ Finset.range L, rowE (resid v lam) (a - 1 - i) :=
        Finset.sum_le_sum fun a _ => rowE_le L hLN v hv lam a
    _ = rowD lam ^ L * ∑ i ∈ Finset.range L, ∑ a, rowE (resid v lam) (a - 1 - i) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = rowD lam ^ L * ∑ _i ∈ Finset.range L, ∑ a, rowE (resid v lam) a := by
        refine congrArg (rowD lam ^ L * ·) (Finset.sum_congr rfl fun i _ => ?_)
        simp_rw [sub_sub]
        exact Fintype.sum_equiv (Equiv.subRight (1 + (i : ZMod N))) _ _ fun _ => rfl
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `|{a : a ≡ t (mod L)}| · L = N`. -/
lemma card_fiber_mul (t : ZMod L) : #{a : ZMod N | res L hLN a = t} * L = N := by
  have heq : ∀ t' : ZMod L, #{a : ZMod N | res L hLN a = t'} = #{a : ZMod N | res L hLN a = t} :=
    fun t' => AddMonoidHom.card_fiber_eq_of_mem_range (res L hLN)
      (ZMod.castHom_surjective hLN t') (ZMod.castHom_surjective hLN t)
  have hsum := Finset.card_eq_sum_card_fiberwise (f := res L hLN) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc #{a : ZMod N | res L hLN a = t} * L = ∑ t' : ZMod L, #{a : ZMod N | res L hLN a = t'} := by
        rw [Finset.sum_congr rfl fun t' _ => heq t', Finset.sum_const, Finset.card_univ,
          ZMod.card, smul_eq_mul, mul_comm]
    _ = #(Finset.univ : Finset (ZMod N)) := hsum.symm
    _ = N := by rw [Finset.card_univ, ZMod.card]

lemma card_Srows_le : #(Srows L hLN) * L ≤ 2 * N ^ 3 := by
  rw [Srows, Finset.card_product, Finset.card_univ, Fintype.card_prod, ZMod.card, Finset.filter_or]
  set F0 : Finset (ZMod N) := {a | res L hLN a = 0}
  set F1 : Finset (ZMod N) := {a | res L hLN a = -1}
  have h := Finset.card_union_le F0 F1
  have h0 : #F0 * L = N := card_fiber_mul L hLN 0
  have h1 : #F1 * L = N := card_fiber_mul L hLN (-1)
  calc #(F0 ∪ F1) * (N * N) * L = #(F0 ∪ F1) * L * (N * N) := by ring
    _ ≤ (#F0 + #F1) * L * (N * N) := by gcongr
    _ = 2 * N ^ 3 := by rw [add_mul, h0, h1]; ring

end Rows

/-! ### Uniform bound on the finite quotients and passage to the limit -/

section Limit

/-- Half-width of the window at level `L`: `h_L = 1/(L·Dᴸ)`. -/
def width (L : ℕ) (lam : ℝ) : ℝ := 1 / (L * rowD lam ^ L)

lemma width_pos (L : ℕ) (hL : 0 < L) (lam : ℝ) : 0 < width L lam :=
  div_pos one_pos (mul_pos (Nat.cast_pos.mpr hL) (pow_pos (by linarith [one_le_rowD lam]) _))

/-- **Uniform window bound on `H₃(ℤ/N)`**: if `L ∣ N` and `g ≤ 1` vanishes off
`[λ - h_L, λ + h_L]`, then `∫ g dσ_N ≤ 2/L`, for every `N`. -/
theorem quot_integral_le {N : ℕ} [NeZero N] (L : ℕ) [NeZero L] (hLN : L ∣ N) (lam : ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ x, g x ≤ 1)
    (hgh : ∀ x, width L lam < |x - lam| → g x = 0) :
    ∫ E, g E ∂(specMeasure (quotAct_rev N) 0).map Subtype.val ≤ 2 / L := by
  set K : ℝ := L * rowD lam ^ L with hKdef
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hK1 : 1 < K := by
    have : 1 < rowD lam ^ L :=
      one_lt_pow₀ (by unfold rowD rowC; nlinarith [sq_nonneg lam]) (NeZero.ne L)
    nlinarith
  have hK0 : 0 < K := by linarith
  have hKh : K * width L lam ^ 2 < 1 := by
    have : K * width L lam ^ 2 = 1 / K := by
      rw [width, ← hKdef]; field_simp
    rw [this]; exact (div_lt_one hK0).mpr hK1
  have hcard := card_near_le (quotAct_rev N) (Srows L hLN) lam (width L lam) K hK0.le hKh
    (fun v hv => uniqueCont L hLN v hv lam)
  have hsum := sum_integral_le (quotAct_rev N) g hg hg1 lam (width L lam) hgh
  rw [Finset.sum_congr rfl fun p _ => by rw [specMeasure_map_eq p], Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  have hcardX : (Fintype.card (QPt N) : ℝ) = (N : ℝ) ^ 3 := by
    simp [Fintype.card_prod, ZMod.card]; ring
  rw [hcardX] at hsum
  have hS : (#(Srows L hLN) : ℝ) * L ≤ 2 * (N : ℝ) ^ 3 := by
    exact_mod_cast card_Srows_le L hLN
  have hJ : (#{j | |(adj_isHermitian (quotAct_rev N)).eigenvalues j - lam| ≤ width L lam} : ℝ)
      ≤ #(Srows L hLN) := by exact_mod_cast hcard
  have hN : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  rw [le_div_iff₀ (by linarith)]
  set I := ∫ E, g E ∂(specMeasure (quotAct_rev N) 0).map Subtype.val
  have : (N : ℝ) ^ 3 * (I * L) ≤ (N : ℝ) ^ 3 * 2 := by nlinarith
  exact le_of_mul_le_mul_left this hN

/-- A bound valid along a sequence passes to its cluster points. -/
lemma integral_le_of_mapClusterPt (u : ℕ → ProbabilityMeasure S4) (ν : ProbabilityMeasure S4)
    (hν : MapClusterPt ν atTop u) (f : S4 →ᵇ ℝ) (c : ℝ)
    (hc : ∀ n, ∫ E, f E ∂(u n : Measure S4) ≤ c) : ∫ E, f E ∂(ν : Measure S4) ≤ c := by
  have hcont := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have h1 := hν.continuousAt_comp hcont.continuousAt
  have h2 := ClusterPt.mem_closure_of_mem h1 (Iic c) (by
    rw [Filter.mem_map]; exact Filter.Eventually.of_forall fun n => hc n)
  rwa [closure_Iic] at h2

/-- Cluster points of `σ_{s(n)}` (with `s(n) → ∞`) are `μ_A`. -/
theorem map_eq_muA_of_mapClusterPt (s : ℕ → ℕ) (hs : ∀ n, n ≤ s n) (ν : ProbabilityMeasure S4)
    (hν : MapClusterPt ν atTop (fun n => quotMeasure (s n))) :
    (ν : Measure S4).map Subtype.val = muA := by
  have hmom : ∀ k : ℕ, ∫ E, (E : ℝ) ^ k ∂(ν : Measure S4) = moment k := by
    intro k
    let f : S4 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun E => (E : ℝ) ^ k, by fun_prop⟩
    have hf : ∀ E : S4, f E = (E : ℝ) ^ k := fun E => rfl
    have hc := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
    have h1 := hν.continuousAt_comp hc.continuousAt
    have hev : ∀ᶠ n in atTop,
        ((fun μ : ProbabilityMeasure S4 => ∫ E, f E ∂(μ : Measure S4)) ∘
          (fun n => quotMeasure (s n))) n = (moment k : ℝ) := by
      refine eventually_atTop.2 ⟨(k + 1) ^ 2, fun n hn => ?_⟩
      simp only [Function.comp_apply, hf]
      exact integral_pow_quotMeasure (s n) k (by have := hs n; omega)
    simp only [hf] at h1 hev
    by_contra hne
    have hU : ({(moment k : ℝ)}ᶜ : Set ℝ) ∈ 𝓝 (∫ E, (E : ℝ) ^ k ∂(ν : Measure S4)) :=
      isOpen_compl_singleton.mem_nhds hne
    obtain ⟨n, hn1, hn2⟩ := ((mapClusterPt_iff_frequently.mp h1) _ hU).and_eventually hev |>.exists
    exact hn1 hn2
  rw [← isSpectralMeasureA_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr
      inferInstance
  · unfold CarriedBy4
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val ⁻¹' (Icc (-4 : ℝ) 4)ᶜ : Set S4) = ∅ := by ext E; simp
    rw [this, measure_empty]
  · intro k
    rw [integral_map measurable_subtype_coe.aemeasurable (by fun_prop)]
    exact hmom k

/-- The tent function of half-width `h` centred at `E`. -/
def tent (E h x : ℝ) : ℝ := max 0 (1 - |x - E| / h)

lemma continuous_tent (E h : ℝ) : Continuous (tent E h) :=
  continuous_const.max (continuous_const.sub
    ((continuous_id.sub continuous_const).abs.div_const h))

/-- **Window bound for `μ_A`**: `∫ tent_{E,h_L} dμ_A ≤ 2/L`. -/
theorem muA_tent_le (E : ℝ) (L : ℕ) (hL : 0 < L) : ∫ x, tent E (width L E) x ∂muA ≤ 2 / L := by
  have : NeZero L := ⟨hL.ne'⟩
  set h := width L E
  have hh : 0 < h := width_pos L hL E
  set g : ℝ → ℝ := tent E h with hgdef
  have hg : Continuous g := continuous_tent E h
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_max_left _ _
  have hg1 : ∀ x, g x ≤ 1 := fun x =>
    max_le zero_le_one (by have := div_nonneg (abs_nonneg (x - E)) hh.le; linarith)
  have hgh : ∀ x, h < |x - E| → g x = 0 := fun x hx => by
    apply max_eq_left
    have : 1 < |x - E| / h := (one_lt_div hh).mpr hx
    linarith
  set s : ℕ → ℕ := fun n => L * (n + 1) - 1 with hsdef
  have hs1 : ∀ n, s n + 1 = L * (n + 1) := fun n =>
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hL.ne' n.succ_ne_zero))
  have hs : ∀ n, n ≤ s n := fun n => by
    have h1 := hs1 n
    have h2 : n + 1 ≤ L * (n + 1) := Nat.le_mul_of_pos_left _ hL
    omega
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (map (fun n => quotMeasure (s n)) atTop)
  have hν' : MapClusterPt ν atTop (fun n => quotMeasure (s n)) := hν
  let f : S4 →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => g x, hg.comp continuous_subtype_val⟩
  have hbound : ∀ n, ∫ x, f x ∂(quotMeasure (s n) : Measure S4) ≤ 2 / L := by
    intro n
    have hdvd : L ∣ s n + 1 := ⟨n + 1, hs1 n⟩
    have := quot_integral_le (N := s n + 1) L hdvd E g hg hg1 hgh
    rw [integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable] at this
    exact this
  have hν2 := integral_le_of_mapClusterPt _ ν hν' f _ hbound
  have hmu := map_eq_muA_of_mapClusterPt s hs ν hν'
  rw [← hmu, integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
  exact hν2

/-- **Quantitative atom bound**: `μ_A{E} ≤ 2/L` for every `L ≥ 1`. -/
theorem muA_singleton_le (E : ℝ) (L : ℕ) (hL : 0 < L) : muA.real {E} ≤ 2 / L := by
  have hprob := isSpectralMeasureA_muA.isProb
  have hg := continuous_tent E (width L E)
  calc muA.real {E} = ∫ x, ({E} : Set ℝ).indicator 1 x ∂muA :=
        (integral_indicator_one (measurableSet_singleton E)).symm
    _ ≤ ∫ x, tent E (width L E) x ∂muA := by
        refine integral_mono ((integrable_indicator_iff (measurableSet_singleton E)).mpr
          (integrableOn_const (measure_ne_top _ _)))
          (integrable_of_continuous isSpectralMeasureA_muA.carried hg) fun x => ?_
        by_cases hx : x = E
        · subst hx; simp [tent]
        · simp [hx, tent]
    _ ≤ _ := muA_tent_le E L hL

/-- **Modulus of continuity**: `μ_A([E - h_L/2, E + h_L/2]) ≤ 4/L`, `h_L = 1/(L·Dᴸ)`. Since
`h_L ≥ e^{-cL}` (for `E` in a bounded set), this is `μ_A(I) ≲ 1/log(1/|I|)`. -/
theorem muA_Icc_le (E : ℝ) (L : ℕ) (hL : 0 < L) :
    muA.real (Icc (E - width L E / 2) (E + width L E / 2)) ≤ 4 / L := by
  have hprob := isSpectralMeasureA_muA.isProb
  set h := width L E
  have hh : 0 < h := width_pos L hL E
  have hg := continuous_tent E h
  have hint := integrable_of_continuous isSpectralMeasureA_muA.carried hg
  calc muA.real (Icc (E - h / 2) (E + h / 2))
      = ∫ x, (Icc (E - h / 2) (E + h / 2)).indicator 1 x ∂muA :=
        (integral_indicator_one measurableSet_Icc).symm
    _ ≤ ∫ x, 2 * tent E h x ∂muA := by
        refine integral_mono ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (measure_ne_top _ _))) (hint.const_mul 2) fun x => ?_
        by_cases hx : x ∈ Icc (E - h / 2) (E + h / 2)
        · rw [indicator_of_mem hx]
          have habs : |x - E| ≤ h / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have : |x - E| / h ≤ 1 / 2 := by rw [div_le_iff₀ hh]; linarith
          simp only [Pi.one_apply, tent]
          have := le_max_right 0 (1 - |x - E| / h)
          linarith
        · rw [indicator_of_notMem hx]
          exact mul_nonneg zero_le_two (le_max_left _ _)
    _ = 2 * ∫ x, tent E h x ∂muA := integral_const_mul _ _
    _ ≤ 2 * (2 / L) := by linarith [muA_tent_le E L hL]
    _ = 4 / L := by ring

/-- **`μ_A` has no atoms** (unconditional). -/
theorem muA_no_atoms (E : ℝ) : muA {E} = 0 := by
  have hprob := isSpectralMeasureA_muA.isProb
  have h0 : muA.real {E} ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨L, hL⟩ := exists_nat_gt (2 / muA.real {E})
    have hLpos : (0 : ℝ) < L := lt_trans (by positivity) hL
    have hL0 : 0 < L := by exact_mod_cast hLpos
    have h1 := muA_singleton_le E L hL0
    have h2 : 2 / (L : ℝ) < muA.real {E} := by
      rw [div_lt_iff₀ hLpos]
      rw [div_lt_iff₀ hpos] at hL
      linarith
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top muA {E})).mp (le_antisymm h0 measureReal_nonneg)

instance : MeasureTheory.NullSingletonClass muA := ⟨muA_no_atoms⟩

/-- Countable sets are `μ_A`-null. -/
theorem muA_countable {s : Set ℝ} (hs : s.Countable) : muA s = 0 := hs.measure_zero muA

end Limit

/-! ### Consequences for the earlier conditional statements -/

open ThomConclusions in
/-- The no-atom target of `ThomConclusions` holds: the Cesàro means of
`(-1)^j τ(T_{2j}(A/4))` tend to `0`. -/
theorem noAtomTarget : NoAtomTarget := noAtomTarget_iff.mpr (muA_no_atoms 0)

open ThomConclusions in
/-- **The weighted target alone now gives absolute continuity.** -/
theorem muA_ac_of_weightedTarget (h : WeightedTarget) : muA ≪ volume :=
  muA_ac_of_weighted h noAtomTarget

end ThomNoAtoms
