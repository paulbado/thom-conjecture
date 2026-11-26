import ThomLean.Existence
import ThomLean.Chebyshev.Fejer
import ThomLean.Chebyshev.Entropy
import ThomLean.WeightedL2

/-!
# Round 8, Task 6: the Dirichlet strip model, its exact moments, the two-scale identity

The Dirichlet model of round 7 averages the `L × L` Jacobi matrices
`H_L(α,θ)` (off-diagonal `1`, diagonal `2cos 2π(θ + jα)`) over `(α, θ)`. Over the grid
`α, θ ∈ (1/N)ℤ/ℤ`, this average is the averaged vertex spectral measure of a finite graph.
That graph is the **strip graph** `[0,L) × ℤ/N × ℤ/N` of `H₃`: right multiplication by
`x^{±1}, y^{±1}`, where an `x`-step leaving `[0,L)` is deleted (Dirichlet walls), and
`(j,b,c)·y^{±1} = (j, b±1, c±j)`. Fourier transform in `(b,c)` reduces it to the `H_L(α,θ)`;
that reduction is a paper fact and is not formalized here. Everything below concerns the strip
graph itself and is proved.

* `specM`: the spectral measure of a real symmetric matrix at a vertex, with moments
  `(Mᵏ)_{pp}` (generic; the round-3 construction without a group action).
* `sMat_pow_apply`: powers of the strip adjacency matrix count words whose walk stays in the
  strip.
* `stripMeasure W N`: `σ_{W,N} = W⁻¹ ∑_{j<W} σ_{(j,0,0)}`, a probability measure on `[-4,4]`.
* `stripMoment_formula` (**exact Dirichlet moment formula**): for `k ≤ 2W` and `(k+1)² ≤ N`,
  `W · ∫ Eᵏ dσ_{W,N} = W·τ(Aᵏ) − b_k`. Here `b_k = ∑_{w} width(w)` sums over the zero-area
  closed walks of length `k`, so `b_k` does not depend on `W` or `N`. Also `2·b_k ≤ k·τ(Aᵏ)`.
* `two_scale_moment`, `two_scale_poly`: `∫ P dμ_A = 2∫ P dσ_{2W,N} − ∫ P dσ_{W,N}` for
  `deg P ≤ 2W`, `(4W+1)² ≤ N`.
* `fejer_two_scale`, `fejer_dom`: `F_n^{μ_A} = 2F_n^{σ_{2W}} − F_n^{σ_W}`, and
  `0 ≤ F_n^{μ_A} ≤ 2F_n^{σ_{2W}}` on `[-4,4]`, for `n ≤ 2W`.
* `fejEnt_two_scale_le`: `H_n(μ_A) ≤ 2 H_n(σ_{2W,N}) + 2 log 2 + 1` (Fejér entropies, `n ≤ 2W`).
  `fejerEntropyTarget_of_strip`: a uniform bound on the strip entropies `H_n(σ_{2n+2,N_n})`
  implies `FejerEntropyTarget`, hence `μ_A ≪ dE`. **The strip bound is not proved.**
-/

noncomputable section

namespace ThomStrip

open ThomHeisenberg ThomExistence ThomBridge ThomChebyshev MeasureTheory Matrix Set
open Polynomial Polynomial.Chebyshev

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ### Spectral measures of a real symmetric matrix -/

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X] {M : Matrix X X ℝ} (hM : M.IsHermitian)

/-- Eigenvector unitary, as a real matrix. -/
def eU : Matrix X X ℝ := (hM.eigenvectorUnitary : Matrix X X ℝ)

lemma eU_mul_star : eU hM * (eU hM)ᵀ = 1 := by
  have := mem_unitaryGroup_iff.mp (hM.eigenvectorUnitary).2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this

lemma M_mul_eU : M * eU hM = eU hM * diagonal hM.eigenvalues := by
  ext i j
  rw [mul_diagonal]
  have h := congrFun (hM.mulVec_eigenvectorBasis j) i
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [eU, IsHermitian.eigenvectorUnitary_apply, mul_comm, ← h, Matrix.mul_apply]
  simp only [mulVec, dotProduct]
  rfl

theorem M_pow_diag (k : ℕ) (p : X) :
    (M ^ k) p p = ∑ j, eU hM p j ^ 2 * hM.eigenvalues j ^ k := by
  set U := eU hM
  set ev := hM.eigenvalues
  have hk : M ^ k * U = U * diagonal ev ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, M_mul_eU, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have : M ^ k = U * diagonal ev ^ k * Uᵀ := by
    rw [← hk, mul_assoc, eU_mul_star, mul_one]
  rw [this, diagonal_pow, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, transpose_apply]
  simp only [Pi.pow_apply]; ring

lemma sum_eU_sq (p : X) : ∑ j, eU hM p j ^ 2 = 1 := by
  have := congrFun (congrFun (eU_mul_star hM) p) p
  rw [Matrix.mul_apply, one_apply_eq] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [transpose_apply]; ring

/-- The spectral measure of `M` at the vertex `p`. -/
def specM (p : X) : Measure ℝ :=
  ∑ j, (Real.toNNReal (eU hM p j ^ 2)) • Measure.dirac (hM.eigenvalues j)

instance (p : X) : IsProbabilityMeasure (specM hM p) := by
  constructor
  simp only [specM, FunLike.coe_sum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, ← Real.toNNReal_sum_of_nonneg (fun j _ => sq_nonneg _),
    sum_eU_sq]
  simp

theorem integral_pow_specM (k : ℕ) (p : X) : ∫ E, E ^ k ∂specM hM p = (M ^ k) p p := by
  rw [M_pow_diag hM, specM, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def,
      Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure_nnreal

theorem carried_specM (hb : ∀ j, |hM.eigenvalues j| ≤ 4) (p : X) : CarriedBy4 (specM hM p) := by
  unfold CarriedBy4
  simp only [specM, FunLike.coe_sum, Finset.sum_apply, Measure.smul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply' _ (measurableSet_Icc.compl), Set.indicator_of_notMem]
  · simp
  · simpa using abs_le.1 (hb j)

end Generic

/-! ### The strip graph -/

/-- Vertices `[0,W) × ℤ/N × ℤ/N`. -/
abbrev SPt (W N : ℕ) := Fin W × ZMod N × ZMod N

variable {W N : ℕ}

/-- Steps in the strip; an `x`-step leaving `[0,W)` is deleted. -/
def sStep (p : SPt W N) : Step → Option (SPt W N)
  | .R => if h : p.1.val + 1 < W then some (⟨p.1.val + 1, h⟩, p.2) else none
  | .L => if h : 0 < p.1.val then some (⟨p.1.val - 1, by omega⟩, p.2) else none
  | .U => some (p.1, p.2.1 + 1, p.2.2 + (p.1.val : ZMod N))
  | .D => some (p.1, p.2.1 - 1, p.2.2 - (p.1.val : ZMod N))

lemma sStep_rev (p q : SPt W N) (s : Step) : sStep p s = some q ↔ sStep q (stepInv s) = some p := by
  obtain ⟨⟨a, ha⟩, b, c⟩ := p
  obtain ⟨⟨a', ha'⟩, b', c'⟩ := q
  cases s <;> simp only [sStep, stepInv] <;> (try split_ifs) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, false_iff, iff_false] <;>
    first
    | (constructor <;> rintro ⟨h1, h2, h3⟩ <;> subst_vars <;> exact ⟨by omega, by ring, by ring⟩)
    | (rintro ⟨h1, -, -⟩; omega)

variable [NeZero N]

/-- Adjacency matrix of the strip graph. -/
def sMat (W N : ℕ) : Matrix (SPt W N) (SPt W N) ℝ :=
  fun p q => ∑ s : Step, if sStep p s = some q then 1 else 0

lemma stepInv_bij : Function.Bijective stepInv :=
  Function.Involutive.bijective stepInv_stepInv

lemma sMat_symm : (sMat W N)ᵀ = sMat W N := by
  ext p q
  simp only [transpose_apply, sMat]
  rw [← (Equiv.ofBijective _ stepInv_bij).sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Equiv.ofBijective_apply]
  exact if_congr (sStep_rev p q s).symm rfl rfl

lemma sMat_isHermitian : (sMat W N).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial, sMat_symm]

lemma sMat_mulVec (v : SPt W N → ℝ) (p : SPt W N) :
    (sMat W N *ᵥ v) p = ∑ s : Step, (sStep p s).elim 0 v := by
  simp only [mulVec, dotProduct, sMat, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases sStep p s with _ | q <;> simp

theorem abs_eig_sMat_le (j : SPt W N) :
    |(sMat_isHermitian (W := W) (N := N)).eigenvalues j| ≤ 4 := by
  set hA := sMat_isHermitian (W := W) (N := N)
  set b : SPt W N → ℝ := ⇑(hA.eigenvectorBasis j)
  set ev := hA.eigenvalues j
  have hb : ∃ q, b q ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : hA.eigenvectorBasis j = 0 := by ext q; exact h q
    exact (hA.eigenvectorBasis).orthonormal.ne_zero j h0
  obtain ⟨q, hq⟩ := hb
  have : Nonempty (SPt W N) := ⟨q⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun r => |b r|
  have hbp : 0 < |b p| := lt_of_lt_of_le (abs_pos.mpr hq) (hp q)
  have heig : ev * b p = ∑ s : Step, (sStep p s).elim 0 b := by
    have := congrFun (hA.mulVec_eigenvectorBasis j) p
    rw [sMat_mulVec] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hle : |ev| * |b p| ≤ 4 * |b p| := by
    rw [← abs_mul, heig]
    calc |∑ s : Step, (sStep p s).elim 0 b| ≤ ∑ s : Step, |(sStep p s).elim 0 b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : Step, |b p| := Finset.sum_le_sum fun s _ => by
          rcases sStep p s with _ | r
          · simp
          · exact hp r
      _ = 4 * |b p| := by rw [Finset.sum_const, Step.card_univ, nsmul_eq_mul]; norm_num
  exact le_of_mul_le_mul_right hle hbp

/-- The walk spelled by a word in the strip (`none` once it hits a wall). -/
def sWalk (p : SPt W N) : List Step → Option (SPt W N)
  | [] => some p
  | s :: w => (sStep p s).bind fun q => sWalk q w

/-- **Powers of the strip matrix count words that stay in the strip.** -/
theorem sMat_pow_apply (k : ℕ) (p q : SPt W N) :
    (sMat W N ^ k) p q = ∑ w : Fin k → Step, if sWalk p (wordList w) = some q then 1 else 0 := by
  induction k generalizing p with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    simp [wordList, sWalk, eq_comm]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    have e : ∀ f : (Fin (k + 1) → Step) → ℝ,
        ∑ w, f w = ∑ s : Step, ∑ w : Fin k → Step, f (Fin.cons s w) := by
      intro f; rw [← (Fin.consEquiv fun _ => Step).sum_comp, Fintype.sum_prod_type]; rfl
    rw [e]
    simp only [sMat, Finset.sum_mul]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun s _ => ?_)
    simp only [wordList, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, sWalk]
    rcases sStep p s with _ | r <;> simp

/-- The walk from column `x₀` stays in `[0,W)`. -/
def InS (W : ℕ) (x₀ : ℤ) (w : List Step) : Prop := ∀ x ∈ xs x₀ w, 0 ≤ x ∧ x < W

lemma eq_add_iff {G : Type*} [AddCommGroup G] {x a b e e' : G} (h : a + e = b + e') :
    (x = a + e ↔ x = b + e') := by rw [h]

/-- **Strip walks**: the walk exists iff it stays in the strip; its endpoint is the
`H₃(ℤ)` endpoint reduced mod `N`. -/
theorem sWalk_eq_some (w : List Step) (p q : SPt W N) :
    sWalk p w = some q ↔ InS W (p.1.val : ℤ) w ∧ (q.1.val : ℤ) = p.1.val + xEnd w ∧
      q.2.1 = p.2.1 + ((yEnd w : ℤ) : ZMod N) ∧
      q.2.2 = p.2.2 + ((areaFrom (p.1.val : ℤ) w : ℤ) : ZMod N) := by
  induction w generalizing p with
  | nil =>
    obtain ⟨⟨a, ha⟩, b, c⟩ := p
    obtain ⟨⟨a', ha'⟩, b', c'⟩ := q
    simp only [sWalk, InS, xs_nil, List.mem_singleton, forall_eq, xEnd_nil, yEnd_nil,
      areaFrom_nil, Int.cast_zero, add_zero, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, rfl, rfl, rfl⟩
    · rintro ⟨-, h, rfl, rfl⟩; exact ⟨by omega, rfl, rfl⟩
  | cons s w ih =>
    obtain ⟨⟨a, ha⟩, b, c⟩ := p
    have hA : (0 : ℤ) ≤ a ∧ (a : ℤ) < W := ⟨by positivity, by exact_mod_cast ha⟩
    cases s
    · by_cases h : a + 1 < W
      · simp only [sWalk, sStep, h, dif_pos, Option.bind_some]
        rw [ih]
        simp only [InS, xs_cons, List.mem_cons, forall_eq_or_imp, xEnd_cons, yEnd_cons,
          areaFrom_cons, Step.dx, Step.dy]
        push_cast
        simp only [hA, true_and, zero_add, mul_zero, add_assoc]
      · simp only [sWalk, sStep, h, dif_neg, not_false_iff, Option.bind_none, reduceCtorEq,
          false_iff, InS, xs_cons, Step.dx]
        rintro ⟨hS, -⟩
        have := (hS ((a : ℤ) + 1) (List.mem_cons_of_mem _ (start_mem_xs _ _))).2
        omega
    · by_cases h : 0 < a
      · simp only [sWalk, sStep, h, dif_pos, Option.bind_some]
        rw [ih]
        have hc : (((a - 1 : ℕ)) : ℤ) = (a : ℤ) + -1 := by omega
        simp only [hc, InS, xs_cons, List.mem_cons, forall_eq_or_imp, xEnd_cons,
          yEnd_cons, areaFrom_cons, Step.dx, Step.dy]
        push_cast
        simp only [hA, true_and, zero_add, mul_zero, add_assoc]
      · simp only [sWalk, sStep, h, dif_neg, not_false_iff, Option.bind_none, reduceCtorEq,
          false_iff, InS, xs_cons, Step.dx]
        rintro ⟨hS, -⟩
        have := (hS ((a : ℤ) + -1) (List.mem_cons_of_mem _ (start_mem_xs _ _))).1
        omega
    · simp only [sWalk, sStep, Option.bind_some]
      rw [ih]
      simp only [InS, xs_cons, List.mem_cons, forall_eq_or_imp, xEnd_cons,
        yEnd_cons, areaFrom_cons, Step.dx, Step.dy]
      push_cast
      simp only [hA, true_and, zero_add, mul_one, add_zero, add_assoc]
    · simp only [sWalk, sStep, Option.bind_some]
      rw [ih]
      simp only [InS, xs_cons, List.mem_cons, forall_eq_or_imp, xEnd_cons,
        yEnd_cons, areaFrom_cons, Step.dx, Step.dy]
      push_cast
      simp only [hA, true_and, zero_add, mul_neg, mul_one, add_zero, sub_eq_add_neg, add_assoc]

/-! ### Exact moments of the strip measure -/

open scoped Classical in
/-- **Diagonal walk counts**: for `(k+1)² ≤ N`, the closed strip walks from `(j,0,0)` are the
zero-area closed walks of `H₃(ℤ)` whose columns stay in `[0,W)`. -/
theorem sMat_pow_diag (k : ℕ) (hk : (k + 1) ^ 2 ≤ N) (j : Fin W) :
    (sMat W N ^ k) (j, 0, 0) (j, 0, 0) =
      ((zeroAreaWalks k).filter fun w => InS W (j.val : ℤ) (wordList w)).card := by
  rw [sMat_pow_apply, Finset.sum_boole]
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, zeroAreaWalks]
  rw [sWalk_eq_some]
  simp only [zero_add]
  have hlen : (wordList w).length = k := by simp [wordList]
  have hkN : (k : ℤ) < N := by
    have : k < N := by nlinarith
    exact_mod_cast this
  have hk2 : (k : ℤ) ^ 2 < N := by
    have : k ^ 2 < N := by nlinarith
    exact_mod_cast this
  constructor
  · rintro ⟨hS, hx, hy, ha⟩
    have hy' : yEnd (wordList w) = 0 := by
      have h1 := (abs_yEnd_le (wordList w)).trans_lt (by rw [hlen]; exact hkN)
      exact (intCast_eq_zero_iff_of_abs_lt h1).1 hy.symm
    have hc : IsClosed (wordList w) := ⟨by linarith, hy'⟩
    have ha' : area (wordList w) = 0 := by
      rw [areaFrom_eq, hy', mul_zero, zero_add] at ha
      have h1 := (abs_area_le_sq _ hc).trans_lt (by rw [hlen]; exact hk2)
      exact (intCast_eq_zero_iff_of_abs_lt h1).1 ha.symm
    exact ⟨⟨hc, ha'⟩, hS⟩
  · rintro ⟨⟨hc, ha⟩, hS⟩
    refine ⟨hS, by rw [hc.1, add_zero], by rw [hc.2, Int.cast_zero], ?_⟩
    rw [areaFrom_eq, hc.2, ha]; simp

lemma xs_shift (x₀ t : ℤ) (w : List Step) : xs (x₀ + t) w = (xs x₀ w).map (· + t) := by
  induction w generalizing x₀ with
  | nil => simp
  | cons s w ih =>
    simp only [xs_cons, List.map_cons]
    rw [show x₀ + t + s.dx = x₀ + s.dx + t by ring, ih]

/-- Leftmost and rightmost columns visited from `0`. -/
def lo (w : List Step) : ℤ := (xs 0 w).foldr min 0
def hi (w : List Step) : ℤ := (xs 0 w).foldr max 0

lemma foldr_min_mem (l : List ℤ) : l.foldr min 0 = 0 ∨ l.foldr min 0 ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases le_total a (l.foldr min 0) with h | h
    · right; left; exact min_eq_left h
    · rw [min_eq_right h]; rcases ih with h' | h'
      · left; exact h'
      · right; right; exact h'

lemma foldr_max_mem (l : List ℤ) : l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases le_total a (l.foldr max 0) with h | h
    · rw [max_eq_right h]; rcases ih with h' | h'
      · left; exact h'
      · right; right; exact h'
    · right; left; exact max_eq_left h

lemma foldr_min_le (l : List ℤ) : ∀ x ∈ l, l.foldr min 0 ≤ x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih x hx)

lemma le_foldr_max (l : List ℤ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih x hx).trans (le_max_right _ _)

lemma lo_mem (w : List Step) : lo w ∈ xs 0 w := by
  rcases foldr_min_mem (xs 0 w) with h | h
  · rw [lo, h]; exact start_mem_xs 0 w
  · exact h

lemma hi_mem (w : List Step) : hi w ∈ xs 0 w := by
  rcases foldr_max_mem (xs 0 w) with h | h
  · rw [hi, h]; exact start_mem_xs 0 w
  · exact h

lemma lo_nonpos (w : List Step) : lo w ≤ 0 := foldr_min_le _ 0 (start_mem_xs 0 w)
lemma hi_nonneg (w : List Step) : 0 ≤ hi w := le_foldr_max _ 0 (start_mem_xs 0 w)

lemma InS_iff (j : ℤ) (w : List Step) : InS W j w ↔ 0 ≤ lo w + j ∧ hi w + j < W := by
  unfold InS
  rw [show j = 0 + j by ring, xs_shift, ← show j = 0 + j by ring]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h; exact ⟨(h _ (lo_mem w)).1, (h _ (hi_mem w)).2⟩
  · intro h x hx
    have h1 : lo w ≤ x := foldr_min_le _ x hx
    have h2 : x ≤ hi w := le_foldr_max _ x hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Width of the horizontal range of a walk. -/
def width (w : List Step) : ℤ := hi w - lo w

lemma width_nonneg (w : List Step) : 0 ≤ width w := by
  unfold width; linarith [lo_nonpos w, hi_nonneg w]

/-- A closed walk of length `k` has width at most `k/2`. -/
lemma two_width_le {w : List Step} (hw : IsClosed w) : 2 * width w ≤ w.length := by
  have h := abs_sub_le_of_mem 0 w hw.cnt_RL (lo w) (lo_mem w) (hi w) (hi_mem w)
  have hl := hw.length_eq
  unfold width
  have : (w.length : ℤ) = 2 * ((cnt Step.R w : ℤ) + cnt Step.U w) := by exact_mod_cast hl
  have : (0 : ℤ) ≤ cnt Step.U w := by positivity
  linarith

open scoped Classical in
/-- Number of admissible starting columns: `W − width`. -/
lemma card_InS (w : List Step) (hw : width w ≤ W) :
    (((Finset.univ : Finset (Fin W)).filter fun j => InS W (j.val : ℤ) w).card : ℤ) =
      W - width w := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun j => if InS W (j : ℤ) w then 1 else 0)]
  rw [← Finset.card_filter]
  have hset : (Finset.range W).filter (fun j : ℕ => InS W (j : ℤ) w) =
      Finset.Ico (-lo w).toNat ((W : ℤ) - hi w).toNat := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, InS_iff]
    have := lo_nonpos w; have := hi_nonneg w
    omega
  rw [hset, Nat.card_Ico]
  unfold width at hw ⊢
  have := lo_nonpos w; have := hi_nonneg w
  omega

/-- The **deficit** `b_k = ∑_{w ∈ Z_k} width(w)` (sum over zero-area closed walks of length
`k`); it depends on `k` only. -/
def bk (k : ℕ) : ℤ := ∑ w ∈ zeroAreaWalks k, width (wordList w)

lemma bk_nonneg (k : ℕ) : 0 ≤ bk k := Finset.sum_nonneg fun _ _ => width_nonneg _

/-- `2 b_k ≤ k τ(Aᵏ)`. -/
lemma two_bk_le (k : ℕ) : 2 * bk k ≤ k * (moment k : ℤ) := by
  unfold bk moment
  rw [Finset.mul_sum, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have hc : IsClosed (wordList w) := (Finset.mem_filter.1 hw).2.1
  have := two_width_le hc
  simpa [wordList] using this

open scoped Classical in
lemma sum_card_InS (k : ℕ) (hkW : k ≤ 2 * W) :
    (∑ j : Fin W, (((zeroAreaWalks k).filter fun w => InS W (j.val : ℤ) (wordList w)).card : ℤ))
      = W * (moment k : ℤ) - bk k := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  have h : ∀ w ∈ zeroAreaWalks k,
      (∑ j : Fin W, if InS W (j.val : ℤ) (wordList w) then (1 : ℤ) else 0) = W - width (wordList w) := by
    intro w hw
    have hc : IsClosed (wordList w) := (Finset.mem_filter.1 hw).2.1
    have h2 := two_width_le hc
    have hlen : (wordList w).length = k := by simp [wordList]
    rw [hlen] at h2
    have hkW' : (k : ℤ) ≤ 2 * W := by exact_mod_cast hkW
    rw [← card_InS (W := W) (wordList w) (by linarith), Finset.card_filter]
    push_cast; rfl
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, bk, moment]
  ring

/-! ### The strip measure `σ_{W,N}` -/

variable [NeZero W]

/-- `σ_{W,N} = W⁻¹ ∑_{j<W} σ_{(j,0,0)}`: the grid-averaged Dirichlet model. -/
def stripMeasure (W N : ℕ) [NeZero W] [NeZero N] : Measure ℝ :=
  ((W : ENNReal)⁻¹) • ∑ j : Fin W, specM (sMat_isHermitian (W := W) (N := N)) (j, 0, 0)

instance : IsProbabilityMeasure (stripMeasure W N) := by
  constructor
  simp only [stripMeasure, Measure.smul_apply, FunLike.coe_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using NeZero.ne W) (ENNReal.natCast_ne_top W)

lemma carried_strip : CarriedBy4 (stripMeasure W N) := by
  have h := fun j : Fin W =>
    carried_specM (sMat_isHermitian (W := W) (N := N)) abs_eig_sMat_le (j, 0, 0)
  unfold CarriedBy4 at h ⊢
  simp only [stripMeasure, Measure.smul_apply, FunLike.coe_sum, Finset.sum_apply, h,
    Finset.sum_const_zero, smul_zero]

theorem integral_pow_strip (k : ℕ) :
    ∫ E, E ^ k ∂stripMeasure W N =
      (W : ℝ)⁻¹ * ∑ j : Fin W, (sMat W N ^ k) (j, 0, 0) (j, 0, 0) := by
  rw [stripMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_pow_specM, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro j _
    exact integrable_of_continuous
      (carried_specM (sMat_isHermitian (W := W) (N := N)) abs_eig_sMat_le (j, 0, 0))
      (continuous_pow k)

/-- **Exact Dirichlet moment formula** (grid model): for `k ≤ 2W` and `(k+1)² ≤ N`,
`W ∫ Eᵏ dσ_{W,N} = W τ(Aᵏ) − b_k`. -/
theorem stripMoment_formula (k : ℕ) (hk : (k + 1) ^ 2 ≤ N) (hkW : k ≤ 2 * W) :
    (W : ℝ) * ∫ E, E ^ k ∂stripMeasure W N = W * (moment k : ℝ) - bk k := by
  classical
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [integral_pow_strip, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  simp_rw [sMat_pow_diag k hk]
  have := sum_card_InS (W := W) k hkW
  have h2 : ((∑ j : Fin W, (((zeroAreaWalks k).filter fun w =>
      InS W (j.val : ℤ) (wordList w)).card : ℤ) : ℤ) : ℝ) = ((W * (moment k : ℤ) - bk k : ℤ) : ℝ) := by
    rw [this]
  push_cast at h2
  convert h2 using 2

/-! ### The two-scale identity and the Fejér domination -/

/-- **Two-scale identity for moments**: `τ(Aᵏ) = 2∫Eᵏ dσ_{2W,N} − ∫Eᵏ dσ_{W,N}` for `k ≤ 2W`,
`(k+1)² ≤ N`. -/
theorem two_scale_moment (k : ℕ) (hk : (k + 1) ^ 2 ≤ N) (hkW : k ≤ 2 * W) :
    (moment k : ℝ) =
      2 * ∫ E, E ^ k ∂stripMeasure (2 * W) N - ∫ E, E ^ k ∂stripMeasure W N := by
  have h1 := stripMoment_formula (W := W) (N := N) k hk hkW
  have h2 := stripMoment_formula (W := 2 * W) (N := N) k hk (by omega)
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  push_cast at h2
  apply mul_left_cancel₀ hW
  linear_combination h1 - h2

lemma polyIntegral_X_pow (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : CarriedBy4 μ) (k : ℕ) :
    polyIntegral μ hμ (X ^ k) = (4⁻¹ : ℝ) ^ k * ∫ E, E ^ k ∂μ := by
  show ∫ E, polyFun (X ^ k) E ∂μ = _
  simp only [polyFun, eval_pow, eval_X, div_eq_mul_inv, mul_pow]
  rw [integral_mul_const]; ring

/-- **Two-scale identity**: `∫ P(E/4) dμ_A = 2∫ P(E/4) dσ_{2W,N} − ∫ P(E/4) dσ_{W,N}` for
`deg P ≤ 2W`, `(2W+1)² ≤ N`. -/
theorem two_scale_poly (P : ℝ[X]) (hP : P.natDegree ≤ 2 * W) (hN : (2 * W + 1) ^ 2 ≤ N) :
    have := isSpectralMeasureA_muA.isProb
    polyIntegral muA isSpectralMeasureA_muA.carried P =
      2 * polyIntegral (stripMeasure (2 * W) N) carried_strip P -
        polyIntegral (stripMeasure W N) carried_strip P := by
  intro _
  rw [linear_eq_sum, linear_eq_sum (polyIntegral (stripMeasure (2 * W) N) carried_strip),
    linear_eq_sum (polyIntegral (stripMeasure W N) carried_strip)]
  unfold Polynomial.sum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ 2 * W := (le_natDegree_of_mem_supp k hk).trans hP
  have hkN : (k + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left (by omega) 2) hN
  simp only [polyIntegral_X_pow]
  rw [isSpectralMeasureA_muA.moments k, two_scale_moment k hkN hkd]
  ring

/-- Chebyshev coefficients: `c_n(μ_A) = 2 c_n(σ_{2W,N}) − c_n(σ_{W,N})` for `n ≤ 2W`. -/
theorem two_scale_cheb (n : ℕ) (hn : n ≤ 2 * W) (hN : (2 * W + 1) ^ 2 ≤ N) :
    chebCoeff muA n = 2 * chebCoeff (stripMeasure (2 * W) N) n - chebCoeff (stripMeasure W N) n := by
  have := isSpectralMeasureA_muA.isProb
  have h := two_scale_poly (W := W) (N := N) (T ℝ n)
    (by rw [natDegree_T ℝ (n : ℤ), Int.natAbs_natCast]; exact hn) hN
  simpa only [polyIntegral_T] using h

/-- **Fejér two-scale identity**: `F_n^{μ_A} = 2F_n^{σ_{2W,N}} − F_n^{σ_{W,N}}` for `n ≤ 2W`. -/
theorem fejer_two_scale (n : ℕ) (hn : n ≤ 2 * W) (hN : (2 * W + 1) ^ 2 ≤ N) (E : ℝ) :
    fejer muA n E = 2 * fejer (stripMeasure (2 * W) N) n E - fejer (stripMeasure W N) n E := by
  unfold fejer
  have key : ∑ m ∈ Finset.range n, fejMult n (m + 1) * chebCoeff muA (m + 1) * cheb (m + 1) E =
      2 * ∑ m ∈ Finset.range n, fejMult n (m + 1) * chebCoeff (stripMeasure (2 * W) N) (m + 1) *
        cheb (m + 1) E -
      ∑ m ∈ Finset.range n, fejMult n (m + 1) * chebCoeff (stripMeasure W N) (m + 1) *
        cheb (m + 1) E := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [two_scale_cheb (m + 1) (by have := Finset.mem_range.1 hm; omega) hN]
    ring
  rw [key]; ring

/-- **Fejér domination**: on `[-4,4]`, `0 ≤ F_n^{μ_A} ≤ 2F_n^{σ_{2W,N}}` for `n ≤ 2W`. -/
theorem fejer_dom (n : ℕ) (hn : n ≤ 2 * W) (hN : (2 * W + 1) ^ 2 ≤ N) {E : ℝ}
    (hE : E ∈ Icc (-4 : ℝ) 4) :
    0 ≤ fejer muA n E ∧ fejer muA n E ≤ 2 * fejer (stripMeasure (2 * W) N) n E := by
  have := isSpectralMeasureA_muA.isProb
  refine ⟨fejer_nonneg muA isSpectralMeasureA_muA.carried n hE, ?_⟩
  rw [fejer_two_scale n hn hN E]
  have := fejer_nonneg (stripMeasure W N) carried_strip n hE
  linarith

/-- `0 ≤ a ≤ 2b ⇒ a log a ≤ 2b log(2b) + 1`. -/
lemma mul_log_le_of_le_two_mul {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ 2 * b) :
    a * Real.log a ≤ 2 * b * Real.log (2 * b) + 1 := by
  rcases le_or_gt a 1 with h1 | h1
  · have : a * Real.log a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (Real.log_nonpos ha h1)
    have := mul_log_add_one_nonneg (show 0 ≤ 2 * b by linarith)
    linarith
  · have ha0 : 0 < a := by linarith
    have hl : Real.log a ≤ Real.log (2 * b) := Real.log_le_log ha0 hab
    have hl0 : 0 < Real.log a := Real.log_pos h1
    have : a * Real.log a ≤ a * Real.log (2 * b) := mul_le_mul_of_nonneg_left hl ha
    have : a * Real.log (2 * b) ≤ 2 * b * Real.log (2 * b) :=
      mul_le_mul_of_nonneg_right hab (by linarith)
    linarith

lemma two_mul_log_two_mul (b : ℝ) :
    2 * b * Real.log (2 * b) = 2 * Real.log 2 * b + 2 * (b * Real.log b) := by
  rcases eq_or_ne b 0 with h | h
  · simp [h]
  · rw [Real.log_mul (by norm_num) h]; ring

/-- **Entropy domination**: `H_n(μ_A) ≤ 2 H_n(σ_{2W,N}) + 2 log 2 + 1` for `n ≤ 2W`,
`(2W+1)² ≤ N`. -/
theorem fejEnt_two_scale_le (n : ℕ) (hn : n ≤ 2 * W) (hN : (2 * W + 1) ^ 2 ≤ N) :
    fejEnt muA n ≤ 2 * fejEnt (stripMeasure (2 * W) N) n + 2 * Real.log 2 + 1 := by
  set b := fejer (stripMeasure (2 * W) N) n
  have hb : Integrable b arcsine := integrable_of_continuous_arcsine (continuous_fejer _ n)
  have hbl := integrable_fejer_mul_log (stripMeasure (2 * W) N) n
  have hb1 : ∫ E, b E ∂arcsine = 1 := integral_fejer _ n
  calc fejEnt muA n ≤ ∫ E, (2 * Real.log 2 * b E + 2 * (b E * Real.log (b E)) + 1) ∂arcsine := by
        refine integral_mono_ae (integrable_fejer_mul_log muA n)
          (((hb.const_mul _).add (hbl.const_mul _)).add (integrable_const _)) ?_
        filter_upwards [ae_arcsine_mem_Icc] with E hE
        obtain ⟨h0, h2⟩ := fejer_dom n hn hN hE
        rw [← two_mul_log_two_mul]
        exact mul_log_le_of_le_two_mul h0 h2
    _ = 2 * Real.log 2 * 1 + 2 * fejEnt (stripMeasure (2 * W) N) n + 1 := by
        have i1 : Integrable (fun E => 2 * Real.log 2 * b E) arcsine := hb.const_mul _
        have i2 : Integrable (fun E => 2 * (b E * Real.log (b E))) arcsine := hbl.const_mul _
        have i12 : Integrable (fun E => 2 * Real.log 2 * b E + 2 * (b E * Real.log (b E)))
            arcsine := i1.add i2
        rw [integral_add i12 (integrable_const _), integral_add i1 i2, integral_const_mul,
          integral_const_mul, hb1, integral_const, fejEnt]
        simp [b]
    _ = _ := by ring

/-- **Reduction of the Fejér entropy target to the strip model.** If the Fejér entropies of the
strip measures at their own scale, `H_n(σ_{2n+2, (2n+3)²})`, are bounded uniformly in `n`, then
`FejerEntropyTarget` holds (and so `μ_A ≪ dE`). The hypothesis is **open**. -/
theorem fejerEntropyTarget_of_strip
    (h : ∃ B : ℝ, ∀ n : ℕ, fejEnt (stripMeasure (2 * (n + 1)) ((2 * (n + 1) + 1) ^ 2)) n ≤ B) :
    ThomWeightedL2.FejerEntropyTarget := by
  obtain ⟨B, hB⟩ := h
  refine ⟨2 * B + 2 * Real.log 2 + 1, fun n => ?_⟩
  have := fejEnt_two_scale_le (W := n + 1) (N := (2 * (n + 1) + 1) ^ 2) n (by omega) le_rfl
  linarith [hB n]

end ThomStrip
