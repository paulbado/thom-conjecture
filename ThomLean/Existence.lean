import ThomLean.Bridge
import ThomLean.Heisenberg.Isoperimetric
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Data.ZMod.Basic

/-!
# Existence of the canonical spectral measure `μ_A`

We construct a probability measure `μ` on `[-4,4]` with `∫ Eᵏ dμ = τ(Aᵏ)` for every `k`,
i.e. `IsSpectralMeasureA μ`, without the group von Neumann algebra.

1. *Finite quotients.* `H₃(ℤ/N)` acts on itself by right multiplication by the generators
   (`quotAct`). The adjacency matrix of this Schreier graph is real symmetric (`adj_symm`), its
   powers count words (`adj_pow_apply`), and its eigenvalues lie in `[-4,4]`
   (`abs_eigenvalues_le`).
2. *Finite spectral measures.* For a symmetric matrix with eigen-decomposition `A = U D Uᵀ`,
   `σ = ∑_j U_{p j}² δ_{λ_j}` is a probability measure with `∫ Eᵏ dσ = (Aᵏ)_{pp}`
   (`specMeasure`, `integral_pow_specMeasure`).
3. *Exact moment matching.* If `(k+1)² ≤ N`, a word of length `k` is trivial in `H₃(ℤ/N)` iff
   it is trivial in `H₃(ℤ)` (discrete isoperimetric inequality), hence
   `∫ Eᵏ dσ_N = τ(Aᵏ)` (`integral_pow_quotMeasure`).
4. *Compactness.* `ProbabilityMeasure [-4,4]` is compact (Prokhorov). Any cluster point of
   `(σ_N)` has all moments `τ(Aᵏ)`; pushing it to `ℝ` gives `exists_spectralMeasureA`.

Combined with `spectral_unique`, this defines `μ_A` canonically (`muA`, `isSpectralMeasureA_muA`).
All results are unconditional.
-/

noncomputable section

namespace ThomExistence

open ThomHeisenberg ThomChebyshev ThomBridge MeasureTheory Matrix Filter Topology Set
open scoped BoundedContinuousFunction

/-- Inverse step. -/
def stepInv : Step → Step
  | .R => .L
  | .L => .R
  | .U => .D
  | .D => .U

lemma stepInv_stepInv (s : Step) : stepInv (stepInv s) = s := by cases s <;> rfl

/-! ### Schreier graphs of a step action -/

section Generic

variable {X : Type*} (act : X → Step → X)

/-- Endpoint of the walk spelled by a word. -/
def walk (p : X) (w : List Step) : X := w.foldl act p

@[simp] lemma walk_nil (p : X) : walk act p [] = p := rfl
@[simp] lemma walk_cons (p : X) (s : Step) (w : List Step) :
    walk act p (s :: w) = walk act (act p s) w := rfl

variable [Fintype X] [DecidableEq X]

/-- Adjacency matrix `A_{pq} = #{s : p·s = q}`. -/
def adj : Matrix X X ℝ := fun p q => ∑ s : Step, if act p s = q then 1 else 0

lemma adj_mulVec (v : X → ℝ) (p : X) : (adj act *ᵥ v) p = ∑ s : Step, v (act p s) := by
  simp only [mulVec, dotProduct, adj, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- **Powers of the adjacency matrix count words.** -/
theorem adj_pow_apply (k : ℕ) (p q : X) :
    (adj act ^ k) p q = ∑ w : Fin k → Step, if walk act p (wordList w) = q then 1 else 0 := by
  induction k generalizing p with
  | zero => simp [wordList, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    simp only [adj, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← (Fin.consEquiv fun _ => Step).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv_apply, wordList, List.ofFn_succ]

variable {act}

/-- Reversible actions give symmetric adjacency matrices. -/
theorem adj_symm (hrev : ∀ p s, act (act p s) (stepInv s) = p) : (adj act)ᵀ = adj act := by
  ext p q
  rw [transpose_apply, adj, adj]
  let e : Step ≃ Step := ⟨stepInv, stepInv, stepInv_stepInv, stepInv_stepInv⟩
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : act q (stepInv s) = p ↔ act p s = q := by
    constructor
    · rintro rfl
      have := hrev q (stepInv s)
      rwa [stepInv_stepInv] at this
    · rintro rfl; exact hrev p s
  simp only [e, Equiv.coe_fn_mk, this]

theorem adj_isHermitian (hrev : ∀ p s, act (act p s) (stepInv s) = p) : (adj act).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial, adj_symm hrev]

variable (hrev : ∀ p s, act (act p s) (stepInv s) = p)

/-- **Eigenvalue bound** `|λ| ≤ 4` (maximum principle). -/
theorem abs_eigenvalues_le (j : X) : |(adj_isHermitian hrev).eigenvalues j| ≤ 4 := by
  set hA := adj_isHermitian hrev
  set b : X → ℝ := ⇑(hA.eigenvectorBasis j)
  set ev := hA.eigenvalues j
  have hb : ∃ q, b q ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : hA.eigenvectorBasis j = 0 := by ext q; exact h q
    have := (hA.eigenvectorBasis).orthonormal.ne_zero j
    exact this h0
  obtain ⟨q, hq⟩ := hb
  have : Nonempty X := ⟨q⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun r => |b r|
  have hbp : 0 < |b p| := lt_of_lt_of_le (abs_pos.mpr hq) (hp q)
  have heig : ev * b p = ∑ s : Step, b (act p s) := by
    have := congrFun (hA.mulVec_eigenvectorBasis j) p
    rw [adj_mulVec] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hle : |ev| * |b p| ≤ 4 * |b p| := by
    rw [← abs_mul, heig]
    calc |∑ s : Step, b (act p s)| ≤ ∑ s : Step, |b (act p s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : Step, |b p| := Finset.sum_le_sum fun s _ => hp _
      _ = 4 * |b p| := by rw [Finset.sum_const, Step.card_univ, nsmul_eq_mul]; norm_num
  exact le_of_mul_le_mul_right hle hbp

/-- The unitary of eigenvectors, as a real matrix. -/
def eigU : Matrix X X ℝ := ((adj_isHermitian hrev).eigenvectorUnitary : Matrix X X ℝ)

lemma eigU_mul_star : eigU hrev * (eigU hrev)ᵀ = 1 := by
  have := mem_unitaryGroup_iff.mp ((adj_isHermitian hrev).eigenvectorUnitary).2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this

lemma star_mul_eigU : (eigU hrev)ᵀ * eigU hrev = 1 := by
  have := mem_unitaryGroup_iff'.mp ((adj_isHermitian hrev).eigenvectorUnitary).2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this

lemma adj_mul_eigU : adj act * eigU hrev =
    eigU hrev * diagonal (adj_isHermitian hrev).eigenvalues := by
  ext i j
  rw [mul_diagonal]
  have h := congrFun ((adj_isHermitian hrev).mulVec_eigenvectorBasis j) i
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [eigU, IsHermitian.eigenvectorUnitary_apply, mul_comm, ← h, Matrix.mul_apply]
  simp only [mulVec, dotProduct]
  rfl

/-- **Finite spectral decomposition of moments**: `(Aᵏ)_{pp} = ∑_j U_{pj}² λ_jᵏ`. -/
theorem adj_pow_diag (k : ℕ) (p : X) :
    (adj act ^ k) p p = ∑ j, eigU hrev p j ^ 2 * (adj_isHermitian hrev).eigenvalues j ^ k := by
  set U := eigU hrev
  set ev := (adj_isHermitian hrev).eigenvalues
  have hk : adj act ^ k * U = U * diagonal ev ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, adj_mul_eigU, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have : adj act ^ k = U * diagonal ev ^ k * Uᵀ := by
    rw [← hk, mul_assoc, eigU_mul_star, mul_one]
  rw [this, diagonal_pow, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, transpose_apply]
  simp only [Pi.pow_apply]; ring

lemma sum_eigU_sq (p : X) : ∑ j, eigU hrev p j ^ 2 = 1 := by
  have := congrFun (congrFun (eigU_mul_star hrev) p) p
  rw [Matrix.mul_apply, one_apply_eq] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [transpose_apply]; ring

/-- The interval `[-4,4]` as a type. -/
abbrev S4 := Icc (-4 : ℝ) 4

instance : CompactSpace S4 := isCompact_iff_compactSpace.mp isCompact_Icc

lemma eigenvalue_mem (j : X) : (adj_isHermitian hrev).eigenvalues j ∈ Icc (-4 : ℝ) 4 :=
  abs_le.mp (abs_eigenvalues_le hrev j)

/-- The finite spectral measure of `A` at the vertex `p`, on `[-4,4]`. -/
def specMeasure (p : X) : Measure S4 :=
  ∑ j, (Real.toNNReal (eigU hrev p j ^ 2)) • Measure.dirac ⟨_, eigenvalue_mem hrev j⟩

instance (p : X) : IsProbabilityMeasure (specMeasure hrev p) := by
  constructor
  simp only [specMeasure, FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ,
    ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, ← Real.toNNReal_sum_of_nonneg (fun j _ => sq_nonneg _),
    sum_eigU_sq]
  simp

/-- **Moments of the finite spectral measure**: `∫ Eᵏ dσ_p = (Aᵏ)_{pp}`. -/
theorem integral_pow_specMeasure (k : ℕ) (p : X) :
    ∫ E, (E : ℝ) ^ k ∂specMeasure hrev p = (adj act ^ k) p p := by
  rw [adj_pow_diag hrev, specMeasure, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def,
      Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure_nnreal

end Generic

/-! ### Finite Heisenberg quotients `H₃(ℤ/N)` -/

/-- Points of `H₃(ℤ/N)`. -/
abbrev QPt (N : ℕ) := ZMod N × ZMod N × ZMod N

/-- Right multiplication by the generators in `H₃(ℤ/N)`:
`(a,b,c)·x^{±1} = (a±1,b,c)` and `(a,b,c)·y^{±1} = (a,b±1,c±a)`. -/
def quotAct (N : ℕ) (p : QPt N) : Step → QPt N
  | .R => (p.1 + 1, p.2.1, p.2.2)
  | .L => (p.1 - 1, p.2.1, p.2.2)
  | .U => (p.1, p.2.1 + 1, p.2.2 + p.1)
  | .D => (p.1, p.2.1 - 1, p.2.2 - p.1)

lemma quotAct_rev (N : ℕ) (p : QPt N) (s : Step) : quotAct N (quotAct N p s) (stepInv s) = p := by
  cases s <;> simp [quotAct, stepInv]

/-- Reduction `H₃(ℤ) → H₃(ℤ/N)`. -/
def castH (N : ℕ) (g : H3) : QPt N := ((g.a : ZMod N), (g.b : ZMod N), (g.c : ZMod N))

lemma castH_one (N : ℕ) : castH N 1 = 0 := by simp [castH]

lemma castH_mul_gen (N : ℕ) (g : H3) (s : Step) :
    castH N (g * s.gen) = quotAct N (castH N g) s := by
  cases s <;> simp [castH, quotAct, Step.gen, H3.x, H3.y] <;> (try ring_nf) <;> simp

lemma walk_castH (N : ℕ) (g : H3) (w : List Step) :
    walk (quotAct N) (castH N g) w = castH N (g * evalWord w) := by
  induction w generalizing g with
  | nil => simp
  | cons s w ih => rw [walk_cons, ← castH_mul_gen, ih, evalWord_cons, mul_assoc]

lemma abs_xEnd_le (w : List Step) : |xEnd w| ≤ w.length := by
  rw [xEnd_eq_cnt, length_eq_cnt, abs_le]; push_cast; constructor <;> omega

lemma abs_yEnd_le (w : List Step) : |yEnd w| ≤ w.length := by
  rw [yEnd_eq_cnt, length_eq_cnt, abs_le]; push_cast; constructor <;> omega

lemma abs_area_le_sq (w : List Step) (hw : IsClosed w) : |area w| ≤ (w.length : ℤ) ^ 2 := by
  have h := abs_area_le w hw
  have h1 : (cnt Step.R w : ℤ) ≤ w.length := by rw [length_eq_cnt]; push_cast; omega
  have h2 : (cnt Step.U w : ℤ) ≤ w.length := by rw [length_eq_cnt]; push_cast; omega
  have h3 : (0 : ℤ) ≤ cnt Step.U w := by positivity
  nlinarith

lemma intCast_eq_zero_iff_of_abs_lt {N : ℕ} {a : ℤ} (ha : |a| < N) : (a : ZMod N) = 0 ↔ a = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨fun h => Int.eq_zero_of_abs_lt_dvd h ha, fun h => by simp [h]⟩

/-- **Exact moment matching for finite quotients**: if `(k+1)² ≤ N`, a word of length `k` is
trivial in `H₃(ℤ/N)` iff it is trivial in `H₃(ℤ)`. -/
theorem castH_evalWord_eq_zero_iff {N : ℕ} (w : List Step) (hN : (w.length + 1) ^ 2 ≤ N) :
    castH N (evalWord w) = 0 ↔ IsClosed w ∧ area w = 0 := by
  have hlen : (w.length : ℤ) < N := by
    have : w.length < N := by nlinarith
    exact_mod_cast this
  have hsq : (w.length : ℤ) ^ 2 < N := by
    have : w.length ^ 2 < N := by nlinarith
    exact_mod_cast this
  rw [evalWord_eq, castH, Prod.mk_eq_zero, Prod.mk_eq_zero]
  simp only
  rw [intCast_eq_zero_iff_of_abs_lt ((abs_xEnd_le w).trans_lt hlen),
    intCast_eq_zero_iff_of_abs_lt ((abs_yEnd_le w).trans_lt hlen)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hc : IsClosed w := ⟨h1, h2⟩
    exact ⟨hc, (intCast_eq_zero_iff_of_abs_lt ((abs_area_le_sq w hc).trans_lt hsq)).mp h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, by simp [h3]⟩

/-- Word counts in the quotient equal the zero-area walk counts. -/
theorem quot_adj_pow (N : ℕ) [NeZero N] (k : ℕ) (hk : (k + 1) ^ 2 ≤ N) :
    (adj (quotAct N) ^ k) 0 0 = moment k := by
  rw [adj_pow_apply, moment, zeroAreaWalks, Finset.sum_boole]
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← castH_one, walk_castH, one_mul, castH_one,
    castH_evalWord_eq_zero_iff _ (by simpa [wordList] using hk)]

/-- The spectral measure of the vertex `0` of the Schreier graph of `H₃(ℤ/(n+1))`. -/
def quotMeasure (n : ℕ) : ProbabilityMeasure S4 :=
  ⟨specMeasure (quotAct_rev (n + 1)) 0, inferInstance⟩

/-- **Moments of the finite-quotient measures**: `∫ Eᵏ dσ_n = τ(Aᵏ)` once `(k+1)² ≤ n+1`. -/
theorem integral_pow_quotMeasure (n k : ℕ) (hk : (k + 1) ^ 2 ≤ n + 1) :
    ∫ E, (E : ℝ) ^ k ∂(quotMeasure n : Measure S4) = moment k := by
  show ∫ E, (E : ℝ) ^ k ∂specMeasure (quotAct_rev (n + 1)) 0 = _
  rw [integral_pow_specMeasure, quot_adj_pow _ _ hk]

/-! ### Compactness and the limit measure -/

/-- **Existence of the canonical spectral measure**: there is a probability measure `μ` on
`[-4,4]` with `∫ Eᵏ dμ = τ(Aᵏ)` for all `k`. -/
theorem exists_spectralMeasureA : ∃ μ : Measure ℝ, IsSpectralMeasureA μ := by
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (map quotMeasure atTop)
  have hν' : MapClusterPt ν atTop quotMeasure := hν
  have hmom : ∀ k : ℕ, ∫ E, (E : ℝ) ^ k ∂(ν : Measure S4) = moment k := by
    intro k
    let f : S4 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun E => (E : ℝ) ^ k, by fun_prop⟩
    have hf : ∀ E : S4, f E = (E : ℝ) ^ k := fun E => rfl
    have hc := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
    have h1 := hν'.continuousAt_comp hc.continuousAt
    have hev : ∀ᶠ n in atTop,
        ((fun μ : ProbabilityMeasure S4 => ∫ E, f E ∂(μ : Measure S4)) ∘ quotMeasure) n =
          (moment k : ℝ) := by
      refine eventually_atTop.2 ⟨(k + 1) ^ 2, fun n hn => ?_⟩
      simp only [Function.comp_apply, hf]
      exact integral_pow_quotMeasure n k (by omega)
    simp only [hf] at h1 hev
    by_contra hne
    have hU : ({(moment k : ℝ)}ᶜ : Set ℝ) ∈ 𝓝 (∫ E, (E : ℝ) ^ k ∂(ν : Measure S4)) :=
      isOpen_compl_singleton.mem_nhds hne
    obtain ⟨n, hn1, hn2⟩ := ((mapClusterPt_iff_frequently.mp h1) _ hU).and_eventually hev |>.exists
    exact hn1 hn2
  refine ⟨(ν : Measure S4).map Subtype.val, ⟨?_, ?_, ?_⟩⟩
  · exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  · unfold CarriedBy4
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val ⁻¹' (Icc (-4 : ℝ) 4)ᶜ : Set S4) = ∅ := by
      ext E; simp
    rw [this, measure_empty]
  · intro k
    rw [integral_map measurable_subtype_coe.aemeasurable (by fun_prop)]
    exact hmom k

/-- **The canonical spectral measure** `μ_A`, unique by `spectral_unique`. -/
def muA : Measure ℝ := Classical.choose exists_spectralMeasureA

theorem isSpectralMeasureA_muA : IsSpectralMeasureA muA :=
  Classical.choose_spec exists_spectralMeasureA

theorem isSpectralMeasureA_iff (μ : Measure ℝ) : IsSpectralMeasureA μ ↔ μ = muA :=
  ⟨fun h => spectral_unique h isSpectralMeasureA_muA, fun h => h ▸ isSpectralMeasureA_muA⟩

end ThomExistence
