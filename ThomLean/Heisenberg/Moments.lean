import ThomLean.Heisenberg.Group
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Group-ring moments of `A = x + x⁻¹ + y + y⁻¹` and the rational-flux moment formula

* `opA_pow` : `A^n = ∑_{w ∈ Step^n} [eval w]` in the integral group ring `ℤ[H₃(ℤ)]`.
* `tau_opA_pow` : the canonical trace `τ(A^n)` (coefficient of the identity) equals the
  number of closed lattice walks of length `n` with zero algebraic area
  (Bado–Pittet, Lemma 3.1, eq. (14)).
* `fluxTrace_opA_pow` : for every flux `α`, the central-character trace
  `τ_α(f) = ∑_{g = (0,0,c)} f(g) e^{2πiαc}` satisfies
  `τ_α(A^n) = ∑_{closed w} e^{2πiα·area(w)}`.
* `avg_fluxTrace_opA_pow` : averaging over `α = p/Q`, `0 ≤ p < Q`, gives the number of closed
  walks whose area is divisible by `Q` (Lemma 3.1, eq. (15)), via the character
  orthogonality relation `rootsOfUnity_filter`.

Modelling note. `τ_α` is the trace of the image of `ℤ[H₃]` under the central character
`z ↦ e^{2πiα}`, i.e. the canonical trace of the rotation algebra. Its identification with the
`n`-th moment of the Harper density of states `ν_α` (direct-integral / Floquet theory) is
classical but **not** formalized here.
-/

noncomputable section

namespace ThomHeisenberg

open MonoidAlgebra Finset

variable (R : Type*) [CommRing R]

/-- The self-adjoint element `A = x + x⁻¹ + y + y⁻¹` of the group ring `R[H₃(ℤ)]`. -/
def opA : MonoidAlgebra R H3 := ∑ s : Step, single s.gen 1

/-- Words of length `n`, as tuples. -/
abbrev wordList {n : ℕ} (w : Fin n → Step) : List Step := List.ofFn w

/-- **Word expansion** `A^n = ∑_{w} [eval w]`. -/
theorem opA_pow (n : ℕ) :
    opA R ^ n = ∑ w : Fin n → Step, single (evalWord (wordList w)) (1 : R) := by
  induction n with
  | zero => simp [wordList, one_def]
  | succ n ih =>
    rw [pow_succ', ih, opA, Finset.sum_mul_sum]
    simp only [single_mul_single, mul_one]
    rw [← (Fin.consEquiv fun _ => Step).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv_apply, wordList, List.ofFn_succ]

/-- The canonical trace of the group ring: coefficient of the identity. -/
def tau (f : MonoidAlgebra R H3) : R := f.coeff 1

lemma tau_sum_single {ι : Type*} (s : Finset ι) (g : ι → H3) :
    tau R (∑ i ∈ s, single (g i) (1 : R)) = ((s.filter fun i => g i = 1).card : R) := by
  classical
  simp [tau, coeff_sum, Finsupp.single_apply, Finset.sum_boole]

/-- Closed walks of length `n` with zero area. -/
def zeroAreaWalks (n : ℕ) : Finset (Fin n → Step) :=
  Finset.univ.filter fun w => IsClosed (wordList w) ∧ area (wordList w) = 0

/-- Closed walks of length `n` whose area is divisible by `Q`. -/
def modAreaWalks (Q : ℕ) (n : ℕ) : Finset (Fin n → Step) :=
  Finset.univ.filter fun w => IsClosed (wordList w) ∧ (Q : ℤ) ∣ area (wordList w)

/-- Closed walks of length `n`. -/
def closedWalks (n : ℕ) : Finset (Fin n → Step) :=
  Finset.univ.filter fun w => IsClosed (wordList w)

/-- **Trace moments = zero-area closed walks** (Bado–Pittet, eq. (14)). -/
theorem tau_opA_pow (n : ℕ) : tau R (opA R ^ n) = ((zeroAreaWalks n).card : R) := by
  classical
  rw [opA_pow, tau_sum_single]
  congr 2
  ext w
  simp [zeroAreaWalks, evalWord_eq_one_iff, IsClosed, and_assoc]

/-- Integer moments `m_n = τ(A^n)`. -/
def moment (n : ℕ) : ℕ := (zeroAreaWalks n).card

/-! ### Rational flux -/

/-- Central-character weight `g ↦ e^{2πiα c}` on `Z(H₃) = {(0,0,c)}`, zero elsewhere. -/
def fluxWeight (α : ℝ) (g : H3) : ℂ :=
  if g.a = 0 ∧ g.b = 0 then Complex.exp (2 * Real.pi * Complex.I * α * g.c) else 0

/-- The flux-`α` trace `τ_α(f) = ∑_g f(g) · fluxWeight α g` on `ℤ[H₃]`. -/
def fluxTrace (α : ℝ) (f : MonoidAlgebra ℤ H3) : ℂ :=
  f.coeff.sum fun g r => (r : ℂ) * fluxWeight α g

lemma fluxTrace_sum_single {ι : Type*} (s : Finset ι) (g : ι → H3) (α : ℝ) :
    fluxTrace α (∑ i ∈ s, single (g i) (1 : ℤ)) = ∑ i ∈ s, fluxWeight α (g i) := by
  classical
  unfold fluxTrace
  rw [coeff_sum, ← Finsupp.sum_finsetSum_index (by simp) (by intros; push_cast; ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_single, Finsupp.sum_single_index (by simp)]
  simp

/-- **Flux moment formula**: `τ_α(A^n) = ∑_{closed w} e^{2πiα·area(w)}`. -/
theorem fluxTrace_opA_pow (α : ℝ) (n : ℕ) :
    fluxTrace α (opA ℤ ^ n) =
      ∑ w ∈ closedWalks n, Complex.exp (2 * Real.pi * Complex.I * α * area (wordList w)) := by
  classical
  rw [opA_pow, fluxTrace_sum_single, closedWalks, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [fluxWeight, evalWord_eq, IsClosed]

/-- **Character orthogonality on `ℤ/Qℤ`**:
`(1/Q) ∑_{p<Q} e^{2πi p k / Q} = [Q ∣ k]`. -/
theorem rootsOfUnity_filter (Q : ℕ) (hQ : 0 < Q) (k : ℤ) :
    (1 / (Q : ℂ)) * ∑ p ∈ Finset.range Q,
        Complex.exp (2 * Real.pi * Complex.I * ((p : ℝ) / Q) * k) =
      if (Q : ℤ) ∣ k then 1 else 0 := by
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / Q) with hζ
  have hterm : ∀ p : ℕ, Complex.exp (2 * Real.pi * Complex.I * ((p : ℝ) / Q) * k) = ζ ^ p := by
    intro p
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simp_rw [hterm]
  have hζQ : ζ ^ Q = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    rw [show (Q : ℂ) * (2 * Real.pi * Complex.I * k / Q) = (k : ℂ) * (2 * Real.pi * Complex.I) by
      field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I k
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      rw [hζ]
      rw [show 2 * Real.pi * Complex.I * ((((Q : ℤ) * m : ℤ)) : ℂ) / Q =
          (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I m
    simp [hζ1, hQ']
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      apply hdvd
      refine ⟨m, ?_⟩
      have h2 : (k : ℂ) = (Q : ℂ) * m := by
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        field_simp at hm
        linear_combination hm
      exact_mod_cast h2
    rw [geom_sum_eq hζ1, hζQ]
    simp

/-- **Rational-flux moment formula** (Bado–Pittet, eq. (15)):
`(1/Q) ∑_{p<Q} τ_{p/Q}(A^n) = #{closed walks of length n with Q ∣ area}`. -/
theorem avg_fluxTrace_opA_pow (Q : ℕ) (hQ : 0 < Q) (n : ℕ) :
    (1 / (Q : ℂ)) * ∑ p ∈ Finset.range Q, fluxTrace ((p : ℝ) / Q) (opA ℤ ^ n) =
      ((modAreaWalks Q n).card : ℂ) := by
  classical
  calc (1 / (Q : ℂ)) * ∑ p ∈ Finset.range Q, fluxTrace ((p : ℝ) / Q) (opA ℤ ^ n)
      = ∑ w ∈ closedWalks n, (1 / (Q : ℂ)) * ∑ p ∈ Finset.range Q,
          Complex.exp (2 * Real.pi * Complex.I * ((p : ℝ) / Q) * area (wordList w)) := by
        simp_rw [fluxTrace_opA_pow]
        rw [Finset.sum_comm, Finset.mul_sum]
        simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    _ = ∑ w ∈ closedWalks n, if (Q : ℤ) ∣ area (wordList w) then (1 : ℂ) else 0 :=
        Finset.sum_congr rfl fun w _ => rootsOfUnity_filter Q hQ _
    _ = ((modAreaWalks Q n).card : ℂ) := by
        rw [Finset.sum_boole, closedWalks, Finset.filter_filter]
        rfl

/-- Integer rational-flux moments `m_n^{(Q)}`. -/
def fluxMoment (Q n : ℕ) : ℕ := (modAreaWalks Q n).card

lemma zeroAreaWalks_subset (Q n : ℕ) : zeroAreaWalks n ⊆ modAreaWalks Q n := by
  intro w hw
  simp only [zeroAreaWalks, modAreaWalks, Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, hw.2.1, by rw [hw.2.2]; exact dvd_zero _⟩

/-- The moment discrepancy is a nonnegative integer: `m_n ≤ m_n^{(Q)}`. -/
theorem moment_le_fluxMoment (Q n : ℕ) : moment n ≤ fluxMoment Q n :=
  Finset.card_le_card (zeroAreaWalks_subset Q n)

end ThomHeisenberg
