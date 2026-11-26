import ThomLean.UpperBound.Decomp
import ThomLean.ZeroLevel.LogSq

/-!
# Round 8, Task 4 (conclusion): the logarithmic upper bound at `0`

* `card_le_of_coercive` (generic): if a linear family `Φ : ℂ^ι → ℂ^X` is injective and the
  adjacency operator is coercive on its range, `‖Φβ‖² ≤ K ‖AΦβ‖²` with `K h² < 1`, then
  `#ι + #{j : |λ_j| ≤ h} ≤ #X` (subspace-codimension form of min–max).
* `card_small_le`: for `H₃(ℤ/N)`, `N` an odd prime, take `ι = {(p,t,x) : x ∉ Z_top(p,t)}` and
  `Φβ = ∑_{p,t} F^{p,t}_{ζ_{p,t}}` (chain vectors of round 6); `#{|λ_j| ≤ h} ≤ ∑_{p,t} #Z_top(p,t)`.
* `nuQ_upper`: `σ_N([−h,h]) ≤ 2/L + 640 (K+1)³/T² + L/N` (`L = 2^K ≤ N`, `T ≥ 24`,
  `4^K e^T h² < 1`).
* `logUpperBound_explicit`: **`μ_A([−h,h]) ≤ 17284 (1 + log log(1/h))³ / log²(1/h)`** for
  `0 < h ≤ e^{−121}` (unconditional), via moment matching along primes and `muA_no_atoms`.
-/

noncomputable section

namespace ThomUpper

open ThomZeroLevel ThomHeisenberg ThomExistence ThomNoAtoms ThomLowerBound ThomChebyshev
open Real Finset ComplexConjugate MeasureTheory Filter

set_option linter.unusedSectionVars false
set_option linter.deprecated false

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {act : X → Step → X} (hrev : ∀ p s, act (act p s) (stepInv s) = p)

lemma coef_add (u v : X → ℂ) (j : X) :
    coef hrev (fun p => u p + v p) j = coef hrev u j + coef hrev v j := by
  simp only [coef, mul_add, Finset.sum_add_distrib]

lemma coef_smul (c : ℂ) (u : X → ℂ) (j : X) :
    coef hrev (fun p => c * u p) j = c * coef hrev u j := by
  simp only [coef, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Codimension form of min–max.** -/
theorem card_le_of_coercive {ι : Type*} [Fintype ι] (Φ : (ι → ℂ) →ₗ[ℂ] (X → ℂ))
    (hΦ : ∀ β, nrm (Φ β) = 0 → β = 0) {h K : ℝ} (hK0 : 0 ≤ K) (hK : K * h ^ 2 < 1)
    (hco : ∀ β, nrm (Φ β) ≤ K * nrm (cAdj act (Φ β))) :
    Fintype.card ι + #{j | |(adj_isHermitian hrev).eigenvalues j| ≤ h} ≤ Fintype.card X := by
  set ev := (adj_isHermitian hrev).eigenvalues
  set J : Finset X := {j | |ev j| ≤ h} with hJ
  set Jc : Finset X := {j | ¬ |ev j| ≤ h} with hJc
  let M : (ι → ℂ) →ₗ[ℂ] (Jc → ℂ) :=
    { toFun := fun β j => coef hrev (Φ β) j
      map_add' := fun β β' => by
        funext j; simp only [map_add, Pi.add_apply]
        exact coef_add hrev (Φ β) (Φ β') j
      map_smul' := fun c β => by
        funext j; simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact coef_smul hrev c (Φ β) j }
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    set v := Φ β
    have hc : ∀ j, ¬ |ev j| ≤ h → coef hrev v j = 0 := by
      intro j hj
      have := congrFun hβ ⟨j, by simp only [hJc, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj⟩
      exact this
    have hAv : nrm (cAdj act v) ≤ h ^ 2 * nrm v := by
      rw [← parseval hrev v, ← parseval hrev (cAdj act v), Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [coef_cAdj, Complex.normSq_mul, Complex.normSq_ofReal]
      by_cases hj : |ev j| ≤ h
      · have : ev j * ev j ≤ h ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hj 2
          rw [sq_abs] at h2; nlinarith
        exact mul_le_mul_of_nonneg_right this (Complex.normSq_nonneg _)
      · rw [hc j hj]; simp
    have h1 := hco β
    have hv0 : nrm v = 0 := by
      have := nrm_nonneg v
      have h2 : nrm v ≤ K * h ^ 2 * nrm v := by
        calc nrm v ≤ K * nrm (cAdj act v) := h1
          _ ≤ K * (h ^ 2 * nrm v) := mul_le_mul_of_nonneg_left hAv hK0
          _ = _ := by ring
      nlinarith
    exact hΦ β hv0
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
    (fun j => |ev j| ≤ h)
  simp only [Finset.card_univ] at hsplit
  have e1 : #J = #(univ.filter fun j => |ev j| ≤ h) := rfl
  have e2 : #Jc = #(univ.filter fun j => ¬ |ev j| ≤ h) := rfl
  omega

end Generic

/-! ### The Heisenberg quotient -/

variable {N : ℕ} [NeZero N]

/-- Coordinates of `β` on the chain `(p,t)`. -/
def zeta {T : ℝ} {K : ℕ}
    (β : {i : ZMod N × ZMod N × ZMod N // i.2.2 ∉ Ztop T i.1 i.2.1 K} → ℂ) (p t : ZMod N)
    (x : ZMod N) : ℂ :=
  if hx : x ∉ Ztop T p t K then β ⟨(p, t, x), hx⟩ else 0

/-- The embedding `β ↦ ∑_{p,t} F^{p,t}_{ζ_{p,t}}`. -/
def PhiMap (T : ℝ) (K : ℕ) :
    ({i : ZMod N × ZMod N × ZMod N // i.2.2 ∉ Ztop T i.1 i.2.1 K} → ℂ) →ₗ[ℂ] (QPt N → ℂ) where
  toFun β g := ∑ pt : ZMod N × ZMod N, Fv pt.1 pt.2 (zeta β pt.1 pt.2) g
  map_add' β β' := by
    funext g
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pt _ => ?_
    simp only [Fv, zeta]; split_ifs <;> simp [add_mul]
  map_smul' c β := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pt _ => ?_
    simp only [Fv, zeta]; split_ifs <;> simp [mul_assoc]

lemma Fv_orth (ξ : ZMod N × ZMod N → ZMod N → ℂ) :
    ∀ i k : ZMod N × ZMod N, i ≠ k → ip (Fv i.1 i.2 (ξ i)) (Fv k.1 k.2 (ξ k)) = 0 := by
  intro i k hik
  rw [ip_Fv, if_neg]
  intro h; exact hik (Prod.ext h.1 h.2)

lemma nrm_sum_Fv (ξ : ZMod N × ZMod N → ZMod N → ℂ) :
    nrm (fun g => ∑ pt : ZMod N × ZMod N, Fv pt.1 pt.2 (ξ pt) g) =
      (N : ℝ) ^ 2 * ∑ pt : ZMod N × ZMod N, nrm (ξ pt) := by
  have := nrm_sum (fun _ => (1 : ℂ)) (fun pt : ZMod N × ZMod N => Fv pt.1 pt.2 (ξ pt)) (Fv_orth ξ)
  simp only [one_mul, map_one] at this
  rw [this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => nrm_Fv _ _ _

lemma cAdj_sum_Fv (hN : Odd N) (ξ : ZMod N × ZMod N → ZMod N → ℂ) :
    cAdj (quotAct N) (fun g => ∑ pt : ZMod N × ZMod N, Fv pt.1 pt.2 (ξ pt) g) =
      fun g => ∑ pt : ZMod N × ZMod N, Fv pt.1 pt.2 (chainH pt.1 pt.2 (ξ pt)) g := by
  have := cAdj_sum (act := quotAct N) (fun _ => (1 : ℂ))
    (fun pt : ZMod N × ZMod N => Fv pt.1 pt.2 (ξ pt))
  simp only [one_mul] at this
  rw [this]
  funext g
  exact Finset.sum_congr rfl fun pt _ => by rw [cAdj_Fv hN]

lemma card_iota (T : ℝ) (K : ℕ) :
    Fintype.card {i : ZMod N × ZMod N × ZMod N // i.2.2 ∉ Ztop T i.1 i.2.1 K} +
      ∑ pt : ZMod N × ZMod N, #(Ztop T pt.1 pt.2 K) = N ^ 3 := by
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod N × ZMod N × ZMod N))) (fun i => i.2.2 ∈ Ztop T i.1 i.2.1 K)
  have h2 : #(univ.filter fun i : ZMod N × ZMod N × ZMod N => i.2.2 ∈ Ztop T i.1 i.2.1 K) =
      ∑ pt : ZMod N × ZMod N, #(Ztop T pt.1 pt.2 K) := by
    rw [Finset.card_filter]
    rw [← Fintype.sum_equiv (Equiv.prodAssoc (ZMod N) (ZMod N) (ZMod N))
      (fun q : (ZMod N × ZMod N) × ZMod N => if q.2 ∈ Ztop T q.1.1 q.1.2 K then 1 else 0) _
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun pt _ => ?_
    simp
  simp only [Finset.card_univ, Fintype.card_prod, ZMod.card] at h
  rw [h2] at h
  rw [show N ^ 3 = N * (N * N) by ring]; omega

/-- **Eigenvalue count**: `#{j : |λ_j(A)| ≤ h} ≤ ∑_{p,t} #Z_top(p,t)` on `H₃(ℤ/N)`. -/
theorem card_small_le (hN : Odd N) {T : ℝ} {K : ℕ} (hK : 1 ≤ K) {h : ℝ}
    (hgap : 4 ^ K * exp T * h ^ 2 < 1) :
    #{j | |(adj_isHermitian (quotAct_rev N)).eigenvalues j| ≤ h} ≤
      ∑ pt : ZMod N × ZMod N, #(Ztop T pt.1 pt.2 K) := by
  set Φ := PhiMap (N := N) T K
  have hnrm : ∀ β, nrm (Φ β) = (N : ℝ) ^ 2 * ∑ pt : ZMod N × ZMod N, nrm (zeta β pt.1 pt.2) :=
    fun β => nrm_sum_Fv (fun pt => zeta β pt.1 pt.2)
  have hA : ∀ β, nrm (cAdj (quotAct N) (Φ β)) =
      (N : ℝ) ^ 2 * ∑ pt : ZMod N × ZMod N, nrm (chainH pt.1 pt.2 (zeta β pt.1 pt.2)) := by
    intro β
    show nrm (cAdj (quotAct N) (fun g => ∑ pt : ZMod N × ZMod N,
      Fv pt.1 pt.2 (zeta β pt.1 pt.2) g)) = _
    rw [cAdj_sum_Fv hN]
    exact nrm_sum_Fv (fun pt => chainH pt.1 pt.2 (zeta β pt.1 pt.2))
  have hzv : ∀ (β : {i : ZMod N × ZMod N × ZMod N // i.2.2 ∉ Ztop T i.1 i.2.1 K} → ℂ)
      (pt : ZMod N × ZMod N), ∀ x ∈ Ztop T pt.1 pt.2 K, zeta β pt.1 pt.2 x = 0 := by
    intro β pt x hx; simp [zeta, hx]
  have hco : ∀ β, nrm (Φ β) ≤ 4 ^ K * exp T * nrm (cAdj (quotAct N) (Φ β)) := by
    intro β
    rw [hnrm, hA, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun pt _ => ?_
    have := Ztop_coercive hN hK (zeta β pt.1 pt.2) (hzv β pt)
    have hN2 : (0 : ℝ) ≤ N ^ 2 := by positivity
    nlinarith
  have hΦ : ∀ β, nrm (Φ β) = 0 → β = 0 := by
    intro β h0
    rw [hnrm] at h0
    have hN2 : (0 : ℝ) < N ^ 2 := by have := Nat.pos_of_neZero N; positivity
    have hs : ∑ pt : ZMod N × ZMod N, nrm (zeta β pt.1 pt.2) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hN2.ne'
      · exact h
    funext i
    obtain ⟨⟨p, t, x⟩, hi⟩ := i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun pt _ => nrm_nonneg _)).mp hs (p, t)
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)).mp h1 x
      (Finset.mem_univ _)
    simp only [zeta, dif_pos hi, Complex.normSq_eq_zero] at h2
    exact h2
  have := card_le_of_coercive (quotAct_rev N) Φ hΦ (by positivity) hgap hco
  have hc := card_iota (N := N) T K
  simp only [QPt, Fintype.card_prod, ZMod.card] at this
  have e : N * (N * N) = N ^ 3 := by ring
  rw [e, ← hc] at this
  exact Nat.le_of_add_le_add_left this

/-! ### The finite-`N` bound -/

/-- **Upper bound at a prime level**: `σ_N([−h,h]) ≤ 2/L + 640 (K+1)³/T² + L/N`, `L = 2^K`. -/
theorem nuQ_upper (n : ℕ) [Fact (n + 1).Prime] (hN : Odd (n + 1)) {T : ℝ} (hT : 24 ≤ T)
    {K : ℕ} (hK : 1 ≤ K) (hKN : 2 ^ K ≤ n + 1) {h : ℝ} (hgap : 4 ^ K * exp T * h ^ 2 < 1) :
    (nuQ n).real (Set.Icc (-h) h) ≤
      2 / 2 ^ K + 640 * (K + 1) ^ 3 / T ^ 2 + 2 ^ K / ((n : ℝ) + 1) := by
  set N := n + 1 with hNdef
  have hq := quotMeasure_real_Icc n h
  have hc := card_small_le (N := N) hN hK hgap
  set L := 2 ^ K
  set q := N / L
  have hqL : q * L ≤ N := Nat.div_mul_le_self N L
  have hrem : N - q * L < L := by
    have := Nat.lt_div_mul_add (a := N) (b := L) (by positivity)
    change N < q * L + L at this
    omega
  have hT2 : 0 < T ^ 2 := by positivity
  -- expected size of the vanishing sets
  have hbad : ∀ i, (∑ pt : ZMod N × ZMod N, (badCount T pt.1 pt.2 (i * L) K : ℝ)) ≤
      320 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2 := by
    intro i
    rw [le_div_iff₀ hT2]
    have := sum_badCount_le (N := N) hN hT K (i * L) hKN
    have e : ((L : ℕ) : ℝ) = 2 ^ K := by simp [L]
    rw [e]; linarith
  have hsum : (∑ pt : ZMod N × ZMod N, (#(Ztop T pt.1 pt.2 K) : ℝ)) ≤
      q * (2 * (N : ℝ) ^ 2 + 640 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2) +
        (N : ℝ) ^ 2 * (N - q * L : ℕ) := by
    calc (∑ pt : ZMod N × ZMod N, (#(Ztop T pt.1 pt.2 K) : ℝ))
        ≤ ∑ pt : ZMod N × ZMod N, (∑ i ∈ range q, (2 + 2 * (badCount T pt.1 pt.2 (i * L) K : ℝ)) +
            (N - q * L : ℕ)) := Finset.sum_le_sum fun pt _ => card_Ztop_le K
      _ = ∑ i ∈ range q, (2 * (N : ℝ) ^ 2 + 2 * ∑ pt : ZMod N × ZMod N,
            (badCount T pt.1 pt.2 (i * L) K : ℝ)) + (N : ℝ) ^ 2 * (N - q * L : ℕ) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, ZMod.card, nsmul_eq_mul, ← Finset.mul_sum]
          push_cast; ring
      _ ≤ ∑ i ∈ range q, (2 * (N : ℝ) ^ 2 + 2 * (320 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2)) +
            (N : ℝ) ^ 2 * (N - q * L : ℕ) := by
          gcongr with i _; exact hbad i
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hcount : (nuQ n).real (Set.Icc (-h) h) * (N : ℝ) ^ 3 ≤
      q * (2 * (N : ℝ) ^ 2 + 640 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2) +
        (N : ℝ) ^ 2 * (N - q * L : ℕ) := by
    have e : ((n : ℝ) + 1) = (N : ℝ) := by simp [hNdef]
    have hq' : (nuQ n).real (Set.Icc (-h) h) * (N : ℝ) ^ 3 =
        #{j | |(adj_isHermitian (quotAct_rev (n + 1))).eigenvalues j| ≤ h} := by
      rw [← e]; exact hq
    rw [hq']
    calc (#{j | |(adj_isHermitian (quotAct_rev (n + 1))).eigenvalues j| ≤ h} : ℝ)
        ≤ ((∑ pt : ZMod N × ZMod N, #(Ztop T pt.1 pt.2 K) : ℕ) : ℝ) := by exact_mod_cast hc
      _ = ∑ pt : ZMod N × ZMod N, (#(Ztop T pt.1 pt.2 K) : ℝ) := by push_cast; rfl
      _ ≤ _ := hsum
  have hNp : (0 : ℝ) < N := by positivity
  have hLp : (0 : ℝ) < L := by positivity
  have hqLr : (q : ℝ) * L ≤ N := by exact_mod_cast hqL
  have hremr : ((N - q * L : ℕ) : ℝ) ≤ L := by exact_mod_cast hrem.le
  have e : ((n : ℝ) + 1) = (N : ℝ) := by simp [hNdef]
  rw [e]
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  rw [← mul_le_mul_iff_of_pos_right hN3]
  refine hcount.trans ?_
  have hK3 : (0 : ℝ) ≤ 640 * (K + 1) ^ 3 / T ^ 2 := by positivity
  have h1 : (q : ℝ) * (2 * (N : ℝ) ^ 2) ≤ 2 / L * N ^ 3 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLp]; nlinarith [sq_nonneg (N : ℝ)]
  have h2 : (q : ℝ) * (640 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2) ≤
      640 * (K + 1) ^ 3 / T ^ 2 * N ^ 3 := by
    have : (q : ℝ) * (640 * (N : ℝ) ^ 2 * L * (K + 1) ^ 3 / T ^ 2) =
        (q * L) * (N ^ 2 * (640 * (K + 1) ^ 3 / T ^ 2)) := by ring
    rw [this]
    calc (q * L : ℝ) * (N ^ 2 * (640 * (K + 1) ^ 3 / T ^ 2))
        ≤ N * (N ^ 2 * (640 * (K + 1) ^ 3 / T ^ 2)) :=
          mul_le_mul_of_nonneg_right hqLr (by positivity)
      _ = _ := by ring
  have h3 : (N : ℝ) ^ 2 * (N - q * L : ℕ) ≤ L / N * N ^ 3 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hNp]
    have : (N : ℝ) ^ 2 * (N - q * L : ℕ) * N = N ^ 3 * (N - q * L : ℕ) := by ring
    rw [this]; nlinarith [pow_pos hNp 3]
  have e2 : ((L : ℕ) : ℝ) = 2 ^ K := by simp [L]
  rw [e2] at h1 h3
  linarith

/-! ### Passage to `μ_A` -/

lemma real_split (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CarriedBy4 ν) {h : ℝ}
    (hh : 0 < h) (h4 : h ≤ 4) :
    ν.real (Set.Icc (-4) (-h) ∪ Set.Icc h 4) + ν.real (Set.Ioo (-h) h) = 1 := by
  have hI : ν.real (Set.Icc (-4 : ℝ) 4) = 1 := by
    have h1 : ν (Set.Icc (-4 : ℝ) 4) = 1 := by
      rw [← prob_compl_eq_zero_iff measurableSet_Icc]; exact hν
    simp [Measure.real, h1]
  have hU : Set.Icc (-4 : ℝ) 4 = (Set.Icc (-4) (-h) ∪ Set.Icc h 4) ∪ Set.Ioo (-h) h := by
    ext E; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioo]
    constructor
    · intro ⟨a, b⟩
      by_cases h1 : E ≤ -h
      · left; left; exact ⟨a, h1⟩
      · by_cases h2 : h ≤ E
        · left; right; exact ⟨h2, b⟩
        · right; constructor <;> linarith
    · rintro ((⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩) <;> constructor <;> linarith
  have hD : Disjoint (Set.Icc (-4) (-h) ∪ Set.Icc h 4) (Set.Ioo (-h) h) := by
    rw [Set.disjoint_left]
    rintro E (⟨_, b⟩ | ⟨a, _⟩) ⟨c, d⟩ <;> linarith
  rw [← hI, hU, measureReal_union hD measurableSet_Ioo]

/-- **Transfer of upper bounds** from the finite quotients along a frequent set of levels. -/
theorem muA_real_Icc_le {h B : ℝ} (hh : 0 < h) (h4 : h ≤ 4)
    (hB : ∀ ε > 0, ∃ᶠ n in atTop, (nuQ n).real (Set.Icc (-h) h) ≤ B + ε) :
    muA.real (Set.Icc (-h) h) ≤ B := by
  have hprob := isSpectralMeasureA_muA.isProb
  have hC : IsCompact (Set.Icc (-4 : ℝ) (-h) ∪ Set.Icc h 4) := isCompact_Icc.union isCompact_Icc
  have hIcc : muA.real (Set.Icc (-h) h) = muA.real (Set.Ioo (-h) h) := by
    have e : Set.Icc (-h) h = Set.Ioo (-h) h ∪ ({-h} ∪ {h}) := by
      ext E; simp only [Set.mem_Icc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro ⟨a, b⟩
        rcases eq_or_lt_of_le a with h1 | h1
        · right; left; exact h1.symm
        · rcases eq_or_lt_of_le b with h2 | h2
          · right; right; exact h2
          · left; exact ⟨h1, h2⟩
      · rintro (⟨a, b⟩ | rfl | rfl) <;> constructor <;> linarith
    have h0 : muA.real ({-h} ∪ {h}) = 0 := by
      have : muA ({-h} ∪ {h}) = 0 := measure_union_null (muA_no_atoms _) (muA_no_atoms _)
      rw [measureReal_def, this, ENNReal.toReal_zero]
    have hD : Disjoint (Set.Ioo (-h) h) ({-h} ∪ {h}) := by
      rw [Set.disjoint_left]; rintro E ⟨a, b⟩ (rfl | rfl) <;> simp_all
    rw [e, measureReal_union hD ((measurableSet_singleton _).union (measurableSet_singleton _)),
      h0, add_zero]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlow : 1 - B - ε ≤ muA.real (Set.Icc (-4 : ℝ) (-h) ∪ Set.Icc h 4) := by
    refine le_measureReal_of_moments muA isSpectralMeasureA_muA.carried nuQ nuQ_carried
      nuQ_moments hC ?_
    refine (hB ε hε).mono fun n hn => ?_
    have hs := real_split (nuQ n) (nuQ_carried n) hh h4
    have : (nuQ n).real (Set.Ioo (-h) h) ≤ (nuQ n).real (Set.Icc (-h) h) :=
      measureReal_mono Set.Ioo_subset_Icc_self
    linarith
  have hs := real_split muA isSpectralMeasureA_muA.carried hh h4
  linarith

/-- **The logarithmic upper bound at `0`** (unconditional):
`μ_A([−h,h]) ≤ 17284 (1 + log log(1/h))³ / log²(1/h)` for `0 < h ≤ e^{−121}`. -/
theorem logUpperBound_explicit {h : ℝ} (hh : 0 < h) (hh0 : h ≤ exp (-121)) :
    muA.real (Set.Icc (-h) h) ≤ 17284 * (1 + log (-log h)) ^ 3 / log h ^ 2 := by
  set T := -log h with hTdef
  have hT : 121 ≤ T := by
    have := Real.log_le_log hh hh0; rw [Real.log_exp] at this; linarith
  have hT0 : 0 < T := by linarith
  have hhT : h = exp (-T) := by rw [hTdef, neg_neg, Real.exp_log hh]
  -- the dyadic scale `L = 2^K`, `T²/2 < L ≤ T²`
  set F := ⌊T ^ 2⌋₊ with hF
  have hF2 : 2 ≤ F := by
    rw [hF]; apply Nat.le_floor; push_cast; nlinarith
  set K := Nat.log 2 F with hK
  have hKpow : 2 ^ K ≤ F := Nat.pow_log_le_self 2 (by omega)
  have hKlt : F < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) F
  have hK1 : 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) (by simpa using hF2)
  have hLT : (2 : ℝ) ^ K ≤ T ^ 2 := by
    have : ((2 ^ K : ℕ) : ℝ) ≤ F := by exact_mod_cast hKpow
    push_cast at this; exact this.trans (Nat.floor_le (by positivity))
  have hTL : T ^ 2 < 2 * 2 ^ K := by
    have h1 : T ^ 2 < F + 1 := Nat.lt_floor_add_one _
    have h2 : ((F + 1 : ℕ) : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast hKlt
    push_cast at h2; rw [pow_succ] at h2; linarith
  -- the gap condition `4^K e^T h² < 1`, from `T⁴ < e^T`
  have hgap : 4 ^ K * exp T * h ^ 2 < 1 := by
    have e1 : (4 : ℝ) ^ K = (2 ^ K) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e2 : exp T * h ^ 2 = exp (-T) := by
      rw [hhT, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have h5 : T ^ 5 / 120 ≤ exp T := by
      have := Real.pow_div_factorial_le_exp T hT0.le 5
      simpa [Nat.factorial] using this
    have h4 : T ^ 4 < exp T := by
      have : T ^ 4 < T ^ 5 / 120 := by
        rw [lt_div_iff₀ (by norm_num), show T ^ 5 = T ^ 4 * T by ring]
        have := pow_pos hT0 4; nlinarith
      linarith
    have hL4 : ((2 : ℝ) ^ K) ^ 2 ≤ T ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hLT 2
      calc ((2 : ℝ) ^ K) ^ 2 ≤ (T ^ 2) ^ 2 := this
        _ = T ^ 4 := by ring
    rw [e1, mul_assoc, e2]
    have hexp : exp (-T) * exp T = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-T)
    have : ((2 : ℝ) ^ K) ^ 2 * exp (-T) < exp T * exp (-T) :=
      mul_lt_mul_of_pos_right (hL4.trans_lt h4) hpos
    linarith
  -- the finite-`N` bound along primes
  set B := 2 / (2 : ℝ) ^ K + 640 * (K + 1) ^ 3 / T ^ 2
  have hfreq : ∀ ε > 0, ∃ᶠ n in atTop, (nuQ n).real (Set.Icc (-h) h) ≤ B + ε := by
    intro ε hε
    rw [Nat.frequently_atTop_iff_infinite]
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    obtain ⟨P, hPge, hP⟩ := Nat.exists_infinite_primes (M + 2 ^ K + ⌈(2 : ℝ) ^ K / ε⌉₊ + 3)
    have hPodd : Odd P := hP.odd_of_ne_two (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
    have : Fact (n + 1).Prime := ⟨hP⟩
    have hKN : 2 ^ K ≤ n + 1 := by omega
    have hbound := nuQ_upper n hPodd (by linarith) hK1 hKN hgap
    have hεb : (2 : ℝ) ^ K / ((n : ℝ) + 1) ≤ ε := by
      have hc : (2 : ℝ) ^ K / ε ≤ ⌈(2 : ℝ) ^ K / ε⌉₊ := Nat.le_ceil _
      have hc' : ⌈(2 : ℝ) ^ K / ε⌉₊ ≤ n + 1 := by omega
      have : ((⌈(2 : ℝ) ^ K / ε⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc'
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hc
      nlinarith
    have : n ∈ {n | (nuQ n).real (Set.Icc (-h) h) ≤ B + ε} := by
      show _ ≤ B + ε; simp only [B] at *; linarith
    have := hM this
    omega
  have hmain := muA_real_Icc_le hh (by
    have : exp (-121 : ℝ) ≤ 4 := by
      have := Real.exp_le_one_iff.mpr (by norm_num : (-121 : ℝ) ≤ 0); linarith
    linarith) hfreq
  -- `B ≤ 17284 (1 + log T)³ / T²`
  have hlogT : 0 ≤ log T := Real.log_nonneg (by linarith)
  have hKlog : (K : ℝ) ≤ 3 * log T := by
    have h1 : (K : ℝ) * log 2 ≤ 2 * log T := by
      have := Real.log_le_log (by positivity) hLT
      rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    have h2 : (2 : ℝ) / 3 < log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hK0 : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hT2 : 0 < T ^ 2 := by positivity
  have hB : B ≤ 17284 * (1 + log T) ^ 3 / T ^ 2 := by
    have hA : 2 / (2 : ℝ) ^ K ≤ 4 / T ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hT2]; linarith
    have hC : (K + 1 : ℝ) ^ 3 ≤ 27 * (1 + log T) ^ 3 := by
      have : (K + 1 : ℝ) ≤ 3 * (1 + log T) := by linarith
      have h0 : (0 : ℝ) ≤ K + 1 := by positivity
      calc (K + 1 : ℝ) ^ 3 ≤ (3 * (1 + log T)) ^ 3 := pow_le_pow_left₀ h0 this 3
        _ = 27 * (1 + log T) ^ 3 := by ring
    have h1 : (1 : ℝ) ≤ (1 + log T) ^ 3 := one_le_pow₀ (by linarith)
    simp only [B]
    rw [show 17284 * (1 + log T) ^ 3 / T ^ 2 = 4 * (1 + log T) ^ 3 / T ^ 2 +
      640 * (27 * (1 + log T) ^ 3) / T ^ 2 by ring]
    have hX : 640 * ((K : ℝ) + 1) ^ 3 / T ^ 2 ≤ 640 * (27 * (1 + log T) ^ 3) / T ^ 2 := by
      gcongr
    have hY : 4 / T ^ 2 ≤ 4 * (1 + log T) ^ 3 / T ^ 2 := by
      gcongr; linarith
    linarith
  have hT2' : T ^ 2 = log h ^ 2 := by rw [hTdef]; ring
  rw [← hT2']
  linarith

/-- The upper bound in the form of `LogSqLowerBound`. -/
def LogUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
    muA.real (Set.Icc (-h) h) ≤ C * (1 + log (-log h)) ^ 3 / log h ^ 2

theorem logUpperBound : LogUpperBound :=
  ⟨17284, by norm_num, exp (-121), exp_pos _, fun _ hh hh0 => logUpperBound_explicit hh hh0.le⟩

end ThomUpper
