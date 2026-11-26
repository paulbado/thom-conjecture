import ThomLean.ZeroLevel.Chain

/-!
# Explicit zero-energy quasimodes of the chain operator

Fix `p, t ∈ ℤ/N`, a start `s ∈ ℕ` and a length `M`. Put `x_j = s + 2j`, `c_j = c(x_j)` (even bonds)
and `d_j = c(x_j + 1)` (odd bonds). The vector

`ξ = ∑_{j=0}^{M} u_j δ_{x_j}`, `u_0 = 1`, `u_{j+1} = -c_j u_j / conj(d_j)`,

satisfies `H ξ = conj(c(s-1)) u_0 δ_{s-1} + c_M u_M δ_{s+2M+1}` (`chainH_qmXi`): every odd interior
residual cancels and only the two exterior boundary sites survive. Hence

`‖H ξ‖² ≤ 8 (|u_0|² + |u_M|²)`.

If `|c_j| ≥ (3/2)|d_j|` for the first `m` steps and `|c_j| ≤ (2/3)|d_j|` for the last `m` steps,
then `|u_0|², |u_M|² ≤ (4/9)^m ‖ξ‖²` and so `‖H ξ‖² ≤ 16 (4/9)^m ‖ξ‖²` (`qm_bound`).
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomExistence ThomNoAtoms Finset ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- Even site `x_j = s + 2j`. -/
def xs (N : ℕ) (s j : ℕ) : ZMod N := ((s + 2 * j : ℕ) : ZMod N)

/-- Odd site `y_j = s + 2j + 1`. -/
def ys (N : ℕ) (s j : ℕ) : ZMod N := ((s + 2 * j + 1 : ℕ) : ZMod N)

/-- Amplitudes of the quasimode. -/
def qmU (p t : ZMod N) (s : ℕ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => -(bond p t (xs N s j) * qmU p t s j) / conj (bond p t (ys N s j))

/-- The quasimode `ξ = ∑_{j ≤ M} u_j δ_{s+2j}`. -/
def qmXi (p t : ZMod N) (s M : ℕ) (l : ZMod N) : ℂ :=
  ∑ j ∈ range (M + 1), if l = xs N s j then qmU p t s j else 0

lemma ys_eq (s j : ℕ) : ys N s j = xs N s j + 1 := by simp only [xs, ys]; push_cast; ring

lemma xs_succ_sub (s j : ℕ) : xs N s (j + 1) - 1 = ys N s j := by
  simp only [xs, ys]; push_cast; ring

/-- **Boundary residual identity.** -/
theorem chainH_qmXi (p t : ZMod N) (s M : ℕ) (hco : ∀ j < M, bond p t (ys N s j) ≠ 0)
    (l : ZMod N) :
    chainH p t (qmXi p t s M) l =
      (if l = xs N s 0 - 1 then conj (bond p t (xs N s 0 - 1)) * qmU p t s 0 else 0) +
      (if l = ys N s M then bond p t (xs N s M) * qmU p t s M else 0) := by
  have A : ∀ j, bond p t (l - 1) * (if l - 1 = xs N s j then qmU p t s j else 0) =
      if l = ys N s j then bond p t (xs N s j) * qmU p t s j else 0 := by
    intro j
    rw [ys_eq]
    by_cases h : l = xs N s j + 1
    · simp [h]
    · have : l - 1 ≠ xs N s j := fun h' => h (by rw [← h']; ring)
      rw [if_neg this, if_neg h, mul_zero]
  have B : ∀ j, conj (bond p t l) * (if l + 1 = xs N s j then qmU p t s j else 0) =
      if l = xs N s j - 1 then conj (bond p t (xs N s j - 1)) * qmU p t s j else 0 := by
    intro j
    by_cases h : l = xs N s j - 1
    · simp [h]
    · have : l + 1 ≠ xs N s j := fun h' => h (by rw [← h']; ring)
      rw [if_neg this, if_neg h, mul_zero]
  simp only [chainH, qmXi, Finset.mul_sum, A, B]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp_rw [xs_succ_sub]
  have hcancel : ∑ j ∈ range M, (if l = ys N s j then bond p t (xs N s j) * qmU p t s j else 0) +
      ∑ j ∈ range M, (if l = ys N s j then conj (bond p t (ys N s j)) * qmU p t s (j + 1)
        else 0) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := hco j (Finset.mem_range.mp hj)
    have hc : conj (bond p t (ys N s j)) ≠ 0 := (map_ne_zero _).mpr hj'
    split_ifs
    · rw [qmU]; field_simp; ring
    · simp
  linear_combination hcancel

/-! ### Norm estimates -/

lemma normSq_add_le (z w : ℂ) : Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  have h1 := Complex.normSq_add z w
  have h2 := Complex.normSq_sub z w
  have h3 := Complex.normSq_nonneg (z - w)
  linarith

lemma normSq_bond_le (p t n : ZMod N) : Complex.normSq (bond p t n) ≤ 4 := by
  have h1 : ‖ψ (t + p * (n + 1))‖ = 1 := AddChar.norm_apply _ _
  have h2 : ‖bond p t n‖ ≤ 2 := by
    calc ‖bond p t n‖ ≤ ‖(1 : ℂ)‖ + ‖ψ (t + p * (n + 1))‖ := norm_add_le _ _
      _ = 2 := by rw [h1]; norm_num
  rw [← Complex.sq_norm]
  nlinarith [norm_nonneg (bond p t n)]

lemma nrm_ite_add (A B : ZMod N) (α β : ℂ) :
    nrm (fun l => (if l = A then α else 0) + (if l = B then β else 0)) ≤
      2 * Complex.normSq α + 2 * Complex.normSq β := by
  calc nrm (fun l => (if l = A then α else 0) + (if l = B then β else 0))
      ≤ ∑ l, (2 * Complex.normSq (if l = A then α else 0) +
          2 * Complex.normSq (if l = B then β else 0)) :=
        Finset.sum_le_sum fun l _ => normSq_add_le _ _
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [apply_ite Complex.normSq]

/-- Sites `x_j`, `j ≤ M`, are distinct when `s + 2M < N`. -/
lemma xs_inj {s M i j : ℕ} (hsM : s + 2 * M < N) (hi : i ≤ M) (hj : j ≤ M)
    (h : xs N s i = xs N s j) : i = j := by
  simp only [xs] at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

lemma qmXi_xs (p t : ZMod N) {s M j : ℕ} (hsM : s + 2 * M < N) (hj : j ≤ M) :
    qmXi p t s M (xs N s j) = qmU p t s j := by
  rw [qmXi, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [if_neg]
    exact fun h => hij (xs_inj hsM hi' hj h.symm)
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h

lemma normSq_qmU_le (p t : ZMod N) {s M j : ℕ} (hsM : s + 2 * M < N) (hj : j ≤ M) :
    Complex.normSq (qmU p t s j) ≤ nrm (qmXi p t s M) := by
  rw [← qmXi_xs p t hsM hj]
  exact Finset.single_le_sum (f := fun l => Complex.normSq (qmXi p t s M l))
    (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ _)

lemma normSq_qmU_succ (p t : ZMod N) (s j : ℕ) (h : bond p t (ys N s j) ≠ 0) :
    Complex.normSq (qmU p t s (j + 1)) * Complex.normSq (bond p t (ys N s j)) =
      Complex.normSq (bond p t (xs N s j)) * Complex.normSq (qmU p t s j) := by
  rw [qmU, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_conj]
  have : Complex.normSq (bond p t (ys N s j)) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  field_simp

/-- Growth over the first `m` steps. -/
lemma qmU_growth (p t : ZMod N) (s : ℕ) {m : ℕ}
    (hfirst : ∀ j < m, (9 / 4) * Complex.normSq (bond p t (ys N s j)) ≤
      Complex.normSq (bond p t (xs N s j)))
    (hco : ∀ j < m, bond p t (ys N s j) ≠ 0) :
    (9 / 4 : ℝ) ^ m * Complex.normSq (qmU p t s 0) ≤ Complex.normSq (qmU p t s m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun j hj => hfirst j (by omega)) (fun j hj => hco j (by omega))
    have hd : 0 < Complex.normSq (bond p t (ys N s m)) :=
      Complex.normSq_pos.mpr (hco m (by omega))
    have hrec := normSq_qmU_succ p t s m (hco m (by omega))
    have hf := hfirst m (by omega)
    have h0 := Complex.normSq_nonneg (qmU p t s m)
    -- `|u_{m+1}|² d = c |u_m|² ≥ (9/4) d |u_m|²`
    have : (9 / 4) * Complex.normSq (qmU p t s m) ≤ Complex.normSq (qmU p t s (m + 1)) := by
      have h1 : (9 / 4) * Complex.normSq (qmU p t s m) * Complex.normSq (bond p t (ys N s m)) ≤
          Complex.normSq (qmU p t s (m + 1)) * Complex.normSq (bond p t (ys N s m)) := by
        rw [hrec]; nlinarith
      exact le_of_mul_le_mul_right h1 hd
    calc (9 / 4 : ℝ) ^ (m + 1) * Complex.normSq (qmU p t s 0)
        = (9 / 4) * ((9 / 4) ^ m * Complex.normSq (qmU p t s 0)) := by ring
      _ ≤ (9 / 4) * Complex.normSq (qmU p t s m) := by linarith
      _ ≤ _ := this

/-- Decay over the last `m` steps. -/
lemma qmU_decay (p t : ZMod N) (s : ℕ) (k : ℕ) {m : ℕ}
    (hlast : ∀ j, k ≤ j → j < k + m → Complex.normSq (bond p t (xs N s j)) ≤
      (4 / 9) * Complex.normSq (bond p t (ys N s j)))
    (hco : ∀ j, k ≤ j → j < k + m → bond p t (ys N s j) ≠ 0) :
    Complex.normSq (qmU p t s (k + m)) ≤ (4 / 9 : ℝ) ^ m * Complex.normSq (qmU p t s k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun j h1 h2 => hlast j h1 (by omega)) (fun j h1 h2 => hco j h1 (by omega))
    have hd : 0 < Complex.normSq (bond p t (ys N s (k + m))) :=
      Complex.normSq_pos.mpr (hco (k + m) (by omega) (by omega))
    have hrec := normSq_qmU_succ p t s (k + m) (hco (k + m) (by omega) (by omega))
    have hl := hlast (k + m) (by omega) (by omega)
    have h0 := Complex.normSq_nonneg (qmU p t s (k + m))
    have : Complex.normSq (qmU p t s (k + m + 1)) ≤ (4 / 9) * Complex.normSq (qmU p t s (k + m)) := by
      have h1 : Complex.normSq (qmU p t s (k + m + 1)) * Complex.normSq (bond p t (ys N s (k + m))) ≤
          (4 / 9) * Complex.normSq (qmU p t s (k + m)) *
            Complex.normSq (bond p t (ys N s (k + m))) := by
        rw [hrec]; nlinarith
      exact le_of_mul_le_mul_right h1 hd
    calc Complex.normSq (qmU p t s (k + (m + 1))) = Complex.normSq (qmU p t s (k + m + 1)) := by
          rw [← add_assoc]
      _ ≤ (4 / 9) * Complex.normSq (qmU p t s (k + m)) := this
      _ ≤ (4 / 9) * ((4 / 9) ^ m * Complex.normSq (qmU p t s k)) := by gcongr
      _ = _ := by ring

/-- **Quasimode estimate**: `‖H ξ‖² ≤ 16 (4/9)^m ‖ξ‖²` and `‖ξ‖² ≥ 1`. -/
theorem qm_bound (p t : ZMod N) {s M m : ℕ} (hsM : s + 2 * M < N) (hmM : m ≤ M)
    (hco : ∀ j < M, bond p t (ys N s j) ≠ 0)
    (hfirst : ∀ j < m, (9 / 4) * Complex.normSq (bond p t (ys N s j)) ≤
      Complex.normSq (bond p t (xs N s j)))
    (hlast : ∀ j, M - m ≤ j → j < M → Complex.normSq (bond p t (xs N s j)) ≤
      (4 / 9) * Complex.normSq (bond p t (ys N s j))) :
    nrm (chainH p t (qmXi p t s M)) ≤ 16 * (4 / 9 : ℝ) ^ m * nrm (qmXi p t s M) ∧
      1 ≤ nrm (qmXi p t s M) := by
  have hX := nrm_nonneg (qmXi p t s M)
  have hu0 : Complex.normSq (qmU p t s 0) = 1 := by simp [qmU]
  have hres : chainH p t (qmXi p t s M) = fun l =>
      (if l = xs N s 0 - 1 then conj (bond p t (xs N s 0 - 1)) * qmU p t s 0 else 0) +
      (if l = ys N s M then bond p t (xs N s M) * qmU p t s M else 0) :=
    funext (chainH_qmXi p t s M hco)
  have h1 : nrm (chainH p t (qmXi p t s M)) ≤
      8 * Complex.normSq (qmU p t s 0) + 8 * Complex.normSq (qmU p t s M) := by
    rw [hres]
    refine (nrm_ite_add _ _ _ _).trans ?_
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj]
    have := normSq_bond_le p t (xs N s 0 - 1)
    have := normSq_bond_le p t (xs N s M)
    have := Complex.normSq_nonneg (qmU p t s 0)
    have := Complex.normSq_nonneg (qmU p t s M)
    nlinarith
  -- `|u_0|² ≤ (4/9)^m ‖ξ‖²`
  have hq : (0 : ℝ) < (9 / 4) ^ m := by positivity
  have hinv : (4 / 9 : ℝ) ^ m * (9 / 4) ^ m = 1 := by rw [← mul_pow]; norm_num
  have h2 : Complex.normSq (qmU p t s 0) ≤ (4 / 9 : ℝ) ^ m * nrm (qmXi p t s M) := by
    have hg := qmU_growth p t s (m := m) hfirst (fun j hj => hco j (by omega))
    have hm := normSq_qmU_le p t (j := m) hsM hmM
    calc Complex.normSq (qmU p t s 0)
        = (4 / 9 : ℝ) ^ m * ((9 / 4) ^ m * Complex.normSq (qmU p t s 0)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (4 / 9 : ℝ) ^ m * nrm (qmXi p t s M) := by gcongr; exact hg.trans hm
  have h3 : Complex.normSq (qmU p t s M) ≤ (4 / 9 : ℝ) ^ m * nrm (qmXi p t s M) := by
    have hd := qmU_decay p t s (M - m) (m := m)
      (fun j h1 h2 => hlast j h1 (by omega)) (fun j h1 h2 => hco j (by omega))
    rw [Nat.sub_add_cancel hmM] at hd
    have hk := normSq_qmU_le p t (j := M - m) hsM (Nat.sub_le _ _)
    calc Complex.normSq (qmU p t s M) ≤ (4 / 9 : ℝ) ^ m * Complex.normSq (qmU p t s (M - m)) := hd
      _ ≤ _ := by gcongr
  refine ⟨by nlinarith, ?_⟩
  rw [← hu0]
  exact normSq_qmU_le p t (j := 0) hsM (Nat.zero_le _)

/-! ### Supports -/

lemma qmXi_support (p t : ZMod N) (s M : ℕ) {l : ZMod N} (hl : qmXi p t s M l ≠ 0) :
    ∃ j ≤ M, l = xs N s j := by
  by_contra h
  push Not at h
  apply hl
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg (h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]

end ThomZeroLevel
