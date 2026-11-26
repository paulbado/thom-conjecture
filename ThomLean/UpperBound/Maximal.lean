import ThomLean.UpperBound.Moment

/-!
# Round 8, Task 2: the dyadic (Rademacher–Menshov) maximal inequality

Elementary dyadic proof, for an orthogonal family on a finite probability space given by
sums over a `Fintype Ω`. For `Y : ℕ → Ω → ℝ` set `S_a(m) = ∑_{j<m} Y_{a+j}` and define the dyadic
square function

`Q_0(a) = Y_a²`, `Q_{r+1}(a) = Q_r(a) + Q_r(a + 2^r) + S_a(2^{r+1})²`

(the sum of the squares of all dyadic block sums of `[a, a + 2^r)`).

* `psum_sq_le_Qd` (pointwise): `S_a(m)² ≤ (r+1) Q_r(a)` for every `m ≤ 2^r`.
* `sum_Qd_le`: if the `Y_j` (`a ≤ j < a + 2^r`) are orthogonal with `∑_ω Y_j² ≤ V`, then
  `∑_ω Q_r(a) ≤ (r+1) 2^r V`.
* `sum_max_psum_sq_le`: hence `∑_ω max_{m ≤ 2^r} S_a(m)² ≤ (r+1)² 2^r V`, and the Chebyshev bound
  `card_bad_le`: `#{ω : ∃ m ≤ 2^r, c < |S_a(m)|} · c² ≤ (r+1)² 2^r V`.
-/

noncomputable section

namespace ThomUpper

open Finset

variable {Ω : Type*} [Fintype Ω]
set_option linter.unusedSectionVars false

/-- Partial sums `S_a(m) = ∑_{j<m} Y_{a+j}`. -/
def psum (Y : ℕ → Ω → ℝ) (a m : ℕ) (ω : Ω) : ℝ := ∑ j ∈ range m, Y (a + j) ω

/-- The dyadic square function. -/
def Qd (Y : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, a, ω => Y a ω ^ 2
  | r + 1, a, ω => Qd Y r a ω + Qd Y r (a + 2 ^ r) ω + psum Y a (2 ^ (r + 1)) ω ^ 2

variable (Y : ℕ → Ω → ℝ)

lemma Qd_nonneg (r a : ℕ) (ω : Ω) : 0 ≤ Qd Y r a ω := by
  induction r generalizing a with
  | zero => exact sq_nonneg _
  | succ r ih => simp only [Qd]; have := ih a; have := ih (a + 2 ^ r); positivity

lemma psum_full_sq_le (r a : ℕ) (ω : Ω) : psum Y a (2 ^ r) ω ^ 2 ≤ Qd Y r a ω := by
  cases r with
  | zero => simp [psum, Qd]
  | succ r =>
    simp only [Qd]
    have := Qd_nonneg Y r a ω; have := Qd_nonneg Y r (a + 2 ^ r) ω
    linarith

lemma psum_add (a m m' : ℕ) (ω : Ω) :
    psum Y a (m + m') ω = psum Y a m ω + psum Y (a + m) m' ω := by
  simp only [psum, Finset.sum_range_add, add_assoc]

/-- **Pointwise dyadic bound**: `S_a(m)² ≤ (r+1) Q_r(a)` for `m ≤ 2^r`. -/
theorem psum_sq_le_Qd (r : ℕ) : ∀ a m, m ≤ 2 ^ r → ∀ ω : Ω,
    psum Y a m ω ^ 2 ≤ (r + 1) * Qd Y r a ω := by
  induction r with
  | zero =>
    intro a m hm ω
    interval_cases m
    · simp [psum, Qd_nonneg]
    · simp [psum, Qd]
  | succ r ih =>
    intro a m hm ω
    have h0 := Qd_nonneg Y r a ω
    have h1 := Qd_nonneg Y r (a + 2 ^ r) ω
    have hQ : Qd Y (r + 1) a ω = Qd Y r a ω + Qd Y r (a + 2 ^ r) ω +
        psum Y a (2 ^ (r + 1)) ω ^ 2 := rfl
    have h2 := sq_nonneg (psum Y a (2 ^ (r + 1)) ω)
    by_cases hm' : m ≤ 2 ^ r
    · have := ih a m hm' ω
      push_cast
      nlinarith
    · obtain ⟨m', rfl⟩ : ∃ m', m = 2 ^ r + m' := ⟨m - 2 ^ r, by omega⟩
      have hm'' : m' ≤ 2 ^ r := by rw [pow_succ] at hm; omega
      rw [psum_add]
      set A := psum Y a (2 ^ r) ω
      set B := psum Y (a + 2 ^ r) m' ω
      have hA : A ^ 2 ≤ Qd Y r a ω := psum_full_sq_le Y r a ω
      have hB : B ^ 2 ≤ (r + 1) * Qd Y r (a + 2 ^ r) ω := ih _ m' hm'' ω
      have hr : (0 : ℝ) < r + 1 := by positivity
      -- `(r+1)(A+B)² ≤ (r+1)(r+2)A² + (r+2)B²`, i.e. `0 ≤ ((r+1)A − B)²`
      have key : (r + 1) * (A + B) ^ 2 ≤ (r + 1) * (r + 2) * A ^ 2 + (r + 2) * B ^ 2 := by
        nlinarith [sq_nonneg ((r + 1) * A - B)]
      have e1 : (r + 1) * (r + 2) * A ^ 2 ≤ (r + 1) * (r + 2) * Qd Y r a ω :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have e2 : (r + 2) * B ^ 2 ≤ (r + 2) * ((r + 1) * Qd Y r (a + 2 ^ r) ω) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      have : (r + 1) * (A + B) ^ 2 ≤ (r + 1) * ((r + 2) * (Qd Y r a ω + Qd Y r (a + 2 ^ r) ω)) := by
        nlinarith
      have := le_of_mul_le_mul_left this hr
      rw [hQ]; push_cast; nlinarith

/-- Orthogonal expansion of a block sum. -/
lemma sum_psum_sq (a n : ℕ)
    (horth : ∀ i < n, ∀ j < n, i ≠ j → ∑ ω, Y (a + i) ω * Y (a + j) ω = 0) :
    ∑ ω, psum Y a n ω ^ 2 = ∑ j ∈ range n, ∑ ω, Y (a + j) ω ^ 2 := by
  simp only [psum, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · intro j hj hji
    exact horth i (mem_range.mp hi) j (mem_range.mp hj) (Ne.symm hji)
  · intro h; exact absurd hi h

/-- **Summed dyadic square function**: `∑_ω Q_r(a) ≤ (r+1) 2^r V`. -/
theorem sum_Qd_le {V : ℝ} (r : ℕ) : ∀ a,
    (∀ i < 2 ^ r, ∀ j < 2 ^ r, i ≠ j → ∑ ω, Y (a + i) ω * Y (a + j) ω = 0) →
    (∀ j < 2 ^ r, ∑ ω, Y (a + j) ω ^ 2 ≤ V) →
    ∑ ω, Qd Y r a ω ≤ (r + 1) * 2 ^ r * V := by
  induction r with
  | zero =>
    intro a _ hV
    simpa [Qd] using hV 0 (by norm_num)
  | succ r ih =>
    intro a horth hV
    have hpow : 2 ^ r < 2 ^ (r + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpow2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
    have h1 := ih a (fun i hi j hj hij => horth i (by omega) j (by omega) hij)
      (fun j hj => hV j (by omega))
    have h2 := ih (a + 2 ^ r)
      (fun i hi j hj hij => by
        have := horth (2 ^ r + i) (by omega) (2 ^ r + j) (by omega) (by omega)
        simpa [add_assoc] using this)
      (fun j hj => by simpa [add_assoc] using hV (2 ^ r + j) (by omega))
    have h3 : ∑ ω, psum Y a (2 ^ (r + 1)) ω ^ 2 ≤ 2 ^ (r + 1) * V := by
      rw [sum_psum_sq Y a _ horth]
      calc ∑ j ∈ range (2 ^ (r + 1)), ∑ ω, Y (a + j) ω ^ 2
          ≤ ∑ j ∈ range (2 ^ (r + 1)), V := Finset.sum_le_sum fun j hj => hV j (mem_range.mp hj)
        _ = 2 ^ (r + 1) * V := by simp
    simp only [Qd, Finset.sum_add_distrib]
    push_cast
    rw [show (2 : ℝ) ^ (r + 1) = 2 * 2 ^ r by ring] at h3 ⊢
    linarith

/-- **Chebyshev bound for the bad event**: `#{ω : ∃ m ≤ 2^r, c < |S_a(m)|} · c² ≤ (r+1)² 2^r V`. -/
theorem card_bad_le {V c : ℝ} (r a : ℕ)
    (horth : ∀ i < 2 ^ r, ∀ j < 2 ^ r, i ≠ j → ∑ ω, Y (a + i) ω * Y (a + j) ω = 0)
    (hV : ∀ j < 2 ^ r, ∑ ω, Y (a + j) ω ^ 2 ≤ V) [DecidablePred fun ω : Ω =>
      ∃ m ≤ 2 ^ r, c < |psum Y a m ω|] (hc : 0 ≤ c) :
    (#{ω | ∃ m ≤ 2 ^ r, c < |psum Y a m ω|} : ℝ) * c ^ 2 ≤ (r + 1) ^ 2 * 2 ^ r * V := by
  have hQ := sum_Qd_le Y r a horth hV
  have hpt : ∀ ω ∈ ({ω | ∃ m ≤ 2 ^ r, c < |psum Y a m ω|} : Finset Ω),
      c ^ 2 ≤ (r + 1) * Qd Y r a ω := by
    intro ω hω
    obtain ⟨m, hm, hcm⟩ := (Finset.mem_filter.mp hω).2
    have := psum_sq_le_Qd Y r a m hm ω
    have : c ^ 2 ≤ psum Y a m ω ^ 2 := by
      rw [← sq_abs (psum Y a m ω)]; exact pow_le_pow_left₀ hc hcm.le 2
    linarith
  calc (#{ω | ∃ m ≤ 2 ^ r, c < |psum Y a m ω|} : ℝ) * c ^ 2
      = ∑ ω ∈ ({ω | ∃ m ≤ 2 ^ r, c < |psum Y a m ω|} : Finset Ω), c ^ 2 := by simp
    _ ≤ ∑ ω ∈ ({ω | ∃ m ≤ 2 ^ r, c < |psum Y a m ω|} : Finset Ω), (r + 1) * Qd Y r a ω :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ ω, (r + 1) * Qd Y r a ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun ω _ _ => mul_nonneg (by positivity) (Qd_nonneg Y r a ω)
    _ = (r + 1) * ∑ ω, Qd Y r a ω := by rw [Finset.mul_sum]
    _ ≤ (r + 1) * ((r + 1) * 2 ^ r * V) := by gcongr
    _ = (r + 1) ^ 2 * 2 ^ r * V := by ring

end ThomUpper
