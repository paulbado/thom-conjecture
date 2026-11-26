import ThomLean.Heisenberg.Isoperimetric
import ThomLean.Heisenberg.Moments
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.IntervalCases

/-!
# The exact moment-matching threshold `N_Q = 2⌈2√Q⌉`

Bado–Pittet, Theorem 1.1 and Lemma 3.3.

* `kQ Q` is the least `k` with `4Q ≤ k²`; `kQ_eq_ceil` identifies it with `⌈2√Q⌉`.
* `NQ Q = 2 * kQ Q`.
* `moment_eq_fluxMoment` : for `n < N_Q` the rational-flux moments and the canonical moments
  agree (unconditional, combinatorial form of eq. (4)).
* `exists_walk_area_eq` : there is a closed walk of length exactly `N_Q` with area `Q`
  (explicit polyomino boundary, Lemma 3.3).
* `moment_lt_fluxMoment_NQ` : at `n = N_Q` the moments differ (sharpness of the threshold).
-/

namespace ThomHeisenberg

open Step

lemma exists_sq_ge (Q : ℕ) : ∃ k : ℕ, 4 * Q ≤ k ^ 2 :=
  ⟨2 * Q + 1, by nlinarith [Nat.zero_le Q]⟩

/-- `kQ Q = min {k : 4Q ≤ k²}`. -/
def kQ (Q : ℕ) : ℕ := Nat.find (exists_sq_ge Q)

lemma kQ_spec (Q : ℕ) : 4 * Q ≤ kQ Q ^ 2 := Nat.find_spec (exists_sq_ge Q)

lemma lt_of_lt_kQ {Q k : ℕ} (hk : k < kQ Q) : k ^ 2 < 4 * Q := by
  have := Nat.find_min (exists_sq_ge Q) hk
  omega

lemma kQ_le {Q k : ℕ} (hk : 4 * Q ≤ k ^ 2) : kQ Q ≤ k := Nat.find_min' _ hk

/-- `kQ Q = ⌈2√Q⌉`. -/
theorem kQ_eq_ceil (Q : ℕ) : kQ Q = ⌈2 * Real.sqrt Q⌉₊ := by
  have key : ∀ k : ℕ, (2 * Real.sqrt Q ≤ k ↔ 4 * Q ≤ k ^ 2) := by
    intro k
    have hs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
    have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt (by positivity)
    constructor
    · intro h
      have : (2 * Real.sqrt Q) ^ 2 ≤ (k : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) h 2
      have : (4 * Q : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      exact_mod_cast this
    · intro h
      have h' : (4 * Q : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast h
      nlinarith [sq_nonneg (2 * Real.sqrt Q - k), sq_nonneg (2 * Real.sqrt Q + k),
        Nat.cast_nonneg (α := ℝ) k]
  apply le_antisymm
  · apply kQ_le
    exact (key _).1 (Nat.le_ceil _)
  · rw [Nat.ceil_le]
    exact (key _).2 (kQ_spec Q)

/-- The threshold `N_Q = 2⌈2√Q⌉`. -/
def NQ (Q : ℕ) : ℕ := 2 * kQ Q

theorem NQ_eq (Q : ℕ) : NQ Q = 2 * ⌈2 * Real.sqrt Q⌉₊ := by rw [NQ, kQ_eq_ceil]

/-- Below the threshold, a closed walk with area divisible by `Q` has zero area. -/
theorem area_eq_zero_of_lt_NQ {Q : ℕ} (_hQ : 0 < Q) (w : List Step) (hw : IsClosed w)
    (hn : w.length < NQ Q) (hd : (Q : ℤ) ∣ area w) : area w = 0 := by
  have hlen := hw.length_eq
  set r := cnt R w
  set s := cnt U w
  have hrs : r + s < kQ Q := by unfold NQ at hn; omega
  have h1 : (r + s) ^ 2 < 4 * Q := lt_of_lt_kQ hrs
  have h2 : r * s < Q := by nlinarith [sq_nonneg ((r : ℤ) - s)]
  have h3 : |area w| < Q := by
    have := abs_area_le w hw
    have : ((r * s : ℕ) : ℤ) < Q := by exact_mod_cast h2
    push_cast at this
    linarith
  exact Int.eq_zero_of_abs_lt_dvd hd h3

/-- **Exact moment matching below `N_Q`** (Bado–Pittet, eq. (4), combinatorial form):
for `n < N_Q`, `m_n^{(Q)} = m_n`. -/
theorem moment_eq_fluxMoment {Q : ℕ} (hQ : 0 < Q) {n : ℕ} (hn : n < NQ Q) :
    fluxMoment Q n = moment n := by
  unfold fluxMoment moment modAreaWalks zeroAreaWalks
  congr 1
  apply Finset.filter_congr
  intro w _
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨hc, area_eq_zero_of_lt_NQ hQ _ hc (by simpa [wordList] using hn) hd⟩
  · rintro ⟨hc, h0⟩
    exact ⟨hc, by rw [h0]; exact dvd_zero _⟩

/-! ### The extremal polyomino walk -/

lemma areaFrom_replicate' (x₀ : ℤ) (t : Step) (m : ℕ) :
    areaFrom x₀ (List.replicate m t) = m * (x₀ * t.dy) := by
  induction m generalizing x₀ with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, areaFrom_cons, ih]
    cases t <;> simp [Step.dx, Step.dy] <;> ring

lemma xEnd_replicate (t : Step) (m : ℕ) : xEnd (List.replicate m t) = m * t.dx := by
  simp [xEnd, List.sum_replicate]

lemma yEnd_replicate (t : Step) (m : ℕ) : yEnd (List.replicate m t) = m * t.dy := by
  simp [yEnd, List.sum_replicate]

lemma xEnd_append (v w : List Step) : xEnd (v ++ w) = xEnd v + xEnd w := by simp [xEnd]
lemma yEnd_append (v w : List Step) : yEnd (v ++ w) = yEnd v + yEnd w := by simp [yEnd]

/-- Boundary of an `r × s` rectangle with the `d` rightmost cells of the top row removed,
traversed counterclockwise: `R^r U^(s-1) L^d U L^(r-d) D^s`. -/
def polyWord (r s d : ℕ) : List Step :=
  List.replicate r R ++ List.replicate (s - 1) U ++ List.replicate d L ++ [U] ++
    List.replicate (r - d) L ++ List.replicate s D

lemma polyWord_length (r s d : ℕ) (hs : 1 ≤ s) (hd : d ≤ r) :
    (polyWord r s d).length = 2 * (r + s) := by
  simp [polyWord]; omega

lemma polyWord_closed (r s d : ℕ) (hs : 1 ≤ s) (hd : d ≤ r) : IsClosed (polyWord r s d) := by
  constructor
  · simp only [polyWord, xEnd_append, xEnd_replicate, xEnd_cons, xEnd_nil]
    simp [Step.dx]; push_cast [Nat.cast_sub hd]; ring
  · simp only [polyWord, yEnd_append, yEnd_replicate, yEnd_cons, yEnd_nil]
    simp [Step.dy]; push_cast [Nat.cast_sub hs]; ring

lemma polyWord_area (r s d : ℕ) (hs : 1 ≤ s) (hd : d ≤ r) :
    area (polyWord r s d) = (r : ℤ) * s - d := by
  simp only [area, polyWord, areaFrom_append, areaFrom_replicate', xEnd_append, xEnd_replicate,
    areaFrom_cons, areaFrom_nil, xEnd_cons, xEnd_nil]
  simp [Step.dx, Step.dy]
  push_cast [Nat.cast_sub hd, Nat.cast_sub hs]
  ring

/-- **Lemma 3.3 (existence)**: for `Q ≥ 1` there is a closed walk of length `N_Q` and
algebraic area exactly `Q`. -/
theorem exists_walk_area_eq {Q : ℕ} (hQ : 0 < Q) :
    ∃ w : List Step, IsClosed w ∧ w.length = NQ Q ∧ area w = Q := by
  set k := kQ Q with hk
  have hspec : 4 * Q ≤ k ^ 2 := kQ_spec Q
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> omega
  have hmin : (k - 1) ^ 2 < 4 * Q := lt_of_lt_kQ (by omega)
  -- choose `r = ⌈k/2⌉`, `s = ⌊k/2⌋`
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' k
  · -- k = 2t, r = s = t
    have ht1 : 1 ≤ t := by omega
    have hQle : Q ≤ t * t := by rw [ht] at hspec; nlinarith
    have hlow : t * t - Q < t := by
      have : (2 * t - 1) ^ 2 < 4 * Q := by rw [← ht]; exact hmin
      have h' : ((2 * t - 1 : ℕ) : ℤ) ^ 2 < 4 * Q := by exact_mod_cast this
      push_cast [show 1 ≤ 2 * t by omega] at h'
      have : (t : ℤ) * t - Q < t := by nlinarith
      omega
    refine ⟨polyWord t t (t * t - Q), polyWord_closed _ _ _ ht1 (by omega), ?_, ?_⟩
    · rw [polyWord_length _ _ _ ht1 (by omega), NQ, ← hk, ht]; ring
    · rw [polyWord_area _ _ _ ht1 (by omega)]; push_cast [hQle]; ring
  · -- k = 2t+1, r = t+1, s = t
    have ht1 : 1 ≤ t := by omega
    have hQle : Q ≤ (t + 1) * t := by rw [ht] at hspec; nlinarith
    have hlow : (t + 1) * t - Q ≤ t + 1 := by
      have : (2 * t) ^ 2 < 4 * Q := by
        have := hmin; rwa [ht, show 2 * t + 1 - 1 = 2 * t by omega] at this
      have : t * t < Q := by nlinarith
      have : (t + 1) * t - Q < t := by
        have h3 : (t + 1) * t = t * t + t := by ring
        omega
      omega
    refine ⟨polyWord (t + 1) t ((t + 1) * t - Q), polyWord_closed _ _ _ ht1 hlow, ?_, ?_⟩
    · rw [polyWord_length _ _ _ ht1 hlow, NQ, ← hk, ht]; ring
    · rw [polyWord_area _ _ _ ht1 hlow]; push_cast [hQle]; ring

/-- Transport a list of known length to a tuple. -/
def toTuple (w : List Step) {n : ℕ} (h : w.length = n) : Fin n → Step :=
  fun i => w.get (i.cast h.symm)

lemma wordList_toTuple (w : List Step) {n : ℕ} (h : w.length = n) :
    wordList (toTuple w h) = w := by
  subst h
  apply List.ext_get
  · simp [wordList]
  · intro i h1 h2; simp [wordList, toTuple]

/-- **Sharpness of `N_Q`** (Bado–Pittet, Theorem 1.1): at `n = N_Q` the rational-flux moment
strictly exceeds the canonical moment. -/
theorem moment_lt_fluxMoment_NQ {Q : ℕ} (hQ : 0 < Q) : moment (NQ Q) < fluxMoment Q (NQ Q) := by
  obtain ⟨w, hc, hl, ha⟩ := exists_walk_area_eq hQ
  apply Finset.card_lt_card
  refine ⟨zeroAreaWalks_subset Q _, fun hsub => ?_⟩
  have hmem : toTuple w hl ∈ modAreaWalks Q (NQ Q) := by
    simp only [modAreaWalks, Finset.mem_filter, Finset.mem_univ, true_and, wordList_toTuple]
    exact ⟨hc, by rw [ha]⟩
  have := hsub hmem
  simp only [zeroAreaWalks, Finset.mem_filter, Finset.mem_univ, true_and,
    wordList_toTuple] at this
  rw [ha] at this
  have : (Q : ℤ) = 0 := this.2
  omega

end ThomHeisenberg
