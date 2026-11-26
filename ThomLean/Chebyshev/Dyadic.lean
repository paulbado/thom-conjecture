import ThomLean.Chebyshev.Duality

/-!
# The dyadic entropy criterion

For a finite measure `ν` on `ℝ`, carried by `[0,1)`, and the dyadic cells
`I_{k,j} = [j/2^k, (j+1)/2^k)`, set `m_{k,j} = ν(I_{k,j})`,

* `H_k = ∑_j m_{k,j} log(2^k m_{k,j})` (`dyEnt`, with `0 log 0 = 0`, Mathlib's convention),
* `D_k = ∑_j (m_{k+1,2j} - m_{k+1,2j+1})² / m_{k,j}` (`dyDisc`, a zero-mass term is `0`).

Results:

* `dyEnt_succ_sub` : `H_{k+1} - H_k = ∑_j [a log(2a/m) + b log(2b/m)]` with `a, b` the masses of
  the two halves of a cell of mass `m` (the **entropy increment identity**),
* `dyEnt_succ_sub_nonneg`, `dyEnt_succ_sub_le` : `0 ≤ H_{k+1} - H_k ≤ D_k`,
* `ac_of_dyEnt_bounded` : `sup_k H_k < ∞ ⇒ ν ≪ Lebesgue`,
* `ac_of_summable_dyDisc` : `∑_k D_k < ∞ ⇒ ν ≪ Lebesgue`.
-/

noncomputable section

namespace ThomDyadic

open MeasureTheory Real Set Filter Topology

/-- Dyadic cell `[j/2^k, (j+1)/2^k)`. -/
def cell (k j : ℕ) : Set ℝ := Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)

lemma measurableSet_cell (k j : ℕ) : MeasurableSet (cell k j) := measurableSet_Ico

lemma cell_split (k j : ℕ) : cell k j = cell (k + 1) (2 * j) ∪ cell (k + 1) (2 * j + 1) := by
  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have e1 : ((2 * j : ℕ) : ℝ) / 2 ^ (k + 1) = (j : ℝ) / 2 ^ k := by
    rw [pow_succ]; push_cast; field_simp
  have e2 : ((2 * j + 1 : ℕ) : ℝ) + 1 = (2 * j + 1 : ℕ) + 1 := rfl
  have e3 : (((2 * j + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((j : ℝ) + 1) / 2 ^ k := by
    rw [pow_succ]; push_cast; field_simp; ring
  unfold cell
  rw [e1, show (((2 * j : ℕ) : ℝ) + 1) = ((2 * j + 1 : ℕ) : ℝ) by push_cast; ring, e3]
  refine (Ico_union_Ico_eq_Ico ?_ ?_).symm
  · rw [← e1, div_le_div_iff_of_pos_right h2]; push_cast; linarith
  · rw [← e3, div_le_div_iff_of_pos_right h2]; push_cast; linarith

lemma cell_disjoint_halves (k j : ℕ) :
    Disjoint (cell (k + 1) (2 * j)) (cell (k + 1) (2 * j + 1)) := by
  unfold cell
  rw [show (((2 * j : ℕ) : ℝ) + 1) = ((2 * j + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Ico_disjoint_Ico_same

lemma cell_pairwiseDisjoint (k : ℕ) (s : Finset ℕ) : PairwiseDisjoint (↑s) (cell k) := by
  intro i _ j _ hij
  unfold cell
  rw [Function.onFun, Set.Ico_disjoint_Ico]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rcases lt_or_gt_of_ne hij with h | h
  · have : ((i : ℝ) + 1) / 2 ^ k ≤ (j : ℝ) / 2 ^ k := by
      rw [div_le_div_iff_of_pos_right h2]; exact_mod_cast h
    exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
  · have : ((j : ℝ) + 1) / 2 ^ k ≤ (i : ℝ) / 2 ^ k := by
      rw [div_le_div_iff_of_pos_right h2]; exact_mod_cast h
    exact (min_le_right _ _).trans (this.trans (le_max_left _ _))

lemma volume_real_cell (k j : ℕ) : volume.real (cell k j) = 1 / 2 ^ k := by
  unfold cell
  rw [Real.volume_real_Ico_of_le (by gcongr; linarith)]
  ring

/-- Every point of `[0,1)` lies in the cell `⌊2^k x⌋`. -/
lemma mem_cell_floor (k : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    ⌊2 ^ k * x⌋₊ < 2 ^ k ∧ x ∈ cell k ⌊2 ^ k * x⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hy : 0 ≤ 2 ^ k * x := mul_nonneg h2.le hx.1
  refine ⟨?_, ?_, ?_⟩
  · have : (⌊2 ^ k * x⌋₊ : ℝ) < 2 ^ k :=
      (Nat.floor_le hy).trans_lt (by nlinarith [hx.2])
    exact_mod_cast this
  · rw [div_le_iff₀ h2]; linarith [Nat.floor_le hy]
  · rw [lt_div_iff₀ h2]; linarith [Nat.lt_floor_add_one (2 ^ k * x)]

/-- Points of a cell are within `2^{-k}` of each other. -/
lemma dist_lt_of_mem_cell {k j : ℕ} {x y : ℝ} (hx : x ∈ cell k j) (hy : y ∈ cell k j) :
    dist x y < 1 / 2 ^ k := by
  unfold cell at hx hy
  rw [Real.dist_eq, abs_lt]
  have : ((j : ℝ) + 1) / 2 ^ k - (j : ℝ) / 2 ^ k = 1 / 2 ^ k := by ring
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-! ### Masses, entropy, discrepancy -/

variable (ν : Measure ℝ)

/-- Mass of a dyadic cell. -/
def mass (k j : ℕ) : ℝ := ν.real (cell k j)

lemma mass_nonneg (k j : ℕ) : 0 ≤ mass ν k j := measureReal_nonneg

lemma mass_split [IsFiniteMeasure ν] (k j : ℕ) :
    mass ν k j = mass ν (k + 1) (2 * j) + mass ν (k + 1) (2 * j + 1) := by
  unfold mass
  rw [cell_split, measureReal_union (cell_disjoint_halves k j) (measurableSet_cell _ _)]

/-- Dyadic entropy `H_k = ∑_j m_{k,j} log(2^k m_{k,j})`. -/
def dyEnt (k : ℕ) : ℝ := ∑ j ∈ Finset.range (2 ^ k), mass ν k j * log (2 ^ k * mass ν k j)

/-- Dyadic discrepancy `D_k = ∑_j (m_{k+1,2j} - m_{k+1,2j+1})² / m_{k,j}`. -/
def dyDisc (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ k), (mass ν (k + 1) (2 * j) - mass ν (k + 1) (2 * j + 1)) ^ 2 /
    mass ν k j

lemma dyDisc_nonneg (k : ℕ) : 0 ≤ dyDisc ν k :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (mass_nonneg ν _ _)

/-- The two-point Kullback–Leibler term `a log(2a/m) + b log(2b/m)`. -/
def klTerm (a b : ℝ) : ℝ := a * log (2 * a / (a + b)) + b * log (2 * b / (a + b))

lemma sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- `x log(Kx) - x log(Ky) = x log(x/y)` for `x ≥ 0`, `y, K > 0` (both sides `0` if `x = 0`). -/
lemma mul_log_sub (x y K : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hK : 0 < K) :
    x * log (K * x) - x * log (K * y) = x * log (x / y) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [← mul_sub, ← log_div (by positivity) (by positivity)]
    congr 2; field_simp

lemma klTerm_eq (a b K : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 < K) :
    a * log (2 * K * a) + b * log (2 * K * b) - (a + b) * log (K * (a + b)) = klTerm a b := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp [klTerm]
  · have e1 := mul_log_sub a (a + b) (2 * K) ha h (by positivity)
    have e2 := mul_log_sub b (a + b) (2 * K) hb h (by positivity)
    have e3 : log (2 * K * (a + b)) = log 2 + log (K * (a + b)) := by
      rw [mul_assoc, log_mul two_ne_zero (by positivity)]
    unfold klTerm
    rw [show 2 * a / (a + b) = a / ((a + b) / 2) by field_simp,
      show 2 * b / (a + b) = b / ((a + b) / 2) by field_simp]
    have f1 := mul_log_sub a ((a + b) / 2) (2 * K) ha (by positivity) (by positivity)
    have f2 := mul_log_sub b ((a + b) / 2) (2 * K) hb (by positivity) (by positivity)
    rw [← f1, ← f2, show 2 * K * ((a + b) / 2) = K * (a + b) by ring]
    ring

lemma klTerm_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ klTerm a b := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp [klTerm]
  · have key : ∀ x, 0 ≤ x → x * log (2 * x / (a + b)) ≥ x - (a + b) / 2 := by
      intro x hx
      rcases hx.eq_or_lt with hx0 | hx0
      · subst hx0; simp; linarith
      · have := one_sub_inv_le_log_of_pos (x := 2 * x / (a + b)) (by positivity)
        have h' : x * (1 - (2 * x / (a + b))⁻¹) = x - (a + b) / 2 := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left this hx0.le]
    unfold klTerm
    linarith [key a ha, key b hb]

lemma klTerm_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : klTerm a b ≤ (a - b) ^ 2 / (a + b) := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp [klTerm]
  · have key : ∀ x, 0 ≤ x → x * log (2 * x / (a + b)) ≤ x * (2 * x / (a + b) - 1) := by
      intro x hx
      rcases hx.eq_or_lt with hx0 | hx0
      · subst hx0; simp
      · exact mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by positivity)) hx
    have hsum : a * (2 * a / (a + b) - 1) + b * (2 * b / (a + b) - 1) = (a - b) ^ 2 / (a + b) := by
      field_simp; ring
    unfold klTerm
    linarith [key a ha, key b hb]

/-- **Entropy increment identity.** -/
theorem dyEnt_succ_sub [IsFiniteMeasure ν] (k : ℕ) :
    dyEnt ν (k + 1) - dyEnt ν k = ∑ j ∈ Finset.range (2 ^ k),
      klTerm (mass ν (k + 1) (2 * j)) (mass ν (k + 1) (2 * j + 1)) := by
  unfold dyEnt
  rw [pow_succ, mul_comm (2 ^ k) 2, sum_range_two_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mass_split ν k j, pow_succ, mul_comm ((2 : ℝ) ^ k) 2]
  exact klTerm_eq _ _ _ (mass_nonneg _ _ _) (mass_nonneg _ _ _) (by positivity)

theorem dyEnt_succ_sub_nonneg [IsFiniteMeasure ν] (k : ℕ) : 0 ≤ dyEnt ν (k + 1) - dyEnt ν k := by
  rw [dyEnt_succ_sub]
  exact Finset.sum_nonneg fun j _ => klTerm_nonneg _ _ (mass_nonneg _ _ _) (mass_nonneg _ _ _)

/-- **Increment bound** `H_{k+1} - H_k ≤ D_k`. -/
theorem dyEnt_succ_sub_le [IsFiniteMeasure ν] (k : ℕ) : dyEnt ν (k + 1) - dyEnt ν k ≤ dyDisc ν k := by
  rw [dyEnt_succ_sub]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mass_split ν k j]
  exact klTerm_le _ _ (mass_nonneg _ _ _) (mass_nonneg _ _ _)

theorem dyEnt_le [IsFiniteMeasure ν] (k : ℕ) :
    dyEnt ν k ≤ dyEnt ν 0 + ∑ i ∈ Finset.range k, dyDisc ν i := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; linarith [dyEnt_succ_sub_le ν k]

theorem dyEnt_mono [IsFiniteMeasure ν] : Monotone (dyEnt ν) :=
  monotone_nat_of_le_succ fun k => by linarith [dyEnt_succ_sub_nonneg ν k]

/-! ### Bounded entropy implies absolute continuity -/

/-- `x ≤ M + (x log x + 1)/log M` for `x ≥ 0`, `M > 1`. -/
lemma le_of_entropy (x M : ℝ) (hx : 0 ≤ x) (hM : 1 < M) : x ≤ M + (x * log x + 1) / log M := by
  have hlM : 0 < log M := log_pos hM
  have hxlog : -1 ≤ x * log x := by
    rcases hx.eq_or_lt with h | h
    · subst h; simp
    · have := one_sub_inv_le_log_of_pos h
      have : x * (1 - x⁻¹) ≤ x * log x := mul_le_mul_of_nonneg_left this h.le
      have e : x * (1 - x⁻¹) = x - 1 := by field_simp
      linarith
  by_cases hxM : x ≤ M
  · have : 0 ≤ (x * log x + 1) / log M := div_nonneg (by linarith) hlM.le
    linarith
  · push Not at hxM
    have hlog : log M ≤ log x := log_le_log (by linarith) hxM.le
    have : x ≤ (x * log x + 1) / log M := by
      rw [le_div_iff₀ hlM]; nlinarith
    linarith [show (0 : ℝ) ≤ M by linarith]

/-- Cell form: `m ≤ M 2^{-k} + (m log(2^k m) + 2^{-k}) / log M`. -/
lemma mass_le_of_entropy (k : ℕ) (m M : ℝ) (hm : 0 ≤ m) (hM : 1 < M) :
    m ≤ M * (1 / 2 ^ k) + (m * log (2 ^ k * m) + 1 / 2 ^ k) / log M := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have := le_of_entropy (2 ^ k * m) M (by positivity) hM
  have e : m = (1 / 2 ^ k) * (2 ^ k * m) := by field_simp
  have hl : 0 < log M := log_pos hM
  calc m = (1 / 2 ^ k) * (2 ^ k * m) := e
    _ ≤ (1 / 2 ^ k) * (M + (2 ^ k * m * log (2 ^ k * m) + 1) / log M) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by field_simp

/-- Each entropy term is `≥ -2^{-k}`. -/
lemma mass_log_ge (k : ℕ) (m : ℝ) (hm : 0 ≤ m) : -(1 / 2 ^ k) ≤ m * log (2 ^ k * m) := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rcases hm.eq_or_lt with h | h
  · subst h; simp
  · have := one_sub_inv_le_log_of_pos (x := 2 ^ k * m) (by positivity)
    have h3 : m * (1 - (2 ^ k * m)⁻¹) = m - 1 / 2 ^ k := by field_simp
    have := mul_le_mul_of_nonneg_left this h.le
    linarith

/-- **Uniform integrability on a set of cells**: if `H_k ≤ B`, the cells in `G` carry mass at
most `M·(their total length) + (B + 2)/log M`. -/
theorem sum_mass_le [IsFiniteMeasure ν] (k : ℕ) (B : ℝ) (hB : dyEnt ν k ≤ B) (M : ℝ) (hM : 1 < M)
    (G : Finset ℕ) (hG : G ⊆ Finset.range (2 ^ k)) :
    ∑ j ∈ G, mass ν k j ≤ M * (G.card * (1 / 2 ^ k)) + (B + 2) / log M := by
  have hl : 0 < log M := log_pos hM
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  set t : ℕ → ℝ := fun j => mass ν k j * log (2 ^ k * mass ν k j)
  have hrest : ∑ j ∈ G, t j ≤ B + 1 := by
    have hsplit := Finset.sum_sdiff hG (f := t)
    have hlow : -(1 : ℝ) ≤ ∑ j ∈ Finset.range (2 ^ k) \ G, t j := by
      calc -(1 : ℝ) = ∑ _j ∈ Finset.range (2 ^ k), -(1 / 2 ^ k : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
        _ ≤ ∑ _j ∈ Finset.range (2 ^ k) \ G, -(1 / 2 ^ k : ℝ) := by
            rw [← Finset.sum_sdiff hG (f := fun _ => -(1 / 2 ^ k : ℝ))]
            have : ∑ _j ∈ G, -(1 / 2 ^ k : ℝ) ≤ 0 :=
              Finset.sum_nonpos fun _ _ => by have : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
                                              linarith
            linarith
        _ ≤ _ := Finset.sum_le_sum fun j _ => mass_log_ge k _ (mass_nonneg ν k j)
    have : dyEnt ν k = ∑ j ∈ Finset.range (2 ^ k) \ G, t j + ∑ j ∈ G, t j := hsplit.symm
    linarith
  have hGl : (G.card : ℝ) * (1 / 2 ^ k) ≤ 1 := by
    have : G.card ≤ 2 ^ k := by simpa using Finset.card_le_card hG
    have : (G.card : ℝ) ≤ 2 ^ k := by exact_mod_cast this
    rw [mul_one_div, div_le_one h2]; exact this
  calc ∑ j ∈ G, mass ν k j
      ≤ ∑ j ∈ G, (M * (1 / 2 ^ k) + (t j + 1 / 2 ^ k) / log M) :=
        Finset.sum_le_sum fun j _ => mass_le_of_entropy k _ M (mass_nonneg ν k j) hM
    _ = M * (G.card * (1 / 2 ^ k)) + (∑ j ∈ G, t j + G.card * (1 / 2 ^ k)) / log M := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div,
          Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ M * (G.card * (1 / 2 ^ k)) + (B + 2) / log M := by
        have h := div_le_div_of_nonneg_right
          (show ∑ j ∈ G, t j + G.card * (1 / 2 ^ k) ≤ B + 2 by linarith) hl.le
        linarith

/-- **Dyadic entropy criterion**: a finite measure carried by `[0,1)` with bounded dyadic
entropies is absolutely continuous. -/
theorem ac_of_dyEnt_bounded [IsFiniteMeasure ν] (hν : ν (Ico (0 : ℝ) 1)ᶜ = 0) (B : ℝ)
    (hB : ∀ k, dyEnt ν k ≤ B) : ν ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  -- step 1: `ν(A) ≤ (B+2)/log M + ε` for all `M > 1`, `ε > 0`
  have step : ∀ M : ℝ, 1 < M → ∀ ε : ℝ, 0 < ε → ν.real A ≤ (B + 2) / log M + ε := by
    intro M hM ε hε
    have hM0 : 0 < M := by linarith
    set η := ε / (2 * M)
    have hη : 0 < η := by positivity
    obtain ⟨U, hAU, hU, hvU⟩ := Set.exists_isOpen_lt_of_lt A (ENNReal.ofReal η)
      (by rw [hvol]; exact ENNReal.ofReal_pos.mpr hη)
    obtain ⟨C, hCA, hC, hνC⟩ := hA.exists_isCompact_lt_add (μ := ν) (measure_ne_top ν A)
      (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
    obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU (hCA.trans hAU)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / (2 : ℝ) ^ k < δ := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨k, by rwa [one_div_pow] at hk⟩
    classical
    set G := (Finset.range (2 ^ k)).filter fun j => (cell k j ∩ C).Nonempty
    have hGsub : G ⊆ Finset.range (2 ^ k) := Finset.filter_subset _ _
    -- cells of `G` lie in `U`
    have hcellU : ∀ j ∈ G, cell k j ⊆ U := by
      intro j hj x hx
      obtain ⟨y, hy, hyC⟩ := (Finset.mem_filter.mp hj).2
      exact hthick (Metric.mem_thickening_iff.mpr ⟨y, hyC, (dist_lt_of_mem_cell hx hy).trans hk⟩)
    -- total length of `G` is at most `vol U < η`
    have hlen : (G.card : ℝ) * (1 / 2 ^ k) ≤ η := by
      have h1 : volume.real (⋃ j ∈ G, cell k j) = G.card * (1 / 2 ^ k) := by
        rw [measureReal_biUnion_finset (cell_pairwiseDisjoint k G) (fun j _ => measurableSet_cell k j)
          (fun j _ => by unfold cell; exact measure_Ico_lt_top.ne)]
        simp [volume_real_cell]
      have hUfin : volume U ≠ ⊤ := ne_top_of_lt hvU
      have h2 : volume.real (⋃ j ∈ G, cell k j) ≤ volume.real U :=
        measureReal_mono (Set.iUnion₂_subset hcellU) hUfin
      have h3 : volume.real U ≤ η := by
        rw [Measure.real]; exact ENNReal.toReal_le_of_le_ofReal hη.le hvU.le
      linarith
    -- `ν(C) ≤ ∑_{G} m`
    have hCcov : ν.real C ≤ ∑ j ∈ G, mass ν k j := by
      have hsub : C ∩ Ico 0 1 ⊆ ⋃ j ∈ G, cell k j := by
        intro x ⟨hxC, hx01⟩
        obtain ⟨hlt, hmem⟩ := mem_cell_floor k hx01
        exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, x, hmem, hxC⟩) hmem
      have hCeq : ν.real C ≤ ν.real (C ∩ Ico 0 1) := by
        have : ν.real C ≤ ν.real (C ∩ Ico 0 1) + ν.real (Ico (0 : ℝ) 1)ᶜ := by
          calc ν.real C ≤ ν.real ((C ∩ Ico 0 1) ∪ (Ico (0 : ℝ) 1)ᶜ) := by
                refine measureReal_mono (fun x hx => ?_)
                by_cases h : x ∈ Ico (0 : ℝ) 1
                · exact Or.inl ⟨hx, h⟩
                · exact Or.inr h
            _ ≤ _ := measureReal_union_le _ _
        have h0 : ν.real (Ico (0 : ℝ) 1)ᶜ = 0 := by simp [Measure.real, hν]
        linarith
      exact hCeq.trans ((measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_biUnion_finset_le _ _))
    have hsum := sum_mass_le ν k B (hB k) M hM G hGsub
    have hAC : ν.real A ≤ ν.real C + ε / 2 := by
      rw [Measure.real, Measure.real]
      calc (ν A).toReal ≤ (ν C + ENNReal.ofReal (ε / 2)).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
              hνC.le
        _ = (ν C).toReal + ε / 2 := by
            rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
              ENNReal.toReal_ofReal (by positivity)]
    have hMη : M * η = ε / 2 := by simp only [η]; field_simp
    have : M * (G.card * (1 / 2 ^ k)) ≤ ε / 2 := by
      rw [← hMη]; exact mul_le_mul_of_nonneg_left hlen hM0.le
    linarith
  -- step 2: let `ε → 0`, then `M → ∞`
  have step2 : ∀ M : ℝ, 1 < M → ν.real A ≤ (B + 2) / log M := fun M hM =>
    le_of_forall_pos_le_add fun ε hε => step M hM ε hε
  have hA0 : ν.real A ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set c := max (B + 2) 1
    have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    set t := 2 * c / ν.real A + 1
    have ht : 0 < t := by positivity
    have hM : 1 < exp t := one_lt_exp_iff.mpr ht
    have h1 := step2 (exp t) hM
    rw [log_exp] at h1
    have h2 : (B + 2) / t ≤ c / t := div_le_div_of_nonneg_right (le_max_left _ _) ht.le
    have h3 : c / t < ν.real A := by
      rw [div_lt_iff₀ ht]
      have : ν.real A * t = 2 * c + ν.real A := by simp only [t]; field_simp
      rw [this]; linarith
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top ν A)).mp (le_antisymm hA0 measureReal_nonneg)

/-- **Summable dyadic discrepancies imply absolute continuity.** -/
theorem ac_of_summable_dyDisc [IsFiniteMeasure ν] (hν : ν (Ico (0 : ℝ) 1)ᶜ = 0)
    (hD : Summable (dyDisc ν)) : ν ≪ volume :=
  ac_of_dyEnt_bounded ν hν (dyEnt ν 0 + ∑' i, dyDisc ν i) fun k =>
    (dyEnt_le ν k).trans (by
      gcongr
      exact hD.sum_le_tsum _ fun i _ => dyDisc_nonneg ν i)

/-! ### Convexity under mixtures -/

/-- Sedrakyan's inequality with the convention `x/0 = 0`, for `g ≥ 0` and `f = 0` where `g = 0`. -/
lemma sq_sum_div_le_of_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, g i = 0 → f i = 0) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by
  classical
  set t := s.filter fun i => 0 < g i
  have hz : ∀ i ∈ s, i ∉ t → g i = 0 := fun i hi hit => by
    have : ¬ 0 < g i := fun h => hit (Finset.mem_filter.mpr ⟨hi, h⟩)
    exact le_antisymm (not_lt.mp this) (hg i hi)
  have e1 : ∑ i ∈ s, f i = ∑ i ∈ t, f i :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hit => hfg i hi (hz i hi hit)).symm
  have e2 : ∑ i ∈ s, g i = ∑ i ∈ t, g i :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hit => hz i hi hit).symm
  have e3 : ∑ i ∈ s, f i ^ 2 / g i = ∑ i ∈ t, f i ^ 2 / g i :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hit => by
      rw [hz i hi hit, div_zero]).symm
  rw [e1, e2, e3]
  exact Finset.sq_sum_div_le_sum_sq_div t f fun i hi => (Finset.mem_filter.mp hi).2

lemma mass_finset_sum {ι : Type*} (s : Finset ι) (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (k j : ℕ) : mass (∑ i ∈ s, ν i) k j = ∑ i ∈ s, mass (ν i) k j := by
  unfold mass Measure.real
  rw [FunLike.coe_sum, Finset.sum_apply, ENNReal.toReal_sum fun i _ => measure_ne_top _ _]

/-- **Dyadic discrepancies are subadditive** (convex under mixtures): for a finite sum of finite
measures, `D_k(∑ νᵢ) ≤ ∑ D_k(νᵢ)`. In particular `D_k(Q⁻¹ ∑_p N_{p/Q}) ≤ Q⁻¹ ∑_p D_k(N_{p/Q})`:
flux-wise discrepancy bounds average, and so does their failure. -/
theorem dyDisc_finset_sum_le {ι : Type*} (s : Finset ι) (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] (k : ℕ) :
    dyDisc (∑ i ∈ s, ν i) k ≤ ∑ i ∈ s, dyDisc (ν i) k := by
  unfold dyDisc
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [mass_finset_sum]
  rw [← Finset.sum_sub_distrib]
  refine sq_sum_div_le_of_nonneg s _ _ (fun i _ => mass_nonneg _ _ _) fun i _ h0 => ?_
  have hs := mass_split (ν i) k j
  have ha := mass_nonneg (ν i) (k + 1) (2 * j)
  have hb := mass_nonneg (ν i) (k + 1) (2 * j + 1)
  have : mass (ν i) (k + 1) (2 * j) = 0 := by linarith
  have : mass (ν i) (k + 1) (2 * j + 1) = 0 := by linarith
  simp [*]

end ThomDyadic
