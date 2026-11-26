import ThomLean.UpperBound.Gap

/-!
# Round 8, Task 4: adaptive dyadic decomposition of the chiral chain

All blocks are intervals of sites `[a, a + n)` with `a + n ≤ N`, described through `val`
(`inB a n x`). For a vector `ξ` vanishing on a set `Z(p,t)` of sites built from the good/bad
structure of the dyadic blocks, the chain operator is coercive: `‖ξ‖² ≤ 4^K e^T ‖H_{p,t} ξ‖²`.

* `block_gap`: the spectral gap of a good block, from `chiral_gap`.
* `chainH_supp`: a vector supported in a block and vanishing at its two end sites has its image
  supported in the block (cutting the two boundary bonds costs two sites).
* `Zt`: the adaptive set: a good dyadic block contributes its two end sites; a bad block of
  length `2` contributes both sites; a bad longer block is bisected.
* `Zt_coercive`: coercivity on a dyadic block; `Ztop_coercive`: on the whole cycle, with the
  top-level blocks `[iL, (i+1)L)`, `i < N / L`, and the remainder `[qL, N)` removed.
* `card_Zt_le`, `sum_badCount_le`: `#Z ≤ 2 + 2·#(bad dyadic sub-blocks)`, and the expected
  number of bad sub-blocks of a block of length `2^ℓ` is `≤ 320 · 2^ℓ (ℓ+1)³ / T²`.

This replaces the "rank-two cut changes the count by at most four" step of the round-8 plan by
the equivalent subspace-codimension argument: two vanishing conditions per cut.
-/

noncomputable section

namespace ThomUpper

open ThomZeroLevel Real Finset ComplexConjugate

variable {N : ℕ} [NeZero N]
set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ### Sites and blocks -/

/-- `x` lies in the block `[a, a+n)`. -/
def inB (a n : ℕ) (x : ZMod N) : Prop := a ≤ x.val ∧ x.val < a + n

instance (a n : ℕ) : DecidablePred (inB (N := N) a n) := fun _ => by unfold inB; infer_instance

lemma val_cast_add {a k : ℕ} (h : a + k < N) : (((a + k : ℕ) : ZMod N)).val = a + k :=
  ZMod.val_cast_of_lt h

lemma inB_cast {a n k : ℕ} (hk : k < n) (h : a + n ≤ N) : inB a n (((a + k : ℕ) : ZMod N)) := by
  unfold inB; rw [val_cast_add (by omega)]; omega

/-- Sum over a block as a sum over offsets. -/
lemma sum_inB (f : ZMod N → ℝ) {a n : ℕ} (h : a + n ≤ N) :
    ∑ k ∈ range n, f ((a + k : ℕ) : ZMod N) = ∑ x ∈ univ.filter (inB a n), f x := by
  refine Finset.sum_nbij' (fun k => ((a + k : ℕ) : ZMod N)) (fun x => x.val - a) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact inB_cast (Finset.mem_range.mp hk) h
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and, inB] at hx
    simp only [Finset.mem_range]; omega
  · intro k hk; have := Finset.mem_range.mp hk; rw [val_cast_add (by omega)]; omega
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and, inB] at hx
    rw [show a + (x.val - a) = x.val by omega, ZMod.natCast_zmod_val]
  · intro k _; rfl

lemma nrm_eq_sum_blk (ξ : ZMod N → ℂ) {a n : ℕ} (h : a + n ≤ N)
    (hs : ∀ x, ¬ inB a n x → ξ x = 0) :
    nrm ξ = ∑ k ∈ range n, Complex.normSq (ξ ((a + k : ℕ) : ZMod N)) := by
  rw [sum_inB (fun x => Complex.normSq (ξ x)) h, nrm]
  rw [← Finset.sum_filter_add_sum_filter_not univ (inB a n)]
  have : ∑ x ∈ univ.filter (fun x => ¬ inB a n x), Complex.normSq (ξ x) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [hs x (Finset.mem_filter.mp hx).2, map_zero]
  rw [this, add_zero]

lemma sum_blk_le_nrm (y : ZMod N → ℂ) {a n : ℕ} (h : a + n ≤ N) :
    ∑ k ∈ range n, Complex.normSq (y ((a + k : ℕ) : ZMod N)) ≤ nrm y := by
  rw [sum_inB (fun x => Complex.normSq (y x)) h, nrm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => Complex.normSq_nonneg _

/-! ### Bonds are nonzero -/

lemma norm_bond_pos (hN : Odd N) (p t n : ZMod N) : 0 < ‖bond p t n‖ := by
  set u := t + p * (n + 1)
  have h1 : ‖bond p t n‖ = 2 * |cos (π * (u.val / N))| := norm_one_add_psi u
  have h2 := abs_sub_le_abs_cos (N := N) (ZMod.val_lt u).le
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h3 : (0 : ℝ) < |(N : ℝ) - 2 * u.val| := by
    rw [abs_pos, sub_ne_zero]
    intro h
    obtain ⟨k, hk⟩ := hN
    have : (N : ℝ) = 2 * u.val := h
    have : N = 2 * u.val := by exact_mod_cast this
    omega
  rw [h1]; have := div_pos h3 hNp; linarith

lemma norm_bond_eq_exp (hN : Odd N) (p t : ZMod N) (n : ℕ) :
    ‖bond p t (n : ZMod N)‖ = exp (Xs p t n) := by
  rw [Xs_eq, exp_log (norm_bond_pos hN p t _)]

/-! ### Spectral gap of a good block on the chain -/

lemma val_sub_one_not_inB {a n : ℕ} (hn : n < N) (h : a + n ≤ N) :
    ¬ inB a n ((a : ZMod N) - 1) := by
  unfold inB
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.cast_zero, zero_sub, zero_le, true_and, zero_add, not_lt]
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have : (-1 : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
      rw [Nat.cast_sub hN1, ZMod.natCast_self]; simp
    rw [this, ZMod.val_cast_of_lt (by omega)]; omega
  · have : ((a : ZMod N) - 1) = ((a - 1 : ℕ) : ZMod N) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this, ZMod.val_cast_of_lt (by omega)]; omega

lemma val_end_not_inB {a n : ℕ} (hn : n < N) (h : a + n ≤ N) :
    ¬ inB a n (((a + n : ℕ) : ZMod N)) := by
  unfold inB
  rcases (show a + n < N ∨ a + n = N by omega) with h' | h'
  · rw [ZMod.val_cast_of_lt h']; omega
  · rw [h', ZMod.natCast_self, ZMod.val_zero]; omega

/-- **Gap of a good block** on the chain: if `ξ` is supported in `[a, a+2m)` and the alternating
bond sums of the block are bounded by `T/4`, then `‖ξ‖² ≤ 4 m² e^T ‖H ξ‖²`. -/
theorem block_gap (hN : Odd N) (p t : ZMod N) {a m : ℕ} {T : ℝ} (ha : a + 2 * m ≤ N)
    (hgood : ∀ k ≤ 2 * m, |altS p t a k| ≤ T / 4) (ξ : ZMod N → ℂ)
    (hs : ∀ x, ¬ inB a (2 * m) x → ξ x = 0) :
    nrm ξ ≤ 4 * m ^ 2 * exp T * nrm (chainH p t ξ) := by
  have hmN : 2 * m < N := by
    rcases (show 2 * m < N ∨ 2 * m = N by omega) with h | h
    · exact h
    · obtain ⟨k, hk⟩ := hN; omega
  set b : ℕ → ℂ := fun k => bond p t ((a + k : ℕ) : ZMod N)
  set η : ℕ → ℂ := fun k => ξ ((a + k : ℕ) : ZMod N)
  set y : ℕ → ℂ := fun k => chainH p t ξ ((a + k : ℕ) : ZMod N)
  set X : ℕ → ℝ := fun k => Xs p t (a + k)
  set S : ℕ → ℝ := fun k => altS p t a k
  have hX : ∀ k, ‖b k‖ = exp (X k) := fun k => norm_bond_eq_exp hN p t (a + k)
  have hS0 : S 0 = 0 := by simp [S, altS]
  have hS : ∀ k, S (k + 1) = S k + (-1) ^ k * X k := fun k => by
    simp only [S, altS, X, Finset.sum_range_succ]
  have hy : ∀ k, 1 ≤ k → y k = b (k - 1) * η (k - 1) + conj (b k) * η (k + 1) := by
    intro k hk
    simp only [y, b, η, chainH]
    have e1 : ((a + k : ℕ) : ZMod N) - 1 = ((a + (k - 1) : ℕ) : ZMod N) := by
      rw [show a + k = a + (k - 1) + 1 by omega]; push_cast; ring
    have e2 : ((a + k : ℕ) : ZMod N) + 1 = ((a + (k + 1) : ℕ) : ZMod N) := by push_cast; ring
    rw [e1, e2]
  have hy0 : y 0 = conj (b 0) * η 1 := by
    simp only [y, b, η, chainH, add_zero]
    rw [hs _ (val_sub_one_not_inB hmN ha), mul_zero, zero_add]
    congr 2
    push_cast; ring
  have hη : η (2 * m) = 0 := hs _ (val_end_not_inB hmN ha)
  have key := chiral_gap b η y X S m T hX hS0 hS hgood hy0 hy hη
  rw [nrm_eq_sum_blk ξ ha hs]
  have h2 := sum_blk_le_nrm (chainH p t ξ) ha
  simp only [Complex.normSq_eq_norm_sq] at h2 ⊢
  calc ∑ k ∈ range (2 * m), ‖ξ ((a + k : ℕ) : ZMod N)‖ ^ 2
      ≤ 4 * m ^ 2 * exp T * ∑ k ∈ range (2 * m), ‖y k‖ ^ 2 := key
    _ ≤ 4 * m ^ 2 * exp T * nrm (chainH p t ξ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact h2

/-! ### Locality -/

/-- A vector supported in `[a, a+n)` and vanishing at both end sites has its image under the
chain operator supported in `[a, a+n)`. -/
lemma chainH_supp (p t : ZMod N) {a n : ℕ} (h : a + n ≤ N) (hn : 1 ≤ n) (ξ : ZMod N → ℂ)
    (hs : ∀ x, ¬ inB a n x → ξ x = 0) (h0 : ξ (a : ZMod N) = 0)
    (h1 : ξ (((a + n - 1 : ℕ) : ZMod N)) = 0) :
    ∀ x, ¬ inB a n x → chainH p t ξ x = 0 := by
  intro x hx
  have hl : ξ (x - 1) = 0 := by
    by_cases hin : inB a n (x - 1)
    · obtain ⟨hv1, hv2⟩ := hin
      set v := (x - 1).val
      have hxv : x = ((v + 1 : ℕ) : ZMod N) := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      by_cases hv : v + 1 < a + n
      · exfalso; apply hx
        rw [hxv]; unfold inB; rw [ZMod.val_cast_of_lt (by omega)]; omega
      · have : x - 1 = ((a + n - 1 : ℕ) : ZMod N) := by
          rw [← ZMod.natCast_zmod_val (x - 1)]; congr 1; omega
        rw [this, h1]
    · exact hs _ hin
  have hr : ξ (x + 1) = 0 := by
    by_cases hin : inB a n (x + 1)
    · obtain ⟨hw1, hw2⟩ := hin
      set w := (x + 1).val
      by_cases hw : a < w
      · exfalso; apply hx
        have hxw : x = ((w - 1 : ℕ) : ZMod N) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; simp
        rw [hxw]; unfold inB
        rw [ZMod.val_cast_of_lt (by have := ZMod.val_lt (x + 1); omega)]; omega
      · have : x + 1 = (a : ZMod N) := by
          rw [← ZMod.natCast_zmod_val (x + 1)]; congr 1; omega
        rw [this, h0]
    · exact hs _ hin
  simp only [chainH, hl, hr, mul_zero, add_zero]

lemma chainH_add (p t : ZMod N) (u v : ZMod N → ℂ) :
    chainH p t (fun x => u x + v x) = fun x => chainH p t u x + chainH p t v x := by
  funext x; simp only [chainH]; ring

lemma nrm_add_of_disj (u v : ZMod N → ℂ) (h : ∀ x, u x = 0 ∨ v x = 0) :
    nrm (fun x => u x + v x) = nrm u + nrm v := by
  simp only [nrm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases h x with h | h <;> simp [h]

/-! ### The adaptive vanishing set -/

open Classical in
/-- The adaptive vanishing set of the dyadic block `[a, a + 2^ℓ)`: a good block contributes its
two end sites, a bad block of length `2` both its sites, a bad longer block is bisected. -/
def Zt (T : ℝ) (p t : ZMod N) : ℕ → ℕ → Finset (ZMod N)
  | a, 0 => {(a : ZMod N)}
  | a, ℓ + 1 =>
    if ¬ badB T p t a (ℓ + 1) then {(a : ZMod N), ((a + 2 ^ (ℓ + 1) - 1 : ℕ) : ZMod N)}
    else if ℓ = 0 then {(a : ZMod N), ((a + 1 : ℕ) : ZMod N)}
    else Zt T p t a ℓ ∪ Zt T p t (a + 2 ^ ℓ) ℓ

open Classical in
/-- Number of bad dyadic sub-blocks (of length `≥ 2`) of `[a, a + 2^ℓ)`. -/
def badCount (T : ℝ) (p t : ZMod N) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, ℓ + 1 => (if badB T p t a (ℓ + 1) then 1 else 0) + badCount T p t a ℓ +
      badCount T p t (a + 2 ^ ℓ) ℓ

variable {T : ℝ} {p t : ZMod N}

lemma Zt_ends : ∀ ℓ, 1 ≤ ℓ → ∀ a, (a : ZMod N) ∈ Zt T p t a ℓ ∧
    (((a + 2 ^ ℓ - 1 : ℕ) : ZMod N)) ∈ Zt T p t a ℓ := by
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    intro a
    by_cases hb : badB T p t a (0 + 1)
    · simp [Zt, hb]
    · simp [Zt, hb]
  | succ ℓ hℓ ih =>
    intro a
    by_cases hb : badB T p t a (ℓ + 1)
    · have hℓ0 : ℓ ≠ 0 := by omega
      simp only [Zt, hb, not_true_eq_false, if_false, hℓ0, Finset.mem_union]
      refine ⟨Or.inl (ih a).1, Or.inr ?_⟩
      have := (ih (a + 2 ^ ℓ)).2
      rwa [show a + 2 ^ ℓ + 2 ^ ℓ - 1 = a + 2 ^ (ℓ + 1) - 1 by rw [pow_succ]; omega] at this
    · simp [Zt, hb]

lemma Zt_supp {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {a : ℕ} (ha : a + 2 ^ ℓ ≤ N) (ξ : ZMod N → ℂ)
    (hs : ∀ x, ¬ inB a (2 ^ ℓ) x → ξ x = 0) (hz : ∀ x ∈ Zt T p t a ℓ, ξ x = 0) :
    ∀ x, ¬ inB a (2 ^ ℓ) x → chainH p t ξ x = 0 :=
  chainH_supp p t ha (Nat.one_le_two_pow) ξ hs (hz _ (Zt_ends ℓ hℓ a).1)
    (hz _ (Zt_ends ℓ hℓ a).2)

/-- A vector supported in a bad block of length two and vanishing at both sites is zero. -/
lemma eq_zero_of_two {a : ℕ} (ha : a + 2 ≤ N) (ξ : ZMod N → ℂ)
    (hs : ∀ x, ¬ inB a 2 x → ξ x = 0) (h0 : ξ (a : ZMod N) = 0)
    (h1 : ξ (((a + 1 : ℕ) : ZMod N)) = 0) : ∀ x, ξ x = 0 := by
  intro x
  by_cases hx : inB a 2 x
  · obtain ⟨h1', h2'⟩ := hx
    rcases (show x.val = a ∨ x.val = a + 1 by omega) with e | e
    · rw [← ZMod.natCast_zmod_val x, e, h0]
    · rw [← ZMod.natCast_zmod_val x, e, h1]
  · exact hs x hx

/-- **Coercivity on a dyadic block**: `‖ξ‖² ≤ 4^ℓ e^T ‖H ξ‖²` for `ξ` supported in the block and
vanishing on `Z_t(a, ℓ)`. -/
theorem Zt_coercive (hN : Odd N) : ∀ ℓ, 1 ≤ ℓ → ∀ a, a + 2 ^ ℓ ≤ N → ∀ ξ : ZMod N → ℂ,
    (∀ x, ¬ inB a (2 ^ ℓ) x → ξ x = 0) → (∀ x ∈ Zt T p t a ℓ, ξ x = 0) →
    nrm ξ ≤ 4 ^ ℓ * exp T * nrm (chainH p t ξ) := by
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    intro a ha ξ hs hz
    by_cases hb : badB T p t a (0 + 1)
    · have hz' : ∀ x ∈ ({(a : ZMod N), ((a + 1 : ℕ) : ZMod N)} : Finset (ZMod N)), ξ x = 0 := by
        intro x hx; apply hz; simp only [Zt, hb, not_true_eq_false, if_false, if_true]; exact hx
      have h0 := eq_zero_of_two (by simpa using ha) ξ (by simpa using hs) (hz' _ (by simp))
        (hz' _ (by simp))
      have : nrm ξ = 0 := by simp [nrm, h0]
      rw [this]; exact mul_nonneg (by positivity) (nrm_nonneg _)
    · have hgood : ∀ k ≤ 2 * 1, |altS p t a k| ≤ T / 4 := by
        intro k hk; by_contra hc; exact hb ⟨k, by simpa using hk, lt_of_not_ge hc⟩
      have := block_gap hN p t (m := 1) (by simpa using ha) hgood ξ (by simpa using hs)
      simpa using this
  | succ ℓ hℓ ih =>
    intro a ha ξ hs hz
    have hℓ0 : ℓ ≠ 0 := by omega
    by_cases hb : badB T p t a (ℓ + 1)
    · have hz' : ∀ x ∈ Zt T p t a ℓ ∪ Zt T p t (a + 2 ^ ℓ) ℓ, ξ x = 0 := by
        intro x hx; apply hz; simp only [Zt, hb, not_true_eq_false, if_false, hℓ0]; exact hx
      have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
      set c := a + 2 ^ ℓ
      let ξ1 : ZMod N → ℂ := fun x => if x.val < c then ξ x else 0
      let ξ2 : ZMod N → ℂ := fun x => if x.val < c then 0 else ξ x
      have hsplit : ξ = fun x => ξ1 x + ξ2 x := by
        funext x; simp only [ξ1, ξ2]; split_ifs <;> simp
      have hs1 : ∀ x, ¬ inB a (2 ^ ℓ) x → ξ1 x = 0 := by
        intro x hx; simp only [ξ1]; split_ifs with h
        · apply hs; unfold inB at hx ⊢; omega
        · rfl
      have hs2 : ∀ x, ¬ inB c (2 ^ ℓ) x → ξ2 x = 0 := by
        intro x hx; simp only [ξ2]; split_ifs with h
        · rfl
        · apply hs; unfold inB at hx ⊢; omega
      have hz1 : ∀ x ∈ Zt T p t a ℓ, ξ1 x = 0 := by
        intro x hx; simp only [ξ1]; split_ifs
        · exact hz' x (Finset.mem_union_left _ hx)
        · rfl
      have hz2 : ∀ x ∈ Zt T p t c ℓ, ξ2 x = 0 := by
        intro x hx; simp only [ξ2]; split_ifs
        · rfl
        · exact hz' x (Finset.mem_union_right _ hx)
      have ha1 : a + 2 ^ ℓ ≤ N := by have := Nat.one_le_two_pow (n := ℓ); omega
      have ha2 : c + 2 ^ ℓ ≤ N := by simp only [c]; have := Nat.one_le_two_pow (n := ℓ); omega
      have g1 := ih a ha1 ξ1 hs1 hz1
      have g2 := ih c ha2 ξ2 hs2 hz2
      have s1 := Zt_supp hℓ ha1 ξ1 hs1 hz1
      have s2 := Zt_supp hℓ ha2 ξ2 hs2 hz2
      have hdisj : ∀ x, chainH p t ξ1 x = 0 ∨ chainH p t ξ2 x = 0 := by
        intro x
        by_cases hx : inB a (2 ^ ℓ) x
        · right; apply s2; unfold inB at hx ⊢; omega
        · left; exact s1 x hx
      have hdisj0 : ∀ x, ξ1 x = 0 ∨ ξ2 x = 0 := by
        intro x; simp only [ξ1, ξ2]; split_ifs <;> simp
      rw [hsplit, chainH_add, nrm_add_of_disj _ _ hdisj, nrm_add_of_disj _ _ hdisj0]
      have hE : 0 ≤ 4 ^ ℓ * exp T := by positivity
      have h1 := nrm_nonneg (chainH p t ξ1)
      have h2 := nrm_nonneg (chainH p t ξ2)
      have : (4 : ℝ) ^ ℓ * exp T ≤ 4 ^ (ℓ + 1) * exp T := by
        gcongr; norm_num; omega
      nlinarith
    · have hgood : ∀ k ≤ 2 * 2 ^ ℓ, |altS p t a k| ≤ T / 4 := by
        intro k hk; by_contra hc
        exact hb ⟨k, by rw [pow_succ]; omega, lt_of_not_ge hc⟩
      have ha' : a + 2 * 2 ^ ℓ ≤ N := by rw [pow_succ] at ha; omega
      have hs' : ∀ x, ¬ inB a (2 * 2 ^ ℓ) x → ξ x = 0 := by
        intro x hx; apply hs; rwa [pow_succ, mul_comm]
      have := block_gap hN p t (m := 2 ^ ℓ) ha' hgood ξ hs'
      calc nrm ξ ≤ 4 * ((2 ^ ℓ : ℕ) : ℝ) ^ 2 * exp T * nrm (chainH p t ξ) := this
        _ = 4 ^ (ℓ + 1) * exp T * nrm (chainH p t ξ) := by
          push_cast; rw [← pow_mul, pow_succ, show (2 : ℝ) ^ (ℓ * 2) = 4 ^ ℓ by
            rw [pow_mul']; norm_num]; ring

lemma card_Zt_le : ∀ ℓ a, (#(Zt T p t a ℓ) : ℝ) ≤ 2 + 2 * badCount T p t a ℓ := by
  intro ℓ
  induction ℓ with
  | zero => intro a; simp [Zt, badCount]
  | succ ℓ ih =>
    intro a
    by_cases hb : badB T p t a (ℓ + 1)
    · by_cases hℓ0 : ℓ = 0
      · subst hℓ0
        simp only [Zt, hb, not_true_eq_false, if_false, if_true, badCount]
        have := Finset.card_insert_le (a : ZMod N) {((a + 1 : ℕ) : ZMod N)}
        simp only [Finset.card_singleton] at this
        have : (#({(a : ZMod N), ((a + 1 : ℕ) : ZMod N)} : Finset _) : ℝ) ≤ 2 := by
          exact_mod_cast this
        push_cast at this ⊢
        have h0 : (0 : ℝ) ≤ badCount T p t a 0 := by positivity
        have h0' : (0 : ℝ) ≤ badCount T p t (a + 2 ^ 0) 0 := by positivity
        linarith
      · simp only [Zt, hb, not_true_eq_false, if_false, hℓ0, if_true, badCount]
        have h1 := ih a; have h2 := ih (a + 2 ^ ℓ)
        have := Finset.card_union_le (Zt T p t a ℓ) (Zt T p t (a + 2 ^ ℓ) ℓ)
        have : (#(Zt T p t a ℓ ∪ Zt T p t (a + 2 ^ ℓ) ℓ) : ℝ) ≤
            #(Zt T p t a ℓ) + #(Zt T p t (a + 2 ^ ℓ) ℓ) := by exact_mod_cast this
        push_cast; linarith
    · simp only [Zt, hb, not_false_eq_true, if_true, badCount, if_false]
      have := Finset.card_insert_le (a : ZMod N) {((a + 2 ^ (ℓ + 1) - 1 : ℕ) : ZMod N)}
      simp only [Finset.card_singleton] at this
      have : (#({(a : ZMod N), ((a + 2 ^ (ℓ + 1) - 1 : ℕ) : ZMod N)} : Finset _) : ℝ) ≤ 2 := by
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ badCount T p t a ℓ := by positivity
      have h0' : (0 : ℝ) ≤ badCount T p t (a + 2 ^ ℓ) ℓ := by positivity
      push_cast; linarith

/-! ### Expected number of bad sub-blocks -/

theorem sum_badCount_le [Fact N.Prime] (hN : Odd N) (hT : 24 ≤ T) :
    ∀ ℓ a, 2 ^ ℓ ≤ N → (∑ pt : ZMod N × ZMod N, (badCount T pt.1 pt.2 a ℓ : ℝ)) * T ^ 2 ≤
      320 * N ^ 2 * 2 ^ ℓ * (ℓ + 1) ^ 3 := by
  intro ℓ
  induction ℓ with
  | zero => intro a _; simp [badCount]
  | succ ℓ ih =>
    intro a hℓ
    have hℓ' : 2 ^ ℓ ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hℓ
    have h1 := ih a hℓ'
    have h2 := ih (a + 2 ^ ℓ) hℓ'
    have h3 := card_badB_le hN hT a (ℓ + 1) hℓ
    have hsum : ∑ pt : ZMod N × ZMod N, (badCount T pt.1 pt.2 a (ℓ + 1) : ℝ) =
        (#{pt : ZMod N × ZMod N | badB T pt.1 pt.2 a (ℓ + 1)} : ℝ) +
        ∑ pt : ZMod N × ZMod N, (badCount T pt.1 pt.2 a ℓ : ℝ) +
        ∑ pt : ZMod N × ZMod N, (badCount T pt.1 pt.2 (a + 2 ^ ℓ) ℓ : ℝ) := by
      simp only [badCount]
      push_cast
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 2
      rw [Finset.card_filter]; push_cast
      exact Finset.sum_congr rfl fun pt _ => by split_ifs <;> simp
    rw [hsum]
    push_cast at h3 ⊢
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
    have hp : (2 : ℝ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
    rw [hp] at h3 ⊢
    have hN2 : 0 ≤ (N : ℝ) ^ 2 * 2 ^ ℓ := by positivity
    have hpoly : ((ℓ : ℝ) + 1 + 1) ^ 2 + ((ℓ : ℝ) + 1) ^ 3 ≤ ((ℓ : ℝ) + 1 + 1) ^ 3 := by
      have h0 : (0 : ℝ) ≤ ℓ := by positivity
      nlinarith [mul_nonneg h0 h0]
    have := mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ 640 * N ^ 2 * 2 ^ ℓ)
    nlinarith

/-! ### The whole cycle -/

/-- The vanishing set on the whole cycle: top-level blocks `[iL, (i+1)L)` (`L = 2^K`,
`i < N / L`) and the remainder `[qL, N)`. -/
def Ztop (T : ℝ) (p t : ZMod N) (K : ℕ) : Finset (ZMod N) :=
  ((range (N / 2 ^ K)).biUnion fun i => Zt T p t (i * 2 ^ K) K) ∪
    univ.filter (fun x : ZMod N => N / 2 ^ K * 2 ^ K ≤ x.val)

/-- **Coercivity of the chain operator off `Z_top`**: `‖ξ‖² ≤ 4^K e^T ‖H_{p,t} ξ‖²`. -/
theorem Ztop_coercive (hN : Odd N) {K : ℕ} (hK : 1 ≤ K) (ξ : ZMod N → ℂ)
    (hz : ∀ x ∈ Ztop T p t K, ξ x = 0) :
    nrm ξ ≤ 4 ^ K * exp T * nrm (chainH p t ξ) := by
  set L := 2 ^ K
  set q := N / L
  have hqL : q * L ≤ N := Nat.div_mul_le_self N L
  have hC : 0 ≤ (4 : ℝ) ^ K * exp T := by positivity
  have key : ∀ j ≤ q, (∀ x : ZMod N, ¬ x.val < j * L →
      chainH p t (fun y => if y.val < j * L then ξ y else 0) x = 0) ∧
      nrm (fun y => if y.val < j * L then ξ y else 0) ≤
        4 ^ K * exp T * nrm (chainH p t (fun y => if y.val < j * L then ξ y else 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [zero_mul, Nat.not_lt_zero, if_false]
      refine ⟨fun x _ => by simp [chainH], ?_⟩
      have : nrm (fun _ : ZMod N => (0 : ℂ)) = 0 := by simp [nrm]
      rw [this]; exact mul_nonneg hC (nrm_nonneg _)
    | succ j ih =>
      intro hj
      obtain ⟨ihs, ihn⟩ := ih (by omega)
      set u : ZMod N → ℂ := fun y => if y.val < j * L then ξ y else 0
      set w : ZMod N → ℂ := fun y => if inB (j * L) L y then ξ y else 0
      have hsplit : (fun y : ZMod N => if y.val < (j + 1) * L then ξ y else 0) =
          fun y => u y + w y := by
        funext y; simp only [u, w, inB, add_mul, one_mul]
        have hL0 : j * L ≤ j * L + L := Nat.le_add_right _ _
        by_cases h1 : y.val < j * L
        · have h2 : y.val < j * L + L := by omega
          simp [h1, h2]
        · by_cases h2 : y.val < j * L + L
          · simp [h1, h2, show j * L ≤ y.val by omega]
          · simp [h1, h2]
      have hjL : j * L + L ≤ N := by
        have : (j + 1) * L ≤ q * L := Nat.mul_le_mul_right L hj
        rw [add_mul, one_mul] at this; omega
      have hws : ∀ x, ¬ inB (j * L) L x → w x = 0 := by
        intro x hx; simp only [w, if_neg hx]
      have hwz : ∀ x ∈ Zt T p t (j * L) K, w x = 0 := by
        intro x hx; simp only [w]; split_ifs
        · apply hz; simp only [Ztop, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
          left; exact ⟨j, hj, hx⟩
        · rfl
      have gw := Zt_coercive hN K hK (j * L) hjL w hws hwz
      have sw := Zt_supp hK hjL w hws hwz
      have hdisj : ∀ x, chainH p t u x = 0 ∨ chainH p t w x = 0 := by
        intro x
        by_cases hx : x.val < j * L
        · right; apply sw; unfold inB; omega
        · left; exact ihs x hx
      have hdisj0 : ∀ x, u x = 0 ∨ w x = 0 := by
        intro x; simp only [u, w, inB]; split_ifs <;> first | (exfalso; omega) | simp
      rw [hsplit, chainH_add, nrm_add_of_disj _ _ hdisj, nrm_add_of_disj _ _ hdisj0]
      refine ⟨fun x hx => ?_, ?_⟩
      · have hx' : ¬ x.val < j * L + L := by rwa [add_mul, one_mul] at hx
        have hL0 : j * L ≤ j * L + L := Nat.le_add_right _ _
        have h1 : chainH p t u x = 0 := ihs x (by omega)
        have h2 : chainH p t w x = 0 := sw x (by unfold inB; omega)
        show chainH p t u x + chainH p t w x = 0
        rw [h1, h2, add_zero]
      · have := nrm_nonneg (chainH p t u); have := nrm_nonneg (chainH p t w)
        nlinarith
  obtain ⟨_, hfin⟩ := key q le_rfl
  have hξ : (fun y : ZMod N => if y.val < q * L then ξ y else 0) = ξ := by
    funext y; split_ifs with h
    · rfl
    · symm; apply hz; simp only [Ztop, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]; right; show q * L ≤ y.val; omega
  rwa [hξ] at hfin

lemma card_val_ge {c : ℕ} (hc : c ≤ N) :
    #(univ.filter (fun x : ZMod N => c ≤ x.val)) = N - c := by
  have h := sum_inB (N := N) (fun _ => (1 : ℝ)) (a := c) (n := N - c) (by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  have e : univ.filter (inB (N := N) c (N - c)) = univ.filter (fun x : ZMod N => c ≤ x.val) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, inB]
    have := ZMod.val_lt x; omega
  rw [e] at h
  exact_mod_cast h.symm

lemma card_Ztop_le (K : ℕ) : (#(Ztop T p t K) : ℝ) ≤
    ∑ i ∈ range (N / 2 ^ K), (2 + 2 * (badCount T p t (i * 2 ^ K) K : ℝ)) +
      (N - N / 2 ^ K * 2 ^ K : ℕ) := by
  have h1 := Finset.card_union_le ((range (N / 2 ^ K)).biUnion fun i => Zt T p t (i * 2 ^ K) K)
    (univ.filter (fun x : ZMod N => N / 2 ^ K * 2 ^ K ≤ x.val))
  have h2 := Finset.card_biUnion_le (s := range (N / 2 ^ K)) (t := fun i => Zt T p t (i * 2 ^ K) K)
  rw [card_val_ge (Nat.div_mul_le_self N _)] at h1
  have h3 : (∑ i ∈ range (N / 2 ^ K), #(Zt T p t (i * 2 ^ K) K) : ℝ) ≤
      ∑ i ∈ range (N / 2 ^ K), (2 + 2 * (badCount T p t (i * 2 ^ K) K : ℝ)) :=
    Finset.sum_le_sum fun i _ => card_Zt_le K _
  have : (#(Ztop T p t K) : ℝ) ≤ (∑ i ∈ range (N / 2 ^ K), #(Zt T p t (i * 2 ^ K) K) : ℕ) +
      (N - N / 2 ^ K * 2 ^ K : ℕ) := by
    unfold Ztop; exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
  push_cast at this h3 ⊢
  linarith

end ThomUpper
