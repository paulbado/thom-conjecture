import ThomLean.ZeroLevel.Trig

/-!
# The quasimode family and the eigenvalue count near `0`

For odd `N`, `m ≥ 4`, `M = 11m`, `D = 2M + 3`, consider the triples `(p, t, k)` with

* `val p / N ∈ [1/2 + 9/(640m), 1/2 + 1/(64m)]` (flux slightly above `1/2`),
* `k < N / D` (start `s_k = 1 + kD`; the chains occupy disjoint bands `[kD, (k+1)D)`),
* `θ = val(t + p(s_k+1))/N ∈ [1/16, 1/8]` (good phase at the start).

Each gives the chain vector `F = F^{p,t}_{ξ}` with `ξ` the explicit quasimode of length `M`.
These vectors are pairwise orthogonal, so are their images under `A`, and
`‖A F‖² ≤ 16 (4/9)^m ‖F‖²`. Hence (`card_good_le`)

`#{triples} ≤ #{j : |λ_j| ≤ h}` whenever `16 (4/9)^m < h²`,

and the number of triples is `#P · (N/D) · #T` (`card_good`), with explicit lower bounds on
`#P` and `#T` (`card_window`).
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomExistence ThomNoAtoms Finset ComplexConjugate Real

/-! ### Generic helpers -/

lemma ip_eq_zero_of_disjoint {X : Type*} [Fintype X] (u v : X → ℂ)
    (h : ∀ l, u l = 0 ∨ v l = 0) : ip u v = 0 :=
  Finset.sum_eq_zero fun l _ => by rcases h l with h | h <;> simp [h]

lemma nrm_Fv {N : ℕ} [NeZero N] (p t : ZMod N) (ξ : ZMod N → ℂ) :
    nrm (Fv p t ξ) = (N : ℝ) ^ 2 * nrm ξ := by
  have := ip_Fv p t p t ξ ξ
  simp only [and_self, if_true, ip_self] at this
  exact_mod_cast this

/-- Lower bound for the number of residues in a window `[α, β]` of `[0,1)`. -/
lemma card_window (N : ℕ) [NeZero N] {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) :
    (N : ℝ) * (β - α) - 1 ≤
      #{x : ZMod N | α ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ β} := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set a := ⌈α * N⌉₊
  set b := ⌊β * N⌋₊
  have hβ0 : 0 ≤ β * N := by have := hα.trans hαβ; positivity
  have hb : (b : ℝ) ≤ β * N := Nat.floor_le hβ0
  have hbN : b < N := by
    have : (b : ℝ) < N := by nlinarith
    exact_mod_cast this
  have hsub : (Finset.Icc a b).card ≤
      #{x : ZMod N | α ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ β} := by
    refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ZMod N)) ?_ ?_
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hnN : n < N := lt_of_le_of_lt hn'.2 hbN
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        ZMod.val_natCast_of_lt hnN]
      constructor
      · rw [le_div_iff₀ hN]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hn'.1)
      · rw [div_le_iff₀ hN]
        exact le_trans (by exact_mod_cast hn'.2) hb
    · intro n hn n' hn' h
      have h1 : n < N := lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hbN
      have h2 : n' < N := lt_of_le_of_lt (Finset.mem_Icc.mp hn').2 hbN
      have := congrArg ZMod.val h
      simp only [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
      exact this
  have hcard : ((b : ℝ) + 1 - a) ≤ ((Finset.Icc a b).card : ℝ) := by
    rw [Nat.card_Icc]
    by_cases hab : a ≤ b + 1
    · rw [Nat.cast_sub hab]; push_cast; linarith
    · push Not at hab
      have : ((b : ℝ) + 1) < a := by exact_mod_cast hab
      have : (0 : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have ha : (a : ℝ) < α * N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hb' : β * N < b + 1 := Nat.lt_floor_add_one _
  have : ((Finset.Icc a b).card : ℝ) ≤
      #{x : ZMod N | α ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ β} := by exact_mod_cast hsub
  nlinarith

lemma card_shift {N : ℕ} [NeZero N] (P : ZMod N → Prop) [DecidablePred P] (c : ZMod N) :
    #{t : ZMod N | P (t + c)} = #{x : ZMod N | P x} := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp (Equiv.addRight c) (fun x => if P x then 1 else 0)

/-! ### The family -/

variable {N : ℕ} [NeZero N]

/-- Band length `D = 2M + 3` with `M = 11m`. -/
def bandD (m : ℕ) : ℕ := 2 * (11 * m) + 3

/-- Good fluxes. -/
def Pwin (N m : ℕ) [NeZero N] : Finset (ZMod N) :=
  {p | 1 / 2 + 9 / (640 * m) ≤ (p.val : ℝ) / N ∧ (p.val : ℝ) / N ≤ 1 / 2 + 1 / (64 * m)}

/-- Good phases. -/
def Twin (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  {x | 1 / 16 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 / 8}

/-- The index set of the quasimode family. -/
def good (N m : ℕ) [NeZero N] : Finset (ZMod N × ZMod N × ℕ) :=
  (Pwin N m ×ˢ (Finset.univ ×ˢ Finset.range (N / bandD m))).filter fun i =>
    1 / 16 ≤ theta i.1 i.2.1 (1 + i.2.2 * bandD m) ∧ theta i.1 i.2.1 (1 + i.2.2 * bandD m) ≤ 1 / 8

/-- The quasimode attached to an index. -/
def fam (m : ℕ) (i : ZMod N × ZMod N × ℕ) : QPt N → ℂ :=
  Fv i.1 i.2.1 (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m))

lemma band_bound {m k : ℕ} (hk : k < N / bandD m) : (k + 1) * bandD m ≤ N := by
  have h1 : k + 1 ≤ N / bandD m := hk
  calc (k + 1) * bandD m ≤ N / bandD m * bandD m := Nat.mul_le_mul_right _ h1
    _ ≤ N := Nat.div_mul_le_self _ _

/-- Support of the quasimode in its band. -/
lemma qmXi_band (p t : ZMod N) {m k : ℕ} (hk : (k + 1) * bandD m ≤ N) {l : ZMod N}
    (hl : qmXi p t (1 + k * bandD m) (11 * m) l ≠ 0) :
    k * bandD m ≤ l.val ∧ l.val < (k + 1) * bandD m := by
  obtain ⟨j, hj, rfl⟩ := qmXi_support p t _ _ hl
  have hE : (k + 1) * bandD m = k * bandD m + bandD m := by ring
  simp only [bandD] at hE hk ⊢
  set E := k * (2 * (11 * m) + 3)
  rw [xs, ZMod.val_natCast_of_lt (by omega)]
  omega

/-- Support of the residual in the same band. -/
lemma chainH_band (p t : ZMod N) {m k : ℕ} (hk : (k + 1) * bandD m ≤ N) {l : ZMod N}
    (hl : chainH p t (qmXi p t (1 + k * bandD m) (11 * m)) l ≠ 0) :
    k * bandD m ≤ l.val ∧ l.val < (k + 1) * bandD m := by
  have hE : (k + 1) * bandD m = k * bandD m + bandD m := by ring
  have h : qmXi p t (1 + k * bandD m) (11 * m) (l - 1) ≠ 0 ∨
      qmXi p t (1 + k * bandD m) (11 * m) (l + 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hl
    simp [chainH, hc.1, hc.2]
  rcases h with h | h
  · obtain ⟨j, hj, hjl⟩ := qmXi_support p t _ _ h
    have : l = (((1 + k * bandD m + 2 * j + 1 : ℕ)) : ZMod N) := by
      rw [sub_eq_iff_eq_add.mp hjl, xs]; push_cast; ring
    rw [this]
    simp only [bandD] at hE hk ⊢
    set E := k * (2 * (11 * m) + 3)
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega
  · obtain ⟨j, hj, hjl⟩ := qmXi_support p t _ _ h
    have : l = (((k * bandD m + 2 * j : ℕ)) : ZMod N) := by
      rw [eq_sub_of_add_eq hjl, xs]; push_cast; ring
    rw [this]
    simp only [bandD] at hE hk ⊢
    set E := k * (2 * (11 * m) + 3)
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega

lemma band_unique {m k k' v : ℕ} (h1 : k * bandD m ≤ v ∧ v < (k + 1) * bandD m)
    (h2 : k' * bandD m ≤ v ∧ v < (k' + 1) * bandD m) : k = k' :=
  (Nat.div_eq_of_lt_le h1.1 h1.2).symm.trans (Nat.div_eq_of_lt_le h2.1 h2.2)

/-- Flux window facts. -/
lemma dlt_of_Pwin {m : ℕ} (hm : 4 ≤ m) {p : ZMod N} (hp : p ∈ Pwin N m) :
    0 < dlt N p ∧ dlt N p ≤ 1 / 256 ∧ 9 / 640 ≤ m * dlt N p ∧ m * dlt N p ≤ 1 / 64 := by
  have hp' := (Finset.mem_filter.mp hp).2
  have hm0 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have e1 : 9 / (640 * m) ≤ dlt N p := by simp only [dlt]; linarith [hp'.1]
  have e2 : dlt N p ≤ 1 / (64 * m) := by simp only [dlt]; linarith [hp'.2]
  have f1 : 9 / 640 ≤ m * dlt N p := by
    rw [div_le_iff₀ (by positivity)] at e1; nlinarith
  have f2 : m * dlt N p ≤ 1 / 64 := by
    rw [le_div_iff₀ (by positivity)] at e2; nlinarith
  refine ⟨by nlinarith, by nlinarith, f1, f2⟩

/-- The quasimode estimate for a member of the family. -/
lemma fam_qm {m : ℕ} (hm : 4 ≤ m) {i : ZMod N × ZMod N × ℕ} (hi : i ∈ good N m) :
    nrm (chainH i.1 i.2.1 (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m))) ≤
        16 * (4 / 9 : ℝ) ^ m * nrm (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m)) ∧
      1 ≤ nrm (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m)) := by
  obtain ⟨p, t, k⟩ := i
  simp only [good, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_range] at hi
  obtain ⟨⟨hp, hk⟩, hθ1, hθ2⟩ := hi
  obtain ⟨hδ0, hδ1, f1, f2⟩ := dlt_of_Pwin hm hp
  have hb := band_bound hk
  have hE : (k + 1) * bandD m = k * bandD m + bandD m := by ring
  refine qm_of_phase p t ?_ hθ1 hθ2 hδ0 hδ1 ?_ ?_ ?_
  · simp only [bandD] at hE hb ⊢
    set E := k * (2 * (11 * m) + 3)
    omega
  · linarith
  · push_cast; linarith
  · push_cast; nlinarith

/-- **Eigenvalue count from the quasimode family.** -/
theorem card_good_le (hN : Odd N) {h : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 4 ≤ m)
    (hε : 16 * (4 / 9 : ℝ) ^ m < h ^ 2) :
    #(good N m) ≤ #{j | |(adj_isHermitian (quotAct_rev N)).eigenvalues j| ≤ h} := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  have hband : ∀ i ∈ good N m, (i.2.2 + 1) * bandD m ≤ N := by
    intro i hi
    simp only [good, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hi
    exact band_bound hi.1.2
  -- orthogonality of the chain vectors of one `(p,t)`
  have horth : ∀ i ∈ good N m, ∀ k ∈ good N m, i ≠ k →
      ∀ (u v : ZMod N × ZMod N × ℕ → ZMod N → ℂ),
      (∀ j ∈ good N m, ∀ l, u j l ≠ 0 →
        j.2.2 * bandD m ≤ l.val ∧ l.val < (j.2.2 + 1) * bandD m) →
      (∀ j ∈ good N m, ∀ l, v j l ≠ 0 →
        j.2.2 * bandD m ≤ l.val ∧ l.val < (j.2.2 + 1) * bandD m) →
      ip (Fv i.1 i.2.1 (u i)) (Fv k.1 k.2.1 (v k)) = 0 := by
    intro i hi k hk hik u v hu hv
    rw [ip_Fv]
    split_ifs with hpt
    · have hkk : i.2.2 ≠ k.2.2 := fun h => hik (Prod.ext hpt.1 (Prod.ext hpt.2 h))
      rw [ip_eq_zero_of_disjoint, mul_zero]
      intro l
      by_contra hc
      push Not at hc
      exact hkk (band_unique (hu i hi l hc.1) (hv k hk l hc.2))
    · rfl
  have hξband : ∀ j ∈ good N m, ∀ l, qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m) l ≠ 0 →
      j.2.2 * bandD m ≤ l.val ∧ l.val < (j.2.2 + 1) * bandD m :=
    fun j hj l hl => qmXi_band _ _ (hband j hj) hl
  have hHband : ∀ j ∈ good N m, ∀ l,
      chainH j.1 j.2.1 (qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m)) l ≠ 0 →
      j.2.2 * bandD m ≤ l.val ∧ l.val < (j.2.2 + 1) * bandD m :=
    fun j hj l hl => chainH_band _ _ (hband j hj) hl
  refine card_le_of_quasimodes (quotAct_rev N) (good N m) (fam m) hh hε ?_ ?_ ?_ ?_
  · intro i hi
    rw [fam, nrm_Fv]
    have := (fam_qm hm hi).2
    positivity
  · intro i hi
    rw [fam, cAdj_Fv hN, nrm_Fv, nrm_Fv]
    have := (fam_qm hm hi).1
    calc (N : ℝ) ^ 2 * nrm (chainH i.1 i.2.1 (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m)))
        ≤ (N : ℝ) ^ 2 * (16 * (4 / 9 : ℝ) ^ m *
            nrm (qmXi i.1 i.2.1 (1 + i.2.2 * bandD m) (11 * m))) :=
          mul_le_mul_of_nonneg_left this hN2.le
      _ = _ := by ring
  · intro i hi k hk hik
    exact horth i hi k hk hik (fun j => qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m))
      (fun j => qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m)) hξband hξband
  · intro i hi k hk hik
    simp only [fam, cAdj_Fv hN]
    exact horth i hi k hk hik
      (fun j => chainH j.1 j.2.1 (qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m)))
      (fun j => chainH j.1 j.2.1 (qmXi j.1 j.2.1 (1 + j.2.2 * bandD m) (11 * m))) hHband hHband

/-- **Size of the family**: `#good = #P · (N/D) · #T`. -/
theorem card_good (m : ℕ) : #(good N m) = #(Pwin N m) * (N / bandD m) * #(Twin N) := by
  rw [good, Finset.card_filter, Finset.sum_product, Finset.card_eq_sum_ones (Pwin N m),
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_product, Finset.sum_comm, one_mul]
  have : ∀ k ∈ Finset.range (N / bandD m), (∑ t : ZMod N,
      if 1 / 16 ≤ theta p t (1 + k * bandD m) ∧ theta p t (1 + k * bandD m) ≤ 1 / 8 then 1 else 0)
        = #(Twin N) := by
    intro k _
    rw [← Finset.card_filter]
    exact card_shift (fun x : ZMod N => 1 / 16 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 / 8)
      (p * (((1 + k * bandD m : ℕ) : ZMod N) + 1))
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]

end ThomZeroLevel
