import ThomLean.Heisenberg.Group
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Finset.Max

/-!
# Discrete isoperimetric inequality for the algebraic area of closed lattice walks

Bado–Pittet, Lemma 3.2 (first part). For a closed nearest-neighbour walk with `r` steps to
the right and `s` steps up,

  `|area| ≤ r * s`,  hence  `16 * |area| ≤ length²`.

The proof follows the manuscript: the horizontal range of a closed walk is at most `r`
(`range_le`), and after translating so that the leftmost visited column is `0`, the up-steps
contribute at most `range` each and the down-steps at least `-range` each (`areaFrom_bounds`).
All results here are unconditional.
-/

namespace ThomHeisenberg

open Step

/-- Number of occurrences of a given step. -/
def cnt (t : Step) : List Step → ℕ
  | [] => 0
  | s :: w => (if s = t then 1 else 0) + cnt t w

@[simp] lemma cnt_nil (t : Step) : cnt t [] = 0 := rfl
@[simp] lemma cnt_cons (t s : Step) (w : List Step) :
    cnt t (s :: w) = (if s = t then 1 else 0) + cnt t w := rfl

lemma length_eq_cnt (w : List Step) : w.length = cnt R w + cnt L w + cnt U w + cnt D w := by
  induction w with
  | nil => rfl
  | cons s w ih => cases s <;> simp [ih] <;> omega

lemma xEnd_eq_cnt (w : List Step) : xEnd w = (cnt R w : ℤ) - cnt L w := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp [ih, Step.dx] <;> ring

lemma yEnd_eq_cnt (w : List Step) : yEnd w = (cnt U w : ℤ) - cnt D w := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp [ih, Step.dy] <;> ring

lemma IsClosed.cnt_RL {w : List Step} (h : IsClosed w) : cnt R w = cnt L w := by
  have := h.1; rw [xEnd_eq_cnt] at this; omega

lemma IsClosed.cnt_UD {w : List Step} (h : IsClosed w) : cnt U w = cnt D w := by
  have := h.2; rw [yEnd_eq_cnt] at this; omega

lemma IsClosed.length_eq {w : List Step} (h : IsClosed w) :
    w.length = 2 * (cnt R w + cnt U w) := by
  rw [length_eq_cnt, ← h.cnt_RL, ← h.cnt_UD]; ring

/-- Horizontal positions visited by the walk started at `x₀` (including start and end). -/
def xs : ℤ → List Step → List ℤ
  | x₀, [] => [x₀]
  | x₀, s :: w => x₀ :: xs (x₀ + s.dx) w

@[simp] lemma xs_nil (x₀ : ℤ) : xs x₀ [] = [x₀] := rfl
@[simp] lemma xs_cons (x₀ : ℤ) (s : Step) (w : List Step) :
    xs x₀ (s :: w) = x₀ :: xs (x₀ + s.dx) w := rfl

lemma start_mem_xs (x₀ : ℤ) (w : List Step) : x₀ ∈ xs x₀ w := by
  cases w <;> simp

/-- Any visited column is reached from the start using at most `#R` right steps and
at most `#L` left steps. -/
lemma reach (x₀ : ℤ) (w : List Step) :
    ∀ b ∈ xs x₀ w, b - x₀ ≤ cnt R w ∧ x₀ - b ≤ cnt L w := by
  induction w generalizing x₀ with
  | nil => intro b hb; simp at hb; subst hb; simp
  | cons s w ih =>
    intro b hb
    simp only [xs_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp only [sub_self, cnt_cons]; push_cast; split_ifs <;> constructor <;> positivity
    · have := ih _ b hb
      cases s <;> simp [Step.dx] at this ⊢ <;> push_cast <;> omega

/-- Order-sensitive range bound: if column `a` is visited before column `b`, then
`b - a ≤ #R` and `a - b ≤ #L`. -/
lemma pairwise_xs (x₀ : ℤ) (w : List Step) :
    (xs x₀ w).Pairwise (fun a b => b - a ≤ (cnt R w : ℤ) ∧ a - b ≤ (cnt L w : ℤ)) := by
  induction w generalizing x₀ with
  | nil => simp
  | cons s w ih =>
    simp only [xs_cons, List.pairwise_cons]
    refine ⟨fun b hb => reach x₀ (s :: w) b (by simp [hb]), ?_⟩
    refine (ih (x₀ + s.dx)).imp ?_
    intro a b ⟨h1, h2⟩
    constructor <;> simp only [cnt_cons] <;> push_cast <;> split_ifs <;> push_cast <;> omega

/-- For a walk with `#R = #L = r`, any two visited columns differ by at most `r`. -/
lemma abs_sub_le_of_mem (x₀ : ℤ) (w : List Step) (hRL : cnt R w = cnt L w) :
    ∀ a ∈ xs x₀ w, ∀ b ∈ xs x₀ w, b - a ≤ (cnt R w : ℤ) := by
  have hp := pairwise_xs x₀ w
  have key : ∀ (l : List ℤ), l.Pairwise (fun a b => b - a ≤ (cnt R w : ℤ) ∧ a - b ≤ (cnt L w : ℤ)) →
      ∀ a ∈ l, ∀ b ∈ l, b - a ≤ (cnt R w : ℤ) := by
    intro l hl
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [List.pairwise_cons] at hl
      intro a ha b hb
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · simp
      · exact (hl.1 b hb).1
      · have := (hl.1 a ha).2; rw [hRL]; exact this
      · exact ih hl.2 a ha b hb
  exact key _ hp

/-- Area bounds relative to a column window `[lo, hi]` containing every visited column. -/
lemma areaFrom_bounds (x₀ lo hi : ℤ) (w : List Step)
    (hw : ∀ v ∈ xs x₀ w, lo ≤ v ∧ v ≤ hi) :
    areaFrom x₀ w - lo * yEnd w ≤ (hi - lo) * cnt U w ∧
      -((hi - lo) * cnt D w) ≤ areaFrom x₀ w - lo * yEnd w := by
  induction w generalizing x₀ with
  | nil => simp
  | cons s w ih =>
    have h0 := hw x₀ (by simp)
    have ih' := ih (x₀ + s.dx) (fun v hv => hw v (by simp [hv]))
    cases s <;> simp only [areaFrom_cons, yEnd_cons, cnt_cons, Step.dy] at ih' ⊢ <;>
      simp <;> push_cast <;> constructor <;> nlinarith [ih'.1, ih'.2, h0.1, h0.2]

/-- **Discrete isoperimetric inequality** (Bado–Pittet, Lemma 3.2):
a closed walk with `r` right steps and `s` up steps has `|area| ≤ r s`. -/
theorem abs_area_le (w : List Step) (hw : IsClosed w) :
    |area w| ≤ (cnt R w : ℤ) * cnt U w := by
  classical
  set l := xs 0 w with hl
  have hne : l.toFinset.Nonempty := ⟨0, by simp [hl, start_mem_xs]⟩
  set lo := l.toFinset.min' hne
  set hi := l.toFinset.max' hne
  have hlo : lo ∈ l := by simpa using l.toFinset.min'_mem hne
  have hhi : hi ∈ l := by simpa using l.toFinset.max'_mem hne
  have hwin : ∀ v ∈ xs 0 w, lo ≤ v ∧ v ≤ hi := fun v hv =>
    ⟨l.toFinset.min'_le v (by simpa [hl] using hv), l.toFinset.le_max' v (by simpa [hl] using hv)⟩
  have hrange : hi - lo ≤ cnt R w := abs_sub_le_of_mem 0 w hw.cnt_RL lo hlo hi hhi
  have hrange0 : 0 ≤ hi - lo := sub_nonneg.mpr (l.toFinset.min'_le_max' hne)
  have hb := areaFrom_bounds 0 lo hi w hwin
  have hy : yEnd w = 0 := hw.2
  rw [hy, mul_zero, sub_zero] at hb
  have hUD : (cnt D w : ℤ) = cnt U w := by exact_mod_cast hw.cnt_UD.symm
  rw [hUD] at hb
  have hU : (0 : ℤ) ≤ cnt U w := by positivity
  rw [abs_le]
  unfold area
  constructor <;> nlinarith [hb.1, hb.2]

/-- `16 |area| ≤ n²` for a closed walk of length `n`. -/
theorem sixteen_abs_area_le (w : List Step) (hw : IsClosed w) :
    16 * |area w| ≤ (w.length : ℤ) ^ 2 := by
  have h := abs_area_le w hw
  rw [hw.length_eq]; push_cast
  nlinarith [sq_nonneg ((cnt R w : ℤ) - cnt U w)]

/-- Closed walks have even length. -/
lemma IsClosed.even_length {w : List Step} (hw : IsClosed w) : Even w.length :=
  ⟨cnt R w + cnt U w, by rw [hw.length_eq]; ring⟩

end ThomHeisenberg
