import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The discrete Heisenberg group, lattice words, and algebraic area

Coordinates `(a, b, c) ∈ ℤ³` with the law (Bado–Pittet, eq. (11))
`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`.

Main results (all unconditional):

* `H3` is a group; `x y z` are the standard generators, `x * y = z * y * x`, `z` is central,
  and `H3` is torsion-free (`H3.eq_one_of_pow_eq_one`).
* `evalWord_eq` : a word in `x^{±1}, y^{±1}` evaluates to
  `(endpoint_x, endpoint_y, algebraic area)` of the associated lattice walk.
* `evalWord_eq_one_iff` : a word is trivial in `H3` iff its walk is closed with zero area.
-/

namespace ThomHeisenberg

/-- The discrete Heisenberg group `H₃(ℤ)` in coordinates. -/
@[ext] structure H3 where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

namespace H3

instance : Mul H3 := ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One H3 := ⟨⟨0, 0, 0⟩⟩
instance : Inv H3 := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩

@[simp] lemma mul_a (g h : H3) : (g * h).a = g.a + h.a := rfl
@[simp] lemma mul_b (g h : H3) : (g * h).b = g.b + h.b := rfl
@[simp] lemma mul_c (g h : H3) : (g * h).c = g.c + h.c + g.a * h.b := rfl
@[simp] lemma one_a : (1 : H3).a = 0 := rfl
@[simp] lemma one_b : (1 : H3).b = 0 := rfl
@[simp] lemma one_c : (1 : H3).c = 0 := rfl
@[simp] lemma inv_a (g : H3) : g⁻¹.a = -g.a := rfl
@[simp] lemma inv_b (g : H3) : g⁻¹.b = -g.b := rfl
@[simp] lemma inv_c (g : H3) : g⁻¹.c = -g.c + g.a * g.b := rfl

instance : Group H3 where
  mul_assoc f g h := by ext <;> simp only [mul_a, mul_b, mul_c] <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

/-- Standard generators. -/
def x : H3 := ⟨1, 0, 0⟩
def y : H3 := ⟨0, 1, 0⟩
def z : H3 := ⟨0, 0, 1⟩

theorem x_mul_y : x * y = z * y * x := by ext <;> simp [x, y, z]

theorem commutator_xy : x * y * x⁻¹ * y⁻¹ = z := by ext <;> simp [x, y, z]

theorem z_central (g : H3) : z * g = g * z := by ext <;> simp [z]; ring

lemma pow_a (g : H3) (n : ℕ) : (g ^ n).a = n * g.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

lemma pow_b (g : H3) (n : ℕ) : (g ^ n).b = n * g.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

lemma pow_c_of_a_eq_zero (g : H3) (hg : g.a = 0) (n : ℕ) : (g ^ n).c = n * g.c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_c, ih, pow_a, hg]; push_cast; ring

/-- `H₃(ℤ)` is torsion-free. -/
theorem eq_one_of_pow_eq_one {g : H3} {n : ℕ} (hn : n ≠ 0) (h : g ^ n = 1) : g = 1 := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have ha : g.a = 0 := by
    have := congrArg H3.a h; rw [pow_a] at this; simpa [hn] using this
  have hb : g.b = 0 := by
    have := congrArg H3.b h; rw [pow_b] at this; simpa [hn] using this
  have hc : g.c = 0 := by
    have := congrArg H3.c h; rw [pow_c_of_a_eq_zero g ha] at this; simpa [hn] using this
  ext <;> simp [ha, hb, hc]

end H3

open H3

/-- The four lattice steps, corresponding to `x, x⁻¹, y, y⁻¹`. -/
inductive Step
  | R | L | U | D
deriving DecidableEq, Repr

namespace Step

instance : Fintype Step := ⟨{R, L, U, D}, by intro s; cases s <;> simp⟩

/-- Group element of a step. -/
def gen : Step → H3
  | R => x
  | L => x⁻¹
  | U => y
  | D => y⁻¹

/-- Horizontal increment. -/
def dx : Step → ℤ
  | R => 1
  | L => -1
  | U => 0
  | D => 0

/-- Vertical increment. -/
def dy : Step → ℤ
  | R => 0
  | L => 0
  | U => 1
  | D => -1

lemma gen_eq (s : Step) : s.gen = ⟨s.dx, s.dy, 0⟩ := by
  cases s <;> ext <;> simp [gen, dx, dy, x, y]

lemma card_univ : (Finset.univ : Finset Step).card = 4 := rfl

end Step

/-- Horizontal coordinate of the endpoint. -/
def xEnd (w : List Step) : ℤ := (w.map Step.dx).sum
/-- Vertical coordinate of the endpoint. -/
def yEnd (w : List Step) : ℤ := (w.map Step.dy).sum

/-- Signed area `∑ x_k (y_{k+1} - y_k)` of the walk started at horizontal position `x₀`. -/
def areaFrom : ℤ → List Step → ℤ
  | _, [] => 0
  | x₀, s :: w => x₀ * s.dy + areaFrom (x₀ + s.dx) w

/-- Signed algebraic area of the lattice walk of a word, started at the origin. -/
def area (w : List Step) : ℤ := areaFrom 0 w

@[simp] lemma xEnd_nil : xEnd [] = 0 := rfl
@[simp] lemma yEnd_nil : yEnd [] = 0 := rfl
@[simp] lemma xEnd_cons (s : Step) (w : List Step) : xEnd (s :: w) = s.dx + xEnd w := by
  simp [xEnd]
@[simp] lemma yEnd_cons (s : Step) (w : List Step) : yEnd (s :: w) = s.dy + yEnd w := by
  simp [yEnd]
@[simp] lemma areaFrom_nil (x₀ : ℤ) : areaFrom x₀ [] = 0 := rfl
@[simp] lemma areaFrom_cons (x₀ : ℤ) (s : Step) (w : List Step) :
    areaFrom x₀ (s :: w) = x₀ * s.dy + areaFrom (x₀ + s.dx) w := rfl

/-- Horizontal translation changes the area by `t ·` (net vertical displacement). -/
lemma areaFrom_add (x₀ t : ℤ) (w : List Step) :
    areaFrom (x₀ + t) w = t * yEnd w + areaFrom x₀ w := by
  induction w generalizing x₀ with
  | nil => simp
  | cons s w ih =>
    simp only [areaFrom_cons, yEnd_cons]
    rw [show x₀ + t + s.dx = (x₀ + s.dx) + t by ring, ih]; ring

lemma areaFrom_eq (x₀ : ℤ) (w : List Step) : areaFrom x₀ w = x₀ * yEnd w + area w := by
  simpa [area] using areaFrom_add 0 x₀ w

@[simp] lemma area_nil : area [] = 0 := rfl
lemma area_cons (s : Step) (w : List Step) : area (s :: w) = s.dx * yEnd w + area w := by
  unfold area
  rw [areaFrom_cons, zero_mul, zero_add, show (0 : ℤ) + s.dx = 0 + s.dx from rfl, areaFrom_add]

lemma areaFrom_append (x₀ : ℤ) (v w : List Step) :
    areaFrom x₀ (v ++ w) = areaFrom x₀ v + areaFrom (x₀ + xEnd v) w := by
  induction v generalizing x₀ with
  | nil => simp
  | cons s v ih => simp only [List.cons_append, areaFrom_cons, ih, xEnd_cons]; ring_nf

/-- Evaluation of a word in `H₃(ℤ)`. -/
def evalWord (w : List Step) : H3 := (w.map Step.gen).prod

@[simp] lemma evalWord_nil : evalWord [] = 1 := rfl
@[simp] lemma evalWord_cons (s : Step) (w : List Step) :
    evalWord (s :: w) = s.gen * evalWord w := by simp [evalWord]

/-- **Word/walk dictionary.** The first two coordinates are the endpoint of the lattice
walk, and the central coordinate is its signed algebraic area. -/
theorem evalWord_eq (w : List Step) : evalWord w = ⟨xEnd w, yEnd w, area w⟩ := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    rw [evalWord_cons, ih, Step.gen_eq, area_cons]
    ext <;> simp; ring

/-- A word is trivial in `H₃(ℤ)` iff its lattice walk is closed and has zero signed area. -/
theorem evalWord_eq_one_iff (w : List Step) :
    evalWord w = 1 ↔ xEnd w = 0 ∧ yEnd w = 0 ∧ area w = 0 := by
  rw [evalWord_eq]
  constructor
  · intro h
    exact ⟨congrArg H3.a h, congrArg H3.b h, congrArg H3.c h⟩
  · rintro ⟨h1, h2, h3⟩; ext <;> simp [h1, h2, h3]

/-- Closed walks: endpoint at the origin. -/
def IsClosed (w : List Step) : Prop := xEnd w = 0 ∧ yEnd w = 0

instance (w : List Step) : Decidable (IsClosed w) := by unfold IsClosed; infer_instance

end ThomHeisenberg
