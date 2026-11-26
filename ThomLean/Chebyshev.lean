import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Thom / Harper–Heisenberg: Chebyshev regularity project

Research scaffold based on the two uploaded Bado–Pittet working manuscripts.

STATUS: Compiles against Mathlib v4.36.0 (Lean 4.36.0). All theorems use only the standard
axioms (propext, Classical.choice, Quot.sound). The research targets are `def`s (propositions),
never assumed. See `ThomLean.Bridge` for the version stated for the Heisenberg trace moments.
No theorem about absolute continuity of the Heisenberg spectral measure is claimed.

The code below cleanly separates a finite, elementary estimate from the
research target. The research target is recorded as a *def*, not assumed
as an axiom or used to prove anything.
-/

noncomputable section

namespace ThomChebyshev

open scoped BigOperators
open Finset

/-- A finite truncation of the logarithmically weighted square energy. -/
def weightedEnergy (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (c n)^2 / (n : ℝ)

/-- A finite truncation of the unweighted square energy. -/
def squareEnergy (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (c n)^2

/-- Easy direction: square summability controls logarithmically weighted
square summability. The missing direction is NOT valid for arbitrary sequences. -/
theorem weightedEnergy_le_squareEnergy (c : ℕ → ℝ) (N : ℕ) :
    weightedEnergy c N ≤ squareEnergy c N := by
  unfold weightedEnergy squareEnergy
  apply Finset.sum_le_sum
  intro n hn
  have hn1_nat : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1_nat
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  apply (div_le_iff₀ hnpos).2
  nlinarith [sq_nonneg (c n)]

/-- Target condition (not a theorem): square-summability of Chebyshev
coefficients of the spectral measure. `c n = ∫ T_n(E/4) dμ(E)` is to be
formalized once the relevant functional calculus and spectral measure are built. -/
def ChebyshevL2Target (c : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => (c (n + 1)) ^ 2)

/-- Weaker weighted condition, insufficient by itself for L² density. -/
def ChebyshevWeightedCondition (c : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => (c (n + 1)) ^ 2 / (n + 1 : ℝ))

/-- The unresolved analytic task in the Harper–Heisenberg approach.
This is merely a *name for a proposition*, not an assertion that it holds. -/
def MissingChebyshevGain (c : ℕ → ℝ) : Prop :=
  ChebyshevL2Target c

/-- **Abstract obstruction** (research note): the weighted condition does not imply the
`L²` target for arbitrary sequences. Witness: `c_n = n^{-1/2}`. -/
theorem weighted_not_imp_L2 :
    ∃ c : ℕ → ℝ, ChebyshevWeightedCondition c ∧ ¬ ChebyshevL2Target c := by
  refine ⟨fun n => Real.sqrt (1 / n), ?_, ?_⟩
  · unfold ChebyshevWeightedCondition
    have h : (fun n : ℕ => Real.sqrt (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 / (n + 1 : ℝ)) =
        fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
      ext n
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      field_simp
    simp only [h]
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.congr
      (fun n => by push_cast; ring_nf)
  · unfold ChebyshevL2Target
    intro hs
    have h : (fun n : ℕ => Real.sqrt (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) =
        fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) := by
      ext n; rw [Real.sq_sqrt (by positivity)]
    simp only [h] at hs
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hs)

end ThomChebyshev
