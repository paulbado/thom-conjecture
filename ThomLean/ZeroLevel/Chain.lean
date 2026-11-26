import ThomLean.ZeroLevel.Count
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Chain vectors in `H₃(ℤ/N)`: the finite chiral model

For `N` odd, `p, t ∈ ℤ/N` and `ξ : ℤ/N → ℂ`, let `ψ(x) = exp(2πi x/N)` and

`F^{p,t}_ξ(a,b,c) = ξ(-a-b) · ψ(pc - pab + ta - p·a(a-1)/2)`.

* **Intertwining** (`cAdj_Fv`): `A F^{p,t}_ξ = F^{p,t}_{H ξ}`, where `H = H_{p,t}` is the
  nearest-neighbour Jacobi operator on the cycle `ℤ/N`

  `(H ξ)(l) = c(l-1) ξ(l-1) + conj(c(l)) ξ(l+1)`, `c(n) = 1 + ψ(t + p(n+1))`.

  `|c(n)| = 2|cos(π(t + p(n+1))/N)|`: this is the chiral (zero-diagonal) Jacobi operator of
  Jitomirskaya–Krasovsky at flux `p/N` and phase `t/N`, in a finite periodic form.
* **Orthogonality** (`ip_Fv`): `⟨F^{p,t}_ξ, F^{p',t'}_η⟩ = N² [p = p'] [t = t'] ⟨ξ, η⟩`.

So `ℓ²(H₃(ℤ/N)) = ⨁_{p,t} {F^{p,t}_ξ}` and the spectrum of `A` is the union of the spectra of the
`N²` chain operators `H_{p,t}`. Eigenvalue counting for `A` reduces to chain quasimodes.
-/

noncomputable section

namespace ThomZeroLevel

open ThomHeisenberg ThomExistence ThomNoAtoms Finset ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- The standard character `ψ(x) = exp(2πi x/N)`. -/
abbrev ψ : AddChar (ZMod N) ℂ := ZMod.stdAddChar

/-- `(N+1)/2`, the inverse of `2` modulo an odd `N`. -/
def half (N : ℕ) : ZMod N := (((N + 1) / 2 : ℕ) : ZMod N)

lemma two_mul_half (hN : Odd N) : 2 * half N = 1 := by
  obtain ⟨k, rfl⟩ := hN
  have : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [half, this]
  have h0 : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination h0

/-- Bond coefficient `c(n) = 1 + ψ(t + p(n+1))` of the chain operator. -/
def bond (p t n : ZMod N) : ℂ := 1 + ψ (t + p * (n + 1))

/-- The chain operator `H_{p,t}` on `ℤ/N`. -/
def chainH (p t : ZMod N) (ξ : ZMod N → ℂ) (l : ZMod N) : ℂ :=
  bond p t (l - 1) * ξ (l - 1) + conj (bond p t l) * ξ (l + 1)

/-- The phase of a chain vector. -/
def phase (p t : ZMod N) (g : QPt N) : ZMod N :=
  p * g.2.2 - p * g.1 * g.2.1 + t * g.1 - p * half N * g.1 * (g.1 - 1)

/-- The chain vector `F^{p,t}_ξ` on `H₃(ℤ/N)`. -/
def Fv (p t : ZMod N) (ξ : ZMod N → ℂ) (g : QPt N) : ℂ := ξ (-g.1 - g.2.1) * ψ (phase p t g)

lemma sum_step_c (f : Step → ℂ) : ∑ s, f s = f .R + f .L + f .U + f .D := by
  rw [show (Finset.univ : Finset Step) = {Step.R, Step.L, Step.U, Step.D} from rfl]
  simp [Finset.sum_insert]
  ring

/-- **Intertwining**: `A F^{p,t}_ξ = F^{p,t}_{H_{p,t} ξ}`. -/
theorem cAdj_Fv (hN : Odd N) (p t : ZMod N) (ξ : ZMod N → ℂ) :
    cAdj (quotAct N) (Fv p t ξ) = Fv p t (chainH p t ξ) := by
  have hh := two_mul_half hN
  funext g
  obtain ⟨a, b, c⟩ := g
  have eR : phase p t (a + 1, b, c) = phase p t (a, b, c) + (t + p * (-a - b - 1 + 1)) := by
    simp only [phase]; linear_combination (-p * a) * hh
  have eL : phase p t (a - 1, b, c) = phase p t (a, b, c) + -(t + p * (-a - b + 1)) := by
    simp only [phase]; linear_combination (p * (a - 1)) * hh
  have eU : phase p t (a, b + 1, c + a) = phase p t (a, b, c) := by simp only [phase]; ring
  have eD : phase p t (a, b - 1, c - a) = phase p t (a, b, c) := by simp only [phase]; ring
  have xR : -(a + 1) - b = -a - b - 1 := by ring
  have xL : -(a - 1) - b = -a - b + 1 := by ring
  have xU : -a - (b + 1) = -a - b - 1 := by ring
  have xD : -a - (b - 1) = -a - b + 1 := by ring
  simp only [cAdj, sum_step_c, quotAct, Fv, chainH, bond]
  rw [eR, eL, eU, eD, xR, xL, xU, xD, AddChar.map_add_eq_mul ψ (phase p t (a, b, c)),
    AddChar.map_add_eq_mul ψ (phase p t (a, b, c)), map_add (starRingEnd ℂ), map_one,
    ← AddChar.map_neg_eq_conj]
  ring

/-- **Orthogonality of chain vectors**: `⟨F^{p,t}_ξ, F^{p',t'}_η⟩ = N² [p=p'] [t=t'] ⟨ξ,η⟩`. -/
theorem ip_Fv (p t p' t' : ZMod N) (ξ η : ZMod N → ℂ) :
    ip (Fv p t ξ) (Fv p' t' η) = if p = p' ∧ t = t' then (N : ℂ) ^ 2 * ip ξ η else 0 := by
  have hterm : ∀ a b c : ZMod N, conj (Fv p t ξ (a, b, c)) * Fv p' t' η (a, b, c) =
      conj (ξ (-a - b)) * η (-a - b) *
        ψ (a * (t' - t) - (p' - p) * a * b - (p' - p) * half N * a * (a - 1)) *
        ψ (c * (p' - p)) := by
    intro a b c
    simp only [Fv, map_mul, ← AddChar.map_neg_eq_conj]
    calc conj (ξ (-a - b)) * ψ (-phase p t (a, b, c)) * (η (-a - b) * ψ (phase p' t' (a, b, c)))
        = conj (ξ (-a - b)) * η (-a - b) *
            (ψ (-phase p t (a, b, c)) * ψ (phase p' t' (a, b, c))) := by ring
      _ = _ := by
        have e : ψ (-phase p t (a, b, c)) * ψ (phase p' t' (a, b, c)) =
            ψ (a * (t' - t) - (p' - p) * a * b - (p' - p) * half N * a * (a - 1)) *
              ψ (c * (p' - p)) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
          congr 1
          simp only [phase]; ring
        rw [e]; ring
  have hprim := ZMod.isPrimitive_stdAddChar N
  simp only [ip, Fintype.sum_prod_type, hterm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hprim, ZMod.card]
  by_cases hp : p = p'
  · subst hp
    simp only [sub_self, if_true, zero_mul, sub_zero, true_and]
    -- reindex `b ↦ -a - b`
    have hre : ∀ a : ZMod N, ∑ b : ZMod N, conj (ξ (-a - b)) * η (-a - b) * ψ (a * (t' - t)) *
        (N : ℂ) = ip ξ η * (N : ℂ) * ψ (a * (t' - t)) := by
      intro a
      rw [ip, Finset.sum_mul, Finset.sum_mul, ← (Equiv.subLeft (-a)).sum_comp]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Equiv.subLeft_apply]
      ring
    simp_rw [hre, ← Finset.mul_sum, AddChar.sum_mulShift _ hprim, ZMod.card, sub_eq_zero]
    by_cases ht : t = t'
    · simp [ht]; rw [ip]; ring
    · simp [ht, Ne.symm ht]
  · have : p' - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    simp [this, hp]

end ThomZeroLevel
