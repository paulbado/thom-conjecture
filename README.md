# thom-conjecture — Lean formalization scaffold

Lean 4 / Mathlib project accompanying the Bado–Pittet work on spectral measures
(Harper–Heisenberg element `A = x + x⁻¹ + y + y⁻¹`).

**Status.** `ThomLean/Chebyshev.lean` compiles against Mathlib `v4.36.0`
(Lean `v4.36.0`). The lemma `weightedEnergy_le_squareEnergy` is proved and
depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
The absolute-continuity question for the Heisenberg spectral measure is **open**:
it appears only as a named `Prop` (`ChebyshevL2Target`), never as an axiom.

## Build

```sh
lake exe cache get   # optional; downloads prebuilt Mathlib
lake build
```

## Roadmap

1. ✅ `weightedEnergy_le_squareEnergy`.
2. Arcsine measure on (−4, 4) as the pushforward of normalized Lebesgue measure on [0, π] under θ ↦ 4 cos θ.
3. Orthogonality and completeness of rescaled Chebyshev polynomials `T_n(E/4)` in `L²(ρ)`
   (Mathlib already has orthogonality on [−1, 1]: `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean`).
4. `ChebyshevL2Target → μ ≪ Lebesgue` with the exact `L²(ρ)` norm identity.
5. Relate `c_n` to trace moments `τ(T_n(A/4))`.
6. The missing bound itself, without axioms.
