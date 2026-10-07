import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNClassField
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNAgree

/-!
# QS-ANALYTIC, RN-R: root number `+1` for a quadratic ray character

Let `E/K` be the quadratic class field of `ψ` (RN-C).  Grouping the Euler product of `ζ_E` over
the places of `K` (RN-E) gives, for `Re s > 1`,
`ζ_E(s) P(s) = ζ_K(s) L(s, ψ) Q(s)` with finite products `P, Q` over the places of the modulus.
With the completed Dedekind functions `ξ_E`, `ξ_K` (`Hecke.dedekind_completed`) and
`Λ = hkCompleted ψ` (RN-A) this reads `ξ_E P = ξ_K Λ D^{s/2} Q` for a positive constant `D`,
an identity of entire functions.  The functional equations of `ξ_E`, `ξ_K` and
`Λ(s) = W Λ(1-s)` (HK-FE export, `ψ⁻¹ = ψ`) give
`ξ_K(s) Λ(1-s) (W D^{s/2} Q(s) P(1-s) - D^{(1-s)/2} Q(1-s) P(s)) = 0`; the first factors do not
vanish near a large real `s`, so the bracket vanishes identically, and at `s = 1/2` it is
`(W - 1) D^{1/4} Q(1/2) P(1/2)` with `P(1/2) Q(1/2) ≠ 0`.  Hence `W = 1`.
No conductor-discriminant formula and no information at the places of the modulus is needed.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- RN-R: a primitive nontrivial quadratic ray character has root number `+1`. -/
theorem qsa_hkCompleted_one_sub [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hsq : ψ⁻¹ = ψ) (hp : Hecke.HKPrimitive ψ)
    (s : ℂ) : Hecke.hkCompleted ψ (1 - s) = Hecke.hkCompleted ψ s := by
  sorry

end ArtinPrimitiveRoots.A2
