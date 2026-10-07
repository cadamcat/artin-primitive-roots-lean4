import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNEuler
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

/-!
# QS-ANALYTIC, RN-C: the quadratic class field of a quadratic ray character

For a nontrivial quadratic ray character `ψ` of a totally complex field `K`, the class field of
`ker ψ` (ClassFieldTheory's `GlobalClassFieldComparison.rayClassSubgroup_existence`) is a quadratic,
totally complex extension `E/K`, unramified outside the modulus, whose Artin map sends a prime class
to arithmetic Frobenius.  At a place `v` outside the modulus, `v` splits in `E` when `ψ(v) = 1` and
is inert when `ψ(v) = -1`; hence the local Euler factor of `ζ_E` at `v` is
`(1 - N v^{-s})⁻¹ (1 - ψ(v) N v^{-s})⁻¹`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- RN-C: the quadratic class field of a nontrivial quadratic ray character, with its degree,
signature and the local Euler factors at the places outside the modulus. -/
theorem qsa_quadratic_class_field [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hsq : ψ⁻¹ = ψ) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      InfinitePlace.nrRealPlaces E = 0 ∧
      InfinitePlace.nrComplexPlaces E = 2 * InfinitePlace.nrComplexPlaces K ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support → ∀ s : ℂ,
        ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
            (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ *
            (1 - Hecke.charValue ψ v.asIdeal *
              ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  sorry

end ArtinPrimitiveRoots.A2
