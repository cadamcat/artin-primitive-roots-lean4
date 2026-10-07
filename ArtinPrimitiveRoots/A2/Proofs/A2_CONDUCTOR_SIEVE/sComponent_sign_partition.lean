import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The infinite image of a finite-order family has at most 2^r1 elements;
partition by exact finite/infinite components, and recover the common supported-S
ideal weight with modulus at most one. Guide: sol-thin-a2zf/PROOFS.md:658–665.
Uses finite-order triviality on connected archimedean units; feeds assembly. -/
theorem sComponent_sign_partition (S : A1.SData F CE condη)
    (𝓛S : Finset (SLocalCharacter S)) (𝓧 : Finset (A1.HeckeChar F))
    (h𝓧 : ∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S) :
    (𝓧.image conductorInfiniteComponent).card ≤ 2 ^ NumberField.InfinitePlace.nrRealPlaces F ∧
    (𝓧.image (fun ω => (SComponent S ω, conductorInfiniteComponent ω))).card ≤
      𝓛S.card * 2 ^ NumberField.InfinitePlace.nrRealPlaces F ∧
    (∀ f : A1.HeckeChar F → ℝ,
      ∑ p ∈ 𝓧.image (fun ω => (SComponent S ω, conductorInfiniteComponent ω)),
        ∑ ω ∈ 𝓧.filter (fun ω => (SComponent S ω, conductorInfiniteComponent ω) = p),
          f ω = ∑ ω ∈ 𝓧, f ω) ∧
    (∀ (ω ω' : A1.HeckeChar F), IsOfFinOrder ω → IsOfFinOrder ω' →
      SComponent S ω = SComponent S ω' →
      ∀ J : Ideal (𝓞 F), ConductorSupportedAtS S J →
        ω.idealValue J = ω'.idealValue J ∧ ‖ω.idealValue J‖ ≤ 1) := by
  sorry

end ArtinPrimitiveRoots.A2
