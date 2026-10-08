import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import ArtinPrimitiveRoots.Proofs.a2_cond_b.Sign

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
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorInfiniteComponent_card_le
      𝓧 (fun ω hω => (h𝓧 ω hω).1)
  · let τset := 𝓧.image conductorInfiniteComponent
    let pairset := 𝓧.image (fun ω => (SComponent S ω, conductorInfiniteComponent ω))
    have hsubset : pairset ⊆ 𝓛S.product τset := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨ω, hω, rfl⟩
      exact Finset.mem_product.mpr
        ⟨(h𝓧 ω hω).2, Finset.mem_image_of_mem _ hω⟩
    have hinf := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorInfiniteComponent_card_le
      𝓧 (fun ω hω => (h𝓧 ω hω).1)
    calc
      pairset.card ≤ (𝓛S.product τset).card := Finset.card_le_card hsubset
      _ = 𝓛S.card * τset.card := Finset.card_product 𝓛S τset
      _ ≤ 𝓛S.card * 2 ^ NumberField.InfinitePlace.nrRealPlaces F :=
        Nat.mul_le_mul_left _ hinf
  · intro f
    exact Finset.sum_fiberwise_of_maps_to
      (fun ω hω => Finset.mem_image_of_mem _ hω) (fun ω => f ω)
  · intro ω ω' hω hω' hcomp J hJ
    exact ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSupported_idealValue_eq_and_norm
      S ω ω' hω hω' hcomp hJ

end ArtinPrimitiveRoots.A2
