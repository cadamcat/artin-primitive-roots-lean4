import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.primitive_conductor_residue_bridge

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A common finite/infinite component and residue realization determine the
full idelic character. Guide: sol-thin-a2zf/PROOFS.md:680–693.
Uses HK-DICT-RAY prime-value uniqueness off the finite conductor support.
This is the injectivity clause needed to sum over a subset of residue characters. -/
theorem primitive_conductor_residue_determines (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (q : S.ExtIdeal) (lambdaq : MulChar (ConductorResidueRing q) ℂ)
    (ω ω' : A1.HeckeChar F) (hω : IsOfFinOrder ω) (hω' : IsOfFinOrder ω')
    (f f' : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (hf' : IsPrimitiveConductor ω' f')
    (hℓ : SComponent S ω = ℓ) (hℓ' : SComponent S ω' = ℓ)
    (hτ : conductorInfiniteComponent ω = τ) (hτ' : conductorInfiniteComponent ω' = τ)
    (h : ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω)
    (h' : ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω') : ω = ω' := by
  sorry

end ArtinPrimitiveRoots.A2
