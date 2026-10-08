import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.ideal_S_exterior_split_count
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Minimal finite conductor gives an ideal-primitive residue character on its
exact exterior part. The inverse local factor has the rational-idele orientation,
and equality includes nonunits. Infinite components retain real-place signs.
Guide: sol-thin-a2zf/PROOFS.md:666–693.
Uses ideal_S_exterior_split_count, exact localization, and HK-DICT-RAY. -/
theorem primitive_conductor_residue_bridge (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (hℓ : SComponent S ω = ℓ) (hτ : conductorInfiniteComponent ω = τ) :
    (∀ a : Fˣ, ‖conductorLambdaS S ℓ τ a‖ = 1) ∧
    ∃ q : S.ExtIdeal, q.1 = conductorExteriorPart S f ∧
      Ideal.absNorm q.1 ≤ Ideal.absNorm f ∧
      ∃ lambdaq : MulChar (ConductorResidueRing q) ℂ,
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals lambdaq ∧
        ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω := by
  sorry

end ArtinPrimitiveRoots.A2
