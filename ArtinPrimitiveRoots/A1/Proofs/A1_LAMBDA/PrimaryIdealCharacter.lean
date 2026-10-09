import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Compose OAI.CompletedGauss.primaryGeneratorHom with the zero-preserving normalized angular map; norm_mul also handles zero.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem primary_ideal_character_exists (σ : E →+* ℂ) :
    ∃ φ : Ideal OE →*₀ ℂ, ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖ := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
