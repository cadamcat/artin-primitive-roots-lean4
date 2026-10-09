import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: D.hζ12 gives a primitive cubic fourth power; use the cyclotomic power basis or embeddingsEquivPrimitiveRoots, aligned on omega.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem aligned_eisenstein_embedding_exists (D : FieldData F) :
    ∃ ι : E →ₐ[ℚ] F, ι (algebraMap OE E omega) = D.ζ12 ^ 4 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
