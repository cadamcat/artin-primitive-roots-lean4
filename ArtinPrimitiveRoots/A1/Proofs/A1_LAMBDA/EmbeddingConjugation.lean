import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Adapt OAI.ringComplex_conjO with arbitrary embedding: a complex cubic root has norm one, and conjugation sends omega to its square.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem eisenstein_embedding_conjugation (σ : E →+* ℂ) (a : OE) :
    integerComplex σ (OAI.ActualEisensteinCubic.conjO a) =
      (starRingEnd ℂ) (integerComplex σ a) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
