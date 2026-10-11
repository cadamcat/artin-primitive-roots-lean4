import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AngularNormTransport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA LEAD: Build canonical finite completion norm maps and their fiberwise products, complex coordinate norms, continuity and principal_norm. Local norm valuations give residueDegree on uniformizers and unit_norm; restriction of complex embeddings gives angular_norm. Reuse existing lower-level completion and idelic APIs; unavailable TauCeti modules must not be imported.
Uses: Definitions. -/
theorem relative_norm_data_exists (D : FieldData F) (ι : E →ₐ[ℚ] F) :
    Nonempty (RelativeNormData D ι) := by
  exact ⟨{
    norm := relativeIdeleNorm ι
    continuous_norm := relativeIdeleNorm_continuous ι
    principal_norm := relativeIdeleNorm_principal ι
    unit_norm := relativeIdeleNorm_unit_norm ι
    uniformizer_norm := relativeIdeleNorm_uniformizer_norm ι
    angular_norm := relativeIdeleNorm_angular_norm D ι
  }⟩

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
