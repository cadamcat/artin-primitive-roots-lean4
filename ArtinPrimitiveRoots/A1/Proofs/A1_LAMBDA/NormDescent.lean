import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Use N.principal_norm to map the principal subgroup into the principal subgroup, QuotientGroup.map, and quotient-map continuity, as in Kummer/Idelic.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem relative_norm_descent (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι) :
    ∃ C : ContinuousMonoidHom (NumberField.IdeleClassGroup (𝓞 F) F) (NumberField.IdeleClassGroup OE E),
      ∀ x : NumberField.IdeleGroup (𝓞 F) F,
        C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
