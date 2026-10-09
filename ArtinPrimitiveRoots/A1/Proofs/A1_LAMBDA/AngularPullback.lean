import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Unfold angularType, infiniteComponent and composition; use hC and N.angular_norm. The m=±1 exponents use the frozen completion equivalence.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem relative_norm_angular_pullback (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι)
    (C : ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) (IdeleClassGroup OE E))
    (hC : ∀ x : IdeleGroup (𝓞 F) F,
      C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x))
    (χ : LambdaChar E) (hχ : simpleAngularType χ) : angularType D (χ.comp C) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
