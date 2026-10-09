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

/-- A1-LAMBDA IMPL: For local units use N.unit_norm and hC. For uniformizers use N.uniformizer_norm, kill the unit factor with hv, and unfold primeValue. Preserve residue-degree exponent.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem relative_norm_prime_pullback (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι)
    (C : ContinuousMonoidHom (NumberField.IdeleClassGroup (𝓞 F) F) (NumberField.IdeleClassGroup OE E))
    (hC : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x))
    (χ : LambdaChar E) (v : FinPlace F)
    (hv : unramifiedAt χ (basePlace ι v)) :
    unramifiedAt (χ.comp C) v ∧
      primeValue (χ.comp C) v = primeValue χ (basePlace ι v) ^ residueDegree ι v := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
