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

/-- A1-LAMBDA IMPL: Unfold angularType, infiniteComponent and composition; use hC and N.angular_norm. The m=±1 exponents use the frozen completion equivalence.
Uses: Definitions. -/
theorem relative_norm_angular_pullback (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι)
    (C : ContinuousMonoidHom (NumberField.IdeleClassGroup (𝓞 F) F) (NumberField.IdeleClassGroup OE E))
    (hC : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x))
    (χ : LambdaChar E) (hχ : simpleAngularType χ) : angularType D (χ.comp C) := by
  intro w
  obtain ⟨m, hm, hz⟩ := N.angular_norm χ hχ w
  refine ⟨m, hm, fun z => ?_⟩
  have := hz z
  have hmk : IdeleClassGroup.ofCompletion (𝓞 F) F w
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) =
    QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 F) F w
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z)) := rfl
  change ((χ (C (IdeleClassGroup.ofCompletion (𝓞 F) F w
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z))) : ℂˣ) : ℂ) = _
  rw [hmk, hC]
  exact this

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
