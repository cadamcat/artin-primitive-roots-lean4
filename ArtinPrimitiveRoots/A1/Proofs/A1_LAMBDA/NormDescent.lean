import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions
import Mathlib.Topology.Algebra.Group.Quotient

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
Uses: Definitions. -/
theorem relative_norm_descent (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι) :
    ∃ C : ContinuousMonoidHom (NumberField.IdeleClassGroup (𝓞 F) F) (NumberField.IdeleClassGroup OE E),
      ∀ x : NumberField.IdeleGroup (𝓞 F) F,
        C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x) := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  let NF := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F
  let NE := NumberField.IdeleGroup.principalSubgroup OE E
  have hsub : NF ≤ Subgroup.comap N.norm NE := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    change N.norm (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) ∈ NE
    rw [N.principal_norm a]
    exact ⟨Units.map (Algebra.norm E) a, rfl⟩
  let φ : IdeleClassGroup (𝓞 F) F →* IdeleClassGroup OE E :=
    QuotientGroup.map NF NE N.norm hsub
  have hcont : Continuous φ := by
    apply (QuotientGroup.isQuotientMap_mk NF).continuous_iff.mpr
    exact (QuotientGroup.isQuotientMap_mk NE).continuous.comp N.continuous_norm
  exact ⟨⟨φ, hcont⟩, fun x => rfl⟩

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
