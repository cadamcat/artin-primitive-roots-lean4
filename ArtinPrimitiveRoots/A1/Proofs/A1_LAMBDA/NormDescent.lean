import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Use N.principal_norm to map the principal subgroup into the principal subgroup, QuotientGroup.map, and quotient-map continuity, as in Kummer/Idelic.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem relative_norm_descent (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι) :
    ∃ C : ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) (IdeleClassGroup OE E),
      ∀ x : IdeleGroup (𝓞 F) F,
        C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x) := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  have hsub : IdeleGroup.principalSubgroup (𝓞 F) F ≤
      Subgroup.comap N.norm (IdeleGroup.principalSubgroup OE E) := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    change N.norm (IdeleGroup.unitEmbedding (𝓞 F) F a) ∈ IdeleGroup.principalSubgroup OE E
    rw [N.principal_norm a]
    exact ⟨Units.map (Algebra.norm E) a, rfl⟩
  let φ : IdeleClassGroup (𝓞 F) F →* IdeleClassGroup OE E :=
    QuotientGroup.map (IdeleGroup.principalSubgroup (𝓞 F) F)
      (IdeleGroup.principalSubgroup OE E) N.norm hsub
  have hcont : Continuous φ := by
    apply (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
    exact (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup OE E)).continuous.comp N.continuous_norm
  exact ⟨⟨φ, hcont⟩, fun x => rfl⟩

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
