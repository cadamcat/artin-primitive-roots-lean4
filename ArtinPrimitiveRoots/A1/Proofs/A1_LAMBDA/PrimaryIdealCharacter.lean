import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def angularZeroHom : ℂ →*₀ ℂ where
  toFun z := z / ‖z‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    by_cases hz : z = 0
    · simp [hz]
    by_cases hw : w = 0
    · simp [hw]
    rw [Complex.norm_mul]
    push_cast
    field_simp [norm_ne_zero_iff.mpr hz, norm_ne_zero_iff.mpr hw]

/-- A1-LAMBDA IMPL: Compose OAI.CompletedGauss.primaryGeneratorHom with the zero-preserving normalized angular map; norm_mul also handles zero.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem primary_ideal_character_exists (σ : E →+* ℂ) :
    ∃ φ : Ideal OE →*₀ ℂ, ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖ := by
  refine ⟨angularZeroHom.comp ((integerComplex σ).toMonoidWithZeroHom.comp
    OAI.CompletedGauss.primaryGeneratorHom), ?_⟩
  intro I
  rfl

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
