import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Bundle z/abs(z) on complex units; norm multiplicativity and continuous division give the homomorphism.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem angular_character_exists :
    ∃ a : ContinuousMonoidHom ℂˣ ℂˣ, ∀ z : ℂˣ,
      ((a z : ℂˣ) : ℂ) = (z : ℂ) / ‖(z : ℂ)‖ := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
