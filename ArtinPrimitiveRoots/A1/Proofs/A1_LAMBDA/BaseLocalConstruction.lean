import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseLocalCorrection

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA LEAD: Construct the conductor-(3) finite local factors from primary unit normalization; use the inverse angular factor at infinity. Prove the principal product formula before idelic descent.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem base_local_data_exists (σ : E →+* ℂ)
    (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, ((a z : ℂˣ) : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) :
    Nonempty (BaseLocalData σ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
