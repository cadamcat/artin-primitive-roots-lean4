import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryPrimeSpec
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.EmbeddingConjugation

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Map OAI.primary_generator_mul_conj_eq_card through σ, use embedding conjugation, and identify quotient cardinal with absNorm.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: PrimaryPrimeSpec, EmbeddingConjugation. -/
theorem primary_prime_norm_sq (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    ‖integerComplex σ (primary v.asIdeal)‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
