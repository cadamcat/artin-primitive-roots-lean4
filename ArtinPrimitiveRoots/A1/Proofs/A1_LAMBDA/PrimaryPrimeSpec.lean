import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Use normalizedFactors_irreducible to reduce to primaryPrime, then OAI primaryPrime_ne_zero and primaryGenerator_spec.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem primary_prime_spec (v : FinPlace E) (hv : lambda ∉ v.asIdeal) :
    primary v.asIdeal ≠ 0 ∧ v.asIdeal = Ideal.span {primary v.asIdeal} ∧
      lambda ^ 2 ∣ primary v.asIdeal - 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
