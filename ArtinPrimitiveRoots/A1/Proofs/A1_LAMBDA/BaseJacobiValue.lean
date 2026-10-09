import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryPrimeNorm

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Map cubicJacobi_eq_neg_primary_generator_of_principal by jacobiSum_ringHomComp. Rewrite the real normalization using the positive generator norm and norm-square formula.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: PrimaryPrimeNorm. -/
theorem base_jacobi_value (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    normalizedJacobi v (baseCubicChar σ v hv) = -eisensteinPrimeValue σ v := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
