import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: If lambda maps into v then the associated element 3 does too, contradicting S.over6. Apply OAI.card_sub_one_div_three to the base prime.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem base_prime_good (S : SData F CE condη) (ι : E →ₐ[ℚ] F)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    lambda ∉ (basePlace ι v).asIdeal ∧
      3 ∣ Nat.card (OE ⧸ (basePlace ι v).asIdeal) - 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
