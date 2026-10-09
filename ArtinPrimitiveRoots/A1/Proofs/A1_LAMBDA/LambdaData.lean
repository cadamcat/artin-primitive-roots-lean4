import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.LambdaPullback
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.LocalGammaTransport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Combine lambda_pullback_data and local_cubic_gamma_transport for every prime generator.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: LambdaPullback, LocalGammaTransport. -/
theorem lambda_data_below (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) :
    ∃ Λ : LambdaChar F, unitary Λ ∧ angularType D Λ ∧
      ∀ v : FinPlace F, v ∉ S.Sf → unramifiedAt Λ v ∧
        ∀ c : F, S.IsGen c v.asIdeal →
          gamma D S A 2 v.asIdeal c ^ 3 = -primeValue Λ v := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
