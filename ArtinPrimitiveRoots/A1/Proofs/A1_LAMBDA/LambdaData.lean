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
Uses: LambdaPullback, LocalGammaTransport. -/
theorem lambda_data_below (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) :
    ∃ Λ : LambdaChar F, unitary Λ ∧ angularType D Λ ∧
      ∀ v : FinPlace F, v ∉ S.Sf → unramifiedAt Λ v ∧
        ∀ c : F, S.IsGen c v.asIdeal →
          gamma D S A 2 v.asIdeal c ^ 3 = -primeValue Λ v := by
  obtain ⟨ι, hι, Λ, hΛ_unit, hΛ_ang, hΛ_vals⟩ := lambda_pullback_data D S
  refine ⟨Λ, hΛ_unit, hΛ_ang, ?_⟩
  intro v hv
  have hbase := hΛ_vals v hv
  refine ⟨hbase.1, ?_⟩
  intro c hc
  have hgam := local_cubic_gamma_transport D S A ι hι v hv c hc
  rw [hgam, hbase.2]

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
