import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AlignedEmbedding
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.RelativeNormConstruction
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.NormDescent
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimePullback
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AngularPullback

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: assemble the angular norm pullback and its exterior prime values.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: AlignedEmbedding, BaseCharacter,
RelativeNormConstruction, NormDescent, PrimePullback, AngularPullback. -/
theorem lambda_pullback_data (D : FieldData F) (S : SData F CE condη) :
    ∃ ι : E →ₐ[ℚ] F, ι (algebraMap OE E omega) = D.ζ12 ^ 4 ∧
      ∃ Λ : LambdaChar F, unitary Λ ∧ angularType D Λ ∧
        ∀ v : FinPlace F, v ∉ S.Sf → unramifiedAt Λ v ∧
          primeValue Λ v = eisensteinPrimeValue (complexEmbedding D ι)
            (basePlace ι v) ^ residueDegree ι v := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
