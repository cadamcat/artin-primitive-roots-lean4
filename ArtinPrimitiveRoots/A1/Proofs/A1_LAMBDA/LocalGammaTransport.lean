import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.CubicNormTransport
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseJacobiValue

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Choose the existing concrete sextic residue character; apply gamma_two_cube_of_norm_lift using cubic transport and base_jacobi_value. The outer minus is independent of residue degree.
Guide: sol-thin-a1/PROOFS.md:428-446. Uses: CubicNormTransport, BaseJacobiValue. -/
theorem local_cubic_gamma_transport (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (ι : E →ₐ[ℚ] F)
    (hι : ι (algebraMap OE E omega) = D.ζ12 ^ 4)
    (v : FinPlace F) (hv : v ∉ S.Sf) (c : F) (hc : S.IsGen c v.asIdeal) :
    gamma D S A 2 v.asIdeal c ^ 3 =
      -(eisensteinPrimeValue (complexEmbedding D ι) (basePlace ι v) ^
        residueDegree ι v) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
