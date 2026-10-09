import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BasePrimeGood
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.NormTransport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Use existing cubic_character_norm_transport and residue_cubic_readout_exists. Align OAI cubicChar_reduce along residueMap with the common D.σ0 root readout; hι aligns omega.
Guide: sol-thin-a1/PROOFS.md:428-446. Uses: BasePrimeGood, NormTransport. -/
theorem cubic_residue_character_norm_transport (D : FieldData F)
    (S : SData F CE condη) (ι : E →ₐ[ℚ] F)
    (hι : ι (algebraMap OE E omega) = D.ζ12 ^ 4)
    (v : FinPlace F) (hv : v ∉ S.Sf)
    (hb : lambda ∉ (basePlace ι v).asIdeal)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχ : ∀ x : 𝓞 F, χ (Ideal.Quotient.mk v.asIdeal x) =
      chi D v (algebraMap (𝓞 F) F x)) (hχ6 : χ ^ 6 = 1) :
    letI : (basePlace ι v).asIdeal.IsMaximal := (basePlace ι v).isMaximal
    letI : Field (OE ⧸ (basePlace ι v).asIdeal) :=
      Ideal.Quotient.field (basePlace ι v).asIdeal
    letI : Fintype (OE ⧸ (basePlace ι v).asIdeal) := Fintype.ofFinite _
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    letI := residueAlgebra ι v
    χ ^ 2 = ArtinPrimitiveRoots.Arith.normLift
      (k := OE ⧸ (basePlace ι v).asIdeal) (K := 𝓞 F ⧸ v.asIdeal)
      (baseCubicChar (complexEmbedding D ι) (basePlace ι v) hb) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
