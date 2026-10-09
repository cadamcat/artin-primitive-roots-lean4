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
  classical
  letI : (basePlace ι v).asIdeal.IsMaximal := (basePlace ι v).isMaximal
  letI : Field (OE ⧸ (basePlace ι v).asIdeal) :=
    Ideal.Quotient.field (basePlace ι v).asIdeal
  letI : Fintype (OE ⧸ (basePlace ι v).asIdeal) := Fintype.ofFinite _
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  letI := residueAlgebra ι v
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  obtain ⟨χ, hχ, hχ6⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_character_exists D v h6
  let α : MulChar (OE ⧸ (basePlace ι v).asIdeal) ℂ :=
    baseCubicChar (complexEmbedding D ι) (basePlace ι v) (base_prime_good S ι v hv).1
  have hσ : Function.Injective (integerComplex (complexEmbedding D ι)) := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    apply ι.injective
    apply D.σ0.injective
    simpa [integerComplex, complexEmbedding] using hxy
  have hαne : α ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff hσ).2
    exact OAI.ActualEisensteinCubic.cubicChar_ne_one
      (basePlace ι v).asIdeal (base_prime_good S ι v hv).1
  have hα3 : α ^ 3 = 1 := by
    simp only [α, baseCubicChar, MulChar.ringHomComp_pow,
      OAI.ActualEisensteinCubic.cubicChar_pow_three, MulChar.ringHomComp_one]
  have hnorm := cubic_residue_character_norm_transport
    D S ι hι v hv (base_prime_good S ι v hv).1 χ hχ hχ6
  have hcard : Fintype.card (OE ⧸ (basePlace ι v).asIdeal) =
      Ideal.absNorm (basePlace ι v).asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
  have hJ :
      ((Fintype.card (OE ⧸ (basePlace ι v).asIdeal) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        jacobiSum α α = -eisensteinPrimeValue (complexEmbedding D ι) (basePlace ι v) := by
    have hbaseJ := base_jacobi_value (complexEmbedding D ι) (basePlace ι v)
      (base_prime_good S ι v hv).1
    change ((Ideal.absNorm (basePlace ι v).asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        jacobiSum α α =
          -eisensteinPrimeValue (complexEmbedding D ι) (basePlace ι v) at hbaseJ
    rw [hcard]
    exact hbaseJ
  have hgamma :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.gamma_two_cube_of_norm_lift
      D S A v hv c hc χ hχ hχ6 (k := OE ⧸ (basePlace ι v).asIdeal)
      (residueAlgebra ι v) α hαne hα3 hnorm
      (eisensteinPrimeValue (complexEmbedding D ι) (basePlace ι v)) hJ
  simpa only [residueDegree] using hgamma

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
