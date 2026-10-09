import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BasePrimeGood
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.NormTransport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
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
  obtain ⟨readRoot, hroot, hread⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_cubic_readout_exists D v h6 χ hχ
  let α : MulChar (OE ⧸ (basePlace ι v).asIdeal) ℂ :=
    baseCubicChar (complexEmbedding D ι) (basePlace ι v) hb
  have hα : ∀ u : (OE ⧸ (basePlace ι v).asIdeal)ˣ,
      α (u : OE ⧸ (basePlace ι v).asIdeal) =
        readRoot (residueMap ι v ((u : OE ⧸ (basePlace ι v).asIdeal) ^
          ((Nat.card (OE ⧸ (basePlace ι v).asIdeal) - 1) / 3))) := by
    intro u
    let γ := OAI.ActualEisensteinCubic.cubicChar (basePlace ι v).asIdeal hb
    let y : (OE)ˣ := γ.toUnitHom u
    let z : (𝓞 F)ˣ := Units.map (integerEmbedding ι).toMonoidHom y
    have hy3 : y ^ 3 = 1 := by
      apply Units.ext
      have hpow := congrArg
        (fun φ : MulChar (OE ⧸ (basePlace ι v).asIdeal) OE =>
          φ (u : OE ⧸ (basePlace ι v).asIdeal))
        (OAI.ActualEisensteinCubic.cubicChar_pow_three
          (basePlace ι v).asIdeal hb)
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, y,
        MulChar.coe_toUnitHom, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hpow
    have hy6 : y ^ 6 = 1 := by
      rw [show 6 = 3 * 2 by norm_num, pow_mul, hy3]
      simp
    have hz6 : z ^ 6 = 1 := by
      change (Units.map (integerEmbedding ι).toMonoidHom y) ^ 6 = 1
      rw [← map_pow, hy6]
      simp
    have hz6val : ((z : (𝓞 F)ˣ) : 𝓞 F) ^ 6 = 1 := by
      exact congrArg (fun a : (𝓞 F)ˣ => (a : 𝓞 F)) hz6
    let ζ : rootsOfUnity 6 (𝓞 F) :=
      rootsOfUnity.mkOfPowEq (z : 𝓞 F) hz6val
    have hζcoe : ((ζ : (𝓞 F)ˣ) : 𝓞 F) = integerEmbedding ι (γ (u : _)) := by
      rw [rootsOfUnity.coe_mkOfPowEq hz6val]
      simp [z, y, γ, integerEmbedding]
    have hred :
        residueMap ι v (Ideal.Quotient.mk (basePlace ι v).asIdeal (γ (u : _))) =
          residueMap ι v ((u : OE ⧸ (basePlace ι v).asIdeal) ^
            ((Nat.card (OE ⧸ (basePlace ι v).asIdeal) - 1) / 3)) := by
      exact congrArg (residueMap ι v)
        (OAI.ActualEisensteinCubic.cubicChar_reduce
          (basePlace ι v).asIdeal hb (u : OE ⧸ (basePlace ι v).asIdeal))
    have hζred :
        Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
          residueMap ι v
            (Ideal.Quotient.mk (basePlace ι v).asIdeal (γ (u : _))) := by
      rw [hζcoe]
      simp [residueMap, Ideal.quotientMap_mk]
    change α (u : OE ⧸ (basePlace ι v).asIdeal) = _
    calc
      α (u : OE ⧸ (basePlace ι v).asIdeal) =
          D.σ0 (algebraMap (𝓞 F) F (integerEmbedding ι (γ (u : _)))) := by
            simp [α, baseCubicChar, integerComplex, complexEmbedding, integerEmbedding, γ]
      _ = readRoot (Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F)) :=
        (hroot ζ).symm
      _ = readRoot (residueMap ι v
          (Ideal.Quotient.mk (basePlace ι v).asIdeal (γ (u : _)))) := by
            rw [hζred]
      _ = readRoot (residueMap ι v
          ((u : OE ⧸ (basePlace ι v).asIdeal) ^
            ((Nat.card (OE ⧸ (basePlace ι v).asIdeal) - 1) / 3))) := by
            rw [hred]
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hβ : ∀ u : (𝓞 F ⧸ v.asIdeal)ˣ,
      (χ ^ 2) (u : 𝓞 F ⧸ v.asIdeal) =
        readRoot ((u : 𝓞 F ⧸ v.asIdeal) ^
          ((Nat.card (𝓞 F ⧸ v.asIdeal) - 1) / 3)) := by
    intro u
    simpa only [hcard] using hread u
  exact ArtinPrimitiveRoots.Proofs.a1_gauss_sol.cubic_character_norm_transport
    (ArtinPrimitiveRoots.Proofs.a1_lambda_sol.base_prime_good S ι v hv).2
    α (χ ^ 2) readRoot hα hβ

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
