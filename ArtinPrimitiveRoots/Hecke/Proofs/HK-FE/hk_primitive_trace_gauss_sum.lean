import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_residue_character
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_datum
import ArtinPrimitiveRoots.Hecke.Theta.RayArithmetic

set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

private lemma hkResidueRing_card (m : RayClassModulus K) :
    Fintype.card (HKResidueRing m) = modulusNorm m := by
  have h1 : Fintype.card (HKResidueRing m) = Nat.card (HKResidueRing m) := Nat.card_eq_fintype_card.symm
  have h2 : Nat.card (HKResidueRing m) = Submodule.cardQuot (modulusIdeal m) :=
    (Submodule.cardQuot_apply (modulusIdeal m)).symm
  have h3 : Submodule.cardQuot (modulusIdeal m) = Ideal.absNorm (modulusIdeal m) :=
    (Ideal.absNorm_apply (modulusIdeal m)).symm
  have h4 : Ideal.absNorm (modulusIdeal m) = modulusNorm m :=
    modulusIdeal_absNorm m
  rw [h1, h2, h3, h4]

/-- The residue cardinal is the norm, so the generic finite-ring Gauss norm is exactly sqrt q.
Uses hk_primitive_residue_character,
hk_primitive_trace_datum and OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm. -/
theorem hk_primitive_trace_gauss_sum [IsTotallyComplex K] {m : RayClassModulus K}
    {ψ : RayClassGroup m →* ℂˣ} (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) :
    ‖hkGaussSum χ T‖ = Real.sqrt (modulusNorm m : ℝ) ∧ hkGaussSum χ T ≠ 0 := by
  have hcard : (Fintype.card (HKResidueRing m) : ℝ) = (modulusNorm m : ℝ) := by
    rw [hkResidueRing_card]
  have hnorm := OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm χ.character χ.primitive T.additive T.primitive
  have hnz := OAI.SevenEighths.FiniteFourier.primitive_gaussSum_ne_zero χ.character χ.primitive T.additive T.primitive
  change ‖gaussSum χ.character T.additive‖ = Real.sqrt (modulusNorm m : ℝ) ∧ gaussSum χ.character T.additive ≠ 0
  rw [← hcard]
  exact ⟨hnorm, hnz⟩

end ArtinPrimitiveRoots.Hecke
