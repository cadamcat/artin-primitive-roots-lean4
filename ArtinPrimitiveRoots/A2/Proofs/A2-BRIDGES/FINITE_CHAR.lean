import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SYMBOL

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Construct the actual residue multiplicative characters and primitive additive phase.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses SYMBOL and AddCharData.unramified.
Power zero is the unit mask because the target is MulChar. -/
theorem a2_bridge_FINITE_CHAR (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    letI := bridgeResidueField v
    letI := bridgeResidueFintype v
    (∀ j : ℤ, ∃ χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ,
      ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) j) ∧
    (∃ χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ, orderOf χ = 6 ∧
      ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 1) ∧
    (∃ ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ, ψ.IsPrimitive ∧
      ∀ t x, ψ (t * x) = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F t.out / (p : F)))) := by
  sorry

/-- Finite additive orthogonality with no finsum ambiguity.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses FINITE_CHAR; Mathlib AddChar orthogonality. -/
theorem a2_bridge_FINITE_CHAR_orthogonality (v : FinPlace F) :
    letI := bridgeResidueField v
    letI := bridgeResidueFintype v
    ∀ (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ), ψ.IsPrimitive → ∀ t,
      (∑ x : 𝓞 F ⧸ v.asIdeal, ψ (t * x)) =
        if t = 0 then (Ideal.absNorm v.asIdeal : ℂ) else 0 := by
  sorry

/-- Rewrite every finite residue finsum as the actual univ sum.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses bridgeResidueFintype. -/
theorem a2_bridge_FINITE_CHAR_finsum (v : FinPlace F) (f : (𝓞 F ⧸ v.asIdeal) → ℂ) :
    letI := bridgeResidueFintype v
    (∑ᶠ x, f x) = ∑ x : 𝓞 F ⧸ v.asIdeal, f x := by
  sorry

end ArtinPrimitiveRoots.A2
