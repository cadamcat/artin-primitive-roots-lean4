import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Uniform fixed-base product over any finite prime set.
Guide: sol-thin-a2rp/PROOFS.md:65–66. Uses COUNT_finite and ideal norm finiteness. -/
theorem a2_bridge_SMALL_PRIME (B : ℝ) (hB : 1 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Finset (FinPlace F),
      (∏ _v ∈ T, B) ≤ C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := by
  sorry

/-- Uniform decaying-factor product; constants precede the growing prime set.
Guide: sol-thin-a2rp/PROOFS.md:65–66. Uses SMALL_PRIME and threshold splitting. -/
theorem a2_bridge_SMALL_PRIME_decay (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Finset (FinPlace F),
      (∏ v ∈ T, (1 + B * Real.rpow (idealNorm v.asIdeal) (-δ))) ≤
        C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := by
  sorry

end ArtinPrimitiveRoots.A2
