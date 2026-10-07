import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Exact norm cutoffs and their finiteness. Guide: sol-thin-a2rp/PROOFS.md:42–49.
Uses bridgeNormFinset and Ideal.finite_setOfPred_absNorm_le. -/
theorem a2_bridge_COUNT_finite (S : SData F CE condη) (X : ℝ) (hX : 0 ≤ X) :
    {I : S.ExtIdeal | idealNorm I.1 ≤ X}.Finite ∧
    (∀ I : S.ExtIdeal, I ∈ bridgeNormFinset S X ↔ idealNorm I.1 ≤ X) := by
  sorry

/-- Sharp linear count, including the initial compact range.
Guide: sol-thin-a2rp/PROOFS.md:42–49. Uses NumberField.Ideal.tendsto_norm_le_div_atTop. -/
theorem a2_bridge_COUNT (S : SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ({I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard : ℝ) ≤ C * X := by
  sorry

/-- Sharp convergence at s>1, required for σ just above 1/2.
Guide: sol-thin-a2rp/PROOFS.md:42–49. Uses COUNT and dyadic geometric series. -/
theorem a2_bridge_COUNT_summable (S : SData F CE condη) (s : ℝ) (hs : 1 < s) :
    Summable (fun I : S.ExtIdeal => Real.rpow (idealNorm I.1) (-s)) := by
  sorry

/-- Harmonic mass on finite norm cutoffs.
Guide: sol-thin-a2rp/PROOFS.md:42–49. Uses COUNT, COUNT_finite and dyadic decomposition. -/
theorem a2_bridge_COUNT_harmonic (S : SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ I ∈ bridgeNormFinset S X, (idealNorm I.1)⁻¹ ≤ C * Real.log (2 * X) := by
  sorry

end ArtinPrimitiveRoots.A2
