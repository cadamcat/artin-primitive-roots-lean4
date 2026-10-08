import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Positive, bounded band masses, disjoint bands, and b-prime denominators at large x.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:402–417,482–503. Uses band_mass and
large-x separation of ValidBands; feeds all lifespan normalization and bounds. -/
theorem pd_lifecycle_parameters (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ i : Fin K, 0 < bandMass x (F.a i) ∧ bandMass x (F.a i) ≤ 2 * Real.log 2) ∧
      (∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand x (F.a i)) (primeBand x (F.a i'))) ∧
      (∀ p ∈ markedPrimes x K F.a, (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
