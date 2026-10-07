import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Exact finite Fourier constraint expansion, reusing pd5b's performed-address encoding.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:537–611`; uses pd5b_memHistory_constraint_fourier;
feeds phase attachment and frozen history_rank_low. -/
theorem pd5_fourier_birth_constraints {K T : ℕ} [NeZero T]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : ℕ)
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (hA : birthAddresses S.x K B ⊆ A)
    (hT : ∀ p ∈ markedPrimes S.x K F.a, p < T)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none (constraintWeight C) =
      (Fintype.card ({p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) : ℂ)⁻¹ *
        ∑ θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T,
          memHistory F S ρ w (some B) none (pd5b_systemPairPhase A C hC · θ) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
