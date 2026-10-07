import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_fourier_birth_constraints

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Attach bounded address phases at their unique births, eliminating the log exactly.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:612–656`; uses pd5 prefix uniqueness and finite
cutoff expansions; feeds low-rank norm iteration. -/
theorem pd5_phase_at_births {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : ℕ) (U : Finset (BirthAddress K)) (hU : U ⊆ birthAddresses S.x K B)
    (φ : BirthAddress K → ℕ → ℂ) (hφ : ∀ a p, ‖φ a p‖ ≤ 1)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none (pd5_birthPhaseWeight U φ) =
      pd5_phaseHistory F S ρ w B U φ := by
  sorry

/-- Pair phases regroup into the product of their per-address coefficients, including absent
performed flags. Guide `runs/lanes/sol-thin-pd5/PROOFS.md:570–611`; uses pd5b_pairAddressCoeff;
feeds pd5_phase_at_births and low-rank norm iteration. -/
theorem pd5_pairPhase_eq_birthPhase {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) (log : BirthLog K) :
    pd5b_systemPairPhase A C hC log θ =
      pd5_birthPhaseWeight (C.biUnion id)
        (fun a p => ZMod.stdAddChar (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))) log := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
