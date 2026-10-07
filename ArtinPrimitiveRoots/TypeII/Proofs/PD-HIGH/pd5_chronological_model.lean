import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Finite invariant cutoff state set and exact finite kernel expansions of local twists.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:92–150,771–805`. Uses pd5_envBox_finite_of_valid
and finite cutoff expansions; feeds fixed-system estimates and low-rank norm iteration. -/
theorem pd5_chronological_model (δ c₁ c₂ : ℝ) (K : ℕ) (F : PDFix K)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S)
    (B : ℕ) :
    ∃ T : Finset (MemPoint S.x K),
      (∀ s, s ∈ T ↔ pd5_stateRegion F S w B s) ∧
      (∀ s ∈ T, ∀ σ : MemoryPermutation s, memoryPermute s σ ∈ T) ∧
      ∀ W : BirthLog K → ℂ, ∀ f : MemPoint S.x K → ℂ, ∀ s ∈ T,
        (∀ j : ℕ, j ≤ S.N →
          pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
            ∑ t ∈ T, memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
              (pd5_plainTrunc B g)) s t * f t) ∧
        (∀ j : ℕ, j < S.N →
          pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
            ∑ t ∈ T, memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
              (pd5_plainTrunc B g)) s t * f t) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
