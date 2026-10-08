import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Reuse the proved 3r coefficient-mass bound, sufficient for the tail (9 log L absorption).
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:398–455`; uses pd5_constraint_support_card_le_twice_rank,
pd5_constraint_rank_le_address_card and pd5_constraint_coeff_mass_le; feeds both rank bounds. -/
theorem pd5_rank_support_mass {K : ℕ} (A : Finset (BirthAddress K)) :
    (∀ C ∈ constraintSystems A, (C.biUnion id).card ≤ 2 * constraintRank C ∧
      constraintRank C ≤ A.card) ∧
    ∀ r : ℕ, (∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C = r),
      |(constraintCoeff C : ℝ)|) ≤ (max 1 A.card : ℝ) ^ (3 * r) := by
  classical
  refine ⟨?_, ?_⟩
  · intro C hC
    exact ⟨pd5_constraint_support_card_le_twice_rank hC,
      pd5_constraint_rank_le_address_card hC⟩
  · intro r
    exact pd5_constraint_coeff_mass_le A r

end
end ArtinPrimitiveRoots.TypeII.PD
