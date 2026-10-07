import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Eventual elementary scales and uniform atom/mass bounds. Guide:
`runs/lanes/sol-thin-pd5/PROOFS.md:29–91`. Uses proved pd5 Atoms and HistoryPartition;
feeds positive rows, fixed-system bounds, boundary estimates and both frozen rank declarations. -/
theorem pd5_scale_facts (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x →
      1 ≤ S.L ∧ 2 ≤ S.N ∧
      Real.rpow S.L (1 / 2 : ℝ) ≤ (S.N : ℝ) ∧
      (S.N : ℝ) < Real.rpow S.L (1 / 2 : ℝ) + 2 ∧
      (slotCount S.x : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) ∧
      (memoryCutoff S : ℝ) ≤ 2 * S.L ^ 2 ∧ slotCount S.x ≤ S.N ∧
      ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
        bandMass S.x (F.a i) ≤ 2 * Real.log 2 ∧
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2 ∧
        ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p ∧
          memoryNu S.x K F.a F.q_d i p ≤
            (4 / Real.log 2) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
