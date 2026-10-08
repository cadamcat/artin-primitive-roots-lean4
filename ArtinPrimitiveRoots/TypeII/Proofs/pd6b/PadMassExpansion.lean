import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadMass

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

/-- Summing the ordered pads identifies their allowed probability in the signed pair sum. -/
theorem padMass_sum_eq_pair_difference {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    (∑ d : PadChoice x K F.a,
      ∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        ∑ q ∈ coefficientQuadChoices family x,
          if PadChoiceGood d ta tb ∧ Nat.Coprime (tupleProduct ta) (tupleProduct tb) then
            (padChoiceWeight x F.a d : ℂ) * (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
              padQuadCore F x Y family beta ta tb q else 0) =
      ∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then
          (padAllowedMass x F.a ta tb : ℂ) *
            (rawPairSum F x Y family beta ta tb - comparisonPairSum F x Y family beta ta tb) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ta hta
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tb htb
  by_cases hcop : Nat.Coprime (tupleProduct ta) (tupleProduct tb)
  · rw [if_pos hcop]
    have hpoint (d : PadChoice x K F.a) :
        (∑ q ∈ coefficientQuadChoices family x,
          if PadChoiceGood d ta tb ∧ Nat.Coprime (tupleProduct ta) (tupleProduct tb) then
            (padChoiceWeight x F.a d : ℂ) * (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
              padQuadCore F x Y family beta ta tb q else 0) =
        if PadChoiceGood d ta tb then (padChoiceWeight x F.a d : ℂ) *
          (rawPairSum F x Y family beta ta tb - comparisonPairSum F x Y family beta ta tb) else 0 := by
      by_cases hg : PadChoiceGood d ta tb
      · have hc : PadChoiceGood d ta tb ∧ Nat.Coprime (tupleProduct ta) (tupleProduct tb) := ⟨hg, hcop⟩
        simp only [if_pos hg, if_pos hc]
        rw [rawPairSum_sub_comparisonPairSum_eq_core]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      · simp [hg]
    simp_rw [hpoint]
    exact padAllowedMass_complex_sum F.a ta tb _
  · simp [hcop]

end
end ArtinPrimitiveRoots.TypeII.PD
