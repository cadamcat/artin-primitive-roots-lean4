import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgeCoordinates
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GoodnessMeasurable
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridVolume
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.RootGrid

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

def normalizedArchRoot (S : PDScale) (y : ℝ × ℝ × ℝ) : ArchRoot :=
  ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩

def badEdgePredicate {K : ℕ} (F : PDFix K) (S : PDScale) (p : PrimeLists S.x K) (z : ℤ × ℤ)
    (y : ℝ × ℝ × ℝ) : Prop :=
  envBox S (normalizedArchRoot S y) (1, 0) ∧
    ¬ envGood F S (normalizedArchRoot S y) ((1, 0), p) ∧
      envBox S (normalizedArchRoot S y) z

theorem measurableSet_normalized_envBox (S : PDScale) (z : ℤ × ℤ) :
    MeasurableSet {y : ℝ × ℝ × ℝ | envBox S (normalizedArchRoot S y) z} := by
  unfold envBox normalizedArchRoot ArchRoot.tau
  simp only [Set.setOf_and]
  apply MeasurableSet.inter
  · apply measurableSet_le <;> fun_prop
  · apply MeasurableSet.inter
    · apply measurableSet_le <;> fun_prop
    · apply MeasurableSet.inter <;> apply measurableSet_le <;> fun_prop

theorem measurableSet_normalized_sourceGood {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) :
    MeasurableSet {y : ℝ × ℝ × ℝ | envGood F S (normalizedArchRoot S y) ((1, 0), p)} := by
  have heq : {y : ℝ × ℝ × ℝ | envGood F S (normalizedArchRoot S y) ((1, 0), p)} =
      {y : ℝ × ℝ × ℝ | IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2} := by
    ext y
    exact envGood_e1 F S (normalizedArchRoot S y) p
  rw [heq]
  exact (measurableSet_isGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p).preimage (by fun_prop)

theorem badEdgePredicate_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (z : ℤ × ℤ) : MeasurableSet {y | badEdgePredicate F S p z y} := by
  unfold badEdgePredicate
  change MeasurableSet ({y | envBox S (normalizedArchRoot S y) (1, 0)} ∩
    ({y | envGood F S (normalizedArchRoot S y) ((1, 0), p)}ᶜ ∩
      {y | envBox S (normalizedArchRoot S y) z}))
  exact (measurableSet_normalized_envBox S (1, 0)).inter
    ((measurableSet_normalized_sourceGood F S p).compl.inter (measurableSet_normalized_envBox S z))

theorem normalizedRootCoord_state_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (P : PState F S)
    (hC : P.completionC = (rootC P.first P.second : ℤ)) :
    normalizedArchRoot S (normalizedRootCoord S.U S.V (P.first, P.second)) = archRootOfState P := by
  change ArchRoot.mk (S.U * ((P.first : ℝ) / S.U)) (S.V * ((P.second : ℝ) / S.V))
    ((rootC P.first P.second : ℝ) / (P.first : ℝ)) =
      ArchRoot.mk (P.first : ℝ) (P.second : ℝ) ((P.completionC : ℝ) / (P.first : ℝ))
  congr 1
  · exact mul_div_cancel₀ _ hU.ne'
  · exact mul_div_cancel₀ _ hV.ne'
  · have hCR : (P.completionC : ℝ) = (rootC P.first P.second : ℝ) := by exact_mod_cast hC
    rw [hCR]


end
end ArtinPrimitiveRoots.TypeII.PD
