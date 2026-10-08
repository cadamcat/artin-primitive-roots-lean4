import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TargetModelMeasure
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.KernelEnvelope
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgeCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical MeasureTheory
noncomputable section

/-- The coordinate envelope keeps the raw determinant line and the short comparison lines. -/
def coordinateEnvelope (D aa bb : ℕ) (Y R H : ℝ) (z : ℤ × ℤ) : ℝ :=
  (if z.2 = (D : ℤ) * ((bb : ℤ) - aa) then 1 else 0) +
    (if ∃ t : ℤ, |(t : ℝ)| ≤ R * Y ∧ z.2 = (D : ℤ) * t then H else 0)

theorem coordinateEnvelope_nonneg_le (D aa bb : ℕ) (Y R H : ℝ) (hH : 0 ≤ H)
    (z : ℤ × ℤ) : 0 ≤ coordinateEnvelope D aa bb Y R H z ∧
      coordinateEnvelope D aa bb Y R H z ≤ 1 + H := by
  unfold coordinateEnvelope
  split_ifs <;> constructor <;> linarith

/-- Pad integrality transfers the geometric envelope into determinant coordinates. -/
theorem physicalEnvelope_le_coordinateEnvelope {K : ℕ} (F : PDFix K) (S : PDScale)
    (R B : ℝ) (hV : ∀ i : Fin K, 0 < bandMass S.x (F.a i)) (hY : 0 < S.Y)
    (hB : 0 ≤ B) (hL : 0 ≤ S.L) (P Q : PState F S) :
    physicalEnvelope F S R B P Q ≤
      (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) *
        coordinateEnvelope (sharedProduct P.labels) (lastProduct Q.labels) (lastProduct P.labels)
          S.Y R (32 * B * Real.rpow S.L (3 * F.A₀) / S.Y) (edgeCoordinates P Q) := by
  have hν : 0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ :=
    Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hV i).le)
  have hPow := Real.rpow_nonneg hL (3 * F.A₀)
  have hH : 0 ≤ 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y := by positivity
  by_cases h : IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos)
  · rw [physicalEnvelope, if_pos h]
    apply mul_le_mul_of_nonneg_left _ hν
    let t : ℤ := det2 P.pos Q.pos / (sharedProduct P.labels : ℤ)
    have hdet : (edgeCoordinates P Q).2 = (sharedProduct P.labels : ℤ) * t := by
      rw [edgeCoordinates_second_eq_det]
      exact (Int.mul_ediv_cancel' h.2.2.2).symm
    have hraw : (if t = (lastProduct P.labels : ℤ) - lastProduct Q.labels then (1 : ℝ) else 0) ≤
        (if (edgeCoordinates P Q).2 = (sharedProduct P.labels : ℤ) *
          ((lastProduct P.labels : ℤ) - lastProduct Q.labels) then (1 : ℝ) else 0) := by
      by_cases ht : t = (lastProduct P.labels : ℤ) - lastProduct Q.labels
      · simp only [if_pos ht, hdet, ht, if_true, le_refl]
      · simp only [if_neg ht]
        split_ifs <;> norm_num
    have hcmp : (if |(t : ℝ)| ≤ R * S.Y then 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y else 0) ≤
        (if ∃ u : ℤ, |(u : ℝ)| ≤ R * S.Y ∧
          (edgeCoordinates P Q).2 = (sharedProduct P.labels : ℤ) * u
          then 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y else 0) := by
      by_cases ht : |(t : ℝ)| ≤ R * S.Y
      · simp only [if_pos ht, if_pos (show ∃ u : ℤ, |(u : ℝ)| ≤ R * S.Y ∧
          (edgeCoordinates P Q).2 = (sharedProduct P.labels : ℤ) * u from ⟨t, ht, hdet⟩), le_refl]
      · simp only [if_neg ht]
        split_ifs
        · exact hH
        · exact le_rfl
    exact add_le_add hraw hcmp
  · rw [physicalEnvelope, if_neg h]
    exact mul_nonneg hν (coordinateEnvelope_nonneg_le _ _ _ _ _ _ hH _).1

/-- The model weighted by the coordinate envelope has a bounded target mass. -/
theorem coordinateEnvelope_model_sum_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (hY : 0 < S.Y) (p : PrimeLists S.x K)
    (Z : Finset (ℤ × ℤ)) (D aa bb : ℕ) (R H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) :
    (∑ z ∈ Z, volume.real (normalizedRootRegion ∩ {y | badEdgePredicate F S p z y}) *
        coordinateEnvelope D aa bb S.Y R H z) ≤
      (17 + H * (17 * (2 * R * S.Y + 1))) *
        (15 * (∫ r in (0 : ℝ)..1,
          if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p r then (0 : ℝ) else 1)) := by
  let m (z : ℤ × ℤ) := volume.real (normalizedRootRegion ∩ {y | badEdgePredicate F S p z y})
  let mr (z : ℤ × ℤ) := volume.real (normalizedRootRegion ∩
    {y | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧
      z.2 = (D : ℤ) * ((bb : ℤ) - aa) ∧ envBox S (normalizedArchRoot S y) z})
  let mc (z : ℤ × ℤ) := volume.real (normalizedRootRegion ∩
    {y | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧
      (∃ t : ℤ, |(t : ℝ)| ≤ R * S.Y ∧ z.2 = (D : ℤ) * t) ∧
        envBox S (normalizedArchRoot S y) z})
  have hsub (z : ℤ × ℤ) (cond : Prop) (hc : cond) :
      m z ≤ volume.real (normalizedRootRegion ∩
        {y | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧ cond ∧
          envBox S (normalizedArchRoot S y) z}) := by
    refine measureReal_mono ?_ ?_
    · intro y hy
      refine ⟨hy.1, ?_, hc, hy.2.2.2⟩
      have hgood := hy.2.2.1
      rw [envGood_e1] at hgood
      exact hgood
    · exact (measure_mono Set.inter_subset_left).trans_lt normalizedRootRegion_compact.measure_lt_top |>.ne_top
  have hpoint (z : ℤ × ℤ) : m z * coordinateEnvelope D aa bb S.Y R H z ≤ mr z + H * mc z := by
    unfold coordinateEnvelope
    by_cases hr : z.2 = (D : ℤ) * ((bb : ℤ) - aa)
    · have hm := hsub z _ hr
      by_cases hc : ∃ t : ℤ, |(t : ℝ)| ≤ R * S.Y ∧ z.2 = (D : ℤ) * t
      · have hm' := hsub z _ hc
        simp only [if_pos hr, if_pos hc]
        dsimp [mr, mc] at *
        have hh := mul_le_mul_of_nonneg_left hm' hH
        nlinarith
      · simp only [if_pos hr, if_neg hc, add_zero, mul_one]
        exact hm.trans (le_add_of_nonneg_right (mul_nonneg hH (measureReal_nonneg)))
    · by_cases hc : ∃ t : ℤ, |(t : ℝ)| ≤ R * S.Y ∧ z.2 = (D : ℤ) * t
      · have hm' := hsub z _ hc
        simp only [if_neg hr, if_pos hc, zero_add]
        have hh := mul_le_mul_of_nonneg_left hm' hH
        dsimp [mc] at *
        have hr0 : 0 ≤ mr z := measureReal_nonneg
        nlinarith
      · simp only [if_neg hr, if_neg hc, add_zero, mul_zero]
        exact add_nonneg (measureReal_nonneg) (mul_nonneg hH (measureReal_nonneg))
  have hr := rawTargetModel_bad_volume_upper F S hU hV p Z ((D : ℤ) * ((bb : ℤ) - aa))
  have hc := comparisonTargetModel_bad_volume_upper F S hU hV p Z (D : ℤ) R hY hR
  calc
    _ ≤ ∑ z ∈ Z, (mr z + H * mc z) := Finset.sum_le_sum (fun z hz => hpoint z)
    _ = (∑ z ∈ Z, mr z) + H * (∑ z ∈ Z, mc z) := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hc hH
      dsimp [mr, mc] at *
      nlinarith

end
end ArtinPrimitiveRoots.TypeII.PD
