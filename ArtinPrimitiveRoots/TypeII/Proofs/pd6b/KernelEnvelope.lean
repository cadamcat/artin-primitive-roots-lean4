import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.MajorKernelBound

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def geometricEnvelope {K : ℕ} (F : PDFix K) (S : PDScale) (R B : ℝ)
    (aa bb : ℕ) (t : ℤ) : ℝ :=
  (if t = (bb : ℤ) - aa then 1 else 0) +
    (if |(t : ℝ)| ≤ R * S.Y then 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y else 0)

theorem dampingHalf_nonneg_le_one {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (n : ℕ) : 0 ≤ dampingHalf F S n ∧ dampingHalf F S n ≤ 1 := by
  unfold dampingHalf
  have he : 0 ≤ ((markedOmega S.x K F.a n - K * slotCount S.x : ℕ) : ℝ) / 2 := by positivity
  exact ⟨Real.rpow_nonneg hF.2.1.le _, Real.rpow_le_one hF.2.1.le hF.2.2.1.le he⟩

theorem geometricMultiplier_norm_le_envelope {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (hY : 0 < S.Y) (hL : 1 ≤ Real.log S.x) (D aa bb : ℕ)
    (hD : 0 < D) (hdyad : (S.d₀ : ℝ) ≤ (D : ℝ)) (R B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ y : ℝ, |F.psi y| ≤ B) (hSupport : ∀ y : ℝ, F.psi y ≠ 0 → |y| ≤ R)
    (t : ℤ) : ‖geometricMultiplier F S D aa bb t‖ ≤ geometricEnvelope F S R B aa bb t := by
  have hRaw : ‖rawMultiplier F S D aa bb t‖ ≤ (if t = (bb : ℤ) - aa then (1 : ℝ) else 0) := by
    by_cases ht : t = (bb : ℤ) - aa
    · simpa only [if_pos ht] using rawMultiplier_norm_le_one F S hF hY D aa bb hD hdyad t
    · simp [rawMultiplier, ht]
  have hComp : ‖comparisonMultiplier F S D aa bb t‖ ≤
      (if |(t : ℝ)| ≤ R * S.Y then 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y else 0) := by
    by_cases ht : |(t : ℝ)| ≤ R * S.Y
    · rw [if_pos ht]
      exact (comparisonMultiplier_norm_le_kernel F S hF D aa bb hD hdyad t).trans
        (majorKernel_norm_bound S.x S.Y F.A₀ (t : ℝ) aa bb F.psi B hB hBound hY hL hF.2.2.2.1)
    · have hzero : F.psi ((t : ℝ) / S.Y) = 0 := by
        by_contra hnot
        have hs := hSupport ((t : ℝ) / S.Y) hnot
        rw [abs_div, abs_of_pos hY] at hs
        exact ht ((div_le_iff₀ hY).mp hs)
      simp [comparisonMultiplier, majorKernel, hzero, ht]
  exact (norm_sub_le _ _).trans (add_le_add hRaw hComp)

def physicalEnvelope {K : ℕ} (F : PDFix K) (S : PDScale) (R B : ℝ) (P Q : PState F S) : ℝ :=
  if IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos) then
    (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) *
      geometricEnvelope F S R B (lastProduct Q.labels) (lastProduct P.labels)
        (det2 P.pos Q.pos / (sharedProduct P.labels : ℤ))
  else 0

/-- Discarding damping gives a nonnegative label/vector envelope for physical edge norms. -/
theorem physRowKernel_norm_le_envelope {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hV : ∀ i : Fin K, 0 < bandMass S.x (F.a i)) (hY : 0 < S.Y) (hL : 1 ≤ Real.log S.x)
    (R B : ℝ) (hB : 0 ≤ B) (hBound : ∀ y : ℝ, |F.psi y| ≤ B)
    (hSupport : ∀ y : ℝ, F.psi y ≠ 0 → |y| ≤ R) (P Q : PState F S) :
    ‖physRowKernel F S P Q‖ ≤ physicalEnvelope F S R B P Q := by
  have hν : 0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ :=
    Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hV i).le)
  have hSlot : ‖slotKernel F S P.labels Q.labels (det2 P.pos Q.pos)‖ ≤ physicalEnvelope F S R B P Q := by
    by_cases h : IsSlotTransition P.labels Q.labels ∧
        IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos)
    · have hD : 0 < sharedProduct P.labels := by
        unfold sharedProduct
        apply Finset.prod_pos
        intro i hi
        apply Finset.prod_pos
        intro j hj
        split_ifs
        · exact (P.label_prime i j).pos
        · norm_num
      rw [physicalEnvelope, if_pos h]
      rw [slotKernel, if_pos h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
      exact mul_le_mul_of_nonneg_left
        (geometricMultiplier_norm_le_envelope F S hF hY hL (sharedProduct P.labels)
          (lastProduct Q.labels) (lastProduct P.labels) hD h.2.1 R B hB hBound hSupport
          (det2 P.pos Q.pos / (sharedProduct P.labels : ℤ))) hν
    · simp [slotKernel, physicalEnvelope, h]
  have hP := dampingHalf_nonneg_le_one F S hF P.first
  have hQ := dampingHalf_nonneg_le_one F S hF Q.first
  have hDamp : ‖((dampingHalf F S P.first * dampingHalf F S Q.first : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hP.1 hQ.1)]
    simpa only [one_mul] using mul_le_mul hP.2 hQ.2 hQ.1 (by norm_num : (0 : ℝ) ≤ 1)
  rw [physRowKernel, norm_mul]
  calc
    _ ≤ physicalEnvelope F S R B P Q * 1 :=
      mul_le_mul hSlot hDamp (norm_nonneg _) ((norm_nonneg _).trans hSlot)
    _ = _ := mul_one _

end
end ArtinPrimitiveRoots.TypeII.PD
