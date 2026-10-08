import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.KernelEnvelope
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgeCoordinates
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TargetCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

theorem edgeCoordinates_first_abs_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (P Q : PState F S) :
    |((edgeCoordinates P Q).1 : ℝ)| ≤ 16 + |((edgeCoordinates P Q).2 : ℝ)| := by
  have hreg := archRootOfState_inRegion P
  have hbox := envBox_edgeCoordinates P Q
  have htau := envBox_tau_bounds S (archRootOfState P) (edgeCoordinates P Q) hU hreg hbox
  have hTauAbs : |(archRootOfState P).tau (edgeCoordinates P Q)| ≤ 16 :=
    abs_le.mpr ⟨by linarith [htau.1], htau.2⟩
  have hRootAbs : |(archRootOfState P).r| ≤ 1 := abs_le.mpr ⟨by linarith [hreg.2.2.2.2.1], hreg.2.2.2.2.2⟩
  have heq : ((edgeCoordinates P Q).1 : ℝ) =
      (archRootOfState P).tau (edgeCoordinates P Q) -
        (archRootOfState P).r * ((edgeCoordinates P Q).2 : ℝ) := by unfold ArchRoot.tau; ring
  rw [heq]
  calc
    _ ≤ |(archRootOfState P).tau (edgeCoordinates P Q)| +
        |(archRootOfState P).r * ((edgeCoordinates P Q).2 : ℝ)| := abs_sub _ _
    _ ≤ 16 + |((edgeCoordinates P Q).2 : ℝ)| := by
      apply add_le_add hTauAbs
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hRootAbs (abs_nonneg _)

/-- The envelope has only raw-difference or short-comparison determinants. -/
theorem physicalEnvelope_positive_tube {K : ℕ} (F : PDFix K) (S : PDScale)
    (P Q : PState F S) (R B : ℝ) (hR : 0 ≤ R) (hY : 0 < S.Y)
    (h : 0 < physicalEnvelope F S R B P Q) :
    |((edgeCoordinates P Q).2 : ℝ)| ≤
      (sharedProduct P.labels : ℝ) *
        ((lastProduct P.labels : ℝ) + (lastProduct Q.labels : ℝ) + R * S.Y) := by
  have hcond : IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos) := by
    by_contra hnot
    simp only [physicalEnvelope, if_neg hnot] at h
    exact (lt_irrefl 0) h
  let t := det2 P.pos Q.pos / (sharedProduct P.labels : ℤ)
  have ht : t = (lastProduct P.labels : ℤ) - lastProduct Q.labels ∨ |(t : ℝ)| ≤ R * S.Y := by
    by_contra hnot
    push_neg at hnot
    have hzero : geometricEnvelope F S R B (lastProduct Q.labels) (lastProduct P.labels) t = 0 := by
      simp [geometricEnvelope, hnot.1, hnot.2]
    have hEnvZero : physicalEnvelope F S R B P Q = 0 := by
      rw [physicalEnvelope, if_pos hcond]
      change (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) *
        geometricEnvelope F S R B (lastProduct Q.labels) (lastProduct P.labels) t = 0
      rw [hzero, mul_zero]
    exact (lt_irrefl (0 : ℝ)) (hEnvZero ▸ h)
  have hDpos : 0 < sharedProduct P.labels := by
    unfold sharedProduct
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    split_ifs
    · exact (P.label_prime i j).pos
    · norm_num
  have hDne : (sharedProduct P.labels : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  obtain ⟨v, hv⟩ := hcond.2.2.2
  have htv : t = v := by rw [show t = det2 P.pos Q.pos / (sharedProduct P.labels : ℤ) from rfl, hv]; exact Int.mul_ediv_cancel_left _ hDne
  have hdet : (edgeCoordinates P Q).2 = (sharedProduct P.labels : ℤ) * t := by
    rw [edgeCoordinates_second_eq_det, htv]
    exact hv
  have hdetR : ((edgeCoordinates P Q).2 : ℝ) = (sharedProduct P.labels : ℝ) * (t : ℝ) := by exact_mod_cast hdet
  have htBound : |(t : ℝ)| ≤ (lastProduct P.labels : ℝ) + (lastProduct Q.labels : ℝ) + R * S.Y := by
    rcases ht with ht | ht
    · rw [ht]
      push_cast
      have hb := abs_sub (lastProduct P.labels : ℝ) (lastProduct Q.labels : ℝ)
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (lastProduct P.labels)),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (lastProduct Q.labels))] at hb
      nlinarith [mul_nonneg hR hY.le]
    · have hp0 := Nat.cast_nonneg (α := ℝ) (lastProduct P.labels)
      have hq0 := Nat.cast_nonneg (α := ℝ) (lastProduct Q.labels)
      linarith
  rw [hdetR, abs_mul, abs_of_pos (Nat.cast_pos.mpr hDpos)]
  exact mul_le_mul_of_nonneg_left htBound (Nat.cast_nonneg _)

end
end ArtinPrimitiveRoots.TypeII.PD
