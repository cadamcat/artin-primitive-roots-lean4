import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.KernelEnvelope
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadReindexing

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

private theorem slot_eq_last {x : ℝ} (j : Fin (slotCount x)) (hj : ¬ j.val < momentJ x) : j = lastSlot x := by
  have hjlt : j.val < momentJ x + 1 := by simpa only [slotCount] using j.isLt
  have hv : j.val = momentJ x := by omega
  exact Fin.ext hv

/-- The copied-slot rule and cross-edge ban are symmetric for separated valid lists. -/
theorem slotTransition_reverse {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hq : ValidPrimeLists x K a q)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (ht : IsSlotTransition p q) : IsSlotTransition q p := by
  refine ⟨fun i j hj => (ht.1 i j hj).symm, ?_⟩
  intro i i' j heq
  by_cases hj : j.val < momentJ x
  · have hcopy := ht.1 i' j hj
    have hpEq : p i (lastSlot x) = p i' j := heq.trans hcopy
    by_cases hii : i = i'
    · subst i'
      have hne : lastSlot x ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [lastSlot] at hv
        omega
      exact hp.2 i (lastSlot x) j hne hpEq
    · have hnot := Finset.disjoint_left.mp (hbands i i' hii) (hp.1 i (lastSlot x)).2
      exact hnot (by simpa only [hpEq] using (hp.1 i' j).2)
  · have hjEq := slot_eq_last j hj
    rw [hjEq] at heq
    exact ht.2 i' i (lastSlot x) heq.symm

/-- The envelope is unchanged by determinant sign and swapping the fresh labels. -/
theorem geometricEnvelope_neg_swap {K : ℕ} (F : PDFix K) (S : PDScale)
    (R B : ℝ) (aa bb : ℕ) (t : ℤ) :
    geometricEnvelope F S R B bb aa (-t) = geometricEnvelope F S R B aa bb t := by
  have hraw : (-t = (aa : ℤ) - bb) ↔ t = (bb : ℤ) - aa := by constructor <;> intro h <;> omega
  unfold geometricEnvelope
  simp only [Int.cast_neg, abs_neg]
  by_cases ht : t = (bb : ℤ) - aa
  · rw [if_pos (hraw.mpr ht), if_pos ht]
  · have hn : ¬ -t = (aa : ℤ) - bb := fun h => ht (hraw.mp h)
    rw [if_neg hn, if_neg ht]

private theorem padAdmissible_neg (d D : ℕ) (t : ℤ) : IsPadAdmissible d D t ↔ IsPadAdmissible d D (-t) := by
  constructor
  · rintro ⟨hl, hu, hd⟩
    exact ⟨hl, hu, dvd_neg.mpr hd⟩
  · rintro ⟨hl, hu, hd⟩
    exact ⟨hl, hu, dvd_neg.mp hd⟩

/-- The nonnegative physical envelope is symmetric even when psi itself is not even. -/
theorem physicalEnvelope_symm {K : ℕ} (F : PDFix K) (S : PDScale)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (R B : ℝ) (P Q : PState F S) : physicalEnvelope F S R B P Q = physicalEnvelope F S R B Q P := by
  have hp : ValidPrimeLists S.x K F.a P.labels :=
    ⟨fun i j => ⟨P.label_prime i j, P.label_in_band i j⟩, P.label_distinct⟩
  have hq : ValidPrimeLists S.x K F.a Q.labels :=
    ⟨fun i j => ⟨Q.label_prime i j, Q.label_in_band i j⟩, Q.label_distinct⟩
  have hdet : det2 Q.pos P.pos = -det2 P.pos Q.pos := by unfold det2; ring
  have hconditions : (IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos)) ↔
      (IsSlotTransition Q.labels P.labels ∧
        IsPadAdmissible S.d₀ (sharedProduct Q.labels) (det2 Q.pos P.pos)) := by
    constructor
    · rintro ⟨ht, hd⟩
      have hshared := sharedProduct_eq_of_slotTransition ht
      refine ⟨slotTransition_reverse P.labels Q.labels hp hq hbands ht, ?_⟩
      rw [← hshared, hdet]
      exact (padAdmissible_neg _ _ _).mp hd
    · rintro ⟨ht, hd⟩
      have hshared := sharedProduct_eq_of_slotTransition ht
      have hdet' : det2 P.pos Q.pos = -det2 Q.pos P.pos := by unfold det2; ring
      refine ⟨slotTransition_reverse Q.labels P.labels hq hp hbands ht, ?_⟩
      rw [← hshared, hdet']
      exact (padAdmissible_neg _ _ _).mp hd
  by_cases h : IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos)
  · have hrev := hconditions.mp h
    have hshared := sharedProduct_eq_of_slotTransition h.1
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
    obtain ⟨t, ht⟩ := h.2.2.2
    have hquot : det2 P.pos Q.pos / (sharedProduct P.labels : ℤ) = t := by
      rw [ht]
      exact Int.mul_ediv_cancel_left _ hDne
    have hquotRev : det2 Q.pos P.pos / (sharedProduct Q.labels : ℤ) = -t := by
      rw [hdet, ← hshared, ht]
      have heq : -((sharedProduct P.labels : ℤ) * t) = (sharedProduct P.labels : ℤ) * (-t) := by ring
      rw [heq]
      exact Int.mul_ediv_cancel_left _ hDne
    rw [physicalEnvelope, if_pos h, physicalEnvelope, if_pos hrev, hquot, hquotRev]
    exact congrArg (fun x : ℝ => (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) * x)
      (geometricEnvelope_neg_swap F S R B (lastProduct Q.labels) (lastProduct P.labels) t).symm
  · have hn : ¬ (IsSlotTransition Q.labels P.labels ∧
        IsPadAdmissible S.d₀ (sharedProduct Q.labels) (det2 Q.pos P.pos)) := fun hr => h (hconditions.mpr hr)
    simp [physicalEnvelope, h, hn]


end
end ArtinPrimitiveRoots.TypeII.PD
