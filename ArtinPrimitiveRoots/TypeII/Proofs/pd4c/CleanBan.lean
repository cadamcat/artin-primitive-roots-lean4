import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Valid copied lists in disjoint bands leave only same-group last-label collisions. -/
theorem clean_slot_transition_iff_last_neq {K : ℕ} (F : PDFix K) (S : PDScale)
    (hbands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (p q : PrimeLists S.x K)
    (hp : ValidPrimeLists S.x K F.a p) (hq : ValidPrimeLists S.x K F.a q)
    (hshared : ∀ (i : Fin K) (j : Fin (slotCount S.x)),
      j.val < momentJ S.x → q i j = p i j) :
    IsSlotTransition p q ↔ ∀ i : Fin K, q i (lastSlot S.x) ≠ p i (lastSlot S.x) := by
  constructor
  · intro h i
    exact h.2 i i (lastSlot S.x)
  · intro h
    refine ⟨hshared, ?_⟩
    intro i i' jj heq
    by_cases hii : i = i'
    · subst i'
      by_cases hjj : jj.val < momentJ S.x
      · have hjne : lastSlot S.x ≠ jj := by
          intro hh
          have hhval := congrArg Fin.val hh
          dsimp only [lastSlot] at hhval
          omega
        apply hq.2 i (lastSlot S.x) jj hjne
        rw [hshared i jj hjj]
        exact heq
      · have hjlast : jj = lastSlot S.x := by
          apply Fin.ext
          have hjlt := jj.isLt
          dsimp only [slotCount] at hjlt
          dsimp only [lastSlot]
          omega
        subst jj
        exact h i heq
    · apply (Finset.disjoint_left.mp (hbands i i' hii)) ((hq.1 i (lastSlot S.x)).2)
      rw [heq]
      exact (hp.1 i' jj).2

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
