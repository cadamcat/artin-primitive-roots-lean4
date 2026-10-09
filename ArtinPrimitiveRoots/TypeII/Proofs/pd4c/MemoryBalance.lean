import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LastSlotMeasure

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Copied slots and unchanged memory give the exact balance of endpoint and fresh masses. -/
theorem clean_common_memory_measure_balance {K : ℕ} (F : PDFix K) (S : PDScale)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t)
    (hmem : s.2.2 = t.2.2)
    (hcopy : ∀ (i : Fin K) (j : Fin (slotCount S.x)),
      j.val < momentJ S.x → s.2.1 i j = t.2.1 i j) :
    memMeasure F S s*(∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))) =
      memMeasure F S t*(∏ i : Fin K, memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x))) := by
  have hνcopy :
      (∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        if j.val < momentJ S.x then memoryNu S.x K F.a F.q_d i (s.2.1 i j) else 1) =
      (∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        if j.val < momentJ S.x then memoryNu S.x K F.a F.q_d i (t.2.1 i j) else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hjval : j.val < momentJ S.x
    · rw [if_pos hjval, if_pos hjval, hcopy i j hjval]
    · simp only [if_neg hjval]
  rw [clean_shared_memory_measure_factorization F S s hs,
    clean_shared_memory_measure_factorization F S t ht, hνcopy, hmem]
  ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
