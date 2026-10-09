import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A valid state's measure separates into its copied-slot/memory factor and last-slot mass. -/
theorem clean_shared_memory_measure_factorization {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K) (hs : MemValid F S s) :
    memMeasure F S s =
      ((∏ i : Fin K, ∏ j : Fin (slotCount S.x),
          if j.val < momentJ S.x then memoryNu S.x K F.a F.q_d i (s.2.1 i j) else 1) *
        ∏ i : Fin K, (((s.2.2 i).map fun e => memoryNu S.x K F.a F.q_d i e.1).prod /
          ((s.2.2 i).length.factorial : ℝ))) *
      (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x))) := by
  let ν := fun (i : Fin K) (j : Fin (slotCount S.x)) =>
    memoryNu S.x K F.a F.q_d i (s.2.1 i j)
  have hslot (i : Fin K) (j : Fin (slotCount S.x)) :
      ν i j = (if j.val < momentJ S.x then ν i j else 1)*
        (if j = lastSlot S.x then ν i j else 1) := by
    by_cases hj : j.val < momentJ S.x
    · have hne : j ≠ lastSlot S.x := by
        intro hlast
        rw [hlast] at hj
        exact (Nat.lt_irrefl (momentJ S.x)) hj
      simp only [if_pos hj, if_neg hne, mul_one]
    · have hlast : j = lastSlot S.x := by
        apply Fin.ext
        have hlt := j.isLt
        dsimp only [slotCount] at hlt
        dsimp only [lastSlot]
        omega
      rw [if_neg hj, hlast]
      simp only [ite_true, one_mul]
  have hrow (i : Fin K) : (∏ j : Fin (slotCount S.x), ν i j) =
      (∏ j : Fin (slotCount S.x), if j.val < momentJ S.x then ν i j else 1)*
        ν i (lastSlot S.x) := by
    calc
      _ = ∏ j : Fin (slotCount S.x),
          (if j.val < momentJ S.x then ν i j else 1)*
            (if j = lastSlot S.x then ν i j else 1) :=
        Finset.prod_congr rfl (fun j hj => hslot i j)
      _ = (∏ j : Fin (slotCount S.x), if j.val < momentJ S.x then ν i j else 1)*
          (∏ j : Fin (slotCount S.x), if j = lastSlot S.x then ν i j else 1) :=
        Finset.prod_mul_distrib
      _ = _ := by simp
  have hactive : (∏ i : Fin K, ∏ j : Fin (slotCount S.x), ν i j) =
      (∏ i : Fin K, ∏ j : Fin (slotCount S.x), if j.val < momentJ S.x then ν i j else 1)*
        (∏ i : Fin K, ν i (lastSlot S.x)) := by
    calc
      _ = ∏ i : Fin K,
          (∏ j : Fin (slotCount S.x), if j.val < momentJ S.x then ν i j else 1)*
            ν i (lastSlot S.x) := Finset.prod_congr rfl (fun i hi => hrow i)
      _ = _ := Finset.prod_mul_distrib
  rw [memMeasure, if_pos hs]
  change (∏ i : Fin K, ∏ j : Fin (slotCount S.x), ν i j)*_ = _
  rw [hactive]
  dsimp only [ν]
  ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
