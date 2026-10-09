import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

/-- A finite memory-state collision row is bounded by its fresh-label position envelope. -/
theorem clean_finite_collision_state_row_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (T : Finset (MemPoint S.x K))
    (hT : ∀ t ∈ T, MemValid F S t)
    (hν : ∀ i : Fin K, ∀ p ∈ primeBand S.x (F.a i),
      0 ≤ memoryNu S.x K F.a F.q_d i p)
    (g : PrimeLists S.x K → (ℤ × ℤ) → ℝ) (hg : ∀ p z, 0 ≤ g p z)
    (R : ℝ)
    (hrow :
      let q := fun (a : (i : Fin K) → primeBand S.x (F.a i))
        (i : Fin K) (j : Fin (slotCount S.x)) =>
        if j.val < momentJ S.x then s.2.1 i j else (a i : ℕ)
      (∑ a : (i : Fin K) → primeBand S.x (F.a i),
        if ∃ i : Fin K, (a i : ℕ) = s.2.1 i (lastSlot S.x) then
          (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i))*
            (∑ z ∈ T.image (fun t => t.1), g (q a) z)
        else 0) ≤ R) :
    (∑ t ∈ T,
      if s.2.2 = t.2.2 ∧
        (∀ (i : Fin K) (j : Fin (slotCount S.x)),
          j.val < momentJ S.x → s.2.1 i j = t.2.1 i j) ∧
        (∃ i : Fin K, t.2.1 i (lastSlot S.x) = s.2.1 i (lastSlot S.x)) then
        (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x)))*g t.2.1 t.1
      else 0) ≤ R := by
  classical
  let X := (i : Fin K) → primeBand S.x (F.a i)
  let q : X → PrimeLists S.x K := fun a i j =>
    if j.val < momentJ S.x then s.2.1 i j else (a i : ℕ)
  let out : X → (ℤ × ℤ) → MemPoint S.x K := fun a z => (z, q a, s.2.2)
  let μ := fun t : MemPoint S.x K =>
    ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))
  let coll := fun a : X => ∃ i : Fin K, (a i : ℕ) = s.2.1 i (lastSlot S.x)
  let P := fun t : MemPoint S.x K => s.2.2 = t.2.2 ∧
    (∀ (i : Fin K) (j : Fin (slotCount S.x)),
      j.val < momentJ S.x → s.2.1 i j = t.2.1 i j) ∧
    (∃ i : Fin K, t.2.1 i (lastSlot S.x) = s.2.1 i (lastSlot S.x))
  change (∑ t ∈ T, if P t then μ t*g t.2.1 t.1 else 0) ≤ R
  let Z := T.image (fun t => t.1)
  let A := ((Finset.univ : Finset X).product Z).filter fun a =>
    out a.1 a.2 ∈ T ∧ coll a.1
  let B := T.filter P
  have hlast (a : X) (z : ℤ × ℤ) (i : Fin K) :
      (out a z).2.1 i (lastSlot S.x) = (a i : ℕ) := by
    simp only [out, q, lastSlot, lt_self_iff_false, if_false]
  have hcopy (a : X) (z : ℤ × ℤ) (i : Fin K) (j : Fin (slotCount S.x))
      (hj : j.val < momentJ S.x) : s.2.1 i j = (out a z).2.1 i j := by
    simp only [out, q, if_pos hj]
  have hinj : Function.Injective (fun a : X × (ℤ × ℤ) => out a.1 a.2) := by
    intro a b hab
    apply Prod.ext
    · funext i
      apply Subtype.ext
      have hh := congrArg (fun t : MemPoint S.x K => t.2.1 i (lastSlot S.x)) hab
      simpa only [hlast] using hh
    · exact congrArg (fun t : MemPoint S.x K => t.1) hab
  have hμ (a : X) (z : ℤ × ℤ) :
      μ (out a z) = ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i) := by
    dsimp only [μ]
    exact Finset.prod_congr rfl (fun i hi => by rw [hlast])
  have hreindex :
      (∑ a ∈ A, μ (out a.1 a.2)*g (q a.1) a.2) =
        ∑ t ∈ B, μ t*g t.2.1 t.1 := by
    apply Finset.sum_bij (fun a ha => out a.1 a.2)
    · intro a ha
      obtain ⟨_, ho, hc⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨ho, rfl, hcopy a.1 a.2, ?_⟩
      simpa only [hlast] using hc
    · intro a ha b hb heq
      exact hinj heq
    · intro t ht
      obtain ⟨htT, htP⟩ := Finset.mem_filter.mp ht
      have htvalid := hT t htT
      let a : X := fun i => ⟨t.2.1 i (lastSlot S.x), htvalid.2.1 i (lastSlot S.x)⟩
      have hlabels : q a = t.2.1 := by
        funext i j
        by_cases hj : j.val < momentJ S.x
        · simpa only [q, if_pos hj] using htP.2.1 i j hj
        · have hjlast : j = lastSlot S.x := by
            apply Fin.ext
            have hjlt := j.isLt
            dsimp only [slotCount] at hjlt
            dsimp only [lastSlot]
            omega
          subst j
          change (out a t.1).2.1 i (lastSlot S.x) = _
          rw [hlast]
      have hout : out a t.1 = t := by
        exact Prod.ext rfl (Prod.ext hlabels htP.1)
      refine ⟨(a, t.1), ?_, hout⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_image.mpr ⟨t, htT, rfl⟩⟩, ?_, ?_⟩
      · simpa only [hout] using htT
      · exact htP.2.2
    · intro a ha
      rfl
  have hweight (a : X) : 0 ≤ ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i) :=
    Finset.prod_nonneg (fun i hi => hν i (a i) (a i).property)
  calc
    _ = ∑ t ∈ B, μ t*g t.2.1 t.1 := by
      dsimp only [B]
      rw [Finset.sum_filter]
    _ = ∑ a ∈ A, μ (out a.1 a.2)*g (q a.1) a.2 := hreindex.symm
    _ ≤ ∑ a ∈ (Finset.univ : Finset X).product Z,
        if coll a.1 then
          (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a.1 i))*g (q a.1) a.2
        else 0 := by
      dsimp only [A]
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hc : coll a.1
      · by_cases ho : out a.1 a.2 ∈ T
        · simp only [ho, hc, true_and, if_true]
          rw [hμ]
        · simp only [ho, hc, false_and, if_true, if_false]
          exact mul_nonneg (hweight a.1) (hg _ _)
      · simp only [hc, and_false, if_false, le_refl]
    _ = ∑ a : X, ∑ z ∈ Z,
        if coll a then (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i))*g (q a) z else 0 :=
      Finset.sum_product' _ _ (fun a z =>
        if coll a then (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i))*g (q a) z else 0)
    _ = ∑ a : X, if coll a then
        (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (a i))*(∑ z ∈ Z, g (q a) z) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hc : coll a
      · simp only [if_pos hc, Finset.mul_sum]
      · simp only [if_neg hc, Finset.sum_const_zero]
    _ ≤ R := hrow

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
