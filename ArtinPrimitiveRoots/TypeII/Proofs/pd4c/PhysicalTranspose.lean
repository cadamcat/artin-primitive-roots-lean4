import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Omissions
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.GroupTransfer

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Alternating physical steps exchange the two geometric endpoint roles. -/
theorem pd4c_step_parity_flip (j : ℕ) :
    decide ((j + 1) % 2 = 0) = !(decide (j % 2 = 0)) := by
  by_cases hj : j % 2 = 0
  · have hn : (j + 1) % 2 ≠ 0 := by omega
    simp [hj, hn]
  · have hn : (j + 1) % 2 = 0 := by omega
    simp [hj, hn]

theorem pd4c_edgeMultiplier_transpose {K : ℕ} (F : PDFix K) (S : PDScale)
    (forward raw : Bool) (p q : PrimeLists S.x K) (z z' : ℤ × ℤ)
    (hslot : IsSlotTransition p q) :
    edgeMultiplier F S (!forward) raw q p z' z =
      star (edgeMultiplier F S forward raw p q z z') := by
  have hd := pd4c_sharedProduct_eq_of_slotTransition p q hslot
  cases forward <;> cases raw <;> simp [edgeMultiplier, hd]

theorem pd4c_edgeMultiplier_step_norm_transpose {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (raw : Bool) (p q : PrimeLists S.x K) (z z' : ℤ × ℤ)
    (hslot : IsSlotTransition p q) :
    ‖edgeMultiplier F S (decide ((j + 1) % 2 = 0)) raw q p z' z‖ =
      ‖edgeMultiplier F S (decide (j % 2 = 0)) raw p q z z'‖ := by
  rw [pd4c_step_parity_flip, pd4c_edgeMultiplier_transpose F S _ raw p q z z' hslot, norm_star]

/-- A product over the growing slots splits into shared slots and the one last slot. -/
theorem pd4c_slots_product {x : ℝ} {α : Type*} [CommMonoid α]
    (f : Fin (slotCount x) → α) :
    (∏ j : Fin (slotCount x), if j.val < momentJ x then f j else 1) * f (lastSlot x) =
      ∏ j : Fin (slotCount x), f j := by
  have hset : (Finset.univ : Finset (Fin (slotCount x))).filter (fun j => j.val < momentJ x) =
      Finset.univ.erase (lastSlot x) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    have hjlt := j.isLt
    dsimp [slotCount] at hjlt
    constructor
    · intro hj heq
      have hval := congrArg Fin.val heq
      dsimp [lastSlot] at hval
      omega
    · intro hn
      by_contra hnot
      have heq : lastSlot x = j := by apply Fin.ext; dsimp [lastSlot]; omega
      exact hn heq.symm
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  rw [hset]
  exact Finset.prod_erase_mul Finset.univ f (Finset.mem_univ (lastSlot x))

def pd4c_activeDensity {K : ℕ} (F : PDFix K) (S : PDScale) (p : PrimeLists S.x K) : ℝ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (p i j)

def pd4c_sharedDensity {K : ℕ} (F : PDFix K) (S : PDScale) (p : PrimeLists S.x K) : ℝ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount S.x),
    if j.val < momentJ S.x then memoryNu S.x K F.a F.q_d i (p i j) else 1

theorem pd4c_activeDensity_split {K : ℕ} (F : PDFix K) (S : PDScale) (p : PrimeLists S.x K) :
    pd4c_activeDensity F S p = pd4c_sharedDensity F S p *
      ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (p i (lastSlot S.x)) := by
  unfold pd4c_activeDensity pd4c_sharedDensity
  rw [← Finset.prod_mul_distrib]
  symm
  exact Finset.prod_congr rfl (fun i hi => pd4c_slots_product _)

theorem pd4c_sharedDensity_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (hslot : IsSlotTransition p q) :
    pd4c_sharedDensity F S q = pd4c_sharedDensity F S p := by
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hs : j.val < momentJ S.x
  · simp only [if_pos hs, hslot.1 i j hs]
  · simp only [if_neg hs]

theorem pd4c_memMeasure_factor {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) :
    memMeasure F S s = pd4c_activeDensity F S s.2.1 *
      ∏ i : Fin K, pd4c_listDensity (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1) (s.2.2 i) := by
  rw [memMeasure, if_pos hs]
  rfl

end

end ArtinPrimitiveRoots.TypeII.PD
