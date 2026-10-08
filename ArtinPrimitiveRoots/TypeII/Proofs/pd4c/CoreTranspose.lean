import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CorePieceKernel
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MemoryAlphabet

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

def pd4c_bandFactor {K : ℕ} (F : PDFix K) (S : PDScale) (I : Finset (Fin K)) : ℝ :=
  ∏ i : Fin K, if i ∈ I then bandMass S.x (F.a i) else 1

theorem pd4c_coreGroupKernel_star {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (s t : MemPoint S.x K) (St Pr : Finset (Fin K)) (i : Fin K) :
    star (pd4c_coreGroupKernel F S ρ s t St Pr i) = pd4c_coreGroupKernel F S ρ s t St Pr i :=
  pd4c_groupProjectedKernel_star _ _ _ _ _ _ _ _ _ _ _

/-- Factorial group measure and the unshared active-prime measure transpose together. -/
theorem pd4c_coreGroup_measure_transpose {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t)
    (St Pr : Finset (Fin K)) (i : Fin K) (hV : bandMass S.x (F.a i) ≠ 0) :
    (memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x)) : ℂ) *
      (if i ∈ Pr then (bandMass S.x (F.a i) : ℂ) else 1) *
      ((pd4c_listDensity (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1) (s.2.2 i) : ℂ) *
        pd4c_coreGroupKernel F S ρ s t St Pr i) =
    (memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x)) : ℂ) *
      (if i ∈ St then (bandMass S.x (F.a i) : ℂ) else 1) *
      ((pd4c_listDensity (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1) (t.2.2 i) : ℂ) *
        pd4c_coreGroupKernel F S ρ t s Pr St i) := by
  let T := pd4c_particleBand S.x (F.a i)
  let ν := fun e : Particle => memoryNu S.x K F.a F.q_d i e.1
  let p : T := ⟨anchorAt (s.2.1 i (lastSlot S.x)) s.1,
    (pd4c_mem_particleBand _ _ _).mpr ⟨hs.2.1 i _, Nat.le_of_lt_succ (projLine _ _).isLt⟩⟩
  let q : T := ⟨anchorAt (t.2.1 i (lastSlot S.x)) t.1,
    (pd4c_mem_particleBand _ _ _).mpr ⟨ht.2.1 i _, Nat.le_of_lt_succ (projLine _ _).isLt⟩⟩
  have hl (e : Particle) (he : e ∈ s.2.2 i) : e ∈ T :=
    (pd4c_mem_particleBand _ _ _).mpr (hs.2.2 i e he)
  have hm (e : Particle) (he : e ∈ t.2.2 i) : e ∈ T :=
    (pd4c_mem_particleBand _ _ _).mpr (ht.2.2 i e he)
  have h := pd4c_groupProjectedKernel_transpose T (max (s.2.2 i).length (t.2.2 i).length)
    ν (bandMass S.x (F.a i)) hV p q (decide (i ∈ St)) (decide (i ∈ Pr)) ρ s.1 t.1
    (s.2.2 i) (t.2.2 i) hl hm (le_max_left _ _) (le_max_right _ _)
  simpa only [pd4c_coreGroupKernel, ν, p, q, anchorAt, decide_eq_true_eq] using h

theorem pd4c_physicalEdge_reverse_iff {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (p q : PrimeLists S.x K) (z z' : ℤ × ℤ)
    (hbands : ∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    Pd4cPhysicalEdge F S w p q z z' ↔ Pd4cPhysicalEdge F S w q p z' z :=
  ⟨pd4c_physicalEdge_reverse F S w p q z z' hbands,
    pd4c_physicalEdge_reverse F S w q p z' z hbands⟩

/-- Exact weighted reversal of the projected core edge, for raw and comparison pieces. -/
theorem pd4c_coreProjectedKernel_measure_transpose {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t)
    (hV : ∀ i : Fin K, bandMass S.x (F.a i) ≠ 0)
    (hbands : ∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    (memMeasure F S s : ℂ) * (pd4c_bandFactor F S Pr : ℂ) *
      pd4c_coreProjectedKernel F S ρ w raw St Pr j s t =
    (memMeasure F S t : ℂ) * (pd4c_bandFactor F S St : ℂ) *
      star (pd4c_coreProjectedKernel F S ρ w raw Pr St (j + 1) t s) := by
  rw [pd4c_coreProjectedKernel_formula F S ρ w raw St Pr j s t hs ht,
    pd4c_coreProjectedKernel_formula F S ρ w raw Pr St (j + 1) t s ht hs]
  by_cases hp : Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1
  · have hrev := (pd4c_physicalEdge_reverse_iff F S w s.2.1 t.2.1 s.1 t.1 hbands).mp hp
    rw [if_pos hp, if_pos hrev]
    have hslot := hp.2.2.2.2.1
    have hgeom : edgeMultiplier F S (decide ((j + 1) % 2 = 0)) raw t.2.1 s.2.1 t.1 s.1 =
        star (edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1) := by
      rw [pd4c_step_parity_flip]
      exact pd4c_edgeMultiplier_transpose F S _ raw s.2.1 t.2.1 s.1 t.1 hslot
    rw [star_mul, star_prod, hgeom, star_star]
    simp only [pd4c_coreGroupKernel_star]
    rw [pd4c_memMeasure_factor F S s hs, pd4c_memMeasure_factor F S t ht,
      pd4c_activeDensity_split F S s.2.1, pd4c_activeDensity_split F S t.2.1,
      pd4c_sharedDensity_eq F S s.2.1 t.2.1 hslot]
    unfold pd4c_bandFactor
    push_cast
    simp only [apply_ite, Complex.ofReal_one]
    have hprod := Finset.prod_congr (s₁ := (Finset.univ : Finset (Fin K))) rfl
      (fun i hi => pd4c_coreGroup_measure_transpose F S ρ s t hs ht St Pr i (hV i))
    have hm := congrArg (fun a : ℂ => (pd4c_sharedDensity F S s.2.1 : ℂ) *
      edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1 * a) hprod
    simp only [Finset.prod_mul_distrib] at hm
    linear_combination hm
  · have hrev : ¬ Pd4cPhysicalEdge F S w t.2.1 s.2.1 t.1 s.1 :=
      fun h => hp ((pd4c_physicalEdge_reverse_iff F S w s.2.1 t.2.1 s.1 t.1 hbands).mpr h)
    simp only [if_neg hp, if_neg hrev, star_zero, mul_zero]

end

end ArtinPrimitiveRoots.TypeII.PD
