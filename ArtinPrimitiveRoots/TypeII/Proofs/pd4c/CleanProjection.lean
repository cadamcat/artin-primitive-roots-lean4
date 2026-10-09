import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanPermutationClosure
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanActiveContraction

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

private theorem clean_memory_sym_support {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K))
    (hT : ∀ (s : MemPoint x K) (σ : MemoryPermutation s),
      s ∈ T ↔ memoryPermute s σ ∈ T)
    (f : MemPoint x K → ℂ) (hf : ∀ s, s ∉ T → f s = 0) :
    ∀ s, s ∉ T → memorySym f s = 0 := by
  classical
  intro s hs
  unfold memorySym
  have hsum : (∑ σ : MemoryPermutation s, f (memoryPermute s σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    apply hf
    intro hp
    exact hs ((hT s σ).mpr hp)
  rw [hsum, mul_zero]

private theorem clean_active_sym_support {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K))
    (hT : ∀ (s : MemPoint S.x K) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))),
      s ∈ T ↔ (s.1, permuteLists σ s.2.1, s.2.2) ∈ T)
    (f : MemPoint S.x K → ℂ) (hf : ∀ s, s ∉ T → f s = 0) :
    ∀ s, s ∉ T → plainOp (logSym F S) f s = 0 := by
  classical
  intro s hs
  change (permCount S.x K : ℂ)⁻¹ *
    (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      f (s.1, permuteLists σ s.2.1, s.2.2)) = 0
  have hsum : (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      f (s.1, permuteLists σ s.2.1, s.2.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    apply hf
    intro hp
    exact hs ((hT s σ).mpr hp)
  rw [hsum, mul_zero]

private theorem clean_edge_eq_active_core {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j : ℕ)
    (f : MemPoint S.x K → ℂ) :
    memEdge F S ρ w EdgeKind.clean j f =
      plainOp (logSym F S) (fun s =>
        plainOp (logEdgePiece F S ρ w j true ∅ ∅) (plainOp (logSym F S) f) s-
          plainOp (logEdgePiece F S ρ w j false ∅ ∅) (plainOp (logSym F S) f) s) := by
  rfl

/-- Endpoint and memory averaging preserve a finite clean-core norm bound. -/
theorem clean_projected_edge_norm_of_core_norm {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (R : ℝ)
    (hm : ∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s)
    (hcore : MemOpNormLE F S B
      (fun f s => plainOp (logEdgePiece F S ρ w j true ∅ ∅) f s-
        plainOp (logEdgePiece F S ρ w j false ∅ ∅) f s) R) :
    MemOpNormLE_sym F S B (memEdge F S ρ w EdgeKind.clean j) R := by
  classical
  change MemOpNormLE F S B
    (fun f => memEdge F S ρ w EdgeKind.clean j (memorySym f)) R
  intro T O f hf hT hO
  obtain ⟨U, hTU, hU, hUmemory, hUactive⟩ :=
    clean_finite_permutation_support_closure B T hT
  obtain ⟨V, hOV, hV, hVmemory, hVactive⟩ :=
    clean_finite_permutation_support_closure B O hO
  let active := fun g : MemPoint S.x K → ℂ => plainOp (logSym F S) g
  let core := fun g : MemPoint S.x K → ℂ => fun s =>
    plainOp (logEdgePiece F S ρ w j true ∅ ∅) g s-
      plainOp (logEdgePiece F S ρ w j false ∅ ∅) g s
  have hfU : ∀ s, s ∉ U → f s = 0 := by
    intro s hs
    exact hf s (fun ht => hs (hTU ht))
  have hmemorySupport : ∀ s, s ∉ U → memorySym f s = 0 :=
    clean_memory_sym_support U hUmemory f hfU
  have hactiveSupport : ∀ s, s ∉ U → active (memorySym f) s = 0 :=
    clean_active_sym_support F S U hUactive (memorySym f) hmemorySupport
  have hinput : memNormSqOn F S U f = memNormSqOn F S T f := by
    unfold memNormSqOn
    symm
    apply Finset.sum_subset hTU
    intro s hsU hsT
    rw [hf s hsT]
    simp
  have hmemoryNorm : memNormSqOn F S U (memorySym f) ≤ memNormSqOn F S U f :=
    memorySym_contraction F S U f hm (fun s hs σ => (hUmemory s σ).mp hs)
  have hactiveInput : memNormSqOn F S U (active (memorySym f)) ≤
      memNormSqOn F S U (memorySym f) :=
    clean_active_sym_contraction F S U (memorySym f) hm
      (fun s hs σ => (hUactive s σ).mp hs)
  have hcoreNorm : memNormSqOn F S V (core (active (memorySym f))) ≤
      R^2*memNormSqOn F S U (active (memorySym f)) :=
    hcore U V (active (memorySym f)) hactiveSupport hU hV
  have hactiveOutput :
      memNormSqOn F S V (active (core (active (memorySym f)))) ≤
        memNormSqOn F S V (core (active (memorySym f))) :=
    clean_active_sym_contraction F S V (core (active (memorySym f))) hm
      (fun s hs σ => (hVactive s σ).mp hs)
  have houtputSubset :
      memNormSqOn F S O (active (core (active (memorySym f)))) ≤
        memNormSqOn F S V (active (core (active (memorySym f)))) := by
    unfold memNormSqOn
    apply Finset.sum_le_sum_of_subset_of_nonneg hOV
    intro s hsV hsO
    exact mul_nonneg (hm s) (sq_nonneg _)
  have hedge : memEdge F S ρ w EdgeKind.clean j (memorySym f) =
      active (core (active (memorySym f))) :=
    clean_edge_eq_active_core F S ρ w j (memorySym f)
  calc
    memNormSqOn F S O (memEdge F S ρ w EdgeKind.clean j (memorySym f)) =
        memNormSqOn F S O (active (core (active (memorySym f)))) := by rw [hedge]
    _ ≤ memNormSqOn F S V (active (core (active (memorySym f)))) := houtputSubset
    _ ≤ memNormSqOn F S V (core (active (memorySym f))) := hactiveOutput
    _ ≤ R^2*memNormSqOn F S U (active (memorySym f)) := hcoreNorm
    _ ≤ R^2*memNormSqOn F S U (memorySym f) :=
      mul_le_mul_of_nonneg_left hactiveInput (sq_nonneg R)
    _ ≤ R^2*memNormSqOn F S U f :=
      mul_le_mul_of_nonneg_left hmemoryNorm (sq_nonneg R)
    _ = R^2*memNormSqOn F S T f := by rw [hinput]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
