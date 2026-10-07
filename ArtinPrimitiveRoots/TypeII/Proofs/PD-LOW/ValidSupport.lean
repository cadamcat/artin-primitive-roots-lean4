import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.SignSupport

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Indexed removal keeps only particles of the original list. -/
theorem pd5_removeIndices_mem (l : List Particle) (D : Finset (Fin l.length))
    (e : Particle) (he : e ∈ removeIndices l D) : e ∈ l := by
  unfold removeIndices at he
  obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp he
  by_cases hD : k ∈ D
  · simp [hD] at he
  · simp only [if_neg hD] at he
    have heq : l.get k = e := Option.some.inj he
    rw [← heq]
    exact List.get_mem l k

/-- A deterministic anchor lies in the allowed projective-line coordinate range. -/
theorem pd5_anchorAt_valid (p : ℕ) (z : ℤ × ℤ) : (anchorAt p z).2 ≤ p := by
  exact Nat.le_of_lt_succ (projLine p z).isLt

/-- Reordering memory preserves validity, including repeated particles. -/
theorem pd5_memoryPermute_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) (σ : MemoryPermutation s) :
    MemValid F S (memoryPermute s σ) := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro i e he
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
  exact hs.2.2 i _ (List.get_mem _ _)

/-- Active-list permutations preserve validity. -/
theorem pd5_activePermute_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    MemValid F S (s.1, permuteLists σ s.2.1, s.2.2) := by
  exact ⟨hs.1, fun i j => hs.2.1 i (σ i j), hs.2.2⟩

/-- Every ghost choice from a valid source reaches a valid state. -/
theorem pd5_ghost_output_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    MemValid F S (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
      List.ofFn fun k => anchorAt (new i k) s.1) := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro i e he
  rcases List.mem_append.mp he with he | he
  · exact hs.2.2 i e (pd5_removeIndices_mem _ _ _ he)
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨(new i k).property, pd5_anchorAt_valid _ _⟩

/-- Every admissible edge choice from a valid source reaches a valid state. -/
theorem pd5_edge_output_valid {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hc : EdgeAdmissible F S w s c z') :
    MemValid F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
  rcases hc with ⟨_, _, htarget, _, _, hgcd, _, _, _, _⟩
  refine ⟨hgcd, fun i j => (htarget.1 i j).2, ?_⟩
  intro i e he
  change e ∈ removeIndices (s.2.2 i)
    (match (c i).2 with | .inl k => {k} | .inr _ => ∅) ++
    (if (c i).1 then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) at he
  rcases List.mem_append.mp he with he | he
  · exact hs.2.2 i e (pd5_removeIndices_mem _ _ _ he)
  · cases hstore : (c i).1 with
    | false => simp [hstore] at he
    | true =>
      have heq : e = anchorAt (s.2.1 i (lastSlot S.x)) s.1 := by simpa [hstore] using he
      rw [heq]
      exact ⟨hs.2.1 i (lastSlot S.x), pd5_anchorAt_valid _ _⟩

/-- Averaging an invalid target's delta vanishes at each valid evaluation state. -/
theorem pd5_memorySym_delta_invalid {K : ℕ} (F : PDFix K) (S : PDScale)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : ¬ MemValid F S t) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
  have hzero : (∑ σ : MemoryPermutation s,
      if memoryPermute s σ = t then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    have hne : memoryPermute s σ ≠ t := by
      intro he
      exact ht (he ▸ pd5_memoryPermute_valid F S s hs σ)
    simp [hne]
  change (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ * _ = 0
  rw [hzero, mul_zero]

/-- Ghosts annihilate continuations that vanish on every valid state; this is termwise and
needs no convergence assumption. -/
theorem pd5_logGhost_zero_on_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, MemValid F S σL.1 → f σL = 0)
    (sL : LogPoint S.x K) (hs : MemValid F S sL.1) :
    logGhost F S ρ j f sL = 0 := by
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D _
  trans ∑' _l : Fin K → ℕ, (0 : ℂ)
  · apply tsum_congr
    intro l
    apply Finset.sum_eq_zero
    intro new _
    have hvalid := pd5_ghost_output_valid F S sL.1 hs D l new
    split_ifs
    · rw [hf _ hvalid]
      simp
    · rfl
  · exact tsum_zero

/-- A bounded local twist still cannot send a valid evaluation state to an invalid input
state, after the target memory average. -/
theorem pd5_twisted_ghost_kernel_invalid {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (W : BirthLog K → ℂ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : ¬ MemValid F S t) :
    memKernel (fun f => pd5_ghostBirthTwist F S ρ j W (memorySym f)) s t = 0 := by
  unfold memKernel pd5_ghostBirthTwist
  apply pd5_logGhost_zero_on_valid F S ρ j _ _ (s, []) hs
  intro σL hσ
  rw [pd5_memorySym_delta_invalid F S σL.1 t hσ ht, mul_zero]

end
end ArtinPrimitiveRoots.TypeII.PD
