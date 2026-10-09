import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

/-- Finite support admits a finite closure under both endpoint averaging actions. -/
theorem clean_finite_permutation_support_closure {x : ℝ} {K : ℕ}
    (B : ℕ) (T : Finset (MemPoint x K))
    (hT : ∀ s ∈ T, memSize s ≤ B) :
    ∃ U : Finset (MemPoint x K), T ⊆ U ∧
      (∀ s ∈ U, memSize s ≤ B) ∧
      (∀ (s : MemPoint x K) (σ : MemoryPermutation s),
        s ∈ U ↔ memoryPermute s σ ∈ U) ∧
      (∀ (s : MemPoint x K) (σ : Fin K → Equiv.Perm (Fin (slotCount x))),
        s ∈ U ↔ (s.1, permuteLists σ s.2.1, s.2.2) ∈ U) := by
  classical
  let Z := T.image (fun s => s.1)
  let E : Finset ℕ := T.biUnion fun s =>
    Finset.univ.biUnion fun i : Fin K =>
      Finset.univ.image fun j : Fin (slotCount x) => s.2.1 i j
  let Q : Finset Particle := T.biUnion fun s =>
    Finset.univ.biUnion fun i : Fin K => (s.2.2 i).toFinset
  let A := Fin K → Fin (slotCount x) → E
  let C := Σ n : Fin (B+1), Fin n.val → Q
  let D := Z × A × (Fin K → C)
  let out : D → MemPoint x K := fun q =>
    ((q.1 : ℤ × ℤ), (fun i j => (q.2.1 i j : ℕ)),
      fun i => List.ofFn (fun j => ((q.2.2 i).2 j : Particle)))
  let U := ((Finset.univ : Finset D).image out).filter fun s => memSize s ≤ B
  let P := fun s : MemPoint x K => s.1 ∈ Z ∧
    (∀ i j, s.2.1 i j ∈ E) ∧ (∀ i, ∀ e ∈ s.2.2 i, e ∈ Q) ∧ memSize s ≤ B
  have hP (s : MemPoint x K) : s ∈ U ↔ P s := by
    constructor
    · intro hs
      obtain ⟨hi, hsize⟩ := Finset.mem_filter.mp hs
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hi
      rw [← heq] at hsize ⊢
      refine ⟨q.1.2, fun i j => (q.2.1 i j).2, ?_, hsize⟩
      intro i e he
      change e ∈ List.ofFn (fun j => ((q.2.2 i).2 j : Particle)) at he
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
      rw [← hj]
      exact ((q.2.2 i).2 j).2
    · rintro ⟨hz, ha, hm, hsize⟩
      have hlen (i : Fin K) : (s.2.2 i).length ≤ B := by
        have htotal : (s.2.2 i).length ≤ memSize s := by
          change (s.2.2 i).length ≤ ∑ k : Fin K, (s.2.2 k).length
          exact Finset.single_le_sum
            (fun k hk => Nat.zero_le ((s.2.2 k).length)) (Finset.mem_univ i)
        exact htotal.trans hsize
      let a : A := fun i j => ⟨s.2.1 i j, ha i j⟩
      let c : Fin K → C := fun i =>
        ⟨⟨(s.2.2 i).length, Nat.lt_succ_of_le (hlen i)⟩,
          fun j => ⟨(s.2.2 i).get j, hm i _ (List.get_mem _ _)⟩⟩
      let q : D := (⟨s.1, hz⟩, a, c)
      have hout : out q = s := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i
            change List.ofFn (fun j => (s.2.2 i).get j) = s.2.2 i
            exact List.ofFn_get _
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hout⟩, hsize⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply (hP s).mpr
    refine ⟨Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_, ?_, hT s hs⟩
    · intro i j
      exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩⟩
    · intro i e he
      exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr he⟩⟩
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s σ
    have hperm (i : Fin K) : List.Perm ((memoryPermute s σ).2.2 i) (s.2.2 i) := by
      simpa only [memoryPermute, Function.comp_def] using
        (Equiv.Perm.ofFn_comp_perm (σ i) (fun j => (s.2.2 i).get j)).trans
          (List.Perm.of_eq (List.ofFn_get (s.2.2 i)))
    have hsize : memSize (memoryPermute s σ) = memSize s := by
      simp only [memSize, memoryPermute, List.length_ofFn]
    constructor
    · intro hs
      obtain ⟨hz, ha, hm, hb⟩ := (hP s).mp hs
      apply (hP _).mpr
      refine ⟨hz, ha, ?_, ?_⟩
      · intro i e he
        exact hm i e ((hperm i).mem_iff.mp he)
      · rw [hsize]; exact hb
    · intro hs
      obtain ⟨hz, ha, hm, hb⟩ := (hP _).mp hs
      apply (hP s).mpr
      refine ⟨hz, ha, ?_, ?_⟩
      · intro i e he
        exact hm i e ((hperm i).mem_iff.mpr he)
      · rw [← hsize]; exact hb
  · intro s σ
    constructor
    · intro hs
      obtain ⟨hz, ha, hm, hb⟩ := (hP s).mp hs
      apply (hP _).mpr
      exact ⟨hz, fun i j => ha i (σ i j), hm, hb⟩
    · intro hs
      obtain ⟨hz, ha, hm, hb⟩ := (hP _).mp hs
      apply (hP s).mpr
      refine ⟨hz, ?_, hm, hb⟩
      intro i j
      have h := ha i ((σ i).symm j)
      simpa only [permuteLists, Equiv.apply_symm_apply] using h

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
