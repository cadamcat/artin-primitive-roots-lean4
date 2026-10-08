import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MemoryAlphabet
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CubeAdjoint

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_boundedWord_list_injective (T : Finset Particle) (B : ℕ) :
    Function.Injective (fun w : Pd4cBoundedWord T B => pd4c_word w.2) := by
  rintro ⟨n, v⟩ ⟨n', v'⟩ h
  have hlen : n = n' := by
    apply Fin.ext
    have hc := congrArg List.length h
    simpa only [pd4c_word, List.length_ofFn] using hc
  subst n'
  congr 1
  funext k
  apply Subtype.ext
  have hv : (fun k => (v k : Particle)) = (fun k => (v' k : Particle)) :=
    List.ofFn_injective h
  exact congrFun hv k

theorem pd4c_memoryWordPoint_injective {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) :
    Function.Injective (pd4c_memoryWordPoint F S B z p) := by
  intro u v h
  funext i
  apply pd4c_boundedWord_list_injective
  exact congrFun (congrArg (fun s : MemPoint S.x K => s.2.2) h) i

/-- Word representation and the finite physical memory slice have the same weighted sum. -/
theorem pd4c_word_slice_sum {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K)
    (hz : Int.gcd z.1 z.2 = 1) (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i))
    (f : MemPoint S.x K → ℂ) :
    (∑ w : Pd4cMemoryWord F S B, f (pd4c_memoryWordPoint F S B z p w)) =
      ∑ s ∈ (pd4c_valid_memory_slice_finite F S B z p).toFinset, f s := by
  let Q := pd4c_memoryWordPoint F S B z p
  have himage : Finset.univ.image Q = (pd4c_valid_memory_slice_finite F S B z p).toFinset := by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨rfl, rfl, pd4c_memoryWordPoint_valid F S B z p w hz hp,
        pd4c_memoryWordPoint_lengths F S B z p w⟩
    · intro hs
      obtain ⟨w, hw⟩ := pd4c_valid_memory_in_word_range F S B s hs.2.2.1 hs.2.2.2
      exact ⟨w, by simpa only [hs.1, hs.2.1] using hw⟩
  rw [← himage]
  exact (Finset.sum_image (fun u hu v hv h => pd4c_memoryWordPoint_injective F S B z p h)).symm

/-- The exact averaged-delta evaluation in the finite word representation. -/
theorem pd4c_word_delta_pairing {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K)
    (hz : Int.gcd z.1 z.2 = 1) (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i))
    (s : MemPoint S.x K) (hs : s.1 = z ∧ s.2.1 = p ∧ MemValid F S s ∧
      ∀ i, (s.2.2 i).length ≤ B)
    (g : MemPoint S.x K → ℂ) (hg : IsMemorySymmetric g) :
    (∑ w : Pd4cMemoryWord F S B,
      (memMeasure F S (pd4c_memoryWordPoint F S B z p w) : ℂ) *
        star (memorySym (fun u => if u = s then (1 : ℂ) else 0)
          (pd4c_memoryWordPoint F S B z p w)) * g (pd4c_memoryWordPoint F S B z p w)) =
      (memMeasure F S s : ℂ) * g s := by
  rw [pd4c_word_slice_sum F S B z p hz hp (fun t => (memMeasure F S t : ℂ) *
    star (memorySym (fun u => if u = s then (1 : ℂ) else 0) t) * g t)]
  apply pd4c_memorySym_delta_pairing
  · intro t ht σ
    have ht' : t.1 = z ∧ t.2.1 = p ∧ MemValid F S t ∧ ∀ i, (t.2.2 i).length ≤ B := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using ht
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using pd4c_memory_slice_closed F S B z p t ht' σ
  · simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hs
  · exact hg

end

end ArtinPrimitiveRoots.TypeII.PD
