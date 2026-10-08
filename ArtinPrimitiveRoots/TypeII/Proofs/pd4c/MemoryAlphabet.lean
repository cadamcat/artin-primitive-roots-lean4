import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.BoundedAdjoint

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- The finite alphabet of band primes with all their allowed anchors. -/
def pd4c_particleBand (x a : ℝ) : Finset Particle :=
  (primeBand x a).biUnion fun p => (Finset.range (p + 1)).image fun ell => (p, ell)

theorem pd4c_mem_particleBand (x a : ℝ) (e : Particle) :
    e ∈ pd4c_particleBand x a ↔ e.1 ∈ primeBand x a ∧ e.2 ≤ e.1 := by
  rcases e with ⟨p, ell⟩
  simp [pd4c_particleBand, Finset.mem_biUnion, Finset.mem_image, Nat.lt_succ_iff]

/-- A finite representation of all valid per-group words up to the cutoff. -/
abbrev Pd4cMemoryWord {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ) :=
  (i : Fin K) → Pd4cBoundedWord (pd4c_particleBand S.x (F.a i)) B

def pd4c_memoryWordPoint {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) (w : Pd4cMemoryWord F S B) : MemPoint S.x K :=
  (z, p, fun i => pd4c_word (w i).2)

/-- Every valid memory state of bounded group lengths occurs in the finite word representation. -/
theorem pd4c_valid_memory_in_word_range {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (hlen : ∀ i, (s.2.2 i).length ≤ B) :
    s ∈ Set.range (pd4c_memoryWordPoint F S B s.1 s.2.1) := by
  let w : Pd4cMemoryWord F S B := fun i =>
    ⟨⟨(s.2.2 i).length, by have h := hlen i; omega⟩,
      fun k => ⟨(s.2.2 i).get k,
        (pd4c_mem_particleBand S.x (F.a i) _).mpr (hs.2.2 i _ (List.get_mem _ k))⟩⟩
  refine ⟨w, ?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      exact List.ofFn_get (s.2.2 i)

/-- A fixed physical point has only finitely many valid memory states under the cutoff. -/
theorem pd4c_valid_memory_slice_finite {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) :
    {s : MemPoint S.x K | s.1 = z ∧ s.2.1 = p ∧ MemValid F S s ∧
      ∀ i, (s.2.2 i).length ≤ B}.Finite := by
  have hrange := Set.finite_range (pd4c_memoryWordPoint F S B z p)
  apply hrange.subset
  intro s hs
  obtain ⟨w, hw⟩ := pd4c_valid_memory_in_word_range F S B s hs.2.2.1 hs.2.2.2
  refine ⟨w, ?_⟩
  simpa only [hs.1, hs.2.1] using hw

/-- The finite memory slice is closed under each memory-coordinate permutation. -/
theorem pd4c_memory_slice_closed {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) (s : MemPoint S.x K)
    (hs : s.1 = z ∧ s.2.1 = p ∧ MemValid F S s ∧ ∀ i, (s.2.2 i).length ≤ B)
    (σ : MemoryPermutation s) :
    (memoryPermute s σ).1 = z ∧ (memoryPermute s σ).2.1 = p ∧
      MemValid F S (memoryPermute s σ) ∧ ∀ i, ((memoryPermute s σ).2.2 i).length ≤ B := by
  refine ⟨hs.1, hs.2.1, (pd4c_memValid_memoryPermute_iff F S s σ).mpr hs.2.2.1, ?_⟩
  intro i
  simpa only [memoryPermute, List.length_ofFn] using hs.2.2.2 i

/-- Valid physical data and alphabet words give a valid memory-model state. -/
theorem pd4c_memoryWordPoint_valid {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) (w : Pd4cMemoryWord F S B)
    (hz : Int.gcd z.1 z.2 = 1) (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i)) :
    MemValid F S (pd4c_memoryWordPoint F S B z p w) := by
  refine ⟨hz, hp, ?_⟩
  intro i e he
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
  have hband := (pd4c_mem_particleBand S.x (F.a i) ((w i).2 k)).mp ((w i).2 k).property
  simpa only [hk] using hband

theorem pd4c_memoryWordPoint_lengths {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) (w : Pd4cMemoryWord F S B) (i : Fin K) :
    ((pd4c_memoryWordPoint F S B z p w).2.2 i).length ≤ B := by
  change (pd4c_word (w i).2).length ≤ B
  simp only [pd4c_word, List.length_ofFn]
  have h := (w i).1.isLt
  omega

/-- The state measure factors as active density times the factorial memory densities. -/
theorem pd4c_memoryWordPoint_measure {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (z : ℤ × ℤ) (p : PrimeLists S.x K) (w : Pd4cMemoryWord F S B)
    (hz : Int.gcd z.1 z.2 = 1) (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i)) :
    memMeasure F S (pd4c_memoryWordPoint F S B z p w) =
      (∏ i : Fin K, ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (p i j)) *
        ∏ i : Fin K, pd4c_listDensity
          (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1) (pd4c_word (w i).2) := by
  rw [memMeasure, if_pos (pd4c_memoryWordPoint_valid F S B z p w hz hp)]
  rfl

/-- Pairing with the averaged point mass evaluates a symmetric continuation exactly. -/
theorem pd4c_memorySym_delta_pairing {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (hT : ∀ s ∈ T, ∀ σ, memoryPermute s σ ∈ T)
    (s : MemPoint S.x K) (hs : s ∈ T) (g : MemPoint S.x K → ℂ)
    (hg : IsMemorySymmetric g) :
    (∑ t ∈ T, (memMeasure F S t : ℂ) *
      star (memorySym (fun u => if u = s then (1 : ℂ) else 0) t) * g t) =
      (memMeasure F S s : ℂ) * g s := by
  rw [pd4c_memorySym_pairing F S T hT, pd4c_memorySym_eq_self g hg]
  simp [hs]

end

end ArtinPrimitiveRoots.TypeII.PD
