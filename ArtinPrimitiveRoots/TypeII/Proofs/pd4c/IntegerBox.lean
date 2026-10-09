import ArtinPrimitiveRoots.TypeII.Defs

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- A centered integer box embeds in finite natural ranges with controlled side lengths. -/
theorem centered_integer_box_embedding (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (T : Finset (ℤ × ℤ))
    (hT : ∀ u ∈ T, |(u.1 : ℝ)| ≤ A ∧ |(u.2 : ℝ)| ≤ B) :
    let M := (2*⌊A⌋+1).toNat
    let N := (2*⌊B⌋+1).toNat
    let E : (ℤ × ℤ) → (ℕ × ℕ) := fun u =>
      ((u.1+⌊A⌋).toNat, (u.2+⌊B⌋).toNat)
    (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧
      Set.InjOn E (T : Set (ℤ × ℤ)) ∧
      ∀ u ∈ T, E u ∈ (Finset.range M).product (Finset.range N) ∧
        ((E u).1 : ℤ)-⌊A⌋ = u.1 ∧ ((E u).2 : ℤ)-⌊B⌋ = u.2 := by
  let M := (2*⌊A⌋+1).toNat
  let N := (2*⌊B⌋+1).toNat
  let E : (ℤ × ℤ) → (ℕ × ℕ) := fun u =>
    ((u.1+⌊A⌋).toNat, (u.2+⌊B⌋).toNat)
  change (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧
    Set.InjOn E (T : Set (ℤ × ℤ)) ∧
    ∀ u ∈ T, E u ∈ (Finset.range M).product (Finset.range N) ∧
      ((E u).1 : ℤ)-⌊A⌋ = u.1 ∧ ((E u).2 : ℤ)-⌊B⌋ = u.2
  have hwidth (C : ℝ) (hC : 1 ≤ C) : ((2*⌊C⌋+1).toNat : ℝ) ≤ 3*C := by
    have hfloorone : 1 ≤ ⌊C⌋ := Int.le_floor.mpr (by simpa only [Int.cast_one] using hC)
    have hn : 0 ≤ 2*⌊C⌋+1 := by omega
    have hcast := congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hn)
    push_cast at hcast
    linarith [Int.floor_le C]
  have haxis (C : ℝ) (hC : 1 ≤ C) (v : ℤ) (hv : |(v : ℝ)| ≤ C) :
      (v+⌊C⌋).toNat < (2*⌊C⌋+1).toNat ∧
        ((v+⌊C⌋).toNat : ℤ)-⌊C⌋ = v := by
    have hlo : -⌊C⌋ ≤ v := by
      have hneg : ((-v : ℤ) : ℝ) ≤ C := by
        simpa only [Int.cast_neg] using (show -(v : ℝ) ≤ C by linarith [(abs_le.mp hv).1])
      have h := Int.le_floor.mpr hneg
      omega
    have hhi : v ≤ ⌊C⌋ := Int.le_floor.mpr (abs_le.mp hv).2
    have hfloorone : 1 ≤ ⌊C⌋ := Int.le_floor.mpr (by simpa only [Int.cast_one] using hC)
    have heq := Int.toNat_of_nonneg (show 0 ≤ v+⌊C⌋ by omega)
    have hwidthEq := Int.toNat_of_nonneg (show 0 ≤ 2*⌊C⌋+1 by omega)
    constructor <;> omega
  have hrecover (u : ℤ × ℤ) (hu : u ∈ T) :
      ((E u).1 : ℤ)-⌊A⌋ = u.1 ∧ ((E u).2 : ℤ)-⌊B⌋ = u.2 :=
    ⟨(haxis A hA u.1 (hT u hu).1).2, (haxis B hB u.2 (hT u hu).2).2⟩
  refine ⟨hwidth A hA, hwidth B hB, ?_, ?_⟩
  · intro u hu v hv huv
    apply Prod.ext
    · have h := congrArg (fun p : ℕ × ℕ => ((p.1 : ℤ)-⌊A⌋)) huv
      simpa only [(hrecover u hu).1, (hrecover v hv).1] using h
    · have h := congrArg (fun p : ℕ × ℕ => ((p.2 : ℤ)-⌊B⌋)) huv
      simpa only [(hrecover u hu).2, (hrecover v hv).2] using h
  · intro u hu
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hrecover u hu⟩
    · exact Finset.mem_range.mpr (haxis A hA u.1 (hT u hu).1).1
    · exact Finset.mem_range.mpr (haxis B hB u.2 (hT u hu).2).1

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
