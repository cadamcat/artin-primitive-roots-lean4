import ArtinPrimitiveRoots.TypeII.PD.RootReplacement

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- A bad-source-and-target-box predicate changes only at one of its three component boundaries. -/
theorem nonconstant_bad_and_box {α : Type*} (A B C : α → Prop) (s : Set α)
    (h : ∃ y ∈ s, ∃ y' ∈ s, (A y ∧ ¬ B y ∧ C y) ∧ ¬ (A y' ∧ ¬ B y' ∧ C y')) :
    (∃ y ∈ s, ∃ y' ∈ s, (A y ∧ B y) ∧ ¬ (A y' ∧ B y')) ∨
      (∃ y ∈ s, ∃ y' ∈ s, A y ∧ ¬ A y') ∨
      (∃ y ∈ s, ∃ y' ∈ s, C y ∧ ¬ C y') := by
  obtain ⟨y, hy, y', hy', htrue, hnot⟩ := h
  obtain ⟨hAy, hBy, hCy⟩ := htrue
  by_cases hCy' : C y'
  · by_cases hAy' : A y'
    · have hBy' : B y' := by by_contra h; exact hnot ⟨hAy', h, hCy'⟩
      exact Or.inl ⟨y', hy', y, hy, ⟨hAy', hBy'⟩, fun hAB => hBy hAB.2⟩
    · exact Or.inr (Or.inl ⟨y, hy, y', hy', hAy, hAy'⟩)
  · exact Or.inr (Or.inr ⟨y, hy, y', hy', hCy, hCy'⟩)

/-- A real point is contained in at most three closed one-dimensional grid intervals. -/
theorem gridInterval_membership_card_le (h y : ℝ) (hh : 0 < h) (T : Finset ℤ)
    (hT : ∀ k ∈ T, (k : ℝ) * h ≤ y ∧ y ≤ ((k : ℝ) + 1) * h) : T.card ≤ 3 := by
  let I : Finset ℤ := Finset.Icc ⌈y / h - 1⌉ ⌊y / h⌋
  have hsub : T ⊆ I := by
    intro k hk
    have hb := hT k hk
    refine Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
    · have hle : y / h ≤ (k : ℝ) + 1 := (div_le_iff₀ hh).mpr hb.2
      linarith
    · exact (le_div_iff₀ hh).mpr hb.1
  have hfloor := Int.floor_le (y / h)
  have hceil := Int.le_ceil (y / h - 1)
  have hdiffR : ((⌊y / h⌋ + 1 - ⌈y / h - 1⌉ : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
  have hdiffZ : (⌊y / h⌋ + 1 - ⌈y / h - 1⌉ : ℤ) ≤ 3 := by exact_mod_cast hdiffR
  have hI : I.card ≤ 3 := by simpa only [I, Int.card_Icc] using Int.toNat_le.mpr hdiffZ
  exact (Finset.card_le_card hsub).trans hI

/-- Finite bad-grid boundary counts are bounded by the sum of the three component counts. -/
theorem badGrid_boundary_card_le (h : ℝ) (T : Finset (ℤ × ℤ × ℤ))
    (A B C : ℝ × ℝ × ℝ → Prop) :
    (((T.filter fun k => IsNonconstantOn (fun y => A y ∧ ¬ B y ∧ C y) (gridCube h k)).card) : ℝ) ≤
      ((T.filter fun k => IsNonconstantOn (fun y => A y ∧ B y) (gridCube h k)).card : ℝ) +
      ((T.filter fun k => IsNonconstantOn A (gridCube h k)).card : ℝ) +
      ((T.filter fun k => IsNonconstantOn C (gridCube h k)).card : ℝ) := by
  let U := T.filter fun k => IsNonconstantOn (fun y => A y ∧ B y) (gridCube h k)
  let V := T.filter fun k => IsNonconstantOn A (gridCube h k)
  let W := T.filter fun k => IsNonconstantOn C (gridCube h k)
  have hsub : (T.filter fun k => IsNonconstantOn (fun y => A y ∧ ¬ B y ∧ C y) (gridCube h k)) ⊆
      U ∪ (V ∪ W) := by
    intro k hk
    obtain ⟨hkT, hbad⟩ := Finset.mem_filter.mp hk
    rcases nonconstant_bad_and_box A B C (gridCube h k) hbad with hAB | hA | hC
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hkT, hAB⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hkT, hA⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hkT, hC⟩))))
  have hcard : (T.filter fun k => IsNonconstantOn (fun y => A y ∧ ¬ B y ∧ C y) (gridCube h k)).card ≤
      U.card + V.card + W.card := by
    calc
      _ ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
      _ ≤ U.card + (V ∪ W).card := Finset.card_union_le U (V ∪ W)
      _ ≤ _ := by have hvw := Finset.card_union_le V W; omega
  exact_mod_cast hcard


/-- A point lies in at most 27 cubes of any finite product of closed coordinate grids. -/
theorem gridCube_membership_card_le (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ)
    (T₁ T₂ T₃ : Finset ℤ) :
    (((T₁ ×ˢ (T₂ ×ˢ T₃)).filter fun k => y ∈ gridCube h k).card) ≤ 27 := by
  let A := T₁.filter fun k : ℤ => (k : ℝ) * h ≤ y.1 ∧ y.1 ≤ ((k : ℝ) + 1) * h
  let B := T₂.filter fun k : ℤ => (k : ℝ) * h ≤ y.2.1 ∧ y.2.1 ≤ ((k : ℝ) + 1) * h
  let C := T₃.filter fun k : ℤ => (k : ℝ) * h ≤ y.2.2 ∧ y.2.2 ≤ ((k : ℝ) + 1) * h
  have hset : ((T₁ ×ˢ (T₂ ×ˢ T₃)).filter fun k => y ∈ gridCube h k) = A ×ˢ (B ×ˢ C) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_product, gridCube, Set.mem_setOf_eq, A, B, C]
    aesop
  have hA : A.card ≤ 3 := gridInterval_membership_card_le h y.1 hh A
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hB : B.card ≤ 3 := gridInterval_membership_card_le h y.2.1 hh B
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hC : C.card ≤ 3 := gridInterval_membership_card_le h y.2.2 hh C
    (fun k hk => (Finset.mem_filter.mp hk).2)
  rw [hset, Finset.card_product, Finset.card_product]
  have h := Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
  norm_num at h
  exact h

theorem gridIndices_membership_card_le (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ) :
    ((gridIndices h).filter fun k => y ∈ gridCube h k).card ≤ 27 := by
  unfold gridIndices
  exact gridCube_membership_card_le h hh y _ _ _


end ArtinPrimitiveRoots.TypeII.PD
