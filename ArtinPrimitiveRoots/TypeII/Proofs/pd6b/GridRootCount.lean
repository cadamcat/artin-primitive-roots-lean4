import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridMajorant

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

/-- The finite root count is bounded by model mass, boundary-cube volume and residue errors. -/
theorem grid_root_count_upper {α : Type*} [DecidableEq α]
    (S : Finset α) (coord : α → ℝ × ℝ × ℝ) (P : ℝ × ℝ × ℝ → Prop)
    (hP : MeasurableSet {y | P y}) (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hregion : ∀ x ∈ S, coord x ∈ normalizedRootRegion) (hbad : ∀ x ∈ S, P (coord x))
    (M E : ℝ) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hwindow : ∀ k ∈ selectedRootCells h P,
      ((S.filter fun x => coord x ∈ gridCube h k).card : ℝ) ≤
        M * volume.real (normalizedRootRegion ∩ gridCube h k) + E) :
    (S.card : ℝ) ≤
      M * (27 * volume.real (normalizedRootRegion ∩ {y | P y}) +
        ((boundaryRootCells h P).card : ℝ) * h ^ 3) + (475 / h ^ 3) * E := by
  let cell (k : ℤ × ℤ × ℤ) := S.filter fun x => coord x ∈ gridCube h k
  have hcover : S ⊆ (selectedRootCells h P).biUnion cell := by
    intro x hx
    have hy := hregion x hx
    have hcoords : (1 ≤ (coord x).1 ∧ (coord x).1 ≤ 16) ∧
        (1 ≤ (coord x).2.1 ∧ (coord x).2.1 ≤ 2) ∧
        (0 ≤ (coord x).2.2 ∧ (coord x).2.2 ≤ 1) := hy
    obtain ⟨k, hk, hcell⟩ := normalizedRoot_mem_grid h hh (coord x) hcoords
    have hkSel : k ∈ selectedRootCells h P := by
      have hm : k ∈ gridIndices h ∧ ∃ y ∈ normalizedRootRegion ∩ gridCube h k, P y :=
        ⟨hk, coord x, ⟨hy, hcell⟩, hbad x hx⟩
      simpa only [selectedRootCells, Finset.mem_filter] using hm
    exact Finset.mem_biUnion.mpr ⟨k, hkSel, Finset.mem_filter.mpr ⟨hx, hcell⟩⟩
  have hCount := finiteCover_count_upper S (selectedRootCells h P) cell
    (fun k => volume.real (normalizedRootRegion ∩ gridCube h k)) hcover M E hwindow
  have hVol := selectedRootCells_volume_upper h hh P hP
  have hSelCard : ((selectedRootCells h P).card : ℝ) ≤ ((gridIndices h).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun k =>
      ∃ y ∈ normalizedRootRegion ∩ gridCube h k, P y) (gridIndices h))
  have hAllCard := gridIndices_card_le h hh hh₁
  calc
    _ ≤ M * (∑ k ∈ selectedRootCells h P, volume.real (normalizedRootRegion ∩ gridCube h k)) +
        ((selectedRootCells h P).card : ℝ) * E := hCount
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hVol hM)
      (mul_le_mul_of_nonneg_right (hSelCard.trans hAllCard) hE)

end ArtinPrimitiveRoots.TypeII.PD
