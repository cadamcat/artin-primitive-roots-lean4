import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridVolume
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridCounting
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CoverVolume

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

def selectedRootCells (h : ℝ) (P : ℝ × ℝ × ℝ → Prop) : Finset (ℤ × ℤ × ℤ) :=
  (gridIndices h).filter fun k => ∃ y ∈ normalizedRootRegion ∩ gridCube h k, P y

def boundaryRootCells (h : ℝ) (P : ℝ × ℝ × ℝ → Prop) : Finset (ℤ × ℤ × ℤ) :=
  (gridIndices h).filter fun k => IsNonconstantOn P (gridCube h k)

/-- The upper grid majorant costs model mass and one cube volume per boundary cell. -/
theorem selectedRootCells_volume_upper (h : ℝ) (hh : 0 < h)
    (P : ℝ × ℝ × ℝ → Prop) (hP : MeasurableSet {y | P y}) :
    (∑ k ∈ selectedRootCells h P, volume.real (normalizedRootRegion ∩ gridCube h k)) ≤
      27 * volume.real (normalizedRootRegion ∩ {y | P y}) +
        ((boundaryRootCells h P).card : ℝ) * h ^ 3 := by
  let μ := volume.restrict normalizedRootRegion
  letI : IsFiniteMeasure μ := ⟨by
    change volume.restrict normalizedRootRegion Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact normalizedRootRegion_compact.measure_lt_top⟩
  have hselected : selectedRootCells h P ⊆ gridIndices h := Finset.filter_subset _ _
  have hboundary : boundaryRootCells h P ⊆ gridIndices h := Finset.filter_subset _ _
  have hconstant : ∀ k ∈ selectedRootCells h P, k ∉ boundaryRootCells h P →
      ∀ y ∈ gridCube h k, P y := by
    intro k hk hnot
    have hk' : k ∈ gridIndices h ∧ ∃ y ∈ normalizedRootRegion ∩ gridCube h k, P y := by
      simpa only [selectedRootCells, Finset.mem_filter] using hk
    obtain ⟨y, hy, hPy⟩ := hk'.2
    have hNoChange : ¬ IsNonconstantOn P (gridCube h k) := by
      intro hchange
      exact hnot (Finset.mem_filter.mpr ⟨hk'.1, hchange⟩)
    exact true_of_selected_constant_cell P (gridCube h k) ⟨y, hy.2, hPy⟩ hNoChange
  have hvolume := selectedCell_volume_upper μ (gridIndices h) (selectedRootCells h P)
    (boundaryRootCells h P) (gridCube h) (fun k hk => gridCube_measurable h k) P hP 27
    hselected hboundary hconstant (gridIndices_membership_card_le h hh)
  have hcellReal (k : ℤ × ℤ × ℤ) : μ.real (gridCube h k) =
      volume.real (normalizedRootRegion ∩ gridCube h k) := by
    dsimp [μ, Measure.real]
    rw [Measure.restrict_apply (gridCube_measurable h k), Set.inter_comm]
  have hbadReal : μ.real {y | P y} = volume.real (normalizedRootRegion ∩ {y | P y}) := by
    dsimp [μ, Measure.real]
    rw [Measure.restrict_apply hP, Set.inter_comm]
  simp_rw [hcellReal, hbadReal] at hvolume
  apply hvolume.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ k ∈ boundaryRootCells h P, h ^ 3 :=
      Finset.sum_le_sum (fun k hk => clippedCube_volume_le_all h hh.le k)
    _ = _ := by simp

end
end ArtinPrimitiveRoots.TypeII.PD
