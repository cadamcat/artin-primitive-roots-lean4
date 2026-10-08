import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridRootCount
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.RootWindows

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

def normalizedRootCoord (U V : ℝ) (uv : ℕ × ℕ) : ℝ × ℝ × ℝ :=
  ((uv.1 : ℝ) / U, (uv.2 : ℝ) / V, (rootC uv.1 uv.2 : ℝ) / uv.1)

/-- Apply uniform residue-window counts to a finite bad-root set using the closed-grid majorant. -/
theorem root_grid_upper_from_windows (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (Sq : ℕ) (lam : (p : ℕ) → Fin (p + 1)) (S : Finset (ℕ × ℕ))
    (hS : ∀ uv ∈ S, uv ∈ rootWindowSet U V Sq lam (1, 1, 0) (16, 2, 1))
    (P : ℝ × ℝ × ℝ → Prop) (hP : MeasurableSet {y | P y})
    (hbad : ∀ uv ∈ S, P (normalizedRootCoord U V uv))
    (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) (ρ E : ℝ) (hρ : 0 ≤ ρ) (hE : 0 ≤ E)
    (horacle : ∀ lo hi : ℝ × ℝ × ℝ,
      1 ≤ lo.1 → lo.1 ≤ hi.1 → hi.1 ≤ 16 → 1 ≤ lo.2.1 → lo.2.1 ≤ hi.2.1 → hi.2.1 ≤ 2 →
      0 ≤ lo.2.2 → lo.2.2 ≤ hi.2.2 → hi.2.2 ≤ 1 →
      |((rootWindowSet U V Sq lam lo hi).ncard : ℝ) -
        U * V * (hi.1 - lo.1) * (hi.2.1 - lo.2.1) * (hi.2.2 - lo.2.2) * ρ| ≤ E) :
    (S.card : ℝ) ≤ U * V * ρ *
      (27 * volume.real (normalizedRootRegion ∩ {y | P y}) +
        ((boundaryRootCells h P).card : ℝ) * h ^ 3) + (475 / h ^ 3) * E := by
  have hregion (uv : ℕ × ℕ) (huv : uv ∈ S) : normalizedRootCoord U V uv ∈ normalizedRootRegion := by
    obtain ⟨hc, hu, hl₁, hr₁, hl₂, hr₂, hl₃, hr₃, hlines⟩ := hS uv huv
    exact ⟨⟨hl₁, hr₁⟩, ⟨hl₂, hr₂⟩, ⟨hl₃, hr₃⟩⟩
  apply grid_root_count_upper S (normalizedRootCoord U V) P hP h hh hh₁ hregion hbad
    (U * V * ρ) E (by positivity) hE
  intro k hk
  have hk' : k ∈ gridIndices h ∧ ∃ y ∈ normalizedRootRegion ∩ gridCube h k, P y := by
    simpa only [selectedRootCells, Finset.mem_filter] using hk
  obtain ⟨y, hy, hPy⟩ := hk'.2
  have hbounds := clippedCube_bounds h k y hy.1 hy.2
  let lo := clippedCubeLo h k
  let hi := clippedCubeHi h k
  have hfinite := rootWindowSet_finite U V hU hV Sq lam lo hi (min_le_left _ _) (min_le_left _ _)
  have hsub : (S.filter fun uv => normalizedRootCoord U V uv ∈ gridCube h k) ⊆ hfinite.toFinset := by
    intro uv huv
    obtain ⟨huvS, hcell⟩ := Finset.mem_filter.mp huv
    obtain ⟨hc, hu, hl₁, hr₁, hl₂, hr₂, hl₃, hr₃, hlines⟩ := hS uv huvS
    obtain ⟨hcl₁, hcr₁, hcl₂, hcr₂, hcl₃, hcr₃⟩ := hcell
    apply hfinite.mem_toFinset.mpr
    exact ⟨hc, hu, max_le hl₁ hcl₁, le_min hr₁ hcr₁,
      max_le hl₂ hcl₂, le_min hr₂ hcr₂, max_le hl₃ hcl₃, le_min hr₃ hcr₃, hlines⟩
  have hcard : ((S.filter fun uv => normalizedRootCoord U V uv ∈ gridCube h k).card : ℝ) ≤
      ((rootWindowSet U V Sq lam lo hi).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    exact_mod_cast Finset.card_le_card hsub
  have hdiscrepancy := horacle lo hi hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1
    hbounds.2.2.2.2.1 hbounds.2.2.2.2.2.1 hbounds.2.2.2.2.2.2.1
    hbounds.2.2.2.2.2.2.2.1 hbounds.2.2.2.2.2.2.2.2
  have hupper := rootWindow_count_upper U V E ρ Sq lam lo hi hdiscrepancy
  have hvolume := clippedCube_volume h k ⟨hbounds.2.1, hbounds.2.2.2.2.1, hbounds.2.2.2.2.2.2.2.1⟩
  rw [← hvolume] at hupper
  exact hcard.trans hupper

end
end ArtinPrimitiveRoots.TypeII.PD
