import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Joint smoothness of the product radial kernel in positive coordinate charts.
Uses frozen `G1_h3_basics`, `G6_ppi` and the
finite product rule; supplies `radialKernel_compact_control`. -/
theorem radialKernel_coord_smooth (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀) :
    ContDiffOn ℝ ∞
      (fun pq : Coord F × Coord F => radialKernel F k₀ (ptX F pq.1) (ptX F pq.2))
      {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
  let S : Set (Coord F × Coord F) := {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F}
  have hheight := (G1_h3_basics (F := F)).1
  have hhoriz := (G1_h3_basics (F := F)).2.1
  have hppiCoord : ∀ w : InfinitePlace F,
      ContDiffOn ℝ ∞ (fun pq : Coord F × Coord F => ppiCoordAt F w pq) S := by
    exact (G6_ppi (F := F)).2.2.2.2
  have hkComplex : ContDiff ℝ ∞ (fun t : ℝ => (k₀ t : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hkSmooth
  have hfactor (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun pq : Coord F × Coord F => (k₀ (ppiCoordAt F w pq) : ℂ)) S := by
    exact hkComplex.comp_contDiffOn (hppiCoord w)
  have hprod : ContDiffOn ℝ ∞
      (fun pq : Coord F × Coord F =>
        ∏ w : InfinitePlace F, (k₀ (ppiCoordAt F w pq) : ℂ)) S := by
    classical
    simpa using (contDiffOn_prod
      (t := (Finset.univ : Finset (InfinitePlace F))) (fun w _ => hfactor w))
  apply hprod.congr
  intro pq hpq
  change (∏ w : InfinitePlace F,
      (k₀ (ppi (pt ((pq.1 w).1) ((pq.1 w).2))
        (pt ((pq.2 w).1) ((pq.2 w).2))) : ℂ)) =
      ∏ w : InfinitePlace F, (k₀ (ppiCoordAt F w pq) : ℂ)
  apply Finset.prod_congr rfl
  intro w _
  have hpoint :
      ppi (pt ((pq.1 w).1) ((pq.1 w).2)) (pt ((pq.2 w).1) ((pq.2 w).2)) =
        ppiCoordAt F w pq := by
    unfold ppi ppiCoordAt
    rw [hhoriz _ _ (hpq.1 w), hhoriz _ _ (hpq.2 w),
      hheight _ _ (hpq.1 w), hheight _ _ (hpq.2 w)]
  rw [hpoint]

end ArtinPrimitiveRoots.A1.Spec
