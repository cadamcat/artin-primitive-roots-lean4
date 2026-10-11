import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 5000000
open NumberField Matrix MeasureTheory Module Filter Topology
open scoped MatrixGroups ContDiff Classical ENNReal ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private noncomputable def rellichFiberEquiv :
    (ℂ × ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  (Complex.measurableEquivRealProd.prodCongr (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm))

private theorem rellichFiberEquiv_zero (q : ℂ × ℝ) :
    rellichFiberEquiv q 0 = q.1.re := by
  simp [rellichFiberEquiv, MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piFinTwo, piFinTwoEquiv, Fin.insertNth_apply_below]

private theorem rellichFiberEquiv_one (q : ℂ × ℝ) :
    rellichFiberEquiv q 1 = q.1.im := by
  simp [rellichFiberEquiv, MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piFinTwo, piFinTwoEquiv, Fin.insertNth_apply_below]

private theorem rellichFiberEquiv_two (q : ℂ × ℝ) :
    rellichFiberEquiv q 2 = q.2 := by
  simp [rellichFiberEquiv, MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piFinTwo, piFinTwoEquiv, Fin.insertNth_apply_same]

private theorem rellichFiber_measurePreserving :
    MeasurePreserving rellichFiberEquiv volume volume := by
  have h₁ : MeasurePreserving
      (Complex.measurableEquivRealProd.prodCongr (MeasurableEquiv.refl ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod ℂ ℝ, Measure.volume_eq_prod (ℝ × ℝ) ℝ]
    exact Complex.volume_preserving_equiv_real_prod.prod (MeasurePreserving.id _)
  have h₂ : MeasurePreserving (MeasurableEquiv.prodComm :
      ((ℝ × ℝ) × ℝ) ≃ᵐ ℝ × (ℝ × ℝ)) volume volume := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ, Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact MeasureTheory.Measure.measurePreserving_swap
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm)
      volume volume := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
    exact (MeasurePreserving.id volume).prod
      (MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  have h₄ : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      volume volume := by
    rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
    exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  exact h₄.comp (h₃.comp (h₂.comp h₁))

private def rellichCoordToNestedEquiv :
    Coord F ≃ᵐ (InfinitePlace F → Fin 3 → ℝ) where
  toEquiv :=
    { toFun := fun q w => rellichFiberEquiv (q w)
      invFun := fun p w => rellichFiberEquiv.symm (p w)
      left_inv := by intro q; funext w; exact rellichFiberEquiv.left_inv (q w)
      right_inv := by intro p; funext w; exact rellichFiberEquiv.right_inv (p w) }
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro w
    exact rellichFiberEquiv.measurable.comp (measurable_pi_apply w)
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro w
    exact rellichFiberEquiv.symm.measurable.comp (measurable_pi_apply w)

private theorem rellichCoordToNested_measurePreserving :
    MeasurePreserving (rellichCoordToNestedEquiv (F := F)) volume volume := by
  have h : MeasurePreserving
      (fun q : Coord F => fun w : InfinitePlace F => rellichFiberEquiv (q w)) volume volume :=
    MeasureTheory.volume_preserving_pi (fun _ : InfinitePlace F => rellichFiber_measurePreserving)
  change MeasurePreserving (fun q : Coord F => fun w : InfinitePlace F =>
    rellichFiberEquiv (q w)) volume volume
  exact h

private def rellichProductCurry :
    (InfinitePlace F × Fin 3 → ℝ) ≃ᵐ (InfinitePlace F → Fin 3 → ℝ) where
  toEquiv :=
    { toFun := fun f w j => f (w, j)
      invFun := fun f ij => f ij.1 ij.2
      left_inv := by intro f; funext ij; cases ij; rfl
      right_inv := by intro f; funext w j; rfl }
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro w
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (w, j)
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro ij
    exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)

private theorem rellichMeasurableSpace_eq :
    RellichChart.rellichMeasurableSpace (ι := InfinitePlace F × Fin 3) =
      WithLp.measurableSpace 2 (InfinitePlace F × Fin 3 → ℝ) := by
  have h₁ : RellichChart.rellichMeasurableSpace
      (ι := InfinitePlace F × Fin 3) =
      borel (EuclideanSpace ℝ (InfinitePlace F × Fin 3)) := rfl
  letI : MeasurableSpace (WithLp 2 (InfinitePlace F × Fin 3 → ℝ)) :=
    WithLp.measurableSpace 2 (InfinitePlace F × Fin 3 → ℝ)
  have h₂ : WithLp.measurableSpace 2 (InfinitePlace F × Fin 3 → ℝ) =
      borel (WithLp 2 (InfinitePlace F × Fin 3 → ℝ)) := by
    letI : BorelSpace (WithLp 2 (InfinitePlace F × Fin 3 → ℝ)) :=
      PiLp.borelSpace (p := 2) (X := fun _ : InfinitePlace F × Fin 3 => ℝ)
    exact BorelSpace.measurable_eq
  exact h₁.trans h₂.symm

private noncomputable def rellichToLpMeasurableEquiv :
    (InfinitePlace F × Fin 3 → ℝ) ≃ᵐ RellichCoord F := by
  refine ⟨(WithLp.equiv 2 (InfinitePlace F × Fin 3 → ℝ)).symm, ?_, ?_⟩
  · exact (PiLp.continuous_toLp 2 (fun _ : InfinitePlace F × Fin 3 => ℝ)).measurable
  · exact (PiLp.continuous_ofLp 2 (fun _ : InfinitePlace F × Fin 3 => ℝ)).measurable

private theorem rellichPiCurry_symm_measurePreserving :
    MeasurePreserving (rellichProductCurry (F := F)).symm volume volume := by
  have hpi : Measure.pi (fun _ : (InfinitePlace F × Fin 3) => (volume : Measure ℝ)) =
      Measure.map (rellichProductCurry (F := F)).symm
        (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (Fin 3 → ℝ)))) := by
    apply Measure.pi_eq
    intro s hs
    rw [MeasurableEquiv.map_apply]
    have hpre : (rellichProductCurry (F := F)).symm ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun w : InfinitePlace F =>
          Set.pi Set.univ (fun j : Fin 3 => s (w, j))) := by
      ext x
      simp [rellichProductCurry, Set.mem_pi]
    rw [hpre]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  constructor
  · exact (rellichProductCurry (F := F)).symm.measurable
  · simpa only [volume_pi] using hpi.symm

private theorem rellichToLp_measurePreserving :
    MeasurePreserving (rellichToLpMeasurableEquiv (F := F)) volume volume := by
  have hvol : (volume : Measure (RellichCoord F)) =
      Measure.map (@WithLp.toLp 2 (InfinitePlace F × Fin 3 → ℝ))
        (volume : Measure (InfinitePlace F × Fin 3 → ℝ)) := by
    rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun,
      ← Basis.addHaar_def, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ,
      Basis.map_addHaar]
    exact (EuclideanSpace.basisFun _ _).addHaar_eq_volume.symm
  exact ⟨(rellichToLpMeasurableEquiv (F := F)).measurable, hvol.symm⟩

private noncomputable def rellichCoordEquiv : Coord F ≃ᵐ RellichCoord F :=
  (rellichCoordToNestedEquiv (F := F)).trans
    ((rellichProductCurry (F := F)).symm.trans
      (rellichToLpMeasurableEquiv (F := F)))

private theorem rellichCoord_measurePreserving :
    MeasurePreserving (rellichCoordEquiv (F := F)) volume volume := by
  exact (rellichToLp_measurePreserving (F := F)).comp
    ((rellichPiCurry_symm_measurePreserving (F := F)).comp
    (rellichCoordToNested_measurePreserving (F := F)))

private def rellichFromCoord (q : Coord F) : RellichCoord F :=
  WithLp.toLp 2 fun wj : InfinitePlace F × Fin 3 =>
    match wj.2 with
    | 0 => (q wj.1).1.re
    | 1 => (q wj.1).1.im
    | 2 => (q wj.1).2

private theorem rellichFromCoord_continuous :
    Continuous (rellichFromCoord (F := F)) := by
  have hpi : Continuous (fun q : Coord F => fun wj : InfinitePlace F × Fin 3 =>
      match wj.2 with
      | 0 => (q wj.1).1.re
      | 1 => (q wj.1).1.im
      | 2 => (q wj.1).2) := by
    apply continuous_pi
    intro wj
    rcases wj with ⟨w, j⟩
    fin_cases j <;> fun_prop
  change Continuous (fun q : Coord F => WithLp.toLp 2 fun wj : InfinitePlace F × Fin 3 =>
    match wj.2 with
    | 0 => (q wj.1).1.re
    | 1 => (q wj.1).1.im
    | 2 => (q wj.1).2)
  exact (PiLp.continuous_toLp 2 (fun _ : InfinitePlace F × Fin 3 => ℝ)).comp hpi

private theorem rellichCoordEquiv_apply (q : Coord F) :
    rellichCoordEquiv (F := F) q = rellichFromCoord (F := F) q := by
  ext wj
  rcases wj with ⟨w, j⟩
  fin_cases j
  · simpa [rellichCoordEquiv, rellichCoordToNestedEquiv, rellichProductCurry,
      rellichFromCoord, rellichToLpMeasurableEquiv, WithLp.equiv] using
      rellichFiberEquiv_zero (q w)
  · simpa [rellichCoordEquiv, rellichCoordToNestedEquiv, rellichProductCurry,
      rellichFromCoord, rellichToLpMeasurableEquiv, WithLp.equiv] using
      rellichFiberEquiv_one (q w)
  · simpa [rellichCoordEquiv, rellichCoordToNestedEquiv, rellichProductCurry,
      rellichFromCoord, rellichToLpMeasurableEquiv, WithLp.equiv] using
      rellichFiberEquiv_two (q w)

private theorem rellichFromCoord_toCoord (p : RellichCoord F) :
    rellichFromCoord (F := F) (rellichToCoord F p) = p := by
  ext wj
  rcases wj with ⟨w, j⟩
  fin_cases j <;> simp [rellichFromCoord, rellichToCoord]

private theorem rellichToCoord_fromCoord (q : Coord F) (hq : q ∈ posSet F) :
    rellichToCoord F (rellichFromCoord (F := F) q) = q := by
  funext w
  apply Prod.ext
  · apply Complex.ext <;> simp [rellichFromCoord, rellichToCoord]
  · simp [rellichFromCoord, rellichToCoord]

private theorem rellichFromCoord_mem_posSet (q : Coord F) (hq : q ∈ posSet F) :
    rellichFromCoord (F := F) q ∈ rellichPosSet F := by
  change ∀ w, 0 < (rellichFromCoord (F := F) q) (w, 2)
  intro w
  simpa [rellichFromCoord] using hq w

private theorem rellichCoordEquiv_pos_iff (q : Coord F) :
    rellichCoordEquiv (F := F) q ∈ rellichPosSet F ↔ q ∈ posSet F := by
  rw [rellichCoordEquiv_apply]
  constructor
  · intro hp
    change ∀ w, 0 < (q w).2
    intro w
    simpa [rellichFromCoord] using hp w
  · exact rellichFromCoord_mem_posSet (F := F) q

private theorem rellich_chart_integral_eq
    (hvol : ∀ g : X F → ℝ, Integrable g (volX F) →
      ∫ z, g z ∂(volX F) =
        ∫ q, g (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹))
          ∂(volume.restrict (posSet F)))
    (gX : X F → ℝ) (gP : RellichCoord F → ℝ)
    (hpoint : ∀ q, q ∈ posSet F →
      gX (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
        gP (rellichFromCoord (F := F) q))
    (hsupp : Function.support gP ⊆ rellichPosSet F)
    (hintX : Integrable gX (volX F))
    (hintP : Integrable gP (volume : Measure (RellichCoord F))) :
    ∫ p, gP p ∂(volume : Measure (RellichCoord F)) = ∫ z, gX z ∂(volX F) := by
  have hInd : (rellichPosSet F).indicator gP = gP := by
    funext p
    by_cases hp : p ∈ rellichPosSet F
    · simp [hp]
    · have hp0 : gP p = 0 := by
        by_contra hne
        exact hp (hsupp hne)
      simp [hp, hp0]
  have hCoord :
      (fun q => (posSet F).indicator
        (fun q => gX (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹))) q) =
      (fun q => (rellichPosSet F).indicator gP (rellichCoordEquiv (F := F) q)) := by
    funext q
    by_cases hq : q ∈ posSet F
    · have hp : rellichCoordEquiv (F := F) q ∈ rellichPosSet F :=
        (rellichCoordEquiv_pos_iff (F := F) q).2 hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hp,
        rellichCoordEquiv_apply]
      exact hpoint q hq
    · have hp : rellichCoordEquiv (F := F) q ∉ rellichPosSet F := by
        intro hp
        exact hq ((rellichCoordEquiv_pos_iff (F := F) q).1 hp)
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hp]
  have hG3 := hvol gX hintX
  have hPosOpen : IsOpen (posSet F) := by
    rw [show posSet F = ⋂ w : InfinitePlace F,
        {q : Coord F | 0 < (q w).2} by
      ext q
      simp [posSet]]
    exact isOpen_iInter_of_finite fun w => by
      have hcoord : Continuous (fun q : Coord F => (q w).2) := by fun_prop
      exact isOpen_Ioi.preimage hcoord
  calc
    ∫ p, gP p ∂(volume : Measure (RellichCoord F)) =
        ∫ p, (rellichPosSet F).indicator gP p ∂(volume : Measure (RellichCoord F)) := by
      rw [hInd]
    _ = ∫ q, (rellichPosSet F).indicator gP (rellichCoordEquiv (F := F) q)
          ∂(volume : Measure (Coord F)) :=
      (rellichCoord_measurePreserving (F := F)).integral_comp' _ |>.symm
    _ = ∫ q, (posSet F).indicator
          (fun q => gX (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹))) q
          ∂(volume : Measure (Coord F)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => (congrFun hCoord q).symm)
    _ = ∫ q, gX (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹))
          ∂(volume.restrict (posSet F)) := by
      rw [← integral_indicator hPosOpen.measurableSet]
    _ = ∫ z, gX z ∂(volX F) := hG3.symm

private theorem rellichPosSet_isOpen : IsOpen (rellichPosSet F) := by
  rw [show rellichPosSet F = ⋂ w : InfinitePlace F,
      {p : RellichCoord F | 0 < p (w, 2)} by
    ext p
    simp [rellichPosSet]]
  exact isOpen_iInter_of_finite fun w => by
    have hcoord : Continuous (fun p : RellichCoord F => p (w, 2)) := by fun_prop
    exact isOpen_Ioi.preimage hcoord

private theorem rellichCoordPosSet_isOpen : IsOpen (posSet F) := by
  rw [show posSet F = ⋂ w : InfinitePlace F,
      {q : Coord F | 0 < (q w).2} by
    ext q
    simp [posSet]]
  exact isOpen_iInter_of_finite fun w => by
    have hcoord : Continuous (fun q : Coord F => (q w).2) := by fun_prop
    exact isOpen_Ioi.preimage hcoord

private theorem rellichLocalized_component_value
    (ψ : X F → ℝ) (f : X F → ℂ) (T : ℂ →L[ℝ] ℝ)
    (q : Coord F) (hq : q ∈ posSet F) :
    T (rellichLocalized F ψ f (rellichFromCoord (F := F) q)) =
      ψ (ptX F q) * T (f (ptX F q)) := by
  have hp := rellichFromCoord_mem_posSet (F := F) q hq
  rw [rellichLocalized, if_pos hp, rellichToCoord_fromCoord (F := F) q hq]
  calc
    T ((ψ (ptX F q) : ℂ) * f (ptX F q)) =
        T ((ψ (ptX F q) : ℝ) • f (ptX F q)) := by
      congr 1
    _ = (ψ (ptX F q) : ℝ) • T (f (ptX F q)) := map_smul T _ _
    _ = ψ (ptX F q) * T (f (ptX F q)) := rfl

private theorem rellichLocalized_component_on_pos
    (ψ : X F → ℝ) (f : X F → ℂ) (T : ℂ →L[ℝ] ℝ)
    (p : RellichCoord F) (hp : p ∈ rellichPosSet F) :
    T (rellichLocalized F ψ f p) =
      ψ (ptX F (rellichToCoord F p)) * T (f (ptX F (rellichToCoord F p))) := by
  rw [rellichLocalized, if_pos hp]
  calc
    T ((ψ (ptX F (rellichToCoord F p) : X F) : ℂ) *
        f (ptX F (rellichToCoord F p))) =
        T ((ψ (ptX F (rellichToCoord F p)) : ℝ) •
          f (ptX F (rellichToCoord F p))) := by
      congr 1
    _ = (ψ (ptX F (rellichToCoord F p)) : ℝ) •
        T (f (ptX F (rellichToCoord F p))) := map_smul T _ _
    _ = ψ (ptX F (rellichToCoord F p)) * T (f (ptX F (rellichToCoord F p))) := rfl

private theorem rellichLocalized_component_support_subset
    (ψ : X F → ℝ) (f : X F → ℂ) (T : ℂ →L[ℝ] ℝ)
    (K : Set (X F)) (hψK : ∀ z, ψ z ≠ 0 → z ∈ K)
    (hcoordPt : ∀ q, q ∈ posSet F → coordsX F (ptX F q) = q) :
    Function.support (fun p => T (rellichLocalized F ψ f p)) ⊆
      rellichFromCoord (F := F) '' (coordsX F '' K) := by
  intro p hp
  change T (rellichLocalized F ψ f p) ≠ 0 at hp
  by_cases hpos : p ∈ rellichPosSet F
  · let z := ptX F (rellichToCoord F p)
    have hψnz : ψ z ≠ 0 := by
      by_contra hz
      apply hp
      simp [z, rellichLocalized, hpos, hz]
    have hzK : z ∈ K := hψK z hψnz
    have hqpos : rellichToCoord F p ∈ posSet F := by
      change ∀ w, 0 < (rellichToCoord F p w).2
      intro w
      simpa [rellichToCoord] using hpos w
    have hcoords : coordsX F z = rellichToCoord F p := hcoordPt _ hqpos
    refine ⟨coordsX F z, ⟨z, hzK, rfl⟩, ?_⟩
    rw [hcoords]
    exact rellichFromCoord_toCoord (F := F) p
  · have hz : rellichLocalized F ψ f p = 0 := by
      simp [rellichLocalized, hpos]
    simp [hz] at hp

private theorem rellichLp_norm_eq_sqrt_integral
    {α G : Type*} [MeasureSpace α] [NormedAddCommGroup G]
    (u : Lp G 2 (volume : Measure α)) :
    ‖u‖ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂(volume : Measure α)) := by
  calc
    ‖u‖ = lpNorm (u : α → G) 2 (volume : Measure α) := by
      rw [Lp.norm_def, toReal_eLpNorm]
    _ = (∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure α)) ^ (2 : ℝ)⁻¹ :=
      lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) (Lp.aestronglyMeasurable u)
    _ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂(volume : Measure α)) := by
      norm_num [Real.sqrt_eq_rpow]

private theorem rellichComplexEuclidean_norm_apply_le
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  have hsq : ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun j hj => sq_nonneg ‖x j‖) (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem rellichEuclidean_grad_apply
    (u : RellichCoord F → ℝ) (p : RellichCoord F) (i : InfinitePlace F × Fin 3) :
    RellichEuclidean.grad u p i =
      fderiv ℝ u p (EuclideanSpace.single i (1 : ℝ)) := by
  change ((InnerProductSpace.toDual ℝ (RellichCoord F)).symm (fderiv ℝ u p)) i = _
  have h := InnerProductSpace.toDual_symm_apply
      (x := EuclideanSpace.single i (1 : ℝ))
      (y := fderiv ℝ u p)
  rw [EuclideanSpace.inner_single_right] at h
  simpa using h

private theorem rellichNormHeight_ptX
    (hcoordPt : ∀ q, q ∈ posSet F → coordsX F (ptX F q) = q)
    (q : Coord F) (hq : q ∈ posSet F) :
    normHeight F (ptX F q) = ∏ w, (q w).2 := by
  change ∏ w, (coordsX F (ptX F q) w).2 = _
  rw [hcoordPt q hq]

private theorem rellichDensity_cancel (q : Coord F) (hq : q ∈ posSet F) :
    (∏ w, (q w).2) ^ 3 * ∏ w, (((q w).2 ^ 3)⁻¹) = 1 := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  simp [ne_of_gt (hq _)]

private theorem rellichEuclidean_grad_support_subset
    (u : RellichCoord F → ℝ) (K : Set (RellichCoord F)) (hK : IsCompact K)
    (hu : Function.support u ⊆ K) :
    Function.support (fun p => RellichEuclidean.grad u p) ⊆ K := by
  intro p hp
  by_contra hpK
  have hts : tsupport u ⊆ K := closure_minimal hu hK.isClosed
  have hpt : p ∉ tsupport u := fun h => hpK (hts h)
  have hzero : u =ᶠ[𝓝 p] 0 :=
    (notMem_tsupport_iff_eventuallyEq (f := u) (x := p)).1 hpt
  have hfd : fderiv ℝ u p = 0 := by
    rw [hzero.fderiv_eq]
    simp
  have hgrad : RellichEuclidean.grad u p = 0 := by
    ext i
    rw [rellichEuclidean_grad_apply, hfd]
    simp
  exact hpK (by simpa [hgrad] using hp)

private theorem rellich_fullGradient_continuous
    (hcoordsXCont : Continuous (coordsX F))
    (hcoordPos : ∀ z : X F, coordsX F z ∈ posSet F)
    (hPosOpen : IsOpen (posSet F)) (f : X F → ℂ) (hf : IsSmoothX F f) :
    Continuous (fullGradient F f) := by
  have hdf : ContinuousOn (fderiv ℝ (fun q => f (ptX F q))) (posSet F) :=
    hf.continuousOn_fderiv_of_isOpen hPosOpen (by simp)
  have hdfGlob : Continuous (fun z : X F =>
      fderiv ℝ (fun q => f (ptX F q)) (coordsX F z)) := by
    apply continuousOn_univ.mp
    exact hdf.comp hcoordsXCont.continuousOn (fun z _ => hcoordPos z)
  have hpi : Continuous (fun z : X F => fun wj : InfinitePlace F × Fin 3 =>
      placeGradient F wj.1 f z wj.2) := by
    apply continuous_pi
    intro wj
    rcases wj with ⟨w, j⟩
    change Continuous (fun z : X F =>
      ((coordsX F z w).2 : ℂ) *
        fderiv ℝ (fun q => f (ptX F q)) (coordsX F z) (placeDirection F w j))
    have hy : Continuous (fun z : X F => ((coordsX F z w).2 : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        (continuous_snd.comp ((continuous_apply w).comp hcoordsXCont))
    have hd : Continuous (fun z : X F =>
        fderiv ℝ (fun q => f (ptX F q)) (coordsX F z) (placeDirection F w j)) := by
      exact (ContinuousLinearMap.evalL ℝ (Coord F) ℂ (placeDirection F w j)).continuous.comp
        hdfGlob
    exact hy.mul hd
  change Continuous (fun z : X F => WithLp.toLp 2
    (fun wj : InfinitePlace F × Fin 3 => placeGradient F wj.1 f z wj.2))
  exact (PiLp.continuous_toLp 2 (fun _ : InfinitePlace F × Fin 3 => ℂ)).comp hpi

private theorem rellichPlaceDirection_norm (w : InfinitePlace F) (j : Fin 3) :
    ‖placeDirection F w j‖ = 1 := by
  fin_cases j
  · change ‖(Pi.single w ((1 : ℂ), (0 : ℝ)) : Coord F)‖ = 1
    rw [Pi.norm_single]
    simp [Prod.norm_def]
  · change ‖(Pi.single w (Complex.I, (0 : ℝ)) : Coord F)‖ = 1
    rw [Pi.norm_single]
    simp [Prod.norm_def]
  · change ‖(Pi.single w ((0 : ℂ), (1 : ℝ)) : Coord F)‖ = 1
    rw [Pi.norm_single]
    simp [Prod.norm_def]

private noncomputable def rellichCoordToCoordLinear :
    RellichCoord F →L[ℝ] Coord F where
  toFun := rellichToCoord F
  map_add' := by
    intro p q
    funext w
    apply Prod.ext
    · apply Complex.ext <;> simp [rellichToCoord]
    · simp [rellichToCoord]
  map_smul' := by
    intro a p
    funext w
    apply Prod.ext
    · apply Complex.ext <;> simp [rellichToCoord, smul_eq_mul]
    · simp [rellichToCoord, smul_eq_mul]
  cont := by
    apply continuous_pi
    intro w
    let e0 : RellichCoord F →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : InfinitePlace F × Fin 3 => ℝ) (w, 0)
    let e1 : RellichCoord F →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : InfinitePlace F × Fin 3 => ℝ) (w, 1)
    let e2 : RellichCoord F →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : InfinitePlace F × Fin 3 => ℝ) (w, 2)
    have h0 : Continuous (fun p : RellichCoord F => (p (w, 0) : ℂ)) := by
      change Continuous (fun p => Complex.ofRealCLM (e0 p))
      exact Complex.continuous_ofReal.comp e0.continuous
    have h1 : Continuous (fun p : RellichCoord F => (p (w, 1) : ℂ)) := by
      change Continuous (fun p => Complex.ofRealCLM (e1 p))
      exact Complex.continuous_ofReal.comp e1.continuous
    have h2 : Continuous (fun p : RellichCoord F => p (w, 2)) := by
      change Continuous e2
      exact e2.continuous
    exact (h0.add (continuous_const.mul h1)).prodMk h2

private theorem rellichLocalized_component_contDiffOn
    (ψ : X F → ℝ) (f : X F → ℂ) (T : ℂ →L[ℝ] ℝ)
    (hψsmooth : IsSmoothRealX F ψ) (hfsmooth : IsSmoothX F f) :
    ContDiffOn ℝ ∞ (fun p => T (rellichLocalized F ψ f p)) (rellichPosSet F) := by
  let L := rellichCoordToCoordLinear (F := F)
  let ψc : Coord F → ℂ := fun q => (ψ (ptX F q) : ℂ)
  let fc : Coord F → ℂ := fun q => f (ptX F q)
  let ψp : RellichCoord F → ℂ := ψc ∘ L
  let fp : RellichCoord F → ℂ := fc ∘ L
  have hMaps : Set.MapsTo (rellichToCoord F) (rellichPosSet F) (posSet F) := by
    intro p hp
    change ∀ w, 0 < (rellichToCoord F p w).2
    intro w
    simpa [rellichToCoord] using hp w
  have hLcd : ContDiff ℝ ∞ (rellichToCoord F) := by
    change ContDiff ℝ ∞ (fun p => (L p : Coord F))
    exact L.contDiff
  have hψc : ContDiffOn ℝ ∞ ψc (posSet F) := by
    change ContDiffOn ℝ ∞ (Complex.ofRealCLM ∘ fun q => ψ (ptX F q)) (posSet F)
    exact Complex.ofRealCLM.contDiff.contDiffOn.comp hψsmooth (fun _ _ => Set.mem_univ _)
  have hfcoord : ContDiffOn ℝ ∞ fc (posSet F) := hfsmooth
  have hψp' : ContDiffOn ℝ ∞ ψp (rellichPosSet F) := by
    exact hψc.comp hLcd.contDiffOn hMaps
  have hfp' : ContDiffOn ℝ ∞ fp (rellichPosSet F) := by
    exact hfcoord.comp hLcd.contDiffOn hMaps
  have hprod : ContDiffOn ℝ ∞ (fun p => T (ψp p * fp p)) (rellichPosSet F) :=
    T.contDiff.contDiffOn.comp (hψp'.mul hfp') (fun _ _ => Set.mem_univ _)
  have hEqOn : Set.EqOn (fun p => T (rellichLocalized F ψ f p))
      (fun p => T (ψp p * fp p)) (rellichPosSet F) := by
    intro p hp
    change T (rellichLocalized F ψ f p) = T (ψp p * fp p)
    rw [rellichLocalized_component_on_pos ψ f T p hp]
    symm
    calc
      T ((ψ (ptX F (rellichToCoord F p)) : ℂ) *
          f (ptX F (rellichToCoord F p))) =
          T ((ψ (ptX F (rellichToCoord F p)) : ℝ) •
            f (ptX F (rellichToCoord F p))) := by congr 1 <;> simp
      _ = (ψ (ptX F (rellichToCoord F p)) : ℝ) •
          T (f (ptX F (rellichToCoord F p))) := map_smul T _ _
      _ = ψ (ptX F (rellichToCoord F p)) *
          T (f (ptX F (rellichToCoord F p))) := rfl
  exact hprod.congr hEqOn

private theorem rellichCoordToCoordLinear_single (w : InfinitePlace F) (j : Fin 3) :
    rellichCoordToCoordLinear (F := F) (EuclideanSpace.single (w, j) (1 : ℝ)) =
      placeDirection F w j := by
  fin_cases j
  · funext v
    apply Prod.ext
    · apply Complex.ext
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
    · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
        placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
  · funext v
    apply Prod.ext
    · apply Complex.ext
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
    · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
        placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
  · funext v
    apply Prod.ext
    · apply Complex.ext
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
      · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
          placeDirection, EuclideanSpace.single, Pi.single] <;> aesop
    · by_cases hv : v = w <;> simp [hv, eq_comm, rellichCoordToCoordLinear, rellichToCoord,
        placeDirection, EuclideanSpace.single, Pi.single] <;> aesop

private theorem rellichLocalized_component_fderiv
    (ψ : X F → ℝ) (f : X F → ℂ) (T : ℂ →L[ℝ] ℝ)
    (hPosOpen : IsOpen (posSet F)) (hRellichPosOpen : IsOpen (rellichPosSet F))
    (hψsmooth : IsSmoothRealX F ψ)
    (hfsmooth : IsSmoothX F f)
    (p : RellichCoord F) (hp : p ∈ rellichPosSet F)
    (w : InfinitePlace F) (j : Fin 3) :
    fderiv ℝ (fun x => T (rellichLocalized F ψ f x)) p
        (EuclideanSpace.single (w, j) (1 : ℝ)) =
      fderiv ℝ (fun q => ψ (ptX F q)) (rellichToCoord F p)
          (placeDirection F w j) * T (f (ptX F (rellichToCoord F p))) +
      ψ (ptX F (rellichToCoord F p)) *
        T (fderiv ℝ (fun q => f (ptX F q)) (rellichToCoord F p)
          (placeDirection F w j)) := by
  let L := rellichCoordToCoordLinear (F := F)
  let ψc : Coord F → ℝ := fun q => ψ (ptX F q)
  let fc : Coord F → ℂ := fun q => f (ptX F q)
  let A : RellichCoord F → ℝ := ψc ∘ L
  let B : RellichCoord F → ℝ := fun x => T (fc (L x))
  let U : RellichCoord F → ℝ := fun x => T (rellichLocalized F ψ f x)
  have hq : rellichToCoord F p ∈ posSet F := by
    change ∀ v, 0 < (rellichToCoord F p v).2
    intro v
    simpa [rellichToCoord] using hp v
  have hψD : DifferentiableAt ℝ ψc (rellichToCoord F p) :=
    (hψsmooth.contDiffAt (hPosOpen.mem_nhds hq)).differentiableAt (by simp)
  have hfD : DifferentiableAt ℝ fc (rellichToCoord F p) :=
    (hfsmooth.contDiffAt (hPosOpen.mem_nhds hq)).differentiableAt (by simp)
  have hLD : DifferentiableAt ℝ L p := L.differentiableAt
  have hTD : DifferentiableAt ℝ (fun q => T (fc q)) (rellichToCoord F p) :=
    T.differentiableAt.comp _ hfD
  have hAD : DifferentiableAt ℝ A p := hψD.comp _ hLD
  have hBD : DifferentiableAt ℝ B p := hTD.comp _ hLD
  have hEqOn : Set.EqOn U (A * B) (rellichPosSet F) := by
    intro x hx
    change T (rellichLocalized F ψ f x) =
      ψ (ptX F (rellichToCoord F x)) * T (f (ptX F (rellichToCoord F x)))
    simp only [rellichLocalized, if_pos hx]
    change T ((ψ (ptX F (rellichToCoord F x)) : ℂ) *
        f (ptX F (rellichToCoord F x))) =
      ψ (ptX F (rellichToCoord F x)) *
        T (f (ptX F (rellichToCoord F x)))
    let a := ψ (ptX F (rellichToCoord F x))
    let z := f (ptX F (rellichToCoord F x))
    calc
      T ((a : ℂ) * z) = T ((a : ℝ) • z) := by
        congr 1
      _ = (a : ℝ) • T z := map_smul T a z
      _ = a * T z := rfl
  have hEq : U =ᶠ[𝓝 p] A * B := by
    filter_upwards [hRellichPosOpen.mem_nhds hp] with x hx
    exact hEqOn hx
  have hLvalue : L p = rellichToCoord F p := rfl
  have hLderiv : fderiv ℝ (⇑L) p = L := L.hasFDerivAt.fderiv
  have hAderiv (v : RellichCoord F) :
      fderiv ℝ A p v = fderiv ℝ ψc (rellichToCoord F p) (L v) := by
    rw [show A = ψc ∘ L by rfl,
      fderiv_comp (f := L) (g := ψc) p hψD hLD]
    rw [ContinuousLinearMap.comp_apply, hLderiv, hLvalue]
  have hTfcDeriv : ∀ v : Coord F,
      fderiv ℝ (fun q => T (fc q)) (rellichToCoord F p) v =
        T (fderiv ℝ fc (rellichToCoord F p) v) := by
    intro v
    rw [show (fun q => T (fc q)) = T ∘ fc by rfl,
      fderiv_comp (f := fc) (g := T) (rellichToCoord F p) T.differentiableAt hfD]
    rw [ContinuousLinearMap.comp_apply,
      T.hasFDerivAt.fderiv]
  have hBderiv (v : RellichCoord F) :
      fderiv ℝ B p v = T (fderiv ℝ fc (rellichToCoord F p) (L v)) := by
    rw [show B = (fun q => T (fc q)) ∘ L by rfl,
      fderiv_comp (f := L) (g := fun q => T (fc q)) p hTD hLD]
    rw [ContinuousLinearMap.comp_apply, hLderiv, hLvalue, hTfcDeriv]
  have hprod := fderiv_mul hAD hBD
  rw [hEq.fderiv_eq, hprod]
  have hdir := rellichCoordToCoordLinear_single (F := F) w j
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [hAderiv, hBderiv, hdir]
  simp [A, B, ψc, fc, L, rellichCoordToCoordLinear, hLvalue]
  ring

/-- Uniform H¹ estimates for a calibrated real/imaginary cutoff test localization.
Uses the local-energy bound from
quotient_to_chart_finite_overlap, compact bounds on heights/density/cutoff derivatives,
and the mass and gradient representatives of localized_chart_H1_membership. -/
theorem localized_chart_H1_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hlocal : RellichLocalEnergyBound Γ D E e)
    (ψ : X F → ℝ) (hψsmooth : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (c : RellichTestChart Γ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : testSubmodule F Γ,
      ‖c.re f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ∧
      ‖c.im f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := by
  classical
  have hG3 := G3_volume (F := F)
  letI : IsFiniteMeasureOnCompacts (volX F) := ⟨fun K hK => hG3.2.2.1 K hK⟩
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoordPt, hptXcoords, _, _, _, ⟨chartEquiv, _, hcoordsX⟩⟩
  haveI : BorelSpace H3 := ⟨rfl⟩
  haveI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := inferInstance
  have hCountMatrix2 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := hCountMatrix2
  have hCountSL2C : SecondCountableTopology (SL(2,ℂ)) := by
    apply (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ))).secondCountableTopology
  haveI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
  letI : ContinuousMul (SL(2,ℂ)) := ⟨by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)⟩
  have hCountH3 : SecondCountableTopology H3 := by
    letI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
    exact Topology.IsOpenQuotientMap.secondCountableTopology
      (QuotientGroup.isOpenQuotientMap_mk (N := SU2))
  haveI : SecondCountableTopology H3 := hCountH3
  haveI : OpensMeasurableSpace H3 := inferInstance
  haveI : Finite (InfinitePlace F) := Fintype.finite (inferInstance : Fintype (InfinitePlace F))
  haveI : Countable (InfinitePlace F) := inferInstance
  have hOpenX : OpensMeasurableSpace (X F) := Pi.opensMeasurableSpace
  haveI : OpensMeasurableSpace (X F) := hOpenX
  have hT2X : T2Space (X F) := chartEquiv.t2Space
  haveI : T2Space (X F) := hT2X
  obtain ⟨K, hK, hψKcomplex⟩ := hψcompact
  have hKclosed : IsClosed K :=
    @IsCompact.isClosed (X F) inferInstance hT2X K hK
  have hKmeas : MeasurableSet K := by
    simpa using hKclosed.isOpen_compl.measurableSet.compl
  have hψK : ∀ z, ψ z ≠ 0 → z ∈ K := by
    intro z hz
    apply hψKcomplex
    simpa using hz
  have hcoordsXCont : Continuous (coordsX F) := by
    have heq : (fun z : X F => coordsX F z) = fun z => (chartEquiv.symm z).1 := by
      funext z
      exact (hcoordsX z).symm
    change Continuous (fun z : X F => coordsX F z)
    rw [heq]
    exact continuous_subtype_val.comp chartEquiv.symm.continuous
  have hcoordPos : ∀ z : X F, coordsX F z ∈ posSet F := by
    intro z
    change ∀ w, 0 < height (z w)
    intro w
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hCoordPosOpen := rellichCoordPosSet_isOpen (F := F)
  have hRellichPosOpen := rellichPosSet_isOpen (F := F)
  let coordK : Set (Coord F) := coordsX F '' K
  have hCoordK : IsCompact coordK := by
    dsimp [coordK]
    exact hK.image hcoordsXCont
  have hCoordKPos : coordK ⊆ posSet F := by
    rintro q ⟨z, hz, rfl⟩
    exact hcoordPos z
  let ψcoord : Coord F → ℝ := fun q => ψ (ptX F q)
  have hψcoord : ContinuousOn ψcoord (posSet F) := hψsmooth.continuousOn
  obtain ⟨Cψ, hCψ⟩ := hCoordK.exists_bound_of_continuousOn (hψcoord.mono hCoordKPos)
  let Bψ : ℝ := max Cψ 0
  have hBψ : 0 ≤ Bψ := le_max_right _ _
  have hψcoordBound (q : Coord F) (hq : q ∈ coordK) : |ψcoord q| ≤ Bψ := by
    have hn := hCψ q hq
    have hn' : |ψcoord q| ≤ Cψ := by simpa [Real.norm_eq_abs] using hn
    exact hn'.trans (le_max_left _ _)
  have hψfderivCont : ContinuousOn
      (fderiv ℝ ψcoord) (posSet F) :=
    hψsmooth.continuousOn_fderiv_of_isOpen hCoordPosOpen (by simp)
  obtain ⟨Cψd, hCψd⟩ := hCoordK.exists_bound_of_continuousOn
    (hψfderivCont.norm.mono hCoordKPos)
  let Bψd : ℝ := max Cψd 0
  have hBψd : 0 ≤ Bψd := le_max_right _ _
  have hψfderivBound (q : Coord F) (hq : q ∈ coordK) :
      ‖fderiv ℝ ψcoord q‖ ≤ Bψd := by
    calc
      _ = ‖‖fderiv ℝ ψcoord q‖‖ := by rw [Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ Cψd := hCψd q hq
      _ ≤ Bψd := le_max_left _ _
  let invHeightSum : Coord F → ℝ := fun q => ∑ w, ((q w).2)⁻¹
  have hinvHeightSumCont : ContinuousOn invHeightSum (posSet F) := by
    dsimp [invHeightSum]
    apply continuousOn_finsetSum
    intro w hw
    have hy : Continuous (fun q : Coord F => (q w).2) :=
      continuous_snd.comp (continuous_apply w)
    exact hy.continuousOn.inv₀ (fun q hq => ne_of_gt (hq w))
  obtain ⟨Cinv, hCinv⟩ := hCoordK.exists_bound_of_continuousOn
    (hinvHeightSumCont.mono hCoordKPos)
  let Binv : ℝ := max Cinv 1
  have hBinv : 0 < Binv := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hinvHeightSumBound (q : Coord F) (hq : q ∈ coordK) :
      invHeightSum q ≤ Binv := by
    have hqpos := hCoordKPos hq
    have hnonneg : 0 ≤ invHeightSum q := by
      apply Finset.sum_nonneg
      intro w hw
      exact inv_nonneg.mpr (le_of_lt (hqpos w))
    have hn := hCinv q hq
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
    exact hn.trans (le_max_left _ _)
  have hinvHeightBound (q : Coord F) (hq : q ∈ coordK) (w : InfinitePlace F) :
      ((q w).2)⁻¹ ≤ Binv := by
    have hqpos := hCoordKPos hq
    have hterm : ((q w).2)⁻¹ ≤ invHeightSum q := by
      dsimp [invHeightSum]
      exact Finset.single_le_sum
        (fun v hv => inv_nonneg.mpr (le_of_lt (hqpos v))) (Finset.mem_univ w)
    exact hterm.trans (hinvHeightSumBound q hq)
  have hnormHeightEq : normHeight F = fun z => ∏ w, (coordsX F z w).2 := by
    funext z
    simp [normHeight, coordsX]
  have hnormHeightCont : Continuous (normHeight F) := by
    rw [hnormHeightEq]
    apply continuous_finsetProd
    intro w hw
    exact continuous_snd.comp ((continuous_apply w).comp hcoordsXCont)
  obtain ⟨CN, hCN⟩ := hK.exists_bound_of_continuousOn hnormHeightCont.continuousOn
  let BN : ℝ := max CN 1
  have hBN : 0 < BN := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hNormHeightBound (z : X F) (hz : z ∈ K) : normHeight F z ≤ BN := by
    have hzpos : 0 ≤ normHeight F z := by
      rw [hnormHeightEq]
      exact Finset.prod_nonneg fun w hw => le_of_lt (hcoordPos z w)
    have hbound := hCN z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hzpos] at hbound
    exact hbound.trans (le_max_left _ _)
  rcases hlocal K hK with ⟨Cenergy, hCenergy, hlocalK⟩
  let rdim : ℝ := Fintype.card (InfinitePlace F × Fin 3)
  let Cchart : ℝ := BN ^ 3 *
    (Bψ ^ 2 + 2 * rdim * (Bψd ^ 2 + Bψ ^ 2 * Binv ^ 2))
  have hCchart : 0 ≤ Cchart := by positivity
  let Aenergy : ℝ := Cenergy * Cchart
  have hAenergy : 0 ≤ Aenergy := mul_nonneg hCenergy hCchart
  let Cbound : ℝ := 2 * Real.sqrt Aenergy
  have hCbound : 0 ≤ Cbound := by positivity
  let Q : Set (RellichCoord F) := rellichFromCoord (F := F) '' coordK
  have hQ : IsCompact Q := by
    dsimp [Q]
    exact hCoordK.image rellichFromCoord_continuous
  have hQpos : Q ⊆ rellichPosSet F := by
    rintro p ⟨q, hq, rfl⟩
    exact rellichFromCoord_mem_posSet (F := F) q (hCoordKPos hq)
  refine ⟨Cbound, hCbound, ?_⟩
  intro f
  let hfTest : IsGammaTest F Γ (f : X F → ℂ) := (htests (f : X F → ℂ)).1 f.property
  have hfSmooth : IsSmoothX F (f : X F → ℂ) := hfTest.2.1
  let coordSub : X F → {q : Coord F // q ∈ posSet F} := fun z =>
    ⟨coordsX F z, hcoordPos z⟩
  have hcoordSubCont : Continuous coordSub :=
    Continuous.subtype_mk hcoordsXCont hcoordPos
  let ψcoordSub : {q : Coord F // q ∈ posSet F} → ℝ := fun q => ψcoord q.1
  have hψcoordSubCont : Continuous ψcoordSub :=
    continuousOn_iff_continuous_domRestrict.mp hψcoord
  let fcoord : Coord F → ℂ := fun q => (f : X F → ℂ) (ptX F q)
  have hfcoordOn : ContinuousOn fcoord (posSet F) := hfSmooth.continuousOn
  let fcoordSub : {q : Coord F // q ∈ posSet F} → ℂ := fun q => fcoord q.1
  have hfcoordSubCont : Continuous fcoordSub :=
    continuousOn_iff_continuous_domRestrict.mp hfcoordOn
  have hψXCont : Continuous (fun z => ψcoord (coordsX F z)) :=
    hψcoordSubCont.comp hcoordSubCont
  have hfXCont : Continuous (fun z => fcoord (coordsX F z)) :=
    hfcoordSubCont.comp hcoordSubCont
  have hfContinuous : Continuous (fun z : X F => (f : X F → ℂ) z) := by
    have heq : (fun z : X F => (f : X F → ℂ) z) =
        fun z => fcoord (coordsX F z) := by
      funext z
      simp [fcoord, hptXcoords z]
    rw [heq]
    exact hfXCont
  have hfullGradCont : Continuous (fullGradient F (f : X F → ℂ)) :=
    rellich_fullGradient_continuous hcoordsXCont hcoordPos hCoordPosOpen
      (f : X F → ℂ) hfSmooth
  let energyDensity : X F → ℝ := fun z =>
    ‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2
  have hEnergyCont : Continuous energyDensity := by
    dsimp [energyDensity]
    exact (hfContinuous.norm.pow 2).add (hfullGradCont.norm.pow 2)
  have hEnergyOn : IntegrableOn energyDensity K (volX F) :=
    @ContinuousOn.integrableOn_compact (X F) ℝ inferInstance inferInstance inferInstance
      (volX F) hOpenX K energyDensity inferInstance hT2X hK hEnergyCont.continuousOn
  let TRe : ℂ →L[ℝ] ℝ := Complex.reCLM
  let TIm : ℂ →L[ℝ] ℝ := Complex.imCLM
  let uRe : RellichCoord F → ℝ := fun p => TRe (rellichLocalized F ψ (f : X F → ℂ) p)
  let uIm : RellichCoord F → ℝ := fun p => TIm (rellichLocalized F ψ (f : X F → ℂ) p)
  have huReSupport : Function.support uRe ⊆ Q := by
    exact rellichLocalized_component_support_subset ψ (f : X F → ℂ) TRe K hψK hcoordPt
  have huImSupport : Function.support uIm ⊆ Q := by
    exact rellichLocalized_component_support_subset ψ (f : X F → ℂ) TIm K hψK hcoordPt
  have hgradReSupport : Function.support (fun p => RellichEuclidean.grad uRe p) ⊆ Q :=
    rellichEuclidean_grad_support_subset uRe Q hQ huReSupport
  have hgradImSupport : Function.support (fun p => RellichEuclidean.grad uIm p) ⊆ Q :=
    rellichEuclidean_grad_support_subset uIm Q hQ huImSupport
  let chartPt : X F → RellichCoord F := fun z => rellichFromCoord (F := F) (coordsX F z)
  have hchartPtCont : Continuous chartPt := rellichFromCoord_continuous.comp hcoordsXCont
  have hchartPtPos : ∀ z, chartPt z ∈ rellichPosSet F := fun z =>
    rellichFromCoord_mem_posSet (F := F) (coordsX F z) (hcoordPos z)
  have huReContOn : ContDiffOn ℝ ∞ uRe (rellichPosSet F) := by
    simpa [uRe, TRe, Complex.reCLM_apply] using
      rellichLocalized_component_contDiffOn ψ (f : X F → ℂ) TRe hψsmooth hfSmooth
  have huImContOn : ContDiffOn ℝ ∞ uIm (rellichPosSet F) := by
    simpa [uIm, TIm, Complex.imCLM_apply] using
      rellichLocalized_component_contDiffOn ψ (f : X F → ℂ) TIm hψsmooth hfSmooth
  have huReGradContOn : ContinuousOn (fun p => RellichEuclidean.grad uRe p)
      (rellichPosSet F) := by
    change ContinuousOn (fun p => (InnerProductSpace.toDual ℝ (RellichCoord F)).symm
      (fderiv ℝ uRe p)) (rellichPosSet F)
    exact (InnerProductSpace.toDual ℝ (RellichCoord F)).symm.continuous.comp_continuousOn
      (huReContOn.continuousOn_fderiv_of_isOpen hRellichPosOpen (by simp))
  have huImGradContOn : ContinuousOn (fun p => RellichEuclidean.grad uIm p)
      (rellichPosSet F) := by
    change ContinuousOn (fun p => (InnerProductSpace.toDual ℝ (RellichCoord F)).symm
      (fderiv ℝ uIm p)) (rellichPosSet F)
    exact (InnerProductSpace.toDual ℝ (RellichCoord F)).symm.continuous.comp_continuousOn
      (huImContOn.continuousOn_fderiv_of_isOpen hRellichPosOpen (by simp))
  let massXRe : X F → ℝ := fun z =>
    ψcoord (coordsX F z) ^ 2 * (TRe (fcoord (coordsX F z))) ^ 2 * normHeight F z ^ 3
  let massXIm : X F → ℝ := fun z =>
    ψcoord (coordsX F z) ^ 2 * (TIm (fcoord (coordsX F z))) ^ 2 * normHeight F z ^ 3
  have hMassXReCont : Continuous massXRe := by
    dsimp [massXRe]
    exact hψXCont.pow 2 |>.mul ((TRe.continuous.comp hfXCont).pow 2) |>.mul
      (hnormHeightCont.pow 3)
  have hMassXImCont : Continuous massXIm := by
    dsimp [massXIm]
    exact hψXCont.pow 2 |>.mul ((TIm.continuous.comp hfXCont).pow 2) |>.mul
      (hnormHeightCont.pow 3)
  have hMassXReSupport : Function.support massXRe ⊆ K := by
    intro z hz
    by_contra hzK
    have hψzero : ψcoord (coordsX F z) = 0 := by
      by_contra hψnz
      have hz' : ptX F (coordsX F z) ∈ K := hψK _ hψnz
      exact hzK (hptXcoords z ▸ hz')
    simp [massXRe, hψzero] at hz
  have hMassXImSupport : Function.support massXIm ⊆ K := by
    intro z hz
    by_contra hzK
    have hψzero : ψcoord (coordsX F z) = 0 := by
      by_contra hψnz
      have hz' : ptX F (coordsX F z) ∈ K := hψK _ hψnz
      exact hzK (hptXcoords z ▸ hz')
    simp [massXIm, hψzero] at hz
  have hMassXReIntOn : IntegrableOn massXRe K (volX F) :=
    @ContinuousOn.integrableOn_compact (X F) ℝ inferInstance inferInstance inferInstance
      (volX F) hOpenX K massXRe inferInstance hT2X hK hMassXReCont.continuousOn
  have hMassXImIntOn : IntegrableOn massXIm K (volX F) :=
    @ContinuousOn.integrableOn_compact (X F) ℝ inferInstance inferInstance inferInstance
      (volX F) hOpenX K massXIm inferInstance hT2X hK hMassXImCont.continuousOn
  have hMassXReIndInt : Integrable (K.indicator massXRe) (volX F) :=
    hMassXReIntOn.integrable_indicator hKmeas
  have hMassXImIndInt : Integrable (K.indicator massXIm) (volX F) :=
    hMassXImIntOn.integrable_indicator hKmeas
  have hMassXReIndEq : massXRe = K.indicator massXRe := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : massXRe z = 0 := by
        by_contra hne
        exact hz (hMassXReSupport hne)
      simp [hz, hz0]
  have hMassXImIndEq : massXIm = K.indicator massXIm := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : massXIm z = 0 := by
        by_contra hne
        exact hz (hMassXImSupport hne)
      simp [hz, hz0]
  have hMassXReInt : Integrable massXRe (volX F) := hMassXReIndEq ▸ hMassXReIndInt
  have hMassXImInt : Integrable massXIm (volX F) := hMassXImIndEq ▸ hMassXImIndInt
  let gradXRe : X F → ℝ := fun z =>
    normHeight F z ^ 3 * ‖RellichEuclidean.grad uRe (chartPt z)‖ ^ 2
  let gradXIm : X F → ℝ := fun z =>
    normHeight F z ^ 3 * ‖RellichEuclidean.grad uIm (chartPt z)‖ ^ 2
  have hchartPt_not_Q (z : X F) (hz : z ∉ K) : chartPt z ∉ Q := by
    rintro ⟨p, hp, hpeq⟩
    rcases hp with ⟨z', hz'K, hqeq⟩
    have hcoordEq : coordsX F z = coordsX F z' := by
      apply rellichCoordEquiv.injective
      calc
        rellichCoordEquiv (coordsX F z) = chartPt z := by
          simp [chartPt, rellichCoordEquiv_apply]
        _ = rellichFromCoord (F := F) p := hpeq.symm
        _ = rellichCoordEquiv p := by simp [rellichCoordEquiv_apply]
        _ = rellichCoordEquiv (coordsX F z') := congrArg _ hqeq.symm
    have hzEq : z = z' := by
      rw [← hptXcoords z, ← hptXcoords z', hcoordEq]
    exact hz (hzEq ▸ hz'K)
  have hgradXReCont : Continuous gradXRe := by
    dsimp [gradXRe]
    have hgrad : Continuous (fun z : X F => RellichEuclidean.grad uRe (chartPt z)) := by
      apply continuousOn_univ.mp
      exact huReGradContOn.comp hchartPtCont.continuousOn (fun z _ => hchartPtPos z)
    exact hnormHeightCont.pow 3 |>.mul (hgrad.norm.pow 2)
  have hgradXImCont : Continuous gradXIm := by
    dsimp [gradXIm]
    have hgrad : Continuous (fun z : X F => RellichEuclidean.grad uIm (chartPt z)) := by
      apply continuousOn_univ.mp
      exact huImGradContOn.comp hchartPtCont.continuousOn (fun z _ => hchartPtPos z)
    exact hnormHeightCont.pow 3 |>.mul (hgrad.norm.pow 2)
  have hgradXReSupport : Function.support gradXRe ⊆ K := by
    intro z hz
    by_contra hzK
    have hp : RellichEuclidean.grad uRe (chartPt z) ≠ 0 := by
      intro hp0
      apply hz
      simp [gradXRe, hp0]
    exact hchartPt_not_Q z hzK (hgradReSupport hp)
  have hgradXImSupport : Function.support gradXIm ⊆ K := by
    intro z hz
    by_contra hzK
    have hp : RellichEuclidean.grad uIm (chartPt z) ≠ 0 := by
      intro hp0
      apply hz
      simp [gradXIm, hp0]
    exact hchartPt_not_Q z hzK (hgradImSupport hp)
  have hgradXReIntOn : IntegrableOn gradXRe K (volX F) :=
    @ContinuousOn.integrableOn_compact (X F) ℝ inferInstance inferInstance inferInstance
      (volX F) hOpenX K gradXRe inferInstance hT2X hK hgradXReCont.continuousOn
  have hgradXImIntOn : IntegrableOn gradXIm K (volX F) :=
    @ContinuousOn.integrableOn_compact (X F) ℝ inferInstance inferInstance inferInstance
      (volX F) hOpenX K gradXIm inferInstance hT2X hK hgradXImCont.continuousOn
  have hgradXReIndInt : Integrable (K.indicator gradXRe) (volX F) :=
    hgradXReIntOn.integrable_indicator hKmeas
  have hgradXImIndInt : Integrable (K.indicator gradXIm) (volX F) :=
    hgradXImIntOn.integrable_indicator hKmeas
  have hgradXReIndEq : gradXRe = K.indicator gradXRe := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : gradXRe z = 0 := by
        by_contra hne
        exact hz (hgradXReSupport hne)
      simp [hz, hz0]
  have hgradXImIndEq : gradXIm = K.indicator gradXIm := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : gradXIm z = 0 := by
        by_contra hne
        exact hz (hgradXImSupport hne)
      simp [hz, hz0]
  have hgradXReInt : Integrable gradXRe (volX F) := hgradXReIndEq ▸ hgradXReIndInt
  have hgradXImInt : Integrable gradXIm (volX F) := hgradXImIndEq ▸ hgradXImIndInt
  let massReLp := RellichEuclidean.h1OnToL2 c.support c.compact.measurableSet (c.re f)
  let massImLp := RellichEuclidean.h1OnToL2 c.support c.compact.measurableSet (c.im f)
  let gradReLp := rellichChartGradient c.support c.compact.measurableSet (c.re f)
  let gradImLp := rellichChartGradient c.support c.compact.measurableSet (c.im f)
  have hmassReAe : ∀ᵐ p ∂(volume : Measure (RellichCoord F)), massReLp p = uRe p := by
    filter_upwards [c.re_rep f] with p hp
    simpa [massReLp, uRe, TRe, Complex.reCLM_apply] using hp
  have hmassImAe : ∀ᵐ p ∂(volume : Measure (RellichCoord F)), massImLp p = uIm p := by
    filter_upwards [c.im_rep f] with p hp
    simpa [massImLp, uIm, TIm, Complex.imCLM_apply] using hp
  have hgradReAe : ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
      gradReLp p = RellichEuclidean.grad uRe p := by
    simpa [gradReLp, uRe, TRe, Complex.reCLM_apply] using c.re_grad_rep f
  have hgradImAe : ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
      gradImLp p = RellichEuclidean.grad uIm p := by
    simpa [gradImLp, uIm, TIm, Complex.imCLM_apply] using c.im_grad_rep f
  have hmassReSqInt : Integrable (fun p => ‖massReLp p‖ ^ 2)
      (volume : Measure (RellichCoord F)) :=
    (Lp.memLp massReLp).integrable_norm_pow (by norm_num)
  have hmassImSqInt : Integrable (fun p => ‖massImLp p‖ ^ 2)
      (volume : Measure (RellichCoord F)) :=
    (Lp.memLp massImLp).integrable_norm_pow (by norm_num)
  have hgradReSqInt : Integrable (fun p => ‖gradReLp p‖ ^ 2)
      (volume : Measure (RellichCoord F)) :=
    (Lp.memLp gradReLp).integrable_norm_pow (by norm_num)
  have hgradImSqInt : Integrable (fun p => ‖gradImLp p‖ ^ 2)
      (volume : Measure (RellichCoord F)) :=
    (Lp.memLp gradImLp).integrable_norm_pow (by norm_num)
  have huReSqInt : Integrable (fun p => (uRe p) ^ 2) (volume : Measure (RellichCoord F)) := by
    apply hmassReSqInt.congr
    filter_upwards [hmassReAe] with p hp
    rw [← hp]
    simp
  have huImSqInt : Integrable (fun p => (uIm p) ^ 2) (volume : Measure (RellichCoord F)) := by
    apply hmassImSqInt.congr
    filter_upwards [hmassImAe] with p hp
    rw [← hp]
    simp
  have hgradReNormSqInt : Integrable
      (fun p => ‖RellichEuclidean.grad uRe p‖ ^ 2) (volume : Measure (RellichCoord F)) := by
    apply hgradReSqInt.congr
    filter_upwards [hgradReAe] with p hp
    rw [← hp]
  have hgradImNormSqInt : Integrable
      (fun p => ‖RellichEuclidean.grad uIm p‖ ^ 2) (volume : Measure (RellichCoord F)) := by
    apply hgradImSqInt.congr
    filter_upwards [hgradImAe] with p hp
    rw [← hp]
  let chartEnergyRe : RellichCoord F → ℝ := fun p =>
    (uRe p) ^ 2 + ‖RellichEuclidean.grad uRe p‖ ^ 2
  let chartEnergyIm : RellichCoord F → ℝ := fun p =>
    (uIm p) ^ 2 + ‖RellichEuclidean.grad uIm p‖ ^ 2
  have hchartEnergyReInt : Integrable chartEnergyRe (volume : Measure (RellichCoord F)) := by
    exact huReSqInt.add hgradReNormSqInt
  have hchartEnergyImInt : Integrable chartEnergyIm (volume : Measure (RellichCoord F)) := by
    exact huImSqInt.add hgradImNormSqInt
  let chartMassRe : RellichCoord F → ℝ := fun p => (uRe p) ^ 2
  let chartMassIm : RellichCoord F → ℝ := fun p => (uIm p) ^ 2
  let chartGradRe : RellichCoord F → ℝ := fun p => ‖RellichEuclidean.grad uRe p‖ ^ 2
  let chartGradIm : RellichCoord F → ℝ := fun p => ‖RellichEuclidean.grad uIm p‖ ^ 2
  have hchartMassReSupport : Function.support chartMassRe ⊆ rellichPosSet F := by
    intro p hp
    have hu : uRe p ≠ 0 := by
      intro h0
      exact hp (by simp [chartMassRe, h0])
    exact hQpos (huReSupport hu)
  have hchartMassImSupport : Function.support chartMassIm ⊆ rellichPosSet F := by
    intro p hp
    have hu : uIm p ≠ 0 := by
      intro h0
      exact hp (by simp [chartMassIm, h0])
    exact hQpos (huImSupport hu)
  have hchartGradReSupport : Function.support chartGradRe ⊆ rellichPosSet F := by
    intro p hp
    have hu : RellichEuclidean.grad uRe p ≠ 0 := by
      intro h0
      exact hp (by simp [chartGradRe, h0])
    exact hQpos (hgradReSupport hu)
  have hchartGradImSupport : Function.support chartGradIm ⊆ rellichPosSet F := by
    intro p hp
    have hu : RellichEuclidean.grad uIm p ≠ 0 := by
      intro h0
      exact hp (by simp [chartGradIm, h0])
    exact hQpos (hgradImSupport hu)
  have hmassRePoint (q : Coord F) (hq : q ∈ posSet F) :
      massXRe (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
        chartMassRe (rellichFromCoord (F := F) q) := by
    have hcoord := hcoordPt q hq
    have hheight := rellichNormHeight_ptX hcoordPt q hq
    have hcomp := rellichLocalized_component_value ψ (f : X F → ℂ) TRe q hq
    calc
      massXRe (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
          (ψ (ptX F q) * TRe ((f : X F → ℂ) (ptX F q))) ^ 2 := by
        simp only [massXRe, hcoord, hheight, ψcoord, fcoord]
        calc
          _ = (ψ (ptX F q) * TRe ((f : X F → ℂ) (ptX F q))) ^ 2 *
                ((∏ w, (q w).2) ^ 3 * (∏ w, (((q w).2 ^ 3)⁻¹))) := by ring
          _ = (ψ (ptX F q) * TRe ((f : X F → ℂ) (ptX F q))) ^ 2 * 1 :=
            congrArg _ (rellichDensity_cancel q hq)
          _ = _ := by ring
      _ = chartMassRe (rellichFromCoord (F := F) q) := by
        simp [chartMassRe, uRe, hcomp]
  have hmassImPoint (q : Coord F) (hq : q ∈ posSet F) :
      massXIm (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
        chartMassIm (rellichFromCoord (F := F) q) := by
    have hcoord := hcoordPt q hq
    have hheight := rellichNormHeight_ptX hcoordPt q hq
    have hcomp := rellichLocalized_component_value ψ (f : X F → ℂ) TIm q hq
    calc
      massXIm (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
          (ψ (ptX F q) * TIm ((f : X F → ℂ) (ptX F q))) ^ 2 := by
        simp only [massXIm, hcoord, hheight, ψcoord, fcoord]
        calc
          _ = (ψ (ptX F q) * TIm ((f : X F → ℂ) (ptX F q))) ^ 2 *
                ((∏ w, (q w).2) ^ 3 * (∏ w, (((q w).2 ^ 3)⁻¹))) := by ring
          _ = (ψ (ptX F q) * TIm ((f : X F → ℂ) (ptX F q))) ^ 2 * 1 :=
            congrArg _ (rellichDensity_cancel q hq)
          _ = _ := by ring
      _ = chartMassIm (rellichFromCoord (F := F) q) := by
        simp [chartMassIm, uIm, hcomp]
  have hgradRePoint (q : Coord F) (hq : q ∈ posSet F) :
      gradXRe (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
        chartGradRe (rellichFromCoord (F := F) q) := by
    have hcoord := hcoordPt q hq
    have hheight := rellichNormHeight_ptX hcoordPt q hq
    calc
      gradXRe (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
          ‖RellichEuclidean.grad uRe (rellichFromCoord (F := F) q)‖ ^ 2 := by
        simp only [gradXRe, chartPt, hcoord, hheight]
        calc
          (∏ w, (q w).2) ^ 3 *
              ‖RellichEuclidean.grad uRe (rellichFromCoord (F := F) q)‖ ^ 2 *
              (∏ w, (((q w).2 ^ 3)⁻¹)) =
              ‖RellichEuclidean.grad uRe (rellichFromCoord (F := F) q)‖ ^ 2 *
                ((∏ w, (q w).2) ^ 3 * (∏ w, (((q w).2 ^ 3)⁻¹))) := by ring
          _ = ‖RellichEuclidean.grad uRe (rellichFromCoord (F := F) q)‖ ^ 2 := by
            calc
              _ = ‖RellichEuclidean.grad uRe (rellichFromCoord (F := F) q)‖ ^ 2 * 1 :=
                congrArg _ (rellichDensity_cancel q hq)
              _ = _ := by ring
      _ = chartGradRe (rellichFromCoord (F := F) q) := by rfl
  have hgradImPoint (q : Coord F) (hq : q ∈ posSet F) :
      gradXIm (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
        chartGradIm (rellichFromCoord (F := F) q) := by
    have hcoord := hcoordPt q hq
    have hheight := rellichNormHeight_ptX hcoordPt q hq
    calc
      gradXIm (ptX F q) * (∏ w, (((q w).2 ^ 3)⁻¹)) =
          ‖RellichEuclidean.grad uIm (rellichFromCoord (F := F) q)‖ ^ 2 := by
        simp only [gradXIm, chartPt, hcoord, hheight]
        calc
          (∏ w, (q w).2) ^ 3 *
              ‖RellichEuclidean.grad uIm (rellichFromCoord (F := F) q)‖ ^ 2 *
              (∏ w, (((q w).2 ^ 3)⁻¹)) =
              ‖RellichEuclidean.grad uIm (rellichFromCoord (F := F) q)‖ ^ 2 *
                ((∏ w, (q w).2) ^ 3 * (∏ w, (((q w).2 ^ 3)⁻¹))) := by ring
          _ = ‖RellichEuclidean.grad uIm (rellichFromCoord (F := F) q)‖ ^ 2 := by
            calc
              _ = ‖RellichEuclidean.grad uIm (rellichFromCoord (F := F) q)‖ ^ 2 * 1 :=
                congrArg _ (rellichDensity_cancel q hq)
              _ = _ := by ring
      _ = chartGradIm (rellichFromCoord (F := F) q) := by rfl
  have hMassReVolume :
      ∫ p, chartMassRe p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, massXRe z ∂(volX F) :=
    rellich_chart_integral_eq (hG3.2.1) massXRe chartMassRe hmassRePoint
      hchartMassReSupport hMassXReInt huReSqInt
  have hMassImVolume :
      ∫ p, chartMassIm p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, massXIm z ∂(volX F) :=
    rellich_chart_integral_eq (hG3.2.1) massXIm chartMassIm hmassImPoint
      hchartMassImSupport hMassXImInt huImSqInt
  have hGradReVolume :
      ∫ p, chartGradRe p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, gradXRe z ∂(volX F) :=
    rellich_chart_integral_eq (hG3.2.1) gradXRe chartGradRe hgradRePoint
      hchartGradReSupport hgradXReInt hgradReNormSqInt
  have hGradImVolume :
      ∫ p, chartGradIm p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, gradXIm z ∂(volX F) :=
    rellich_chart_integral_eq (hG3.2.1) gradXIm chartGradIm hgradImPoint
      hchartGradImSupport hgradXImInt hgradImNormSqInt
  have hderivSqBound (T : ℂ →L[ℝ] ℝ) (u : RellichCoord F → ℝ)
      (hu : ∀ p, u p = T (rellichLocalized F ψ (f : X F → ℂ) p))
      (hTnorm : ∀ a : ℂ, |T a| ≤ ‖a‖)
      (z : X F) (hz : z ∈ K) (w : InfinitePlace F) (j : Fin 3) :
      (fderiv ℝ u (chartPt z) (EuclideanSpace.single (w, j) (1 : ℝ))) ^ 2 ≤
        2 * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
    let q : Coord F := coordsX F z
    have hqpos : q ∈ posSet F := hcoordPos z
    have hqK : q ∈ coordK := ⟨z, hz, rfl⟩
    have hy : 0 < (q w).2 := hqpos w
    let dψ := fderiv ℝ ψcoord q (placeDirection F w j)
    let vf := T (fcoord q)
    let df := fderiv ℝ (fun q => (f : X F → ℂ) (ptX F q)) q
      (placeDirection F w j)
    let cutTerm := dψ * vf
    let funTerm := ψcoord q * T df
    have hToCoord : rellichToCoord F (chartPt z) = q := by
      dsimp [chartPt, q]
      exact rellichToCoord_fromCoord (F := F) (coordsX F z) (hcoordPos z)
    have hD := rellichLocalized_component_fderiv ψ (f : X F → ℂ) T
      hCoordPosOpen hRellichPosOpen hψsmooth hfSmooth (chartPt z) (hchartPtPos z) w j
    have hD' : fderiv ℝ u (chartPt z) (EuclideanSpace.single (w, j) (1 : ℝ)) =
        cutTerm + funTerm := by
      rw [show u = fun p => T (rellichLocalized F ψ (f : X F → ℂ) p) from funext hu]
      simpa [dψ, vf, df, cutTerm, funTerm, ψcoord, fcoord, hToCoord] using hD
    have hdψNorm : ‖dψ‖ ≤ Bψd := by
      calc
        ‖dψ‖ ≤ ‖fderiv ℝ ψcoord q‖ * ‖placeDirection F w j‖ :=
          (fderiv ℝ ψcoord q).le_opNorm (placeDirection F w j)
        _ = ‖fderiv ℝ ψcoord q‖ := by rw [rellichPlaceDirection_norm]; simp
        _ ≤ Bψd := hψfderivBound q hqK
    have hdψAbs : |dψ| ≤ Bψd := by simpa [Real.norm_eq_abs] using hdψNorm
    have hvfAbs : |vf| ≤ ‖(f : X F → ℂ) z‖ := by
      simpa [vf, fcoord, q, hptXcoords z] using hTnorm ((f : X F → ℂ) z)
    have hcutAbs : |cutTerm| ≤ Bψd * ‖(f : X F → ℂ) z‖ := by
      dsimp [cutTerm]
      rw [abs_mul]
      exact mul_le_mul hdψAbs hvfAbs (abs_nonneg _) hBψd
    have hfullComp :
        ‖placeGradient F w (f : X F → ℂ) z j‖ ≤
          ‖fullGradient F (f : X F → ℂ) z‖ := by
      have h := rellichComplexEuclidean_norm_apply_le
        (fullGradient F (f : X F → ℂ) z) (w, j)
      simpa [fullGradient] using h
    have hplace : placeGradient F w (f : X F → ℂ) z j =
        ((q w).2 : ℂ) * df := by
      dsimp [placeGradient, df, q]
      rfl
    have hdfWeighted : (q w).2 * ‖df‖ ≤ ‖fullGradient F (f : X F → ℂ) z‖ := by
      simpa [hplace, norm_mul, Complex.norm_real, abs_of_pos hy] using hfullComp
    have hdfNorm : ‖df‖ ≤ Binv * ‖fullGradient F (f : X F → ℂ) z‖ := by
      calc
        ‖df‖ = (q w).2⁻¹ * ((q w).2 * ‖df‖) := by
          field_simp [ne_of_gt hy]
        _ ≤ (q w).2⁻¹ * ‖fullGradient F (f : X F → ℂ) z‖ :=
          mul_le_mul_of_nonneg_left hdfWeighted (inv_nonneg.mpr (le_of_lt hy))
        _ ≤ Binv * ‖fullGradient F (f : X F → ℂ) z‖ :=
          mul_le_mul_of_nonneg_right (hinvHeightBound q hqK w) (norm_nonneg _)
    have hTdfAbs : |T df| ≤ Binv * ‖fullGradient F (f : X F → ℂ) z‖ :=
      (hTnorm df).trans hdfNorm
    have hψAbs : |ψcoord q| ≤ Bψ := hψcoordBound q hqK
    have hfunAbs : |funTerm| ≤ Bψ * Binv * ‖fullGradient F (f : X F → ℂ) z‖ := by
      dsimp [funTerm]
      rw [abs_mul]
      calc
        |ψcoord q| * |T df| ≤ Bψ * (Binv * ‖fullGradient F (f : X F → ℂ) z‖) :=
          mul_le_mul hψAbs hTdfAbs (abs_nonneg _) hBψ
        _ = Bψ * Binv * ‖fullGradient F (f : X F → ℂ) z‖ := by ring
    rw [hD']
    calc
      (cutTerm + funTerm) ^ 2 = |cutTerm + funTerm| ^ 2 := by simp [sq_abs]
      _ ≤ (Bψd * ‖(f : X F → ℂ) z‖ +
          Bψ * Binv * ‖fullGradient F (f : X F → ℂ) z‖) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
          ((abs_add_le _ _).trans (add_le_add hcutAbs hfunAbs))
      _ ≤ 2 * ((Bψd * ‖(f : X F → ℂ) z‖) ^ 2 +
          (Bψ * Binv * ‖fullGradient F (f : X F → ℂ) z‖) ^ 2) := add_sq_le
      _ = 2 * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by ring
  have hgradReSqBound (z : X F) (hz : z ∈ K) :
      ‖RellichEuclidean.grad uRe (chartPt z)‖ ^ 2 ≤
        2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i, (RellichEuclidean.grad uRe (chartPt z) i) ^ 2) =
          ∑ i, (fderiv ℝ uRe (chartPt z) (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [rellichEuclidean_grad_apply]
      _ ≤ ∑ i, 2 * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rcases i with ⟨w, j⟩
        exact hderivSqBound TRe uRe (fun p => rfl)
          (by intro a; simpa [TRe] using Complex.abs_re_le_norm a) z hz w j
      _ = 2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        simp [rdim, Finset.sum_const, nsmul_eq_mul]
        ring
  have hgradImSqBound (z : X F) (hz : z ∈ K) :
      ‖RellichEuclidean.grad uIm (chartPt z)‖ ^ 2 ≤
        2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i, (RellichEuclidean.grad uIm (chartPt z) i) ^ 2) =
          ∑ i, (fderiv ℝ uIm (chartPt z) (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [rellichEuclidean_grad_apply]
      _ ≤ ∑ i, 2 * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rcases i with ⟨w, j⟩
        exact hderivSqBound TIm uIm (fun p => rfl)
          (by intro a; simpa [TIm] using Complex.abs_im_le_norm a) z hz w j
      _ = 2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        simp [rdim, Finset.sum_const, nsmul_eq_mul]
        ring
  have hmassXReBound (z : X F) (hz : z ∈ K) :
      massXRe z ≤ BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 := by
    let q : Coord F := coordsX F z
    have hqK : q ∈ coordK := ⟨z, hz, rfl⟩
    have hψSq : ψcoord q ^ 2 ≤ Bψ ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hBψ).2 (hψcoordBound q hqK)
    have hvalAbs : |TRe (fcoord q)| ≤ ‖(f : X F → ℂ) z‖ := by
      simpa [TRe, fcoord, q, hptXcoords z] using
        Complex.abs_re_le_norm ((f : X F → ℂ) z)
    have hvalSq : (TRe (fcoord q)) ^ 2 ≤ ‖(f : X F → ℂ) z‖ ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hvalAbs
    have hHpos : 0 < normHeight F z := by
      rw [hnormHeightEq]
      exact Finset.prod_pos fun w hw => hcoordPos z w
    have hHpow : normHeight F z ^ 3 ≤ BN ^ 3 := by
      exact pow_le_pow_left₀ hHpos.le (hNormHeightBound z hz) 3
    have hmass : ψcoord q ^ 2 * (TRe (fcoord q)) ^ 2 ≤
        Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 :=
      mul_le_mul hψSq hvalSq (sq_nonneg _) (sq_nonneg _)
    calc
      massXRe z = (ψcoord q ^ 2 * (TRe (fcoord q)) ^ 2) * normHeight F z ^ 3 := rfl
      _ ≤ (Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2) * BN ^ 3 :=
        mul_le_mul hmass hHpow (pow_nonneg (le_of_lt hHpos) 3)
          (mul_nonneg (sq_nonneg Bψ) (sq_nonneg _))
      _ = BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 := by ring
  have hmassXImBound (z : X F) (hz : z ∈ K) :
      massXIm z ≤ BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 := by
    let q : Coord F := coordsX F z
    have hqK : q ∈ coordK := ⟨z, hz, rfl⟩
    have hψSq : ψcoord q ^ 2 ≤ Bψ ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hBψ).2 (hψcoordBound q hqK)
    have hvalAbs : |TIm (fcoord q)| ≤ ‖(f : X F → ℂ) z‖ := by
      simpa [TIm, fcoord, q, hptXcoords z] using
        Complex.abs_im_le_norm ((f : X F → ℂ) z)
    have hvalSq : (TIm (fcoord q)) ^ 2 ≤ ‖(f : X F → ℂ) z‖ ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hvalAbs
    have hHpos : 0 < normHeight F z := by
      rw [hnormHeightEq]
      exact Finset.prod_pos fun w hw => hcoordPos z w
    have hHpow : normHeight F z ^ 3 ≤ BN ^ 3 := by
      exact pow_le_pow_left₀ hHpos.le (hNormHeightBound z hz) 3
    have hmass : ψcoord q ^ 2 * (TIm (fcoord q)) ^ 2 ≤
        Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 :=
      mul_le_mul hψSq hvalSq (sq_nonneg _) (sq_nonneg _)
    calc
      massXIm z = (ψcoord q ^ 2 * (TIm (fcoord q)) ^ 2) * normHeight F z ^ 3 := rfl
      _ ≤ (Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2) * BN ^ 3 :=
        mul_le_mul hmass hHpow (pow_nonneg (le_of_lt hHpos) 3)
          (mul_nonneg (sq_nonneg Bψ) (sq_nonneg _))
      _ = BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 := by ring
  have hgradXReBound (z : X F) (hz : z ∈ K) :
      gradXRe z ≤ BN ^ 3 * (2 * rdim) *
        (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
    have hHpos : 0 < normHeight F z := by
      rw [hnormHeightEq]
      exact Finset.prod_pos fun w hw => hcoordPos z w
    have hHpow : normHeight F z ^ 3 ≤ BN ^ 3 :=
      pow_le_pow_left₀ hHpos.le (hNormHeightBound z hz) 3
    have hgradSqNonneg : 0 ≤ ‖RellichEuclidean.grad uRe (chartPt z)‖ ^ 2 := sq_nonneg _
    calc
      gradXRe z = normHeight F z ^ 3 *
          ‖RellichEuclidean.grad uRe (chartPt z)‖ ^ 2 := rfl
      _ ≤ BN ^ 3 * (2 * rdim) *
          (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        calc
          _ ≤ BN ^ 3 * (2 * rdim *
              (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
                Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) :=
            mul_le_mul hHpow (hgradReSqBound z hz) hgradSqNonneg
              (pow_nonneg (le_of_lt hBN) 3)
          _ = _ := by ring
  have hgradXImBound (z : X F) (hz : z ∈ K) :
      gradXIm z ≤ BN ^ 3 * (2 * rdim) *
        (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
    have hHpos : 0 < normHeight F z := by
      rw [hnormHeightEq]
      exact Finset.prod_pos fun w hw => hcoordPos z w
    have hHpow : normHeight F z ^ 3 ≤ BN ^ 3 := by
      exact pow_le_pow_left₀ hHpos.le (hNormHeightBound z hz) 3
    have hgradSqNonneg : 0 ≤ ‖RellichEuclidean.grad uIm (chartPt z)‖ ^ 2 := sq_nonneg _
    calc
      gradXIm z = normHeight F z ^ 3 *
          ‖RellichEuclidean.grad uIm (chartPt z)‖ ^ 2 := rfl
      _ ≤ BN ^ 3 * (2 * rdim) *
          (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
        calc
          _ ≤ BN ^ 3 * (2 * rdim *
              (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
                Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) :=
            mul_le_mul hHpow (hgradImSqBound z hz) hgradSqNonneg
              (pow_nonneg (le_of_lt hBN) 3)
          _ = _ := by ring
  let totalXRe : X F → ℝ := fun z => massXRe z + gradXRe z
  let totalXIm : X F → ℝ := fun z => massXIm z + gradXIm z
  have htotalXReBound (z : X F) (hz : z ∈ K) :
      totalXRe z ≤ Cchart * energyDensity z := by
    have ha : 0 ≤ ‖(f : X F → ℂ) z‖ ^ 2 := sq_nonneg _
    have hb : 0 ≤ ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 := sq_nonneg _
    have hA : 0 ≤ Bψ ^ 2 := sq_nonneg _
    have hP : 0 ≤ 2 * rdim * Bψd ^ 2 := by positivity
    have hQ : 0 ≤ 2 * rdim * Bψ ^ 2 * Binv ^ 2 := by positivity
    have hinner :
        Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) ≤
        (Bψ ^ 2 + 2 * rdim * (Bψd ^ 2 + Bψ ^ 2 * Binv ^ 2)) *
          (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
      calc
        _ = Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            (2 * rdim * Bψd ^ 2) * ‖(f : X F → ℂ) z‖ ^ 2 +
            (2 * rdim * Bψ ^ 2 * Binv ^ 2) *
              ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 := by ring
        _ ≤ (Bψ ^ 2 + 2 * rdim * Bψd ^ 2 +
            2 * rdim * Bψ ^ 2 * Binv ^ 2) *
              (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
          nlinarith [mul_nonneg hA hb, mul_nonneg hP hb, mul_nonneg hQ ha]
        _ = _ := by ring
    calc
      totalXRe z = massXRe z + gradXRe z := rfl
      _ ≤ BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          BN ^ 3 * (2 * rdim) *
            (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
              Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) :=
        add_le_add (hmassXReBound z hz) (hgradXReBound z hz)
      _ = BN ^ 3 * (Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) := by ring
      _ ≤ Cchart * energyDensity z := by
        calc
          _ ≤ BN ^ 3 * ((Bψ ^ 2 + 2 * rdim * (Bψd ^ 2 + Bψ ^ 2 * Binv ^ 2)) *
              (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
          _ = Cchart * energyDensity z := by simp [Cchart, energyDensity]; ring
  have htotalXImBound (z : X F) (hz : z ∈ K) :
      totalXIm z ≤ Cchart * energyDensity z := by
    have ha : 0 ≤ ‖(f : X F → ℂ) z‖ ^ 2 := sq_nonneg _
    have hb : 0 ≤ ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 := sq_nonneg _
    have hA : 0 ≤ Bψ ^ 2 := sq_nonneg _
    have hP : 0 ≤ 2 * rdim * Bψd ^ 2 := by positivity
    have hQ : 0 ≤ 2 * rdim * Bψ ^ 2 * Binv ^ 2 := by positivity
    have hinner :
        Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) ≤
        (Bψ ^ 2 + 2 * rdim * (Bψd ^ 2 + Bψ ^ 2 * Binv ^ 2)) *
          (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
      calc
        _ = Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            (2 * rdim * Bψd ^ 2) * ‖(f : X F → ℂ) z‖ ^ 2 +
            (2 * rdim * Bψ ^ 2 * Binv ^ 2) *
              ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 := by ring
        _ ≤ (Bψ ^ 2 + 2 * rdim * Bψd ^ 2 +
            2 * rdim * Bψ ^ 2 * Binv ^ 2) *
              (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) := by
          nlinarith [mul_nonneg hA hb, mul_nonneg hP hb, mul_nonneg hQ ha]
        _ = _ := by ring
    calc
      totalXIm z = massXIm z + gradXIm z := rfl
      _ ≤ BN ^ 3 * Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          BN ^ 3 * (2 * rdim) *
            (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
              Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) :=
        add_le_add (hmassXImBound z hz) (hgradXImBound z hz)
      _ = BN ^ 3 * (Bψ ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
          2 * rdim * (Bψd ^ 2 * ‖(f : X F → ℂ) z‖ ^ 2 +
            Bψ ^ 2 * Binv ^ 2 * ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) := by ring
      _ ≤ Cchart * energyDensity z := by
        calc
          _ ≤ BN ^ 3 * ((Bψ ^ 2 + 2 * rdim * (Bψd ^ 2 + Bψ ^ 2 * Binv ^ 2)) *
              (‖(f : X F → ℂ) z‖ ^ 2 + ‖fullGradient F (f : X F → ℂ) z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = Cchart * energyDensity z := by simp [Cchart, energyDensity]; ring
  have htotalXReSupport : Function.support totalXRe ⊆ K := by
    intro z hz
    by_contra hzK
    have hmass0 : massXRe z = 0 := by
      by_contra hne
      exact hzK (hMassXReSupport hne)
    have hgrad0 : gradXRe z = 0 := by
      by_contra hne
      exact hzK (hgradXReSupport hne)
    exact hz (by simp [totalXRe, hmass0, hgrad0])
  have htotalXImSupport : Function.support totalXIm ⊆ K := by
    intro z hz
    by_contra hzK
    have hmass0 : massXIm z = 0 := by
      by_contra hne
      exact hzK (hMassXImSupport hne)
    have hgrad0 : gradXIm z = 0 := by
      by_contra hne
      exact hzK (hgradXImSupport hne)
    exact hz (by simp [totalXIm, hmass0, hgrad0])
  have htotalXReIndEq : totalXRe = K.indicator totalXRe := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : totalXRe z = 0 := by
        by_contra hne
        exact hz (htotalXReSupport hne)
      simp [hz, hz0]
  have htotalXImIndEq : totalXIm = K.indicator totalXIm := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · have hz0 : totalXIm z = 0 := by
        by_contra hne
        exact hz (htotalXImSupport hne)
      simp [hz, hz0]
  have htotalXReIndInt : Integrable (K.indicator totalXRe) (volX F) :=
    (hMassXReIntOn.add hgradXReIntOn).integrable_indicator hKmeas
  have htotalXImIndInt : Integrable (K.indicator totalXIm) (volX F) :=
    (hMassXImIntOn.add hgradXImIntOn).integrable_indicator hKmeas
  have htotalChartReVolume :
      ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, totalXRe z ∂(volX F) := by
    calc
      ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) =
          (∫ p, chartMassRe p ∂(volume : Measure (RellichCoord F))) +
            ∫ p, chartGradRe p ∂(volume : Measure (RellichCoord F)) := by
        simpa [chartEnergyRe, chartMassRe, chartGradRe] using
          integral_add huReSqInt hgradReNormSqInt
      _ = (∫ z, massXRe z ∂(volX F)) + ∫ z, gradXRe z ∂(volX F) := by
        rw [hMassReVolume, hGradReVolume]
      _ = ∫ z, totalXRe z ∂(volX F) := by
        simpa [totalXRe] using (integral_add hMassXReInt hgradXReInt).symm
  have htotalChartImVolume :
      ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) =
        ∫ z, totalXIm z ∂(volX F) := by
    calc
      ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) =
          (∫ p, chartMassIm p ∂(volume : Measure (RellichCoord F))) +
            ∫ p, chartGradIm p ∂(volume : Measure (RellichCoord F)) := by
        simpa [chartEnergyIm, chartMassIm, chartGradIm] using
          integral_add huImSqInt hgradImNormSqInt
      _ = (∫ z, massXIm z ∂(volX F)) + ∫ z, gradXIm z ∂(volX F) := by
        rw [hMassImVolume, hGradImVolume]
      _ = ∫ z, totalXIm z ∂(volX F) := by
        simpa [totalXIm] using (integral_add hMassXImInt hgradXImInt).symm
  have hScaledEnergyOn : IntegrableOn (fun z => Cchart * energyDensity z) K (volX F) := by
    exact hEnergyOn.const_mul Cchart
  have hScaledEnergyIndInt :
      Integrable (K.indicator (fun z => Cchart * energyDensity z)) (volX F) :=
    hScaledEnergyOn.integrable_indicator hKmeas
  have htotalXReIndLe :
      K.indicator totalXRe ≤ᵐ[volX F] K.indicator (fun z => Cchart * energyDensity z) := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · simpa [hz] using htotalXReBound z hz
    · simp [hz]
  have htotalXImIndLe :
      K.indicator totalXIm ≤ᵐ[volX F] K.indicator (fun z => Cchart * energyDensity z) := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · simpa [hz] using htotalXImBound z hz
    · simp [hz]
  have htotalChartReBound :
      ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) ≤
        Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) := by
    calc
      ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) =
          ∫ z, K.indicator totalXRe z ∂(volX F) := by
        rw [htotalChartReVolume, ← htotalXReIndEq]
      _ ≤ ∫ z, K.indicator (fun z => Cchart * energyDensity z) z ∂(volX F) :=
        integral_mono_ae htotalXReIndInt hScaledEnergyIndInt htotalXReIndLe
      _ = Cchart * ∫ z in K, energyDensity z ∂(volX F) := by
        rw [integral_indicator hKmeas, integral_const_mul]
      _ ≤ Cchart * (Cenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hlocalK f) hCchart
      _ = Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) := by
        simp [Aenergy]
        ring
  have htotalChartImBound :
      ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) ≤
        Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) := by
    calc
      ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) =
          ∫ z, K.indicator totalXIm z ∂(volX F) := by
        rw [htotalChartImVolume, ← htotalXImIndEq]
      _ ≤ ∫ z, K.indicator (fun z => Cchart * energyDensity z) z ∂(volX F) :=
        integral_mono_ae htotalXImIndInt hScaledEnergyIndInt htotalXImIndLe
      _ = Cchart * ∫ z in K, energyDensity z ∂(volX F) := by
        rw [integral_indicator hKmeas, integral_const_mul]
      _ ≤ Cchart * (Cenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hlocalK f) hCchart
      _ = Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) := by
        simp [Aenergy]
        ring
  have hmassReSqAE :
      (fun p => ‖massReLp p‖ ^ 2) =ᵐ[(volume : Measure (RellichCoord F))] chartMassRe := by
    filter_upwards [hmassReAe] with p hp
    simp [chartMassRe, hp]
  have hmassImSqAE :
      (fun p => ‖massImLp p‖ ^ 2) =ᵐ[(volume : Measure (RellichCoord F))] chartMassIm := by
    filter_upwards [hmassImAe] with p hp
    simp [chartMassIm, hp]
  have hgradReSqAE :
      (fun p => ‖gradReLp p‖ ^ 2) =ᵐ[(volume : Measure (RellichCoord F))] chartGradRe := by
    filter_upwards [hgradReAe] with p hp
    simp [chartGradRe, hp]
  have hgradImSqAE :
      (fun p => ‖gradImLp p‖ ^ 2) =ᵐ[(volume : Measure (RellichCoord F))] chartGradIm := by
    filter_upwards [hgradImAe] with p hp
    simp [chartGradIm, hp]
  have hmassReNormSq :
      ‖massReLp‖ ^ 2 = ∫ p, chartMassRe p ∂(volume : Measure (RellichCoord F)) := by
    calc
      ‖massReLp‖ ^ 2 =
          (Real.sqrt (∫ p, ‖massReLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F))) : ℝ) ^ 2 := by
        rw [rellichLp_norm_eq_sqrt_integral]
      _ = ∫ p, ‖massReLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F)) :=
        Real.sq_sqrt (integral_nonneg fun p => sq_nonneg ‖massReLp p‖)
      _ = ∫ p, chartMassRe p ∂(volume : Measure (RellichCoord F)) :=
        integral_congr_ae hmassReSqAE
  have hmassImNormSq :
      ‖massImLp‖ ^ 2 = ∫ p, chartMassIm p ∂(volume : Measure (RellichCoord F)) := by
    calc
      ‖massImLp‖ ^ 2 =
          (Real.sqrt (∫ p, ‖massImLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F))) : ℝ) ^ 2 := by
        rw [rellichLp_norm_eq_sqrt_integral]
      _ = ∫ p, ‖massImLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F)) :=
        Real.sq_sqrt (integral_nonneg fun p => sq_nonneg ‖massImLp p‖)
      _ = ∫ p, chartMassIm p ∂(volume : Measure (RellichCoord F)) :=
        integral_congr_ae hmassImSqAE
  have hgradReNormSq :
      ‖gradReLp‖ ^ 2 = ∫ p, chartGradRe p ∂(volume : Measure (RellichCoord F)) := by
    calc
      ‖gradReLp‖ ^ 2 =
          (Real.sqrt (∫ p, ‖gradReLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F))) : ℝ) ^ 2 := by
        rw [rellichLp_norm_eq_sqrt_integral]
      _ = ∫ p, ‖gradReLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F)) :=
        Real.sq_sqrt (integral_nonneg fun p => sq_nonneg ‖gradReLp p‖)
      _ = ∫ p, chartGradRe p ∂(volume : Measure (RellichCoord F)) :=
        integral_congr_ae hgradReSqAE
  have hgradImNormSq :
      ‖gradImLp‖ ^ 2 = ∫ p, chartGradIm p ∂(volume : Measure (RellichCoord F)) := by
    calc
      ‖gradImLp‖ ^ 2 =
          (Real.sqrt (∫ p, ‖gradImLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F))) : ℝ) ^ 2 := by
        rw [rellichLp_norm_eq_sqrt_integral]
      _ = ∫ p, ‖gradImLp p‖ ^ 2 ∂(volume : Measure (RellichCoord F)) :=
        Real.sq_sqrt (integral_nonneg fun p => sq_nonneg ‖gradImLp p‖)
      _ = ∫ p, chartGradIm p ∂(volume : Measure (RellichCoord F)) :=
        integral_congr_ae hgradImSqAE
  have hchartMassReLe :
      ∫ p, chartMassRe p ∂(volume : Measure (RellichCoord F)) ≤
        ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) := by
    apply integral_mono huReSqInt hchartEnergyReInt
    intro p
    exact le_add_of_nonneg_right (sq_nonneg ‖RellichEuclidean.grad uRe p‖)
  have hchartMassImLe :
      ∫ p, chartMassIm p ∂(volume : Measure (RellichCoord F)) ≤
        ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) := by
    apply integral_mono huImSqInt hchartEnergyImInt
    intro p
    exact le_add_of_nonneg_right (sq_nonneg ‖RellichEuclidean.grad uIm p‖)
  have hchartGradReLe :
      ∫ p, chartGradRe p ∂(volume : Measure (RellichCoord F)) ≤
        ∫ p, chartEnergyRe p ∂(volume : Measure (RellichCoord F)) := by
    apply integral_mono hgradReNormSqInt hchartEnergyReInt
    intro p
    exact le_add_of_nonneg_left (sq_nonneg (uRe p))
  have hchartGradImLe :
      ∫ p, chartGradIm p ∂(volume : Measure (RellichCoord F)) ≤
        ∫ p, chartEnergyIm p ∂(volume : Measure (RellichCoord F)) := by
    apply integral_mono hgradImNormSqInt hchartEnergyImInt
    intro p
    exact le_add_of_nonneg_left (sq_nonneg (uIm p))
  have hmassReNormSqBound :
      ‖massReLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
    hmassReNormSq ▸ hchartMassReLe.trans htotalChartReBound
  have hmassImNormSqBound :
      ‖massImLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
    hmassImNormSq ▸ hchartMassImLe.trans htotalChartImBound
  have hgradReNormSqBound :
      ‖gradReLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
    hgradReNormSq ▸ hchartGradReLe.trans htotalChartReBound
  have hgradImNormSqBound :
      ‖gradImLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
    hgradImNormSq ▸ hchartGradImLe.trans htotalChartImBound
  have henergySumSq :
      ‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2 ≤
        (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg (e.toL2 f)) (norm_nonneg (e.gradL2 f))]
  have hmassReSqTarget :
      ‖massReLp‖ ^ 2 ≤
        (Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) ^ 2 := by
    calc
      ‖massReLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
        hmassReNormSqBound
      _ ≤ Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left henergySumSq hAenergy
      _ = (Real.sqrt Aenergy) ^ 2 * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        congrArg (fun a : ℝ => a * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2)
          (Real.sq_sqrt hAenergy).symm
      _ = _ := by ring
  have hmassImSqTarget :
      ‖massImLp‖ ^ 2 ≤
        (Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) ^ 2 := by
    calc
      ‖massImLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
        hmassImNormSqBound
      _ ≤ Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left henergySumSq hAenergy
      _ = (Real.sqrt Aenergy) ^ 2 * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        congrArg (fun a : ℝ => a * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2)
          (Real.sq_sqrt hAenergy).symm
      _ = _ := by ring
  have hgradReSqTarget :
      ‖gradReLp‖ ^ 2 ≤
        (Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) ^ 2 := by
    calc
      ‖gradReLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
        hgradReNormSqBound
      _ ≤ Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left henergySumSq hAenergy
      _ = (Real.sqrt Aenergy) ^ 2 * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        congrArg (fun a : ℝ => a * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2)
          (Real.sq_sqrt hAenergy).symm
      _ = _ := by ring
  have hgradImSqTarget :
      ‖gradImLp‖ ^ 2 ≤
        (Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) ^ 2 := by
    calc
      ‖gradImLp‖ ^ 2 ≤ Aenergy * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) :=
        hgradImNormSqBound
      _ ≤ Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left henergySumSq hAenergy
      _ = (Real.sqrt Aenergy) ^ 2 * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2 :=
        congrArg (fun a : ℝ => a * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ^ 2)
          (Real.sq_sqrt hAenergy).symm
      _ = _ := by ring
  have hmassReNormBound :
      ‖massReLp‖ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hmassReSqTarget
  have hmassImNormBound :
      ‖massImLp‖ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hmassImSqTarget
  have hgradReNormBound :
      ‖gradReLp‖ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hgradReSqTarget
  have hgradImNormBound :
      ‖gradImLp‖ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hgradImSqTarget
  have hRePairNorm : ‖c.re f‖ ≤ ‖massReLp‖ + ‖gradReLp‖ := by
    change max ‖massReLp‖ ‖gradReLp‖ ≤ _
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  have hImPairNorm : ‖c.im f‖ ≤ ‖massImLp‖ + ‖gradImLp‖ := by
    change max ‖massImLp‖ ‖gradImLp‖ ≤ _
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  constructor
  · calc
      ‖c.re f‖ ≤ ‖massReLp‖ + ‖gradReLp‖ := hRePairNorm
      _ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) +
          Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
        add_le_add hmassReNormBound hgradReNormBound
      _ = Cbound * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := by simp [Cbound]; ring
  · calc
      ‖c.im f‖ ≤ ‖massImLp‖ + ‖gradImLp‖ := hImPairNorm
      _ ≤ Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) +
          Real.sqrt Aenergy * (‖e.toL2 f‖ + ‖e.gradL2 f‖) :=
        add_le_add hmassImNormBound hgradImNormBound
      _ = Cbound * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := by simp [Cbound]; ring

end ArtinPrimitiveRoots.A1.Spec
