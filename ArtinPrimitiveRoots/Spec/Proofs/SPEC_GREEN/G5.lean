import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GREEN.G4
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Euclidean.Inversion.Calculus

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.deprecated false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private abbrev G5Spatial := OAI.CubicEisenstein.EuclideanSpatial

private def g5SpatialOfCoord (c : ℂ × ℝ) : G5Spatial :=
  WithLp.toLp 2 ![Complex.reCLM c.1, Complex.imCLM c.1, c.2]

private def g5CoordOfSpatial (q : G5Spatial) : ℂ × ℝ :=
  (((q 0 : ℝ) : ℂ) + Complex.I * (q 1 : ℝ), q 2)

private theorem g5CoordOfSpatial_spatialOfCoord (c : ℂ × ℝ) :
    g5CoordOfSpatial (g5SpatialOfCoord c) = c := by
  rcases c with ⟨x, y⟩
  apply Prod.ext
  · apply Complex.ext <;> simp [g5CoordOfSpatial, g5SpatialOfCoord,
      Complex.reCLM_apply, Complex.imCLM_apply]
  · simp [g5CoordOfSpatial, g5SpatialOfCoord]

private theorem g5SpatialOfCoord_coordOfSpatial (q : G5Spatial) :
    g5SpatialOfCoord (g5CoordOfSpatial q) = q := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext j
  fin_cases j <;> simp [g5SpatialOfCoord, g5CoordOfSpatial]

private theorem g5SpatialOfCoord_contDiff : ContDiff ℝ ∞ g5SpatialOfCoord := by
  have hvec : ContDiff ℝ ∞ (fun c : ℂ × ℝ => ![c.1.re, c.1.im, c.2]) := by
    apply contDiff_pi.2
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun c : ℂ × ℝ => Complex.reCLM c.1)
      exact Complex.reCLM.contDiff.comp contDiff_fst
    · change ContDiff ℝ ∞ (fun c : ℂ × ℝ => Complex.imCLM c.1)
      exact Complex.imCLM.contDiff.comp contDiff_fst
    · change ContDiff ℝ ∞ (fun c : ℂ × ℝ => c.2)
      exact contDiff_snd
  have hlp : ContDiff ℝ ∞ (fun v : Fin 3 → ℝ => (WithLp.toLp 2 v : G5Spatial)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff
  exact hlp.comp hvec

private theorem g5CoordOfSpatial_contDiff : ContDiff ℝ ∞ g5CoordOfSpatial := by
  let E : G5Spatial ≃L[ℝ] (Fin 3 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hzero : ContDiff ℝ ∞ (fun q : G5Spatial => E q 0) := by fun_prop
  have hone : ContDiff ℝ ∞ (fun q : G5Spatial => E q 1) := by fun_prop
  have htwo : ContDiff ℝ ∞ (fun q : G5Spatial => E q 2) := by fun_prop
  have hcomplex : ContDiff ℝ ∞ (fun q : G5Spatial =>
      ((E q 0 : ℝ) : ℂ) + Complex.I * (E q 1 : ℂ)) := by
    have h0 : ContDiff ℝ ∞ (fun q : G5Spatial => ((E q 0 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hzero
    have h1 : ContDiff ℝ ∞ (fun q : G5Spatial => ((E q 1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hone
    exact h0.add (contDiff_const.mul h1)
  have hEq : g5CoordOfSpatial = fun q =>
      (((E q 0 : ℝ) : ℂ) + Complex.I * (E q 1 : ℂ), E q 2) := by
    funext q
    apply Prod.ext
    · rfl
    · rfl
  rw [hEq]
  exact hcomplex.prodMk htwo

private def g5EuclideanPos : Set G5Spatial := {q | 0 < q.ofLp 2}

private theorem g5EuclideanAction_smooth (g : SL(2, ℂ)) :
    ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction g) g5EuclideanPos := by
  classical
  have hTranslation (b : ℂ) :
      ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction
        (OAI.CubicEisenstein.complexTranslation b)) g5EuclideanPos := by
    have hEq : Set.EqOn (OAI.CubicEisenstein.euclideanAction
        (OAI.CubicEisenstein.complexTranslation b))
        (fun p => p + OAI.CubicEisenstein.euclideanHorizontalTranslation b)
        g5EuclideanPos := by
      intro p hp
      exact OAI.CubicEisenstein.euclideanAction_translation b p hp
    exact (contDiffOn_id.add contDiffOn_const).congr hEq
  have hDiagonal (b : ℂ) (hb : b ≠ 0) :
      ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction
        (OAI.CubicEisenstein.complexDiagonal b hb)) g5EuclideanPos := by
    have hEq : Set.EqOn (OAI.CubicEisenstein.euclideanAction
        (OAI.CubicEisenstein.complexDiagonal b hb))
        (fun p => OAI.CubicEisenstein.euclideanComplexDilation b p)
        g5EuclideanPos := by
      intro p hp
      exact OAI.CubicEisenstein.euclideanAction_diagonal b hb p hp
    exact (OAI.CubicEisenstein.euclideanComplexDilation b).contDiff.contDiffOn.congr hEq
  have hWeyl : ContDiffOn ℝ ∞
      (OAI.CubicEisenstein.euclideanAction OAI.CubicEisenstein.complexWeyl) g5EuclideanPos := by
    have hInv : ContDiffOn ℝ ∞ OAI.CubicEisenstein.euclideanInversion g5EuclideanPos := by
      apply ContDiffOn.inversion (c := fun _ : G5Spatial => (0 : G5Spatial))
        (R := fun _ : G5Spatial => (1 : ℝ)) (x := id)
      · fun_prop
      · fun_prop
      · exact contDiffOn_id
      · intro p hp hzero
        have hy := congrArg (fun q : G5Spatial => q.ofLp 2) hzero
        have hp' : 0 < p.ofLp 2 := hp
        simp at hy
        linarith
    have hRefl : ContDiff ℝ ∞ OAI.CubicEisenstein.euclideanWeylReflection :=
      OAI.CubicEisenstein.euclideanWeylReflection.contDiff
    have hComp : ContDiffOn ℝ ∞
        (fun p => OAI.CubicEisenstein.euclideanWeylReflection
          (OAI.CubicEisenstein.euclideanInversion p)) g5EuclideanPos :=
      hRefl.contDiffOn.comp hInv (fun _ _ => Set.mem_univ _)
    have hEq : Set.EqOn (OAI.CubicEisenstein.euclideanAction
        OAI.CubicEisenstein.complexWeyl)
        OAI.CubicEisenstein.euclideanWeylAction g5EuclideanPos := by
      intro p hp
      exact OAI.CubicEisenstein.euclideanAction_weyl p hp
    exact hComp.congr hEq
  have hMul (g h : SL(2, ℂ))
      (hg : ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction g) g5EuclideanPos)
      (hh : ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction h) g5EuclideanPos) :
      ContDiffOn ℝ ∞ (OAI.CubicEisenstein.euclideanAction (g * h)) g5EuclideanPos := by
    rw [OAI.CubicEisenstein.euclideanAction_mul]
    exact hg.comp hh (fun p hp => OAI.CubicEisenstein.euclideanAction_positive h p)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · obtain ⟨ha, hfactor⟩ := OAI.CubicEisenstein.complex_bruhat_zero g hc
    rw [hfactor]
    exact hMul _ _ (hDiagonal _ ha) (hTranslation _)
  · have hfactor := OAI.CubicEisenstein.complex_bruhat_nonzero g hc
    rw [hfactor]
    exact hMul _ _ (hMul _ _ (hMul _ _ (hTranslation _)
      (hDiagonal _ _)) hWeyl) (hTranslation _)

private def g5CoordAction (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F) : Coord F :=
  fun w => g5CoordOfSpatial
    (OAI.CubicEisenstein.euclideanAction (g w) (g5SpatialOfCoord (p w)))

private theorem g5CoordAction_pos (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F)
    (hp : p ∈ posSet F) : g5CoordAction g p ∈ posSet F := by
  intro w
  change 0 < (g5CoordOfSpatial _).2
  simp only [g5CoordOfSpatial]
  exact OAI.CubicEisenstein.euclideanAction_positive (g w) _

private theorem g5CoordAction_contDiffOn (g : InfinitePlace F → SL(2, ℂ)) :
    ContDiffOn ℝ ∞ (g5CoordAction g) (posSet F) := by
  classical
  apply contDiffOn_pi.2
  intro w
  have hspatial : ContDiff ℝ ∞ (fun p : Coord F => g5SpatialOfCoord (p w)) := by
    exact g5SpatialOfCoord_contDiff.comp (by fun_prop)
  have hpos : ∀ p ∈ posSet F, g5SpatialOfCoord (p w) ∈ g5EuclideanPos := by
    intro p hp
    change 0 < (g5SpatialOfCoord (p w)).ofLp 2
    simpa [g5SpatialOfCoord] using hp w
  have hact : ContDiffOn ℝ ∞
      (fun p : Coord F => OAI.CubicEisenstein.euclideanAction (g w)
        (g5SpatialOfCoord (p w))) (posSet F) :=
    (g5EuclideanAction_smooth (g w)).comp hspatial.contDiffOn hpos
  have hback : ContDiff ℝ ∞ g5CoordOfSpatial := g5CoordOfSpatial_contDiff
  exact hback.contDiffOn.comp hact (fun _ _ => Set.mem_univ _)

private theorem g5CoordsX_pos (z : X F) : coordsX F z ∈ posSet F := by
  intro w
  change 0 < height (z w)
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem g5CoordsX_ptX (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (ptX F p) = p := by
  funext w
  simp [coordsX, ptX, horiz_pt, height_pt, hp w]

private theorem g5PtX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  funext w
  exact pt_horiz_height (z w)

private theorem g5PtCoord_eq_euclideanToHyperbolic (q : G5Spatial) (hq : 0 < q.ofLp 2) :
    pt (g5CoordOfSpatial q).1 (g5CoordOfSpatial q).2 =
      OAI.CubicEisenstein.euclideanToHyperbolic q := by
  simpa only [g5CoordOfSpatial] using
    (pt_eq_upperPoint (g5CoordOfSpatial q).1 (g5CoordOfSpatial q).2 hq).trans
      (OAI.CubicEisenstein.euclideanToHyperbolic_positive q hq).symm

private theorem g5PtX_coordAction (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F)
    (hp : p ∈ posSet F) :
    ptX F (g5CoordAction g p) = actAtPlaces F g (ptX F p) := by
  funext w
  let q := g5SpatialOfCoord (p w)
  have hq : 0 < q.ofLp 2 := by simpa [q, g5SpatialOfCoord] using hp w
  change pt (g5CoordOfSpatial (OAI.CubicEisenstein.euclideanAction (g w) q)).1
      (g5CoordOfSpatial (OAI.CubicEisenstein.euclideanAction (g w) q)).2 =
    (g w) • pt (p w).1 (p w).2
  rw [← g5CoordOfSpatial_spatialOfCoord (p w)]
  rw [g5PtCoord_eq_euclideanToHyperbolic _
      (OAI.CubicEisenstein.euclideanAction_positive (g w) q),
    g5PtCoord_eq_euclideanToHyperbolic q hq]
  change OAI.CubicEisenstein.euclideanToHyperbolic
      (OAI.CubicEisenstein.hyperbolicEuclideanCoordinates
        ((g w) • OAI.CubicEisenstein.euclideanToHyperbolic q)) = _
  exact OAI.CubicEisenstein.euclideanToHyperbolic_coordinates _

theorem g5IsSmoothX_action (g : InfinitePlace F → SL(2, ℂ))
    (f : X F → ℂ) (hf : IsSmoothX F f) :
    IsSmoothX F (fun z => f (actAtPlaces F g z)) := by
  change ContDiffOn ℝ ∞ (fun p => f (actAtPlaces F g (ptX F p))) (posSet F)
  have hcomp : ContDiffOn ℝ ∞
      ((fun p => f (ptX F p)) ∘ g5CoordAction g) (posSet F) :=
    hf.comp (g5CoordAction_contDiffOn g)
      (fun p hp => g5CoordAction_pos g p hp)
  apply hcomp.congr
  intro p hp
  change f (actAtPlaces F g (ptX F p)) = f (ptX F (g5CoordAction g p))
  rw [← g5PtX_coordAction g p hp]

private theorem g5CoordsX_continuous : Continuous (coordsX F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, hesymm⟩ := hchart
  have hEq : coordsX F = fun z => (e.symm z).1 := by
    funext z
    exact (hesymm z).symm
  rw [hEq]
  exact continuous_subtype_val.comp e.symm.continuous

private theorem g5PtX_continuousOn : ContinuousOn (ptX F) (posSet F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, he, _⟩ := hchart
  have hsub : Continuous (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1) := by
    have hEq : (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1) = e := by
      funext p
      exact (he p).symm
    rw [hEq]
    exact e.continuous
  exact continuousOn_iff_continuous_restrict.2 hsub

private def g5ZeroExtend (u : Coord F → ℂ) (p : Coord F) : ℂ :=
  if hp : p ∈ posSet F then u p else 0

private theorem g5ZeroExtend_contDiff (u : Coord F → ℂ) (C : Set (Coord F))
    (hU : IsOpen (posSet F)) (hUu : ContDiffOn ℝ ∞ u (posSet F))
    (hC : IsCompact C) (hCsub : C ⊆ posSet F)
    (hSupport : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C) :
    ContDiff ℝ ∞ (g5ZeroExtend u) := by
  apply contDiff_iff_contDiffAt.2
  intro p
  by_cases hp : p ∈ posSet F
  · have hu := hUu.contDiffAt (hU.mem_nhds hp)
    have heq : (g5ZeroExtend u) =ᶠ[𝓝 p] u := by
      filter_upwards [hU.mem_nhds hp] with q hq
      simp [g5ZeroExtend, hq]
    exact hu.congr_of_eventuallyEq heq
  · have hpC : p ∉ C := by
      intro hpC
      exact hp (hCsub hpC)
    have hnhds : Cᶜ ∈ 𝓝 p := hC.isClosed.isOpen_compl.mem_nhds hpC
    have heq : (g5ZeroExtend u) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
      filter_upwards [hnhds] with q hq
      by_cases hqU : q ∈ posSet F
      · have hzero : u q = 0 := by
          by_contra hne
          exact hq (hSupport ⟨hqU, hne⟩)
        simp [g5ZeroExtend, hqU, hzero]
      · simp [g5ZeroExtend, hqU]
    have hz : ContDiffAt ℝ ∞ (fun _ : Coord F => (0 : ℂ)) p := contDiffAt_const
    exact hz.congr_of_eventuallyEq heq

private theorem g5ZeroExtend_tsupport_subset (u : Coord F → ℂ) (C : Set (Coord F))
    (hC : IsCompact C) (hSupport : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C) :
    tsupport (g5ZeroExtend u) ⊆ C := by
  change closure (Function.support (g5ZeroExtend u)) ⊆ C
  apply closure_minimal
  · intro p hp
    have hne : g5ZeroExtend u p ≠ 0 := by simpa [Function.mem_support] using hp
    by_cases hpos : p ∈ posSet F
    · exact hSupport ⟨hpos, by simpa [g5ZeroExtend, hpos] using hne⟩
    · simp [g5ZeroExtend, hpos] at hne
  · exact hC.isClosed

private theorem g5ZeroExtend_hasCompactSupport (u : Coord F → ℂ) (C : Set (Coord F))
    (hC : IsCompact C) (hSupport : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C) :
    HasCompactSupport (g5ZeroExtend u) := by
  exact hC.of_isClosed_subset (isClosed_tsupport _)
    (g5ZeroExtend_tsupport_subset u C hC hSupport)

private theorem g5ZeroExtend_fderiv_eq (u : Coord F → ℂ) (p : Coord F)
    (hU : IsOpen (posSet F)) (hp : p ∈ posSet F) (e : Coord F) :
    fderiv ℝ (g5ZeroExtend u) p e = fderiv ℝ u p e := by
  have heq : (g5ZeroExtend u) =ᶠ[𝓝 p] u := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simp [g5ZeroExtend, hq]
  exact congrArg (fun L : Coord F →L[ℝ] ℂ => L e)
    (Filter.EventuallyEq.fderiv_eq heq)

private theorem g5ZeroExtend_fderiv_zero_of_notMem (u : Coord F → ℂ)
    (C : Set (Coord F)) (hC : IsCompact C)
    (hSupport : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C)
    (p : Coord F) (hp : p ∉ C) (e : Coord F) :
    fderiv ℝ (g5ZeroExtend u) p e = 0 := by
  have hnot : p ∉ tsupport (g5ZeroExtend u) := fun ht => hp
    (g5ZeroExtend_tsupport_subset u C hC hSupport ht)
  have hzero := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simpa using congrArg (fun L : Coord F →L[ℝ] ℂ => L e) hzero

private theorem g5ZeroExtend_continuous (u : Coord F → ℂ) (C : Set (Coord F))
    (hU : IsOpen (posSet F)) (hUu : ContinuousOn u (posSet F))
    (hC : IsCompact C) (hCsub : C ⊆ posSet F)
    (hSupport : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C) :
    Continuous (g5ZeroExtend u) := by
  apply continuous_iff_continuousAt.2
  intro p
  by_cases hp : p ∈ posSet F
  · have hu := hUu.continuousAt (hU.mem_nhds hp)
    have heq : (g5ZeroExtend u) =ᶠ[𝓝 p] u := by
      filter_upwards [hU.mem_nhds hp] with q hq
      simp [g5ZeroExtend, hq]
    exact hu.congr_of_eventuallyEq heq
  · have hpC : p ∉ C := by
      intro hpC
      exact hp (hCsub hpC)
    have hnhds : Cᶜ ∈ 𝓝 p := hC.isClosed.isOpen_compl.mem_nhds hpC
    have heq : (g5ZeroExtend u) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
      filter_upwards [hnhds] with q hq
      by_cases hqU : q ∈ posSet F
      · have hzero : u q = 0 := by
          by_contra hne
          exact hq (hSupport ⟨hqU, hne⟩)
        simp [g5ZeroExtend, hqU, hzero]
      · simp [g5ZeroExtend, hqU]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem g5PosSet_isOpen : IsOpen (posSet F) := by
  have hc : ∀ w : InfinitePlace F, Continuous (fun p : Coord F => (p w).2) := by
    intro w
    fun_prop
  have heq : posSet F = ⋂ w : InfinitePlace F, {p : Coord F | 0 < (p w).2} := by
    ext p
    simp [posSet]
  rw [heq]
  exact isOpen_iInter_of_finite fun w : InfinitePlace F =>
    isOpen_lt (continuous_const : Continuous fun _ : Coord F => (0 : ℝ)) (hc w)

private theorem g5Continuous_from_chart {β : Type*} [TopologicalSpace β]
    (f : X F → β)
    (hf : ContinuousOn (fun p : Coord F => f (ptX F p)) (posSet F)) : Continuous f := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, hesymm⟩ := hchart
  let fsub : {p : Coord F // p ∈ posSet F} → β := fun p => f (ptX F p.1)
  have hfsub : Continuous fsub :=
    hf.comp_continuous continuous_subtype_val (fun p => p.property)
  have hEq : fsub ∘ e.symm = f := by
    funext z
    change f (ptX F ((e.symm z).1)) = f z
    rw [hesymm z, g5PtX_coordsX]
  rw [← hEq]
  exact hfsub.comp e.symm.continuous

private theorem g5SmoothX_continuous (f : X F → ℂ) (hf : IsSmoothX F f) : Continuous f :=
  g5Continuous_from_chart f hf.continuousOn

private theorem g5PlaceGradient_continuous (f : X F → ℂ) (hf : IsSmoothX F f)
    (w : InfinitePlace F) (j : Fin 3) :
    Continuous (fun z => placeGradient F w f z j) := by
  let u : Coord F → ℂ := fun p => f (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hderiv : ContinuousOn (fderiv ℝ u) (posSet F) :=
    hu.continuousOn_fderiv_of_isOpen g5PosSet_isOpen (by norm_num)
  have hy : ContinuousOn (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
    have hr : ContinuousOn (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    exact Complex.continuous_ofReal.comp_continuousOn hr
  have hgrad : ContinuousOn
      (fun p => fderiv ℝ u p (placeDirection F w j)) (posSet F) := by
    have heval : Continuous (fun L : Coord F →L[ℝ] ℂ => L (placeDirection F w j)) := by
      fun_prop
    exact heval.comp_continuousOn hderiv
  let L : Coord F → ℂ := fun p =>
    ((p w).2 : ℂ) * fderiv ℝ u p (placeDirection F w j)
  have hL : ContinuousOn L (posSet F) := by
    dsimp [L]
    exact hy.mul hgrad
  have hEq : Set.EqOn (fun p => placeGradient F w f (ptX F p) j) L (posSet F) := by
    intro p hp
    dsimp [L, placeGradient]
    rw [g5CoordsX_ptX p hp]
    rfl
  exact g5Continuous_from_chart (fun z => placeGradient F w f z j)
    (hL.congr fun p hp => hEq hp)

private theorem g5PartialLap_continuous (f : X F → ℂ) (hf : IsSmoothX F f)
    (w : InfinitePlace F) : Continuous (fun z => partialLap F w f z) := by
  let u : Coord F → ℂ := fun p => f (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hderiv : ContinuousOn (fderiv ℝ u) (posSet F) :=
    hu.continuousOn_fderiv_of_isOpen g5PosSet_isOpen (by norm_num)
  have hsecond : ContinuousOn (iteratedFDeriv ℝ 2 u) (posSet F) :=
    ContinuousOn.continuousOn_iteratedFDeriv hu g5PosSet_isOpen (by norm_num)
  have hy : ContinuousOn (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
    have hr : ContinuousOn (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    exact Complex.continuous_ofReal.comp_continuousOn hr
  have hgrad (j : Fin 3) : ContinuousOn
      (fun p => fderiv ℝ u p (placeDirection F w j)) (posSet F) := by
    have heval : Continuous (fun L : Coord F →L[ℝ] ℂ => L (placeDirection F w j)) := by
      fun_prop
    exact heval.comp_continuousOn hderiv
  have hhess (j : Fin 3) : ContinuousOn
      (fun p => iteratedFDeriv ℝ 2 u p
        ![placeDirection F w j, placeDirection F w j]) (posSet F) := by
    have heval : Continuous
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Coord F) ℂ =>
          L ![placeDirection F w j, placeDirection F w j]) := by
      fun_prop
    exact heval.comp_continuousOn hsecond
  let L : Coord F → ℂ := fun p =>
    ((p w).2 : ℂ) * fderiv ℝ u p (placeDirection F w 2) -
      ((p w).2 : ℂ) ^ 2 *
        (iteratedFDeriv ℝ 2 u p ![placeDirection F w 0, placeDirection F w 0] +
          iteratedFDeriv ℝ 2 u p ![placeDirection F w 1, placeDirection F w 1] +
          iteratedFDeriv ℝ 2 u p ![placeDirection F w 2, placeDirection F w 2])
  have hL : ContinuousOn L (posSet F) := by
    dsimp [L]
    have hsum : ContinuousOn (fun p =>
        iteratedFDeriv ℝ 2 u p ![placeDirection F w 0, placeDirection F w 0] +
          iteratedFDeriv ℝ 2 u p ![placeDirection F w 1, placeDirection F w 1] +
          iteratedFDeriv ℝ 2 u p ![placeDirection F w 2, placeDirection F w 2])
        (posSet F) := by
      exact ((hhess 0).add (hhess 1)).add (hhess 2)
    exact hy.mul (hgrad 2) |>.sub (hy.pow 2 |>.mul hsum)
  have hEq : Set.EqOn (fun p => partialLap F w f (ptX F p)) L (posSet F) := by
    intro p hp
    have hcoords := g5CoordsX_ptX p hp
    dsimp [partialLap]
    simp only [Function.comp_def]
    rw [hcoords]
    rfl
  exact g5Continuous_from_chart (fun z => partialLap F w f z)
    (hL.congr fun p hp => hEq hp)

private def g5HeightCLM (v : InfinitePlace F) : Coord F →L[ℝ] ℝ where
  toLinearMap :=
    { toFun := fun p => (p v).2
      map_add' := by intro p q; simp
      map_smul' := by intro c p; simp [smul_eq_mul] }
  cont := by fun_prop

private theorem g5HeightCLM_fderiv (v : InfinitePlace F) (p : Coord F) :
    fderiv ℝ (fun q : Coord F => (q v).2) p = g5HeightCLM v := by
  simpa [g5HeightCLM] using (g5HeightCLM v).hasFDerivAt.fderiv

private theorem g5HeightCLM_placeDirection (v w : InfinitePlace F) (j : Fin 3) :
    g5HeightCLM v (placeDirection F w j) = if j = 2 ∧ v = w then 1 else 0 := by
  by_cases hv : v = w
  · subst v
    fin_cases j <;> simp [g5HeightCLM, placeDirection]
  · fin_cases j <;> simp [g5HeightCLM, placeDirection, hv]

private def g5Density (p : Coord F) : ℝ :=
  ∏ v : InfinitePlace F, ((p v).2 ^ 3)⁻¹

private def g5Rest (w : InfinitePlace F) (p : Coord F) : ℝ :=
  ∏ v ∈ Finset.univ.erase w, ((p v).2 ^ 3)⁻¹

private def g5Weight (w : InfinitePlace F) (p : Coord F) : ℝ :=
  ((p w).2)⁻¹ * g5Rest w p

private theorem g5InvCube_contDiffOn (v : InfinitePlace F) :
    ContDiffOn ℝ ∞ (fun p : Coord F => ((p v).2 ^ 3)⁻¹) (posSet F) := by
  have hy : ContDiff ℝ ∞ (fun p : Coord F => (p v).2) := by
    change ContDiff ℝ ∞ (g5HeightCLM v)
    exact (g5HeightCLM v).contDiff
  exact (hy.contDiffOn.pow 3).inv fun p hp => pow_ne_zero 3 (ne_of_gt (hp v))

private theorem g5ProdInvCube_contDiffOn (s : Finset (InfinitePlace F)) :
    ContDiffOn ℝ ∞ (fun p : Coord F => ∏ v ∈ s, ((p v).2 ^ 3)⁻¹) (posSet F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord F => (1 : ℝ)) _)
  | @insert v s hv ih =>
      simpa [Finset.prod_insert, hv, mul_comm] using (g5InvCube_contDiffOn (F := F) v).mul ih

private theorem g5Density_contDiffOn :
    ContDiffOn ℝ ∞ (g5Density (F := F)) (posSet F) := by
  change ContDiffOn ℝ ∞ (fun p : Coord F => ∏ v ∈ Finset.univ, ((p v).2 ^ 3)⁻¹)
    (posSet F)
  exact g5ProdInvCube_contDiffOn (F := F) Finset.univ

private theorem g5Rest_contDiffOn (w : InfinitePlace F) :
    ContDiffOn ℝ ∞ (g5Rest w) (posSet F) := by
  change ContDiffOn ℝ ∞
    (fun p : Coord F => ∏ v ∈ Finset.univ.erase w, ((p v).2 ^ 3)⁻¹) (posSet F)
  exact g5ProdInvCube_contDiffOn (F := F) (Finset.univ.erase w)

private theorem g5Weight_contDiffOn (w : InfinitePlace F) :
    ContDiffOn ℝ ∞ (g5Weight w) (posSet F) := by
  have hy : ContDiff ℝ ∞ (fun p : Coord F => (p w).2) := by
    change ContDiff ℝ ∞ (g5HeightCLM w)
    exact (g5HeightCLM w).contDiff
  have hbase : ContDiffOn ℝ ∞ (fun p : Coord F => ((p w).2)⁻¹) (posSet F) :=
    hy.contDiffOn.inv fun p hp => ne_of_gt (hp w)
  exact hbase.mul (g5Rest_contDiffOn (F := F) w)

private theorem g5Density_continuousOn :
    ContinuousOn (g5Density (F := F)) (posSet F) :=
  g5Density_contDiffOn.continuousOn

private theorem g5Inv_fderiv_apply (v : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) (e : Coord F) :
    fderiv ℝ (fun q : Coord F => ((q v).2)⁻¹) p e =
      -(((p v).2 ^ 2)⁻¹) * g5HeightCLM v e := by
  have hy : (p v).2 ≠ 0 := ne_of_gt (hp v)
  have houter : DifferentiableAt ℝ (fun t : ℝ => t⁻¹) ((p v).2) := differentiableAt_inv hy
  have hinner : DifferentiableAt ℝ (fun q : Coord F => (q v).2) p :=
    (g5HeightCLM v).differentiableAt
  have hcomp : (fun q : Coord F => ((q v).2)⁻¹) =
      (fun t : ℝ => t⁻¹) ∘ (fun q : Coord F => (q v).2) := rfl
  rw [hcomp, fderiv_comp p houter hinner, fderiv_inv, g5HeightCLM_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  ring

private theorem g5HeightCube_fderiv (v : InfinitePlace F) (p : Coord F) :
    fderiv ℝ (fun q : Coord F => (q v).2 ^ 3) p =
      (3 * (p v).2 ^ 2) • g5HeightCLM v := by
  have hlin : DifferentiableAt ℝ (fun q : Coord F => (q v).2) p :=
    (g5HeightCLM v).differentiableAt
  have hpow := fderiv_pow 3 hlin
  rw [g5HeightCLM_fderiv] at hpow
  have hfun : ((fun q : Coord F => (q v).2) ^ 3) =
      (fun q : Coord F => (q v).2 ^ 3) := by
    funext q
    rfl
  rw [hfun] at hpow
  simpa [smul_eq_mul] using hpow

private theorem g5InvCube_fderiv_apply (v : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) (e : Coord F) :
    fderiv ℝ (fun q : Coord F => ((q v).2 ^ 3)⁻¹) p e =
      -(((p v).2 ^ 3) ^ 2)⁻¹ * (3 * (p v).2 ^ 2) * g5HeightCLM v e := by
  have hy : (p v).2 ≠ 0 := ne_of_gt (hp v)
  have houter : DifferentiableAt ℝ (fun t : ℝ => t⁻¹) ((p v).2 ^ 3) :=
    differentiableAt_inv (pow_ne_zero 3 hy)
  have hinner : DifferentiableAt ℝ (fun q : Coord F => (q v).2 ^ 3) p :=
    (g5HeightCLM v).differentiableAt.pow 3
  have hcomp : (fun q : Coord F => ((q v).2 ^ 3)⁻¹) =
      (fun t : ℝ => t⁻¹) ∘ (fun q : Coord F => (q v).2 ^ 3) := rfl
  rw [hcomp, fderiv_comp p houter hinner, fderiv_inv, g5HeightCube_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem g5Rest_fderiv_apply (w : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) (j : Fin 3) :
    fderiv ℝ (g5Rest w) p (placeDirection F w j) = 0 := by
  classical
  have hdiff (v : InfinitePlace F) (hv : v ∈ Finset.univ.erase w) :
      DifferentiableAt ℝ (fun q : Coord F => ((q v).2 ^ 3)⁻¹) p := by
    exact (g5InvCube_contDiffOn (F := F) v).differentiableOn (by simp) |>.differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  change fderiv ℝ
      (fun p : Coord F => ∏ v ∈ Finset.univ.erase w, ((p v).2 ^ 3)⁻¹) p
      (placeDirection F w j) = 0
  rw [fderiv_finsetProd hdiff, ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro v hv
  have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g5InvCube_fderiv_apply v p hp (placeDirection F w j)]
  simp [g5HeightCLM_placeDirection, hvw]

private theorem g5Weight_fderiv_apply (w : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) (j : Fin 3) :
    fderiv ℝ (g5Weight w) p (placeDirection F w j) =
      (if j = 2 then -(((p w).2 ^ 2)⁻¹) * g5Rest w p else 0) := by
  have hy : (p w).2 ≠ 0 := ne_of_gt (hp w)
  have hbase : DifferentiableAt ℝ (fun q : Coord F => ((q w).2)⁻¹) p :=
    differentiableAt_inv hy |>.comp p (g5HeightCLM w).differentiableAt
  have hrest : DifferentiableAt ℝ (g5Rest w) p :=
    (g5Rest_contDiffOn (F := F) w).differentiableOn (by simp) |>.differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  change fderiv ℝ
      ((fun q : Coord F => ((q w).2)⁻¹) * g5Rest w) p
      (placeDirection F w j) = _
  rw [fderiv_mul hbase hrest]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g5Inv_fderiv_apply w p hp (placeDirection F w j),
    g5Rest_fderiv_apply w p hp j]
  simp [g5HeightCLM_placeDirection, mul_comm]

private theorem g5CoordsX_injective : Function.Injective (coordsX F) := by
  intro z z' h
  calc
    z = ptX F (coordsX F z) := (g5PtX_coordsX z).symm
    _ = ptX F (coordsX F z') := by rw [h]
    _ = z' := g5PtX_coordsX z'

private theorem g5Compact_isClosed (K : Set (X F)) (hK : IsCompact K) : IsClosed K := by
  let C : Set (Coord F) := coordsX F '' K
  have hC : IsCompact C := hK.image g5CoordsX_continuous
  have hEq : K = (coordsX F) ⁻¹' C := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · intro hz
      rcases hz with ⟨z', hzK, hcoord⟩
      have hzEq : z = z' := g5CoordsX_injective hcoord.symm
      simpa [hzEq] using hzK
  rw [hEq]
  exact hC.isClosed.preimage g5CoordsX_continuous

private theorem g5HasCompactSupport_of_X (G : X F → ℂ)
    (hcompact : HasCompactSupportX F G) : HasCompactSupport G := by
  rcases hcompact with ⟨K, hK, hSupport⟩
  have hKclosed : IsClosed K := g5Compact_isClosed K hK
  change IsCompact (closure (Function.support G))
  apply hK.of_isClosed_subset isClosed_closure
  exact closure_minimal hSupport hKclosed

private theorem g5SecondCountableX : SecondCountableTopology (X F) := by
  have hcoord : SecondCountableTopology (Coord F) := inferInstance
  letI : SecondCountableTopology (Coord F) := hcoord
  letI : SecondCountableTopology {p : Coord F // p ∈ posSet F} := inferInstance
  obtain ⟨e, _, _⟩ := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.2.2.2.2
  exact e.symm.isEmbedding.secondCountableTopology

private theorem g5OpensMeasurableX : OpensMeasurableSpace (X F) := by
  letI : SecondCountableTopology (X F) := g5SecondCountableX (F := F)
  let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hsurj : Function.Surjective (fun x : X F => x w) := by
    intro z
    exact ⟨fun _ => z, rfl⟩
  have hq : IsOpenQuotientMap (fun x : X F => x w) :=
    ⟨hsurj, continuous_apply w, isOpenMap_eval w⟩
  letI : SecondCountableTopology H3 :=
    Topology.IsOpenQuotientMap.secondCountableTopology hq
  letI : BorelSpace H3 := instBorelSpaceH3
  letI : BorelSpace (X F) := inferInstance
  infer_instance

private theorem g5BorelSpaceX : BorelSpace (X F) := by
  letI : SecondCountableTopology (X F) := g5SecondCountableX (F := F)
  let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hsurj : Function.Surjective (fun x : X F => x w) := by
    intro z
    exact ⟨fun _ => z, rfl⟩
  have hq : IsOpenQuotientMap (fun x : X F => x w) :=
    ⟨hsurj, continuous_apply w, isOpenMap_eval w⟩
  letI : SecondCountableTopology H3 :=
    Topology.IsOpenQuotientMap.secondCountableTopology hq
  letI : BorelSpace H3 := instBorelSpaceH3
  infer_instance

private theorem g5IntegrableX (G : X F → ℂ) (hcont : Continuous G)
    (hcompact : HasCompactSupportX F G) : Integrable G (volX F) := by
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun {K} hK => (G3_volume (F := F)).2.2.1 K hK⟩
  letI : OpensMeasurableSpace (X F) := g5OpensMeasurableX (F := F)
  exact hcont.integrable_of_hasCompactSupport (g5HasCompactSupport_of_X G hcompact)

private theorem g5CoordinateIntegral (G : X F → ℂ) (hcont : Continuous G)
    (hcompact : HasCompactSupportX F G) :
    Integrable
        (g5ZeroExtend (fun q => G (ptX F q) * (g5Density (F := F) q : ℂ))) volume ∧
      ∫ z, G z ∂(volX F) =
        ∫ p, g5ZeroExtend (fun q => G (ptX F q) * (g5Density (F := F) q : ℂ)) p ∂volume := by
  classical
  rcases hcompact with ⟨K, hK, hSupportX⟩
  let C : Set (Coord F) := coordsX F '' K
  have hC : IsCompact C := by
    exact hK.image g5CoordsX_continuous
  have hCsub : C ⊆ posSet F := by
    rintro p ⟨z, hzK, rfl⟩
    exact g5CoordsX_pos z
  let u : Coord F → ℂ := fun p => G (ptX F p) * (g5Density (F := F) p : ℂ)
  have hpt : ContinuousOn (ptX F) (posSet F) := g5PtX_continuousOn
  have hJ : ContinuousOn (fun p : Coord F => (g5Density (F := F) p : ℂ)) (posSet F) := by
    exact Complex.continuous_ofReal.comp_continuousOn g5Density_continuousOn
  have hu : ContinuousOn u (posSet F) := by
    dsimp [u]
    exact (hcont.comp_continuousOn hpt).mul hJ
  have hSupportU : {p | p ∈ posSet F ∧ u p ≠ 0} ⊆ C := by
    rintro p ⟨hp, hne⟩
    have hGp : G (ptX F p) ≠ 0 := by
      intro hzero
      apply hne
      simp [u, hzero]
    have hKp : ptX F p ∈ K := hSupportX hGp
    exact ⟨ptX F p, hKp, g5CoordsX_ptX p hp⟩
  let E : Coord F → ℂ := g5ZeroExtend u
  have hEcont : Continuous E :=
    g5ZeroExtend_continuous u C g5PosSet_isOpen hu hC hCsub hSupportU
  have hEsupp : HasCompactSupport E :=
    g5ZeroExtend_hasCompactSupport u C hC hSupportU
  letI : OpensMeasurableSpace (Coord F) := by infer_instance
  have hEint : Integrable E volume := hEcont.integrable_of_hasCompactSupport hEsupp
  refine ⟨?_, ?_⟩
  · simpa [E] using hEint
  have hEintPos : Integrable E (volume.restrict (posSet F)) := hEint.restrict
  have hPosMeas : MeasurableSet (posSet F) := g5PosSet_isOpen.measurableSet
  have hGint : Integrable G (volX F) := g5IntegrableX G hcont ⟨K, hK, hSupportX⟩
  have hRe : ∫ z, (G z).re ∂(volX F) =
      ∫ p, (E p).re ∂(volume.restrict (posSet F)) := by
    calc
      _ = ∫ p, (G (ptX F p)).re * g5Density (F := F) p
          ∂(volume.restrict (posSet F)) :=
        (G3_volume (F := F)).2.1 (fun z => (G z).re) hGint.re
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hPosMeas] with p hp
        simp [E, g5ZeroExtend, u, hp, Complex.mul_re]
  have hIm : ∫ z, (G z).im ∂(volX F) =
      ∫ p, (E p).im ∂(volume.restrict (posSet F)) := by
    calc
      _ = ∫ p, (G (ptX F p)).im * g5Density (F := F) p
          ∂(volume.restrict (posSet F)) :=
        (G3_volume (F := F)).2.1 (fun z => (G z).im) hGint.im
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hPosMeas] with p hp
        simp [E, g5ZeroExtend, u, hp, Complex.mul_im]
  calc
    ∫ z, G z ∂(volX F) =
        ((∫ z, (G z).re ∂(volX F) : ℝ) : ℂ) +
          (∫ z, (G z).im ∂(volX F) : ℝ) * Complex.I := by
        exact (integral_re_add_im hGint).symm
    _ = ((∫ p, (E p).re ∂(volume.restrict (posSet F)) : ℝ) : ℂ) +
          (∫ p, (E p).im ∂(volume.restrict (posSet F)) : ℝ) * Complex.I := by
        rw [hRe, hIm]
    _ = ∫ p, E p ∂(volume.restrict (posSet F)) :=
        (integral_re_add_im hEintPos)
    _ = ∫ p, E p ∂volume := by
        have hEeq : E =ᵐ[volume] (posSet F).indicator E := by
          filter_upwards [] with p
          by_cases hp : p ∈ posSet F
          · simp [hp]
          · simp [E, g5ZeroExtend, hp]
        calc
          _ = ∫ p, (posSet F).indicator E p ∂volume := by
            rw [← integral_indicator hPosMeas]
          _ = _ := integral_congr_ae hEeq.symm

private theorem g5PiCoordVolume_isAddHaarMeasure :
    Measure.IsAddHaarMeasure
      (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hleft : Measure.IsAddLeftInvariant
      (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) := by
    constructor
    intro g
    letI : ∀ w : InfinitePlace F,
        SigmaFinite (Measure.map (fun q : ℂ × ℝ => g w + q) (volume : Measure (ℂ × ℝ))) := by
      intro w
      rw [Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := volume) (g w)]
      infer_instance
    have hmap := Measure.pi_map_pi
      (μ := fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))
      (f := fun w q => g w + q)
      (fun w => (continuous_const.add continuous_id).measurable.aemeasurable)
    calc
      Measure.map (fun p : Coord F => fun w => g w + p w)
          (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) =
        Measure.pi (fun w => Measure.map (fun q : ℂ × ℝ => g w + q) volume) := hmap
      _ = Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ))) := by
        congr 1
        funext w
        exact Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := volume) (g w)
  letI : IsFiniteMeasureOnCompacts
      (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) := by infer_instance
  letI : Measure.IsAddLeftInvariant
      (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) := hleft
  letI : Measure.IsOpenPosMeasure
      (Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ)))) := by infer_instance
  exact Measure.IsAddHaarMeasure.mk

private theorem g5CoordVolume_isAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Coord F)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hvol : (volume : Measure (Coord F)) =
      Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ))) := by
    simpa [Coord] using
      (MeasureTheory.volume_pi (α := fun _ : InfinitePlace F => ℂ × ℝ))
  rw [hvol]
  exact g5PiCoordVolume_isAddHaarMeasure (F := F)

private def g5RawSlice (w : InfinitePlace F) (j : Fin 3)
    (u φ : Coord F → ℂ) (p : Coord F) : ℂ :=
  (g5Weight w p : ℂ) * (fderiv ℝ u p (placeDirection F w j) * φ p)

private theorem g5RawSlice_contDiffOn (w : InfinitePlace F) (j : Fin 3)
    (u φ : Coord F → ℂ) (hu : ContDiffOn ℝ ∞ u (posSet F))
    (hφ : ContDiffOn ℝ ∞ φ (posSet F)) :
    ContDiffOn ℝ ∞ (g5RawSlice w j u φ) (posSet F) := by
  have hweight : ContDiffOn ℝ ∞ (fun p : Coord F => (g5Weight w p : ℂ)) (posSet F) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (g5Weight_contDiffOn (F := F) w)
  have huDeriv : ContDiffOn ℝ ∞ (fderiv ℝ u) (posSet F) :=
    hu.fderiv_of_isOpen g5PosSet_isOpen (by norm_num)
  have hD : ContDiffOn ℝ ∞
      (fun p => fderiv ℝ u p (placeDirection F w j)) (posSet F) :=
    huDeriv.clm_apply contDiffOn_const
  change ContDiffOn ℝ ∞
    (fun p => (g5Weight w p : ℂ) *
      (fderiv ℝ u p (placeDirection F w j) * φ p)) (posSet F)
  exact hweight.mul (hD.mul hφ)

private theorem g5FDeriv_ofReal (r : Coord F → ℝ) (p e : Coord F)
    (hr : DifferentiableAt ℝ r p) :
    fderiv ℝ (fun q => (r q : ℂ)) p e = ((fderiv ℝ r p e : ℝ) : ℂ) := by
  have hcomp := fderiv_comp p Complex.ofRealCLM.differentiableAt hr
  have hL := Complex.ofRealCLM.fderiv (x := r p)
  have hEq : (fun q => (r q : ℂ)) = Complex.ofRealCLM ∘ r := rfl
  rw [hEq, hcomp]
  change (fderiv ℝ Complex.ofRealCLM (r p) ∘SL fderiv ℝ r p) e = _
  rw [hL]
  rfl

private theorem g5SecondDirectional (u : Coord F → ℂ) (p e : Coord F)
    (hu : ContDiffOn ℝ ∞ u (posSet F)) (hp : p ∈ posSet F) :
    fderiv ℝ (fun q => fderiv ℝ u q e) p e =
      iteratedFDeriv ℝ 2 u p ![e, e] := by
  have huDeriv : ContDiffOn ℝ ∞ (fderiv ℝ u) (posSet F) :=
    hu.fderiv_of_isOpen g5PosSet_isOpen (by norm_num)
  have hdf : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (huDeriv.differentiableOn (by simp)).differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  have hconst : DifferentiableAt ℝ (fun _ : Coord F => e) p := by fun_prop
  change fderiv ℝ (fun q => fderiv ℝ u q e) p e = _
  rw [fderiv_clm_apply hdf hconst]
  rw [iteratedFDeriv_two_apply]
  simp

private theorem g5RawSlice_fderiv (w : InfinitePlace F) (j : Fin 3)
    (u φ : Coord F → ℂ) (p : Coord F) (hp : p ∈ posSet F)
    (hu : ContDiffOn ℝ ∞ u (posSet F)) (hφ : ContDiffOn ℝ ∞ φ (posSet F)) :
    fderiv ℝ (g5RawSlice w j u φ) p (placeDirection F w j) =
      ((if j = 2 then -(((p w).2 ^ 2)⁻¹) * g5Rest w p else 0 : ℝ) : ℂ) *
        (fderiv ℝ u p (placeDirection F w j) * φ p) +
      (g5Weight w p : ℂ) *
        (iteratedFDeriv ℝ 2 u p
            ![placeDirection F w j, placeDirection F w j] * φ p +
          fderiv ℝ u p (placeDirection F w j) *
            fderiv ℝ φ p (placeDirection F w j)) := by
  let e := placeDirection F w j
  have huDeriv : ContDiffOn ℝ ∞ (fderiv ℝ u) (posSet F) :=
    hu.fderiv_of_isOpen g5PosSet_isOpen (by norm_num)
  have hD : ContDiffOn ℝ ∞ (fun q => fderiv ℝ u q e) (posSet F) :=
    huDeriv.clm_apply contDiffOn_const
  have hUDiff : DifferentiableAt ℝ (fun q => fderiv ℝ u q e) p :=
    (hD.differentiableOn (by simp)).differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  have hφDiff : DifferentiableAt ℝ φ p :=
    (hφ.differentiableOn (by simp)).differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  have hWeightDiff : DifferentiableAt ℝ (g5Weight w) p :=
    (g5Weight_contDiffOn (F := F) w).differentiableOn (by simp) |>.differentiableAt
      (g5PosSet_isOpen.mem_nhds hp)
  have hWeightCastDiff : DifferentiableAt ℝ (fun q => (g5Weight w q : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hWeightDiff
  have hInnerDiff : DifferentiableAt ℝ
      (fun q => fderiv ℝ u q e * φ q) p := hUDiff.mul hφDiff
  have hInnerEq : (fun q : Coord F => fderiv ℝ u q e * φ q) =
      (fun q => fderiv ℝ u q e) * φ := rfl
  have hInnerFDeriv := fderiv_mul hUDiff hφDiff
  change fderiv ℝ
      ((fun q => (g5Weight w q : ℂ)) * (fun q => fderiv ℝ u q e * φ q)) p e = _
  rw [fderiv_mul hWeightCastDiff hInnerDiff]
  rw [hInnerEq, hInnerFDeriv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g5FDeriv_ofReal (g5Weight w) p e hWeightDiff,
    g5Weight_fderiv_apply w p hp j,
    g5SecondDirectional u p e hu hp]
  simp [e] <;> ring

private theorem g5IntegralDirectionalDerivative_zero (H : Coord F → ℂ)
    (hH : ContDiff ℝ ∞ H) (hcompact : HasCompactSupport H) (e : Coord F) :
    Integrable (fun p => fderiv ℝ H p e) volume ∧
      ∫ p, fderiv ℝ H p e ∂volume = 0 := by
  letI : BorelSpace (Coord F) := inferInstance
  letI : OpensMeasurableSpace (Coord F) := by infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure (Coord F)) :=
    g5CoordVolume_isAddHaarMeasure (F := F)
  have hHInt : Integrable H volume := hH.continuous.integrable_of_hasCompactSupport hcompact
  have hderivCompact : HasCompactSupport (fderiv ℝ H · e) :=
    HasCompactSupport.fderiv_apply (𝕜 := ℝ) hcompact e
  have hderivCont : Continuous (fun p : Coord F => fderiv ℝ H p e) := by
    have hdf : ContinuousOn (fderiv ℝ H) Set.univ :=
      hH.contDiffOn.continuousOn_fderiv_of_isOpen isOpen_univ (by norm_num)
    have hdf' : Continuous (fderiv ℝ H) := by
      simpa only [continuousOn_univ] using hdf
    have heval : Continuous (fun L : Coord F →L[ℝ] ℂ => L e) := by fun_prop
    exact heval.comp hdf'
  have hderivInt : Integrable (fun p : Coord F => fderiv ℝ H p e) volume :=
    hderivCont.integrable_of_hasCompactSupport hderivCompact
  refine ⟨hderivInt, ?_⟩
  have hzero : Integrable
      (fun p : Coord F => fderiv ℝ (fun _ : Coord F => (1 : ℂ)) p e * H p) volume := by
    simpa using (integrable_zero : Integrable (fun _ : Coord F => (0 : ℂ)) volume)
  have hfg' : Integrable
      (fun p : Coord F => (1 : ℂ) * fderiv ℝ H p e) volume := by
    simpa using hderivInt
  have hfg : Integrable (fun p : Coord F => (1 : ℂ) * H p) volume := by
    simpa using hHInt
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Coord F => (1 : ℂ)) (g := H) (v := e)
    hzero hfg' hfg
    (by intro p hp; simpa using (differentiableAt_const (c := (1 : ℂ)) (x := p)))
    (by intro p hp; exact hH.differentiable (by simp) p)
  calc
    ∫ p, fderiv ℝ H p e ∂volume =
        ∫ p, (1 : ℂ) * fderiv ℝ H p e ∂volume := by simp
    _ = -∫ p, fderiv ℝ (fun _ : Coord F => (1 : ℂ)) p e * H p ∂volume := hIBP
    _ = 0 := by simp

private theorem g5PartialLap_chartFormula (f : X F → ℂ) (p : Coord F)
    (hp : p ∈ posSet F) (w : InfinitePlace F) :
    partialLap F w f (ptX F p) =
      ((p w).2 : ℂ) * fderiv ℝ (fun q => f (ptX F q)) p
          (placeDirection F w 2) -
        ((p w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 0, placeDirection F w 0] +
            iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 1, placeDirection F w 1] +
            iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 2, placeDirection F w 2]) := by
  have hcoords := g5CoordsX_ptX p hp
  dsimp [partialLap]
  simp only [Function.comp_def]
  rw [hcoords]
  rfl

private theorem g5PlaceGradient_chartFormula (f : X F → ℂ) (p : Coord F)
    (hp : p ∈ posSet F) (w : InfinitePlace F) (j : Fin 3) :
    placeGradient F w f (ptX F p) j =
      ((p w).2 : ℂ) * fderiv ℝ (fun q => f (ptX F q)) p
        (placeDirection F w j) := by
  dsimp [placeGradient]
  rw [g5CoordsX_ptX p hp]
  rfl

private theorem g5Weight_eq_sq_density (w : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) :
    g5Weight w p = (p w).2 ^ 2 * g5Density p := by
  have hprod : g5Density p = ((p w).2 ^ 3)⁻¹ * g5Rest w p := by
    simpa [g5Density, g5Rest] using
      (Finset.mul_prod_erase (s := Finset.univ)
        (f := fun v : InfinitePlace F => ((p v).2 ^ 3)⁻¹) (Finset.mem_univ w)).symm
  rw [g5Weight, hprod]
  have hy : (p w).2 ≠ 0 := ne_of_gt (hp w)
  field_simp
  <;> ring

private theorem g5PlaceGradBilinear_continuous (f φ : X F → ℂ)
    (hf : IsSmoothX F f) (hφ : IsSmoothX F φ) (w : InfinitePlace F) :
    Continuous (fun z => placeGradBilinear F w f φ z) := by
  classical
  unfold placeGradBilinear
  apply continuous_finsetSum
  intro j hj
  exact (g5PlaceGradient_continuous f hf w j).mul
    (g5PlaceGradient_continuous φ hφ w j)

private theorem g5PlaceGradient_zero_of_outside_support (φ : X F → ℂ)
    (hφ : IsSmoothX F φ) (K : Set (X F)) (hK : IsCompact K)
    (hSupport : {z | φ z ≠ 0} ⊆ K) (z : X F) (hz : z ∉ K)
    (w : InfinitePlace F) (j : Fin 3) : placeGradient F w φ z j = 0 := by
  let C : Set (Coord F) := coordsX F '' K
  have hC : IsCompact C := hK.image g5CoordsX_continuous
  have hCsub : C ⊆ posSet F := by
    rintro p ⟨z', hz'K, rfl⟩
    exact g5CoordsX_pos z'
  let p := coordsX F z
  have hp : p ∈ posSet F := by simpa [p] using g5CoordsX_pos z
  have hpC : p ∉ C := by
    intro h
    rcases h with ⟨z', hz'K, hcoord⟩
    have hcoord' : coordsX F z' = coordsX F z := by simpa [p] using hcoord
    have hzEq : z' = z := g5CoordsX_injective hcoord'
    exact hz (hzEq ▸ hz'K)
  have hopen : IsOpen (posSet F ∩ Cᶜ) := g5PosSet_isOpen.inter hC.isClosed.isOpen_compl
  have hpopen : p ∈ posSet F ∩ Cᶜ := ⟨hp, hpC⟩
  let v : Coord F → ℂ := fun q => φ (ptX F q)
  have heq : v =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds hpopen] with q hq
    by_contra hne
    have hφq : φ (ptX F q) ≠ 0 := by simpa [v] using hne
    exact hq.2 ⟨ptX F q, hSupport hφq, g5CoordsX_ptX q hq.1⟩
  have hfd : fderiv ℝ v p = 0 := by
    have := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
    simpa [v] using this
  change ((coordsX F z w).2 : ℂ) * fderiv ℝ v p (placeDirection F w j) = 0
  rw [hfd]
  simp

private theorem g5PlaceGradBilinear_support_subset (f φ : X F → ℂ)
    (hf : IsSmoothX F f) (hφ : IsSmoothX F φ) (w : InfinitePlace F)
    (K : Set (X F)) (hK : IsCompact K) (hSupport : {z | φ z ≠ 0} ⊆ K) :
    {z | placeGradBilinear F w f φ z ≠ 0} ⊆ K := by
  intro z hz
  by_contra hzK
  have hgrad (j : Fin 3) : placeGradient F w φ z j = 0 :=
    g5PlaceGradient_zero_of_outside_support φ hφ K hK hSupport z hzK w j
  apply hz
  simp [placeGradBilinear, hgrad]

private theorem g5SumFinThree (t : Fin 3 → ℂ) :
    (∑ j : Fin 3, t j) = t 0 + t 1 + t 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp <;> ring

private theorem g5CoordinateDivergence (f φ : X F → ℂ)
    (hf : IsSmoothX F f) (hφ : IsSmoothX F φ)
    (w : InfinitePlace F) (p : Coord F) (hp : p ∈ posSet F) :
    partialLap F w f (ptX F p) * φ (ptX F p) * (g5Density p : ℂ) +
      ∑ j : Fin 3,
        fderiv ℝ
          (g5RawSlice w j (fun q => f (ptX F q)) (fun q => φ (ptX F q))) p
          (placeDirection F w j) =
      placeGradBilinear F w f φ (ptX F p) * (g5Density p : ℂ) := by
  let u : Coord F → ℂ := fun q => f (ptX F q)
  let v : Coord F → ℂ := fun q => φ (ptX F q)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hv : ContDiffOn ℝ ∞ v (posSet F) := hφ
  have hLap := g5PartialLap_chartFormula f p hp w
  have hWeight := g5Weight_eq_sq_density w p hp
  have hprod : g5Density p = ((p w).2 ^ 3)⁻¹ * g5Rest w p := by
    simpa [g5Density, g5Rest] using
      (Finset.mul_prod_erase (s := Finset.univ)
        (f := fun a : InfinitePlace F => ((p a).2 ^ 3)⁻¹) (Finset.mem_univ w)).symm
  have hVertical : (p w).2 * g5Density p =
      ((p w).2 ^ 2)⁻¹ * g5Rest w p := by
    rw [hprod]
    have hy : (p w).2 ≠ 0 := ne_of_gt (hp w)
    field_simp
    <;> ring
  have hy : (p w).2 ≠ 0 := ne_of_gt (hp w)
  have hsq : ((p w).2⁻¹) ^ 2 = ((p w).2 ^ 2)⁻¹ := by
    field_simp [hy]
  have hreal : (p w).2 * g5Density p = ((p w).2⁻¹) ^ 2 * g5Rest w p := by
    calc
      _ = ((p w).2 ^ 2)⁻¹ * g5Rest w p := hVertical
      _ = _ := by rw [← hsq]
  have hYJ : ((p w).2 : ℂ) * (g5Density p : ℂ) =
      (((p w).2 : ℂ)⁻¹) ^ 2 * (g5Rest w p : ℂ) := by
    exact_mod_cast hreal
  have hgrad : placeGradBilinear F w f φ (ptX F p) =
      ∑ j : Fin 3,
        (((p w).2 : ℂ) * fderiv ℝ u p (placeDirection F w j)) *
          (((p w).2 : ℂ) * fderiv ℝ v p (placeDirection F w j)) := by
    unfold placeGradBilinear
    apply Finset.sum_congr rfl
    intro j hj
    rw [g5PlaceGradient_chartFormula f p hp w j,
      g5PlaceGradient_chartFormula φ p hp w j]
  have hraw (j : Fin 3) :
      fderiv ℝ (g5RawSlice w j u v) p (placeDirection F w j) =
        ((if j = 2 then -(((p w).2 ^ 2)⁻¹) * g5Rest w p else 0 : ℝ) : ℂ) *
          (fderiv ℝ u p (placeDirection F w j) * v p) +
        (g5Weight w p : ℂ) *
          (iteratedFDeriv ℝ 2 u p
              ![placeDirection F w j, placeDirection F w j] * v p +
            fderiv ℝ u p (placeDirection F w j) *
              fderiv ℝ v p (placeDirection F w j)) := by
    simpa [u, v] using g5RawSlice_fderiv w j u v p hp hu hv
  rw [hLap, hgrad]
  change _ + (∑ j : Fin 3,
      fderiv ℝ (g5RawSlice w j u v) p (placeDirection F w j)) = _
  have hrawsum :
      (∑ j : Fin 3, fderiv ℝ (g5RawSlice w j u v) p (placeDirection F w j)) =
        ∑ j : Fin 3,
          (((if j = 2 then -(((p w).2 ^ 2)⁻¹) * g5Rest w p else 0 : ℝ) : ℂ) *
              (fderiv ℝ u p (placeDirection F w j) * v p) +
            (g5Weight w p : ℂ) *
              (iteratedFDeriv ℝ 2 u p
                  ![placeDirection F w j, placeDirection F w j] * v p +
                fderiv ℝ u p (placeDirection F w j) *
                  fderiv ℝ v p (placeDirection F w j))) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hraw j
  rw [hrawsum]
  simp_rw [g5SumFinThree]
  simp
  rw [hWeight]
  push_cast
  linear_combination
    (fderiv ℝ u p (placeDirection F w 2) * v p) * hYJ

theorem g5GreenFirst (f φ : X F → ℂ) (hf : IsSmoothX F f)
    (hφ : IsSmoothX F φ) (hcompact : HasCompactSupportX F φ)
    (w : InfinitePlace F) :
    ∫ z, partialLap F w f z * φ z ∂(volX F) =
      ∫ z, placeGradBilinear F w f φ z ∂(volX F) := by
  classical
  rcases hcompact with ⟨K, hK, hSupportX⟩
  let C : Set (Coord F) := coordsX F '' K
  have hC : IsCompact C := hK.image g5CoordsX_continuous
  have hCsub : C ⊆ posSet F := by
    rintro p ⟨z, hzK, rfl⟩
    exact g5CoordsX_pos z
  let u : Coord F → ℂ := fun p => f (ptX F p)
  let v : Coord F → ℂ := fun p => φ (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hv : ContDiffOn ℝ ∞ v (posSet F) := hφ
  have hVSupport : {p | p ∈ posSet F ∧ v p ≠ 0} ⊆ C := by
    rintro p ⟨hp, hne⟩
    exact ⟨ptX F p, hSupportX (by simpa [v] using hne), g5CoordsX_ptX p hp⟩
  let raw : Fin 3 → Coord F → ℂ := fun j => g5RawSlice w j u v
  let H : Fin 3 → Coord F → ℂ := fun j => g5ZeroExtend (raw j)
  have hRawSupport (j : Fin 3) : {p | p ∈ posSet F ∧ raw j p ≠ 0} ⊆ C := by
    intro p hp
    have hne : v p ≠ 0 := by
      intro hzero
      apply hp.2
      simp [raw, g5RawSlice, hzero]
    exact hVSupport ⟨hp.1, hne⟩
  have hRawSmooth (j : Fin 3) : ContDiffOn ℝ ∞ (raw j) (posSet F) := by
    simpa [raw] using g5RawSlice_contDiffOn w j u v hu hv
  have hHSmooth (j : Fin 3) : ContDiff ℝ ∞ (H j) := by
    simpa [H, raw] using g5ZeroExtend_contDiff (raw j) C g5PosSet_isOpen
      (hRawSmooth j) hC hCsub (hRawSupport j)
  have hHCompact (j : Fin 3) : HasCompactSupport (H j) := by
    exact g5ZeroExtend_hasCompactSupport (raw j) C hC (hRawSupport j)
  have hHZero (j : Fin 3) :
      Integrable (fun p => fderiv ℝ (H j) p (placeDirection F w j)) volume ∧
        ∫ p, fderiv ℝ (H j) p (placeDirection F w j) ∂volume = 0 :=
    g5IntegralDirectionalDerivative_zero (H j) (hHSmooth j) (hHCompact j)
      (placeDirection F w j)
  let gLap : X F → ℂ := fun z => partialLap F w f z * φ z
  let gGrad : X F → ℂ := fun z => placeGradBilinear F w f φ z
  have hGLcont : Continuous gLap := by
    exact (g5PartialLap_continuous f hf w).mul (g5SmoothX_continuous φ hφ)
  have hGLsupport : {z | gLap z ≠ 0} ⊆ K := by
    intro z hz
    have hφz : φ z ≠ 0 := by
      intro hzero
      apply hz
      simp [gLap, hzero]
    exact hSupportX hφz
  have hGLcompact : HasCompactSupportX F gLap := ⟨K, hK, hGLsupport⟩
  have hGRcont : Continuous gGrad := g5PlaceGradBilinear_continuous f φ hf hφ w
  have hGRsupport : {z | gGrad z ≠ 0} ⊆ K :=
    g5PlaceGradBilinear_support_subset f φ hf hφ w K hK hSupportX
  have hGRcompact : HasCompactSupportX F gGrad := ⟨K, hK, hGRsupport⟩
  let eLap : Coord F → ℂ := g5ZeroExtend
    (fun p => gLap (ptX F p) * (g5Density (F := F) p : ℂ))
  let eGrad : Coord F → ℂ := g5ZeroExtend
    (fun p => gGrad (ptX F p) * (g5Density (F := F) p : ℂ))
  have hELTransfer := g5CoordinateIntegral gLap hGLcont hGLcompact
  have hERTransfer := g5CoordinateIntegral gGrad hGRcont hGRcompact
  have hELInt : Integrable eLap volume := by simpa [eLap] using hELTransfer.1
  have hERInt : Integrable eGrad volume := by simpa [eGrad] using hERTransfer.1
  have hELEq : (∫ z, gLap z ∂(volX F)) = ∫ p, eLap p ∂volume := by
    simpa [eLap] using hELTransfer.2
  have hEREq : (∫ z, gGrad z ∂(volX F)) = ∫ p, eGrad p ∂volume := by
    simpa [eGrad] using hERTransfer.2
  have hDInt (j : Fin 3) :
      Integrable (fun p => fderiv ℝ (H j) p (placeDirection F w j)) volume :=
    (hHZero j).1
  have hSumInt : Integrable
      (fun p => ∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j)) volume := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hDInt j
  have hSumZero :
      ∫ p, ∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j) ∂volume = 0 := by
    calc
      _ = ∑ j : Fin 3,
          ∫ p, fderiv ℝ (H j) p (placeDirection F w j) ∂volume := by
            simpa using integral_finsetSum Finset.univ (fun j hj => hDInt j)
      _ = 0 := by simp [fun j => (hHZero j).2]
  have hPoint : ∀ p,
      eLap p + (∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j)) = eGrad p := by
    intro p
    by_cases hp : p ∈ posSet F
    · have hELp : eLap p = gLap (ptX F p) * (g5Density (F := F) p : ℂ) := by
        simp [eLap, g5ZeroExtend, hp]
      have hERp : eGrad p = gGrad (ptX F p) * (g5Density (F := F) p : ℂ) := by
        simp [eGrad, g5ZeroExtend, hp]
      have hsum :
          (∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j)) =
            ∑ j : Fin 3, fderiv ℝ (raw j) p (placeDirection F w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact g5ZeroExtend_fderiv_eq (raw j) p g5PosSet_isOpen hp
          (placeDirection F w j)
      rw [hELp, hERp, hsum]
      simpa [gLap, gGrad, raw, u, v] using g5CoordinateDivergence f φ hf hφ w p hp
    · have hpC : p ∉ C := by
        intro hpC
        exact hp (hCsub hpC)
      have hELp : eLap p = 0 := by simp [eLap, g5ZeroExtend, hp]
      have hERp : eGrad p = 0 := by simp [eGrad, g5ZeroExtend, hp]
      have hDzero (j : Fin 3) : fderiv ℝ (H j) p (placeDirection F w j) = 0 :=
        g5ZeroExtend_fderiv_zero_of_notMem (raw j) C hC (hRawSupport j) p hpC
          (placeDirection F w j)
      simp [hELp, hERp, hDzero]
  have hPointAE :
      (fun p => eLap p + ∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j)) =ᵐ[volume] eGrad :=
    Filter.Eventually.of_forall hPoint
  have hInt :
      (∫ p, eLap p ∂volume) +
          (∫ p, ∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j) ∂volume) =
        ∫ p, eGrad p ∂volume := by
    calc
      _ = ∫ p, eLap p + ∑ j : Fin 3, fderiv ℝ (H j) p (placeDirection F w j) ∂volume :=
        (integral_add hELInt hSumInt).symm
      _ = _ := integral_congr_ae hPointAE
  rw [hSumZero] at hInt
  calc
    ∫ z, partialLap F w f z * φ z ∂(volX F) = ∫ p, eLap p ∂volume := by
      simpa [gLap] using hELEq
    _ = ∫ p, eGrad p ∂volume := by simpa using hInt
    _ = ∫ z, placeGradBilinear F w f φ z ∂(volX F) := by
      symm
      simpa [gGrad] using hEREq

private theorem g5PlaceGradBilinear_comm (f φ : X F → ℂ) (w : InfinitePlace F)
    (z : X F) :
    placeGradBilinear F w f φ z = placeGradBilinear F w φ f z := by
  unfold placeGradBilinear
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem g5GreenSymmetry (f φ : X F → ℂ) (hf : IsSmoothX F f)
    (hφ : IsSmoothX F φ) (hfcompact : HasCompactSupportX F f)
    (hφcompact : HasCompactSupportX F φ) (w : InfinitePlace F) :
    ∫ z, partialLap F w f z * φ z ∂(volX F) =
      ∫ z, f z * partialLap F w φ z ∂(volX F) := by
  have h1 := g5GreenFirst f φ hf hφ hφcompact w
  have h2 := g5GreenFirst φ f hφ hf hfcompact w
  calc
    ∫ z, partialLap F w f z * φ z ∂(volX F) =
        ∫ z, placeGradBilinear F w f φ z ∂(volX F) := h1
    _ = ∫ z, placeGradBilinear F w φ f z ∂(volX F) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (g5PlaceGradBilinear_comm f φ w)
    _ = ∫ z, partialLap F w φ z * f z ∂(volX F) := h2.symm
    _ = ∫ z, f z * partialLap F w φ z ∂(volX F) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_comm _ _

private theorem g5IsSmoothX_star (f : X F → ℂ) (hf : IsSmoothX F f) :
    IsSmoothX F (fun z => star (f z)) := by
  change ContDiffOn ℝ ∞ (fun p => star (f (ptX F p))) (posSet F)
  have hEq : (fun p => star (f (ptX F p))) =
      Complex.conjCLE ∘ (fun p => f (ptX F p)) := by
    funext p
    simp [Complex.conjCLE_apply, Complex.star_def]
  rw [hEq]
  exact Complex.conjCLE.contDiff.comp_contDiffOn hf

private theorem g5PlaceGradient_star (f : X F → ℂ) (hf : IsSmoothX F f)
    (w : InfinitePlace F) (z : X F) (j : Fin 3) :
    placeGradient F w (fun x => star (f x)) z j = star (placeGradient F w f z j) := by
  let p := coordsX F z
  have hp : p ∈ posSet F := by simpa [p] using g5CoordsX_pos z
  have hdiff : DifferentiableAt ℝ (fun q => f (ptX F q)) p :=
    (hf.differentiableOn (by simp)).differentiableAt (g5PosSet_isOpen.mem_nhds hp)
  have hEq : (fun q => star (f (ptX F q))) =
      Complex.conjCLE ∘ (fun q => f (ptX F q)) := by
    funext q
    simp [Complex.conjCLE_apply, Complex.star_def]
  have hcomp := fderiv_comp p Complex.conjCLE.differentiableAt hdiff
  have hL := Complex.conjCLE.fderiv (x := f (ptX F p))
  unfold placeGradient
  simp only [Function.comp_def]
  rw [hEq, hcomp, hL]
  simp [p, Complex.conjCLE_apply, Complex.star_def]

private theorem g5PlaceGradBilinear_starInner (f φ : X F → ℂ)
    (hφ : IsSmoothX F φ) (w : InfinitePlace F) (z : X F) :
    placeGradBilinear F w f φ z =
      star (placeGradInner F w f (fun x => star (φ x)) z) := by
  unfold placeGradBilinear placeGradInner
  simp_rw [g5PlaceGradient_star φ hφ w z]
  simp [star_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem g5PlaceGradBilinear_action (g : InfinitePlace F → SL(2, ℂ))
    (f φ : X F → ℂ) (hf : IsSmoothX F f) (hφ : IsSmoothX F φ)
    (w : InfinitePlace F) (z : X F) :
    placeGradBilinear F w (fun x => f (actAtPlaces F g x))
        (fun x => φ (actAtPlaces F g x)) z =
      placeGradBilinear F w f φ (actAtPlaces F g z) := by
  let fcomp : X F → ℂ := fun x => f (actAtPlaces F g x)
  let φcomp : X F → ℂ := fun x => φ (actAtPlaces F g x)
  have hfcomp : IsSmoothX F fcomp := g5IsSmoothX_action g f hf
  have hφcomp : IsSmoothX F φcomp := g5IsSmoothX_action g φ hφ
  have hG4 := greenPlaceGradInner_action g f (fun x => star (φ x)) hf
    (g5IsSmoothX_star φ hφ) w z
  calc
    placeGradBilinear F w fcomp φcomp z =
        star (placeGradInner F w fcomp (fun x => star (φcomp x)) z) :=
          g5PlaceGradBilinear_starInner fcomp φcomp hφcomp w z
    _ = star (placeGradInner F w f (fun x => star (φ x)) (actAtPlaces F g z)) := by
          rw [hG4]
    _ = placeGradBilinear F w f φ (actAtPlaces F g z) :=
          (g5PlaceGradBilinear_starInner f φ hφ w (actAtPlaces F g z)).symm

private def g5InversePlaces (g : InfinitePlace F → SL(2, ℂ)) :
    InfinitePlace F → SL(2, ℂ) := fun w => (g w)⁻¹

private theorem g5Act_comp (g h : InfinitePlace F → SL(2, ℂ)) (z : X F) :
    actAtPlaces F g (actAtPlaces F h z) =
      actAtPlaces F (fun w => g w * h w) z := by
  funext w
  simp [actAtPlaces, smul_smul]

private theorem g5Act_inverse_left (g : InfinitePlace F → SL(2, ℂ)) (z : X F) :
    actAtPlaces F (g5InversePlaces g) (actAtPlaces F g z) = z := by
  funext w
  simp [actAtPlaces, g5InversePlaces, smul_smul]

private theorem g5Act_inverse_right (g : InfinitePlace F → SL(2, ℂ)) (z : X F) :
    actAtPlaces F g (actAtPlaces F (g5InversePlaces g) z) = z := by
  funext w
  simp [actAtPlaces, g5InversePlaces, smul_smul]

private theorem g5ActAtPlaces_continuous (g : InfinitePlace F → SL(2, ℂ)) :
    Continuous (actAtPlaces F g) := by
  have hchart : ContinuousOn
      (fun p : Coord F => ptX F (g5CoordAction g p)) (posSet F) :=
    g5PtX_continuousOn.comp (g5CoordAction_contDiffOn g).continuousOn
      (fun p hp => g5CoordAction_pos g p hp)
  have hEq : Set.EqOn (fun p => actAtPlaces F g (ptX F p))
      (fun p => ptX F (g5CoordAction g p)) (posSet F) := by
    intro p hp
    exact (g5PtX_coordAction g p hp).symm
  exact g5Continuous_from_chart (actAtPlaces F g) (hchart.congr hEq)

private theorem g5HasCompactSupportX_comp_action (g : InfinitePlace F → SL(2, ℂ))
    (φ : X F → ℂ) (hcompact : HasCompactSupportX F φ) :
    HasCompactSupportX F (fun z => φ (actAtPlaces F g z)) := by
  rcases hcompact with ⟨K, hK, hSupport⟩
  let gInv := g5InversePlaces g
  let K' := actAtPlaces F gInv '' K
  have hK' : IsCompact K' := hK.image (g5ActAtPlaces_continuous gInv)
  refine ⟨K', hK', ?_⟩
  intro z hz
  have hTz : actAtPlaces F g z ∈ K := hSupport hz
  refine ⟨actAtPlaces F g z, hTz, ?_⟩
  exact g5Act_inverse_left g z

private theorem g5Integral_comp_action (g : InfinitePlace F → SL(2, ℂ))
    (G : X F → ℂ) (hcont : Continuous G) :
    ∫ z, G z ∂(volX F) = ∫ z, G (actAtPlaces F g z) ∂(volX F) := by
  letI : BorelSpace (X F) := g5BorelSpaceX (F := F)
  letI : OpensMeasurableSpace (X F) := g5OpensMeasurableX (F := F)
  have hmap := (G3_volume (F := F)).1 g
  have hact : AEMeasurable (actAtPlaces F g) (volX F) :=
    (g5ActAtPlaces_continuous g).measurable.aemeasurable
  have hGae : AEStronglyMeasurable G (Measure.map (actAtPlaces F g) (volX F)) := by
    rw [hmap]
    exact hcont.measurable.aestronglyMeasurable
  calc
    ∫ z, G z ∂(volX F) =
        ∫ z, G z ∂Measure.map (actAtPlaces F g) (volX F) := by rw [hmap]
    _ = ∫ z, G (actAtPlaces F g z) ∂(volX F) := integral_map hact hGae

private theorem g5LaplacianAction_test (g : InfinitePlace F → SL(2, ℂ))
    (F₀ ψ : X F → ℂ) (hF₀ : IsSmoothX F F₀) (hψ : IsSmoothX F ψ)
    (hψcompact : HasCompactSupportX F ψ) (w : InfinitePlace F) :
    ∫ z, partialLap F w (fun x => F₀ (actAtPlaces F g x)) z * ψ z ∂(volX F) =
      ∫ z, partialLap F w F₀ (actAtPlaces F g z) * ψ z ∂(volX F) := by
  let gInv := g5InversePlaces g
  let ψInv : X F → ℂ := fun z => ψ (actAtPlaces F gInv z)
  let Fcomp : X F → ℂ := fun z => F₀ (actAtPlaces F g z)
  have hψInv : IsSmoothX F ψInv := g5IsSmoothX_action gInv ψ hψ
  have hψInvCompact : HasCompactSupportX F ψInv :=
    g5HasCompactSupportX_comp_action gInv ψ hψcompact
  have hFcomp : IsSmoothX F Fcomp := g5IsSmoothX_action g F₀ hF₀
  have hgrad (z : X F) :
      placeGradBilinear F w Fcomp ψ z =
        placeGradBilinear F w F₀ ψInv (actAtPlaces F g z) := by
    have h := g5PlaceGradBilinear_action g F₀ ψInv hF₀ hψInv w z
    have h' : placeGradBilinear F w Fcomp
        (fun x => ψ (actAtPlaces F gInv (actAtPlaces F g x))) z =
        placeGradBilinear F w F₀ ψInv (actAtPlaces F g z) := by
      simpa [Fcomp, ψInv] using h
    have hψcomp : (fun x => ψ (actAtPlaces F gInv (actAtPlaces F g x))) = ψ := by
      funext x
      rw [g5Act_inverse_left]
    rw [hψcomp] at h'
    exact h'
  have hFirstLeft := g5GreenFirst Fcomp ψ hFcomp hψ hψcompact w
  have hFirstRight := g5GreenFirst F₀ ψInv hF₀ hψInv hψInvCompact w
  let Ggrad : X F → ℂ := fun z => placeGradBilinear F w F₀ ψInv z
  let Glap : X F → ℂ := fun z => partialLap F w F₀ z * ψInv z
  have hGgradCont : Continuous Ggrad :=
    g5PlaceGradBilinear_continuous F₀ ψInv hF₀ hψInv w
  have hGlapCont : Continuous Glap :=
    (g5PartialLap_continuous F₀ hF₀ w).mul (g5SmoothX_continuous ψInv hψInv)
  calc
    ∫ z, partialLap F w Fcomp z * ψ z ∂(volX F) =
        ∫ z, placeGradBilinear F w Fcomp ψ z ∂(volX F) := hFirstLeft
    _ = ∫ z, Ggrad (actAtPlaces F g z) ∂(volX F) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by simpa [Ggrad] using hgrad z
    _ = ∫ z, Ggrad z ∂(volX F) := (g5Integral_comp_action g Ggrad hGgradCont).symm
    _ = ∫ z, Glap z ∂(volX F) := hFirstRight.symm
    _ = ∫ z, partialLap F w F₀ (actAtPlaces F g z) * ψ z ∂(volX F) := by
      calc
        ∫ z, Glap z ∂(volX F) =
            ∫ z, Glap (actAtPlaces F g z) ∂(volX F) :=
              g5Integral_comp_action g Glap hGlapCont
        _ = ∫ z, partialLap F w F₀ (actAtPlaces F g z) * ψ z ∂(volX F) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            change partialLap F w F₀ (actAtPlaces F g z) *
              ψInv (actAtPlaces F g z) = _
            change partialLap F w F₀ (actAtPlaces F g z) *
              ψ (actAtPlaces F gInv (actAtPlaces F g z)) = _
            rw [g5Act_inverse_left]

theorem g5PartialLap_action_pointwise (g : InfinitePlace F → SL(2, ℂ))
    (F₀ : X F → ℂ) (hF₀ : IsSmoothX F F₀)
    (w : InfinitePlace F) (z : X F) :
    partialLap F w (fun x => F₀ (actAtPlaces F g x)) z =
      partialLap F w F₀ (actAtPlaces F g z) := by
  let Fcomp : X F → ℂ := fun x => F₀ (actAtPlaces F g x)
  let d : X F → ℂ := fun x =>
    partialLap F w Fcomp x - partialLap F w F₀ (actAtPlaces F g x)
  have hFcomp : IsSmoothX F Fcomp := g5IsSmoothX_action g F₀ hF₀
  have hDcont : Continuous d := by
    have h1 : Continuous (fun x => partialLap F w Fcomp x) :=
      g5PartialLap_continuous Fcomp hFcomp w
    have h2 : Continuous (fun x => partialLap F w F₀ (actAtPlaces F g x)) :=
      (g5PartialLap_continuous F₀ hF₀ w).comp (g5ActAtPlaces_continuous g)
    exact h1.sub h2
  by_contra hneq
  have hD0 : d z ≠ 0 := by
    dsimp [d, Fcomp]
    exact sub_ne_zero.mpr hneq
  let p0 : Coord F := coordsX F z
  have hp0 : p0 ∈ posSet F := by simpa [p0] using g5CoordsX_pos z
  let c : ℂ := star (d z)
  let R : Coord F → ℝ := fun p => Complex.re (c * d (ptX F p))
  have hRcont : ContinuousOn R (posSet F) := by
    dsimp [R]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (hDcont.comp_continuousOn g5PtX_continuousOn))
  have hR0eq : R p0 = ‖d z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [R, c, p0, g5PtX_coordsX, Complex.normSq_apply,
      Complex.star_def, Complex.mul_re]
  have hR0 : 0 < R p0 := by
    rw [hR0eq]
    have hnorm : 0 < ‖d z‖ := norm_pos_iff.mpr hD0
    positivity
  have hRcontAt : ContinuousAt R p0 :=
    hRcont.continuousAt (g5PosSet_isOpen.mem_nhds hp0)
  have hRpos : ∀ᶠ q in 𝓝 p0, 0 < R q :=
    hRcontAt.eventually (isOpen_Ioi.mem_nhds hR0)
  let S : Set (Coord F) := {q | q ∈ posSet F ∧ 0 < R q}
  have hS : S ∈ 𝓝 p0 := by
    filter_upwards [g5PosSet_isOpen.mem_nhds hp0, hRpos] with q hq hRq
    exact ⟨hq, hRq⟩
  obtain ⟨χ, hχsupport, hχcompact, hχsmooth, hχrange, hχone⟩ :=
    exists_contDiff_tsupport_subset (s := S) (x := p0) (n := (⊤ : ℕ∞)) hS
  have hχpos : tsupport χ ⊆ posSet F := by
    intro q hq
    exact (hχsupport hq).1
  let Ktest : Set (X F) := ptX F '' tsupport χ
  have hKtest : IsCompact Ktest :=
    hχcompact.image_of_continuousOn (g5PtX_continuousOn.mono hχpos)
  let ρ : X F → ℝ := fun x => χ (coordsX F x)
  have hρcont : Continuous ρ := hχsmooth.continuous.comp g5CoordsX_continuous
  have hρsmooth : IsSmoothRealX F ρ := by
    change ContDiffOn ℝ ∞ (fun q => χ (coordsX F (ptX F q))) (posSet F)
    apply hχsmooth.contDiffOn.congr
    intro q hq
    rw [g5CoordsX_ptX q hq]
  let ψ : X F → ℂ := fun x => c * (ρ x : ℂ)
  have hψsmooth : IsSmoothX F ψ := by
    change ContDiffOn ℝ ∞ (fun q => c * (ρ (ptX F q) : ℂ)) (posSet F)
    have hEq : Set.EqOn (fun q => c * (ρ (ptX F q) : ℂ))
        (fun q => c * (χ q : ℂ)) (posSet F) := by
      intro q hq
      simp [ρ, g5CoordsX_ptX q hq]
    have hbase : ContDiffOn ℝ ∞ (fun q => c * (χ q : ℂ)) (posSet F) :=
      contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hχsmooth.contDiffOn)
    exact hbase.congr hEq
  have hψsupport : {x | ψ x ≠ 0} ⊆ Ktest := by
    intro x hx
    have hχx : χ (coordsX F x) ≠ 0 := by
      intro hzero
      apply hx
      simp [ψ, ρ, hzero]
    have hpSupport : coordsX F x ∈ Function.support χ := by
      simpa [Function.mem_support] using hχx
    have hpTail : coordsX F x ∈ tsupport χ := subset_closure hpSupport
    exact ⟨coordsX F x, hpTail, g5PtX_coordsX x⟩
  have hψcompact : HasCompactSupportX F ψ := ⟨Ktest, hKtest, hψsupport⟩
  let testReal : X F → ℝ := fun x => Complex.re (d x * ψ x)
  have htestRealCont : Continuous testReal :=
    Complex.continuous_re.comp (hDcont.mul (Complex.continuous_ofReal.comp hρcont |>.const_mul c))
  have htestRealSupport : {x | testReal x ≠ 0} ⊆ Ktest := by
    intro x hx
    apply hψsupport
    intro hψzero
    apply hx
    simp [testReal, hψzero]
  have hKtestClosed : IsClosed Ktest := g5Compact_isClosed Ktest hKtest
  have htestRealCompact : HasCompactSupport testReal := by
    change IsCompact (closure (Function.support testReal))
    apply hKtest.of_isClosed_subset isClosed_closure
    exact closure_minimal htestRealSupport hKtestClosed
  have htestRealEq (x : X F) : testReal x = R (coordsX F x) * ρ x := by
    simp [testReal, ψ, ρ, R, c, g5PtX_coordsX, Complex.mul_re, Complex.mul_im]
    <;> ring
  have hRpos_of_test (x : X F) (hx : ρ x ≠ 0) : 0 < R (coordsX F x) := by
    have hχx : χ (coordsX F x) ≠ 0 := by simpa [ρ] using hx
    have hpSupport : coordsX F x ∈ Function.support χ := by
      simpa [Function.mem_support] using hχx
    have hpTail : coordsX F x ∈ tsupport χ := subset_closure hpSupport
    exact (hχsupport hpTail).2
  have hρnonneg (x : X F) : 0 ≤ ρ x :=
    (hχrange (Set.mem_range_self (coordsX F x))).1
  have htestRealNonneg : ∀ x, 0 ≤ testReal x := by
    intro x
    rw [htestRealEq x]
    by_cases hx : ρ x = 0
    · simp [hx]
    · exact mul_nonneg (le_of_lt (hRpos_of_test x hx)) (hρnonneg x)
  have hρz : ρ z = 1 := by simp [ρ, p0, hχone]
  have htestRealz : testReal z ≠ 0 := by
    rw [htestRealEq z, hρz]
    have hRz : R (coordsX F z) = R p0 := by rfl
    rw [hRz]
    simpa using ne_of_gt hR0
  let g1 : X F → ℂ := fun x => partialLap F w Fcomp x * ψ x
  let g2 : X F → ℂ := fun x => partialLap F w F₀ (actAtPlaces F g x) * ψ x
  have hψcont : Continuous ψ := Complex.continuous_ofReal.comp hρcont |>.const_mul c
  have hg1cont : Continuous g1 :=
    (g5PartialLap_continuous Fcomp hFcomp w).mul hψcont
  have hg2cont : Continuous g2 :=
    ((g5PartialLap_continuous F₀ hF₀ w).comp (g5ActAtPlaces_continuous g)).mul hψcont
  have hg1support : {x | g1 x ≠ 0} ⊆ Ktest := by
    intro x hx
    apply hψsupport
    intro hzero
    apply hx
    simp [g1, hzero]
  have hg2support : {x | g2 x ≠ 0} ⊆ Ktest := by
    intro x hx
    apply hψsupport
    intro hzero
    apply hx
    simp [g2, hzero]
  have hg1int : Integrable g1 (volX F) :=
    g5IntegrableX g1 hg1cont ⟨Ktest, hKtest, hg1support⟩
  have hg2int : Integrable g2 (volX F) :=
    g5IntegrableX g2 hg2cont ⟨Ktest, hKtest, hg2support⟩
  have htest := g5LaplacianAction_test g F₀ ψ hF₀ hψsmooth hψcompact w
  have hprodInt : Integrable (fun x => d x * ψ x) (volX F) := by
    apply (hg1int.sub hg2int).congr
    filter_upwards [] with x
    simp [d, g1, g2, Fcomp]
    <;> ring
  have hprodZero : ∫ x, d x * ψ x ∂(volX F) = 0 := by
    calc
      _ = ∫ x, g1 x - g2 x ∂(volX F) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [d, g1, g2, Fcomp]
        <;> ring
      _ = _ := by
        rw [integral_sub hg1int hg2int]
        have htest' : ∫ x, g1 x ∂(volX F) = ∫ x, g2 x ∂(volX F) := by
          simpa [g1, g2, Fcomp] using htest
        rw [htest']
        exact sub_self _
  have htestRealZero : ∫ x, testReal x ∂(volX F) = 0 := by
    have h := integral_re hprodInt
    rw [hprodZero] at h
    simpa [testReal] using h
  letI : OpensMeasurableSpace (X F) := g5OpensMeasurableX (F := F)
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun {K} hK => (G3_volume (F := F)).2.2.1 K hK⟩
  letI : Measure.IsOpenPosMeasure (volX F) := by
    constructor
    intro U hU hne
    exact (G3_volume (F := F)).2.2.2.1 U hU hne
  have hposInt : 0 < ∫ x, testReal x ∂(volX F) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := volX F) htestRealCont htestRealCompact htestRealNonneg htestRealz
  rw [htestRealZero] at hposInt
  exact (lt_irrefl 0 hposInt)

end ArtinPrimitiveRoots.A1.Spec
