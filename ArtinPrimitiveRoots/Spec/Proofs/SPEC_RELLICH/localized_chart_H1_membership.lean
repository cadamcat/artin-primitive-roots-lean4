import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField Matrix MeasureTheory Function Set Filter Topology
open scoped MatrixGroups ContDiff ENNReal ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private def rellichFromCoord (q : Coord F) : RellichCoord F :=
  WithLp.toLp 2 fun wj : InfinitePlace F × Fin 3 =>
    match wj.2 with
    | 0 => (q wj.1).1.re
    | 1 => (q wj.1).1.im
    | 2 => (q wj.1).2

private theorem rellichFromCoord_toCoord (p : RellichCoord F) :
    rellichFromCoord (F := F) (rellichToCoord F p) = p := by
  ext wj
  rcases wj with ⟨w, j⟩
  fin_cases j <;> simp [rellichFromCoord, rellichToCoord]

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

private theorem rellichFromCoord_mem_posSet (q : Coord F) (hq : q ∈ posSet F) :
    rellichFromCoord (F := F) q ∈ rellichPosSet F := by
  change ∀ w : InfinitePlace F, 0 < (rellichFromCoord (F := F) q) (w, 2)
  intro w
  simpa [rellichFromCoord] using hq w

private def rellichLocalizedRe (ψ : X F → ℝ) (f : X F → ℂ) : RellichCoord F → ℝ :=
  fun p => (rellichLocalized F ψ f p).re

private def rellichLocalizedIm (ψ : X F → ℝ) (f : X F → ℂ) : RellichCoord F → ℝ :=
  fun p => (rellichLocalized F ψ f p).im

private theorem rellich_contDiff_of_contDiffOn_of_support_subset
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s K : Set E} {f : E → G} (hs : IsOpen s) (hK : IsCompact K)
    (hKs : K ⊆ s) (hf : ContDiffOn ℝ ∞ f s)
    (hfsupp : Function.support f ⊆ K) : ContDiff ℝ ∞ f := by
  have htsupp : tsupport f ⊆ s := by
    exact (closure_minimal hfsupp hK.isClosed).trans hKs
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hf.contDiffAt (hs.mem_nhds hx)
  · have hx' : x ∉ tsupport f := fun h => hx (htsupp h)
    have hzero : f =ᶠ[𝓝 x] 0 :=
      (notMem_tsupport_iff_eventuallyEq (f := f) (x := x)).1 hx'
    exact ContDiffAt.congr_of_eventuallyEq
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : G)) x) hzero

private theorem rellich_mem_range_extendByZero_of_support
    {E G : Type*} [MeasurableSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (f : E → G) (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfsupp : Function.support f ⊆ K) :
    hf.toLp f ∈ LinearMap.range
      ((Lp.extendByZeroₗᵢ (μ := μ) (E := G) (p := (2 : ℝ≥0∞)) (s := K) hK).toLinearMap) := by
  classical
  let u : Lp G 2 (μ.restrict K) := (hf.restrict K).toLp f
  refine ⟨u, ?_⟩
  apply Lp.ext
  have hExt := Lp.extendByZeroₗᵢ_ae_eq (μ := μ) (E := G)
    (p := (2 : ℝ≥0∞)) (s := K) hK u
  have hOn : ∀ᵐ x ∂μ, x ∈ K → u x = f x :=
    (ae_restrict_iff' hK).1 ((hf.restrict K).coeFn_toLp)
  have hFull : ∀ᵐ x ∂μ, (hf.toLp f) x = f x := hf.coeFn_toLp
  filter_upwards [hExt, hOn, hFull] with x hxExt hxOn hxFull
  by_cases hxK : x ∈ K
  · calc
      (Lp.extendByZeroₗᵢ (μ := μ) (E := G) (p := (2 : ℝ≥0∞))
          (s := K) hK u) x = K.indicator (fun y => u y) x := hxExt
      _ = u x := by simp [hxK]
      _ = f x := hxOn hxK
      _ = (hf.toLp f) x := hxFull.symm
  · have hzero : f x = 0 := by
      by_contra hne
      exact hxK (hfsupp hne)
    calc
      (Lp.extendByZeroₗᵢ (μ := μ) (E := G) (p := (2 : ℝ≥0∞))
          (s := K) hK u) x = K.indicator (fun y => u y) x := hxExt
      _ = 0 := by simp [hxK]
      _ = f x := hzero.symm
      _ = (hf.toLp f) x := hxFull.symm

private abbrev RellichC1c :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c
    (E := RellichCoord F)

private noncomputable def rellichC1cGraphH1Linear :
    RellichC1c (F := F) →ₗ[ℝ]
      ↥(RellichEuclidean.h1 (μ := (volume : Measure (RellichCoord F)))) :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F)).codRestrict
    (RellichEuclidean.h1 (μ := (volume : Measure (RellichCoord F))) :
      Submodule ℝ _)
    (by
      intro g
      change RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) g ∈
        (LinearMap.range
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F))).topologicalClosure
      exact (LinearMap.range _).le_topologicalClosure ⟨g, rfl⟩)

private theorem rellichC1cGraph_mem_h1On
    (K : Set (RellichCoord F)) (hK : MeasurableSet K)
    (g : RellichC1c (F := F)) (hgsupp : Function.support (g : RellichCoord F → ℝ) ⊆ K) :
    rellichC1cGraphH1Linear (F := F) g ∈ RellichEuclidean.h1On K hK := by
  change RellichEuclidean.h1ToL2 (μ := (volume : Measure (RellichCoord F)))
      (rellichC1cGraphH1Linear (F := F) g) ∈
    LinearMap.range
      ((Lp.extendByZeroₗᵢ (μ := (volume : Measure (RellichCoord F)))
          (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hK).toLinearMap)
  have hfirst :
      RellichEuclidean.h1ToL2 (μ := (volume : Measure (RellichCoord F)))
          (rellichC1cGraphH1Linear (F := F) g) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) g := by
    rfl
  rw [hfirst]
  exact rellich_mem_range_extendByZero_of_support (volume : Measure (RellichCoord F))
    K hK (g : RellichCoord F → ℝ)
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) g.2)
    hgsupp

private noncomputable def rellichC1cGraphH1OnLinear
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (K : Set (RellichCoord F)) (hK : MeasurableSet K)
    (A : T →ₗ[ℝ] RellichC1c (F := F))
    (hA : ∀ f, Function.support (A f : RellichCoord F → ℝ) ⊆ K) :
    T →ₗ[ℝ] ↥(RellichEuclidean.h1On K hK) :=
  ((rellichC1cGraphH1Linear (F := F)).comp A).codRestrict
    (RellichEuclidean.h1On K hK)
    (fun f => rellichC1cGraph_mem_h1On (F := F) K hK (A f) (hA f))

/-- The cutoff test has supported real and imaginary H¹ representatives after zero extension.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:318-319. Uses G1_h3_basics, G2_x_action and the
T2 test characterization; the compact cutoff vanishes near the positive-chart boundary.
Build C1c representatives and their core maps into h1On, including gradient calibration. -/
theorem localized_chart_H1_membership
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (ψ : X F → ℝ) (hψsmooth : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) :
    Nonempty (RellichTestChart Γ ψ) := by
  classical
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoordPt, _, _, _, _, ⟨chartEquiv, _, hcoordsX⟩⟩
  obtain ⟨K, hK, hψK⟩ := hψcompact
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
  let support : Set (RellichCoord F) :=
    rellichFromCoord (F := F) '' (coordsX F '' K)
  have hSupportCompact : IsCompact support := by
    dsimp [support]
    exact (hK.image hcoordsXCont).image (rellichFromCoord_continuous (F := F))
  have hSupportMeas : MeasurableSet support := hSupportCompact.measurableSet
  have hSupportPos : support ⊆ rellichPosSet F := by
    rintro p ⟨q, hq, rfl⟩
    rcases hq with ⟨z, hzK, rfl⟩
    exact rellichFromCoord_mem_posSet (F := F) (coordsX F z) (hcoordPos z)
  have hPosOpen : IsOpen (rellichPosSet F) := by
    rw [show rellichPosSet F = ⋂ w : InfinitePlace F,
        {p : RellichCoord F | 0 < p (w, 2)} by
      ext p
      simp [rellichPosSet]]
    exact isOpen_iInter_of_finite fun w => by
      have hcoord : Continuous (fun p : RellichCoord F => p (w, 2)) := by fun_prop
      exact isOpen_Ioi.preimage hcoord
  have hToCoordSmooth : ContDiff ℝ ∞ (rellichToCoord F) := by
    change ContDiff ℝ ∞ (fun p : RellichCoord F => fun w : InfinitePlace F =>
      (((p (w, 0) : ℂ) + Complex.I * (p (w, 1) : ℂ)), p (w, 2)))
    rw [contDiff_pi]
    intro w
    let e0 : RellichCoord F →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ => ℝ) (w, 0)
    let e1 : RellichCoord F →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ => ℝ) (w, 1)
    let e2 : RellichCoord F →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ => ℝ) (w, 2)
    have h0 : ContDiff ℝ ∞ (fun p : RellichCoord F => (p (w, 0) : ℂ)) := by
      change ContDiff ℝ ∞ (fun p => Complex.ofRealCLM (e0 p))
      exact Complex.ofRealCLM.contDiff.comp e0.contDiff
    have h1 : ContDiff ℝ ∞ (fun p : RellichCoord F => (p (w, 1) : ℂ)) := by
      change ContDiff ℝ ∞ (fun p => Complex.ofRealCLM (e1 p))
      exact Complex.ofRealCLM.contDiff.comp e1.contDiff
    have h2 : ContDiff ℝ ∞ (fun p : RellichCoord F => p (w, 2)) := by
      change ContDiff ℝ ∞ e2
      exact e2.contDiff
    have hI : ContDiff ℝ ∞ (fun _ : RellichCoord F => (Complex.I : ℂ)) := contDiff_const
    exact ContDiff.prodMk (h0.add (hI.mul h1)) h2
  have hToCoordMaps : MapsTo (rellichToCoord F) (rellichPosSet F) (posSet F) := by
    intro p hp
    change ∀ w, 0 < (rellichToCoord F p w).2
    intro w
    simpa [rellichToCoord] using hp w
  have hψSupport : ∀ z, ψ z ≠ 0 → z ∈ K := by
    intro z hz
    apply hψK
    simpa using hz
  have hLocalizedSupport (f : testSubmodule F Γ) :
      {p | rellichLocalized F ψ (f : X F → ℂ) p ≠ 0} ⊆ support := by
    intro p hp
    by_cases hpPos : p ∈ rellichPosSet F
    · have hprod :
          (ψ (ptX F (rellichToCoord F p)) : ℂ) *
              (f : X F → ℂ) (ptX F (rellichToCoord F p)) ≠ 0 := by
        simpa [rellichLocalized, hpPos] using hp
      have hψnz : ψ (ptX F (rellichToCoord F p)) ≠ 0 := by
        intro hzero
        exact hprod (by simp [hzero])
      have hzK : ptX F (rellichToCoord F p) ∈ K :=
        hψSupport _ hψnz
      have hToCoordPos : rellichToCoord F p ∈ posSet F := by
        change ∀ w, 0 < (rellichToCoord F p w).2
        intro w
        simpa [rellichToCoord] using hpPos w
      have hcoords :
          coordsX F (ptX F (rellichToCoord F p)) = rellichToCoord F p :=
        hcoordPt _ hToCoordPos
      have hfrom :
          rellichFromCoord (F := F) (coordsX F (ptX F (rellichToCoord F p))) = p := by
        rw [hcoords]
        exact rellichFromCoord_toCoord (F := F) p
      change p ∈ rellichFromCoord (F := F) '' (coordsX F '' K)
      rw [← hfrom]
      exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hzK)
    · simp [rellichLocalized, hpPos] at hp
  have hRellichLocalizedSmooth (f : testSubmodule F Γ) :
      ContDiffOn ℝ ∞ (rellichLocalizedRe (F := F) ψ (f : X F → ℂ)) (rellichPosSet F) ∧
      ContDiffOn ℝ ∞ (rellichLocalizedIm (F := F) ψ (f : X F → ℂ)) (rellichPosSet F) := by
    have hfTest : IsGammaTest F Γ (f : X F → ℂ) := (htests (f : X F → ℂ)).1 f.property
    have hψChartReal : ContDiffOn ℝ ∞ (fun q : Coord F => ψ (ptX F q)) (posSet F) := hψsmooth
    have hfChart : ContDiffOn ℝ ∞
        (fun q : Coord F => (f : X F → ℂ) (ptX F q)) (posSet F) := hfTest.2.1
    have hψRellichReal : ContDiffOn ℝ ∞
        (fun p : RellichCoord F => ψ (ptX F (rellichToCoord F p))) (rellichPosSet F) :=
      hψChartReal.comp hToCoordSmooth.contDiffOn hToCoordMaps
    have hfRellich : ContDiffOn ℝ ∞
        (fun p : RellichCoord F => (f : X F → ℂ) (ptX F (rellichToCoord F p)))
        (rellichPosSet F) := hfChart.comp hToCoordSmooth.contDiffOn hToCoordMaps
    have hψRellich : ContDiffOn ℝ ∞
        (fun p : RellichCoord F => (ψ (ptX F (rellichToCoord F p)) : ℂ))
        (rellichPosSet F) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hψRellichReal
    have hprod : ContDiffOn ℝ ∞
        (fun p : RellichCoord F =>
          (ψ (ptX F (rellichToCoord F p)) : ℂ) *
            (f : X F → ℂ) (ptX F (rellichToCoord F p)))
        (rellichPosSet F) := hψRellich.mul hfRellich
    have hReDerived : ContDiffOn ℝ ∞
        (fun p : RellichCoord F =>
          Complex.re ((ψ (ptX F (rellichToCoord F p)) : ℂ) *
            (f : X F → ℂ) (ptX F (rellichToCoord F p))))
        (rellichPosSet F) := by
      exact Complex.reCLM.contDiff.comp_contDiffOn hprod
    have hImDerived : ContDiffOn ℝ ∞
        (fun p : RellichCoord F =>
          Complex.im ((ψ (ptX F (rellichToCoord F p)) : ℂ) *
            (f : X F → ℂ) (ptX F (rellichToCoord F p))))
        (rellichPosSet F) := by
      exact Complex.imCLM.contDiff.comp_contDiffOn hprod
    have hReEq : ∀ p ∈ rellichPosSet F,
        rellichLocalizedRe (F := F) ψ (f : X F → ℂ) p =
          Complex.re ((ψ (ptX F (rellichToCoord F p)) : ℂ) *
            (f : X F → ℂ) (ptX F (rellichToCoord F p)) ) := by
      intro p hp
      simp [rellichLocalizedRe, rellichLocalized, hp]
    have hImEq : ∀ p ∈ rellichPosSet F,
        rellichLocalizedIm (F := F) ψ (f : X F → ℂ) p =
          Complex.im ((ψ (ptX F (rellichToCoord F p)) : ℂ) *
            (f : X F → ℂ) (ptX F (rellichToCoord F p)) ) := by
      intro p hp
      simp [rellichLocalizedIm, rellichLocalized, hp]
    exact ⟨hReDerived.congr hReEq, hImDerived.congr hImEq⟩
  have hReC1c : ∀ f : testSubmodule F Γ,
      rellichLocalizedRe (F := F) ψ (f : X F → ℂ) ∈ RellichC1c (F := F) := by
    intro f
    let g := rellichLocalizedRe (F := F) ψ (f : X F → ℂ)
    refine ⟨?_, ?_⟩
    · exact (rellich_contDiff_of_contDiffOn_of_support_subset hPosOpen hSupportCompact
        hSupportPos (hRellichLocalizedSmooth f).1 (by
          intro p hp
          exact hLocalizedSupport f (by
            intro hzero
            exact hp (by simp [rellichLocalizedRe, hzero])))).of_le (by simp)
    · exact HasCompactSupport.of_support_subset_isCompact hSupportCompact (by
        intro p hp
        exact hLocalizedSupport f (by
          intro hzero
          exact hp (by simp [rellichLocalizedRe, hzero])))
  have hImC1c : ∀ f : testSubmodule F Γ,
      rellichLocalizedIm (F := F) ψ (f : X F → ℂ) ∈ RellichC1c (F := F) := by
    intro f
    let g := rellichLocalizedIm (F := F) ψ (f : X F → ℂ)
    refine ⟨?_, ?_⟩
    · exact (rellich_contDiff_of_contDiffOn_of_support_subset hPosOpen hSupportCompact
        hSupportPos (hRellichLocalizedSmooth f).2 (by
          intro p hp
          exact hLocalizedSupport f (by
            intro hzero
            exact hp (by simp [rellichLocalizedIm, hzero])))).of_le (by simp)
    · exact HasCompactSupport.of_support_subset_isCompact hSupportCompact (by
        intro p hp
        exact hLocalizedSupport f (by
          intro hzero
          exact hp (by simp [rellichLocalizedIm, hzero])))
  let reC1c : testSubmodule F Γ →ₗ[ℝ] RellichC1c (F := F) := {
    toFun := fun f => ⟨rellichLocalizedRe (F := F) ψ (f : X F → ℂ), hReC1c f⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext p
      by_cases hp : p ∈ rellichPosSet F
      · simp [rellichLocalizedRe, rellichLocalized, hp, mul_add, Complex.add_re]
      · simp [rellichLocalizedRe, rellichLocalized, hp]
    map_smul' := by
      intro c f
      apply Subtype.ext
      funext p
      by_cases hp : p ∈ rellichPosSet F
      · simp [rellichLocalizedRe, rellichLocalized, hp, Pi.smul_apply,
          Complex.mul_re, mul_assoc, mul_left_comm, mul_comm]
      · simp [rellichLocalizedRe, rellichLocalized, hp, Pi.smul_apply]
  }
  let imC1c : testSubmodule F Γ →ₗ[ℝ] RellichC1c (F := F) := {
    toFun := fun f => ⟨rellichLocalizedIm (F := F) ψ (f : X F → ℂ), hImC1c f⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext p
      by_cases hp : p ∈ rellichPosSet F
      · simp [rellichLocalizedIm, rellichLocalized, hp, mul_add, Complex.add_im]
      · simp [rellichLocalizedIm, rellichLocalized, hp]
    map_smul' := by
      intro c f
      apply Subtype.ext
      funext p
      by_cases hp : p ∈ rellichPosSet F
      · simp [rellichLocalizedIm, rellichLocalized, hp, Pi.smul_apply,
          Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]
      · simp [rellichLocalizedIm, rellichLocalized, hp, Pi.smul_apply]
  }
  have hReSupport (f : testSubmodule F Γ) :
      Function.support (reC1c f : RellichCoord F → ℝ) ⊆ support := by
    intro p hp
    exact hLocalizedSupport f (by
      intro hzero
      apply hp
      change rellichLocalizedRe (F := F) ψ (f : X F → ℂ) p = 0
      exact congrArg Complex.re hzero)
  have hImSupport (f : testSubmodule F Γ) :
      Function.support (imC1c f : RellichCoord F → ℝ) ⊆ support := by
    intro p hp
    exact hLocalizedSupport f (by
      intro hzero
      apply hp
      change rellichLocalizedIm (F := F) ψ (f : X F → ℂ) p = 0
      exact congrArg Complex.im hzero)
  let reMap : testSubmodule F Γ →ₗ[ℝ]
      ↥(RellichEuclidean.h1On support hSupportMeas) :=
    rellichC1cGraphH1OnLinear (F := F) support hSupportMeas reC1c hReSupport
  let imMap : testSubmodule F Γ →ₗ[ℝ]
      ↥(RellichEuclidean.h1On support hSupportMeas) :=
    rellichC1cGraphH1OnLinear (F := F) support hSupportMeas imC1c hImSupport
  have hReProj (f : testSubmodule F Γ) :
      RellichEuclidean.h1OnToL2 support hSupportMeas (reMap f) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (reC1c f) := by
    rfl
  have hImProj (f : testSubmodule F Γ) :
      RellichEuclidean.h1OnToL2 support hSupportMeas (imMap f) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (imC1c f) := by
    rfl
  have hReGradProj (f : testSubmodule F Γ) :
      rellichChartGradient support hSupportMeas (reMap f) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (reC1c f) := by
    rfl
  have hImGradProj (f : testSubmodule F Γ) :
      rellichChartGradient support hSupportMeas (imMap f) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
          (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (imC1c f) := by
    rfl
  have hReI (f : testSubmodule F Γ) : reC1c (Complex.I • f) = -imC1c f := by
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ rellichPosSet F
    · simp [reC1c, imC1c, rellichLocalizedRe, rellichLocalizedIm,
        rellichLocalized, hp, Pi.smul_apply, Complex.mul_re, Complex.mul_im]
    · simp [reC1c, imC1c, rellichLocalizedRe, rellichLocalizedIm,
        rellichLocalized, hp, Pi.smul_apply]
  have hImI (f : testSubmodule F Γ) : imC1c (Complex.I • f) = reC1c f := by
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ rellichPosSet F
    · simp [reC1c, imC1c, rellichLocalizedRe, rellichLocalizedIm,
        rellichLocalized, hp, Pi.smul_apply, Complex.mul_re, Complex.mul_im]
    · simp [reC1c, imC1c, rellichLocalizedRe, rellichLocalizedIm,
        rellichLocalized, hp, Pi.smul_apply]
  have hReMapI (f : testSubmodule F Γ) : reMap (Complex.I • f) = -imMap f := by
    apply Subtype.ext
    change rellichC1cGraphH1Linear (F := F) (reC1c (Complex.I • f)) =
      -rellichC1cGraphH1Linear (F := F) (imC1c f)
    rw [hReI f]
    simp
  have hImMapI (f : testSubmodule F Γ) : imMap (Complex.I • f) = reMap f := by
    apply Subtype.ext
    change rellichC1cGraphH1Linear (F := F) (imC1c (Complex.I • f)) =
      rellichC1cGraphH1Linear (F := F) (reC1c f)
    rw [hImI f]
  refine ⟨{
    support := support
    compact := hSupportCompact
    re := reMap
    im := imMap
    re_rep := ?_
    im_rep := ?_
    re_grad_rep := ?_
    im_grad_rep := ?_
    re_I := ?_
    im_I := ?_ }⟩
  · intro f
    rw [hReProj f]
    exact (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (reC1c f).2).coeFn_toLp
  · intro f
    rw [hImProj f]
    exact (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (imC1c f).2).coeFn_toLp
  · intro f
    rw [hReGradProj f]
    exact (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (reC1c f).2).coeFn_toLp
  · intro f
    rw [hImGradProj f]
    exact (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
      (μ := (volume : Measure (RellichCoord F))) (E := RellichCoord F) (imC1c f).2).coeFn_toLp
  · intro f
    exact hReMapI f
  · intro f
    exact hImMapI f

end ArtinPrimitiveRoots.A1.Spec
