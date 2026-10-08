import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem probe_smooth_meas
    (D : Set (X F)) (f : X F → ℂ) (hf : IsSmoothX F f) :
    AEStronglyMeasurable f ((volX F).restrict D) ∧
    AEStronglyMeasurable (fullGradient F f) ((volX F).restrict D) := by
  classical
  letI : Countable (InfinitePlace F) := by infer_instance
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, hex⟩
  obtain ⟨e, he, hesym⟩ := hex
  letI : SecondCountableTopology (X F) := e.symm.secondCountableTopology
  let w₀ : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hproj : IsOpenQuotientMap (fun z : X F => z w₀) :=
    ⟨(fun z => ⟨fun _ => z, rfl⟩), continuous_apply w₀, isOpenMap_eval w₀⟩
  letI : SecondCountableTopology H3 := Topology.IsOpenQuotientMap.secondCountableTopology hproj
  letI : MeasurableSpace H3 := borel H3
  letI : BorelSpace H3 := ⟨rfl⟩
  have hXBorel : BorelSpace (InfinitePlace F → H3) := Pi.borelSpace
  letI : BorelSpace (X F) := hXBorel
  letI : OpensMeasurableSpace (X F) := BorelSpace.opensMeasurable
  have hcoord : Continuous (coordsX F) := by
    have heq : coordsX F = fun z => (e.symm z).1 := by
      funext z
      exact (hesym z).symm
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  let g : Coord F → ℂ := fun p => f (ptX F p)
  have hgCont : Continuous (fun p : {p : Coord F // p ∈ posSet F} => g p.1) :=
    hf.continuousOn.domRestrict
  have hfeq : f = fun z => g ((e.symm z).1) := by
    funext z
    dsimp [g]
    rw [hesym z]
    exact congrArg f (hptCoord z).symm
  have hfCont : Continuous f := by
    rw [hfeq]
    exact hgCont.comp e.symm.continuous
  have hWmeas : AEStronglyMeasurable f ((volX F).restrict D) :=
    hfCont.aestronglyMeasurable
  have hDeriv : ContDiffOn ℝ ∞ (fderiv ℝ g) (posSet F) :=
    hf.fderiv_of_isOpen (specIdentify_posSet_open (F := F)) (by simp)
  have hGradCoord : ∀ ij : InfinitePlace F × Fin 3,
      Continuous (fun z => placeGradient F ij.1 f z ij.2) := by
    intro ij
    rcases ij with ⟨w, j⟩
    let v := placeDirection F w j
    let ev : (Coord F →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
    have hEvalOn : ContinuousOn (fun p : Coord F => (fderiv ℝ g p) v) (posSet F) := by
      have hev : ContinuousOn ev (Set.univ : Set (Coord F →L[ℝ] ℂ)) :=
        ev.continuous.continuousOn
      exact (ContinuousOn.comp hev hDeriv.continuousOn
        (fun p hp => Set.mem_univ (fderiv ℝ g p)))
    have hPos : ∀ z : X F, coordsX F z ∈ posSet F := by
      intro z
      have hp := (e.symm z).2
      simpa [hesym z] using hp
    have hcoordOn : ContinuousOn (coordsX F) (Set.univ : Set (X F)) := hcoord.continuousOn
    have hPosMaps : Set.MapsTo (coordsX F) Set.univ (posSet F) := fun z hz => hPos z
    have hEval : Continuous fun z : X F => (fderiv ℝ g (coordsX F z)) v :=
      continuousOn_univ.mp (hEvalOn.comp hcoordOn hPosMaps)
    have hheight : Continuous fun z : X F => (coordsX F z w).2 :=
      ((continuous_apply w).comp hcoord).snd
    have hcomp : Continuous fun z : X F =>
        ((coordsX F z w).2 : ℂ) * (fderiv ℝ g (coordsX F z)) v := by
      exact (Complex.ofRealCLM.continuous.comp hheight).mul hEval
    simpa [v, placeGradient, g, Function.comp_def] using hcomp
  have hGradCont : Continuous (fun z => fullGradient F f z) := by
    change Continuous (fun z => WithLp.toLp 2
      (fun ij : InfinitePlace F × Fin 3 => placeGradient F ij.1 f z ij.2))
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : InfinitePlace F × Fin 3 => ℂ)).symm.continuous.comp
      (continuous_pi hGradCoord)
  exact ⟨hWmeas, hGradCont.aestronglyMeasurable⟩

end ArtinPrimitiveRoots.A1.Spec
