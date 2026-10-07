import ArtinPrimitiveRoots.Spec.Geometry
import OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

open OAI.CubicEisenstein

private abbrev GreenSpatial := OAI.CubicEisenstein.EuclideanSpatial

private def greenSpatialOfCoord (c : ℂ × ℝ) : GreenSpatial :=
  WithLp.toLp 2 ![c.1.re, c.1.im, c.2]

private def greenCoordOfSpatial (q : GreenSpatial) : ℂ × ℝ :=
  (((q 0 : ℝ) : ℂ) + Complex.I * (q 1 : ℝ), q 2)

private theorem greenCoordOfSpatial_spatialOfCoord (c : ℂ × ℝ) :
    greenCoordOfSpatial (greenSpatialOfCoord c) = c := by
  rcases c with ⟨x, y⟩
  apply Prod.ext
  · apply Complex.ext <;> simp [greenCoordOfSpatial, greenSpatialOfCoord]
  · simp [greenCoordOfSpatial, greenSpatialOfCoord]

private theorem greenSpatialOfCoord_coordOfSpatial (q : GreenSpatial) :
    greenSpatialOfCoord (greenCoordOfSpatial q) = q := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext j
  fin_cases j <;> simp [greenSpatialOfCoord, greenCoordOfSpatial]

private def greenCoordAction (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F) : Coord F :=
  fun w => greenCoordOfSpatial (OAI.CubicEisenstein.euclideanAction (g w)
    (greenSpatialOfCoord (p w)))

private theorem greenCoordAction_pos (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F)
    : greenCoordAction g p ∈ posSet F := by
  intro w
  change 0 < (greenCoordOfSpatial _).2
  simp only [greenCoordOfSpatial]
  exact OAI.CubicEisenstein.euclideanAction_positive (g w) _

private theorem greenPtCoord_eq_euclideanToHyperbolic (q : GreenSpatial) (hq : 0 < q 2) :
    pt (greenCoordOfSpatial q).1 (greenCoordOfSpatial q).2 =
      OAI.CubicEisenstein.euclideanToHyperbolic q := by
  simpa only [greenCoordOfSpatial] using
    (pt_eq_upperPoint (greenCoordOfSpatial q).1 (greenCoordOfSpatial q).2 hq).trans
      (OAI.CubicEisenstein.euclideanToHyperbolic_positive q hq).symm

private theorem greenPtX_coordAction (g : InfinitePlace F → SL(2, ℂ)) (p : Coord F)
    (hp : p ∈ posSet F) :
    ptX F (greenCoordAction g p) = actAtPlaces F g (ptX F p) := by
  funext w
  let q := greenSpatialOfCoord (p w)
  have hq : 0 < q 2 := by simpa [q, greenSpatialOfCoord] using hp w
  change pt (greenCoordOfSpatial (OAI.CubicEisenstein.euclideanAction (g w) q)).1
      (greenCoordOfSpatial (OAI.CubicEisenstein.euclideanAction (g w) q)).2 =
    (g w) • pt (p w).1 (p w).2
  rw [← greenCoordOfSpatial_spatialOfCoord (p w)]
  rw [greenPtCoord_eq_euclideanToHyperbolic _
      (OAI.CubicEisenstein.euclideanAction_positive (g w) q),
    greenPtCoord_eq_euclideanToHyperbolic q hq]
  change OAI.CubicEisenstein.euclideanToHyperbolic
      (OAI.CubicEisenstein.hyperbolicEuclideanCoordinates
        ((g w) • OAI.CubicEisenstein.euclideanToHyperbolic q)) = _
  exact OAI.CubicEisenstein.euclideanToHyperbolic_coordinates _

private def greenSpatialPairLinear : GreenSpatial →L[ℝ] (ℂ × ℝ) where
  toLinearMap :=
    { toFun := greenCoordOfSpatial
      map_add' := by
        intro q q'
        apply Prod.ext
        · simp [greenCoordOfSpatial, Complex.ofReal_add]
          ring
        · rfl
      map_smul' := by
        intro c q
        apply Prod.ext
        · simp [greenCoordOfSpatial, Complex.ofReal_mul, smul_eq_mul]
          ring
        · rfl }
  cont := by
    change Continuous (fun q : GreenSpatial =>
      (((q 0 : ℝ) : ℂ) + Complex.I * (q 1 : ℝ), q 2))
    fun_prop

private def greenCoordSliceLinear (w : InfinitePlace F) :
    GreenSpatial →L[ℝ] Coord F :=
  ContinuousLinearMap.pi fun v => if v = w then greenSpatialPairLinear else 0

private def greenCoordSlice (p : Coord F) (w : InfinitePlace F) (q : GreenSpatial) :
    Coord F := greenCoordSliceLinear w q + Function.update p w (0, 0)

private theorem greenCoordSlice_same (p : Coord F) (w : InfinitePlace F)
    (q : GreenSpatial) : greenCoordSlice p w q w = greenCoordOfSpatial q := by
  simp [greenCoordSlice, greenCoordSliceLinear, greenSpatialPairLinear]

private theorem greenCoordSlice_other (p : Coord F) (w v : InfinitePlace F)
    (q : GreenSpatial) (hv : v ≠ w) : greenCoordSlice p w q v = p v := by
  simp [greenCoordSlice, greenCoordSliceLinear, hv]

private theorem greenCoordSlice_spatialOfCoord (p : Coord F) (w : InfinitePlace F) :
    greenCoordSlice p w (greenSpatialOfCoord (p w)) = p := by
  funext v
  by_cases hv : v = w
  · subst v
    simp [greenCoordSlice_same, greenCoordOfSpatial_spatialOfCoord]
  · rw [greenCoordSlice_other _ _ _ _ hv]

private theorem greenCoordAction_slice (g : InfinitePlace F → SL(2, ℂ))
    (p : Coord F) (w : InfinitePlace F) (q : GreenSpatial) :
    greenCoordAction g (greenCoordSlice p w q) =
      greenCoordSlice (greenCoordAction g p) w
        (OAI.CubicEisenstein.euclideanAction (g w) q) := by
  funext v
  by_cases hv : v = w
  · subst v
    simp [greenCoordAction, greenCoordSlice_same, greenSpatialOfCoord_coordOfSpatial]
  · simp [greenCoordAction, greenCoordSlice_other _ _ _ _ hv]

private theorem greenCoordSliceLinear_basis (w : InfinitePlace F) (j : Fin 3) :
    greenCoordSliceLinear w (WithLp.toLp 2 (Pi.single j (1 : ℝ))) =
      placeDirection F w j := by
  funext v
  by_cases hv : v = w
  · subst v
    fin_cases j <;>
      simp [greenCoordSliceLinear, greenSpatialPairLinear, greenCoordOfSpatial,
        placeDirection]
  · fin_cases j <;>
      simp [greenCoordSliceLinear, greenSpatialPairLinear, greenCoordOfSpatial,
        placeDirection, hv]

private theorem greenCoordSlice_hasFDerivAt (p : Coord F) (w : InfinitePlace F)
    (q : GreenSpatial) :
    HasFDerivAt (greenCoordSlice p w) (greenCoordSliceLinear w) q := by
  simpa [greenCoordSlice] using
    (greenCoordSliceLinear w).hasFDerivAt |>.add_const (Function.update p w (0, 0))

private theorem greenPosSet_isOpen : IsOpen (posSet F) := by
  classical
  have hc : ∀ w : InfinitePlace F, Continuous (fun p : Coord F => (p w).2) := by
    intro w
    fun_prop
  have heq : posSet F = ⋂ w : InfinitePlace F, {p : Coord F | 0 < (p w).2} := by
    ext p
    simp [posSet]
  rw [heq]
  exact isOpen_iInter_of_finite fun w : InfinitePlace F =>
    isOpen_lt (continuous_const : Continuous fun _ : Coord F => (0 : ℝ)) (hc w)

private theorem greenCoordAction_differentiableAt (g : InfinitePlace F → SL(2, ℂ))
    (p : Coord F) (hp : p ∈ posSet F) :
    DifferentiableAt ℝ (greenCoordAction g) p := by
  classical
  apply differentiableAt_pi.2
  intro w
  have hproj : DifferentiableAt ℝ (fun p : Coord F => p w) p := by fun_prop
  have hinput : DifferentiableAt ℝ greenSpatialOfCoord (p w) := by
    have hv : DifferentiableAt ℝ
        (fun c : ℂ × ℝ => ![c.1.re, c.1.im, c.2]) (p w) := by
      apply differentiableAt_pi.2
      intro j
      fin_cases j <;> simp <;> fun_prop
    have hLp : DifferentiableAt ℝ (fun v : Fin 3 → ℝ => WithLp.toLp 2 v)
        ![(p w).1.re, (p w).1.im, (p w).2] := by
      simpa only [PiLp.coe_symm_continuousLinearEquiv] using
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiableAt
    simpa [greenSpatialOfCoord] using hLp.comp (p w) hv
  have hq : 0 < (greenSpatialOfCoord (p w)) 2 := by
    simpa [greenSpatialOfCoord] using hp w
  obtain ⟨A, hA, _⟩ :=
    OAI.CubicEisenstein.hyperbolicDifferentialIsometry (g w)
      (greenSpatialOfCoord (p w)) hq
  have hmid : DifferentiableAt ℝ (OAI.CubicEisenstein.euclideanAction (g w))
      (greenSpatialOfCoord (p w)) := hA.differentiableAt
  have hout : DifferentiableAt ℝ greenCoordOfSpatial
      (OAI.CubicEisenstein.euclideanAction (g w) (greenSpatialOfCoord (p w))) := by
    fun_prop [greenCoordOfSpatial]
  have hMidPair : DifferentiableAt ℝ
      (fun c : ℂ × ℝ => OAI.CubicEisenstein.euclideanAction (g w)
        (greenSpatialOfCoord c)) (p w) := hmid.comp (p w) hinput
  have hLocal : DifferentiableAt ℝ
      (fun c : ℂ × ℝ => greenCoordOfSpatial
        (OAI.CubicEisenstein.euclideanAction (g w) (greenSpatialOfCoord c))) (p w) :=
    hout.comp (p w) hMidPair
  have hinner : DifferentiableAt ℝ
      (fun x : Coord F => greenCoordOfSpatial
        (OAI.CubicEisenstein.euclideanAction (g w) (greenSpatialOfCoord (x w)))) p :=
    hLocal.comp p hproj
  simpa [greenCoordAction] using hinner

private theorem greenChartAction_eventuallyEq (g : InfinitePlace F → SL(2, ℂ))
    (f : X F → ℂ) (p : Coord F) (hp : p ∈ posSet F) :
    (fun q => f (actAtPlaces F g (ptX F q))) =ᶠ[𝓝 p]
      (fun q => f (ptX F (greenCoordAction g q))) := by
  filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
  rw [← greenPtX_coordAction g q hq]

private theorem greenChartAction_differentiableAt (g : InfinitePlace F → SL(2, ℂ))
    (f : X F → ℂ) (hf : IsSmoothX F f) (p : Coord F) (hp : p ∈ posSet F) :
    DifferentiableAt ℝ (fun q => f (actAtPlaces F g (ptX F q))) p := by
  have hp' : greenCoordAction g p ∈ posSet F := greenCoordAction_pos g p
  have hfAt : DifferentiableAt ℝ (fun q => f (ptX F q)) (greenCoordAction g p) := by
    change ContDiffOn ℝ ∞ (fun q => f (ptX F q)) (posSet F) at hf
    exact (hf.differentiableOn (by simp)).differentiableAt
      (greenPosSet_isOpen.mem_nhds hp')
  have hcomp : DifferentiableAt ℝ
      ((fun q => f (ptX F q)) ∘ greenCoordAction g) p :=
    hfAt.comp p (greenCoordAction_differentiableAt g p hp)
  exact (hcomp.hasFDerivAt.congr_of_eventuallyEq
    (greenChartAction_eventuallyEq g f p hp)).differentiableAt

private theorem greenFDeriv_coordSlice_apply {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (H : Coord F → G) (p : Coord F) (w : InfinitePlace F)
    (q : GreenSpatial) (hH : DifferentiableAt ℝ H (greenCoordSlice p w q))
    (j : Fin 3) :
    fderiv ℝ (fun q' => H (greenCoordSlice p w q')) q
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) =
    fderiv ℝ H (greenCoordSlice p w q) (placeDirection F w j) := by
  have hcomp := hH.hasFDerivAt.comp q (greenCoordSlice_hasFDerivAt p w q)
  change (fderiv ℝ (H ∘ greenCoordSlice p w) q)
      (WithLp.toLp 2 (Pi.single j (1 : ℝ))) = _
  rw [hcomp.fderiv]
  simpa only [ContinuousLinearMap.comp_apply, greenCoordSliceLinear_basis]

private def greenRealEnergy (H : Coord F → ℝ) (p : Coord F) (w : InfinitePlace F) : ℝ :=
  ∑ j : Fin 3, ((p w).2 * fderiv ℝ H p (placeDirection F w j)) ^ 2

private theorem greenRealEnergy_action (g : InfinitePlace F → SL(2, ℂ))
    (H : Coord F → ℝ) (p : Coord F) (w : InfinitePlace F) (hp : p ∈ posSet F)
    (hH : DifferentiableAt ℝ H (greenCoordAction g p)) :
    greenRealEnergy (fun x => H (greenCoordAction g x)) p w =
      greenRealEnergy H (greenCoordAction g p) w := by
  let p' := greenCoordAction g p
  let q := greenSpatialOfCoord (p w)
  let q' := OAI.CubicEisenstein.euclideanAction (g w) q
  have hq : 0 < q 2 := by simpa [q, greenSpatialOfCoord] using hp w
  have hp' : p' ∈ posSet F := by
    simpa [p'] using greenCoordAction_pos g p
  have hq0 : greenCoordSlice p w q = p := by
    exact greenCoordSlice_spatialOfCoord p w
  have hq'coord : greenSpatialOfCoord (p' w) = q' := by
    simp [p', q', greenCoordAction, greenSpatialOfCoord_coordOfSpatial]
  have hq'base : greenCoordSlice p' w q' = p' := by
    rw [← hq'coord]
    exact greenCoordSlice_spatialOfCoord p' w
  have hY0 : q 2 = (p w).2 := by simp [q, greenSpatialOfCoord]
  have hY1 : q' 2 = (p' w).2 := by simp [p', q', greenCoordAction, greenCoordOfSpatial]
  have hK : DifferentiableAt ℝ (fun x => H (greenCoordAction g x)) p :=
    hH.comp p (greenCoordAction_differentiableAt g p hp)
  have hKslice : DifferentiableAt ℝ (fun x => H (greenCoordAction g x))
      (greenCoordSlice p w q) := by simpa [hq0] using hK
  have hBpoint : DifferentiableAt ℝ H (greenCoordSlice p' w q') := by
    simpa [hq'base] using hH
  have hB : DifferentiableAt ℝ (fun x => H (greenCoordSlice p' w x)) q' := by
    exact hBpoint.comp q' (greenCoordSlice_hasFDerivAt p' w q')
  let A : GreenSpatial → ℝ := fun x => H (greenCoordAction g (greenCoordSlice p w x))
  let B : GreenSpatial → ℝ := fun x => H (greenCoordSlice p' w x)
  have hAB : A = B ∘ OAI.CubicEisenstein.euclideanAction (g w) := by
    funext x
    simp [A, B, p', greenCoordAction_slice]
  have hOAI := OAI.CubicEisenstein.hyperbolic_cotangent_energy_comp
    (g w) B q hq hB
  have hOAI' : q 2 ^ 2 * ‖fderiv ℝ A q‖ ^ 2 =
      q' 2 ^ 2 * ‖fderiv ℝ B q'‖ ^ 2 := by
    simpa [A, B, q', hAB] using hOAI
  let b : OrthonormalBasis (Fin 3) ℝ GreenSpatial :=
    EuclideanSpace.basisFun (Fin 3) ℝ
  have hsumNorm (V : GreenSpatial → ℝ) (x : GreenSpatial) :
      ∑ j : Fin 3, (x 2 * fderiv ℝ V x (b j)) ^ 2 =
        x 2 ^ 2 * ‖fderiv ℝ V x‖ ^ 2 := by
    calc
      _ = x 2 ^ 2 * ∑ j : Fin 3, (fderiv ℝ V x (b j)) ^ 2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum]
      _ = _ := by rw [b.norm_dual]
  have hKdir (j : Fin 3) :
      fderiv ℝ (fun x => H (greenCoordAction g x)) p (placeDirection F w j) =
        fderiv ℝ A q (b j) := by
    have h := greenFDeriv_coordSlice_apply
      (fun x => H (greenCoordAction g x)) p w q hKslice j
    have hb : b j = WithLp.toLp 2 (Pi.single j (1 : ℝ)) := by
      simp [b, EuclideanSpace.basisFun]
    rw [hb]
    simpa [A, hq0] using h.symm
  have hBdir (j : Fin 3) :
      fderiv ℝ H (p') (placeDirection F w j) = fderiv ℝ B q' (b j) := by
    have h := greenFDeriv_coordSlice_apply H p' w q' hBpoint j
    have hb : b j = WithLp.toLp 2 (Pi.single j (1 : ℝ)) := by
      simp [b, EuclideanSpace.basisFun]
    rw [hb]
    simpa [B, hq'base] using h.symm
  calc
    greenRealEnergy (fun x => H (greenCoordAction g x)) p w =
        ∑ j : Fin 3, (q 2 * fderiv ℝ A q (b j)) ^ 2 := by
      unfold greenRealEnergy
      rw [← hY0]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hKdir]
    _ = q 2 ^ 2 * ‖fderiv ℝ A q‖ ^ 2 := hsumNorm A q
    _ = q' 2 ^ 2 * ‖fderiv ℝ B q'‖ ^ 2 := hOAI'
    _ = greenRealEnergy H p' w := by
      symm
      unfold greenRealEnergy
      rw [hY1]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBdir]
      exact hsumNorm B q'

end ArtinPrimitiveRoots.A1.Spec
