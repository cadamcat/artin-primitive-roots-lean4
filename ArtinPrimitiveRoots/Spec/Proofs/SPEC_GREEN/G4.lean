import ArtinPrimitiveRoots.Spec.Geometry
import OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.BigOperators.Fin

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

private theorem greenSpatialOfCoord_differentiableAt (c : ℂ × ℝ) :
    DifferentiableAt ℝ greenSpatialOfCoord c := by
  have hv : DifferentiableAt ℝ (fun c : ℂ × ℝ => ![c.1.re, c.1.im, c.2]) c := by
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp <;> fun_prop
  have hLp : DifferentiableAt ℝ (fun v : Fin 3 → ℝ => (WithLp.toLp 2 v : GreenSpatial))
      ![c.1.re, c.1.im, c.2] :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiableAt
  exact hLp.comp c hv

private theorem greenCoordAction_differentiableAt (g : InfinitePlace F → SL(2, ℂ))
    (p : Coord F) (hp : p ∈ posSet F) :
    DifferentiableAt ℝ (greenCoordAction g) p := by
  classical
  apply differentiableAt_pi.2
  intro w
  have hproj : DifferentiableAt ℝ (fun p : Coord F => p w) p := by fun_prop
  have hinput := greenSpatialOfCoord_differentiableAt (p w)
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
  have hF : DifferentiableAt ℝ
      (greenCoordOfSpatial ∘ (euclideanAction (g w) ∘ greenSpatialOfCoord)) (p w) :=
    hout.comp (p w) (hmid.comp (p w) hinput)
  have hcomp : DifferentiableAt ℝ
      ((greenCoordOfSpatial ∘ (euclideanAction (g w) ∘ greenSpatialOfCoord)) ∘ (fun p => p w)) p :=
    hF.comp p hproj
  exact hcomp

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
  simp only [ContinuousLinearMap.comp_apply, greenCoordSliceLinear_basis]

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
    dsimp [p', q', greenCoordAction]
    rw [greenSpatialOfCoord_coordOfSpatial]
  have hq'base : greenCoordSlice p' w q' = p' := by
    rw [← hq'coord]
    exact greenCoordSlice_spatialOfCoord p' w
  have hY0 : q 2 = (p w).2 := by simp [q, greenSpatialOfCoord]
  have hY1 : q' 2 = (p' w).2 := rfl
  have hK : DifferentiableAt ℝ (fun x => H (greenCoordAction g x)) p :=
    hH.comp p (greenCoordAction_differentiableAt g p hp)
  have hKslice : DifferentiableAt ℝ (fun x => H (greenCoordAction g x))
      (greenCoordSlice p w q) := by simpa [hq0] using hK
  have hBpoint : DifferentiableAt ℝ H (greenCoordSlice p' w q') := by
    simpa [hq'base] using hH
  have hB : DifferentiableAt ℝ (fun x => H (greenCoordSlice p' w x)) q' := by
    exact hBpoint.comp q' (greenCoordSlice_hasFDerivAt p' w q').differentiableAt
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
      rw [EuclideanSpace.basisFun_apply]
      rfl
    rw [hb]
    simpa [A, hq0] using h.symm
  have hBdir (j : Fin 3) :
      fderiv ℝ H (p') (placeDirection F w j) = fderiv ℝ B q' (b j) := by
    have h := greenFDeriv_coordSlice_apply H p' w q' hBpoint j
    have hb : b j = WithLp.toLp 2 (Pi.single j (1 : ℝ)) := by
      rw [EuclideanSpace.basisFun_apply]
      rfl
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
    _ = ∑ j : Fin 3, (q' 2 * fderiv ℝ B q' (b j)) ^ 2 := (hsumNorm B q').symm
    _ = greenRealEnergy H p' w := by
      unfold greenRealEnergy
      rw [hY1]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBdir]

private def greenRealBilinear (H₁ H₂ : Coord F → ℝ) (p : Coord F) (w : InfinitePlace F) : ℝ :=
  ∑ j : Fin 3, ((p w).2 * fderiv ℝ H₁ p (placeDirection F w j)) *
    ((p w).2 * fderiv ℝ H₂ p (placeDirection F w j))

private theorem greenRealEnergy_add (H₁ H₂ : Coord F → ℝ) (p : Coord F) (w : InfinitePlace F)
    (h₁ : DifferentiableAt ℝ H₁ p) (h₂ : DifferentiableAt ℝ H₂ p) :
    greenRealEnergy (H₁ + H₂) p w =
      greenRealEnergy H₁ p w + greenRealEnergy H₂ p w + 2 * greenRealBilinear H₁ H₂ p w := by
  unfold greenRealEnergy greenRealBilinear
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hsum : fderiv ℝ (H₁ + H₂) p (placeDirection F w j) =
      fderiv ℝ H₁ p (placeDirection F w j) + fderiv ℝ H₂ p (placeDirection F w j) := by
    rw [fderiv_add h₁ h₂]
    rfl
  rw [hsum]
  ring

private theorem greenRealBilinear_action (g : InfinitePlace F → SL(2, ℂ))
    (H₁ H₂ : Coord F → ℝ) (p : Coord F) (w : InfinitePlace F) (hp : p ∈ posSet F)
    (h₁ : DifferentiableAt ℝ H₁ (greenCoordAction g p))
    (h₂ : DifferentiableAt ℝ H₂ (greenCoordAction g p)) :
    greenRealBilinear (fun x => H₁ (greenCoordAction g x))
      (fun x => H₂ (greenCoordAction g x)) p w =
      greenRealBilinear H₁ H₂ (greenCoordAction g p) w := by
  have hK₁ : DifferentiableAt ℝ (fun x => H₁ (greenCoordAction g x)) p :=
    h₁.comp p (greenCoordAction_differentiableAt g p hp)
  have hK₂ : DifferentiableAt ℝ (fun x => H₂ (greenCoordAction g x)) p :=
    h₂.comp p (greenCoordAction_differentiableAt g p hp)
  have hE₁ := greenRealEnergy_action g H₁ p w hp h₁
  have hE₂ := greenRealEnergy_action g H₂ p w hp h₂
  have hE12 := greenRealEnergy_action g (H₁ + H₂) p w hp (h₁.add h₂)
  have hL := greenRealEnergy_add (fun x => H₁ (greenCoordAction g x))
    (fun x => H₂ (greenCoordAction g x)) p w hK₁ hK₂
  have hR := greenRealEnergy_add H₁ H₂ (greenCoordAction g p) w h₁ h₂
  change greenRealEnergy (fun x => (H₁ + H₂) (greenCoordAction g x)) p w = _ at hL
  linarith

private theorem greenFDeriv_complex_eq (F₀ : Coord F → ℂ) (p : Coord F)
    (hF : DifferentiableAt ℝ F₀ p) (v : Coord F) :
    fderiv ℝ F₀ p v = (((fderiv ℝ (fun q => (F₀ q).re) p v : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ (fun q => (F₀ q).im) p v : ℝ) : ℂ)) := by
  have hre : fderiv ℝ (fun q => (F₀ q).re) p v = (fderiv ℝ F₀ p v).re := by
    have h := fderiv_comp p Complex.reCLM.differentiableAt hF
    have hL := Complex.reCLM.fderiv (x := F₀ p)
    change fderiv ℝ (Complex.reCLM ∘ F₀) p v = _
    rw [h, hL]
    rfl
  have him : fderiv ℝ (fun q => (F₀ q).im) p v = (fderiv ℝ F₀ p v).im := by
    have h := fderiv_comp p Complex.imCLM.differentiableAt hF
    have hL := Complex.imCLM.fderiv (x := F₀ p)
    change fderiv ℝ (Complex.imCLM ∘ F₀) p v = _
    rw [h, hL]
    rfl
  apply Complex.ext
  · simp [hre]
  · simp [him]

private lemma star_mul_complex_identity (Y A B C D : ℝ) :
    star ((Y : ℂ) * ((A : ℂ) + Complex.I * (B : ℂ))) *
      ((Y : ℂ) * ((C : ℂ) + Complex.I * (D : ℂ))) =
    (((Y * A * (Y * C) + Y * B * (Y * D) : ℝ) : ℂ) +
      Complex.I * (((Y * A * (Y * D) - Y * B * (Y * C) : ℝ) : ℂ))) := by
  apply Complex.ext
  · simp
  · simp; ring

private theorem placeGradInner_eq_bilinear (w : InfinitePlace F) (f f' : X F → ℂ) (z : X F)
    (hf : DifferentiableAt ℝ (fun q => f (ptX F q)) (coordsX F z))
    (hf' : DifferentiableAt ℝ (fun q => f' (ptX F q)) (coordsX F z)) :
    placeGradInner F w f f' z =
      ((greenRealBilinear (fun q => (f (ptX F q)).re) (fun q => (f' (ptX F q)).re) (coordsX F z) w +
        greenRealBilinear (fun q => (f (ptX F q)).im) (fun q => (f' (ptX F q)).im) (coordsX F z) w : ℝ) : ℂ) +
      Complex.I *
      ((greenRealBilinear (fun q => (f (ptX F q)).re) (fun q => (f' (ptX F q)).im) (coordsX F z) w -
        greenRealBilinear (fun q => (f (ptX F q)).im) (fun q => (f' (ptX F q)).re) (coordsX F z) w : ℝ) : ℂ) := by
  unfold placeGradInner placeGradient greenRealBilinear
  let p := coordsX F z
  have hterm (j : Fin 3) :
      star (((p w).2 : ℂ) * fderiv ℝ (f ∘ ptX F) p (placeDirection F w j)) *
        (((p w).2 : ℂ) * fderiv ℝ (f' ∘ ptX F) p (placeDirection F w j)) =
      ((((p w).2 * fderiv ℝ (fun q => (f (ptX F q)).re) p (placeDirection F w j) *
          ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).re) p (placeDirection F w j)) +
        (p w).2 * fderiv ℝ (fun q => (f (ptX F q)).im) p (placeDirection F w j) *
          ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).im) p (placeDirection F w j)) : ℝ) : ℂ) +
        Complex.I *
        (((p w).2 * fderiv ℝ (fun q => (f (ptX F q)).re) p (placeDirection F w j) *
            ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).im) p (placeDirection F w j)) -
          (p w).2 * fderiv ℝ (fun q => (f (ptX F q)).im) p (placeDirection F w j) *
            ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).re) p (placeDirection F w j)) : ℝ) : ℂ)) := by
    rw [greenFDeriv_complex_eq (f ∘ ptX F) p hf (placeDirection F w j)]
    rw [greenFDeriv_complex_eq (f' ∘ ptX F) p hf' (placeDirection F w j)]
    exact star_mul_complex_identity ((p w).2) _ _ _ _
  calc
    ∑ j : Fin 3, star (((p w).2 : ℂ) * fderiv ℝ (f ∘ ptX F) p (placeDirection F w j)) *
        (((p w).2 : ℂ) * fderiv ℝ (f' ∘ ptX F) p (placeDirection F w j)) =
      ∑ j : Fin 3, ((((p w).2 * fderiv ℝ (fun q => (f (ptX F q)).re) p (placeDirection F w j) *
            ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).re) p (placeDirection F w j)) +
          (p w).2 * fderiv ℝ (fun q => (f (ptX F q)).im) p (placeDirection F w j) *
            ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).im) p (placeDirection F w j)) : ℝ) : ℂ) +
          Complex.I *
          (((p w).2 * fderiv ℝ (fun q => (f (ptX F q)).re) p (placeDirection F w j) *
              ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).im) p (placeDirection F w j)) -
            (p w).2 * fderiv ℝ (fun q => (f (ptX F q)).im) p (placeDirection F w j) *
              ((p w).2 * fderiv ℝ (fun q => (f' (ptX F q)).re) p (placeDirection F w j)) : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
    _ = _ := by
      push_cast
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      rfl

private theorem greenCoordsX_pos (z : X F) : coordsX F z ∈ posSet F := by
  intro w
  change 0 < height (z w)
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem greenCoordsX_ptX (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (ptX F p) = p := by
  have hp' : ∀ w, 0 < (p w).2 := by simpa [posSet] using hp
  funext w
  simp [coordsX, ptX, horiz_pt, height_pt, hp' w]

private theorem greenPtX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  funext w
  exact pt_horiz_height (z w)

private theorem greenCoordsX_act (g : InfinitePlace F → SL(2, ℂ)) (z : X F) :
    coordsX F (actAtPlaces F g z) = greenCoordAction g (coordsX F z) := by
  let p := coordsX F z
  have hp : p ∈ posSet F := greenCoordsX_pos z
  have hp' : greenCoordAction g p ∈ posSet F := greenCoordAction_pos g p
  have hpt : ptX F (greenCoordAction g p) = actAtPlaces F g z := by
    rw [greenPtX_coordAction g p hp, greenPtX_coordsX z]
  rw [← hpt, greenCoordsX_ptX _ hp']

theorem greenPlaceGradInner_action (g : InfinitePlace F → SL(2, ℂ))
    (f f' : X F → ℂ) (hf : IsSmoothX F f) (hf' : IsSmoothX F f')
    (w : InfinitePlace F) (z : X F) :
    placeGradInner F w (fun x => f (actAtPlaces F g x))
      (fun x => f' (actAtPlaces F g x)) z =
      placeGradInner F w f f' (actAtPlaces F g z) := by
  let p := coordsX F z
  have hp : p ∈ posSet F := greenCoordsX_pos z
  have hp' : greenCoordAction g p ∈ posSet F := greenCoordAction_pos g p
  have hf_diff : DifferentiableAt ℝ (fun q => f (ptX F q)) (greenCoordAction g p) := by
    change ContDiffOn ℝ ∞ (fun q => f (ptX F q)) (posSet F) at hf
    exact (hf.differentiableOn (by simp)).differentiableAt
      (greenPosSet_isOpen.mem_nhds hp')
  have hf'_diff : DifferentiableAt ℝ (fun q => f' (ptX F q)) (greenCoordAction g p) := by
    change ContDiffOn ℝ ∞ (fun q => f' (ptX F q)) (posSet F) at hf'
    exact (hf'.differentiableOn (by simp)).differentiableAt
      (greenPosSet_isOpen.mem_nhds hp')
  have hfg_diff : DifferentiableAt ℝ (fun q => f (actAtPlaces F g (ptX F q))) p :=
    greenChartAction_differentiableAt g f hf p hp
  have hf'g_diff : DifferentiableAt ℝ (fun q => f' (actAtPlaces F g (ptX F q))) p :=
    greenChartAction_differentiableAt g f' hf' p hp
  have hre_f :
      fderiv ℝ (fun q => (f (actAtPlaces F g (ptX F q))).re) p =
        fderiv ℝ (fun q => (f (ptX F (greenCoordAction g q))).re) p := by
    have heq : (fun q => (f (actAtPlaces F g (ptX F q))).re) =ᶠ[𝓝 p]
        (fun q => (f (ptX F (greenCoordAction g q))).re) := by
      filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
      rw [← greenPtX_coordAction g q hq]
    exact Filter.EventuallyEq.fderiv_eq heq
  have him_f :
      fderiv ℝ (fun q => (f (actAtPlaces F g (ptX F q))).im) p =
        fderiv ℝ (fun q => (f (ptX F (greenCoordAction g q))).im) p := by
    have heq : (fun q => (f (actAtPlaces F g (ptX F q))).im) =ᶠ[𝓝 p]
        (fun q => (f (ptX F (greenCoordAction g q))).im) := by
      filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
      rw [← greenPtX_coordAction g q hq]
    exact Filter.EventuallyEq.fderiv_eq heq
  have hre_f' :
      fderiv ℝ (fun q => (f' (actAtPlaces F g (ptX F q))).re) p =
        fderiv ℝ (fun q => (f' (ptX F (greenCoordAction g q))).re) p := by
    have heq : (fun q => (f' (actAtPlaces F g (ptX F q))).re) =ᶠ[𝓝 p]
        (fun q => (f' (ptX F (greenCoordAction g q))).re) := by
      filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
      rw [← greenPtX_coordAction g q hq]
    exact Filter.EventuallyEq.fderiv_eq heq
  have him_f' :
      fderiv ℝ (fun q => (f' (actAtPlaces F g (ptX F q))).im) p =
        fderiv ℝ (fun q => (f' (ptX F (greenCoordAction g q))).im) p := by
    have heq : (fun q => (f' (actAtPlaces F g (ptX F q))).im) =ᶠ[𝓝 p]
        (fun q => (f' (ptX F (greenCoordAction g q))).im) := by
      filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
      rw [← greenPtX_coordAction g q hq]
    exact Filter.EventuallyEq.fderiv_eq heq
  let H_re := fun q => (f (ptX F q)).re
  let H_im := fun q => (f (ptX F q)).im
  let H'_re := fun q => (f' (ptX F q)).re
  let H'_im := fun q => (f' (ptX F q)).im
  have hH_re : DifferentiableAt ℝ H_re (greenCoordAction g p) :=
    Complex.reCLM.differentiableAt.comp (greenCoordAction g p) hf_diff
  have hH_im : DifferentiableAt ℝ H_im (greenCoordAction g p) :=
    Complex.imCLM.differentiableAt.comp (greenCoordAction g p) hf_diff
  have hH'_re : DifferentiableAt ℝ H'_re (greenCoordAction g p) :=
    Complex.reCLM.differentiableAt.comp (greenCoordAction g p) hf'_diff
  have hH'_im : DifferentiableAt ℝ H'_im (greenCoordAction g p) :=
    Complex.imCLM.differentiableAt.comp (greenCoordAction g p) hf'_diff
  have hB_re_re :
      greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).re)
        (fun q => (f' (actAtPlaces F g (ptX F q))).re) p w =
        greenRealBilinear H_re H'_re (coordsX F (actAtPlaces F g z)) w := by
    have h_eq : greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).re)
        (fun q => (f' (actAtPlaces F g (ptX F q))).re) p w =
        greenRealBilinear (fun x => H_re (greenCoordAction g x))
          (fun x => H'_re (greenCoordAction g x)) p w := by
      unfold greenRealBilinear
      rw [hre_f, hre_f']
    rw [h_eq, greenRealBilinear_action g H_re H'_re p w hp hH_re hH'_re, greenCoordsX_act]
  have hB_im_im :
      greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).im)
        (fun q => (f' (actAtPlaces F g (ptX F q))).im) p w =
        greenRealBilinear H_im H'_im (coordsX F (actAtPlaces F g z)) w := by
    have h_eq : greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).im)
        (fun q => (f' (actAtPlaces F g (ptX F q))).im) p w =
        greenRealBilinear (fun x => H_im (greenCoordAction g x))
          (fun x => H'_im (greenCoordAction g x)) p w := by
      unfold greenRealBilinear
      rw [him_f, him_f']
    rw [h_eq, greenRealBilinear_action g H_im H'_im p w hp hH_im hH'_im, greenCoordsX_act]
  have hB_re_im :
      greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).re)
        (fun q => (f' (actAtPlaces F g (ptX F q))).im) p w =
        greenRealBilinear H_re H'_im (coordsX F (actAtPlaces F g z)) w := by
    have h_eq : greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).re)
        (fun q => (f' (actAtPlaces F g (ptX F q))).im) p w =
        greenRealBilinear (fun x => H_re (greenCoordAction g x))
          (fun x => H'_im (greenCoordAction g x)) p w := by
      unfold greenRealBilinear
      rw [hre_f, him_f']
    rw [h_eq, greenRealBilinear_action g H_re H'_im p w hp hH_re hH'_im, greenCoordsX_act]
  have hB_im_re :
      greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).im)
        (fun q => (f' (actAtPlaces F g (ptX F q))).re) p w =
        greenRealBilinear H_im H'_re (coordsX F (actAtPlaces F g z)) w := by
    have h_eq : greenRealBilinear (fun q => (f (actAtPlaces F g (ptX F q))).im)
        (fun q => (f' (actAtPlaces F g (ptX F q))).re) p w =
        greenRealBilinear (fun x => H_im (greenCoordAction g x))
          (fun x => H'_re (greenCoordAction g x)) p w := by
      unfold greenRealBilinear
      rw [him_f, hre_f']
    rw [h_eq, greenRealBilinear_action g H_im H'_re p w hp hH_im hH'_re, greenCoordsX_act]
  rw [placeGradInner_eq_bilinear w (fun x => f (actAtPlaces F g x))
    (fun x => f' (actAtPlaces F g x)) z hfg_diff hf'g_diff]
  rw [hB_re_re, hB_im_im, hB_re_im, hB_im_re]
  have h_act_z : coordsX F (actAtPlaces F g z) ∈ posSet F :=
    greenCoordsX_pos (actAtPlaces F g z)
  have hf_diff_act : DifferentiableAt ℝ (fun q => f (ptX F q)) (coordsX F (actAtPlaces F g z)) := by
    change ContDiffOn ℝ ∞ (fun q => f (ptX F q)) (posSet F) at hf
    exact (hf.differentiableOn (by simp)).differentiableAt
      (greenPosSet_isOpen.mem_nhds h_act_z)
  have hf'_diff_act : DifferentiableAt ℝ (fun q => f' (ptX F q)) (coordsX F (actAtPlaces F g z)) := by
    change ContDiffOn ℝ ∞ (fun q => f' (ptX F q)) (posSet F) at hf'
    exact (hf'.differentiableOn (by simp)).differentiableAt
      (greenPosSet_isOpen.mem_nhds h_act_z)
  rw [placeGradInner_eq_bilinear w f f' (actAtPlaces F g z) hf_diff_act hf'_diff_act]

theorem placeGradNormSq_eq_inner (w : InfinitePlace F) (f : X F → ℂ) (z : X F) :
    (placeGradNormSq F w f z : ℂ) = placeGradInner F w f f z := by
  unfold placeGradNormSq placeGradInner
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  apply Complex.ext
  · simp [Complex.normSq]
  · simp; ring

theorem greenTotalGradNormSq_action (g : InfinitePlace F → SL(2, ℂ))
    (f : X F → ℂ) (hf : IsSmoothX F f) (z : X F) :
    totalGradNormSq F (fun x => f (actAtPlaces F g x)) z =
      totalGradNormSq F f (actAtPlaces F g z) := by
  unfold totalGradNormSq
  apply Finset.sum_congr rfl
  intro w _
  have h_inner := greenPlaceGradInner_action g f f hf hf w z
  have h_cast : ((placeGradNormSq F w (fun x => f (actAtPlaces F g x)) z : ℂ)) =
      ((placeGradNormSq F w f (actAtPlaces F g z) : ℂ)) := by
    rw [placeGradNormSq_eq_inner, h_inner, ← placeGradNormSq_eq_inner]
  exact_mod_cast h_cast

private def greenCoordHeightCLM (v : InfinitePlace F) : Coord F →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj (R := ℝ) v)

private lemma greenCoordHeightCLM_placeDirection (w v : InfinitePlace F) (j : Fin 3) :
    greenCoordHeightCLM v (placeDirection F w j) = if v = w ∧ j = 2 then 1 else 0 := by
  change (placeDirection F w j v).2 = if v = w ∧ j = 2 then 1 else 0
  by_cases hv : v = w
  · subst v
    fin_cases j <;> simp [placeDirection]
  · fin_cases j <;> simp [placeDirection, hv]

private lemma greenHasFDerivAt_logHeight (v : InfinitePlace F) (p : Coord F) (hp : p ∈ posSet F) :
    HasFDerivAt (fun q => Real.log (greenCoordHeightCLM v q))
      (((p v).2)⁻¹ • greenCoordHeightCLM v) p := by
  have hpv : (p v).2 ≠ 0 := (hp v).ne'
  exact (greenCoordHeightCLM v).hasFDerivAt.log hpv

private lemma greenHasFDerivAt_logHeightComplex (v : InfinitePlace F) (p : Coord F) (hp : p ∈ posSet F) :
    HasFDerivAt (fun q => (Real.log ((q v).2) : ℂ))
      (Complex.ofRealCLM.comp (((p v).2)⁻¹ • greenCoordHeightCLM v)) p := by
  have h := greenHasFDerivAt_logHeight v p hp
  exact Complex.ofRealCLM.hasFDerivAt.comp p h

private lemma greenHasFDerivAt_sumLogHeight (p : Coord F) (hp : p ∈ posSet F) :
    HasFDerivAt (fun q => ∑ v : InfinitePlace F, (Real.log ((q v).2) : ℂ))
      (∑ v : InfinitePlace F, Complex.ofRealCLM.comp (((p v).2)⁻¹ • greenCoordHeightCLM v)) p := by
  have h := HasFDerivAt.sum (fun (v : InfinitePlace F) (_ : v ∈ Finset.univ) =>
    greenHasFDerivAt_logHeightComplex v p hp)
  have heq : (∑ v : InfinitePlace F, (fun q : Coord F => (Real.log ((q v).2) : ℂ))) =
      (fun q => ∑ v : InfinitePlace F, (Real.log ((q v).2) : ℂ)) := by
    funext q
    exact Finset.sum_apply q Finset.univ _
  exact heq ▸ h

private lemma greenNormHeight_ptX (q : Coord F) (hq : q ∈ posSet F) :
    normHeight F (ptX F q) = ∏ v, (q v).2 := by
  unfold normHeight
  apply Finset.prod_congr rfl
  intro v _
  exact height_pt (q v).1 (q v).2 (hq v)

private lemma greenLogNormHeight_ptX (q : Coord F) (hq : q ∈ posSet F) :
    logNormHeight F (ptX F q) = ∑ v : InfinitePlace F, (Real.log ((q v).2) : ℂ) := by
  unfold logNormHeight
  rw [greenNormHeight_ptX q hq]
  rw [Real.log_prod (fun v _ => (hq v).ne')]
  push_cast
  rfl

private lemma greenHasFDerivAt_logNormHeight (p : Coord F) (hp : p ∈ posSet F) :
    HasFDerivAt (logNormHeight F ∘ ptX F)
      (∑ v : InfinitePlace F, Complex.ofRealCLM.comp (((p v).2)⁻¹ • greenCoordHeightCLM v)) p := by
  have hsum := greenHasFDerivAt_sumLogHeight p hp
  have heq : (logNormHeight F ∘ ptX F) =ᶠ[𝓝 p]
      fun q => ∑ v : InfinitePlace F, (Real.log ((q v).2) : ℂ) := by
    filter_upwards [greenPosSet_isOpen.mem_nhds hp] with q hq
    exact greenLogNormHeight_ptX q hq
  exact hsum.congr_of_eventuallyEq heq

private lemma greenFDeriv_logNormHeight (p : Coord F) (hp : p ∈ posSet F) :
    fderiv ℝ (logNormHeight F ∘ ptX F) p =
      ∑ v : InfinitePlace F, Complex.ofRealCLM.comp (((p v).2)⁻¹ • greenCoordHeightCLM v) :=
  (greenHasFDerivAt_logNormHeight p hp).fderiv

private lemma greenFDeriv_logNormHeight_dir (w : InfinitePlace F) (p : Coord F)
    (hp : p ∈ posSet F) (j : Fin 3) :
    fderiv ℝ (logNormHeight F ∘ ptX F) p (placeDirection F w j) =
      if j = 2 then ((p w).2⁻¹ : ℂ) else 0 := by
  rw [greenFDeriv_logNormHeight p hp]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w]
  · rw [greenCoordHeightCLM_placeDirection]
    fin_cases j
    · simp
    · simp
    · simp
  · intro v _ hvw
    rw [greenCoordHeightCLM_placeDirection]
    have : ¬(v = w ∧ j = 2) := by intro h; exact hvw h.1
    simp [this]
  · simp

private lemma greenPlaceGradient_logNormHeight (w : InfinitePlace F) (z : X F) (j : Fin 3) :
    placeGradient F w (logNormHeight F) z j = if j = 2 then 1 else 0 := by
  unfold placeGradient
  set p := coordsX F z
  have hp : p ∈ posSet F := greenCoordsX_pos z
  rw [greenFDeriv_logNormHeight_dir w p hp j]
  fin_cases j
  · simp
  · simp
  · simp only [Fin.reduceFinMk, ↓reduceIte]
    have hpw : 0 < (p w).2 := hp w
    have hpw_ne : ((p w).2 : ℂ) ≠ 0 := by exact_mod_cast hpw.ne'
    push_cast
    exact mul_inv_cancel₀ hpw_ne

private lemma greenPlaceGradNormSq_logNormHeight (w : InfinitePlace F) (z : X F) :
    placeGradNormSq F w (logNormHeight F) z = 1 := by
  unfold placeGradNormSq
  simp_rw [greenPlaceGradient_logNormHeight w z]
  rw [Fin.sum_univ_three]
  simp

theorem greenTotalGradNormSq_logNormHeight (z : X F) :
    totalGradNormSq F (logNormHeight F) z = placeCount F := by
  unfold totalGradNormSq placeCount
  simp_rw [greenPlaceGradNormSq_logNormHeight]
  simp

end ArtinPrimitiveRoots.A1.Spec
