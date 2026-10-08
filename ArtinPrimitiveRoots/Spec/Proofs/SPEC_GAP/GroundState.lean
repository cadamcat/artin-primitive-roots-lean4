import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.CuspSums
import Mathlib.LinearAlgebra.Countable

/-! Smooth barriers and coordinate Laplacian calculations for `T7_ground_state`. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

open Classical

private theorem sgPosSetOpen : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem sgSecondCountableX : SecondCountableTopology (X F) := by
  have hcoord : SecondCountableTopology (Coord F) := inferInstance
  letI : SecondCountableTopology (Coord F) := hcoord
  letI : SecondCountableTopology {p : Coord F // p ∈ posSet F} := inferInstance
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, _, _⟩ := hchart
  exact e.symm.isEmbedding.secondCountableTopology

theorem sgOpensMeasurableX : OpensMeasurableSpace (X F) := by
  letI : SecondCountableTopology (X F) := sgSecondCountableX
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

private theorem sgContinuous_from_chart {β : Type*} [TopologicalSpace β]
    (f : X F → β) (hf : ContinuousOn (fun p : Coord F => f (ptX F p)) (posSet F)) :
    Continuous f := by
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hpt, _, _, _, hchart⟩
  obtain ⟨e, _, hesymm⟩ := hchart
  let fsub : {p : Coord F // p ∈ posSet F} → β := fun p => f (ptX F p.1)
  have hfsub : Continuous fsub :=
    hf.comp_continuous continuous_subtype_val (fun p => p.property)
  have hEq : fsub ∘ e.symm = f := by
    funext z
    change f (ptX F ((e.symm z).1)) = f z
    rw [hesymm z, hpt z]
  rw [← hEq]
  exact hfsub.comp e.symm.continuous

theorem sgSmoothX_continuous (f : X F → ℂ) (hf : IsSmoothX F f) :
    Continuous f :=
  sgContinuous_from_chart f hf.continuousOn

private theorem sgSmoothRealX_continuous (f : X F → ℝ) (hf : IsSmoothRealX F f) :
    Continuous f := by
  have hfC : IsSmoothX F (fun z => (f z : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun p => (f (ptX F p) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hcont := sgSmoothX_continuous (fun z => (f z : ℂ)) hfC
  have hEq : (fun z => Complex.re (f z : ℂ)) = f := by
    funext z
    simp
  rw [← hEq]
  exact Complex.continuous_re.comp hcont

private theorem sgCoords_ptX (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (ptX F p) = p := by
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
  exact hcoords p hp

private theorem sgPartialLap_chartFormula (f : X F → ℂ) (p : Coord F)
    (hp : p ∈ posSet F) (w : InfinitePlace F) :
    partialLap F w f (ptX F p) =
      ((p w).2 : ℂ) *
          fderiv ℝ (fun q => f (ptX F q)) p (placeDirection F w 2) -
        ((p w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 0, placeDirection F w 0] +
            iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 1, placeDirection F w 1] +
            iteratedFDeriv ℝ 2 (fun q => f (ptX F q)) p
              ![placeDirection F w 2, placeDirection F w 2]) := by
  have hcoords := sgCoords_ptX p hp
  dsimp [partialLap]
  simp only [Function.comp_def]
  rw [hcoords]
  simp only [placeDirection]

theorem sgPlaceGradient_continuous (f : X F → ℂ) (hf : IsSmoothX F f)
    (w : InfinitePlace F) (j : Fin 3) :
    Continuous (fun z => placeGradient F w f z j) := by
  let u : Coord F → ℂ := fun p => f (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hderiv : ContinuousOn (fderiv ℝ u) (posSet F) :=
    hu.continuousOn_fderiv_of_isOpen sgPosSetOpen (by norm_num)
  have hy : ContinuousOn (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
    have hr : ContinuousOn (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    exact Complex.continuous_ofReal.comp_continuousOn hr
  have hgrad : ContinuousOn (fun p => fderiv ℝ u p (placeDirection F w j))
      (posSet F) := by
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
    rw [sgCoords_ptX p hp]
    rfl
  exact sgContinuous_from_chart (fun z => placeGradient F w f z j)
    (hL.congr fun p hp => hEq hp)

theorem sgPartialLap_continuous (f : X F → ℂ) (hf : IsSmoothX F f)
    (w : InfinitePlace F) :
    Continuous (fun z => partialLap F w f z) := by
  let u : Coord F → ℂ := fun p => f (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := hf
  have hderiv : ContinuousOn (fderiv ℝ u) (posSet F) :=
    hu.continuousOn_fderiv_of_isOpen sgPosSetOpen (by norm_num)
  have hsecond : ContinuousOn (iteratedFDeriv ℝ 2 u) (posSet F) :=
    ContinuousOn.continuousOn_iteratedFDeriv hu sgPosSetOpen (by norm_num)
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
    exact (sgPartialLap_chartFormula f p hp w).trans (by simp [L, u])
  exact sgContinuous_from_chart (fun z => partialLap F w f z)
    (hL.congr fun p hp => hEq hp)

private def sgHessian (f : Coord F → ℝ) (p : Coord F) (v w : Coord F) : ℝ :=
  (fderiv ℝ (fun y => fderiv ℝ f y) p v) w

private theorem sgHessian_eq_iteratedFDeriv (f : Coord F → ℝ) (p v w : Coord F) :
    sgHessian f p v w = iteratedFDeriv ℝ 2 f p ![v, w] := by
  rw [sgHessian, iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rw [show Fin.init ![v, w] 0 = v from rfl]
  rw [show ![v, w] (Fin.last 1) = w from rfl]

private theorem sgHessian_mul {f g : Coord F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p v w : Coord F) :
    sgHessian (fun x => f x * g x) p v w =
      f p * sgHessian g p v w + g p * sgHessian f p v w +
        fderiv ℝ f p v * fderiv ℝ g p w + fderiv ℝ g p v * fderiv ℝ f p w := by
  have hf' (x : Coord F) := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : Coord F) := (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z * g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hf' p).smul (hgd p).hasFDerivAt).add
    ((hg' p).smul (hfd p).hasFDerivAt)
  unfold sgHessian
  change ((fderiv ℝ (fun y => fderiv ℝ (fun z => f z * g z) y) p) v) w = _
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) +
    g • fun y => fderiv ℝ f y) p) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  ring

private theorem sgHessian_scalar_comp {f : Coord F → ℝ} {g g' g'' : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (p v w : Coord F) :
    sgHessian (g ∘ f) p v w =
      g'' (f p) * fderiv ℝ f p v * fderiv ℝ f p w +
        g' (f p) * sgHessian f p v w := by
  have hf' (x : Coord F) := (hf.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (g ∘ f) y) =
      (fun y => g' (f y) • fderiv ℝ f y) := by
    funext y
    exact ((hg (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hg' (f p)).comp_hasFDerivAt p (hf' p)).smul
    (hfd p).hasFDerivAt
  unfold sgHessian
  change ((fderiv ℝ (fun y => fderiv ℝ (g ∘ f) y) p) v) w = _
  rw [hG]
  change ((fderiv ℝ ((g' ∘ f) • fun y => fderiv ℝ f y) p) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, smul_eq_mul]
  simp only [Function.comp_apply]
  ring

private def sgCoordHeight (p : Coord F) : ℝ := ∏ v : InfinitePlace F, (p v).2

private def sgCoordY (v : InfinitePlace F) (p : Coord F) : ℝ := (p v).2

private def sgCoordYCLM (v : InfinitePlace F) : Coord F →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    (ContinuousLinearMap.proj (R := ℝ) (ι := InfinitePlace F) v)

private theorem sgCoordY_smooth (v : InfinitePlace F) :
    ContDiff ℝ ∞ (sgCoordY (F := F) v) := by
  fun_prop [sgCoordY]

private theorem sgCoordY_deriv (v : InfinitePlace F) (p : Coord F)
    (w : InfinitePlace F) (j : Fin 3) :
    fderiv ℝ (sgCoordY (F := F) v) p (placeDirection F w j) =
      if v = w ∧ j = 2 then 1 else 0 := by
  have hlin : (sgCoordY (F := F) v) = sgCoordYCLM (F := F) v := by
    rfl
  rw [hlin]
  rw [(sgCoordYCLM (F := F) v).hasFDerivAt.fderiv]
  fin_cases j <;> by_cases hvw : v = w <;>
    simp [sgCoordYCLM, placeDirection, Pi.single, Function.update, hvw, eq_comm]

private theorem sgCoordY_hessian (v : InfinitePlace F) (p : Coord F)
    (w : InfinitePlace F) (j : Fin 3) :
    sgHessian (sgCoordY (F := F) v) p (placeDirection F w j)
      (placeDirection F w j) = 0 := by
  have hder (x : Coord F) : fderiv ℝ (sgCoordY (F := F) v) x =
      sgCoordYCLM (F := F) v := by
    exact (sgCoordYCLM (F := F) v).hasFDerivAt.fderiv
  unfold sgHessian
  change (fderiv ℝ (fun x => fderiv ℝ (sgCoordY (F := F) v) x) p)
    (placeDirection F w j) (placeDirection F w j) = 0
  rw [show (fun x => fderiv ℝ (sgCoordY (F := F) v) x) =
      fun _ => sgCoordYCLM (F := F) v from funext hder]
  simp

private def sgCoordHeightProd (s : Finset (InfinitePlace F)) (p : Coord F) : ℝ :=
  ∏ v ∈ s, sgCoordY (F := F) v p

private theorem sgCoordHeightProd_smooth (s : Finset (InfinitePlace F)) :
    ContDiff ℝ ∞ (sgCoordHeightProd (F := F) s) := by
  unfold sgCoordHeightProd
  exact contDiff_prod (fun v hv => sgCoordY_smooth v)

private theorem sgCoordHeightProd_fderiv
    (s : Finset (InfinitePlace F)) (w : InfinitePlace F) (j : Fin 3)
    (p : Coord F) :
    fderiv ℝ (sgCoordHeightProd (F := F) s) p (placeDirection F w j) =
      if j = 2 ∧ w ∈ s then
        ∏ v ∈ s.erase w, sgCoordY (F := F) v p else 0 := by
  classical
  have hformula : fderiv ℝ (sgCoordHeightProd (F := F) s) p =
      ∑ v ∈ s, (∏ q ∈ s.erase v, sgCoordY (F := F) q p) •
        fderiv ℝ (sgCoordY (F := F) v) p := by
    unfold sgCoordHeightProd
    exact fderiv_finsetProd (fun v hv =>
      (sgCoordY_smooth (F := F) v).differentiable (by simp) p)
  rw [hformula]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [sgCoordY_deriv]
  by_cases hj : j = 2 <;> by_cases hw : w ∈ s <;> simp [hj, hw]

private theorem sgCoordHeightProd_hessian
    (s : Finset (InfinitePlace F)) (w : InfinitePlace F) (j : Fin 3)
    (p : Coord F) :
    sgHessian (sgCoordHeightProd (F := F) s) p
      (placeDirection F w j) (placeDirection F w j) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (fderiv ℝ (fun y => fderiv ℝ (fun _ : Coord F => (1 : ℝ)) y) p
        (placeDirection F w j)) (placeDirection F w j) = 0
      simp [sgHessian]
  | @insert i s his ih =>
      have hprod : sgCoordHeightProd (F := F) (insert i s) = fun p =>
          sgCoordY (F := F) i p * sgCoordHeightProd (F := F) s p := by
        funext p
        simp [sgCoordHeightProd, his]
      rw [hprod, sgHessian_mul (sgCoordY_smooth (F := F) i)
        (sgCoordHeightProd_smooth (F := F) s)]
      rw [ih, sgCoordY_hessian]
      rw [sgCoordHeightProd_fderiv]
      rw [sgCoordY_deriv]
      by_cases hiw : i = w
      · have hws : w ∉ s := by simpa [hiw] using his
        simp [hiw, hws]
      · simp [hiw]

private theorem sgFDeriv_ofReal {u : Coord F → ℝ} (p v : Coord F)
    (hu : DifferentiableAt ℝ u p) :
    fderiv ℝ (fun q => (u q : ℂ)) p v =
      (fderiv ℝ u p v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp p hu.hasFDerivAt
  change (fderiv ℝ (Complex.ofRealCLM ∘ u) p) v = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private theorem sgIteratedFDeriv_ofReal {u : Coord F → ℝ} (p v w : Coord F)
    (hu : ContDiff ℝ ∞ u) :
    iteratedFDeriv ℝ 2 (fun q => (u q : ℂ)) p ![v, w] =
      (iteratedFDeriv ℝ 2 u p ![v, w] : ℂ) := by
  have h := (Complex.ofRealCLM).iteratedFDeriv_comp_left
    (f := u) (x := p) hu.contDiffAt (by norm_num : 2 ≤ (∞ : ℕ∞ω))
  have happ := congrArg (fun D => D ![v, w]) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at happ
  have hfun : (fun q => (u q : ℂ)) = Complex.ofRealCLM ∘ u := rfl
  rw [hfun]
  exact happ

private theorem sgFDeriv_realCompAt {u : Coord F → ℝ} {ψ ψ' : ℝ → ℝ}
    (p v : Coord F) (hu : DifferentiableAt ℝ u p)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) :
    fderiv ℝ (ψ ∘ u) p v = ψ' (u p) * fderiv ℝ u p v := by
  have hcomp := (hψ (u p)).hasFDerivAt.comp p hu.hasFDerivAt
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

private theorem sgNormHeight_ptX (p : Coord F) (hp : p ∈ posSet F) :
    normHeight F (ptX F p) = sgCoordHeight (F := F) p := by
  unfold normHeight sgCoordHeight ptX
  simp only [height]
  congr 1
  funext w
  exact (G1_h3_basics (F := F)).1 (p w).1 (p w).2 (hp w)

private theorem sgPartialLap_realChart (u : Coord F → ℝ) (hu : ContDiff ℝ ∞ u)
    (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) :
    partialLap F w (fun z => (u (coordsX F z) : ℂ)) (ptX F p) =
      ((p w).2 : ℂ) * (fderiv ℝ u p (placeDirection F w 2) : ℂ) -
        ((p w).2 : ℂ) ^ 2 *
          ((sgHessian u p (placeDirection F w 0) (placeDirection F w 0) : ℂ) +
            (sgHessian u p (placeDirection F w 1) (placeDirection F w 1) : ℂ) +
            (sgHessian u p (placeDirection F w 2) (placeDirection F w 2) : ℂ)) := by
  have hcoords : coordsX F (ptX F p) = p := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
    exact hcoords p hp
  have hEq : (fun q : Coord F =>
      ((u (coordsX F (ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p]
      (fun q => (u q : ℂ)) := by
    filter_upwards [sgPosSetOpen.mem_nhds hp] with q hq
    rw [sgCoords_ptX q hq]
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  dsimp [partialLap]
  simp only [Function.comp_def]
  rw [hcoords]
  simp only [placeDirection]
  rw [h1]
  rw [sgFDeriv_ofReal _ _ ((hu.differentiable (by simp) p))]
  rw [h2]
  rw [sgIteratedFDeriv_ofReal p (Pi.single w (1, 0)) (Pi.single w (1, 0)) hu,
    sgIteratedFDeriv_ofReal p (Pi.single w (Complex.I, 0)) (Pi.single w (Complex.I, 0)) hu,
    sgIteratedFDeriv_ofReal p (Pi.single w (0, 1)) (Pi.single w (0, 1)) hu]
  simp only [sgHessian_eq_iteratedFDeriv]

private theorem sgPartialLap_comp_normHeight_base (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (p : Coord F) (hp : p ∈ posSet F)
    (w : InfinitePlace F) :
    partialLap F w (fun z => (ψ (normHeight F z) : ℂ)) (ptX F p) =
      ((sgCoordHeight p * deriv ψ (sgCoordHeight p) -
        sgCoordHeight p ^ 2 * deriv (deriv ψ) (sgCoordHeight p) : ℝ) : ℂ) := by
  let H : Coord F → ℝ := sgCoordHeight
  let u : Coord F → ℝ := ψ ∘ H
  have hH : H = sgCoordHeightProd (F := F) Finset.univ := by
    funext q
    simp [H, sgCoordHeight, sgCoordHeightProd, sgCoordY]
  have hHs : ContDiff ℝ ∞ H := by
    rw [hH]
    exact sgCoordHeightProd_smooth Finset.univ
  have hu : ContDiff ℝ ∞ u := hψ.comp hHs
  have hchart : (fun q : Coord F =>
      ((ψ (normHeight F (ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p]
      (fun q => (u q : ℂ)) := by
    filter_upwards [sgPosSetOpen.mem_nhds hp] with q hq
    rw [sgNormHeight_ptX q hq]
    rfl
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hchart
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hchart 2).self_of_nhds
  have hψder : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hψHas (t : ℝ) : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable (by simp) t).hasDerivAt
  have hψderHas (t : ℝ) : HasDerivAt (deriv ψ) (deriv (deriv ψ) t) t :=
    (hψder.differentiable (by simp) t).hasDerivAt
  have hHgrad (j : Fin 3) :
      fderiv ℝ H p (placeDirection F w j) =
        if j = 2 then ∏ v ∈ Finset.univ.erase w, sgCoordY (F := F) v p else 0 := by
    rw [hH]
    rw [sgCoordHeightProd_fderiv]
    by_cases hj : j = 2 <;> simp [hj]
  have hHhess (j : Fin 3) :
      sgHessian H p (placeDirection F w j) (placeDirection F w j) = 0 := by
    rw [hH]
    exact sgCoordHeightProd_hessian Finset.univ w j p
  have hHderivErase :
      (p w).2 * (∏ v ∈ Finset.univ.erase w, sgCoordY (F := F) v p) = H p := by
    rw [hH]
    change (p w).2 * (∏ v ∈ Finset.univ.erase w, sgCoordY (F := F) v p) =
      ∏ v ∈ Finset.univ, sgCoordY (F := F) v p
    exact Finset.mul_prod_erase Finset.univ (fun v => sgCoordY (F := F) v p)
      (Finset.mem_univ w)
  have hUgrad (j : Fin 3) :
      fderiv ℝ u p (placeDirection F w j) =
        deriv ψ (H p) * fderiv ℝ H p (placeDirection F w j) := by
    exact sgFDeriv_realCompAt p (placeDirection F w j)
      (hHs.differentiable (by simp) p) hψHas
  have hUhess (j : Fin 3) :
      sgHessian u p (placeDirection F w j) (placeDirection F w j) =
        deriv (deriv ψ) (H p) *
          fderiv ℝ H p (placeDirection F w j) *
          fderiv ℝ H p (placeDirection F w j) +
        deriv ψ (H p) * sgHessian H p (placeDirection F w j) (placeDirection F w j) := by
    exact sgHessian_scalar_comp hHs hψHas hψderHas p _ _
  have hreal : partialLap F w (fun z => (u (coordsX F z) : ℂ)) (ptX F p) =
      ((H p * deriv ψ (H p) - H p ^ 2 * deriv (deriv ψ) (H p) : ℝ) : ℂ) := by
    rw [sgPartialLap_realChart u hu p hp w]
    rw [hUgrad 2]
    rw [hUhess 0, hUhess 1, hUhess 2]
    simp_rw [hHhess, hHgrad]
    push_cast
    have hprodC :
        (↑(p w).2 : ℂ) * (∏ i ∈ Finset.univ.erase w, (sgCoordY (F := F) i p : ℂ)) =
          (H p : ℂ) := by
      exact_mod_cast hHderivErase
    have hfirst :
        (↑(p w).2 : ℂ) *
            (((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (sgCoordY (F := F) i p : ℂ)) =
          (H p : ℂ) * ((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (sgCoordY (F := F) i p : ℂ)) := by ring
        _ = _ := by rw [hprodC]; ring
    have hsecond :
        (↑(p w).2 : ℂ) ^ 2 *
            (((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) *
              (∏ i ∈ Finset.univ.erase w, (sgCoordY (F := F) i p : ℂ)) ^ 2) =
          (H p : ℂ) ^ 2 * ((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (sgCoordY (F := F) i p : ℂ)) ^ 2 := by ring
        _ = _ := by rw [hprodC]; ring
    ring_nf
    linear_combination hfirst - hsecond
  have hfun : (fun z => (ψ (normHeight F z) : ℂ)) =
      (fun z => (u (coordsX F z) : ℂ)) := by
    funext z
    rfl
  rw [hfun]
  simpa [H, u] using hreal

noncomputable def specGapGroundWeight (A : ℝ) (t : ℝ) : ℝ :=
  t * specGapHeightCutoff A t

theorem specGapGroundWeight_smooth {A : ℝ} (hA : 0 < A) :
    ContDiff ℝ ∞ (specGapGroundWeight A) := by
  exact contDiff_id.mul (specGapHeightCutoff_isCuspCutoff hA).1

theorem specGapGroundWeight_zero_of_le {A t : ℝ} (hA : 0 < A) (ht : t ≤ A) :
    specGapGroundWeight A t = 0 := by
  simp [specGapGroundWeight, (specGapHeightCutoff_isCuspCutoff hA).2.2.1 t ht]

theorem specGapGroundWeight_eq_of_ge {A t : ℝ} (hA : 0 < A) (ht : 2 * A ≤ t) :
    specGapGroundWeight A t = t := by
  simp [specGapGroundWeight, (specGapHeightCutoff_isCuspCutoff hA).2.2.2 t ht]

theorem specGapGroundWeight_deriv_eq_one_of_gt {A t : ℝ} (hA : 0 < A)
    (ht : 2 * A < t) : deriv (specGapGroundWeight A) t = 1 := by
  have hEq : (fun x : ℝ => x) =ᶠ[𝓝 t] specGapGroundWeight A := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (specGapGroundWeight_eq_of_ge hA (le_of_lt hx)).symm
  have h := hEq.deriv_eq
  simpa using h.symm

theorem specGapGroundWeight_second_deriv_eq_zero_of_gt {A t : ℝ} (hA : 0 < A)
    (ht : 2 * A < t) : deriv (deriv (specGapGroundWeight A)) t = 0 := by
  have hEq : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 t] deriv (specGapGroundWeight A) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (specGapGroundWeight_deriv_eq_one_of_gt hA hx).symm
  have h := hEq.deriv_eq
  simpa using h.symm

noncomputable def specGapGroundPhi {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (z : X F) : ℝ :=
  1 + specGapAllCuspSum Γ d (specGapGroundWeight A) z

theorem specGapGroundPhi_smooth {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) :
    IsSmoothRealX F (specGapGroundPhi d A) := by
  have hzero : ∀ t ≤ A, specGapGroundWeight A t = 0 :=
    fun t ht => specGapGroundWeight_zero_of_le hA ht
  have hsum := specGapAllCuspSum_smooth d (specGapGroundWeight A)
    (specGapGroundWeight_smooth hA) A hA hzero
  change ContDiffOn ℝ ∞
    (fun p => 1 + specGapAllCuspSum Γ d (specGapGroundWeight A) (ptX F p)) (posSet F)
  exact contDiffOn_const.add hsum

theorem specGapGroundPhi_invariant {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (γ : Γ) (z : X F) :
    specGapGroundPhi d A ((γ : SL(2,𝓞 F)) • z) = specGapGroundPhi d A z := by
  simp [specGapGroundPhi, specGapAllCuspSum_invariant]

theorem specGapGroundPhi_ge_one {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A₀ A : ℝ) (hA₀ : 0 < A₀) (hA₀A : A₀ ≤ A)
    (hsep₀ : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A₀ ≤ specGapAllCuspHeight Γ d p z → A₀ ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (hA : 0 < A) (z : X F) : 1 ≤ specGapGroundPhi d A z := by
  have hsepA : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p' := by
    intro p p' x hp hp'
    exact hsep₀ p p' x (le_trans hA₀A hp) (le_trans hA₀A hp')
  have hzero : ∀ t ≤ A, specGapGroundWeight A t = 0 :=
    fun t ht => specGapGroundWeight_zero_of_le hA ht
  rcases specGapAllCuspSum_eq_zero_or_term d (specGapGroundWeight A)
      A hA hzero hsepA z with hnone | ⟨p, hp⟩
  · have hsum : specGapAllCuspSum Γ d (specGapGroundWeight A) z = 0 := by
      unfold specGapAllCuspSum
      calc
        _ = ∑' p, (0 : ℝ) := tsum_congr hnone
        _ = 0 := by simp
    simp [specGapGroundPhi, hsum]
  · have hheight : 0 < specGapAllCuspHeight Γ d p z := by
      rcases p with ⟨i, q⟩
      exact specGapCosetHeight_pos Γ (d.σ i) q z
    rw [specGapGroundPhi, hp]
    have hcut := specGapHeightCutoff_bounds (A := A) (specGapAllCuspHeight Γ d p z)
    have hweight : 0 ≤ specGapGroundWeight A (specGapAllCuspHeight Γ d p z) :=
      mul_nonneg hheight.le hcut.1
    linarith

theorem specGapGroundSum_eq_term_of_ne_zero {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (A₀ A : ℝ)
    (hA₀A : A₀ ≤ A) (hψzero : ∀ t ≤ A, ψ t = 0)
    (hsep₀ : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A₀ ≤ specGapAllCuspHeight Γ d p z → A₀ ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (p : SpecGapCuspIndex Γ d) (z : X F)
    (hp : ψ (specGapAllCuspHeight Γ d p z) ≠ 0) :
    specGapAllCuspSum Γ d ψ z = ψ (specGapAllCuspHeight Γ d p z) := by
  have hpgt : A < specGapAllCuspHeight Γ d p z := by
    by_contra hnot
    exact hp (hψzero _ (le_of_not_gt hnot))
  have hsep : ∀ p' p'' : SpecGapCuspIndex Γ d, ∀ x : X F,
      A ≤ specGapAllCuspHeight Γ d p' x → A ≤ specGapAllCuspHeight Γ d p'' x → p' = p'' := by
    intro p' p'' x hp' hp''
    exact hsep₀ p' p'' x (le_trans hA₀A hp') (le_trans hA₀A hp'')
  unfold specGapAllCuspSum
  rw [tsum_eq_single p]
  intro p' hne
  by_contra hp'nonzero
  have hp'gt : A < specGapAllCuspHeight Γ d p' z := by
    by_contra hnot
    exact hp'nonzero (hψzero _ (le_of_not_gt hnot))
  exact hne (hsep p p' z hpgt.le hp'gt.le).symm

theorem specGapGroundPhi_smooth_complex {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) :
    IsSmoothX F (fun z => (specGapGroundPhi d A z : ℂ)) := by
  change ContDiffOn ℝ ∞
    (fun p => ((specGapGroundPhi d A (ptX F p) : ℝ) : ℂ)) (posSet F)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (specGapGroundPhi_smooth d A hA)

private theorem sgNormHeight_smooth : IsSmoothRealX F (normHeight F) := by
  change ContDiffOn ℝ ∞ (fun p => normHeight F (ptX F p)) (posSet F)
  have hprod : ContDiff ℝ ∞ (sgCoordHeight (F := F)) := by
    have hEq : sgCoordHeight (F := F) = sgCoordHeightProd (F := F) Finset.univ := by
      funext p
      simp [sgCoordHeight, sgCoordHeightProd, sgCoordY]
    rw [hEq]
    exact sgCoordHeightProd_smooth Finset.univ
  apply hprod.contDiffOn.congr
  intro p hp
  exact sgNormHeight_ptX p hp

private theorem sgNormHeight_comp_smooth (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    IsSmoothX F (fun z => (ψ (normHeight F z) : ℂ)) := by
  change ContDiffOn ℝ ∞
    (fun p => (ψ (normHeight F (ptX F p)) : ℂ)) (posSet F)
  have hreal : ContDiffOn ℝ ∞ (fun p => ψ (normHeight F (ptX F p))) (posSet F) :=
    hψ.comp_contDiffOn sgNormHeight_smooth
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hreal

private theorem sgPartialLap_comp_normHeight_at (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (z : X F) (w : InfinitePlace F) :
    partialLap F w (fun x => (ψ (normHeight F x) : ℂ)) z =
      ((normHeight F z * deriv ψ (normHeight F z) -
        normHeight F z ^ 2 * deriv (deriv ψ) (normHeight F z) : ℝ) : ℂ) := by
  let p := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  have hN : sgCoordHeight (F := F) p = normHeight F z := by
    rw [← hpt]
    exact (sgNormHeight_ptX p hp).symm
  rw [← hpt]
  rw [sgPartialLap_comp_normHeight_base ψ hψ p hp w]
  simp [hN, hpt]

private theorem sgPartialLap_comp_normHeight_action (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (g : SL(2,F)) (z : X F) (w : InfinitePlace F) :
    partialLap F w (fun x => (ψ (normHeight F (g • x)) : ℂ)) z =
      ((normHeight F (g • z) * deriv ψ (normHeight F (g • z)) -
        normHeight F (g • z) ^ 2 * deriv (deriv ψ) (normHeight F (g • z)) : ℝ) : ℂ) := by
  let zero : X F → ℂ := fun _ => 0
  have hzsm : IsSmoothX F zero := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  have hzcompact : HasCompactSupportX F zero := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp [zero]
  have h0 := G5_green_x zero zero hzsm hzsm hzcompact
  let F₀ : X F → ℂ := fun x => (ψ (normHeight F x) : ℂ)
  have hF₀ : IsSmoothX F F₀ := sgNormHeight_comp_smooth ψ hψ
  let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F g
  have hcomm := h0.2.2 gPlaces F₀ hF₀ w z
  calc
    partialLap F w (fun x => (ψ (normHeight F (g • x)) : ℂ)) z =
        partialLap F w (fun x => F₀ (actAtPlaces F gPlaces x)) z := by
          rfl
    _ = partialLap F w F₀ (actAtPlaces F gPlaces z) := hcomm
    _ = _ := by
      rw [show actAtPlaces F gPlaces z = g • z from rfl]
      exact sgPartialLap_comp_normHeight_at ψ hψ (g • z) w

private theorem sgPartialLap_congr_chart (f g : X F → ℂ) (z : X F)
    (hEq : (fun p => f (ptX F p)) =ᶠ[𝓝 (coordsX F z)]
      (fun p => g (ptX F p))) (w : InfinitePlace F) :
    partialLap F w f z = partialLap F w g z := by
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  unfold partialLap
  simp only [Function.comp_def, h1, h2]

theorem specGapGroundPhi_lap_high {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A₀ A : ℝ) (hA₀ : 0 < A₀) (hA₀A : A₀ ≤ A)
    (hsep₀ : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A₀ ≤ specGapAllCuspHeight Γ d p z → A₀ ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (hA : 0 < A) (p : SpecGapCuspIndex Γ d) (z : X F)
    (hz : 2 * A < specGapAllCuspHeight Γ d p z) :
    totalLap F (fun x => (specGapGroundPhi d A x : ℂ)) z =
      (placeCount F : ℂ) * (specGapAllCuspHeight Γ d p z : ℂ) := by
  let c : X F → ℝ := specGapAllCuspHeight Γ d p
  let φc : X F → ℂ := fun x => (specGapGroundPhi d A x : ℂ)
  have hcSmooth : IsSmoothRealX F c := by
    rcases p with ⟨i, q⟩
    exact specGapCosetHeight_smooth Γ (d.σ i) q
  let x₀ := coordsX F z
  have hx₀ : x₀ ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F x₀ = z := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  have hcAt : ContinuousAt (fun x => c (ptX F x)) x₀ :=
    (hcSmooth.contDiffAt (sgPosSetOpen.mem_nhds hx₀)).continuousAt
  have hhigh0 : 2 * A < c (ptX F x₀) := by
    rw [hpt]
    exact hz
  have hhigh : ∀ᶠ x in 𝓝 x₀, 2 * A < c (ptX F x) :=
    hcAt.eventually (isOpen_Ioi.mem_nhds hhigh0)
  have hweightZero : ∀ t ≤ A, specGapGroundWeight A t = 0 :=
    fun t ht => specGapGroundWeight_zero_of_le hA ht
  have hEq : (fun x => φc (ptX F x)) =ᶠ[𝓝 x₀]
      (fun x => ((1 + c (ptX F x) : ℝ) : ℂ)) := by
    filter_upwards [hhigh] with x hx
    have hpositive : 0 < c (ptX F x) := by linarith [hA]
    have hnonzero : specGapGroundWeight A (c (ptX F x)) ≠ 0 := by
      rw [specGapGroundWeight_eq_of_ge hA (le_of_lt hx)]
      exact ne_of_gt hpositive
    have hsum := specGapGroundSum_eq_term_of_ne_zero d (specGapGroundWeight A)
      A₀ A hA₀A hweightZero hsep₀ p (ptX F x) hnonzero
    have hcut := specGapGroundWeight_eq_of_ge hA (le_of_lt hx)
    simp [φc, specGapGroundPhi, c, hsum, hcut]
  have hpartial (w : InfinitePlace F) :
      partialLap F w φc z =
        (specGapAllCuspHeight Γ d p z : ℂ) := by
    have hlocal := sgPartialLap_congr_chart φc
      (fun x => ((1 + c x : ℝ) : ℂ)) z hEq w
    have hpsi : ContDiff ℝ ∞ (fun t : ℝ => 1 + t) := by fun_prop
    let g : SL(2,F) := by
      rcases p with ⟨i, q⟩
      exact (d.σ i)⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
    have hheight (x : X F) : c x = normHeight F (g • x) := by
      rcases p with ⟨i, q⟩
      change normHeight F ((d.σ i)⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x)) = _
      change normHeight F ((d.σ i)⁻¹ •
        (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • x)) = _
      rw [smul_smul]
    have hlap := sgPartialLap_comp_normHeight_action (fun t : ℝ => 1 + t) hpsi g z w
    have hRewrite : (fun x => ((1 + c x : ℝ) : ℂ)) =
        (fun x => ((1 + normHeight F (g • x) : ℝ) : ℂ)) := by
      funext x
      rw [hheight]
    calc
      partialLap F w φc z = partialLap F w (fun x => ((1 + c x : ℝ) : ℂ)) z := hlocal
      _ = partialLap F w (fun x => ((1 + normHeight F (g • x) : ℝ) : ℂ)) z := by
        rw [hRewrite]
      _ = (normHeight F (g • z) : ℂ) := by simpa using hlap
      _ = (specGapAllCuspHeight Γ d p z : ℂ) := by
        change (normHeight F (g • z) : ℂ) = (c z : ℂ)
        exact congrArg Complex.ofReal (hheight z).symm
  calc
    totalLap F φc z = ∑ w : InfinitePlace F, (specGapAllCuspHeight Γ d p z : ℂ) := by
      unfold totalLap
      exact Finset.sum_congr rfl (fun w hw => hpartial w)
    _ = (placeCount F : ℂ) * (specGapAllCuspHeight Γ d p z : ℂ) := by
      simp [placeCount, Finset.sum_const, nsmul_eq_mul]

def sgGroundLaplacianRatio (φ : X F → ℝ) (z : X F) : ℝ :=
  (totalLap F (fun x => (φ x : ℂ)) z).re / φ z

theorem specGapGroundPhi_ratio_high {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A₀ A : ℝ) (hA₀ : 0 < A₀) (hA₀A : A₀ ≤ A)
    (hsep₀ : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A₀ ≤ specGapAllCuspHeight Γ d p z → A₀ ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (hA : 0 < A) (p : SpecGapCuspIndex Γ d) (z : X F)
    (hz : 2 * A < specGapAllCuspHeight Γ d p z) :
    placeCount F * (1 - 1 / (2 * A)) ≤
      sgGroundLaplacianRatio (specGapGroundPhi d A) z := by
  let h := specGapAllCuspHeight Γ d p z
  have hhpos : 0 < h := by linarith [hA]
  have hweight : specGapGroundWeight A h ≠ 0 := by
    rw [specGapGroundWeight_eq_of_ge hA (le_of_lt hz)]
    exact ne_of_gt hhpos
  have hsum := specGapGroundSum_eq_term_of_ne_zero d (specGapGroundWeight A)
    A₀ A hA₀A (fun t ht => specGapGroundWeight_zero_of_le hA ht) hsep₀ p z hweight
  have hφ : specGapGroundPhi d A z = 1 + h := by
    unfold specGapGroundPhi
    rw [hsum, specGapGroundWeight_eq_of_ge hA (le_of_lt hz)]
  have hLap := specGapGroundPhi_lap_high d A₀ A hA₀ hA₀A hsep₀ hA p z hz
  have hratio : sgGroundLaplacianRatio (specGapGroundPhi d A) z =
      placeCount F * (h / (1 + h)) := by
    simp [sgGroundLaplacianRatio, hLap, hφ, h, Complex.ofReal_mul,
      Complex.ofReal_re, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hden : 0 < 1 + h := by linarith
  have hscale : 0 < 2 * A := by positivity
  have hdenbound : 2 * A ≤ 1 + h := by linarith
  have hrecip : 1 / (1 + h) ≤ 1 / (2 * A) :=
    one_div_le_one_div_of_le hscale hdenbound
  have hfrac : 1 - 1 / (2 * A) ≤ h / (1 + h) := by
    calc
      1 - 1 / (2 * A) ≤ 1 - 1 / (1 + h) := sub_le_sub_left hrecip 1
      _ = h / (1 + h) := by field_simp [ne_of_gt hden]; ring
  rw [hratio]
  have hr : 0 ≤ placeCount F := by
    unfold placeCount
    exact_mod_cast (Nat.zero_le (Fintype.card (InfinitePlace F)))
  exact mul_le_mul_of_nonneg_left hfrac hr

private theorem sgGroundLaplacianRatio_continuous (φ : X F → ℝ)
    (hφ : IsSmoothRealX F φ) (hφpos : ∀ z, 1 ≤ φ z) :
    Continuous (sgGroundLaplacianRatio φ) := by
  classical
  let f : X F → ℂ := fun z => (φ z : ℂ)
  let u : Coord F → ℂ := fun p => f (ptX F p)
  have hu : ContDiffOn ℝ ∞ u (posSet F) := by
    change ContDiffOn ℝ ∞ (fun p => ((φ (ptX F p) : ℝ) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hderiv : ContinuousOn (fderiv ℝ u) (posSet F) :=
    hu.continuousOn_fderiv_of_isOpen sgPosSetOpen (by norm_num)
  have hsecond : ContinuousOn (iteratedFDeriv ℝ 2 u) (posSet F) :=
    ContinuousOn.continuousOn_iteratedFDeriv hu sgPosSetOpen (by norm_num)
  have hgrad (w : InfinitePlace F) (j : Fin 3) :
      ContinuousOn (fun p => fderiv ℝ u p (placeDirection F w j)) (posSet F) := by
    have heval : Continuous (fun L : Coord F →L[ℝ] ℂ => L (placeDirection F w j)) := by
      fun_prop
    exact heval.comp_continuousOn hderiv
  have hhess (w : InfinitePlace F) (j : Fin 3) :
      ContinuousOn (fun p =>
        iteratedFDeriv ℝ 2 u p ![placeDirection F w j, placeDirection F w j])
        (posSet F) := by
    have heval : Continuous
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Coord F) ℂ =>
          L ![placeDirection F w j, placeDirection F w j]) := by
      fun_prop
    exact heval.comp_continuousOn hsecond
  have hcoord (w : InfinitePlace F) :
      ContinuousOn (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
    have hr : ContinuousOn (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    exact Complex.ofRealCLM.continuous.comp_continuousOn hr
  have hpart (w : InfinitePlace F) :
      ContinuousOn (fun p => partialLap F w f (ptX F p)) (posSet F) := by
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
        exact ((hhess w 0).add (hhess w 1)).add (hhess w 2)
      exact (hcoord w).mul (hgrad w 2) |>.sub ((hcoord w).pow 2 |>.mul hsum)
    have hEq : Set.EqOn (fun p => partialLap F w f (ptX F p)) L (posSet F) := by
      intro p hp
      exact (sgPartialLap_chartFormula f p hp w).trans (by simp [L, u])
    exact hL.congr hEq
  have htotal : ContinuousOn (fun p => totalLap F f (ptX F p)) (posSet F) := by
    have hEq : (fun p => totalLap F f (ptX F p)) =
        fun p => ∑ w : InfinitePlace F, partialLap F w f (ptX F p) := by
      funext p
      rfl
    rw [hEq]
    exact continuousOn_finsetSum Finset.univ (fun w hw => hpart w)
  have hnum : ContinuousOn (fun p => (totalLap F f (ptX F p)).re) (posSet F) :=
    Complex.reCLM.continuous.comp_continuousOn htotal
  have hden : ContinuousOn (fun p => φ (ptX F p)) (posSet F) := by
    change ContDiffOn ℝ ∞ (fun p => φ (ptX F p)) (posSet F) at hφ
    intro p hp
    exact (hφ p hp).continuousWithinAt
  have hratio : ContinuousOn
      (fun p => (totalLap F f (ptX F p)).re / φ (ptX F p)) (posSet F) := by
    apply ContinuousOn.div hnum hden
    intro p hp
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hφpos (ptX F p)))
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, he, hesymm⟩ := hchart
  let qsub : {p : Coord F // p ∈ posSet F} → ℝ := fun p =>
    (totalLap F f (ptX F p.1)).re / φ (ptX F p.1)
  have hqsub : Continuous qsub := by
    exact hratio.comp_continuous continuous_subtype_val (fun p => p.property)
  let qglob : X F → ℝ := qsub ∘ e.symm
  have hqglob : Continuous qglob := hqsub.comp e.symm.continuous
  have hEq : qglob = sgGroundLaplacianRatio φ := by
    funext z
    have hzcoords := hesymm z
    have hpt : ptX F (coordsX F z) = z := by
      rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
      exact hpt z
    simp [qglob, qsub, sgGroundLaplacianRatio, hzcoords, hpt, f]
  rw [← hEq]
  exact hqglob

theorem sgGroundPhi_compact_ratio_bound {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A₀ A : ℝ) (hA₀ : 0 < A₀) (hA₀A : A₀ ≤ A)
    (hsep₀ : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A₀ ≤ specGapAllCuspHeight Γ d p z → A₀ ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (hA : 0 < A) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ z ∈ (⋃ i, SiegelData.compactBox F d i (2 * A)),
      -C₀ ≤ sgGroundLaplacianRatio (specGapGroundPhi d A) z := by
  classical
  letI : Fintype d.ι := d.fintype
  let K : Set (X F) := ⋃ i, SiegelData.compactBox F d i (2 * A)
  have hbox (i : d.ι) : IsCompact (SiegelData.compactBox F d i (2 * A)) :=
    (R13_compact_part Γ d).1 (2 * A) (by positivity) i
  have hK : IsCompact K := by
    simpa [K] using isCompact_iUnion hbox
  have hphi : IsSmoothRealX F (specGapGroundPhi d A) :=
    specGapGroundPhi_smooth d A hA
  have hphiPos (z : X F) : 1 ≤ specGapGroundPhi d A z :=
    specGapGroundPhi_ge_one d A₀ A hA₀ hA₀A hsep₀ hA z
  have hr : Continuous (sgGroundLaplacianRatio (specGapGroundPhi d A)) :=
    sgGroundLaplacianRatio_continuous (specGapGroundPhi d A) hphi hphiPos
  let r : X F → ℝ := sgGroundLaplacianRatio (specGapGroundPhi d A)
  have hbelow : BddBelow (r '' K) :=
    hK.bddBelow_image (hr.continuousOn.mono (Set.subset_univ K))
  rcases hbelow with ⟨b, hb⟩
  let C₀ := max 0 (-b)
  refine ⟨C₀, le_max_left _ _, ?_⟩
  intro z hz
  have hbz : b ≤ r z := hb ⟨z, hz, rfl⟩
  have hlow : -C₀ ≤ b := by
    calc
      -C₀ ≤ -(-b) := by
        apply neg_le_neg
        exact le_max_right 0 (-b)
      _ = b := by ring
  exact le_trans hlow hbz

theorem sgGroundLaplacianRatio_invariant {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A)
    (γ : Γ) (z : X F) :
    sgGroundLaplacianRatio (specGapGroundPhi d A) ((γ : SL(2,𝓞 F)) • z) =
      sgGroundLaplacianRatio (specGapGroundPhi d A) z := by
  let f : X F → ℂ := fun x => (specGapGroundPhi d A x : ℂ)
  have hInv : IsGammaInvariant F Γ f := by
    intro δ hδ x
    exact congrArg Complex.ofReal (specGapGroundPhi_invariant d A ⟨δ, hδ⟩ x)
  have hf : IsSmoothX F f := specGapGroundPhi_smooth_complex d A hA
  let zero : X F → ℂ := fun _ => 0
  have hzsm : IsSmoothX F zero := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  have hzcompact : HasCompactSupportX F zero := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp [zero]
  have hG5 := G5_green_x zero zero hzsm hzsm hzcompact
  let g : SL(2,F) := toSLF F ((γ : Γ) : SL(2,𝓞 F))
  let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F g
  have hact (x : X F) : actAtPlaces F gPlaces x =
      ((γ : SL(2,𝓞 F)) • x) := by rfl
  have hpart (w : InfinitePlace F) :
      partialLap F w f ((γ : SL(2,𝓞 F)) • z) = partialLap F w f z := by
    have hcomm := hG5.2.2 gPlaces f hf w z
    have hcomp : (fun x => f (actAtPlaces F gPlaces x)) = f := by
      funext x
      exact hInv γ γ.property x
    rw [hact] at hcomm
    calc
      _ = partialLap F w (fun x => f (actAtPlaces F gPlaces x)) z := hcomm.symm
      _ = partialLap F w f z := by rw [hcomp]
  have htotal : totalLap F f ((γ : SL(2,𝓞 F)) • z) = totalLap F f z := by
    unfold totalLap
    exact Finset.sum_congr rfl (fun w hw => hpart w)
  simp only [sgGroundLaplacianRatio]
  rw [htotal, specGapGroundPhi_invariant d A γ z]

private theorem sgCuspStab_conjugateHeight_invariant (Γ : Subgroup SL(2,𝓞 F))
    (σ : SL(2,F)) (δ : Γ) (hδ : δ ∈ cuspStab F Γ σ) (z : X F) :
    normHeight F ((σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) • z) = normHeight F z := by
  have hb : σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ ∈ borelSL F := by
    simpa [cuspStab, MulAut.conj_apply] using hδ
  exact ((G2_x_action (F := F)).2.2.1
    ((δ : Γ) : SL(2,𝓞 F)) σ hb).2 z

private theorem sgCosetHeight_rep_eq (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (a b : Γ) (hab : QuotientGroup.rightRel (cuspStab F Γ σ) a b) (z : X F) :
    normHeight F (σ⁻¹ • ((a : SL(2,𝓞 F)) • z)) =
      normHeight F (σ⁻¹ • ((b : SL(2,𝓞 F)) • z)) := by
  let δ : Γ := b * a⁻¹
  have hδ : δ ∈ cuspStab F Γ σ := by
    dsimp [δ]
    exact (QuotientGroup.rightRel_apply.mp hab)
  have hb : b = δ * a := by simp [δ, mul_assoc]
  have hconj :
      (σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • ((a : SL(2,𝓞 F)) • z)) =
        σ⁻¹ • ((b : SL(2,𝓞 F)) • z) := by
    rw [hb]
    change (σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • (toSLF F ((a : Γ) : SL(2,𝓞 F)) • z)) =
        σ⁻¹ • ((toSLF F ((δ : Γ) : SL(2,𝓞 F)) *
          toSLF F ((a : Γ) : SL(2,𝓞 F))) • z)
    simp only [smul_smul]
    congr 1
    group
  rw [← hconj]
  exact (sgCuspStab_conjugateHeight_invariant Γ σ δ hδ
    (σ⁻¹ • ((a : SL(2,𝓞 F)) • z))).symm

theorem sgCompactLow_mem_orbit {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (B : ℝ) (hB : 0 ≤ B) (z : X F)
    (hbound : ∀ p : SpecGapCuspIndex Γ d, specGapAllCuspHeight Γ d p z ≤ B) :
    z ∈ orbitSaturation F Γ (⋃ i, SiegelData.compactBox F d i B) := by
  classical
  letI : Fintype d.ι := d.fintype
  have hR13 : ∀ i : d.ι, ∀ γ : Γ,
      normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ B := by
    intro i γ
    let q : CuspCosets F Γ (d.σ i) :=
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ
    let p : SpecGapCuspIndex Γ d := ⟨i, q⟩
    have hrep : specGapCosetHeight Γ (d.σ i) q z =
        normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) := by
      exact sgCosetHeight_rep_eq Γ (d.σ i) q.out γ (Quotient.mk_out γ) z
    have h := hbound p
    change specGapCosetHeight Γ (d.σ i) q z ≤ B at h
    rw [hrep] at h
    exact h
  have hcompact := (R13_compact_part Γ d).2 B hB z hR13
  rcases hcompact with ⟨i, γ, x, hx, hγx⟩
  refine ⟨γ, x, ?_, hγx⟩
  exact Set.mem_iUnion.2 ⟨i, hx⟩

private theorem sgGroundState_square_identity {α : ℝ} (hα : 0 < α)
    (x y : ℂ) (b : ℝ) :
    ‖y‖ ^ 2 - (2 * inner ℝ x y / α - ‖x‖ ^ 2 / α ^ 2 * b) * b =
      ‖y - (b / α) • x‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm y x]
  simp [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hα]
  field_simp [hα.ne']
  simp only [sq_abs]
  ring

private theorem sgGroundState_square_nonneg {α : ℝ} (hα : 0 < α)
    (x y : ℂ) (b : ℝ) :
    0 ≤ ‖y‖ ^ 2 - (2 * inner ℝ x y / α - ‖x‖ ^ 2 / α ^ 2 * b) * b := by
  rw [sgGroundState_square_identity hα]
  positivity

private theorem sgRealCast_inner_mul (a b : ℝ) :
    RCLike.re (star (a : ℂ) * (b : ℂ)) = a * b := by
  simp [Complex.conj_ofReal, Complex.ofReal_mul]

private theorem sgMeasurableConstSMul (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    MeasurableConstSMul Γ (X F) := by
  constructor
  intro γ
  letI : BorelSpace H3 := instBorelSpaceH3
  let gPlaces : InfinitePlace F → SL(2,ℂ) :=
    toInf F (toSLF F ((γ : Γ) : SL(2,𝓞 F)))
  apply measurable_pi_iff.2
  intro w
  change Measurable (fun x : X F => gPlaces w • x w)
  have hcont : Continuous (fun z : H3 => gPlaces w • z) :=
    OAI.CubicEisenstein.continuous_hyperbolic_action (gPlaces w)
  exact hcont.measurable.comp (measurable_pi_apply w)

private theorem sgVolX_smulInvariant (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    SMulInvariantMeasure Γ (X F) (volX F) := by
  refine ⟨?_⟩
  intro γ s hs
  letI : MeasurableConstSMul Γ (X F) := sgMeasurableConstSMul Γ
  let gPlaces : InfinitePlace F → SL(2,ℂ) :=
    toInf F (toSLF F ((γ : Γ) : SL(2,𝓞 F)))
  have hG3 := (G3_volume (F := F)).1 gPlaces
  have hmeas : Measurable (fun x : X F => actAtPlaces F gPlaces x) := by
    have hsm : Measurable (fun x : X F => (γ : SL(2,𝓞 F)) • x) :=
      measurable_const_smul γ
    convert hsm using 1
    funext x
    rfl
  have hmap := congrArg (fun μ : Measure (X F) => μ s) hG3
  rw [Measure.map_apply hmeas hs] at hmap
  have hact (x : X F) : actAtPlaces F gPlaces x =
      ((γ : SL(2,𝓞 F)) • x) := by rfl
  have hactFun : (fun x : X F => actAtPlaces F gPlaces x) =
      (fun x => ((γ : SL(2,𝓞 F)) • x)) := funext hact
  rw [hactFun] at hmap
  exact hmap

private theorem sgOrbitSaturation_measure_lt_top {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K) :
    (volX F).restrict D (orbitSaturation F Γ K) < ⊤ := by
  classical
  letI : MeasurableConstSMul Γ (X F) := sgMeasurableConstSMul Γ
  letI : SMulInvariantMeasure Γ (X F) (volX F) := sgVolX_smulInvariant Γ
  letI : Countable ℤ := inferInstance
  letI : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ) (M := 𝓞 F)
  letI : Countable (Fin 2 → 𝓞 F) := inferInstance
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    change Countable (Fin 2 → Fin 2 → 𝓞 F)
    infer_instance
  letI : Countable SL(2,𝓞 F) := by
    exact Subtype.val_injective.countable
  letI : Countable Γ := inferInstance
  have hVolK : volX F K < ⊤ := (G3_volume (F := F)).2.2.1 K hK
  have hUnion : D ∩ orbitSaturation F Γ K =
      ⋃ γ : Γ, D ∩ (γ • K) := by
    ext z
    constructor
    · rintro ⟨hzD, ⟨γ, x, hxK, hγx⟩⟩
      refine Set.mem_iUnion.2 ⟨γ, ⟨hzD, ?_⟩⟩
      exact ⟨x, hxK, hγx⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨γ, hzD, hxK⟩
      rcases hxK with ⟨x, hxK, hγx⟩
      exact ⟨hzD, γ, x, hxK, hγx⟩
  have hUnionBound :
      volX F (D ∩ orbitSaturation F Γ K) ≤
        ∑' γ : Γ, volX F (D ∩ (γ • K)) := by
    rw [hUnion]
    exact measure_iUnion_le (fun γ : Γ => D ∩ (γ • K))
  have hTsum :
      (∑' γ : Γ, volX F (D ∩ (γ • K))) = volX F K := by
    calc
      _ = ∑' γ : Γ, volX F ((γ • K) ∩ D) := by
        apply tsum_congr
        intro γ
        rw [Set.inter_comm]
      _ = volX F K := (hD.measure_eq_tsum K).symm
  rw [Measure.restrict_apply₀' hD.nullMeasurableSet]
  calc
    volX F (orbitSaturation F Γ K ∩ D) = volX F (D ∩ orbitSaturation F Γ K) := by
      rw [Set.inter_comm]
    _ ≤ ∑' γ : Γ, volX F (D ∩ (γ • K)) := hUnionBound
    _ = volX F K := hTsum
    _ < ⊤ := hVolK

private theorem sgInvariantContinuousBound {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (f : X F → ℂ) (hcont : Continuous f) (hinv : IsGammaInvariant F Γ f)
    (K : Set (X F)) (hK : IsCompact K)
    (hsupport : {z | f z ≠ 0} ⊆ orbitSaturation F Γ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖f z‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.image hcont |>.isBounded.exists_norm_le
  let B₀ := max 0 B
  refine ⟨B₀, le_max_left _ _, ?_⟩
  intro z
  by_cases hz0 : f z = 0
  · simp [hz0, B₀]
  · rcases hsupport hz0 with ⟨γ, x, hxK, hγx⟩
    have hEq : f z = f x := by
      rw [← hγx]
      exact hinv γ γ.property x
    rw [hEq]
    exact (hB (f x) (Set.mem_image_of_mem f hxK)).trans (le_max_right _ _)

theorem sgIntegrable_of_compactOrbitSupport {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (f : X F → ℂ) (hcont : Continuous f) (hinv : IsGammaInvariant F Γ f)
    (hAEStr : AEStronglyMeasurable f ((volX F).restrict D))
    (K : Set (X F)) (hK : IsCompact K)
    (hsupport : {z | f z ≠ 0} ⊆ orbitSaturation F Γ K) :
    Integrable f ((volX F).restrict D) := by
  let S := orbitSaturation F Γ K
  obtain ⟨B, hBpos, hB⟩ := sgInvariantContinuousBound f hcont hinv K hK hsupport
  have hμS : (volX F).restrict D S < ⊤ := by
    simpa [S] using sgOrbitSaturation_measure_lt_top (Γ := Γ) D hD K hK
  have hsm : AEStronglyMeasurable f (((volX F).restrict D).restrict S) :=
    hAEStr.mono_measure (Measure.restrict_le_self)
  have hOn : IntegrableOn f S ((volX F).restrict D) :=
    IntegrableOn.of_bound hμS hsm B (ae_of_all _ hB)
  apply hOn.integrable_of_forall_notMem_eq_zero
  intro z hz
  by_contra hne
  exact hz (hsupport hne)

def specGapGroundQuotient (f : X F → ℂ) (φ : X F → ℝ) (z : X F) : ℝ :=
  Complex.normSq (f z) / φ z

theorem specGapGroundQuotient_smooth (f : X F → ℂ) (φ : X F → ℝ)
    (hf : IsSmoothX F f) (hφ : IsSmoothRealX F φ) (hφpos : ∀ z, 0 < φ z) :
    IsSmoothRealX F (specGapGroundQuotient f φ) := by
  change ContDiffOn ℝ ∞
    (fun p => Complex.normSq (f (ptX F p)) / φ (ptX F p)) (posSet F)
  have hnum : ContDiffOn ℝ ∞ (fun p => Complex.normSq (f (ptX F p))) (posSet F) := by
    have hnorm : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
      simpa only [Complex.normSq_eq_norm_sq] using
        (contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2))
    exact hnorm.comp_contDiffOn hf
  apply ContDiffOn.div hnum hφ
  intro p hp
  exact (hφpos (ptX F p)).ne'

theorem specGapGroundQuotient_invariant {Γ : Subgroup SL(2,𝓞 F)}
    (f : X F → ℂ) (φ : X F → ℝ) (hInv : IsGammaInvariant F Γ f)
    (hφInv : IsGammaInvariant F Γ (fun z => (φ z : ℂ))) :
    IsGammaInvariant F Γ (fun z => (specGapGroundQuotient f φ z : ℂ)) := by
  intro γ hγ z
  simp [specGapGroundQuotient, hInv γ hγ z, hφInv γ hγ z]

private theorem sgFDeriv_normSq {u : Coord F → ℂ} (p e : Coord F)
    (hu : DifferentiableAt ℝ u p) :
    fderiv ℝ (fun x => Complex.normSq (u x)) p e =
      2 * inner ℝ (u p) (fderiv ℝ u p e) := by
  have hEq : (fun x => Complex.normSq (u x)) = fun x => ‖u x‖ ^ 2 := by
    funext x
    exact Complex.normSq_eq_norm_sq (u x)
  rw [hEq]
  have hnum := hu.hasFDerivAt.norm_sq
  rw [hnum.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

private theorem sgFDeriv_div {a b : Coord F → ℝ} (p e : Coord F)
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hb0 : b p ≠ 0) :
    fderiv ℝ (fun x => a x / b x) p e =
      fderiv ℝ a p e / b p - a p / b p ^ 2 * fderiv ℝ b p e := by
  have hInv := (hasFDerivAt_inv hb0).comp p hb.hasFDerivAt
  have hmul := ha.hasFDerivAt.mul hInv
  have hfun : (fun x => a x / b x) = fun x => a x * (b x)⁻¹ := by
    funext x
    ring
  have hmulD : fderiv ℝ (fun x => a x * (b x)⁻¹) p e =
      -(a p * (fderiv ℝ b p e * (b p ^ 2)⁻¹)) +
        (b p)⁻¹ * fderiv ℝ a p e := by
    have h := congrArg (fun L => L e) hmul.fderiv
    have hmulFun : (a * ((fun x : ℝ => x⁻¹) ∘ b)) =
        fun x => a x * (b x)⁻¹ := by
      funext x
      rfl
    change fderiv ℝ (a * ((fun x : ℝ => x⁻¹) ∘ b)) p e = _ at h
    rw [hmulFun] at h
    simpa [Function.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using h
  rw [hfun, hmulD]
  field_simp [hb0]
  ring

theorem specGapGroundQuotient_placeGradient (f : X F → ℂ) (φ : X F → ℝ)
    (hf : IsSmoothX F f) (hφ : IsSmoothRealX F φ)
    (hq : IsSmoothRealX F (specGapGroundQuotient f φ))
    (hφpos : ∀ z, 0 < φ z) (z : X F) (w : InfinitePlace F) (j : Fin 3) :
    placeGradient F w (fun x => (specGapGroundQuotient f φ x : ℂ)) z j =
      ((2 * inner ℝ (f z) (placeGradient F w f z j) / φ z -
        Complex.normSq (f z) / φ z ^ 2 *
          (placeGradient F w (fun x => (φ x : ℂ)) z j).re : ℝ) : ℂ) := by
  let p : Coord F := coordsX F z
  let e : Coord F := placeDirection F w j
  have hp : p ∈ posSet F := by
    intro v
    change 0 < height (z v)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  let u : Coord F → ℂ := fun x => f (ptX F x)
  let vφ : Coord F → ℝ := fun x => φ (ptX F x)
  let q : Coord F → ℝ := fun x => specGapGroundQuotient f φ (ptX F x)
  have hu : DifferentiableAt ℝ u p :=
    (hf.contDiffAt (sgPosSetOpen.mem_nhds hp)).differentiableAt (by norm_num)
  have hvφ : DifferentiableAt ℝ vφ p :=
    (hφ.contDiffAt (sgPosSetOpen.mem_nhds hp)).differentiableAt (by norm_num)
  have hqAt : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (sgPosSetOpen.mem_nhds hp)).differentiableAt (by norm_num)
  have hqEq : q = fun x => Complex.normSq (u x) / vφ x := by
    funext x
    rfl
  have hqDeriv : fderiv ℝ q p e =
      fderiv ℝ (fun x => Complex.normSq (u x)) p e / vφ p -
        Complex.normSq (u p) / vφ p ^ 2 * fderiv ℝ vφ p e := by
    rw [hqEq]
    exact sgFDeriv_div p e
      (by
        have hnormAt : DifferentiableAt ℝ (fun y : ℂ => ‖y‖ ^ 2) (u p) :=
          (hasStrictFDerivAt_norm_sq (u p)).differentiableAt
        have hnum : DifferentiableAt ℝ (fun x => ‖u x‖ ^ 2) p := hnormAt.comp p hu
        have hEq : (fun x => Complex.normSq (u x)) = fun x => ‖u x‖ ^ 2 := by
          funext x
          exact Complex.normSq_eq_norm_sq (u x)
        rw [hEq]
        exact hnum)
      hvφ (ne_of_gt (hφpos (ptX F p)))
  have hnumDeriv : fderiv ℝ (fun x => Complex.normSq (u x)) p e =
      2 * inner ℝ (u p) (fderiv ℝ u p e) := sgFDeriv_normSq p e hu
  have hqComplexDeriv := sgFDeriv_ofReal p e hqAt
  have hphiComplexDeriv : fderiv ℝ (fun x => (vφ x : ℂ)) p e =
      (fderiv ℝ vφ p e : ℂ) := sgFDeriv_ofReal p e hvφ
  have hqGradient :
      placeGradient F w (fun x => (specGapGroundQuotient f φ x : ℂ)) z j =
        ((p w).2 : ℂ) * ((fderiv ℝ q p e : ℝ) : ℂ) := by
    change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun x => (q x : ℂ)) (coordsX F z) (placeDirection F w j) = _
    rw [hqComplexDeriv]
  have hfGradient : placeGradient F w f z j =
      (p w).2 * (fderiv ℝ u p e) := by
    change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun x => f (ptX F x)) (coordsX F z) (placeDirection F w j) = _
    rfl
  have hφGradient : placeGradient F w (fun x => (φ x : ℂ)) z j =
      ((p w).2 * fderiv ℝ vφ p e : ℂ) := by
    change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun x => (vφ x : ℂ)) (coordsX F z) (placeDirection F w j) = _
    rw [hphiComplexDeriv]
  rw [hqGradient, hfGradient, hφGradient, hqDeriv, hnumDeriv]
  have huval : u p = f z := by simp [u, hpt]
  have hφval : vφ p = φ z := by simp [vφ, hpt]
  rw [huval, hφval]
  have hsmul : (↑(p w).2 : ℂ) * fderiv ℝ u p e =
      (p w).2 • fderiv ℝ u p e := by simp [smul_eq_mul]
  rw [hsmul]
  rw [real_inner_smul_right]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  field_simp [ne_of_gt (hφpos z)]

theorem specGapGroundRealGradient (φ : X F → ℝ) (hφ : IsSmoothRealX F φ)
    (z : X F) (w : InfinitePlace F) (j : Fin 3) :
    placeGradient F w (fun x => (φ x : ℂ)) z j =
      ((coordsX F z w).2 *
        fderiv ℝ (fun p => φ (ptX F p)) (coordsX F z)
          (placeDirection F w j) : ℝ) := by
  have hp : coordsX F z ∈ posSet F := by
    intro v
    change 0 < height (z v)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hφdiff : DifferentiableAt ℝ (fun p => φ (ptX F p)) (coordsX F z) :=
    (hφ.contDiffAt (sgPosSetOpen.mem_nhds hp)).differentiableAt (by norm_num)
  change ((coordsX F z w).2 : ℂ) *
    fderiv ℝ (fun p => (φ (ptX F p) : ℂ)) (coordsX F z)
      (placeDirection F w j) = _
  rw [sgFDeriv_ofReal _ _ hφdiff]
  simp [Complex.ofReal_mul]

theorem specGapGroundQuotient_density_ineq (f : X F → ℂ) (φ : X F → ℝ)
    (hf : IsSmoothX F f) (hφ : IsSmoothRealX F φ)
    (hq : IsSmoothRealX F (specGapGroundQuotient f φ))
    (hφpos : ∀ z, 0 < φ z) (z : X F) :
    totalGradNormSq F f z ≥
      RCLike.re (∑ w : InfinitePlace F,
        ∑ j : Fin 3, star (placeGradient F w
          (fun x => (specGapGroundQuotient f φ x : ℂ)) z j) *
          placeGradient F w (fun x => (φ x : ℂ)) z j) := by
  classical
  let qC : X F → ℂ := fun x => (specGapGroundQuotient f φ x : ℂ)
  have hterm (w : InfinitePlace F) (j : Fin 3) :
      0 ≤ Complex.normSq (placeGradient F w f z j) -
        RCLike.re (star (placeGradient F w qC z j) *
          placeGradient F w (fun x => (φ x : ℂ)) z j) := by
    have hqgrad := specGapGroundQuotient_placeGradient f φ hf hφ hq hφpos z w j
    have hφgrad := specGapGroundRealGradient φ hφ z w j
    have hsq := sgGroundState_square_nonneg (hφpos z) (f z)
      (placeGradient F w f z j)
      (RCLike.re (placeGradient F w (fun x => (φ x : ℂ)) z j))
    have hqgrad' : placeGradient F w qC z j =
        ((2 * inner ℝ (f z) (placeGradient F w f z j) / φ z -
          Complex.normSq (f z) / φ z ^ 2 *
            (placeGradient F w (fun x => (φ x : ℂ)) z j).re : ℝ) : ℂ) := by
      simpa [qC] using hqgrad
    have hpair : RCLike.re (star (placeGradient F w qC z j) *
        placeGradient F w (fun x => (φ x : ℂ)) z j) =
        (2 * inner ℝ (f z) (placeGradient F w f z j) / φ z -
          Complex.normSq (f z) / φ z ^ 2 *
            (placeGradient F w (fun x => (φ x : ℂ)) z j).re) *
          (placeGradient F w (fun x => (φ x : ℂ)) z j).re := by
      let a : ℝ := 2 * inner ℝ (f z) (placeGradient F w f z j) / φ z -
        Complex.normSq (f z) / φ z ^ 2 *
          (placeGradient F w (fun x => (φ x : ℂ)) z j).re
      let b : ℝ := (placeGradient F w (fun x => (φ x : ℂ)) z j).re
      have hqa : placeGradient F w qC z j = (a : ℂ) := by
        simpa [a] using hqgrad'
      have hpb : placeGradient F w (fun x => (φ x : ℂ)) z j = (b : ℂ) := by
        change placeGradient F w (fun x => (φ x : ℂ)) z j =
          ((placeGradient F w (fun x => (φ x : ℂ)) z j).re : ℂ)
        simp [hφgrad, Complex.ofReal_re]
      rw [hqa, hpb]
      exact sgRealCast_inner_mul a b
    rw [hpair]
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hsum : 0 ≤ ∑ w : InfinitePlace F, ∑ j : Fin 3,
      (Complex.normSq (placeGradient F w f z j) -
        RCLike.re (star (placeGradient F w qC z j) *
          placeGradient F w (fun x => (φ x : ℂ)) z j)) := by
    apply Finset.sum_nonneg
    intro w hw
    apply Finset.sum_nonneg
    intro j hj
    exact hterm w j
  have henergy : totalGradNormSq F f z =
      ∑ w : InfinitePlace F, ∑ j : Fin 3,
        Complex.normSq (placeGradient F w f z j) := by
    simp [totalGradNormSq, placeGradNormSq, Fintype.sum_prod_type]
  have hinner : RCLike.re (∑ w : InfinitePlace F,
      ∑ j : Fin 3, star (placeGradient F w qC z j) *
        placeGradient F w (fun x => (φ x : ℂ)) z j) =
      ∑ w : InfinitePlace F, ∑ j : Fin 3,
        RCLike.re (star (placeGradient F w qC z j) *
          placeGradient F w (fun x => (φ x : ℂ)) z j) := by
    simp [Complex.re_sum]
  rw [henergy, hinner]
  have hsumEq :
      (∑ w : InfinitePlace F, ∑ j : Fin 3, Complex.normSq (placeGradient F w f z j)) -
        ∑ w : InfinitePlace F, ∑ j : Fin 3,
          RCLike.re (star (placeGradient F w qC z j) *
            placeGradient F w (fun x => (φ x : ℂ)) z j) =
        ∑ w : InfinitePlace F, ∑ j : Fin 3,
          (Complex.normSq (placeGradient F w f z j) -
            RCLike.re (star (placeGradient F w qC z j) *
              placeGradient F w (fun x => (φ x : ℂ)) z j)) := by
    simp_rw [Finset.sum_sub_distrib]
  have hdiff : 0 ≤
      (∑ w : InfinitePlace F, ∑ j : Fin 3, Complex.normSq (placeGradient F w f z j)) -
        ∑ w : InfinitePlace F, ∑ j : Fin 3,
          RCLike.re (star (placeGradient F w qC z j) *
            placeGradient F w (fun x => (φ x : ℂ)) z j) := by
    rw [hsumEq]
    exact hsum
  exact sub_nonneg.mp hdiff

theorem sgPlaceGradInner_continuous (f g : X F → ℂ)
    (hf : IsSmoothX F f) (hg : IsSmoothX F g) (w : InfinitePlace F) :
    Continuous (placeGradInner F w f g) := by
  have hterm (j : Fin 3) : Continuous
      (fun z => star (placeGradient F w f z j) * placeGradient F w g z j) := by
    have hf' := sgPlaceGradient_continuous f hf w j
    have hg' := sgPlaceGradient_continuous g hg w j
    fun_prop
  unfold placeGradInner
  exact continuous_finsetSum Finset.univ (fun j hj => hterm j)

theorem sgPartialLap_invariant {Γ : Subgroup SL(2,𝓞 F)}
    (γ : Γ) (f : X F → ℂ) (hf : IsSmoothX F f)
    (hinv : IsGammaInvariant F Γ f) (w : InfinitePlace F) (z : X F) :
    partialLap F w f ((γ : SL(2,𝓞 F)) • z) = partialLap F w f z := by
  let zero : X F → ℂ := fun _ => 0
  have hzsm : IsSmoothX F zero := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  have hzcompact : HasCompactSupportX F zero := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp [zero]
  have hG5 := G5_green_x zero zero hzsm hzsm hzcompact
  let gPlaces : InfinitePlace F → SL(2,ℂ) :=
    toInf F (toSLF F ((γ : Γ) : SL(2,𝓞 F)))
  have hact (x : X F) : actAtPlaces F gPlaces x =
      ((γ : SL(2,𝓞 F)) • x) := by rfl
  have hcomm := hG5.2.2 gPlaces f hf w z
  have hcompAct : (fun x => f (actAtPlaces F gPlaces x)) = f := by
    funext x
    rw [hact]
    exact hinv γ γ.property x
  rw [hcompAct, hact] at hcomm
  exact hcomm.symm

theorem sgPlaceGradInner_invariant {Γ : Subgroup SL(2,𝓞 F)}
    (γ : Γ) (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g)
    (hfinv : IsGammaInvariant F Γ f) (hginv : IsGammaInvariant F Γ g)
    (w : InfinitePlace F) (z : X F) :
    placeGradInner F w f g ((γ : SL(2,𝓞 F)) • z) = placeGradInner F w f g z := by
  let gPlaces : InfinitePlace F → SL(2,ℂ) :=
    toInf F (toSLF F ((γ : Γ) : SL(2,𝓞 F)))
  have hact (x : X F) : actAtPlaces F gPlaces x =
      ((γ : SL(2,𝓞 F)) • x) := by rfl
  have hcompf : (fun x => f (actAtPlaces F gPlaces x)) = f := by
    funext x
    rw [hact]
    exact hfinv γ γ.property x
  have hcompg : (fun x => g (actAtPlaces F gPlaces x)) = g := by
    funext x
    rw [hact]
    exact hginv γ γ.property x
  have hG4 := (G4_energy gPlaces f g hf hg).1 w z
  rw [hcompf, hcompg, hact] at hG4
  exact hG4.symm

theorem sgGroundQuotient_nonzero_implies (f : X F → ℂ) (φ : X F → ℝ)
    (z : X F) (hq : specGapGroundQuotient f φ z ≠ 0) : f z ≠ 0 := by
  intro hfz
  apply hq
  simp [specGapGroundQuotient, hfz]

theorem sgGroundQuotient_placeGradient_zero_of_zero (f : X F → ℂ)
    (φ : X F → ℝ) (hf : IsSmoothX F f) (hφ : IsSmoothRealX F φ)
    (hq : IsSmoothRealX F (specGapGroundQuotient f φ))
    (hφpos : ∀ z, 0 < φ z) (z : X F) (hfz : f z = 0)
    (w : InfinitePlace F) (j : Fin 3) :
    placeGradient F w (fun x => (specGapGroundQuotient f φ x : ℂ)) z j = 0 := by
  have h := specGapGroundQuotient_placeGradient f φ hf hφ hq hφpos z w j
  simpa [hfz] using h

end ArtinPrimitiveRoots.A1.Spec
