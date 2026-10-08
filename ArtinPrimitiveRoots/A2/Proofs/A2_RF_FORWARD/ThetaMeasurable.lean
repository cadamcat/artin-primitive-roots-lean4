import ArtinPrimitiveRoots.Theta.AnalysisS

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

theorem thetaV_measurable {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hU : MeasurableSet U)
    (cS : InfinitePlace F → ℝ) :
    Measurable (Theta.thetaV S μ v0 U cS) := by
  classical
  let P := (∀ v : S.Sf, v.1.adicCompletion F) ×
    ({w : InfinitePlace F // w ≠ v0} → ℂ)
  let ν : Measure P :=
    (Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC)
  let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
    ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  have hSubstrate := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  letI : ∀ v : S.Sf, SigmaFinite (mulHaarFin (μ v.1)) :=
    fun v => (hSubstrate.1 v.1).2.2.2.2
  letI : SigmaFinite mulHaarC := hSubstrate.2.2
  have hB : Measurable B := by
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (hSubstrate.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  have hBessel : Measurable (ArtinPrimitiveRoots.A1.besselK (1 / 3)) := by
    have hContinuous : Continuous (fun q : ℝ × ℝ =>
        Real.exp (-q.1 * Real.cosh q.2) * Real.cosh ((1 / 3 : ℝ) * q.2)) := by
      fun_prop
    change Measurable (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t))
    exact (hContinuous.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable
  have hRoot : Measurable (fun q : (ℝ × P) × ℝ =>
      ((Real.sqrt (q.1.1 / B q.1.2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp
        (measurable_fst.fst.div (hB.comp measurable_fst.snd)))
  have hAngle : Measurable (fun q : (ℝ × P) × ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (q.2 : ℂ))) := by
    fun_prop
  have hPoint : Measurable (fun q : (ℝ × P) × ℝ =>
      sheetPoint S v0 q.1.1 q.1.2 q.2) := by
    have hFin : Measurable (fun q : (ℝ × P) × ℝ => Prod.fst q.1.2) :=
      measurable_fst.comp measurable_fst.snd
    have hFree : Measurable (fun q : (ℝ × P) × ℝ => Prod.snd q.1.2) :=
      measurable_snd.comp measurable_fst.snd
    refine hFin.prodMk ?_
    apply measurable_pi_iff.mpr
    intro w
    by_cases hw : w = v0
    · simp only [sheetPoint, dif_pos hw]
      exact hRoot.mul hAngle
    · simp only [sheetPoint, dif_neg hw]
      exact (measurable_pi_apply ⟨w, hw⟩).comp hFree
  let radial : S.FS → ℂ := fun y => (if y.1 ∈ U then (1 : ℂ) else 0) *
    ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) *
      (ArtinPrimitiveRoots.A1.besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)
  have hRadial : Measurable radial := by
    have hCut : Measurable (fun y : S.FS => if y.1 ∈ U then (1 : ℂ) else 0) :=
      Measurable.ite (hU.preimage measurable_fst) measurable_const measurable_const
    refine hCut.mul (Finset.univ.measurable_fun_prod ?_)
    intro w hw
    have hCoordinate : Measurable (fun y : S.FS => y.2 w) :=
      (measurable_pi_apply w).comp measurable_snd
    exact (Complex.continuous_ofReal.measurable.comp
      (Complex.continuous_normSq.measurable.comp hCoordinate)).mul
        (Complex.continuous_ofReal.measurable.comp
          (hBessel.comp (measurable_const.mul hCoordinate.norm)))
  have hJoint : StronglyMeasurable (fun q : (ℝ × P) × ℝ =>
      radial (sheetPoint S v0 q.1.1 q.1.2 q.2)) :=
    (hRadial.comp hPoint).stronglyMeasurable
  have hInner : StronglyMeasurable (fun q : ℝ × P =>
      ∫ θ in Set.Ioc (0 : ℝ) 1, radial (sheetPoint S v0 q.1 q.2 θ)) :=
    hJoint.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  have hOuter : StronglyMeasurable (fun u : ℝ =>
      ∫ p, ∫ θ in Set.Ioc (0 : ℝ) 1, radial (sheetPoint S v0 u p θ) ∂volume ∂ν) :=
    hInner.integral_prod_right' (ν := ν)
  change Measurable (fun u : ℝ =>
    ∫ p, ∫ θ in Set.Ioc (0 : ℝ) 1,
      radial (sheetPoint S v0 u p θ) ∂volume ∂ν)
  exact hOuter.measurable

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
