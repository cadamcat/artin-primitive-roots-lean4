import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusRootReduction
import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaExpRoots
import ArtinPrimitiveRoots.Proofs.th_continue_b.PartialDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical Topology ContDiff
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_theta_torus_iteratedFDeriv_cont
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g h : P.tc.G) (n : ℕ) :
    Continuous fun y : S.FSˣ => iteratedFDeriv ℝ n
      (fun x : InfinitePlace F → ℂ => R.theta (g * P.tc.aS y * h * nInf P x)) 0 := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro y0
  let logRatio (y : S.FSˣ) (w : InfinitePlace F) : ℂ :=
    Complex.log (S.compC w (y0⁻¹ * y) : ℂ)
  have hLog : ContinuousAt logRatio y0 := by
    apply continuousAt_pi.mpr
    intro w
    have hC : Continuous (S.compC w) := by
      unfold SData.compC
      apply Continuous.units_map
      exact (continuous_apply w).comp continuous_snd
    have hRatio : Continuous (fun y : S.FSˣ => S.compC w (y0⁻¹ * y)) :=
      hC.comp (continuous_const.mul continuous_id)
    have hVal : ContinuousAt (fun y : S.FSˣ =>
        (S.compC w (y0⁻¹ * y) : ℂ)) y0 :=
      Units.continuous_val.continuousAt.comp hRatio.continuousAt
    have hOne : (S.compC w (y0⁻¹ * y0) : ℂ) = 1 := by
      rw [inv_mul_cancel, map_one, Units.val_one]
    exact hVal.clog (by rw [hOne]; exact Complex.one_mem_slitPlane)
  have hExp (y : S.FSˣ) : continuedEis_archExp S (logRatio y) =
      continuedEis_archPart S (y0⁻¹ * y) := by
    apply Units.ext
    apply Prod.ext
    · rfl
    · funext w
      change Complex.exp (Complex.log (S.compC w (y0⁻¹ * y) : ℂ)) =
        (S.compC w (y0⁻¹ * y) : ℂ)
      exact Complex.exp_log (S.compC w (y0⁻¹ * y)).ne_zero
  let model (t : InfinitePlace F → ℂ) := iteratedFDeriv ℝ n
    (fun x : InfinitePlace F → ℂ =>
      R.theta ((g * P.tc.aS y0) * P.tc.aS (continuedEis_archExp S t) * h * nInf P x)) 0
  have hModel : Continuous model :=
    continuedEis_partial_iteratedFDeriv_continuous _
      (continuedEis_theta_torusExp_root_contDiff R (g * P.tc.aS y0) h) n
  have hCompose : ContinuousAt (fun y => model (logRatio y)) y0 :=
    hModel.continuousAt.comp hLog
  have hEq : (fun y : S.FSˣ => iteratedFDeriv ℝ n
      (fun x : InfinitePlace F → ℂ => R.theta (g * P.tc.aS y * h * nInf P x)) 0) =ᶠ[𝓝 y0]
      (fun y => model (logRatio y)) := by
    filter_upwards [continuedEis_theta_torus_root_local_reduction R g h y0] with y hy
    have hFun : (fun x : InfinitePlace F → ℂ =>
        R.theta (g * P.tc.aS y * h * nInf P x)) =
        (fun x => R.theta ((g * P.tc.aS y0) *
          P.tc.aS (continuedEis_archExp S (logRatio y)) * h * nInf P x)) := by
      funext x
      rw [hExp]
      exact hy x
    exact congrArg (fun f : (InfinitePlace F → ℂ) → ℂ => iteratedFDeriv ℝ n f 0) hFun
  exact hCompose.congr hEq.symm

end ArtinPrimitiveRoots.A1.Theta
