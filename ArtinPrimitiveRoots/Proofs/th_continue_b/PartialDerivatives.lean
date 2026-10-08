import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open scoped ContDiff
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem continuedEis_partial_iteratedFDeriv_continuous
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : E × V → W) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Continuous (fun t : E => iteratedFDeriv ℝ n (fun x : V => f (t, x)) 0) := by
  let L : V →L[ℝ] E × V := ContinuousLinearMap.inr ℝ E V
  let M : ContinuousMultilinearMap ℝ (fun _ : Fin n => E × V) W →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => V) W :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by simp
  have hSlice (t : E) :
      iteratedFDeriv ℝ n (fun x : V => f (t, x)) 0 =
        M (iteratedFDeriv ℝ n f (t, 0)) := by
    have hShift : ContDiff ℝ ∞ (fun q : E × V => f ((t, 0) + q)) :=
      hf.comp (contDiff_const.add contDiff_id)
    have h := L.iteratedFDeriv_comp_right hShift (0 : V) (i := n) hn
    have hFun : ((fun q : E × V => f ((t, 0) + q)) ∘ L) =
        (fun x : V => f (t, x)) := by
      funext x
      change f ((t, 0) + (0, x)) = f (t, x)
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    rw [hFun, L.map_zero, iteratedFDeriv_comp_add_left] at h
    simpa only [add_zero, M, ContinuousMultilinearMap.compContinuousLinearMapL_apply] using h
  have hJoint : Continuous (fun t : E => iteratedFDeriv ℝ n f (t, 0)) :=
    (hf.continuous_iteratedFDeriv hn).comp (continuous_id.prodMk continuous_const)
  have hModel : Continuous (fun t : E => M (iteratedFDeriv ℝ n f (t, 0))) :=
    M.continuous.comp hJoint
  have hEq : (fun t : E => iteratedFDeriv ℝ n (fun x : V => f (t, x)) 0) =
      (fun t : E => M (iteratedFDeriv ℝ n f (t, 0))) := by
    funext t
    exact hSlice t
  rw [hEq]
  exact hModel

end ArtinPrimitiveRoots.A1.Theta
