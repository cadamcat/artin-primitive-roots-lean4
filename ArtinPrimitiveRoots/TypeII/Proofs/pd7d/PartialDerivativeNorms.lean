import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FourierDerivatives2
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelDerivativeBounds

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory LineDeriv
set_option autoImplicit false

lemma pd7d_schwartz_line_jet_norm (F : SchwartzMap PDPlane ℂ) (d u : PDPlane) (k : ℕ) :
    ‖iteratedFDeriv ℝ k ((∂_{d} F : SchwartzMap PDPlane ℂ) : PDPlane → ℂ) u‖ ≤
      ‖d‖ * ‖iteratedFDeriv ℝ (k + 1) (F : PDPlane → ℂ) u‖ := by
  have hfun : ((∂_{d} F : SchwartzMap PDPlane ℂ) : PDPlane → ℂ) =
      fun y => fderiv ℝ (F : PDPlane → ℂ) y d := by
    funext y
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv d F y
  have hfder : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (F : PDPlane → ℂ)) u :=
    (SchwartzMap.fderivCLM ℝ PDPlane ℂ F).smooth ⊤ |>.contDiffAt
  have hh := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ (F : PDPlane → ℂ))
    (c := d) (n := k) hfder (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hh
  rw [hfun]
  exact hh

lemma pd7dPartial_jet_norm (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (n k : ℕ) (u : PDPlane) :
    ‖iteratedFDeriv ℝ k (pd7dPartial i n F : PDPlane → ℂ) u‖ ≤
      ‖iteratedFDeriv ℝ (n + k) (F : PDPlane → ℂ) u‖ := by
  induction n generalizing k with
  | zero =>
    rw [pd7dPartial, show (0 : ℕ) + k = k by omega]
  | succ n ih =>
    rw [pd7dPartial]
    have hstep := pd7d_schwartz_line_jet_norm (pd7dPartial i n F)
      (EuclideanSpace.single i (1 : ℝ)) u k
    have hdir : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    rw [hdir, one_mul] at hstep
    have htail := ih (k + 1)
    rw [show n + (k + 1) = n + 1 + k by omega] at htail
    exact hstep.trans htail

lemma pd7dPartial_norm (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (n : ℕ) (u : PDPlane) :
    ‖pd7dPartial i n F u‖ ≤ ‖iteratedFDeriv ℝ n (F : PDPlane → ℂ) u‖ := by
  have hh := pd7dPartial_jet_norm F i n 0 u
  simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using hh

lemma pd7dPartial_mixed_norm (F : SchwartzMap PDPlane ℂ) (n : ℕ) (u : PDPlane) :
    ‖pd7dPartial 0 n (pd7dPartial 1 n F) u‖ ≤ ‖iteratedFDeriv ℝ (2 * n) (F : PDPlane → ℂ) u‖ := by
  have hfirst := pd7dPartial_norm (pd7dPartial 1 n F) 0 n u
  have hsecond := pd7dPartial_jet_norm F 1 n n u
  rw [show n + n = 2 * n by omega] at hsecond
  exact hfirst.trans hsecond

lemma pd7d_norm_integral_bound_of_support {S : Set PDPlane} (f : PDPlane → ℂ) (M : ℝ)
    (hS : MeasurableSet S) (hSfinite : volume S ≠ ⊤) (hf : Integrable f)
    (hM : 0 ≤ M) (hbound : ∀ u, ‖f u‖ ≤ M) (hsupp : Function.support f ⊆ S) :
    (∫ u : PDPlane, ‖f u‖) ≤ M * volume.real S := by
  have hi : Integrable (S.indicator (fun _ : PDPlane => M)) :=
    (integrableOn_const (s := S) (C := M) hSfinite).integrable_indicator hS
  have hp : ∀ u, ‖f u‖ ≤ S.indicator (fun _ => M) u := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      exact hbound u
    · have hz : f u = 0 := by
        by_contra hne
        exact hu (hsupp hne)
      simp [Set.indicator_of_notMem hu, hz]
  calc
    _ ≤ ∫ u : PDPlane, S.indicator (fun _ => M) u := integral_mono hf.norm hi hp
    _ = _ := by rw [integral_indicator_const _ hS]; simp [smul_eq_mul, mul_comm]

end ArtinPrimitiveRoots.TypeII.PD
