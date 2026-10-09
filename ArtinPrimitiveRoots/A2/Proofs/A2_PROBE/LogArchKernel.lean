import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- The archimedean part of the probe after logarithmic reparametrization. -/
def archLogKernel {J : Type*} [Fintype J]
    (f1 : ℝ → ℂ) (arch : J → SchwartzMap ℂ ℂ) (κ : ℝ)
    (p : ℝ × (J → ℂ)) : ℂ :=
  ((Real.exp (-p.1 / 2) : ℝ) : ℂ) * f1 (Real.exp p.1) *
    ∏ w, arch w (p.2 w * ((Real.exp (-κ * p.1) : ℝ) : ℂ))

/-- The logarithmic archimedean tensor is jointly smooth in the logarithmic scale and
all archimedean coordinates. -/
theorem archLogKernel_smooth {J : Type*} [Fintype J]
    (f1 : ℝ → ℂ) (arch : J → SchwartzMap ℂ ℂ) (κ : ℝ)
    (hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (archLogKernel f1 arch κ) := by
  have hweight : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (J → ℂ) => ((Real.exp (-p.1 / 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_fst.neg.div_const 2))
  have hf1exp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (J → ℂ) => f1 (Real.exp p.1)) :=
    hf1.comp (Real.contDiff_exp.comp contDiff_fst)
  have hdilation : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (J → ℂ) => ((Real.exp (-κ * p.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have htensor : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (J → ℂ) =>
        ∏ w, arch w (p.2 w * ((Real.exp (-κ * p.1) : ℝ) : ℂ))) := by
    apply contDiff_prod
    intro w _
    exact ((arch w).smooth (⊤ : ℕ∞)).comp
      (((contDiff_apply ℝ ℂ w).comp contDiff_snd).mul hdilation)
  exact (hweight.mul hf1exp).mul htensor

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
