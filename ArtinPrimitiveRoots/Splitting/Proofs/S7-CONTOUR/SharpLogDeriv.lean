import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrefactorDeriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- Off the real axis and xi's zeros, the sharp-zeta logarithmic derivative separates its factors. -/
theorem sharp_logderiv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s.im ≠ 0) (hxi : dedekindXi K s ≠ 0) :
    DifferentiableAt ℂ (dedekindZetaSharp K) s ∧
    dedekindZetaSharp K s ≠ 0 ∧
    dedekindZetaLogDerivative K s =
      -(deriv (dedekindXi K) s / dedekindXi K s) + 1 / s + 1 / (s - 1) +
        deriv (dedekindPrefactor K) s / dedekindPrefactor K s := by
  have hdXi : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (dedekind_completed K)).1
  have hs₀ : s ≠ 0 := by
    intro h
    apply hs
    simp [h]
  have hs₁ : s - 1 ≠ 0 := by
    intro h
    have heq : s = 1 := sub_eq_zero.mp h
    apply hs
    simp [heq]
  obtain ⟨hdP, hP, _⟩ := prefactor_logderiv K hs
  have hdSub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    differentiableAt_id.sub_const (1 : ℂ)
  let d : ℂ → ℂ := fun z => z * (z - 1) * dedekindPrefactor K z
  have hd : d s ≠ 0 := mul_ne_zero (mul_ne_zero hs₀ hs₁) hP
  have hdd : DifferentiableAt ℂ d s :=
    (differentiableAt_id.mul hdSub).mul hdP
  have hsharp : dedekindZetaSharp K = fun z : ℂ => dedekindXi K z / d z := rfl
  have hdSharp : DifferentiableAt ℂ (dedekindZetaSharp K) s := by
    rw [hsharp]
    exact (hdXi s).div hdd hd
  have hSharp : dedekindZetaSharp K s ≠ 0 := by
    rw [hsharp]
    exact div_ne_zero hxi hd
  have hSubDer : deriv (fun z : ℂ => z - 1) s = 1 :=
    ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
  have hSubLog : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, hSubDer]
  have hdlog : logDeriv d s = 1 / s + 1 / (s - 1) +
      deriv (dedekindPrefactor K) s / dedekindPrefactor K s := by
    dsimp only [d]
    rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
        (g := dedekindPrefactor K) s (mul_ne_zero hs₀ hs₁) hP
        (differentiableAt_id.mul hdSub) hdP,
      logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
        s hs₀ hs₁ differentiableAt_id hdSub,
      logDeriv_id', hSubLog, logDeriv_apply]
  have hsharplog : logDeriv (dedekindZetaSharp K) s =
      logDeriv (dedekindXi K) s - logDeriv d s := by
    rw [hsharp]
    exact logDeriv_fun_div (f := dedekindXi K) (g := d) s hxi hd (hdXi s) hdd
  refine ⟨hdSharp, hSharp, ?_⟩
  rw [dedekindZetaLogDerivative, neg_div, ← logDeriv_apply, hsharplog, hdlog,
    logDeriv_apply]
  ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
