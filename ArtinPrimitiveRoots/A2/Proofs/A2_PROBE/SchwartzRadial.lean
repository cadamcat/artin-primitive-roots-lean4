import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex

set_option autoImplicit false

open LineDeriv
open scoped RealInnerProductSpace

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

private def schwartzEuler (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℂ) •
    (SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.re : ℂ)) (∂_{(1 : ℂ)} f) +
      SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.im : ℂ)) (∂_{Complex.I} f))

private def schwartzRadialIter : ℕ → SchwartzMap ℂ ℂ → SchwartzMap ℂ ℂ
  | 0, f => f
  | n + 1, f => schwartzEuler (schwartzRadialIter n f)

/-- Every logarithmic radial derivative of a complex Schwartz function is Schwartz. -/
theorem normDeriv_schwartz (f : SchwartzMap ℂ ℂ) (j : ℕ) :
    ∃ g : SchwartzMap ℂ ℂ, ∀ z : ℂ, A1.normDeriv j f z = g z := by
  have hre : (fun z : ℂ => (z.re : ℂ)).HasTemperateGrowth := by fun_prop
  have him : (fun z : ℂ => (z.im : ℂ)).HasTemperateGrowth := by fun_prop
  have heuler (g : SchwartzMap ℂ ℂ) (z : ℂ) :
      schwartzEuler g z = (1 / 2 : ℂ) * fderiv ℝ g z z := by
    have hz : (z.re : ℝ) • (1 : ℂ) + z.im • Complex.I = z := by
      apply Complex.ext <;> simp
    change (1 / 2 : ℂ) *
      (SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.re : ℂ)) (∂_{(1 : ℂ)} g) z +
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.im : ℂ)) (∂_{Complex.I} g) z) = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hre,
      SchwartzMap.smulLeftCLM_apply_apply him,
      SchwartzMap.lineDerivOp_apply_eq_fderiv (1 : ℂ) g z,
      SchwartzMap.lineDerivOp_apply_eq_fderiv Complex.I g z]
    have hlin : fderiv ℝ g z z =
        z.re • fderiv ℝ g z 1 + z.im • fderiv ℝ g z Complex.I := by
      calc
        fderiv ℝ g z z = fderiv ℝ g z ((z.re : ℝ) • (1 : ℂ) + z.im • Complex.I) :=
          by rw [hz]
        _ = _ := by rw [map_add, map_smul, map_smul]
    rw [hlin]
    change (1 / 2 : ℂ) * ((z.re : ℂ) * fderiv ℝ g z 1 +
        (z.im : ℂ) * fderiv ℝ g z Complex.I) = _
    rw [Complex.real_smul, Complex.real_smul]
  have hexp (t : ℝ) :
      HasDerivAt (fun u : ℝ => (Real.exp (u / 2) : ℂ))
        ((Real.exp (t / 2) / 2 : ℝ) : ℂ) t := by
    have hdiv : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t := by
      convert (hasDerivAt_id t).div_const 2 using 1 <;> simp
    have hreal : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
        (Real.exp (t / 2) / 2) t := by
      convert (Real.hasDerivAt_exp (t / 2)).comp t hdiv using 1
      · funext u
        simp only [Function.comp_apply]
      · ring
    exact hreal.ofReal_comp
  have hchain (g : SchwartzMap ℂ ℂ) (z : ℂ) (t : ℝ) :
      deriv (fun u : ℝ => g ((Real.exp (u / 2) : ℂ) * z)) t =
        schwartzEuler g ((Real.exp (t / 2) : ℂ) * z) := by
    let y : ℂ := (Real.exp (t / 2) : ℂ) * z
    have hφ := (hexp t).mul_const z
    have hg : HasFDerivAt (fun w : ℂ => g w) (fderiv ℝ g y) y :=
      g.differentiableAt.hasFDerivAt
    have hcomp := hg.comp t hφ.hasFDerivAt
    have hder : deriv (fun u : ℝ => g ((Real.exp (u / 2) : ℂ) * z)) t =
        fderiv ℝ g y (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) := by
      simpa [y, Function.comp_def] using hcomp.hasDerivAt.deriv
    rw [hder, heuler]
    have hdir : (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) = (1 / 2 : ℝ) • y := by
      dsimp [y]
      push_cast
      ring
    rw [hdir, map_smul]
    change ((1 / 2 : ℝ) : ℂ) * fderiv ℝ g y y =
        (1 / 2 : ℂ) * fderiv ℝ g y y
    push_cast
    ring
  have hiter (n : ℕ) (z : ℂ) (t : ℝ) :
      iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
        schwartzRadialIter n f ((Real.exp (t / 2) : ℂ) * z) := by
    induction n generalizing t with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) =
          fun u => schwartzRadialIter n f ((Real.exp (u / 2) : ℂ) * z) := by
        funext u
        exact ih u
      rw [hfun]
      simpa [schwartzRadialIter] using hchain (schwartzRadialIter n f) z t
  refine ⟨schwartzRadialIter j f, ?_⟩
  intro z
  unfold A1.normDeriv
  simpa using hiter j z 0

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
