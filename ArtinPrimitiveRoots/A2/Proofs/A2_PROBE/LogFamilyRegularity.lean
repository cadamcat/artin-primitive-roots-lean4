import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open scoped Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- A continuous parameter factor times a smooth real/archimedean family is smooth in the
real variable, with every real derivative jointly continuous in all parameters. The parameter
factor needs only a topology, so finite completions can be treated separately from calculus. -/
theorem separated_family_regular {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : X → ℂ) (hc : Continuous c) (f : ℝ × E → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    (∀ x : X × E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => c x.1 * f (u, x.2))) ∧
      ∀ n : ℕ, Continuous (fun p : ℝ × (X × E) =>
        iteratedDeriv n (fun u : ℝ => c p.2.1 * f (u, p.2.2)) p.1) := by
  have hpartial : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × E => iteratedDeriv n (fun u : ℝ => f (u, p.2)) p.1) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_zero, Prod.mk.eta] using hf
    | succ n ih =>
      let g : ℝ × E → ℂ := fun p => iteratedDeriv n (fun u : ℝ => f (u, p.2)) p.1
      have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := ih
      have hgd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
        hg.fderiv_right (by simp)
      have happly : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × E => (fderiv ℝ g p) (1, 0)) :=
        hgd.clm_apply contDiff_const
      convert happly using 1
      funext p
      rw [iteratedDeriv_succ]
      have hs : HasDerivAt (fun u : ℝ => (u, p.2)) (1, 0) p.1 :=
        (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
      have hd := (hg.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1 hs
      exact hd.deriv
  constructor
  · intro x
    have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => f (u, x.2)) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    exact contDiff_const.mul hslice
  · intro n
    have hfinite : Continuous (fun p : ℝ × (X × E) => c p.2.1) :=
      hc.comp (continuous_fst.comp continuous_snd)
    have harch : Continuous (fun p : ℝ × (X × E) =>
        iteratedDeriv n (fun u : ℝ => f (u, p.2.2)) p.1) :=
      (hpartial n).continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    convert hfinite.mul harch using 1
    funext p
    exact iteratedDeriv_const_mul_field (c p.2.1) (fun u : ℝ => f (u, p.2.2))

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
