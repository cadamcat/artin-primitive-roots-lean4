import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpLogDeriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The sharp logarithmic derivative reflects through the prefactor terms. -/
theorem sharp_functional_logderiv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s.im ≠ 0) (hxi : dedekindXi K s ≠ 0) :
    dedekindZetaLogDerivative K s =
      -dedekindZetaLogDerivative K (1 - s) +
        deriv (dedekindPrefactor K) s / dedekindPrefactor K s +
        deriv (dedekindPrefactor K) (1 - s) / dedekindPrefactor K (1 - s) := by
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hdiff : Differentiable ℂ (dedekindXi K) := hspec.1
  have hFE (z : ℂ) : dedekindXi K (1 - z) = dedekindXi K z := by
    simpa only [dedekindXi] using hspec.2.2.1 z
  have hfun : (fun z : ℂ => dedekindXi K (1 - z)) = dedekindXi K := funext hFE
  have hg : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (fun z : ℂ => dedekindXi K (1 - z))
      (-(deriv (dedekindXi K) (1 - s))) s := by
    simpa only [Function.comp_def, mul_neg_one] using
      (hdiff (1 - s)).hasDerivAt.comp s hg
  have hd : deriv (dedekindXi K) s = -(deriv (dedekindXi K) (1 - s)) :=
    (congrArg (fun g : ℂ → ℂ => deriv g s) hfun).symm.trans hcomp.deriv
  have hratio : deriv (dedekindXi K) s / dedekindXi K s =
      -(deriv (dedekindXi K) (1 - s) / dedekindXi K (1 - s)) := by
    rw [hd, hFE s, neg_div]
  have hs' : (1 - s).im ≠ 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using hs
  have hxi' : dedekindXi K (1 - s) ≠ 0 := by rwa [hFE s]
  have hs0 : s ≠ 0 := by
    intro h
    exact hs (by simp [h])
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have heq : s = 1 := sub_eq_zero.mp h
    exact hs (by simp [heq])
  have ht0 : 1 - s ≠ 0 := by
    intro h
    exact hs' (by simp [h])
  have ht1 : (1 - s) - 1 ≠ 0 := by
    intro h
    have heq : 1 - s = 1 := sub_eq_zero.mp h
    exact hs' (by simp [heq])
  have hr : (1 / s + 1 / (s - 1)) + (1 / (1 - s) + 1 / ((1 - s) - 1)) = (0 : ℂ) := by
    field_simp [hs0, hs1, ht0, ht1]
    <;> ring
  rw [(sharp_logderiv K hs hxi).2.2, (sharp_logderiv K hs' hxi').2.2, hratio]
  linear_combination hr

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
