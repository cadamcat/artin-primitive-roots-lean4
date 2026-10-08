import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

/-- Coordinate derivatives of a smooth integer-periodic function are smooth and
integer-periodic, and agree with the derivatives on real coordinate rays. -/
theorem smooth_periodic_coordinate_derivative {d : Type*} [Fintype d] [DecidableEq d]
    (f : (d → ℝ) → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ (x : d → ℝ) (k : d → ℤ),
      f (x + fun j => (k j : ℝ)) = f x)
    (i : d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ))) ∧
    (∀ (x : d → ℝ) (k : d → ℤ),
      fderiv ℝ f (x + fun j => (k j : ℝ)) (Pi.single i (1 : ℝ)) =
        fderiv ℝ f x (Pi.single i (1 : ℝ))) ∧
    ∀ (x : d → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (x + s • Pi.single i (1 : ℝ)))
        (fderiv ℝ f (x + t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ))) t := by
  obtain ⟨hDiff, hDf⟩ := contDiff_infty_iff_fderiv.mp hf
  refine ⟨hDf.clm_apply contDiff_const, ?_, ?_⟩
  · intro x k
    have hshift : (fun y : d → ℝ => f (y + fun j => (k j : ℝ))) = f := by
      funext y
      exact hper y k
    calc
      fderiv ℝ f (x + fun j => (k j : ℝ)) (Pi.single i (1 : ℝ)) =
          fderiv ℝ (fun y : d → ℝ => f (y + fun j => (k j : ℝ))) x
            (Pi.single i (1 : ℝ)) := by rw [fderiv_comp_add_right]
      _ = fderiv ℝ f x (Pi.single i (1 : ℝ)) := by rw [hshift]
  · intro x t
    have hRay : HasDerivAt (fun s : ℝ => x + s • Pi.single i (1 : ℝ))
        (Pi.single i (1 : ℝ)) t := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ))).const_add x
    simpa only [Function.comp_def] using
      (hDiff (x + t • Pi.single i (1 : ℝ))).hasFDerivAt.comp_hasDerivAt t hRay

end ArtinPrimitiveRoots.Proofs.thsol_torusf
