import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.PeriodicTorusLift
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.SmoothPeriodicCoordinate

set_option autoImplicit false

open AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

/-- A smooth periodic coordinate function and its coordinate derivative descend
to continuous torus functions with the expected derivatives on circle slices. -/
theorem periodic_torus_derivative_lift {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ),
      f (x + fun j => (k j : ℝ)) = f x)
    (i : Fin (n + 1)) :
    ∃ (F F' : C(UnitAddTorus (Fin (n + 1)), ℂ)),
      (∀ x : Fin (n + 1) → ℝ,
        F (fun j => (x j : UnitAddCircle)) = f x) ∧
      (∀ x : Fin (n + 1) → ℝ,
        F' (fun j => (x j : UnitAddCircle)) = fderiv ℝ f x (Pi.single i (1 : ℝ))) ∧
      ∀ (z : UnitAddTorus (Fin n)) (t : ℝ),
        HasDerivAt (fun s : ℝ => F (i.insertNth (s : UnitAddCircle) z))
          (F' (i.insertNth (t : UnitAddCircle) z)) t := by
  obtain ⟨hdf, hper_df, hRay⟩ := smooth_periodic_coordinate_derivative f hf hper i
  obtain ⟨F, hF⟩ := periodic_torus_lift f hf.continuous hper
  obtain ⟨F', hF'⟩ := periodic_torus_lift
    (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ))) hdf.continuous hper_df
  refine ⟨F, F', hF, hF', ?_⟩
  intro z t
  let a : Fin n → ℝ := fun j => (AddCircle.equivIco (1 : ℝ) 0 (z j) : ℝ)
  let x : Fin (n + 1) → ℝ := i.insertNth (0 : ℝ) a
  have hcoord (s : ℝ) :
      (fun j : Fin (n + 1) =>
        ((x + s • Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j : UnitAddCircle)) =
        i.insertNth (s : UnitAddCircle) z := by
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · intro j
      simp only [Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (Fin.succAbove_ne i j), smul_zero, add_zero,
        x, Fin.insertNth_apply_succAbove]
      exact AddCircle.coe_equivIco
  have hfun : (fun s : ℝ => F (i.insertNth (s : UnitAddCircle) z)) =
      (fun s : ℝ => f (x + s • Pi.single i (1 : ℝ))) := by
    funext s
    rw [← hcoord s, hF]
  have hderiv : F' (i.insertNth (t : UnitAddCircle) z) =
      fderiv ℝ f (x + t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
    rw [← hcoord t, hF']
  rw [hfun, hderiv]
  exact hRay x t

end ArtinPrimitiveRoots.Proofs.thsol_torusf
