import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DirectionalFourier
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

/-- Repeated directional differentiation raises the periodic exponential multiplier
to the derivative order. -/
theorem theta_periodic_exponential_iterated_identity
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (Γ : AddSubgroup E) [Countable Γ] (Pd : Set E)
    (hPd : IsAddFundamentalDomain Γ Pd μ) (hm : MeasurableSet Pd)
    (hcompact : IsCompact (closure Pd)) (hfinite : μ Pd ≠ ⊤)
    (ℓ : E →L[ℝ] ℝ) (c : ℂ)
    (hchar : ∀ a : Γ, Complex.exp (c * (ℓ (a : E) : ℂ)) = 1)
    (f : E → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ a : Γ, ∀ x, f ((a : E) + x) = f x) (v : E) (N : ℕ) :
    (∫ x in Pd, iteratedFDeriv ℝ N f x (fun _ => v) *
      Complex.exp (c * (ℓ x : ℂ)) ∂μ) =
      (-(c * (ℓ v : ℂ))) ^ N *
        ∫ x in Pd, f x * Complex.exp (c * (ℓ x : ℂ)) ∂μ := by
  let fv : ℕ → E → ℂ := fun m x => iteratedFDeriv ℝ m f x (fun _ => v)
  have hsucc (m : ℕ) (x : E) : fv (m + 1) x = fderiv ℝ (fv m) x v := by
    have hd := hf.differentiable_iteratedFDeriv (m := m)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m) x
    have heq := hd.iteratedFDeriv_succ_apply_left' (m := fun _ : Fin (m + 1) => v)
    have htail : Fin.tail (fun _ : Fin (m + 1) => v) = (fun _ : Fin m => v) := rfl
    rw [htail] at heq
    exact heq
  have hsm : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fv m) := by
    intro m
    induction m with
    | zero => simpa only [fv, iteratedFDeriv_zero_apply] using hf
    | succ m ih =>
      have heq : fv (m + 1) = fun x => fderiv ℝ (fv m) x v := funext (hsucc m)
      rw [heq]
      exact (ih.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
        contDiff_const
  have hperiod (m : ℕ) (a : Γ) (x : E) : fv m ((a : E) + x) = fv m x := by
    have hshift : (fun y => f ((a : E) + y)) = f := funext (hper a)
    dsimp only [fv]
    rw [← iteratedFDeriv_comp_add_left m (a : E) x, hshift]
  induction N with
  | zero => simp only [iteratedFDeriv_zero_apply, pow_zero, one_mul]
  | succ m ih =>
    calc
      _ = ∫ x in Pd, fderiv ℝ (fv m) x v * Complex.exp (c * (ℓ x : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change fv (m + 1) x * Complex.exp (c * (ℓ x : ℂ)) = _
          rw [hsucc]
      _ = -(c * (ℓ v : ℂ)) *
          ∫ x in Pd, fv m x * Complex.exp (c * (ℓ x : ℂ)) ∂μ :=
        theta_periodic_exponential_directional_identity μ Γ Pd hPd hm hcompact hfinite
          ℓ c hchar (fv m) (hsm m) (hperiod m) v
      _ = -(c * (ℓ v : ℂ)) * ((-(c * (ℓ v : ℂ))) ^ m *
          ∫ x in Pd, f x * Complex.exp (c * (ℓ x : ℂ)) ∂μ) :=
        congrArg (fun z : ℂ => -(c * (ℓ v : ℂ)) * z) ih
      _ = _ := by rw [pow_succ']; ring

end ArtinPrimitiveRoots.Proofs.majorant_sol
