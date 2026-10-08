import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CharacterIntegralDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

/-- Taking a directional derivative multiplies a periodic exponential integral by the
negative of that direction's exponential phase. -/
theorem theta_periodic_exponential_directional_identity
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (Γ : AddSubgroup E) [Countable Γ] (Pd : Set E)
    (hPd : IsAddFundamentalDomain Γ Pd μ) (hm : MeasurableSet Pd)
    (hcompact : IsCompact (closure Pd)) (hfinite : μ Pd ≠ ⊤)
    (ℓ : E →L[ℝ] ℝ) (c : ℂ)
    (hchar : ∀ a : Γ, Complex.exp (c * (ℓ (a : E) : ℂ)) = 1)
    (f : E → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ a : Γ, ∀ x, f ((a : E) + x) = f x) (v : E) :
    (∫ x in Pd, fderiv ℝ f x v * Complex.exp (c * (ℓ x : ℂ)) ∂μ) =
      -(c * (ℓ v : ℂ)) *
        ∫ x in Pd, f x * Complex.exp (c * (ℓ x : ℂ)) ∂μ := by
  let χ : E → ℂ := fun x => Complex.exp (c * (ℓ x : ℂ))
  let J : ℂ := ∫ x in Pd, f x * χ x ∂μ
  let a : ℂ := -(c * (ℓ v : ℂ))
  have hχ : Continuous χ :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp ℓ.continuous))
  have hχadd (x y : E) : χ (x + y) = χ x * χ y := by
    dsimp only [χ]
    rw [map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  have hχper (z : Γ) : χ (z : E) = 1 := hchar z
  have hshift :
      (fun t : ℝ => ∫ x in Pd, f (x + t • v) * χ x ∂μ) =
        (fun t : ℝ => Complex.exp ((t : ℂ) * a) * J) := by
    funext t
    have heq : (χ (t • v))⁻¹ = Complex.exp ((t : ℂ) * a) := by
      dsimp only [χ, a]
      rw [← Complex.exp_neg]
      congr 1
      simp only [map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    calc
      _ = ∫ x in Pd, f (t • v + x) * χ x ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change f (x + t • v) * χ x = f (t • v + x) * χ x
          rw [add_comm x]
      _ = (χ (t • v))⁻¹ * J :=
        theta_periodic_character_integral_translate μ Γ Pd hPd χ hχadd hχper f hper
          (t • v)
      _ = _ := by rw [heq]
  have hscalar : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * a) * J) (a * J) 0 := by
    simpa only [id_eq, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero] using
      (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const a).cexp.mul_const J)
  have hintegral := (theta_character_integral_hasDerivAt μ Pd hm hcompact hfinite
    f hf χ hχ v).2
  rw [hshift] at hintegral
  simpa only [χ, a, J] using hintegral.unique hscalar

end ArtinPrimitiveRoots.Proofs.majorant_sol
