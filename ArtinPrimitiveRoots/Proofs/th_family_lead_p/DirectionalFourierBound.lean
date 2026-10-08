import ArtinPrimitiveRoots.Proofs.th_family_lead_p.IteratedDirectionalFourier

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

/-- Uniform bounds on the iterated derivative control the directional decay of a periodic
unit-character integral. -/
theorem theta_periodic_exponential_directional_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (Γ : AddSubgroup E) [Countable Γ] (Pd : Set E)
    (hPd : IsAddFundamentalDomain Γ Pd μ) (hm : MeasurableSet Pd)
    (hcompact : IsCompact (closure Pd)) (hfinite : μ Pd ≠ ⊤)
    (ℓ : E →L[ℝ] ℝ) (c : ℂ)
    (hchar : ∀ a : Γ, Complex.exp (c * (ℓ (a : E) : ℂ)) = 1)
    (hunit : ∀ x : E, ‖Complex.exp (c * (ℓ x : ℂ))‖ = 1)
    (f : E → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ a : Γ, ∀ x, f ((a : E) + x) = f x)
    (v : E) (N : ℕ) (C : ℝ)
    (hbound : ∀ x ∈ Pd, ‖iteratedFDeriv ℝ N f x‖ ≤ C) :
    ‖c * (ℓ v : ℂ)‖ ^ N *
        ‖∫ x in Pd, f x * Complex.exp (c * (ℓ x : ℂ)) ∂μ‖ ≤
      (μ Pd).toReal * C * ‖v‖ ^ N := by
  have hid := theta_periodic_exponential_iterated_identity μ Γ Pd hPd hm hcompact hfinite
    ℓ c hchar f hf hper v N
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hid
  simp only [norm_mul, norm_pow, norm_neg] at hnorm
  have hpoint (x : E) (hx : x ∈ Pd) :
      ‖iteratedFDeriv ℝ N f x (fun _ => v) * Complex.exp (c * (ℓ x : ℂ))‖ ≤
        C * ‖v‖ ^ N := by
    calc
      _ = ‖iteratedFDeriv ℝ N f x (fun _ => v)‖ := by rw [norm_mul, hunit, mul_one]
      _ ≤ ‖iteratedFDeriv ℝ N f x‖ * ‖v‖ ^ N := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ N f x).le_opNorm (fun _ => v)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound x hx) (pow_nonneg (norm_nonneg v) N)
  calc
    ‖c * (ℓ v : ℂ)‖ ^ N *
        ‖∫ x in Pd, f x * Complex.exp (c * (ℓ x : ℂ)) ∂μ‖ =
        ‖∫ x in Pd, iteratedFDeriv ℝ N f x (fun _ => v) *
          Complex.exp (c * (ℓ x : ℂ)) ∂μ‖ := by
      simpa only [norm_mul] using hnorm.symm
    _ ≤ (C * ‖v‖ ^ N) * μ.real Pd :=
      norm_setIntegral_le_of_norm_le_const hfinite.lt_top hpoint
    _ = (μ Pd).toReal * C * ‖v‖ ^ N := by dsimp only [Measure.real]; ring

end ArtinPrimitiveRoots.Proofs.majorant_sol
