import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- A regularization of the Euler product on the positive half-plane, with its residue
identified by the same real-sided limit used in resCprod.
Guide: sol-thin-thglobal/PROOFS.md:843–845 (zeta input: 758–780).
Uses FourierEulerHyp, supplied by the frozen cprod_eq_zeta_ratio and the existing
resLSeries_eq_zetaT0 helper at the Res boundary. Feeds theta_constantTerm. -/
theorem regularized_cprod_continuation (T0 : Finset (FinPlace F))
    (hEuler : FourierEulerHyp T0) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B {s | 0 < s.re} ∧
      B (1 / 6) = limUnder (𝓝[>] (1 / 6 : ℝ))
        (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)) ∧
      ∀ s : ℂ, 1 / 6 < s.re → B s = (s - 1 / 6) * cprod T0 s := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
