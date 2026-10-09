import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_unique

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rational left invariance of the Eisenstein series passes to its residue
by scalar analytic uniqueness. -/
theorem residue_automorphic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) :
    ∀ γ g, C.theta (P.tc.rat γ * g) = C.theta g := by
  intro γ g
  have hseries : Set.EqOn (fun s => C.E s (P.tc.rat γ * g))
      (fun s => C.E s g) (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
    intro s hs
    change C.E s (P.tc.rat γ * g) = C.E s g
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
      simpa [Complex.sub_re] using
        lt_of_le_of_lt (Complex.abs_re_le_norm (s - (5 / 2 : ℂ))) hnorm
    have hsre : 1 / 2 < s.re := by
      have := (abs_lt.mp hreal).1
      linarith
    rw [C.E_series s hs, C.E_series s hs]
    exact (eisenstein_automorphic P G hsre (Fam.sec s)).1 γ g
  exact (continuedEis_component_unique C.ε C.ε C.ε_pos C.ε_pos
    (fun s => C.E s (P.tc.rat γ * g)) (fun s => C.E s g)
    (C.theta (P.tc.rat γ * g)) (C.theta g)
    (C.E_analytic _) (C.E_analytic _) hseries (C.laurent _) (C.laurent _)).2

end ArtinPrimitiveRoots.A1.Theta
