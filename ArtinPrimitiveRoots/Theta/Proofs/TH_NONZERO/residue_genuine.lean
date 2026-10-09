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

/-- Genuineness of the convergent Eisenstein series passes to its residue by
analytic uniqueness. -/
theorem residue_genuine {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) :
    ∀ ζ g, C.theta (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * C.theta g := by
  intro ζ g
  let q : ℂ := ((ζ : ℂˣ) : ℂ)
  have hscaled : AnalyticOnNhd ℂ (fun s => q * C.E s g)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
    exact analyticOnNhd_const.mul (C.E_analytic g)
  have hseries : Set.EqOn (fun s => C.E s (P.tc.z ζ * g))
      (fun s => q * C.E s g) (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
    intro s hs
    change C.E s (P.tc.z ζ * g) = q * C.E s g
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
      simpa [Complex.sub_re] using
        lt_of_le_of_lt (Complex.abs_re_le_norm (s - (5 / 2 : ℂ))) hnorm
    have hsre : 1 / 2 < s.re := by
      have := (abs_lt.mp hreal).1
      linarith
    rw [C.E_series s hs, C.E_series s hs]
    exact (eisenstein_automorphic P G hsre (Fam.sec s)).2.1 ζ g
  have hlaurent : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
      Ψ (1 / 6) = q * C.theta g ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * (q * C.E s g) := by
    obtain ⟨Ψ, hΨ, hcenter, hvalue⟩ := C.laurent g
    refine ⟨fun s => q * Ψ s, analyticOnNhd_const.mul hΨ, ?_, ?_⟩
    · change q * Ψ (1 / 6) = q * C.theta g
      rw [hcenter]
    · intro s hs hne
      change q * Ψ s = (s - 1 / 6) * (q * C.E s g)
      rw [hvalue s hs hne]
      ring
  exact (continuedEis_component_unique C.ε C.ε C.ε_pos C.ε_pos
    (fun s => C.E s (P.tc.z ζ * g)) (fun s => q * C.E s g)
    (C.theta (P.tc.z ζ * g)) (q * C.theta g)
    (C.E_analytic _) hscaled hseries (C.laurent _) hlaurent).2

end ArtinPrimitiveRoots.A1.Theta
