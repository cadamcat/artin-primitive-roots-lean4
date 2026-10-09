import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.«TH-RES-ACTION».scalar_section_affine
import ArtinPrimitiveRoots.Theta.Proofs.«TH-RES-ACTION».scalar_section_translate

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- The Eisenstein series inherits linearity and right translation from
its scalar section on the common series ball. -/
theorem family_series_linear_translate (v0 : FinPlace F)
    (Fam Fam' Fam'' : AnalyticFamily P G μ) :
    ((∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v ∧
      (Fam''.sec s).f v = (Fam.sec s).f v) →
      ∀ c : ℂ, (∀ s, (Fam''.sec s).f v0 = (Fam.sec s).f v0 + c • (Fam'.sec s).f v0) →
        ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
          eisenstein P G (Fam''.sec s) g =
            eisenstein P G (Fam.sec s) g + c * eisenstein P G (Fam'.sec s) g) ∧
    (∀ h : (P.loc v0).L, (∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
      (∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0)) →
        ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
          eisenstein P G (Fam'.sec s) g = eisenstein P G (Fam.sec s) (g * P.emb v0 h)) := by
  constructor
  · intro hext c hlocal s hs g
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
      simpa [Complex.sub_re] using
        lt_of_le_of_lt (Complex.abs_re_le_norm (s - (5 / 2 : ℂ))) hnorm
    have hsre : 1 / 2 < s.re := by
      have := (abs_lt.mp hreal).1
      linarith
    have hC' : (Fam'.sec s).fC = (Fam.sec s).fC := by
      funext w
      rw [Fam'.fC_sph s w, Fam.fC_sph s w]
    have hC'' : (Fam''.sec s).fC = (Fam.sec s).fC := by
      funext w
      rw [Fam''.fC_sph s w, Fam.fC_sph s w]
    have hscalar := scalar_section_affine v0 (Fam.sec s) (Fam'.sec s)
      (Fam''.sec s) c (hext s) (hlocal s) hC' hC''
    have hsum := (eisenstein_summable P G hsre (Fam.sec s) g).of_norm
    have hsum' := (eisenstein_summable P G hsre (Fam'.sec s) g).of_norm
    unfold eisenstein
    rw [← tsum_mul_left, ← hsum.tsum_add (hsum'.mul_left c)]
    apply tsum_congr
    intro γ
    exact hscalar (P.tc.rat (Quotient.out γ) * g)
  · intro h hext hlocal s _hs g
    have hC : (Fam'.sec s).fC = (Fam.sec s).fC := by
      funext w
      rw [Fam'.fC_sph s w, Fam.fC_sph s w]
    have hscalar := scalar_section_translate v0 (Fam.sec s) (Fam'.sec s)
      h (hext s) (hlocal s) hC
    unfold eisenstein
    apply tsum_congr
    intro γ
    simpa only [mul_assoc] using hscalar (P.tc.rat (Quotient.out γ) * g)

end ArtinPrimitiveRoots.A1.Theta
