import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- At each fixed group element, the normalized spherical section is analytic in its parameter. -/
theorem spherical_section_param_analytic
    (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (g : L.L) :
    AnalyticOnNhd ℂ (fun s => (spherical_section L τ T B hv s).choose g)
      {s | 0 < s.re} := by
  obtain ⟨x, y, ζ, k, hk, hg⟩ := iwasawa_tame L τ g
  have horder : g = L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y * k) := by
    rw [hg, ← L.z_central ζ (L.n (Multiplicative.ofAdd x))]
    simp only [mul_assoc]
  have hpow : AnalyticOnNhd ℂ
      (fun s : ℂ => (absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) {s | 0 < s.re} := by
    apply AnalyticOnNhd.cpow analyticOnNhd_const (analyticOnNhd_const.add analyticOnNhd_id)
    intro s hs
    exact Complex.ofReal_mem_slitPlane.mpr (absFin_pos (Units.ne_zero y))
  have hformula : (fun s => (spherical_section L τ T B hv s).choose g) =
      (fun s => ((ζ : ℂˣ) : ℂ) •
        ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (B.e 0)) := by
    funext s
    have hf := (spherical_section L τ T B hv s).choose_spec
    have hfk : (spherical_section L τ T B hv s).choose k = B.e 0 := by
      simpa only [one_mul, hf.2.1] using hf.2.2.1 1 k hk
    rw [horder, hf.1.2.1 ζ _, hf.1.1 x y k, hfk]
  rw [hformula]
  exact analyticOnNhd_const.smul (hpow.smul analyticOnNhd_const)

end ArtinPrimitiveRoots.A1.Theta
