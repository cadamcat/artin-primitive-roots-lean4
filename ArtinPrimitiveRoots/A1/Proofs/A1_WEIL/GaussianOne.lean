import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The normalized ratio at 1 is 1.
Uses: local_absolute_value; W.integral_ne_zero. -/
theorem local_index_one (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) : W.index v 1 = 1 := by
  ext
  change (((absFin v ((1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1) /
      quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1)) = (1 : ℂ)
  have h1 : absFin v ((1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change absFin v 1 = 1
    exact (local_absolute_value v).1
  rw [h1, Real.one_rpow, Complex.ofReal_one, one_mul]
  exact div_self (W.integral_ne_zero v 1)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
