import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Square-class invariance of the normalized quadratic index.
Uses: stable_value_square_scale; local_absolute_value; positive real rpow. -/
theorem local_index_square (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v (a * b ^ 2) = W.index v a := by
  have ha : 0 < absFin v (a : v.adicCompletion F) :=
    (local_absolute_value v).2.1 a
  have hb : 0 < absFin v (b : v.adicCompletion F) :=
    (local_absolute_value v).2.1 b
  have habs :
      absFin v ((a * b ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        absFin v (a : v.adicCompletion F) * absFin v (b : v.adicCompletion F) ^ 2 := by
    calc
      absFin v ((a * b ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          absFin v (a : v.adicCompletion F) * absFin v ((b ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
        (local_absolute_value v).2.2 a (b ^ 2)
      _ = absFin v (a : v.adicCompletion F) * absFin v (b : v.adicCompletion F) ^ 2 := by
        have hbb := (local_absolute_value v).2.2 b b
        simpa [pow_two] using congrArg (fun x : ℝ => absFin v (a : v.adicCompletion F) * x) hbb
  have hpow :
      absFin v ((a * b ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ (1 / 2 : ℝ) =
        absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) * absFin v (b : v.adicCompletion F) := by
    rw [habs, Real.mul_rpow ha.le (sq_nonneg _)]
    rw [← Real.rpow_natCast_mul hb.le 2 (1 / 2 : ℝ)]
    norm_num
  have hpowC :
      ((absFin v ((a * b ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^
          (1 / 2 : ℝ) : ℝ) : ℂ) * (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ =
        ((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hpow]
    apply congrArg (fun x : ℝ => (x : ℂ))
    rw [mul_assoc, mul_inv_cancel₀ hb.ne']
    simp
  have hscale :
      quadraticIntegral A v (W.measure v) (a * b ^ 2) (W.cutoff v (a * b ^ 2)) =
        (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ *
          quadraticIntegral A v (W.measure v) a (W.cutoff v a) := by
    simpa [LocalGaussianData.stableValue] using stable_value_square_scale D A W v a b
  apply Units.ext
  simp only [LocalGaussianData.index, Units.val_mk0]
  rw [hscale, ← mul_assoc, hpowC]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
