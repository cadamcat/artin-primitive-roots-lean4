import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianModulus

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Unit modulus of the normalized ratio.
Uses: stable_quadratic_integral_modulus; W.stable; local_absolute_value. -/
theorem local_index_norm (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : ‖((W.index v a : ℂˣ) : ℂ)‖ = 1 := by
  let q : ℝ := absFin v (a : v.adicCompletion F)
  let I : ℂ := quadraticIntegral A v (W.measure v) a (W.cutoff v a)
  let J : ℂ := quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1)
  have hq : 0 < q := by
    exact (local_absolute_value v).2.1 a
  have hJ : J ≠ 0 := W.integral_ne_zero v 1
  have hstabA : StabilizesAt A v (W.measure v) a (W.cutoff v a) := by
    intro M hM
    exact W.stable v a M hM
  have hstab1 : StabilizesAt A v (W.measure v) 1 (W.cutoff v 1) := by
    intro M hM
    exact W.stable v 1 M hM
  have hmodulus := stable_quadratic_integral_modulus A v (W.measure v) (W.isHaar v)
    (local_character_regular D A v) a (W.cutoff v a) (W.cutoff v 1) hstabA hstab1
  have hmod : q * ‖I‖ ^ 2 = ‖J‖ ^ 2 := by
    simpa [q, I, J] using hmodulus
  have hqpow_nonneg : 0 ≤ q ^ (1 / 2 : ℝ) := Real.rpow_nonneg hq.le _
  have hqpow_nonneg' : 0 ≤ absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) := by
    simpa [q] using hqpow_nonneg
  have hqpow_sq : (q ^ (1 / 2 : ℝ)) ^ 2 = q := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hq.le
  have hprod_nonneg : 0 ≤ q ^ (1 / 2 : ℝ) * ‖I‖ :=
    mul_nonneg hqpow_nonneg (norm_nonneg I)
  have hprod_sq : (q ^ (1 / 2 : ℝ) * ‖I‖) ^ 2 = ‖J‖ ^ 2 := by
    calc
      (q ^ (1 / 2 : ℝ) * ‖I‖) ^ 2 = (q ^ (1 / 2 : ℝ)) ^ 2 * ‖I‖ ^ 2 := by ring
      _ = q * ‖I‖ ^ 2 := by rw [hqpow_sq]
      _ = ‖J‖ ^ 2 := hmod
  have hprod : q ^ (1 / 2 : ℝ) * ‖I‖ = ‖J‖ :=
    (sq_eq_sq₀ hprod_nonneg (norm_nonneg J)).mp hprod_sq
  have hJnorm : 0 < ‖J‖ := norm_pos_iff.mpr hJ
  have hnormIndex :
      ‖((W.index v a : ℂˣ) : ℂ)‖ = q ^ (1 / 2 : ℝ) * ‖I‖ / ‖J‖ := by
    simp only [LocalGaussianData.index, Units.val_mk0, norm_div, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg hqpow_nonneg']
  rw [hnormIndex, hprod, div_self hJnorm.ne']

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
