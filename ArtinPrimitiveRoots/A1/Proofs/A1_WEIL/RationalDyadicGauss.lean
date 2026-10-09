import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def finZModEquiv {n : ℕ} [NeZero n] : Fin n ≃ ZMod n :=
  Equiv.ofBijective (fun i : Fin n => (i.val : ZMod n)) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hval := congrArg ZMod.val hij
      simpa [ZMod.val_natCast_of_lt i.is_lt, ZMod.val_natCast_of_lt j.is_lt] using hval
    · intro z
      exact ⟨⟨z.val, z.val_lt⟩, ZMod.natCast_zmod_val z⟩
  )

private theorem zmod_sum_eq_fin {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    (∑ x : ZMod n, f x) = ∑ x : Fin n, f (x.val : ZMod n) := by
  exact (Equiv.sum_comp finZModEquiv f).symm

/-- The two actual dyadic finite sums needed for the valuation-parity formula.
Guide: PROOFS.md:482–485. Uses: ZMod.stdAddChar_coe; finite enumeration modulo 4 and 8. -/
theorem rational_dyadic_gauss_sums (u : ℕ) (hu : Odd u) :
    (∑ x : ZMod 4, ZMod.stdAddChar ((u : ZMod 4) * x ^ 2)) = 2 * (1 + Complex.I ^ u) ∧
    (∑ x : ZMod 8, ZMod.stdAddChar ((u : ZMod 8) * x ^ 2)) =
      4 * Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
  constructor
  · have hchar : ZMod.stdAddChar (u : ZMod 4) = Complex.I ^ u := by
      calc
        ZMod.stdAddChar (u : ZMod 4) = ZMod.stdAddChar ((u : ℤ) : ZMod 4) := by norm_cast
        _ = Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) / 4) :=
          ZMod.stdAddChar_coe (N := 4) (u : ℤ)
        _ = Complex.I ^ u := by
          rw [show 2 * Real.pi * Complex.I * (u : ℂ) / 4 =
            (u : ℂ) * (Real.pi / 2 * Complex.I) by push_cast; ring,
            Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
    rw [zmod_sum_eq_fin]
    rw [Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl]
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    have h0 : ZMod.stdAddChar ((u : ZMod 4) * (0 : ZMod 4) ^ 2) = 1 := by simp
    have h1 : ZMod.stdAddChar ((u : ZMod 4) * (1 : ZMod 4) ^ 2) = Complex.I ^ u := by
      simpa using hchar
    have h2 : ZMod.stdAddChar ((u : ZMod 4) * (2 : ZMod 4) ^ 2) = 1 := by
      rw [show (2 : ZMod 4) ^ 2 = 4 by norm_num,
        show (4 : ZMod 4) = 0 by decide,
        mul_zero]
      simp
    have h3 : ZMod.stdAddChar ((u : ZMod 4) * (3 : ZMod 4) ^ 2) = Complex.I ^ u := by
      rw [show (3 : ZMod 4) ^ 2 = (9 : ZMod 4) by norm_num,
        show (9 : ZMod 4) = 1 by decide,
        mul_one]
      exact hchar
    rw [h0, h1, h2, h3]
    ring
  · have hchar₁ : ZMod.stdAddChar (u : ZMod 8) =
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
      calc
        ZMod.stdAddChar (u : ZMod 8) = ZMod.stdAddChar ((u : ℤ) : ZMod 8) := by norm_cast
        _ = Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) / 8) :=
          ZMod.stdAddChar_coe (N := 8) (u : ℤ)
        _ = _ := by congr 1 <;> push_cast <;> ring
    have hchar₄ : ZMod.stdAddChar ((4 * u : ℕ) : ZMod 8) = -1 := by
      rw [show ((4 * u : ℕ) : ZMod 8) = 4 • (u : ZMod 8) by
        simp [nsmul_eq_mul, Nat.cast_mul]]
      rw [AddChar.map_nsmul_eq_pow, hchar₁]
      calc
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) ^ 4 =
            Complex.exp ((u : ℂ) * (Real.pi * Complex.I)) := by
          rw [← Complex.exp_nat_mul]
          congr 1
          push_cast
          ring
        _ = Complex.exp (Real.pi * Complex.I) ^ u := by rw [Complex.exp_nat_mul]
        _ = -1 := by rw [Complex.exp_pi_mul_I, hu.neg_one_pow]
    rw [zmod_sum_eq_fin]
    rw [Fin.sum_univ_eight]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 8) : ℕ) = 3 from rfl,
      show ((4 : Fin 8) : ℕ) = 4 from rfl,
      show ((5 : Fin 8) : ℕ) = 5 from rfl,
      show ((6 : Fin 8) : ℕ) = 6 from rfl,
      show ((7 : Fin 8) : ℕ) = 7 from rfl]
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    have h0 : ZMod.stdAddChar ((u : ZMod 8) * (0 : ZMod 8) ^ 2) = 1 := by simp
    have h1 : ZMod.stdAddChar ((u : ZMod 8) * (1 : ZMod 8) ^ 2) =
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by simpa using hchar₁
    have h2 : ZMod.stdAddChar ((u : ZMod 8) * (2 : ZMod 8) ^ 2) = -1 := by
      rw [show (2 : ZMod 8) ^ 2 = 4 by norm_num]
      convert hchar₄ using 1 <;> push_cast <;> ring
    have h3 : ZMod.stdAddChar ((u : ZMod 8) * (3 : ZMod 8) ^ 2) =
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
      rw [show (3 : ZMod 8) ^ 2 = (9 : ZMod 8) by norm_num,
        show (9 : ZMod 8) = 1 by decide,
        mul_one]
      exact hchar₁
    have h4 : ZMod.stdAddChar ((u : ZMod 8) * (4 : ZMod 8) ^ 2) = 1 := by
      rw [show (4 : ZMod 8) ^ 2 = (16 : ZMod 8) by norm_num,
        show (16 : ZMod 8) = 0 by decide,
        mul_zero]
      simp
    have h5 : ZMod.stdAddChar ((u : ZMod 8) * (5 : ZMod 8) ^ 2) =
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
      rw [show (5 : ZMod 8) ^ 2 = (25 : ZMod 8) by norm_num,
        show (25 : ZMod 8) = 1 by decide,
        mul_one]
      exact hchar₁
    have h6 : ZMod.stdAddChar ((u : ZMod 8) * (6 : ZMod 8) ^ 2) = -1 := by
      rw [show (6 : ZMod 8) ^ 2 = (36 : ZMod 8) by norm_num,
        show (36 : ZMod 8) = 4 by decide]
      convert hchar₄ using 1 <;> push_cast <;> ring
    have h7 : ZMod.stdAddChar ((u : ZMod 8) * (7 : ZMod 8) ^ 2) =
        Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
      rw [show (7 : ZMod 8) ^ 2 = (49 : ZMod 8) by norm_num,
        show (49 : ZMod 8) = 1 by decide,
        mul_one]
      exact hchar₁
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    ring

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
