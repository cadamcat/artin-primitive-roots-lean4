import Mathlib

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

private theorem quadratic_binary_norm_cross {K G : Type*} [Field K] [CommGroup G]
    (w : Kˣ → G) (i : Kˣ) (hi : (i : K) ^ 2 = -1)
    (hsquare : ∀ a c, w (a * c ^ 2) = w a)
    (hbinary : ∀ (a b : Kˣ) (h : (a : K) + (b : K) ≠ 0),
      w a * w b = w (Units.mk0 _ h) * w (a * b / Units.mk0 _ h))
    (a b n : Kˣ) (x y : K) (hn : (n : K) = x ^ 2 - (a : K) * y ^ 2) :
    w (b * n) * w (a * b * n) = w b * w (a * b) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply n.ne_zero
      exact hn.trans (by simp [hx, hy])
    let yu : Kˣ := Units.mk0 y hy
    have hnu : n = a * (i * yu) ^ 2 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        mul_pow, hi, yu]
      rw [hn, hx]
      ring
    have hbn : w (b * n) = w (a * b) := by
      rw [hnu, show b * (a * (i * yu) ^ 2) = (a * b) * (i * yu) ^ 2 by ac_rfl]
      exact hsquare _ _
    have habn : w (a * b * n) = w b := by
      rw [hnu, show a * b * (a * (i * yu) ^ 2) = b * (a * i * yu) ^ 2 by
        simp only [pow_two]
        ac_rfl]
      exact hsquare _ _
    rw [hbn, habn, mul_comm]
  · by_cases hy : y = 0
    · let xu : Kˣ := Units.mk0 x hx
      have hnu : n = xu ^ 2 := by
        apply Units.ext
        simpa [xu, hy] using hn
      rw [hnu, hsquare, hsquare]
    · let xu : Kˣ := Units.mk0 x hx
      let yu : Kˣ := Units.mk0 y hy
      let X : Kˣ := b * xu ^ 2
      let Y : Kˣ := (a * b) * (i * yu) ^ 2
      have hsum : (X : K) + (Y : K) = ((b * n : Kˣ) : K) := by
        simp only [X, Y, xu, yu, Units.val_mul, Units.val_pow_eq_pow_val,
          Units.val_mk0, mul_pow, hi]
        rw [hn]
        ring
      have hsum0 : (X : K) + (Y : K) ≠ 0 := by
        rw [hsum]
        exact (b * n).ne_zero
      have hsumu : Units.mk0 _ hsum0 = b * n := by
        apply Units.ext
        exact hsum
      have hother : X * Y / (b * n) = (a * b * n) * (i * xu * yu / n) ^ 2 := by
        apply Units.ext
        simp only [X, Y, xu, yu, Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val, Units.val_mk0]
        field_simp [b.ne_zero, n.ne_zero]
      have hbin := hbinary X Y hsum0
      rw [hsumu, hother] at hbin
      simpa only [X, Y, hsquare] using hbin.symm

/-- The quadratic multiplicative defect is constant under multiplication by a nonzero
binary norm. All Gaussian identities are explicit hypotheses; no analytic comparison is
assumed. -/
theorem quadratic_defect_binary_norm_invariant {K G : Type*} [Field K] [CommGroup G]
    (w : Kˣ → G) (i : Kˣ) (hi : (i : K) ^ 2 = -1)
    (hsquare : ∀ a c, w (a * c ^ 2) = w a)
    (hsign : ∀ a, w a ^ 2 = 1)
    (hbinary : ∀ (a b : Kˣ) (h : (a : K) + (b : K) ≠ 0),
      w a * w b = w (Units.mk0 _ h) * w (a * b / Units.mk0 _ h))
    (a b n : Kˣ) (x y : K) (hn : (n : K) = x ^ 2 - (a : K) * y ^ 2) :
    w a * w (b * n) / w (a * (b * n)) = w a * w b / w (a * b) := by
  have hinv (t : Kˣ) : (w t)⁻¹ = w t := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hsign t
  have hc := quadratic_binary_norm_cross w i hi hsquare hbinary a b n x y hn
  simpa only [div_eq_mul_inv, hinv, mul_assoc] using
    congrArg (fun z : G => w a * z) hc

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
