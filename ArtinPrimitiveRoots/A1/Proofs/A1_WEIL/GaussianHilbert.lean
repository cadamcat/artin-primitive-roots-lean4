import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianBinary
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSign
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.NormCoset

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem complexRoot_injective (D : FieldData F) :
    Function.Injective (complexRoot D) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply D.σ0.injective
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hxy

private theorem hilbert_pow_left (H : HilbertData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) (n : ℕ) :
    H.hilb v (a ^ n) b = H.hilb v a b ^ n := by
  induction n with
  | zero =>
      simpa using H.sixth_power v 1 b ⟨1, by simp⟩
  | succ n ih =>
      rw [pow_succ, H.mul_left, ih, pow_succ]

private theorem quadratic_hilbert_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (c b : (v.adicCompletion F)ˣ) :
    complexRoot D (H.hilb v (c ^ 2) b) ^ 3 = 1 := by
  rw [← map_pow, ← hilbert_pow_left, ← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [H.sixth_power v (c ^ 6) b ⟨c, rfl⟩, map_one]

/-- Cubing the sextic Hilbert pairing has exactly the square subgroup as its radical.
This isolates the Hilbert nondegeneracy needed for the Gaussian comparison.
Guide: PROOFS.md:474–475; uses only the frozen Hilbert multiplicativity,
sixth-power vanishing, and nondegeneracy fields. -/
theorem quadratic_hilbert_trivial_iff_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    (∀ b, complexRoot D (H.hilb v a b) ^ 3 = 1) ↔
      ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2 := by
  constructor
  · intro ha
    have hcube : ∀ b, H.hilb v (a ^ 3) b = 1 := by
      intro b
      apply complexRoot_injective D
      rw [hilbert_pow_left, map_pow, map_one]
      exact ha b
    obtain ⟨c, hc⟩ := H.nondeg v (a ^ 3) hcube
    refine ⟨a ^ 2 / c ^ 3, ?_⟩
    calc
      a = a ^ 4 / a ^ 3 := by
        rw [show a ^ 4 = a * a ^ 3 from pow_succ' a 3]
        simp
      _ = (a ^ 2 / c ^ 3) ^ 2 := by
        rw [hc]
        simp only [div_pow, ← pow_mul, Nat.reduceMul]
  · rintro ⟨c, rfl⟩ b
    exact quadratic_hilbert_square D H v c b

private def quadraticHilbertLeft (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (b : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun a := complexRoot D (H.hilb v a b) ^ 3
  map_one' := by
    rw [H.sixth_power v 1 b ⟨1, by simp⟩, map_one, one_pow]
  map_mul' a a' := by rw [H.mul_left, map_mul, mul_pow]

private def quadraticHilbertRight (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun b := complexRoot D (H.hilb v a b) ^ 3
  map_one' := by
    have h1 := H.sixth_power v 1 a ⟨1, by simp⟩
    have h2 := H.skew v a 1
    rw [h1, mul_one] at h2
    rw [h2, map_one, one_pow]
  map_mul' b b' := by rw [H.mul_right, map_mul, mul_pow]

private theorem quadratic_hilbert_right_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a c : (v.adicCompletion F)ˣ) :
    quadraticHilbertRight D H v a (c ^ 2) = 1 := by
  change complexRoot D (H.hilb v a (c ^ 2)) ^ 3 = 1
  have h := congrArg (fun z : rootsOfUnity 6 F => complexRoot D z ^ 3)
    (H.skew v a (c ^ 2))
  simpa only [map_mul, mul_pow, quadratic_hilbert_square, map_one, one_pow,
    mul_one] using h

private theorem completion_square_neg_one (D : FieldData F) (v : FinPlace F) :
    ∃ i : (v.adicCompletion F)ˣ, (i : v.adicCompletion F) ^ 2 = -1 := by
  have h6 : D.ζ12 ^ 6 = -1 := by
    have hroot : IsPrimitiveRoot (D.ζ12 ^ 6) 2 := by
      simpa using D.hζ12.pow_of_dvd (by norm_num : (6 : ℕ) ≠ 0)
        (by norm_num : 6 ∣ 12)
    exact hroot.eq_neg_one_of_two_right
  have hz : D.ζ12 ^ 3 ≠ 0 :=
    pow_ne_zero 3 (D.hζ12.ne_zero (by norm_num))
  have hzv : algebraMap F (v.adicCompletion F) (D.ζ12 ^ 3) ≠ 0 :=
    (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hz
  refine ⟨Units.mk0 _ hzv, ?_⟩
  change (algebraMap F (v.adicCompletion F) (D.ζ12 ^ 3)) ^ 2 = -1
  rw [← map_pow, ← pow_mul, show 3 * 2 = 6 by rfl, h6, map_neg, map_one]

private theorem quadratic_hilbert_diagonal (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    quadraticHilbertRight D H v a a = 1 := by
  obtain ⟨i, hi⟩ := completion_square_neg_one D v
  let m : (v.adicCompletion F)ˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hm : m = i ^ 2 := by
    apply Units.ext
    exact hi.symm
  have hminus : quadraticHilbertRight D H v a m = 1 := by
    rw [hm]
    exact quadratic_hilbert_right_square D H v a i
  by_cases ha : (a : v.adicCompletion F) = 1
  · have hau : a = 1 := Units.ext ha
    rw [hau]
    exact (quadraticHilbertLeft D H v 1).map_one
  · have ht0 : (1 : v.adicCompletion F) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    let t : (v.adicCompletion F)ˣ := Units.mk0 _ ht0
    have ht : quadraticHilbertRight D H v a t = 1 := by
      change complexRoot D (H.hilb v a (Units.mk0 _ ht0)) ^ 3 = 1
      rw [H.steinberg, map_one, one_pow]
    have htinv0 : (1 : v.adicCompletion F) - (a⁻¹ : (v.adicCompletion F)ˣ) ≠ 0 := by
      intro h
      apply ha
      have hval : (a : v.adicCompletion F)⁻¹ = 1 := by
        simpa only [Units.val_inv_eq_inv_val] using (sub_eq_zero.mp h).symm
      exact inv_eq_one.mp hval
    let ti : (v.adicCompletion F)ˣ := Units.mk0 _ htinv0
    have hti : quadraticHilbertLeft D H v ti (a⁻¹) = 1 := by
      change complexRoot D (H.hilb v (a⁻¹) (Units.mk0 _ htinv0)) ^ 3 = 1
      rw [H.steinberg, map_one, one_pow]
    rw [map_inv] at hti
    have hti' : quadraticHilbertRight D H v a ti = 1 := inv_eq_one.mp hti
    have htiu : ti = m * t / a := by
      apply Units.ext
      simp only [ti, m, t, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_mk0, Units.val_inv_eq_inv_val]
      field_simp [a.ne_zero]
      ring
    rw [htiu, map_div, map_mul, hminus, ht, one_mul, one_div] at hti'
    exact inv_eq_one.mp hti'

/-- The quadratic Hilbert character is trivial on every nonzero binary quadratic norm.
Guide: PROOFS.md:474–475. The proof uses only the supplied Hilbert laws and the square
root of -1 supplied by D; it needs no local norm-index or Gaussian comparison theorem. -/
theorem quadratic_hilbert_binary_norm_eq_one (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a n : (v.adicCompletion F)ˣ) (x y : v.adicCompletion F)
    (hn : (n : v.adicCompletion F) = x ^ 2 - (a : v.adicCompletion F) * y ^ 2) :
    complexRoot D (H.hilb v a n) ^ 3 = 1 := by
  change quadraticHilbertRight D H v a n = 1
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx
      apply n.ne_zero
      exact hn.trans (by simp [hx, hy])
    have hnu : n = (Units.mk0 x hx) ^ 2 := by
      apply Units.ext
      simpa [hy] using hn
    rw [hnu]
    exact quadratic_hilbert_right_square D H v a _
  · by_cases hx : x = 0
    · obtain ⟨i, hi⟩ := completion_square_neg_one D v
      let yu : (v.adicCompletion F)ˣ := Units.mk0 y hy
      have hnu : n = a * (i * yu) ^ 2 := by
        apply Units.ext
        simp only [yu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
          mul_pow, hi]
        rw [hn, hx]
        ring
      rw [hnu, map_mul, quadratic_hilbert_right_square, mul_one]
      exact quadratic_hilbert_diagonal D H v a
    · let xu : (v.adicCompletion F)ˣ := Units.mk0 x hx
      let yu : (v.adicCompletion F)ˣ := Units.mk0 y hy
      let t : (v.adicCompletion F)ˣ := a * (yu / xu) ^ 2
      have hdiff : (1 : v.adicCompletion F) - t = (n : v.adicCompletion F) / x ^ 2 := by
        simp only [t, xu, yu, Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val, Units.val_mk0]
        rw [hn]
        field_simp [hx]
      have ht0 : (1 : v.adicCompletion F) - t ≠ 0 := by
        rw [hdiff]
        exact div_ne_zero n.ne_zero (pow_ne_zero 2 hx)
      let r : (v.adicCompletion F)ˣ := Units.mk0 _ ht0
      have hnu : n = xu ^ 2 * r := by
        apply Units.ext
        simp only [xu, r, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
        rw [hdiff]
        field_simp [hx]
      have hstein : quadraticHilbertLeft D H v r t = 1 := by
        change complexRoot D (H.hilb v t (Units.mk0 _ ht0)) ^ 3 = 1
        rw [H.steinberg, map_one, one_pow]
      change quadraticHilbertLeft D H v r (a * (yu / xu) ^ 2) = 1 at hstein
      rw [map_mul] at hstein
      have hsquare : quadraticHilbertLeft D H v r ((yu / xu) ^ 2) = 1 :=
        quadratic_hilbert_square D H v (yu / xu) r
      rw [hsquare, mul_one] at hstein
      rw [hnu, map_mul, quadratic_hilbert_right_square, one_mul]
      exact hstein

/-- Identify the Gaussian multiplicative defect with the quadratic Hilbert symbol.
Guide: PROOFS.md:474–475. Uses: local_index_binary; local_index_sign; local_index_square; H.steinberg; H.nondeg; H.tame; H.product_formula. -/
theorem local_index_hilbert_defect (D : FieldData F) (A : AddCharData F) (H : HilbertData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v a * W.index v b =
      complexRoot D (H.hilb v a b) ^ 3 * W.index v (a * b) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
