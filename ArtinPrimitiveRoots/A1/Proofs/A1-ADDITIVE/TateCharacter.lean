import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {p : ℕ} [Fact p.Prime]

/-- Every p-adic class modulo the integers has a p-power fractional representative. -/
theorem padic_fraction_representative (x : ℚ_[p]) :
    ∃ n : ℕ, ∃ a : ℤ, ‖x - (a : ℚ_[p]) / (p : ℚ_[p]) ^ n‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · exact ⟨0, 0, by simpa using hx⟩
  have hp : p.Prime := Fact.out
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hx0 : x ≠ 0 := by
    intro h0
    exact hx (by simp [h0])
  let n : ℕ := (-x.valuation).toNat
  have hn : (n : ℤ) = -x.valuation := by
    dsimp [n]
    apply Int.toNat_of_nonneg
    rw [Right.nonneg_neg_iff]
    rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
    exact hx.le
  have hyNorm : ‖x * (p : ℚ_[p]) ^ n‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx0,
      ← zpow_add', hn, neg_neg, neg_add_cancel, zpow_zero]
    exact Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero)
  let y : ℤ_[p] := ⟨x * (p : ℚ_[p]) ^ n, hyNorm.le⟩
  refine ⟨n, (y.appr n : ℤ), ?_⟩
  have happ : ‖y - (y.appr n : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr (PadicInt.appr_spec n y)
  have hcast : ((y - (y.appr n : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
      x * (p : ℚ_[p]) ^ n - (y.appr n : ℚ_[p]) := by
    rfl
  have hdiv : x - ((y.appr n : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ n =
      ((y - (y.appr n : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ n := by
    rw [hcast]
    push_cast
    field_simp
  rw [hdiv, norm_div, ← PadicInt.norm_def, Padic.norm_p_pow]
  exact (div_le_one (zpow_pos (Nat.cast_pos.mpr hp.pos) _)).mpr happ

/-- The Tate exponential depends only on the class modulo the p-adic integers. -/
theorem padic_fraction_congr_exp (m n : ℕ) (a b : ℤ)
    (h : ‖(a : ℚ_[p]) / (p : ℚ_[p]) ^ m -
      (b : ℚ_[p]) / (p : ℚ_[p]) ^ n‖ ≤ 1) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (p : ℂ) ^ m) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (p : ℂ) ^ n) := by
  classical
  have hp : p.Prime := Fact.out
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hsame (i : ℕ) (A B : ℤ)
      (hI : ‖(A : ℚ_[p]) / (p : ℚ_[p]) ^ i -
        (B : ℚ_[p]) / (p : ℚ_[p]) ^ i‖ ≤ 1) :
      Complex.exp (2 * Real.pi * Complex.I * (A : ℂ) / (p : ℂ) ^ i) =
        Complex.exp (2 * Real.pi * Complex.I * (B : ℂ) / (p : ℂ) ^ i) := by
    have hmul : ((A : ℚ_[p]) / (p : ℚ_[p]) ^ i -
        (B : ℚ_[p]) / (p : ℚ_[p]) ^ i) * (p : ℚ_[p]) ^ i =
        ((A - B : ℤ) : ℚ_[p]) := by
      push_cast
      field_simp [hpQ]
    have hnorm : ‖((A - B : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
      rw [← hmul, norm_mul]
      simpa only [Padic.norm_p_pow, one_mul] using
        mul_le_mul_of_nonneg_right hI (norm_nonneg ((p : ℚ_[p]) ^ i))
    have hdvd : ((p ^ i : ℕ) : ℤ) ∣ A - B := by
      simpa only [Nat.cast_pow] using (Padic.norm_int_le_pow_iff_dvd (A - B) i).mp hnorm
    have hmod : (A : ZMod (p ^ i)) = (B : ZMod (p ^ i)) := by
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B) (p ^ i)).mpr hdvd
    letI : NeZero (p ^ i) := ⟨pow_ne_zero i hp.ne_zero⟩
    have hchar := congrArg (fun z : ZMod (p ^ i) => ZMod.stdAddChar z) hmod
    simpa only [ZMod.stdAddChar_coe, Nat.cast_pow] using hchar
  have hlift : ∀ (K : Type) [Field K] [CharZero K] (z : ℤ) (i j : ℕ),
      (((z * (p : ℤ) ^ j : ℤ) : K) / (p : K) ^ (i + j)) =
        (z : K) / (p : K) ^ i := by
    intro K _ _ z i j
    have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    push_cast
    rw [pow_add]
    exact mul_div_mul_right _ _ (pow_ne_zero j hpK)
  let k : ℕ := max m n
  let A : ℤ := a * (p : ℤ) ^ (k - m)
  let B : ℤ := b * (p : ℤ) ^ (k - n)
  have hm : m + (k - m) = k := Nat.add_sub_of_le (Nat.le_max_left m n)
  have hn : n + (k - n) = k := Nat.add_sub_of_le (Nat.le_max_right m n)
  have hqA : (A : ℚ_[p]) / (p : ℚ_[p]) ^ k = (a : ℚ_[p]) / (p : ℚ_[p]) ^ m := by
    have hs := hlift ℚ_[p] a m (k - m)
    rw [hm] at hs
    exact hs
  have hqB : (B : ℚ_[p]) / (p : ℚ_[p]) ^ k = (b : ℚ_[p]) / (p : ℚ_[p]) ^ n := by
    have hs := hlift ℚ_[p] b n (k - n)
    rw [hn] at hs
    exact hs
  have hcA : (A : ℂ) / (p : ℂ) ^ k = (a : ℂ) / (p : ℂ) ^ m := by
    have hs := hlift ℂ a m (k - m)
    rw [hm] at hs
    exact hs
  have hcB : (B : ℂ) / (p : ℂ) ^ k = (b : ℂ) / (p : ℂ) ^ n := by
    have hs := hlift ℂ b n (k - n)
    rw [hn] at hs
    exact hs
  have hcommon := hsame k A B (by simpa only [hqA, hqB] using h)
  simpa only [mul_div_assoc, hcA, hcB] using hcommon

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
