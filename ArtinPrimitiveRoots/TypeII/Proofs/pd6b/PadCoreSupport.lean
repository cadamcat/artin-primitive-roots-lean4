import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.RawCutoff

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical

/-- A nonzero signed pad core retains both eta factors and all four coefficients. -/
theorem padQuadCore_nonzero_eta_coeff {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ))
    (h : padQuadCore F x Y family beta ta tb q ≠ 0) :
    F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0 ∧ F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0 ∧
      coefficientQuadProduct family x beta q ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro hz <;> exact h (by simp [padQuadCore, hz])

/-- The signed core restricts its integer determinant to the common short tube. -/
theorem padQuadCore_nonzero_determinant_bound {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y R : ℝ)
    (hY : 0 < Y) (hR : 4 ≤ R) (hSupport : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ R)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) (ha : 0 < tupleProduct ta)
    (hcop : Nat.Coprime (tupleProduct ta) (tupleProduct tb))
    (hmn : 1 ≤ q.1.1 * q.1.2) (hrs : 1 ≤ q.2.1 * q.2.2)
    (h : padQuadCore F x Y family beta ta tb q ≠ 0) :
    |(((tupleProduct tb : ℤ) * q.1.1 * q.1.2 - (tupleProduct ta : ℤ) * q.2.1 * q.2.2 : ℤ) : ℝ)| ≤ R * Y := by
  let t : ℤ := (tupleProduct tb : ℤ) * q.1.1 * q.1.2 - (tupleProduct ta : ℤ) * q.2.1 * q.2.2
  have hdata := padQuadCore_nonzero_eta_coeff F x Y family beta ta tb q h
  have haBounds := hF.2.2.2.2.1.2.1 hdata.1
  have hbBounds := hF.2.2.2.2.1.2.1 hdata.2.1
  have haLo : Y ≤ (tupleProduct ta : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp haBounds.1
  have haHi : (tupleProduct ta : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp haBounds.2
  have hbLo : Y ≤ (tupleProduct tb : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp hbBounds.1
  have hbHi : (tupleProduct tb : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp hbBounds.2
  have htReal : (t : ℝ) = (tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) -
      (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ) := by dsimp [t]; push_cast; ring
  by_contra ht
  have hraw : ¬ ∃ v : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct ta * v ∧
      q.2.1 * q.2.2 - 1 = tupleProduct tb * v := by
    intro hc
    have he := (raw_det_iff_common_predecessor _ _ _ _ _ _ ha hcop hmn hrs).mpr hc
    have heR : (t : ℝ) = (tupleProduct tb : ℝ) - tupleProduct ta := by
      dsimp [t]
      rw [he, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    apply ht
    rw [heR, abs_le]
    constructor <;> nlinarith
  have hpsi : F.psi ((t : ℝ) / Y) = 0 := by
    by_contra hn
    have hs := hSupport ((t : ℝ) / Y) hn
    rw [abs_div, abs_of_pos hY] at hs
    exact ht ((div_le_iff₀ hY).mp hs)
  have hz : majorKernel x Y F.A₀ (t : ℝ) (tupleProduct ta) (tupleProduct tb) F.psi = 0 := by
    simp [majorKernel, hpsi]
  rw [htReal] at hz
  simp only [Nat.cast_mul] at hz
  exact h (by simp only [padQuadCore, if_neg hraw, hz, Nat.cast_mul, sub_zero, zero_sub, neg_zero, mul_zero, zero_mul])

end ArtinPrimitiveRoots.TypeII.PD
