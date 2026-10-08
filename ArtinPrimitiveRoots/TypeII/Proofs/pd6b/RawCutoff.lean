import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadReindexing
import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- On eta-supported common-predecessor terms the arc cutoff is exactly one. -/
theorem eta_raw_common_identity {K : ℕ} (F : PDFix K) (hF : F.Valid) (Y : ℝ)
    (hY : 0 < Y) (a b m n r s : ℕ) (ha : 0 < a) (hcop : Nat.Coprime a b)
    (hmn : 1 ≤ m * n) (hrs : 1 ≤ r * s) :
    (F.eta ((b : ℝ) / Y) : ℂ) * (F.eta ((a : ℝ) / Y) : ℂ) *
      (if (b : ℤ) * m * n - (a : ℤ) * r * s = (b : ℤ) - a then
        (F.psi ((((b : ℤ) * m * n - (a : ℤ) * r * s : ℤ) : ℝ) / Y) : ℂ) else 0) =
      (F.eta ((a : ℝ) / Y) : ℂ) * (F.eta ((b : ℝ) / Y) : ℂ) *
        (if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0) := by
  by_cases hηa : F.eta ((a : ℝ) / Y) = 0
  · simp only [hηa, Complex.ofReal_zero, mul_zero, zero_mul]
  by_cases hηb : F.eta ((b : ℝ) / Y) = 0
  · simp only [hηb, Complex.ofReal_zero, mul_zero, zero_mul]
  have haBounds := hF.2.2.2.2.1.2.1 hηa
  have hbBounds := hF.2.2.2.2.1.2.1 hηb
  have haLo : Y ≤ (a : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp haBounds.1
  have haHi : (a : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp haBounds.2
  have hbLo : Y ≤ (b : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp hbBounds.1
  have hbHi : (b : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp hbBounds.2
  have heq := raw_det_iff_common_predecessor a b m n r s ha hcop hmn hrs
  by_cases ht : (b : ℤ) * m * n - (a : ℤ) * r * s = (b : ℤ) - a
  · have hc := heq.mp ht
    have hpsi : F.psi ((((b : ℤ) * m * n - (a : ℤ) * r * s : ℤ) : ℝ) / Y) = 1 := by
      apply hF.2.2.2.2.2.2.2
      rw [ht, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
      constructor
      · apply (le_div_iff₀ hY).mpr
        linarith
      · apply (div_le_iff₀ hY).mpr
        linarith
    simp only [if_pos ht, if_pos hc, hpsi, Complex.ofReal_one, mul_one]
    ring
  · have hc : ¬ ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h := fun h => ht (heq.mpr h)
    simp only [if_neg ht, if_neg hc, mul_zero]

end ArtinPrimitiveRoots.TypeII.PD
