import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Geometry
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Equal encoded projective lines imply determinant divisibility, including zero vectors. -/
theorem projLine_eq_imp_det_dvd (p : ℕ) (hp : p.Prime) (z z' : ℤ × ℤ)
    (hline : projLine p z = projLine p z') : (p : ℤ) ∣ det2 z z' := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfinite (u : ℤ × ℤ) (hu : (u.2 : ZMod p) ≠ 0) :
      (projLine p u).val = ((u.1 : ZMod p)*(u.2 : ZMod p)⁻¹).val := by
    rw [projLine, if_neg hu]
    change ((u.1 : ZMod p)*(u.2 : ZMod p)⁻¹).val % (p+1) = _
    exact Nat.mod_eq_of_lt ((ZMod.val_lt _).trans (Nat.lt_succ_self p))
  have hdetmod : (z.1 : ZMod p)*(z'.2 : ZMod p)-
      (z.2 : ZMod p)*(z'.1 : ZMod p) = 0 := by
    by_cases hz2 : (z.2 : ZMod p) = 0
    · by_cases hz'2 : (z'.2 : ZMod p) = 0
      · simp only [hz2, hz'2, mul_zero, zero_mul, sub_self]
      · have hlast : (projLine p z).val = p := by
          simp only [projLine, if_pos hz2, Fin.val_last]
        have hlt := ZMod.val_lt ((z'.1 : ZMod p)*(z'.2 : ZMod p)⁻¹)
        rw [← hfinite z' hz'2, ← hline, hlast] at hlt
        exact (lt_irrefl p hlt).elim
    · by_cases hz'2 : (z'.2 : ZMod p) = 0
      · have hlast : (projLine p z').val = p := by
          simp only [projLine, if_pos hz'2, Fin.val_last]
        have hlt := ZMod.val_lt ((z.1 : ZMod p)*(z.2 : ZMod p)⁻¹)
        rw [← hfinite z hz2, hline, hlast] at hlt
        exact (lt_irrefl p hlt).elim
      · have hvals : ((z.1 : ZMod p)*(z.2 : ZMod p)⁻¹).val =
            ((z'.1 : ZMod p)*(z'.2 : ZMod p)⁻¹).val := by
          rw [← hfinite z hz2, ← hfinite z' hz'2, hline]
        have hratio := ZMod.val_injective p hvals
        have hdiv : (z.1 : ZMod p)/(z.2 : ZMod p) =
            (z'.1 : ZMod p)/(z'.2 : ZMod p) := by
          simpa only [div_eq_mul_inv] using hratio
        have hcross := (div_eq_div_iff hz2 hz'2).mp hdiv
        apply sub_eq_zero.mpr
        exact hcross.trans (mul_comm _ _)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (det2 z z') p).mp
  simpa only [det2, Int.cast_sub, Int.cast_mul] using hdetmod

/-- A common projective-line tuple puts positions in one squarefree pad lattice. -/
theorem projective_line_pad_dvd (D : ℕ) (hD : Squarefree D) (z z' : ℤ × ℤ)
    (hline : ∀ p : ℕ, p.Prime → p ∣ D → projLine p z = projLine p z') :
    (D : ℤ) ∣ det2 z z' := by
  apply Int.natCast_dvd.mpr
  by_cases hzero : (det2 z z').natAbs = 0
  · rw [hzero]
    exact dvd_zero D
  · rw [← Nat.prod_primeFactors_of_squarefree hD]
    apply (Nat.prod_primeFactors_dvd_iff hzero).mpr
    intro p hp
    obtain ⟨hprime, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    apply (Nat.mem_primeFactors_of_ne_zero hzero).mpr
    exact ⟨hprime, Int.natCast_dvd.mp (projLine_eq_imp_det_dvd p hprime z z'
      (hline p hprime hpd))⟩

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
