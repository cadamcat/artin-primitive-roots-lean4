import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

noncomputable section

/-- Normalizing the rectangular packet uses the lattice aspect and denominator bounds. -/
theorem normalized_minor_packet_bound (M N d Y L A C S : ℝ)
    (hY : 0 < Y) (hL : 0 < L) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hdlo : Real.rpow L A ≤ d)
    (hdhi : d ≤ 2*Y/Real.rpow L A)
    (hprod : M*N ≤ C*Y)
    (haspect : M+N ≤ C*Real.rpow Y (9/10 : ℝ)) :
    (M*N/d+(M+N)*S+d*S)/Y ≤
    C*Real.rpow L (-A) +
      (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow L (-A))*S := by
  have hD : 0 < Real.rpow L A := Real.rpow_pos_of_pos hL A
  have hd : 0 < d := lt_of_lt_of_le hD hdlo
  have hneg : Real.rpow L (-A) = (Real.rpow L A)⁻¹ := Real.rpow_neg hL.le A
  have hscale : Real.rpow Y (9/10 : ℝ)/Y = Real.rpow Y (-1/10 : ℝ) := by
    have hraw : Real.rpow Y ((9/10 : ℝ)-1) = Real.rpow Y (9/10 : ℝ)/Y :=
      Real.rpow_sub_one hY.ne' (9/10 : ℝ)
    norm_num at hraw
    simpa only [Real.rpow_eq_pow, neg_div] using hraw.symm
  have hfirst : (M*N/Y)/d ≤ C*Real.rpow L (-A) := by
    calc
      _ ≤ C/d := div_le_div_of_nonneg_right ((div_le_iff₀ hY).mpr hprod) hd.le
      _ ≤ C/Real.rpow L A := div_le_div_of_nonneg_left hC hD hdlo
      _ = _ := by rw [hneg, div_eq_mul_inv]
  have hwidth : (M+N)/Y ≤ C*Real.rpow Y (-1/10 : ℝ) := by
    calc
      _ ≤ (C*Real.rpow Y (9/10 : ℝ))/Y :=
        div_le_div_of_nonneg_right haspect hY.le
      _ = _ := by rw [mul_div_assoc, hscale]
  have hlast : d/Y ≤ 2*Real.rpow L (-A) := by
    calc
      _ ≤ (2*Y/Real.rpow L A)/Y := div_le_div_of_nonneg_right hdhi hY.le
      _ = _ := by
        rw [hneg]
        field_simp [hD.ne', hY.ne'] <;> ring
  calc
    _ = (M*N/Y)/d + ((M+N)/Y)*S + (d/Y)*S := by ring
    _ ≤ C*Real.rpow L (-A) + (C*Real.rpow Y (-1/10 : ℝ))*S +
        (2*Real.rpow L (-A))*S :=
      add_le_add (add_le_add hfirst (mul_le_mul_of_nonneg_right hwidth hS))
        (mul_le_mul_of_nonneg_right hlast hS)
    _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
