import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MinorApproximation
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.TranslatedPacket
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MinorPacket

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Small Fourier shifts of a minor phase have uniformly small rectangular determinant norm. -/
theorem shifted_minor_determinant_bound (x Y A θ u C : ℝ)
    (hL : 0 < Real.log x) (hP : 1 ≤ Real.rpow (Real.log x) A)
    (hPY : Real.rpow (Real.log x) A ≤ Y) (hC : 0 ≤ C)
    (hminor : ¬ majorArc x Y A θ)
    (hu : |u| ≤ Real.rpow (Real.log x) A / 2)
    (M N : ℕ) (hprod : (M : ℝ)*(N : ℝ) ≤ C*Y)
    (haspect : (M : ℝ)+(N : ℝ) ≤ C*Real.rpow Y (9/10 : ℝ))
    (a b s t : ℝ) (f : ℕ → ℕ → ℂ) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
      ‖∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N,
        additiveCharacter ((θ+u/Y)*((a+(i : ℝ))*(t+(l : ℝ))-
          (b+(j : ℝ))*(s+(k : ℝ))))*f k l‖^2) ≤
    (96*Y*(C*Real.rpow (Real.log x) (-A)+
      (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A))*
        (1+Real.log (8*Y))))^2 *
      (∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N, ‖f k l‖^2) := by
  obtain ⟨c, d, hdlo, hdhi, hcop, happrox⟩ :=
    pd4c_minor_rational_approximation x Y A θ u hP hPY hminor hu
  have hY1 : 1 ≤ Y := hP.trans hPY
  have hY : 0 < Y := lt_of_lt_of_le (by norm_num) hY1
  have hdR : (1 : ℝ) < d := lt_of_le_of_lt hP hdlo
  have hd : 2 ≤ d := by
    have : (1 : ℕ) < d := by exact_mod_cast hdR
    omega
  have hdpos : (0 : ℝ) < d := by linarith only [hdR]
  have hdY : (d : ℝ) ≤ 2*Y :=
    hdhi.trans (div_le_self (by positivity) hP)
  let S : ℝ := 1+Real.log (4*(d : ℝ))
  let E : ℝ := (M : ℝ)*(N : ℝ)/(d : ℝ)+((M : ℝ)+(N : ℝ))*S+(d : ℝ)*S
  let Q : ℝ := C*Real.rpow (Real.log x) (-A)+
    (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A))*(1+Real.log (8*Y))
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    have hlog := Real.log_nonneg (by linarith only [hdR] : 1 ≤ 4*(d : ℝ))
    linarith only [hlog]
  have hS : S ≤ 1+Real.log (8*Y) := by
    dsimp only [S]
    exact add_le_add le_rfl (Real.log_le_log
      (by positivity : 0 < 4*(d : ℝ)) (by linarith only [hdY] : 4*(d : ℝ) ≤ 8*Y))
  have hnorm := normalized_minor_packet_bound (M : ℝ) (N : ℝ) (d : ℝ)
    Y (Real.log x) A C S hY hL hC hS0 hdlo.le hdhi hprod haspect
  have hcoef : 0 ≤ C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A) :=
    add_nonneg (mul_nonneg hC (Real.rpow_nonneg hY.le _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
  have hEQ : E/Y ≤ Q := by
    calc
      E/Y ≤ C*Real.rpow (Real.log x) (-A)+
        (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A))*S := hnorm
      _ ≤ Q := by
        dsimp only [Q]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hS hcoef)
  have hbound : 96*E ≤ 96*Y*Q := by
    have h := (div_le_iff₀ hY).mp hEQ
    calc
      _ ≤ 96*(Q*Y) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hE0 : 0 ≤ 96*E := by dsimp only [E]; positivity
  have hsquare : (96*E)^2 ≤ (96*Y*Q)^2 :=
    pow_le_pow_left₀ hE0 hbound 2
  have hmatrix := translated_determinant_packet_bound c d M N hd hcop
    (θ+u/Y) happrox a b s t f
  change _ ≤ (96*Y*Q)^2 * _
  calc
    _ ≤ (96*E)^2 * (∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N, ‖f k l‖^2) := hmatrix
    _ ≤ _ := mul_le_mul_of_nonneg_right hsquare (by positivity)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
