import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.DeterminantRange
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.PacketBound

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Translating rectangular determinant blocks changes only unit character factors. -/
theorem translated_determinant_packet_bound (c : ℤ) (d M N : ℕ)
    (hd : 2 ≤ d) (hcop : Int.gcd c (d : ℤ) = 1)
    (θ : ℝ) (happrox : |θ - (c : ℝ)/(d : ℝ)| ≤ 1/(d : ℝ)^2)
    (a b s t : ℝ) (f : ℕ → ℕ → ℂ) :
    (∑ x ∈ Finset.range M, ∑ y ∈ Finset.range N,
      ‖∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N,
        additiveCharacter (θ*((a+(x : ℝ))*(t+(v : ℝ))-
          (b+(y : ℝ))*(s+(u : ℝ))))*f u v‖^2) ≤
    (96*((M : ℝ)*(N : ℝ)/(d : ℝ)+
      ((M : ℝ)+(N : ℝ))*(1+Real.log (4*(d : ℝ)))+
      (d : ℝ)*(1+Real.log (4*(d : ℝ)))))^2 *
    (∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N, ‖f u v‖^2) := by
  let S : ℝ := 1 + Real.log (4*(d : ℝ))
  let R : ℝ := 96*((M : ℝ)*(N : ℝ)/(d : ℝ)+
    ((M : ℝ)+(N : ℝ))*S+(d : ℝ)*S)
  let A : ℝ := ((N/(d/2)+1 : ℕ) : ℝ)*((M : ℝ)+32*(d : ℝ)*S)
  let B : ℝ := ((M/(d/2)+1 : ℕ) : ℝ)*((N : ℝ)+32*(d : ℝ)*S)
  let f' (u v : ℕ) : ℂ :=
    additiveCharacter (θ*(a*(v : ℝ)-b*(u : ℝ)))*f u v
  let χ (x y : ℕ) : ℂ :=
    additiveCharacter (θ*(t*(x : ℝ)-s*(y : ℝ)+a*t-b*s))
  have hf (u v : ℕ) : ‖f' u v‖ = ‖f u v‖ := by
    simp only [f', norm_mul, pd4c_character_norm, one_mul]
  have hpoint (x y : ℕ) :
      ‖∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N,
        additiveCharacter (θ*((a+(x : ℝ))*(t+(v : ℝ))-
          (b+(y : ℝ))*(s+(u : ℝ))))*f u v‖ =
      ‖∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N,
        additiveCharacter (θ*((x : ℝ)*(v : ℝ)-(y : ℝ)*(u : ℝ)))*f' u v‖ := by
    have hentry (u v : ℕ) :
        additiveCharacter (θ*((a+(x : ℝ))*(t+(v : ℝ))-
          (b+(y : ℝ))*(s+(u : ℝ))))*f u v =
        χ x y * (additiveCharacter (θ*((x : ℝ)*(v : ℝ)-(y : ℝ)*(u : ℝ)))*
          f' u v) := by
      have hphase :
          additiveCharacter (θ*((a+(x : ℝ))*(t+(v : ℝ))-
            (b+(y : ℝ))*(s+(u : ℝ)))) =
          χ x y * (additiveCharacter (θ*((x : ℝ)*(v : ℝ)-(y : ℝ)*(u : ℝ)))*
            additiveCharacter (θ*(a*(v : ℝ)-b*(u : ℝ)))) := by
        dsimp only [χ]
        rw [← pd4c_character_add, ← pd4c_character_add]
        congr 1
        ring
      rw [hphase]
      dsimp only [f']
      ring
    simp_rw [hentry, ← Finset.mul_sum]
    rw [norm_mul]
    simp only [χ, pd4c_character_norm, one_mul]
  have hbase := rational_determinant_range_bound c d M N hd hcop θ happrox f'
  simp_rw [hf] at hbase
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hS : 1 ≤ S := by
    dsimp only [S]
    have hlog := Real.log_nonneg (by linarith only [hdR] : 1 ≤ 4*(d : ℝ))
    linarith only [hlog]
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS
  have hA : A ≤ R := by
    calc
      A ≤ 96*((N : ℝ)*(M : ℝ)/(d : ℝ)+
          ((N : ℝ)+(M : ℝ))*S+(d : ℝ)*S) :=
        half_denominator_packet_bound d N M hd S hS
      _ = R := by dsimp only [R]; ring
  have hB : B ≤ R := half_denominator_packet_bound d M N hd S hS
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hAB : A*B ≤ R^2 := by
    calc
      _ ≤ R*R := mul_le_mul hA hB hB0 hR0
      _ = _ := (pow_two R).symm
  change _ ≤ R^2 * _
  simp_rw [hpoint]
  calc
    _ ≤ A*B*(∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N, ‖f u v‖^2) := hbase
    _ ≤ _ := mul_le_mul_of_nonneg_right hAB (by positivity)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
