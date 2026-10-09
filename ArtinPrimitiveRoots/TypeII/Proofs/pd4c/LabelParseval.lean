import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LabelIntegral

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII MeasureTheory

noncomputable section

/-- Orthogonality evaluates the energy of a finite label Fourier polynomial. -/
theorem finite_label_parseval (U : Finset ℤ) (f : ℤ → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖∑ n ∈ U, additiveCharacter ((n : ℝ)*θ)*f n‖^2) =
      ∑ n ∈ U, ‖f n‖^2 := by
  have hnorm (z : ℂ) : ‖z‖^2 = (star z*z).re := by
    simp only [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hchar (n m : ℤ) (θ : ℝ) :
      star (additiveCharacter ((n : ℝ)*θ))*additiveCharacter ((m : ℝ)*θ) =
        additiveCharacter (((m-n : ℤ) : ℝ)*θ) := by
    unfold additiveCharacter
    rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  let G := fun (n m : ℤ) (θ : ℝ) =>
    star (f n)*f m*additiveCharacter (((m-n : ℤ) : ℝ)*θ)
  have hpoint (θ : ℝ) :
      ‖∑ n ∈ U, additiveCharacter ((n : ℝ)*θ)*f n‖^2 =
        (∑ n ∈ U, ∑ m ∈ U, G n m θ).re := by
    rw [hnorm]
    congr 1
    simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum, star_mul]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    calc
      _ = star (f n)*f m*(star (additiveCharacter ((n : ℝ)*θ))*
          additiveCharacter ((m : ℝ)*θ)) := by ring
      _ = G n m θ := by rw [hchar]
  have hG (n m : ℤ) : Continuous (G n m) := by
    dsimp only [G]
    unfold additiveCharacter
    fun_prop
  have hGs (n : ℤ) : Continuous (fun θ => ∑ m ∈ U, G n m θ) :=
    continuous_finset_sum U (fun m hm => hG n m)
  have hGss : Continuous (fun θ => ∑ n ∈ U, ∑ m ∈ U, G n m θ) :=
    continuous_finset_sum U (fun n hn => hGs n)
  have hsum :
      (∫ θ in (0 : ℝ)..1, ∑ n ∈ U, ∑ m ∈ U, G n m θ) =
        ∑ n ∈ U, ∑ m ∈ U, ∫ θ in (0 : ℝ)..1, G n m θ := by
    rw [intervalIntegral.integral_finsetSum (fun n hn => (hGs n).intervalIntegrable 0 1)]
    apply Finset.sum_congr rfl
    intro n hn
    exact intervalIntegral.integral_finsetSum (fun m hm => (hG n m).intervalIntegrable 0 1)
  have hdiag (n : ℤ) (hn : n ∈ U) :
      (∑ m ∈ U, ∫ θ in (0 : ℝ)..1, G n m θ) = star (f n)*f n := by
    dsimp only [G]
    simp_rw [intervalIntegral.integral_const_mul, integer_character_integral]
    simp [sub_eq_zero, hn]
  calc
    _ = ∫ θ in (0 : ℝ)..1, (∑ n ∈ U, ∑ m ∈ U, G n m θ).re := by
      exact intervalIntegral.integral_congr (fun θ hθ => hpoint θ)
    _ = (∫ θ in (0 : ℝ)..1, ∑ n ∈ U, ∑ m ∈ U, G n m θ).re :=
      Complex.reCLM.intervalIntegral_comp_comm (hGss.intervalIntegrable 0 1)
    _ = (∑ n ∈ U, star (f n)*f n).re := by
      rw [hsum]
      congr 1
      exact Finset.sum_congr rfl hdiag
    _ = _ := by rw [Complex.re_sum]; exact Finset.sum_congr rfl (fun n hn => (hnorm (f n)).symm)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
