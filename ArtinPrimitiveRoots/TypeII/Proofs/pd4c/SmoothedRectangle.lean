import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MinorDeterminant
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.UnitMatrix
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SmoothedFinset

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- The actual cutoff rectangle has the minor-fibre bound plus a trivial Fourier-tail bound. -/
theorem smoothed_minor_rectangle_bound
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ) (x Y A θ C : ℝ)
    (hL : 0 < Real.log x) (hP : 1 ≤ Real.rpow (Real.log x) A)
    (hPY : Real.rpow (Real.log x) A ≤ Y) (hC : 0 ≤ C)
    (hminor : ¬ majorArc x Y A θ)
    (M N : ℕ) (hprod : (M : ℝ)*(N : ℝ) ≤ C*Y)
    (haspect : (M : ℝ)+(N : ℝ) ≤ C*Real.rpow Y (9/10 : ℝ))
    (a b s t : ℝ) (f : ℕ × ℕ → ℂ) :
    let I := (Finset.range M).product (Finset.range N)
    let D := fun i j : ℕ × ℕ => (a+(i.1 : ℝ))*(t+(j.2 : ℝ))-
      (b+(i.2 : ℝ))*(s+(j.1 : ℝ))
    let Q := C*Real.rpow (Real.log x) (-A)+
      (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A))*(1+Real.log (8*Y))
    let T : Set ℝ := {u | |u| ≤ Real.rpow (Real.log x) A/2}
    (∑ i ∈ I, ‖∑ j ∈ I, (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j‖^2) ≤
      ((∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*(96*Y*Q)+
        (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*((M : ℝ)*(N : ℝ)))^2 *
          (∑ j ∈ I, ‖f j‖^2) := by
  let I := (Finset.range M) ×ˢ (Finset.range N)
  let D := fun i j : ℕ × ℕ => (a+(i.1 : ℝ))*(t+(j.2 : ℝ))-
    (b+(i.2 : ℝ))*(s+(j.1 : ℝ))
  let Q := C*Real.rpow (Real.log x) (-A)+
    (C*Real.rpow Y (-1/10 : ℝ)+2*Real.rpow (Real.log x) (-A))*(1+Real.log (8*Y))
  let T : Set ℝ := {u | |u| ≤ Real.rpow (Real.log x) A/2}
  change (∑ i ∈ I, ‖∑ j ∈ I, (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j‖^2) ≤
    ((∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*(96*Y*Q)+
      (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*((M : ℝ)*(N : ℝ)))^2 *
        (∑ j ∈ I, ‖f j‖^2)
  have hY1 : 1 ≤ Y := hP.trans hPY
  have hY : 0 < Y := lt_of_lt_of_le (by norm_num) hY1
  have hlog : 0 ≤ Real.log (8*Y) := Real.log_nonneg (by linarith only [hY1])
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (mul_nonneg hC (Real.rpow_nonneg hL.le _))
      (mul_nonneg
        (add_nonneg (mul_nonneg hC (Real.rpow_nonneg hY.le _))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _)))
        (add_nonneg (by norm_num) hlog))
  have hT : MeasurableSet T := (isClosed_le continuous_abs continuous_const).measurableSet
  have hinner (u : ℝ) (hu : u ∈ T) :
      (∑ i ∈ I, ‖∑ j ∈ I, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        (96*Y*Q)^2*(∑ j ∈ I, ‖f j‖^2) := by
    have h := shifted_minor_determinant_bound x Y A θ u C hL hP hPY hC hminor
      hu M N hprod haspect a b s t (fun k l => f (k,l))
    simpa only [I, D, Q, Finset.sum_product] using h
  have houter (u : ℝ) (hu : u ∉ T) :
      (∑ i ∈ I, ‖∑ j ∈ I, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        ((M : ℝ)*(N : ℝ))^2*(∑ j ∈ I, ‖f j‖^2) := by
    have h := finite_unit_matrix_bound I I
      (fun i j => additiveCharacter ((θ+u/Y)*D i j)) f (by
        intro i hi j hj
        simp only [pd4c_character_norm, le_refl])
    simpa only [I, Finset.card_product, Finset.card_range, Nat.cast_mul, pow_two] using h
  exact smoothed_finset_matrix_bound I I ψ hψ hcompact Y θ D f T hT
    (96*Y*Q) ((M : ℝ)*(N : ℝ)) (by positivity) (by positivity) hinner houter

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
