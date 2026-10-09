import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SmoothedRectangle
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CutoffMasses
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.ScaleDecay

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- The smoothed minor rectangle has the log-scale rate used by the clean assembly. -/
theorem scaled_smoothed_minor_rectangle_bound
    (K : ℕ) (δ c₁ c₂ A Cbox : ℝ) (hA : 0 < A) (hCbox : 0 ≤ Cbox)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ) :
    ∃ C x₁ : ℝ, 0 < C ∧ 2 ≤ x₁ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₁ ≤ S.x →
      ∀ θ : ℝ, ¬ majorArc S.x S.Y A θ →
      ∀ M N : ℕ, (M : ℝ)*(N : ℝ) ≤ Cbox*S.Y →
        (M : ℝ)+(N : ℝ) ≤ Cbox*Real.rpow S.Y (9/10 : ℝ) →
      ∀ a b s t : ℝ, ∀ f : ℕ × ℕ → ℂ,
      let I := (Finset.range M).product (Finset.range N)
      let D := fun i j : ℕ × ℕ =>
        (a+(i.1 : ℝ))*(t+(j.2 : ℝ))-(b+(i.2 : ℝ))*(s+(j.1 : ℝ))
      (∑ i ∈ I, ‖∑ j ∈ I,
        (ψ (D i j/S.Y) : ℂ)*additiveCharacter (θ*D i j)*f j‖^2) ≤
      (S.Y*(C*(Real.rpow S.L ((1/5 : ℝ)-A)+
        Real.rpow S.L (1/5 : ℝ)*
          Real.exp (-(1/200 : ℝ)*Real.rpow S.L (1/10 : ℝ)))))^2 *
        (∑ j ∈ I, ‖f j‖^2) := by
  let m₀ := ∫ u : ℝ, ‖pd4c_psiHat ψ u‖
  let m₁ := ∫ u : ℝ, |u| * ‖pd4c_psiHat ψ u‖
  have hm₀ : 0 ≤ m₀ := integral_nonneg (fun u => norm_nonneg _)
  have hm₁ : 0 ≤ m₁ := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  let H : ℝ := 1+Real.log 8+((K+1 : ℕ) : ℝ)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let Qc := Cbox+2*H+Cbox*H
  have hQc : 0 ≤ Qc := by dsimp only [Qc]; positivity
  let C := 96*m₀*Qc+2*m₁*Cbox+1
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨L₁, hL₁, hdecay⟩ := pd4c_logPower_expDecay 0 A (1/20 : ℝ) (by norm_num)
  let x₁ := max 2 (Real.exp L₁)
  refine ⟨C, x₁, hC, le_max_left _ _, ?_⟩
  intro S hS hx θ hminor M N hprod haspect a b s t f
  have hxexp : Real.exp L₁ ≤ S.x := (le_max_right _ _).trans hx
  have hLthreshold : L₁ ≤ S.L := by
    have h := Real.log_le_log (Real.exp_pos L₁) hxexp
    rw [Real.log_exp] at h
    exact h
  have hL1 : 1 ≤ S.L := hL₁.trans hLthreshold
  have hL : 0 < S.L := lt_of_lt_of_le (by norm_num) hL1
  rcases Finset.mem_filter.mp hS.2.2.2.2.2.1 with ⟨hYmem, hYbounds⟩
  rcases Finset.mem_image.mp hYmem with ⟨n, hn, heq⟩
  have hY : 0 < S.Y := by rw [← heq]; positivity
  have hP : 1 ≤ Real.rpow S.L A := Real.one_le_rpow hL1 hA.le
  have hPY : Real.rpow S.L A ≤ S.Y := by
    have hsmall : Real.rpow S.L A*
        Real.exp (-(1/20 : ℝ)*Real.rpow S.L (1/10 : ℝ)) ≤ 1 := by
      simpa only [Real.rpow_eq_pow, neg_zero, Real.rpow_zero] using hdecay S.L hLthreshold
    let v := (1/20 : ℝ)*Real.rpow S.L (1/10 : ℝ)
    have hsmall' : Real.rpow S.L A*Real.exp (-v) ≤ 1 := by
      simpa only [v, neg_mul] using hsmall
    calc
      _ = (Real.rpow S.L A*Real.exp (-v))*Real.exp v := by
        rw [mul_assoc, ← Real.exp_add]
        simp only [neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ 1*Real.exp v := mul_le_mul_of_nonneg_right hsmall' (Real.exp_pos _).le
      _ ≤ S.Y := by
        rw [one_mul, ← Real.exp_log hY]
        exact Real.exp_le_exp.mpr hYbounds.1
  have hY1 : 1 ≤ S.Y := hP.trans hPY
  let W := Real.rpow S.L (1/5 : ℝ)
  let X := Real.rpow S.L ((1/5 : ℝ)-A)
  let Z := W*Real.exp (-(1/200 : ℝ)*Real.rpow S.L (1/10 : ℝ))
  have hW : 1 ≤ W := Real.one_le_rpow hL1 (by norm_num)
  have hX : 0 ≤ X := (Real.rpow_pos_of_pos hL _).le
  have hZ : 0 ≤ Z := by dsimp only [Z, W]; positivity
  have hnegX : Real.rpow S.L (-A) ≤ X :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : -A ≤ (1/5 : ℝ)-A)
  have hneg0 : 0 ≤ Real.rpow S.L (-A) := Real.rpow_nonneg hL.le _
  have hYinv0 : 0 ≤ Real.rpow S.Y (-1/10 : ℝ) := Real.rpow_nonneg hY.le _
  have hnegW : Real.rpow S.L (-A)*W = X := by
    calc
      _ = Real.rpow S.L (-A+(1/5 : ℝ)) := (Real.rpow_add hL (-A) (1/5 : ℝ)).symm
      _ = X := by dsimp only [X]; congr 1; ring
  have hlog : 1+Real.log (8*S.Y) ≤ H*W := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hY.ne']
    have hconst : 1+Real.log 8 ≤ (1+Real.log 8)*W :=
      le_mul_of_one_le_right (by positivity) hW
    calc
      _ = (1+Real.log 8)+Real.log S.Y := by ring
      _ ≤ (1+Real.log 8)*W+((K+1 : ℕ) : ℝ)*W :=
        add_le_add hconst hYbounds.2
      _ = H*W := by dsimp only [H]; ring
  let Q := Cbox*Real.rpow S.L (-A)+
    (Cbox*Real.rpow S.Y (-1/10 : ℝ)+2*Real.rpow S.L (-A))*(1+Real.log (8*S.Y))
  have hlog0 : 0 ≤ 1+Real.log (8*S.Y) := by
    have := Real.log_nonneg (by linarith only [hY1] : 1 ≤ 8*S.Y)
    linarith
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hYdecay : Real.rpow S.Y (-1/10 : ℝ) ≤
      Real.exp (-(1/200 : ℝ)*Real.rpow S.L (1/10 : ℝ)) := by
    simpa only [neg_div] using pd4c_scale_Y_inv_tenth_le δ c₁ c₂ S hS
  have hQbound : Q ≤ Qc*(X+Z) := by
    have hmain : Cbox*Real.rpow S.L (-A) ≤ Cbox*X :=
      mul_le_mul_of_nonneg_left hnegX hCbox
    have hsub : (Cbox*Real.rpow S.Y (-1/10 : ℝ)+2*Real.rpow S.L (-A))*
        (1+Real.log (8*S.Y)) ≤ Cbox*H*Z+2*H*X := by
      calc
        _ ≤ (Cbox*Real.exp (-(1/200 : ℝ)*Real.rpow S.L (1/10 : ℝ))+
            2*Real.rpow S.L (-A))*(H*W) := by
          apply mul_le_mul
          · exact add_le_add (mul_le_mul_of_nonneg_left hYdecay hCbox) le_rfl
          · exact hlog
          · exact hlog0
          · positivity
        _ = Cbox*H*Z+2*H*(Real.rpow S.L (-A)*W) := by dsimp only [Z]; ring
        _ = Cbox*H*Z+2*H*X := by rw [hnegW]
    calc
      Q ≤ Cbox*X+(Cbox*H*Z+2*H*X) := add_le_add hmain hsub
      _ ≤ Qc*(X+Z) := by
        have h₁ : 0 ≤ (Cbox+2*H)*Z := mul_nonneg (by positivity) hZ
        have h₂ : 0 ≤ (Cbox*H)*X := mul_nonneg (mul_nonneg hCbox hH) hX
        dsimp only [Qc]
        nlinarith only [h₁, h₂]
  let T : Set ℝ := {u | |u| ≤ Real.rpow S.L A/2}
  have hmasses := cutoff_density_mass_bounds ψ hψ hcompact S.L A hL
  have hamp :
      (∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*(96*S.Y*Q)+
        (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*((M : ℝ)*(N : ℝ)) ≤
      S.Y*(C*(X+Z)) := by
    have hsum : 0 ≤ X+Z := add_nonneg hX hZ
    calc
      _ ≤ m₀*(96*S.Y*Q)+(2*m₁*Real.rpow S.L (-A))*(Cbox*S.Y) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hmasses.1 (by positivity)
        · apply mul_le_mul
          · exact hmasses.2
          · exact hprod
          · positivity
          · positivity
      _ = S.Y*(96*m₀*Q+(2*m₁*Cbox)*Real.rpow S.L (-A)) := by ring
      _ ≤ S.Y*(96*m₀*(Qc*(X+Z))+(2*m₁*Cbox)*(X+Z)) := by
        apply mul_le_mul_of_nonneg_left _ hY.le
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hQbound (by positivity)
        · exact mul_le_mul_of_nonneg_left (hnegX.trans (le_add_of_nonneg_right hZ))
            (by positivity)
      _ ≤ S.Y*(C*(X+Z)) := by
        apply mul_le_mul_of_nonneg_left _ hY.le
        dsimp only [C]
        nlinarith only [hsum]
  have hamp0 : 0 ≤
      (∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*(96*S.Y*Q)+
        (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*((M : ℝ)*(N : ℝ)) := by
    apply add_nonneg
    · exact mul_nonneg (integral_nonneg (fun u => norm_nonneg _)) (by positivity)
    · exact mul_nonneg (integral_nonneg (fun u => norm_nonneg _)) (by positivity)
  have hmatrix := smoothed_minor_rectangle_bound ψ hψ hcompact S.x S.Y A θ Cbox
    hL hP hPY hCbox hminor M N hprod haspect a b s t f
  dsimp only at hmatrix ⊢
  change _ ≤ (S.Y*(C*(X+Z)))^2*_
  have hsq := pow_le_pow_left₀ hamp0 hamp 2
  exact hmatrix.trans (mul_le_mul_of_nonneg_right hsq (by positivity))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
