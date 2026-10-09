import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SmoothedMatrix

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- The finite character-matrix smoothing bound applies to arbitrary finite index sets. -/
theorem smoothed_finset_matrix_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ) (Y θ : ℝ) (D : ι → κ → ℝ) (f : κ → ℂ)
    (T : Set ℝ) (hT : MeasurableSet T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinner : ∀ u ∈ T,
      (∑ i ∈ I, ‖∑ j ∈ J, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        a^2*(∑ j ∈ J, ‖f j‖^2))
    (houter : ∀ u ∉ T,
      (∑ i ∈ I, ‖∑ j ∈ J, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        b^2*(∑ j ∈ J, ‖f j‖^2)) :
    (∑ i ∈ I, ‖∑ j ∈ J, (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j‖^2) ≤
    ((∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*a +
      (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*b)^2 * (∑ j ∈ J, ‖f j‖^2) := by
  have hsquared (k : ι → κ → ℂ) :
      (∑ i : I, ‖∑ j : J, k i j‖^2) =
        ∑ i ∈ I, ‖∑ j ∈ J, k i j‖^2 := by
    calc
      _ = ∑ i : I, ‖∑ j ∈ J, k i j‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_coe_sort J (k i)]
      _ = _ := Finset.sum_coe_sort I (fun i => ‖∑ j ∈ J, k i j‖^2)
  have hi (u : ℝ) (hu : u ∈ T) :
      (∑ i : I, ‖∑ j : J, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        a^2*(∑ j : J, ‖f j‖^2) := by
    rw [hsquared (fun i j => additiveCharacter ((θ+u/Y)*D i j)*f j),
      Finset.sum_coe_sort J (fun j => ‖f j‖^2)]
    exact hinner u hu
  have ho (u : ℝ) (hu : u ∉ T) :
      (∑ i : I, ‖∑ j : J, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤
        b^2*(∑ j : J, ‖f j‖^2) := by
    rw [hsquared (fun i j => additiveCharacter ((θ+u/Y)*D i j)*f j),
      Finset.sum_coe_sort J (fun j => ‖f j‖^2)]
    exact houter u hu
  have h := smoothed_finite_matrix_bound ψ hψ hcompact Y θ
    (fun (i : I) (j : J) => D i j) (fun (j : J) => f j) T hT a b ha hb hi ho
  rw [hsquared (fun i j => (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j),
    Finset.sum_coe_sort J (fun j => ‖f j‖^2)] at h
  exact h

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
