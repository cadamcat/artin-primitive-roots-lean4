import Mathlib
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FourierCutoff

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- Finite cutoff matrices are integrals of the shifted character matrices. -/
theorem finite_cutoff_fourier {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ) (Y θ : ℝ)
    (T : Finset α) (U : Finset β) (D : α → β → ℝ) (f : α → β → ℂ) :
    (∑ i ∈ T, ∑ j ∈ U, (ψ (D i j/Y) : ℂ)*
      additiveCharacter (θ*D i j)*f i j) =
    ∫ u : ℝ, pd4c_psiHat ψ u *
      (∑ i ∈ T, ∑ j ∈ U, additiveCharacter ((θ+u/Y)*D i j)*f i j) := by
  obtain ⟨H, hH⟩ := pd4c_psiHat_isSchwartz ψ hψ hcompact
  have hHat : Integrable (pd4c_psiHat ψ) := by simpa only [hH] using H.integrable
  have hHatC : Continuous (pd4c_psiHat ψ) := by simpa only [hH] using H.continuous
  have hchar (t : ℝ) : ‖additiveCharacter t‖ = 1 := by
    simp [additiveCharacter, Complex.norm_exp]
  have hint (i : α) (j : β) : Integrable (fun u : ℝ =>
      pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f i j) := by
    have hc : Continuous (fun u : ℝ => additiveCharacter ((θ+u/Y)*D i j)) := by
      unfold additiveCharacter
      fun_prop
    have hm : AEStronglyMeasurable (fun u : ℝ =>
        pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f i j) :=
      ((hHatC.mul hc).mul_const (f i j)).aestronglyMeasurable
    apply (hHat.norm.mul_const ‖f i j‖).mono' hm
    filter_upwards [] with u
    simp only [norm_mul, hchar, mul_one, le_refl]
  calc
    _ = ∑ i ∈ T, ∑ j ∈ U, ∫ u : ℝ,
        pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [pd4c_determinant_cutoff_fourier ψ hψ hcompact Y θ (D i j),
        ← integral_mul_const]
    _ = ∫ u : ℝ, ∑ i ∈ T, ∑ j ∈ U,
        pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f i j := by
      symm
      rw [integral_finset_sum T (fun i hi => integrable_finset_sum U (fun j hj => hint i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finset_sum U (fun j hj => hint i j)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [Finset.mul_sum, mul_assoc]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
