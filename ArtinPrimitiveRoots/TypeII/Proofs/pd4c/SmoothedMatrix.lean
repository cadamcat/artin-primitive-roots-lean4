import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MatrixCutoff
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CutoffL2

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- Fibre bounds and Fourier density masses control a smoothed finite character matrix. -/
theorem smoothed_finite_matrix_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ) (Y θ : ℝ) (D : ι → κ → ℝ) (f : κ → ℂ)
    (T : Set ℝ) (hT : MeasurableSet T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinner : ∀ u ∈ T,
      (∑ i, ‖∑ j, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤ a^2*(∑ j, ‖f j‖^2))
    (houter : ∀ u ∉ T,
      (∑ i, ‖∑ j, additiveCharacter ((θ+u/Y)*D i j)*f j‖^2) ≤ b^2*(∑ j, ‖f j‖^2)) :
    (∑ i, ‖∑ j, (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j‖^2) ≤
    ((∫ u : ℝ in T, ‖pd4c_psiHat ψ u‖)*a +
      (∫ u : ℝ in Tᶜ, ‖pd4c_psiHat ψ u‖)*b)^2 * (∑ j, ‖f j‖^2) := by
  classical
  let V (u : ℝ) : EuclideanSpace ℂ ι := WithLp.toLp 2
    (fun i => ∑ j, additiveCharacter ((θ+u/Y)*D i j)*f j)
  let fvec : EuclideanSpace ℂ κ := WithLp.toLp 2 f
  obtain ⟨H, hH⟩ := pd4c_psiHat_isSchwartz ψ hψ hcompact
  have hHat : Integrable (pd4c_psiHat ψ) := by simpa only [hH] using H.integrable
  have hHatC : Continuous (pd4c_psiHat ψ) := by simpa only [hH] using H.continuous
  have hchar (t : ℝ) : ‖additiveCharacter t‖ = 1 := by
    simp [additiveCharacter, Complex.norm_exp]
  have hint (i : ι) (j : κ) : Integrable (fun u : ℝ =>
      pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f j) := by
    have hc : Continuous (fun u : ℝ => additiveCharacter ((θ+u/Y)*D i j)) := by
      unfold additiveCharacter
      fun_prop
    have hm : AEStronglyMeasurable (fun u : ℝ =>
        pd4c_psiHat ψ u * additiveCharacter ((θ+u/Y)*D i j)*f j) :=
      ((hHatC.mul hc).mul_const (f j)).aestronglyMeasurable
    apply (hHat.norm.mul_const ‖f j‖).mono' hm
    filter_upwards [] with u
    simp only [norm_mul, hchar, mul_one, le_refl]
  have hV : Integrable (fun u : ℝ => pd4c_psiHat ψ u • V u) := by
    apply Integrable.of_eval_piLp
    intro i
    change Integrable (fun u : ℝ => pd4c_psiHat ψ u *
      (∑ j, additiveCharacter ((θ+u/Y)*D i j)*f j))
    have hi := integrable_finsetSum Finset.univ (fun j hj => hint i j)
    simpa only [Finset.mul_sum, mul_assoc] using hi
  have hcoord (i : ι) :
      (∑ j, (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*f j) =
      ∫ u : ℝ, pd4c_psiHat ψ u * V u i := by
    have h := finite_cutoff_fourier ψ hψ hcompact Y θ
      (Finset.univ : Finset κ) ({()} : Finset Unit)
      (fun j _ => D i j) (fun j _ => f j)
    simpa only [Finset.sum_singleton] using h
  have h := finite_cutoff_l2_bound (pd4c_psiHat ψ) V fvec T hT hHat.norm hV
    a b ha hb hinner houter
  simp_rw [← hcoord] at h
  exact h

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
