import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.Analysis.Complex.Isometry

set_option autoImplicit false
open MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

set_option backward.isDefEq.respectTransparency false in
/-- Complex Bruhat integrals acquire the real two-dimensional dilation factor. -/
theorem complex_bruhat_integral
    (f : PGL2 ℂ → ℂ) (u : ℂˣ) (g : PGL2 ℂ) :
    (∫ x : ℂ, f (aC u * wC * nC x * g)) =
      (‖(u : ℂ)‖ ^ 2 : ℝ) • intertwineC f (aC u⁻¹ * g) ∧
    (∫ x : ℂ, ‖f (aC u * wC * nC x * g)‖) =
      ‖(u : ℂ)‖ ^ 2 * ∫ x : ℂ, ‖f (wC * nC x * aC u⁻¹ * g)‖ := by
  classical
  have hmat (x : ℂ) : diagM ℂ u * weylM ℂ * upperM ℂ x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (weylM ℂ * upperM ℂ (x / (u : ℂ)) * diagM ℂ u⁻¹) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, weylM, upperM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;>
      field_simp [u.ne_zero] <;> ring
  have hscalar : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
      PGL2 ℂ) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hgroup (x : ℂ) : aC u * wC * nC x * g = wC * nC (x / (u : ℂ)) * aC u⁻¹ * g := by
    have h := congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ)) (hmat x)
    simpa only [QuotientGroup.mk_mul, hscalar, one_mul, aC, wC, nC] using
      congrArg (fun a : PGL2 ℂ => a * g) h
  let R : ℝ := ‖(u : ℂ)‖
  have hR : 0 < R := norm_pos_iff.mpr u.ne_zero
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hphase : ‖(R : ℂ) / (u : ℂ)‖ = 1 := by
    simp [R, u.ne_zero]
  let ρ : Circle := ⟨(R : ℂ) / (u : ℂ), mem_sphere_zero_iff_norm.mpr hphase⟩
  have hchange (x : ℂ) : x / (u : ℂ) = rotation ρ (R⁻¹ • x) := by
    change x / (u : ℂ) = (ρ : ℂ) * (R⁻¹ • x)
    rw [RCLike.real_smul_eq_coe_mul]
    dsimp only [ρ]
    rw [RCLike.ofReal_inv]
    change x / (u : ℂ) = (R : ℂ) / (u : ℂ) * ((R : ℂ)⁻¹ * x)
    field_simp [hRC, u.ne_zero]
  have hscale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E) :
      (∫ x : ℂ, F (x / (u : ℂ))) = (R ^ 2 : ℝ) • ∫ x : ℂ, F x := by
    calc
      (∫ x : ℂ, F (x / (u : ℂ))) = ∫ x : ℂ, F (rotation ρ (R⁻¹ • x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg F (hchange x))
      _ = (R ^ 2 : ℝ) • ∫ x : ℂ, F (rotation ρ x) := by
        simpa only [Complex.finrank_real_complex] using
          Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
            (fun x : ℂ => F (rotation ρ x)) hR.le
      _ = (R ^ 2 : ℝ) • ∫ x : ℂ, F x := by
        rw [MeasureTheory.integral_comp (rotation ρ) F]
  constructor
  · calc
      (∫ x : ℂ, f (aC u * wC * nC x * g)) =
          ∫ x : ℂ, f (wC * nC (x / (u : ℂ)) * aC u⁻¹ * g) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg f (hgroup x))
      _ = (‖(u : ℂ)‖ ^ 2 : ℝ) • intertwineC f (aC u⁻¹ * g) := by
        simpa only [R, intertwineC, mul_assoc] using
          hscale (fun x : ℂ => f (wC * nC x * aC u⁻¹ * g))
  · calc
      (∫ x : ℂ, ‖f (aC u * wC * nC x * g)‖) =
          ∫ x : ℂ, ‖f (wC * nC (x / (u : ℂ)) * aC u⁻¹ * g)‖ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a => ‖f a‖) (hgroup x))
      _ = ‖(u : ℂ)‖ ^ 2 * ∫ x : ℂ, ‖f (wC * nC x * aC u⁻¹ * g)‖ := by
        simpa only [R, smul_eq_mul] using
          hscale (fun x : ℂ => ‖f (wC * nC x * aC u⁻¹ * g)‖)

end ArtinPrimitiveRoots.A1.Theta
