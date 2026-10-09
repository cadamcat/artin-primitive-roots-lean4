import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- A positive real complex-power weight preserves entirety and strip decay. -/
theorem cpow_weight_entire_decay (M : ℂ → ℂ)
    (hentire : Differentiable ℂ M)
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖M s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (x : ℝ) (hx : 2 ≤ x) :
    Differentiable ℂ (fun s : ℂ => Complex.cpow (x : ℂ) s * M s) ∧
    ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖Complex.cpow (x : ℂ) s * M s‖ ≤
          C * Real.rpow (1 + |s.im|) (-(A : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hcx : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  letI : NeZero (x : ℂ) := ⟨hcx⟩
  refine ⟨(differentiable_const_cpow_of_neZero (x : ℂ)).mul hentire, ?_⟩
  intro A a b hab
  obtain ⟨D, hDpos, hD⟩ := hdecay A a b hab
  refine ⟨D * Real.rpow x b, mul_pos hDpos (Real.rpow_pos_of_pos hxpos b), ?_⟩
  intro s ha hb
  have hpow : Real.rpow x s.re ≤ Real.rpow x b :=
    Real.rpow_le_rpow_of_exponent_le hxone hb
  have hnonneg : 0 ≤ Real.rpow (1 + |s.im|) (-(A : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hcpow : ‖Complex.cpow (x : ℂ) s‖ = Real.rpow x s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos s
  calc
    ‖Complex.cpow (x : ℂ) s * M s‖ = Real.rpow x s.re * ‖M s‖ := by
      rw [norm_mul, hcpow]
    _ ≤ Real.rpow x s.re * (D * Real.rpow (1 + |s.im|) (-(A : ℝ))) :=
      mul_le_mul_of_nonneg_left (hD s ha hb) (Real.rpow_nonneg hxpos.le _)
    _ ≤ Real.rpow x b * (D * Real.rpow (1 + |s.im|) (-(A : ℝ))) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg hDpos.le hnonneg)
    _ = D * Real.rpow x b * Real.rpow (1 + |s.im|) (-(A : ℝ)) := by ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
