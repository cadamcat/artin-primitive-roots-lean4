import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Interval Topology
open Filter MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Sixth-power weight decay overcomes cubic logarithmic-derivative growth on unit-bin heights. -/
theorem horizontal_integral_tendsto_zero (L W : ℂ → ℂ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (a T : ℕ → ℝ)
    (hT : ∀ n : ℕ, T n ∈ Set.Icc (a n) (a n + 1))
    (ha : Tendsto (fun n : ℕ => |a n|) atTop atTop)
    (hL : ∀ (n : ℕ) (σ : ℝ), σ ∈ Set.Icc (-1 / 2 : ℝ) 2 →
      ‖L ((σ : ℂ) + (T n : ℂ) * Complex.I)‖ ≤ A * (|a n| + 4) ^ 3)
    (hW : ∀ s : ℂ, (-1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖W s‖ ≤ C * Real.rpow (1 + |s.im|) (-6 : ℝ)) :
    Tendsto (fun n : ℕ => ∫ σ : ℝ in (-1 / 2 : ℝ)..2,
      L ((σ : ℂ) + (T n : ℂ) * Complex.I) *
        W ((σ : ℂ) + (T n : ℂ) * Complex.I)) atTop (𝓝 (0 : ℂ)) := by
  let u : ℕ → ℝ := fun n => 1 + |a n|
  let v : ℕ → ℝ := fun n => 1 + |T n|
  have hup (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hvp (n : ℕ) : 0 < v n := by dsimp [v]; positivity
  have huv (n : ℕ) : u n ≤ 2 * v n := by
    have hclose : |a n - T n| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [(hT n).1, (hT n).2]
    have habs := abs_sub_le (a n) (T n) 0
    simp only [sub_zero] at habs
    dsimp [u, v]
    linarith [abs_nonneg (T n)]
  have hpoly (n : ℕ) : (|a n| + 4) ^ 3 ≤ 64 * (u n) ^ 3 := by
    calc
      _ ≤ (4 * u n) ^ 3 := by
        gcongr <;> dsimp [u] <;> linarith [abs_nonneg (a n)]
      _ = _ := by ring
  have htwo : Real.rpow (2 : ℝ) (-6 : ℝ) = (1 / 64 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    norm_num
  have hdecay (n : ℕ) : Real.rpow (v n) (-6 : ℝ) ≤ 64 * Real.rpow (u n) (-6 : ℝ) := by
    calc
      _ ≤ Real.rpow (u n / 2) (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (div_pos (hup n) (by norm_num))
          (by linarith [huv n]) (by norm_num)
      _ = _ := by
        simp only [Real.rpow_eq_pow] at htwo ⊢
        rw [Real.div_rpow (hup n).le (by norm_num : (0 : ℝ) ≤ 2) (-6), htwo]
        ring
  have hprod (n : ℕ) : (u n) ^ 3 * Real.rpow (u n) (-6 : ℝ) =
      Real.rpow (u n) (-3 : ℝ) := by
    calc
      _ = Real.rpow (u n) (3 : ℝ) * Real.rpow (u n) (-6 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_ofNat (u n) 3]
      _ = Real.rpow (u n) ((3 : ℝ) + (-6)) := (Real.rpow_add (hup n) _ _).symm
      _ = _ := by norm_num
  have hpoint (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 2) :
      ‖L ((σ : ℂ) + (T n : ℂ) * Complex.I) *
        W ((σ : ℂ) + (T n : ℂ) * Complex.I)‖ ≤
      (A * (|a n| + 4) ^ 3) * (C * Real.rpow (v n) (-6 : ℝ)) := by
    have hWi := hW ((σ : ℂ) + (T n : ℂ) * Complex.I)
      (by simpa using hσ.1) (by simpa using hσ.2)
    have hWi' : ‖W ((σ : ℂ) + (T n : ℂ) * Complex.I)‖ ≤
        C * Real.rpow (v n) (-6 : ℝ) := by simpa [v] using hWi
    rw [norm_mul]
    exact mul_le_mul (hL n σ hσ) hWi' (norm_nonneg _) (by positivity)
  have hwidth : |(2 : ℝ) - (-1 / 2)| = (5 / 2 : ℝ) := by norm_num
  have hraw (n : ℕ) :
      ‖∫ σ : ℝ in (-1 / 2 : ℝ)..2,
        L ((σ : ℂ) + (T n : ℂ) * Complex.I) *
          W ((σ : ℂ) + (T n : ℂ) * Complex.I)‖ ≤
      ((A * (|a n| + 4) ^ 3) * (C * Real.rpow (v n) (-6 : ℝ))) * (5 / 2) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 / 2 : ℝ)) (b := (2 : ℝ))
      (f := fun σ : ℝ => L ((σ : ℂ) + (T n : ℂ) * Complex.I) *
        W ((σ : ℂ) + (T n : ℂ) * Complex.I)) (fun σ hσ => by
          rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hσ
          exact hpoint n σ ⟨hσ.1.le, hσ.2⟩)
    simpa only [hwidth] using h
  have hbound (n : ℕ) :
      ‖∫ σ : ℝ in (-1 / 2 : ℝ)..2,
        L ((σ : ℂ) + (T n : ℂ) * Complex.I) *
          W ((σ : ℂ) + (T n : ℂ) * Complex.I)‖ ≤
      10240 * A * C * Real.rpow (u n) (-3 : ℝ) := by
    calc
      _ ≤ ((A * (|a n| + 4) ^ 3) * (C * Real.rpow (v n) (-6 : ℝ))) * (5 / 2) := hraw n
      _ ≤ ((A * (64 * (u n) ^ 3)) * (C * (64 * Real.rpow (u n) (-6 : ℝ)))) * (5 / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hpoly n) hA)
          (mul_le_mul_of_nonneg_left (hdecay n) hC)
          (mul_nonneg hC (Real.rpow_nonneg (hvp n).le _))
          (mul_nonneg hA (mul_nonneg (by norm_num) (pow_nonneg (hup n).le _)))
      _ = 10240 * A * C * ((u n) ^ 3 * Real.rpow (u n) (-6 : ℝ)) := by ring
      _ = _ := by rw [hprod n]
  have huTop : Tendsto u atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [u]; linarith) ha
  have hpow : Tendsto (fun n : ℕ => Real.rpow (u n) (-3 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp huTop
  have hconst : Tendsto (fun _ : ℕ => 10240 * A * C) atTop (𝓝 (10240 * A * C)) :=
    tendsto_const_nhds
  have hsmall : Tendsto (fun n : ℕ => 10240 * A * C * Real.rpow (u n) (-3 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hconst.mul hpow
  exact squeeze_zero_norm hbound hsmall

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
