import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.zf_conv_sol

/-- The two real-place parities have a common polynomial left-line Gamma bound.
The height exponent is fixed before the strip width is chosen. -/
theorem gammaR_left_ratio (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : Fin 2, ∀ t : ℝ,
      ‖Complex.Gammaℝ (((1 + δ + (e.val : ℝ) : ℝ) : ℂ) - t * Complex.I) /
        Complex.Gammaℝ (((-δ + (e.val : ℝ) : ℝ) : ℂ) + t * Complex.I)‖ ≤
          C * (2 + |t|) ^ (2 : ℕ) := by
  classical
  have hparity : ∀ e : Fin 2, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (((1 + δ + (e.val : ℝ) : ℝ) : ℂ) - t * Complex.I) /
        Complex.Gammaℝ (((-δ + (e.val : ℝ) : ℝ) : ℂ) + t * Complex.I)‖ ≤
          C * (2 + |t|) ^ (2 : ℕ) := by
    intro e
    let a : ℝ := (1 + δ + (e.val : ℝ)) / 2
    let b : ℝ := (-δ + (e.val : ℝ)) / 2
    let q : ℝ := (1 + 2 * (e.val : ℝ)) / 4
    let σ : ℝ := (1 + 2 * δ) / 4
    let R : ℝ := Real.Gamma a / Real.Gamma (b + 2)
    let B : ℝ := |b| + 2
    let D : ℝ := Real.rpow Real.pi (-(1 + 2 * δ) / 2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b + 2 := by
      dsimp [b]
      have he : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
      linarith
    have hR : 0 < R := div_pos (Real.Gamma_pos_of_pos ha)
      (Real.Gamma_pos_of_pos hb)
    have hB : 0 < B := by dsimp [B]; positivity
    have hD : 0 < D := Real.rpow_pos_of_pos Real.pi_pos _
    refine ⟨D * B ^ 2 * R, by positivity, ?_⟩
    intro t
    let u : ℂ := ((1 + δ + (e.val : ℝ) : ℝ) : ℂ) - t * Complex.I
    let v : ℂ := ((-δ + (e.val : ℝ) : ℝ) : ℂ) + t * Complex.I
    have hu : u / 2 = (a : ℂ) - (t / 2 : ℝ) * Complex.I := by
      dsimp [u, a]
      push_cast
      ring
    have hv : v / 2 = (b : ℂ) + (t / 2 : ℝ) * Complex.I := by
      dsimp [v, b]
      push_cast
      ring
    have hpair := OAI.CubicReflectionKernel.Gamma_shifted_pair_bound
      q σ (-t / 2) 2 (by dsimp [q, σ]; positivity)
      (by dsimp [σ]; norm_num; linarith)
    have hpnum : (q : ℂ) + ((σ : ℂ) + (-t / 2 : ℝ) * Complex.I) = u / 2 := by
      dsimp [q, σ, u]
      push_cast
      ring
    have hpden : (q : ℂ) - ((σ : ℂ) + (-t / 2 : ℝ) * Complex.I) + 2 =
        v / 2 + 2 := by
      dsimp [q, σ, v]
      push_cast
      ring
    have hpA : q + σ = a := by dsimp [q, σ, a]; ring
    have hpB : q - σ + 2 = b + 2 := by dsimp [q, σ, b]; ring
    have hratio : ‖Complex.Gamma (u / 2) / Complex.Gamma (v / 2 + 2)‖ ≤ R := by
      simpa only [Nat.cast_ofNat, hpnum, hpden, hpA, hpB, R] using hpair
    have hvnorm : ‖v / 2‖ ≤ |b| + |t| / 2 := by
      rw [hv]
      simpa [norm_mul, abs_div] using
        (norm_add_le (b : ℂ) ((t / 2 : ℝ) * Complex.I))
    have hvbound : ‖v / 2‖ + 2 ≤ B * (2 + |t|) := by
      dsimp [B]
      nlinarith [abs_nonneg b, abs_nonneg t]
    have hprod : ‖∏ k ∈ Finset.range 2, (v / 2 + (k : ℂ))‖ ≤
        B ^ 2 * (2 + |t|) ^ (2 : ℕ) := by
      have h := OAI.CubicReflectionKernel.norm_Gamma_shift_factor (v / 2) 2
      refine h.trans ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hvbound 2
    have hgam : Complex.Gamma (u / 2) / Complex.Gamma (v / 2) =
        (∏ k ∈ Finset.range 2, (v / 2 + (k : ℂ))) *
          (Complex.Gamma (u / 2) / Complex.Gamma (v / 2 + 2)) := by
      rw [div_eq_mul_inv,
        OAI.CubicReflectionKernel.inverse_Gamma_shift (v / 2) 2, div_eq_mul_inv]
      ring
    have hgamBound : ‖Complex.Gamma (u / 2) / Complex.Gamma (v / 2)‖ ≤
        B ^ 2 * (2 + |t|) ^ (2 : ℕ) * R := by
      rw [hgam, norm_mul]
      exact mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    have hpiU : ‖(Real.pi : ℂ) ^ (-u / 2)‖ =
        Real.rpow Real.pi (-(1 + δ + (e.val : ℝ)) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      simp [u]
    have hpiV : ‖(Real.pi : ℂ) ^ (-v / 2)‖ =
        Real.rpow Real.pi (-(-δ + (e.val : ℝ)) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      simp [v]
    have hpiRatio :
        Real.rpow Real.pi (-(1 + δ + (e.val : ℝ)) / 2) /
          Real.rpow Real.pi (-(-δ + (e.val : ℝ)) / 2) = D := by
      dsimp [D]
      rw [Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos Real.pi_pos,
        Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_sub]
      congr 1 <;> ring
    have hreal : ‖Complex.Gammaℝ u / Complex.Gammaℝ v‖ =
        D * ‖Complex.Gamma (u / 2) / Complex.Gamma (v / 2)‖ := by
      simp only [Complex.Gammaℝ_def, norm_div, norm_mul, hpiU, hpiV]
      rw [mul_div_mul_comm, hpiRatio]
    change ‖Complex.Gammaℝ u / Complex.Gammaℝ v‖ ≤ _
    rw [hreal]
    calc
      _ ≤ D * (B ^ 2 * (2 + |t|) ^ (2 : ℕ) * R) :=
        mul_le_mul_of_nonneg_left hgamBound hD.le
      _ = _ := by ring
  choose C hC hbound using hparity
  refine ⟨∑ e : Fin 2, C e, Finset.sum_pos (fun e _ => hC e) Finset.univ_nonempty, ?_⟩
  intro e t
  have hle : C e ≤ ∑ e : Fin 2, C e :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ e)
  exact (hbound e t).trans
    (mul_le_mul_of_nonneg_right hle (by positivity))

end ArtinPrimitiveRoots.Proofs.zf_conv_sol
