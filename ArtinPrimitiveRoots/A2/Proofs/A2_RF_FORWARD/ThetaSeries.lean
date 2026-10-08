import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.ThetaMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1

theorem theta_series_majorant {ι : Type} [Countable ι]
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) (a : ι → ℂ) (w : ι → ℝ)
    (σ C : ℝ) (hC : 0 ≤ C)
    (hWeight : ∀ i, ‖a i‖ * q i ^ (-σ) ≤ w i) (hSum : Summable w)
    (V : ℝ → ℂ) (hV : Measurable V)
    (hBound : ∀ x : ℝ, 0 < x → ‖V x‖ ≤ C * x ^ (-σ))
    (K : ℝ → ℂ)
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Ioi (0 : ℝ))))
    (hMoment : IntegrableOn (fun t : ℝ => ‖K t‖ * t ^ (-σ) / t) (Set.Ioi 0)) :
    (∀ l : ℝ, 0 < l →
      Summable (fun i => ‖a i * V (q i * l)‖) ∧
      (∑' i, ‖a i * V (q i * l)‖) ≤ C * l ^ (-σ) * ∑' i, w i) ∧
    ∀ Z : ℝ, 0 < Z →
      IntegrableOn (fun t : ℝ => ‖K t‖ *
        (∑' i, ‖a i * V (q i * t / Z)‖) / t) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), ‖K t‖ *
        (∑' i, ‖a i * V (q i * t / Z)‖) / t) ≤
          C * Z ^ σ * Theta.absMoment K (-σ) * ∑' i, w i := by
  classical
  have hw (i : ι) : 0 ≤ w i :=
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hq i).le _)).trans (hWeight i)
  have hSeries (l : ℝ) (hl : 0 < l) :
      Summable (fun i => ‖a i * V (q i * l)‖) ∧
      (∑' i, ‖a i * V (q i * l)‖) ≤ C * l ^ (-σ) * ∑' i, w i := by
    let d : ι → ℝ := fun i => (C * l ^ (-σ)) * w i
    have hd : Summable d := hSum.mul_left (C * l ^ (-σ))
    have hle (i : ι) : ‖a i * V (q i * l)‖ ≤ d i := by
      rw [norm_mul]
      calc
        _ ≤ ‖a i‖ * (C * (q i * l) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (hBound _ (mul_pos (hq i) hl)) (norm_nonneg _)
        _ = (C * l ^ (-σ)) * (‖a i‖ * q i ^ (-σ)) := by
          rw [Real.mul_rpow (hq i).le hl.le]
          ring
        _ ≤ d i := mul_le_mul_of_nonneg_left (hWeight i)
          (mul_nonneg hC (Real.rpow_nonneg hl.le _))
    have hs : Summable (fun i => ‖a i * V (q i * l)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hd
    refine ⟨hs, ?_⟩
    calc
      _ ≤ ∑' i, d i := hs.tsum_le_tsum hle hd
      _ = C * l ^ (-σ) * ∑' i, w i := by
        dsimp only [d]
        rw [tsum_mul_left]
  refine ⟨hSeries, ?_⟩
  intro Z hZ
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let mass : ℝ := ∑' i, w i
  let g : ℝ → ℝ := fun t => ‖K t‖ * (∑' i, ‖a i * V (q i * t / Z)‖) / t
  let majorant : ℝ → ℝ := fun t =>
    (C * Z ^ σ * mass) * (‖K t‖ * t ^ (-σ) / t)
  have hTerm (i : ι) : Measurable (fun t : ℝ => ‖a i * V (q i * t / Z)‖) :=
    (measurable_const.mul
      (hV.comp ((measurable_const.mul measurable_id).div_const Z))).norm
  have hgMeas : AEStronglyMeasurable g ν := by
    have hInv : AEStronglyMeasurable (fun t : ℝ => t⁻¹) ν :=
      measurable_inv.aestronglyMeasurable
    have hEq : g = fun t : ℝ =>
        ‖K t‖ * (∑' i, ‖a i * V (q i * t / Z)‖) * t⁻¹ := by
      funext t
      exact div_eq_mul_inv _ _
    rw [hEq]
    exact (hK.norm.mul (Measurable.tsum hTerm).aestronglyMeasurable).mul hInv
  have hdom (t : ℝ) (ht : 0 < t) : 0 ≤ g t ∧ g t ≤ majorant t := by
    have hPow : (t / Z) ^ (-σ) = Z ^ σ * t ^ (-σ) := by
      rw [Real.div_rpow ht.le hZ.le, Real.rpow_neg hZ.le σ]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    have hAt := hSeries (t / Z) (div_pos ht hZ)
    have hMass : (∑' i, ‖a i * V (q i * t / Z)‖) ≤
        C * Z ^ σ * t ^ (-σ) * mass := by
      calc
        _ = ∑' i, ‖a i * V (q i * (t / Z))‖ := by
          apply tsum_congr
          intro i
          rw [mul_div_assoc]
        _ ≤ C * (t / Z) ^ (-σ) * ∑' i, w i := hAt.2
        _ = C * Z ^ σ * t ^ (-σ) * mass := by
          rw [hPow]
          dsimp only [mass]
          ring
    constructor
    · exact div_nonneg (mul_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))) ht.le
    · calc
        g t = (‖K t‖ / t) * (∑' i, ‖a i * V (q i * t / Z)‖) := by
          dsimp only [g]
          ring
        _ ≤ (‖K t‖ / t) * (C * Z ^ σ * t ^ (-σ) * mass) :=
          mul_le_mul_of_nonneg_left hMass (div_nonneg (norm_nonneg _) ht.le)
        _ = majorant t := by
          dsimp only [majorant]
          ring
  have hMajorant : Integrable majorant ν := hMoment.const_mul (C * Z ^ σ * mass)
  have hg : Integrable g ν := by
    apply hMajorant.mono' hgMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hdom t ht).1]
    exact (hdom t ht).2
  refine ⟨hg, ?_⟩
  change (∫ t, g t ∂ν) ≤ C * Z ^ σ * Theta.absMoment K (-σ) * mass
  calc
    _ ≤ ∫ t, majorant t ∂ν := by
      apply integral_mono_ae hg hMajorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hdom t ht).2
    _ = C * Z ^ σ * Theta.absMoment K (-σ) * mass := by
      dsimp only [majorant, ν]
      rw [integral_const_mul]
      unfold Theta.absMoment
      ring

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
