import ArtinPrimitiveRoots.Theta.Shared
import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem bessel_cubic_eq_prebuilt (x : ℝ) (hx : 0 < x) :
    (besselK (1 / 3) x : ℂ) = OAI.CubicEisenstein.schlafliBesselK (1 / 3) x := by
  rw [besselK_eq_schlafli (1 / 3) x hx,
    OAI.CubicEisenstein.schlafliBesselK_cubic_real x hx]
  rw [show -(1 / 3 : ℝ) = -(1 : ℝ) / 3 by ring]
  congr 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [OAI.CubicEisenstein.cubicBesselDensity]
  congr 1
  congr 1
  ring

/-- The local radial factor in thetaV has a convergent Mellin integral on the exact
half-plane required by gaussian_smoothing. -/
theorem bessel_radial_hasMellin (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    HasMellin (fun t : ℝ => (t : ℂ) * (besselK (1 / 3) (c * Real.sqrt t) : ℂ)) s
      ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  let f : ℝ → ℂ := OAI.CubicEisenstein.schlafliBesselK (1 / 3)
  let g : ℝ → ℂ := fun t => (t : ℂ) * f (c * Real.sqrt t)
  have hs' : (1 / 3 : ℝ) < (2 * s + 2).re := by
    norm_num
    linarith
  have hparam : (s + 1) / ((1 / 2 : ℝ) : ℂ) = 2 * s + 2 := by
    push_cast
    ring
  have hf : MellinConvergent f (2 * s + 2) :=
    OAI.CubicEisenstein.schlafliBesselK_cubic_mellin_integrable (2 * s + 2) hs'
  have hg : MellinConvergent g s := by
    have hscale : MellinConvergent (fun t => f (c * t)) (2 * s + 2) :=
      (MellinConvergent.comp_mul_left hc).2 hf
    have hhalf : MellinConvergent (fun t => f (c * t ^ (1 / 2 : ℝ))) (s + 1) :=
      (MellinConvergent.comp_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)).2 (hparam ▸ hscale)
    simpa only [g, Real.sqrt_eq_rpow, Complex.cpow_one, smul_eq_mul] using
      (MellinConvergent.cpow_smul (a := 1)).2 hhalf
  have heq : ∀ t ∈ Set.Ioi (0 : ℝ),
      (t : ℂ) * (besselK (1 / 3) (c * Real.sqrt t) : ℂ) = g t := by
    intro t ht
    dsimp only [g, f]
    rw [bessel_cubic_eq_prebuilt _ (mul_pos hc (Real.sqrt_pos.mpr ht))]
  refine ⟨?_, ?_⟩
  · apply hg.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [smul_eq_mul]
    rw [heq t ht]
  · have hbase : mellin f (2 * s + 2) =
        (2 : ℂ) ^ (2 * s) * Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
      have hh := OAI.CubicEisenstein.schlafliBesselK_cubic_mellin (2 * s + 2) hs'
      have h₁ : ((2 * s + 2) - 1 / 3) / 2 = s + (5 / 6 : ℂ) := by ring
      have h₂ : ((2 * s + 2) + 1 / 3) / 2 = s + (7 / 6 : ℂ) := by ring
      simpa only [mellin, f, smul_eq_mul, h₁, h₂,
        show 2 * s + 2 - 2 = 2 * s by ring] using hh
    calc
      mellin (fun t : ℝ => (t : ℂ) * (besselK (1 / 3) (c * Real.sqrt t) : ℂ)) s =
          mellin g s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [heq t ht]
      _ = mellin (fun t => f (c * Real.sqrt t)) (s + 1) := by
        simpa only [g, Complex.cpow_one, smul_eq_mul] using
          mellin_cpow_smul (fun t => f (c * Real.sqrt t)) s 1
      _ = (2 : ℝ) • mellin (fun t => f (c * t)) (2 * s + 2) := by
        have hh := mellin_comp_rpow (fun t => f (c * t)) (s + 1) (1 / 2 : ℝ)
        simpa only [← Real.sqrt_eq_rpow, hparam,
          show |(1 / 2 : ℝ)|⁻¹ = 2 by norm_num] using hh
      _ = (2 : ℂ) * (c : ℂ) ^ (-(2 * s + 2)) * mellin f (2 * s + 2) := by
        rw [mellin_comp_mul_left f _ hc]
        simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_ofNat]
        ring
      _ = _ := by
        rw [hbase, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
        rw [show -2 * s - 2 = -(2 * s + 2) by ring]
        ring

end ArtinPrimitiveRoots.Proofs.thsol_smooth
