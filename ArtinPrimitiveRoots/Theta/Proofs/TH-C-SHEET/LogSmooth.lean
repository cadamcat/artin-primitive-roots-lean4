import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogProfile
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

theorem th_c_sheet_log_smooth (m : ℤ) (hm : m = 1 ∨ m = -1) (c : ℂ)
    (hK : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (besselK (1 / 3)) (Set.Ioi 0)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => c * (Complex.normSq y : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) {y | y ≠ 0} := by
  let D : Set ℂ := {y | y ≠ 0}
  have hn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => ‖y‖) D :=
    contDiffOn_id.norm ℂ (fun y hy => hy)
  have hnc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => (‖y‖ : ℂ)) D := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hn
  have hne (y : ℂ) (hy : y ∈ D) : (‖y‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => Complex.normSq y) D := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (contDiff_norm_sq ℂ (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (E := ℂ)).contDiffOn (s := D)
  have hsc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => (Complex.normSq y : ℂ)) D := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hs
  have hx : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => 4 * Real.pi * ‖y‖) D := contDiffOn_const.mul hn
  have hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => besselK (1 / 3) (4 * Real.pi * ‖y‖)) D := by
    apply hK.comp hx
    intro y hy
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr hy)
  have hbc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) D := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hb
  have ha : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ => y / (‖y‖ : ℂ)) D := by
    have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => y) D := contDiffOn_id
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hid.mul (hnc.inv hne)
  have hang : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (omegaAng m) D := by
    rcases hm with rfl | rfl
    · change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => (y / (‖y‖ : ℂ)) ^ (1 : ℤ)) D
      simpa only [zpow_one] using ha
    · change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => (y / (‖y‖ : ℂ)) ^ (-1 : ℤ)) D
      simpa only [zpow_neg_one] using
        ha.fun_inv (fun y hy => div_ne_zero hy (hne y hy))
  exact ((contDiffOn_const.mul hsc).mul hang).mul hbc

end ArtinPrimitiveRoots.Proofs.thsol_smooth
