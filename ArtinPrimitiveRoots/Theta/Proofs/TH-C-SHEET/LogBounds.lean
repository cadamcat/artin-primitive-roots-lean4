import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogProfile
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
noncomputable section

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

theorem th_c_sheet_log_bounds (m : ℤ) (hm : m = 1 ∨ m = -1) (c : ℂ)
    (hctrl : ∀ j : ℕ, ∃ E F : ℝ, 0 ≤ E ∧ 0 ≤ F ∧
      (∀ x : ℝ, 0 < x → ‖iteratedDeriv j (cubicLogProfile 1 x) 0‖ ≤
        E * x ^ (-(1 / 3 : ℝ))) ∧
      (∀ x : ℝ, 1 ≤ x → ‖iteratedDeriv j (cubicLogProfile 1 x) 0‖ ≤
        F * Real.exp (-x / 4))) :
    ∀ (j : ℕ) (A : ℝ), 0 < A → ∃ C : ℝ, ∀ y : ℂ, y ≠ 0 →
      ‖normDeriv j (fun y : ℂ => c * (Complex.normSq y : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) y‖ ≤
          C * min (Complex.normSq y ^ (1 / 3 : ℝ)) (Complex.normSq y ^ (-A)) := by
  intro j A hA
  obtain ⟨E, F, hE, hF, hsmall, hlarge⟩ := hctrl j
  let κ : ℝ := 4 * Real.pi
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hcurve (y : ℂ) (hy : y ≠ 0) :
      (fun t : ℝ => c * (Complex.normSq ((Real.exp (t / 2) : ℂ) * y) : ℂ) *
        omegaAng m ((Real.exp (t / 2) : ℂ) * y) *
        (besselK (1 / 3) (4 * Real.pi * ‖(Real.exp (t / 2) : ℂ) * y‖) : ℂ)) =
      (fun t : ℝ => cubicLogProfile 1 (κ * ‖y‖) t •
        (c * (Complex.normSq y : ℂ) * omegaAng m y)) := by
    funext t
    let b : ℝ := Real.exp (t / 2)
    have hb : 0 < b := Real.exp_pos _
    have hn : ‖(b : ℂ) * y‖ = b * ‖y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
    have he : b * b = Real.exp t := by
      dsimp only [b]
      rw [← Real.exp_add]
      congr 1
      ring
    have hsq : Complex.normSq ((b : ℂ) * y) = Real.exp t * Complex.normSq y := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal, he]
    have ha : omegaAng m ((b : ℂ) * y) = omegaAng m y := by
      unfold omegaAng
      rw [hn, Complex.ofReal_mul]
      have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
      have hy' : (‖y‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
      congr 1
      field_simp
    change c * (Complex.normSq ((b : ℂ) * y) : ℂ) * omegaAng m ((b : ℂ) * y) *
      (besselK (1 / 3) (4 * Real.pi * ‖(b : ℂ) * y‖) : ℂ) = _
    rw [hsq, ha, hn]
    simp only [cubicLogProfile, one_mul, Complex.real_smul, Complex.ofReal_mul]
    have hx : 4 * Real.pi * (b * ‖y‖) = κ * ‖y‖ * Real.exp (t / 2) := by
      dsimp only [κ, b]
      ring
    rw [hx]
    ring
  have hnorm (y : ℂ) (hy : y ≠ 0) :
      ‖normDeriv j (fun y : ℂ => c * (Complex.normSq y : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) y‖ =
      ‖iteratedDeriv j (cubicLogProfile 1 (κ * ‖y‖)) 0‖ * (‖c‖ * ‖y‖ ^ 2) := by
    have hs : ContDiff ℝ j (cubicLogProfile 1 (κ * ‖y‖)) :=
      ((bessel_cubic_log_control.2 1).1 (κ * ‖y‖)
        (mul_pos hκ (norm_pos_iff.mpr hy))).of_le (by simp)
    have ha : ‖omegaAng m y‖ = 1 := by
      rw [omegaAng, norm_zpow, norm_div, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg y), div_self (norm_ne_zero_iff.mpr hy), one_zpow]
    rw [normDeriv, hcurve y hy, iteratedDeriv_smul_const hs.contDiffAt, norm_smul]
    simp only [norm_mul, ha, Complex.norm_real,
      mul_one, Complex.normSq_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg ‖y‖)]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * A + 2)
  let D : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hexp (r : ℝ) (hr : 1 ≤ r) :
      r ^ (2 * A + 2) * Real.exp (-Real.pi * r) ≤ D := by
    have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hp : r ^ (2 * A + 2) ≤ r ^ n := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hr hn.le
    have hpow : (Real.pi * r) ^ n ≤ Real.exp (Real.pi * r) * (n.factorial : ℝ) :=
      (div_le_iff₀ hfact).mp
        (Real.pow_div_factorial_le_exp (Real.pi * r) (by positivity) n)
    have he : Real.exp (Real.pi * r) * Real.exp (-Real.pi * r) = 1 := by
      rw [← Real.exp_add]
      simp
    have hbound : (Real.pi * r) ^ n * Real.exp (-Real.pi * r) ≤ n.factorial := by
      calc
        (Real.pi * r) ^ n * Real.exp (-Real.pi * r) ≤
            (Real.exp (Real.pi * r) * (n.factorial : ℝ)) * Real.exp (-Real.pi * r) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ = n.factorial := by
          calc
            _ = (n.factorial : ℝ) *
                (Real.exp (Real.pi * r) * Real.exp (-Real.pi * r)) := by ring
            _ = _ := by rw [he, mul_one]
    change r ^ (2 * A + 2) * Real.exp (-Real.pi * r) ≤ (n.factorial : ℝ) / Real.pi ^ n
    apply (le_div_iff₀ (pow_pos Real.pi_pos n)).mpr
    calc
      (r ^ (2 * A + 2) * Real.exp (-Real.pi * r)) * Real.pi ^ n ≤
          (r ^ n * Real.exp (-Real.pi * r)) * Real.pi ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (pow_nonneg Real.pi_pos.le n)
      _ = (Real.pi * r) ^ n * Real.exp (-Real.pi * r) := by rw [mul_pow]; ring
      _ ≤ _ := hbound
  let Cs : ℝ := ‖c‖ * E * κ ^ (-(1 / 3 : ℝ))
  let Cl : ℝ := ‖c‖ * F * D
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hCl : 0 ≤ Cl := by dsimp only [Cl]; positivity
  refine ⟨max Cs Cl, ?_⟩
  intro y hy
  let r : ℝ := ‖y‖
  have hr : 0 < r := norm_pos_iff.mpr hy
  have hx : 0 < κ * r := mul_pos hκ hr
  rw [hnorm y hy, Complex.normSq_eq_norm_sq]
  change ‖iteratedDeriv j (cubicLogProfile 1 (κ * r)) 0‖ * (‖c‖ * r ^ 2) ≤
    max Cs Cl * min ((r ^ 2) ^ (1 / 3 : ℝ)) ((r ^ 2) ^ (-A))
  by_cases hr1 : r ≤ 1
  · have hmin : min ((r ^ 2) ^ (1 / 3 : ℝ)) ((r ^ 2) ^ (-A)) =
        (r ^ 2) ^ (1 / 3 : ℝ) := by
      apply min_eq_left
      apply Real.rpow_le_rpow_of_exponent_ge (sq_pos_of_pos hr)
        (by nlinarith) (by linarith)
    have hscale : r ^ 2 * (κ * r) ^ (-(1 / 3 : ℝ)) =
        κ ^ (-(1 / 3 : ℝ)) * r ^ (5 / 3 : ℝ) := by
      calc
        r ^ 2 * (κ * r) ^ (-(1 / 3 : ℝ)) =
            κ ^ (-(1 / 3 : ℝ)) * (r ^ (2 : ℝ) * r ^ (-(1 / 3 : ℝ))) := by
          rw [Real.mul_rpow hκ.le hr.le, Real.rpow_two]
          ring
        _ = κ ^ (-(1 / 3 : ℝ)) * r ^ ((2 : ℝ) + -(1 / 3 : ℝ)) := by
          rw [Real.rpow_add hr]
        _ = _ := by norm_num
    rw [hmin]
    calc
      ‖iteratedDeriv j (cubicLogProfile 1 (κ * r)) 0‖ * (‖c‖ * r ^ 2) ≤
          (E * (κ * r) ^ (-(1 / 3 : ℝ))) * (‖c‖ * r ^ 2) :=
        mul_le_mul_of_nonneg_right (hsmall (κ * r) hx) (by positivity)
      _ = Cs * r ^ (5 / 3 : ℝ) := by
        calc
          _ = (‖c‖ * E) * (r ^ 2 * (κ * r) ^ (-(1 / 3 : ℝ))) := by ring
          _ = _ := by rw [hscale]; dsimp only [Cs]; ring
      _ ≤ Cs * r ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)) hCs
      _ = Cs * (r ^ 2) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast_mul hr.le 2]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left Cs Cl) (Real.rpow_nonneg (sq_nonneg r) _)
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hxr : 1 ≤ κ * r := by
      apply le_trans (show 1 ≤ κ by dsimp only [κ]; linarith [Real.two_le_pi])
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1' hκ.le
    have hmin : min ((r ^ 2) ^ (1 / 3 : ℝ)) ((r ^ 2) ^ (-A)) = (r ^ 2) ^ (-A) := by
      apply min_eq_right
      apply Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)
    have hcancel : r ^ (2 * A + 2) * (r ^ 2) ^ (-A) = r ^ 2 := by
      rw [← Real.rpow_natCast_mul hr.le 2, ← Real.rpow_add hr]
      convert Real.rpow_natCast r 2 using 1 <;> ring
    have hdecay : r ^ 2 * Real.exp (-Real.pi * r) ≤ D * (r ^ 2) ^ (-A) := by
      calc
        r ^ 2 * Real.exp (-Real.pi * r) =
            (r ^ (2 * A + 2) * Real.exp (-Real.pi * r)) * (r ^ 2) ^ (-A) := by
          conv_lhs => rw [← hcancel]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hexp r hr1') (Real.rpow_nonneg (sq_nonneg r) _)
    rw [hmin]
    calc
      ‖iteratedDeriv j (cubicLogProfile 1 (κ * r)) 0‖ * (‖c‖ * r ^ 2) ≤
          (F * Real.exp (-(κ * r) / 4)) * (‖c‖ * r ^ 2) :=
        mul_le_mul_of_nonneg_right (hlarge (κ * r) hxr) (by positivity)
      _ = (‖c‖ * F) * (r ^ 2 * Real.exp (-Real.pi * r)) := by
        rw [show -(κ * r) / 4 = -Real.pi * r by dsimp only [κ]; ring]
        ring
      _ ≤ (‖c‖ * F) * (D * (r ^ 2) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = Cl * (r ^ 2) ^ (-A) := by dsimp only [Cl]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right Cs Cl) (Real.rpow_nonneg (sq_nonneg r) _)

end ArtinPrimitiveRoots.Proofs.thsol_smooth
