import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Heights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HadamardTail

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Every unit height interval has a nonzero xi line with cubic logarithmic-derivative growth. -/
theorem xi_good_height (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, ∃ T : ℝ,
      T ∈ Set.Icc a (a + 1) ∧
      (∀ s : ℂ, s.im = T → dedekindXi K s ≠ 0) ∧
      ∀ σ : ℝ, σ ∈ Set.Icc (-1 / 2 : ℝ) 2 →
        ‖deriv (dedekindXi K) ((σ : ℂ) + T * Complex.I) /
          dedekindXi K ((σ : ℂ) + T * Complex.I)‖ ≤ A * (|a| + 4) ^ 3 := by
  obtain ⟨c, hc, hgap⟩ := zero_ordinates_gap K
  obtain ⟨C, hC, hbound⟩ := xi_logderiv_bound K
  let A : ℝ := C * (2 + 1 / c)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro a
  obtain ⟨T, hT, hsepIm⟩ := hgap a
  let ε : ℝ := c / (1 + |a|)
  have hbase : 0 < 1 + |a| := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsep (s : ℂ) (hs : s.im = T) (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) :
      ε ≤ ‖s - ρ‖ := by
    calc
      ε ≤ |T - ρ.im| := hsepIm ρ hρ
      _ = |(s - ρ).im| := by rw [Complex.sub_im, hs]
      _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
  have hnz (s : ℂ) (hs : s.im = T) : dedekindXi K s ≠ 0 := by
    intro hz
    have h := hsep s hs s ((xi_zero_dictionary K).1 s |>.mp hz)
    simp only [sub_self, norm_zero] at h
    exact not_le_of_gt hε h
  refine ⟨T, hT, hnz, ?_⟩
  intro σ hσ
  let s : ℂ := (σ : ℂ) + T * Complex.I
  have hs : s.im = T := by simp [s]
  have hTabs : |T| ≤ |a| + 1 := by
    apply abs_le.mpr
    constructor
    · linarith [hT.1, neg_abs_le a]
    · linarith [hT.2, le_abs_self a]
  have hσabs : |σ| ≤ 2 := by
    exact abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
  let r : ℝ := |a| + 4
  have hr₄ : 4 ≤ r := by dsimp [r]; linarith [abs_nonneg a]
  have hr : 0 ≤ r := by linarith
  have hnorm : ‖s‖ ≤ r := by
    calc
      ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + |T| := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ r := by dsimp [r]; linarith
  have hbr : 1 + |a| ≤ r := by dsimp [r]; linarith
  have hquot : ‖s‖ / ε ≤ r ^ 2 / c := by
    calc
      ‖s‖ / ε = ‖s‖ * (1 + |a|) / c := by
        dsimp [ε]
        field_simp [hc.ne', hbase.ne'] <;> ring
      _ ≤ r * r / c := div_le_div_of_nonneg_right
        (mul_le_mul hnorm hbr hbase.le hr) hc.le
      _ = r ^ 2 / c := by ring
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  have hcube : r ≤ r ^ 3 := by
    calc
      r = r * 1 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hsq hr
      _ = r ^ 3 := by ring
  have hone : 1 ≤ r ^ 3 := le_trans (by linarith) hcube
  have hlinear : 1 + r ≤ 2 * r ^ 3 := by linarith
  have hquot₁ : 1 + ‖s‖ / ε ≤ 1 + r ^ 2 / c := by linarith only [hquot]
  have hprod : ‖s‖ * (1 + ‖s‖ / ε) ≤ r * (1 + r ^ 2 / c) :=
    mul_le_mul hnorm hquot₁ (by positivity) hr
  have hpoly : 1 + ‖s‖ * (1 + ‖s‖ / ε) ≤ (2 + 1 / c) * r ^ 3 := by
    calc
      _ ≤ 1 + r * (1 + r ^ 2 / c) := by linarith only [hprod]
      _ = 1 + r + r ^ 3 / c := by ring
      _ ≤ 2 * r ^ 3 + r ^ 3 / c := by linarith only [hlinear]
      _ = (2 + 1 / c) * r ^ 3 := by ring
  calc
    ‖deriv (dedekindXi K) s / dedekindXi K s‖ ≤
        C * (1 + ‖s‖ * (1 + ‖s‖ / ε)) := hbound s ε hε (hsep s hs)
    _ ≤ C * ((2 + 1 / c) * r ^ 3) := mul_le_mul_of_nonneg_left hpoly hC.le
    _ = A * (|a| + 4) ^ 3 := by dsimp [A, r]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
