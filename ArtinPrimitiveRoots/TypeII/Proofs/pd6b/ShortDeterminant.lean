import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.Damping
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CutoffBounds

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical Filter

noncomputable section

/-- Every allowed product dyad is small enough for the roughness primitivity argument. -/
theorem dyadic_shortness_eventually (K : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ Y ∈ dyadicScales x K, R * Y < roughCutoff x := by
  let C := ((K + 1 : ℕ) : ℝ) + |Real.log R|
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hEvent : ∀ᶠ x : ℝ in atTop,
      C < Real.rpow (Real.log x) (1 / 25 : ℝ) ∧ 1 ≤ Real.log x := by
    filter_upwards [ht.eventually_gt_atTop C, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hgap hL
    exact ⟨hgap, hL⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx Y hY
  obtain ⟨hgap, hL⟩ := hx₁ x ((le_max_right _ _).trans hx)
  obtain ⟨hImage, hBounds⟩ := Finset.mem_filter.mp hY
  obtain ⟨k, hk, hkY⟩ := Finset.mem_image.mp hImage
  have hYpos : 0 < Y := by rw [← hkY]; positivity
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hPow : 1 ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hPowPos : 0 < Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hJoin : Real.rpow (Real.log x) (24 / 100 : ℝ) =
      Real.rpow (Real.log x) (1 / 5 : ℝ) * Real.rpow (Real.log x) (1 / 25 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) ((1 / 5 : ℝ) + (1 / 25 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hLpos _ _
  have hLogR : Real.log R ≤ |Real.log R| * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    calc
      Real.log R ≤ |Real.log R| := le_abs_self _
      _ ≤ |Real.log R| * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hPow (abs_nonneg _)
  have hLog : Real.log (R * Y) ≤ C * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    rw [Real.log_mul hR.ne' hYpos.ne']
    calc
      _ ≤ |Real.log R| * Real.rpow (Real.log x) (1 / 5 : ℝ) +
          ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) := add_le_add hLogR hBounds.2
      _ = C * Real.rpow (Real.log x) (1 / 5 : ℝ) := by dsimp [C]; ring
  have hSmall : C * Real.rpow (Real.log x) (1 / 5 : ℝ) <
      Real.rpow (Real.log x) (24 / 100 : ℝ) := by
    rw [hJoin]
    calc
      _ = Real.rpow (Real.log x) (1 / 5 : ℝ) * C := mul_comm _ _
      _ < _ := mul_lt_mul_of_pos_left hgap hPowPos
  calc
    R * Y = Real.exp (Real.log (R * Y)) := (Real.exp_log (mul_pos hR hYpos)).symm
    _ ≤ Real.exp (C * Real.rpow (Real.log x) (1 / 5 : ℝ)) := Real.exp_le_exp.mpr hLog
    _ < roughCutoff x := Real.exp_lt_exp.mpr hSmall

/-- Both geometric pieces vanish when the common smoothing factor does. -/
theorem geometricMultiplier_nonzero_psi {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (h : geometricMultiplier F S D aa bb t ≠ 0) :
    F.psi ((t : ℝ) / S.Y) ≠ 0 := by
  intro hzero
  apply h
  simp [geometricMultiplier, rawMultiplier, comparisonMultiplier, majorKernel, hzero]

theorem geometricMultiplier_nonzero_eta {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (h : geometricMultiplier F S D aa bb t ≠ 0) :
    F.eta ((aa : ℝ) / S.Y) ≠ 0 ∧ F.eta ((bb : ℝ) / S.Y) ≠ 0 := by
  constructor
  · intro hzero
    apply h
    simp [geometricMultiplier, rawMultiplier, comparisonMultiplier, hzero]
  · intro hzero
    apply h
    simp [geometricMultiplier, rawMultiplier, comparisonMultiplier, hzero]

end
end ArtinPrimitiveRoots.TypeII.PD
