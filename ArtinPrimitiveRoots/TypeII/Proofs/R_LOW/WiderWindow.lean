import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.LowFrequency
import ArtinPrimitiveRoots.TypeII.Defs

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open Classical ArtinPrimitiveRoots.TypeII
open scoped BigOperators

/-- Uniform rough counts on a fixed exponent window. -/
def roughCountBound (γ wMin wMax A₀ A₁ C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x →
    ∀ M : ℝ, Real.rpow x γ ≤ M →
      Real.log M / Real.log x ∈ Set.Icc wMin wMax →
      Real.log (2 * M) / Real.log x ∈ Set.Icc wMin wMax →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
        ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
          M ≤ l → l ≤ r → r ≤ 2 * M →
            ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
                  l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                ((if roughAbove m (Real.rpow x γ) then 1 else 0 : ℝ) : ℂ) *
                  χ (m : ZMod k)) -
              (if χ = 1 then
                ((1 / Real.log x) * ∫ y in l..r,
                  ArtinPrimitiveRoots.Sieve.roughDensity γ
                    (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
              C * M * Real.rpow (Real.log x) (-A₁)

/-- Rescaling the base widens the exponent window without enlarging the error. -/
theorem rough_count_rescale (γ wMin wMax A₀ A₁ C X₀ c : ℝ)
    (hc : 1 ≤ c) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC : 0 ≤ C)
    (hcount : roughCountBound (γ / c) (wMin / c) (wMax / c) A₀ A₁ C X₀) :
    roughCountBound γ wMin wMax A₀ A₁ C (max 2 X₀) := by
  intro x hx M hM hwM hw2M k hk hklog χ l r hl hlr hr
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
  let X : ℝ := Real.rpow x c
  have hxX : x ≤ X := by
    calc x = Real.rpow x 1 := (Real.rpow_one x).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hxone hc
  have hX₀ : X₀ ≤ X :=
    (le_trans (le_max_right _ _) hx).trans hxX
  have hlogX : Real.log X = c * Real.log x := by
    exact Real.log_rpow hxpos c
  have hlogs : Real.log x ≤ Real.log X := by
    rw [hlogX]
    calc Real.log x = 1 * Real.log x := (one_mul _).symm
      _ ≤ c * Real.log x := mul_le_mul_of_nonneg_right hc (le_of_lt hLpos)
  have hroot : Real.rpow X (γ / c) = Real.rpow x γ := by
    dsimp [X]
    rw [← Real.rpow_mul (le_of_lt hxpos)]
    congr 1
    field_simp [hcne]
  have hratio (y : ℝ) :
      Real.log y / Real.log X = (Real.log y / Real.log x) / c := by
    rw [hlogX, div_div, mul_comm c (Real.log x)]
  have hwM' : Real.log M / Real.log X ∈ Set.Icc (wMin / c) (wMax / c) := by
    rw [hratio M]
    exact ⟨div_le_div_of_nonneg_right hwM.1 (le_of_lt hcpos),
      div_le_div_of_nonneg_right hwM.2 (le_of_lt hcpos)⟩
  have hw2M' : Real.log (2 * M) / Real.log X ∈ Set.Icc (wMin / c) (wMax / c) := by
    rw [hratio (2 * M)]
    exact ⟨div_le_div_of_nonneg_right hw2M.1 (le_of_lt hcpos),
      div_le_div_of_nonneg_right hw2M.2 (le_of_lt hcpos)⟩
  have hklog' : (k : ℝ) ≤ Real.rpow (Real.log X) A₀ :=
    hklog.trans (Real.rpow_le_rpow (le_of_lt hLpos) hlogs hA₀)
  have hM' : Real.rpow X (γ / c) ≤ M := by simpa only [hroot] using hM
  have hscaled := hcount X hX₀ M hM' hwM' hw2M' k hk hklog' χ l r hl hlr hr
  have hdensity (y : ℝ) :
      ArtinPrimitiveRoots.Sieve.roughDensity (γ / c) (Real.log y / Real.log X) =
        c * ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log y / Real.log x) := by
    rw [hratio y]
    exact density_rescale γ (Real.log y / Real.log x) c hcpos
  have hintegral :
      (∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity (γ / c)
        (Real.log y / Real.log X)) =
      c * ∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity γ
        (Real.log y / Real.log x) := by
    simp_rw [hdensity]
    rw [intervalIntegral.integral_const_mul]
  have hmain :
      (1 / Real.log X) * ∫ y in l..r,
        ArtinPrimitiveRoots.Sieve.roughDensity (γ / c) (Real.log y / Real.log X) =
      (1 / Real.log x) * ∫ y in l..r,
        ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log y / Real.log x) := by
    rw [hintegral, hlogX]
    field_simp [hcne, hLne]
  rw [hroot, hmain] at hscaled
  have hMpos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos γ) hM
  exact hscaled.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hLpos hlogs (neg_nonpos.mpr hA₁))
    (mul_nonneg hC (le_of_lt hMpos)))

end ArtinPrimitiveRoots.Proofs.r_impl_muse
