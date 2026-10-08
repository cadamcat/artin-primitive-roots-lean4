import ArtinPrimitiveRoots.Proofs.qs_c_p.C3Helpers

/-! Scalar bounds for the dual high-divisor shells. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

/-- The lower divisor cutoff absorbs the dual high-divisor prefactor. -/
theorem dual_highdiv_shell_arith (M n B D₁ D₂ Λ E A α : ℝ)
    (hM : 0 < M) (hn : 1 ≤ n) (hB : 1 ≤ B) (hD₁ : 1 ≤ D₁)
    (hD₂ : 1 ≤ D₂) (hΛ : 1 ≤ Λ) (hE : 1 ≤ E) (hA : 1 ≤ A)
    (hcut : Real.sqrt (E * n ^ 2 / (M * A * (2 * B))) < 8 * Λ * (D₁ * D₂)) :
    Real.sqrt (M / (E * A * B)) / (D₁ * D₂) * Real.sqrt (D₁ * D₂) *
        (n / Real.sqrt (D₁ * D₂) +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) ≤
      32 * Λ * (M + B ^ α * Real.sqrt (M / B)) := by
  have hnpos : 0 < n := by linarith
  have hBpos : 0 < B := by linarith
  have hD₁pos : 0 < D₁ := by linarith
  have hD₂pos : 0 < D₂ := by linarith
  have hEpos : 0 < E := by linarith
  have hApos : 0 < A := by linarith
  let D : ℝ := D₁ * D₂
  let P : ℝ := Real.sqrt (M / (E * A * B))
  let S : ℝ := Real.sqrt (M / B)
  let L : ℝ := Real.sqrt (E * n ^ 2 / (M * A * (2 * B)))
  let F : ℝ := n * P / D
  let H : ℝ := B ^ α * S
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]
    simpa using mul_le_mul hD₁ hD₂ (by norm_num : (0 : ℝ) ≤ 1) hD₁pos.le
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hPsq : P ^ 2 = M / (E * A * B) := Real.sq_sqrt (by positivity)
  have hLsq : L ^ 2 = E * n ^ 2 / (M * A * (2 * B)) :=
    Real.sq_sqrt (by positivity)
  have hEA : 1 ≤ E * A := by
    simpa using mul_le_mul hE hA (by norm_num : (0 : ℝ) ≤ 1) hEpos.le
  have hPS : P ≤ S := by
    apply Real.sqrt_le_sqrt
    have hden : B ≤ E * A * B := by
      simpa using mul_le_mul_of_nonneg_right hEA hBpos.le
    rw [div_le_div_iff₀ (by positivity : 0 < E * A * B) hBpos]
    exact mul_le_mul_of_nonneg_left hden hM.le
  have hidentitySq : (n * P * E) ^ 2 = (Real.sqrt 2 * M * L) ^ 2 := by
    simp only [mul_pow]
    rw [hPsq, hLsq, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [hM.ne', hEpos.ne', hApos.ne', hBpos.ne']
  have hidentity : n * P * E = Real.sqrt 2 * M * L := by
    apply le_antisymm
    · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hidentitySq.le
    · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hidentitySq.ge
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hnP : n * P ≤ 2 * M * L := by
    calc
      n * P ≤ n * P * E := by
        simpa using mul_le_mul_of_nonneg_left hE (mul_nonneg hnpos.le hP)
      _ = Real.sqrt 2 * M * L := hidentity
      _ ≤ 2 * M * L := by gcongr
  have hFbound : F ≤ 16 * Λ * M := by
    dsimp [F]
    apply (div_le_iff₀ hDpos).2
    calc
      n * P ≤ 2 * M * L := hnP
      _ ≤ 2 * M * (8 * Λ * D) :=
        mul_le_mul_of_nonneg_left hcut.le (by positivity)
      _ = 16 * Λ * M * D := by ring
  have hpow : (B ^ (α / 2)) ^ 2 = B ^ α := by
    calc
      _ = (B ^ (α / 2)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = B ^ ((α / 2) * 2) := (Real.rpow_mul hBpos.le (α / 2) 2).symm
      _ = B ^ α := by congr 1 <;> ring
  let T₁ : ℝ := P / D * Real.sqrt D * Real.sqrt n * B ^ (α / 2) / Real.sqrt D₁
  let T₂ : ℝ := P / D * Real.sqrt D * Real.sqrt n * B ^ (α / 2) / Real.sqrt D₂
  have hT₁ : 0 ≤ T₁ := by dsimp [T₁]; positivity
  have hT₂ : 0 ≤ T₂ := by dsimp [T₂]; positivity
  have hT₁sq : T₁ ^ 2 = F * (B ^ α * P / D₁) := by
    dsimp [T₁, F]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt hDpos.le, Real.sq_sqrt hnpos.le, hpow,
      Real.sq_sqrt hD₁pos.le]
    field_simp [hDpos.ne', hD₁pos.ne']
  have hT₂sq : T₂ ^ 2 = F * (B ^ α * P / D₂) := by
    dsimp [T₂, F]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt hDpos.le, Real.sq_sqrt hnpos.le, hpow,
      Real.sq_sqrt hD₂pos.le]
    field_simp [hDpos.ne', hD₂pos.ne']
  have hcross (Di : ℝ) (hDi : 1 ≤ Di) : B ^ α * P / Di ≤ H := by
    have hDipos : 0 < Di := by linarith
    apply (div_le_iff₀ hDipos).2
    calc
      B ^ α * P ≤ B ^ α * S := mul_le_mul_of_nonneg_left hPS (by positivity)
      _ = H := rfl
      _ ≤ H * Di := by simpa using mul_le_mul_of_nonneg_left hDi hH
  have hT₁sqle : T₁ ^ 2 ≤ F * H := by
    rw [hT₁sq]
    exact mul_le_mul_of_nonneg_left (hcross D₁ hD₁) hF
  have hT₂sqle : T₂ ^ 2 ≤ F * H := by
    rw [hT₂sq]
    exact mul_le_mul_of_nonneg_left (hcross D₂ hD₂) hF
  have hYoung (T : ℝ) (hT : 0 ≤ T) (hTsq : T ^ 2 ≤ F * H) :
      2 * T ≤ F + H := by
    apply (sq_le_sq₀ (by positivity) (add_nonneg hF hH)).mp
    nlinarith only [hTsq, sq_nonneg (F - H)]
  have hT₁le : 2 * T₁ ≤ F + H := hYoung T₁ hT₁ hT₁sqle
  have hT₂le : 2 * T₂ ≤ F + H := hYoung T₂ hT₂ hT₂sqle
  have hroot : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  have hroot1 : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr hD1
  have hlast : P / D * Real.sqrt D * B ^ α ≤ H := by
    have hrewrite : P / D * Real.sqrt D * B ^ α = B ^ α * P / Real.sqrt D := by
      field_simp [hDpos.ne', hroot.ne']
      rw [Real.sq_sqrt hDpos.le]
    rw [hrewrite]
    apply (div_le_iff₀ hroot).2
    calc
      B ^ α * P ≤ B ^ α * S := mul_le_mul_of_nonneg_left hPS (by positivity)
      _ = H := rfl
      _ ≤ H * Real.sqrt D := by
        simpa using mul_le_mul_of_nonneg_left hroot1 hH
  have hexpand : P / D * Real.sqrt D *
        (n / Real.sqrt D +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) =
      F + T₁ + T₂ + P / D * Real.sqrt D * B ^ α := by
    dsimp [F, T₁, T₂]
    field_simp [hroot.ne', hDpos.ne',
      (Real.sqrt_pos.mpr hD₁pos).ne', (Real.sqrt_pos.mpr hD₂pos).ne']
    ring
  change P / D * Real.sqrt D *
        (n / Real.sqrt D +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) ≤
      32 * Λ * (M + H)
  calc
    _ = F + T₁ + T₂ + P / D * Real.sqrt D * B ^ α := hexpand
    _ ≤ 2 * F + 2 * H := by linarith only [hT₁le, hT₂le, hlast]
    _ ≤ 32 * Λ * M + 2 * H := by linarith only [hFbound]
    _ ≤ 32 * Λ * (M + H) := by
      have hh : H ≤ Λ * H := by
        simpa using mul_le_mul_of_nonneg_right hΛ hH
      nlinarith only [hh, hH]

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
