import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Decomp

/-!
# The scalar estimate (E) for the dual transition blocks

With `F_i ≤ G (2n/D_i + 2(2B)^α)` (HasExponent after duality) and the dual cutoff
`D₁ D₂ ≤ 2Λ n √(E/(M B))`, the block prefactor
`(M/E) √(2Λn) √(D₁D₂) √(F₁F₂) n^{-3/2}` is `≤ 64 G Λ^{3/2} (M + √M κ^{α-1/2})` for `B ≤ κ`.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

theorem sqrt_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a)
    (Real.sqrt_nonneg b)]

theorem le_of_sq_le_sq' {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (abs_le_of_sq_le_sq' h hy).2

theorem est_step1 {G a₁ a₂ b N₁ N₂ : ℝ} (hG : 0 ≤ G) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb : 0 ≤ b)
    (hN₂ : 0 ≤ N₂) (hN₁b : N₁ ≤ G * (a₁ + b)) (hN₂b : N₂ ≤ G * (a₂ + b)) :
    Real.sqrt (N₁ * N₂) ≤ G * ((Real.sqrt a₁ + Real.sqrt b) * (Real.sqrt a₂ + Real.sqrt b)) := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : N₁ ≤ G * (Real.sqrt a₁ + Real.sqrt b) ^ 2 :=
    hN₁b.trans (mul_le_mul_of_nonneg_left (sqrt_add_sq_le ha₁ hb) hG)
  have h2 : N₂ ≤ G * (Real.sqrt a₂ + Real.sqrt b) ^ 2 :=
    hN₂b.trans (mul_le_mul_of_nonneg_left (sqrt_add_sq_le ha₂ hb) hG)
  calc N₁ * N₂ ≤ (G * (Real.sqrt a₁ + Real.sqrt b) ^ 2) *
        (G * (Real.sqrt a₂ + Real.sqrt b) ^ 2) := mul_le_mul h1 h2 hN₂ (by positivity)
    _ = (G * ((Real.sqrt a₁ + Real.sqrt b) * (Real.sqrt a₂ + Real.sqrt b))) ^ 2 := by ring

theorem est_step2 {n D₁ D₂ b : ℝ} (hn : 0 < n) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hb : 0 ≤ b) :
    Real.sqrt (D₁ * D₂) * ((Real.sqrt (2 * n / D₁) + Real.sqrt b) *
        (Real.sqrt (2 * n / D₂) + Real.sqrt b)) ≤
      2 * n + 2 * (Real.sqrt (2 * n * (D₁ * D₂)) * Real.sqrt b) + Real.sqrt (D₁ * D₂) * b := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have ha₁0 : 0 ≤ 2 * n / D₁ := by positivity
  have ha₂0 : 0 ≤ 2 * n / D₂ := by positivity
  have hDa : Real.sqrt (D₁ * D₂) * (Real.sqrt (2 * n / D₁) * Real.sqrt (2 * n / D₂)) = 2 * n := by
    rw [← Real.sqrt_mul ha₁0, ← Real.sqrt_mul (by positivity)]
    rw [show D₁ * D₂ * (2 * n / D₁ * (2 * n / D₂)) = (2 * n) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hDa₁ : Real.sqrt (D₁ * D₂) * Real.sqrt (2 * n / D₁) ≤ Real.sqrt (2 * n * (D₁ * D₂)) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [show D₁ * D₂ * (2 * n / D₁) = 2 * n * D₂ by field_simp]
    have := mul_le_mul_of_nonneg_left hD₁ (show (0:ℝ) ≤ 2 * n * D₂ by positivity)
    linarith
  have hDa₂ : Real.sqrt (D₁ * D₂) * Real.sqrt (2 * n / D₂) ≤ Real.sqrt (2 * n * (D₁ * D₂)) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [show D₁ * D₂ * (2 * n / D₂) = 2 * n * D₁ by field_simp]
    have := mul_le_mul_of_nonneg_left hD₂ (show (0:ℝ) ≤ 2 * n * D₁ by positivity)
    linarith
  have hsb := Real.sq_sqrt hb
  have hexp : Real.sqrt (D₁ * D₂) * ((Real.sqrt (2 * n / D₁) + Real.sqrt b) *
        (Real.sqrt (2 * n / D₂) + Real.sqrt b)) =
      Real.sqrt (D₁ * D₂) * (Real.sqrt (2 * n / D₁) * Real.sqrt (2 * n / D₂)) +
        (Real.sqrt (D₁ * D₂) * Real.sqrt (2 * n / D₁)) * Real.sqrt b +
        (Real.sqrt (D₁ * D₂) * Real.sqrt (2 * n / D₂)) * Real.sqrt b +
        Real.sqrt (D₁ * D₂) * (Real.sqrt b) ^ 2 := by ring
  rw [hexp, hDa, hsb]
  have := mul_le_mul_of_nonneg_right hDa₁ (Real.sqrt_nonneg b)
  have := mul_le_mul_of_nonneg_right hDa₂ (Real.sqrt_nonneg b)
  linarith

theorem est_pre {Λ n : ℝ} (hΛ : 0 ≤ Λ) (hn : 0 < n) :
    Real.sqrt (2 * Λ * n) * n ^ (-(3/2 : ℝ)) = Real.sqrt (2 * Λ) / n := by
  rw [Real.sqrt_mul (by positivity), Real.rpow_neg hn.le]
  have : n ^ (3/2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hn,
      Real.rpow_one]
  rw [this]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  field_simp

theorem rpow_three_halves {Λ : ℝ} (hΛ : 0 < Λ) : Λ ^ (3/2 : ℝ) = Λ * Real.sqrt Λ := by
  rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hΛ, Real.rpow_one]

theorem sqrt_two_mul_le {Λ : ℝ} (hΛ : 0 ≤ Λ) : Real.sqrt (2 * Λ) ≤ 2 * Real.sqrt Λ := by
  rw [Real.sqrt_mul (by norm_num)]
  have : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

theorem est_T1 {M E Λ n : ℝ} (hM : 0 < M) (hE : 1 ≤ E) (hΛ : 1 ≤ Λ) (hn : 0 < n) :
    M / E * (Real.sqrt (2 * Λ) / n) * (2 * n) ≤ 4 * Λ ^ (3/2 : ℝ) * M := by
  have hΛ0 : 0 < Λ := by linarith
  rw [rpow_three_halves hΛ0]
  have hME : M / E ≤ M := div_le_self hM.le hE
  have h2 : M / E * (Real.sqrt (2 * Λ) / n) * (2 * n) = 2 * (M / E) * Real.sqrt (2 * Λ) := by
    field_simp
  rw [h2]
  have hsΛ : 1 ≤ Real.sqrt Λ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hΛ
  have hL := sqrt_two_mul_le hΛ0.le
  have hME0 : 0 ≤ M / E := by positivity
  calc 2 * (M / E) * Real.sqrt (2 * Λ) ≤ 2 * M * (2 * Real.sqrt Λ) :=
        mul_le_mul (by linarith) hL (Real.sqrt_nonneg _) (by positivity)
    _ ≤ 4 * (Λ * Real.sqrt Λ) * M := by
        have := mul_le_mul_of_nonneg_left hΛ (show (0:ℝ) ≤ M * Real.sqrt Λ by positivity)
        nlinarith

theorem est_EMB {M E B : ℝ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) :
    (M / E) ^ 2 * Real.sqrt (E / (M * B)) ≤ M * Real.sqrt M / Real.sqrt B := by
  have hE0 : 0 < E := by linarith
  have hsM0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hsB0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hsE0 : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE0
  have hsE1 : 1 ≤ Real.sqrt E := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hE
  have hsE := Real.sq_sqrt hE0.le
  have hsM := Real.sq_sqrt hM.le
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hM.le]
  -- (M/E)² √E / (√M √B) ≤ M √M / √B  ⟸  M² √E ≤ E² M √M · √M / M ... clear denominators
  rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) hsB0]
  -- M^2 * √E * √B ≤ M * √M * (E^2 * (√M * √B))
  have hE2 : Real.sqrt E ≤ E ^ 2 := by nlinarith
  have : M ^ 2 * Real.sqrt E * Real.sqrt B ≤ M * Real.sqrt M * (E ^ 2 * (Real.sqrt M * Real.sqrt B)) := by
    have h1 : M ^ 2 * Real.sqrt E * Real.sqrt B = (M * Real.sqrt B) * (Real.sqrt M) ^ 2 * Real.sqrt E := by
      rw [hsM]; ring
    rw [h1]
    have h2 : M * Real.sqrt M * (E ^ 2 * (Real.sqrt M * Real.sqrt B)) =
        (M * Real.sqrt B) * (Real.sqrt M) ^ 2 * E ^ 2 := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hE2 (by positivity)
  linarith

theorem est_T2 {α M n B D E Λ κ : ℝ} (hα1 : 1 < α) (hM : 0 < M) (hn : 0 < n) (hB : 1 ≤ B)
    (hBκ : B ≤ κ) (hE : 1 ≤ E) (hΛ : 1 ≤ Λ) (hb8 : 2 * (2 * B) ^ α ≤ 8 * B ^ α) (hD0 : 0 ≤ D)
    (hD : D ≤ 2 * Λ * (n * Real.sqrt (E / (M * B)))) :
    M / E * (Real.sqrt (2 * Λ) / n) * (2 * (Real.sqrt (2 * n * D) *
        Real.sqrt (2 * (2 * B) ^ α))) ≤
      8 * Λ * (M + Real.sqrt M * κ ^ (α - 1/2)) := by
  have hB0 : 0 < B := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set b := 2 * (2 * B) ^ α with hbdef
  have hb0 : 0 ≤ b := by positivity
  set Y := Real.sqrt M * κ ^ (α - 1/2) with hY
  set YB := Real.sqrt M * B ^ (α - 1/2) with hYB
  have hYBY : YB ≤ Y := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hB0.le hBκ (by linarith)) (Real.sqrt_nonneg _)
  have hYB0 : 0 ≤ YB := by positivity
  have hsB0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have hBsplit : B ^ α = B ^ (α - 1/2) * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hB0]; norm_num
  set X := M / E * Real.sqrt (2 * Λ) * Real.sqrt (2 * n * D) * Real.sqrt b / n with hX
  have hX0 : 0 ≤ X := by positivity
  have hrw : M / E * (Real.sqrt (2 * Λ) / n) * (2 * (Real.sqrt (2 * n * D) * Real.sqrt b)) =
      2 * X := by rw [hX]; ring
  rw [hrw]
  have hX2 : X ^ 2 = (M / E) ^ 2 * (2 * Λ) * (2 * n * D) * b / n ^ 2 := by
    rw [hX, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt hb0]
  have hEMB := est_EMB hM hE hB0
  have hsq : X ^ 2 ≤ (4 * Λ * (M + Y)) ^ 2 := by
    rw [hX2]
    calc (M / E) ^ 2 * (2 * Λ) * (2 * n * D) * b / n ^ 2
        ≤ (M / E) ^ 2 * (2 * Λ) * (2 * n * (2 * Λ * (n * Real.sqrt (E / (M * B))))) * b /
            n ^ 2 := by gcongr
      _ = 8 * Λ ^ 2 * ((M / E) ^ 2 * Real.sqrt (E / (M * B))) * b := by
          field_simp; ring
      _ ≤ 8 * Λ ^ 2 * (M * Real.sqrt M / Real.sqrt B) * (8 * (B ^ (α - 1/2) * Real.sqrt B)) := by
          rw [← hBsplit]; gcongr
      _ = 64 * Λ ^ 2 * (M * YB) := by rw [hYB]; field_simp; norm_num
      _ ≤ 64 * Λ ^ 2 * (M * Y) := by gcongr
      _ ≤ (4 * Λ * (M + Y)) ^ 2 := by
          have hY0 : 0 ≤ Y := le_trans hYB0 hYBY
          nlinarith [sq_nonneg (M - Y), sq_nonneg Λ, mul_nonneg (sq_nonneg Λ) (sq_nonneg (M - Y))]
  have := le_of_sq_le_sq' (by have := le_trans hYB0 hYBY; positivity) hsq
  linarith

theorem est_T3 {α M n B D E Λ κ : ℝ} (hα1 : 1 < α) (hM : 0 < M) (hn : 0 < n) (hB : 1 ≤ B)
    (hBκ : B ≤ κ) (hE : 1 ≤ E) (hΛ : 1 ≤ Λ) (hb8 : 2 * (2 * B) ^ α ≤ 8 * B ^ α) (hD1 : 1 ≤ D)
    (hD : D ≤ 2 * Λ * (n * Real.sqrt (E / (M * B)))) :
    M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt D * (2 * (2 * B) ^ α)) ≤
      23 * Λ ^ (3/2 : ℝ) * (Real.sqrt M * κ ^ (α - 1/2)) := by
  have hB0 : 0 < B := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hE0 : 0 < E := by linarith
  set b := 2 * (2 * B) ^ α with hbdef
  have hb0 : 0 ≤ b := by positivity
  set Y := Real.sqrt M * κ ^ (α - 1/2) with hY
  set YB := Real.sqrt M * B ^ (α - 1/2) with hYB
  have hYBY : YB ≤ Y := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hB0.le hBκ (by linarith)) (Real.sqrt_nonneg _)
  have hYB0 : 0 ≤ YB := by positivity
  have hY0 : 0 ≤ Y := le_trans hYB0 hYBY
  have hBsplit : B ^ α = B ^ (α - 1/2) * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hB0]; norm_num
  set X := M / E * Real.sqrt (2 * Λ) * Real.sqrt D * b / n with hX
  have hX0 : 0 ≤ X := by positivity
  have hrw : M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt D * b) = X := by rw [hX]; ring
  rw [hrw]
  have hX2 : X ^ 2 = (M / E) ^ 2 * (2 * Λ) * D * b ^ 2 / n ^ 2 := by
    rw [hX, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
  have hDD : D ≤ 4 * Λ ^ 2 * n ^ 2 * (E / (M * B)) := by
    have hsq' : Real.sqrt (E / (M * B)) ^ 2 = E / (M * B) := Real.sq_sqrt (by positivity)
    have h2 : D ^ 2 ≤ (2 * Λ * (n * Real.sqrt (E / (M * B)))) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hD 2
    have h3 : (2 * Λ * (n * Real.sqrt (E / (M * B)))) ^ 2 = 4 * Λ ^ 2 * n ^ 2 * (E / (M * B)) := by
      rw [show (2 * Λ * (n * Real.sqrt (E / (M * B)))) ^ 2 =
        4 * Λ ^ 2 * n ^ 2 * Real.sqrt (E / (M * B)) ^ 2 by ring, hsq']
    nlinarith
  have hb2 : b ^ 2 ≤ 64 * (B ^ (α - 1/2)) ^ 2 * B := by
    have h1 : b ^ 2 ≤ (8 * B ^ α) ^ 2 := pow_le_pow_left₀ hb0 hb8 2
    have h2 : (8 * B ^ α) ^ 2 = 64 * (B ^ (α - 1/2)) ^ 2 * B := by
      rw [hBsplit, mul_pow, mul_pow, Real.sq_sqrt hB0.le]; ring
    linarith
  have hΛ3 : (Λ ^ (3/2 : ℝ)) ^ 2 = Λ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hYB2 : YB ^ 2 = M * (B ^ (α - 1/2)) ^ 2 := by
    rw [hYB, mul_pow, Real.sq_sqrt hM.le]
  have hsq : X ^ 2 ≤ (23 * Λ ^ (3/2 : ℝ) * Y) ^ 2 := by
    rw [hX2]
    calc (M / E) ^ 2 * (2 * Λ) * D * b ^ 2 / n ^ 2
        ≤ (M / E) ^ 2 * (2 * Λ) * (4 * Λ ^ 2 * n ^ 2 * (E / (M * B))) *
            (64 * (B ^ (α - 1/2)) ^ 2 * B) / n ^ 2 := by gcongr
      _ = 512 * Λ ^ 3 * (M * (B ^ (α - 1/2)) ^ 2) / E := by field_simp; ring
      _ ≤ 512 * Λ ^ 3 * (M * (B ^ (α - 1/2)) ^ 2) := div_le_self (by positivity) hE
      _ = 512 * (Λ ^ (3/2 : ℝ)) ^ 2 * YB ^ 2 := by rw [hΛ3, hYB2]
      _ ≤ 512 * (Λ ^ (3/2 : ℝ)) ^ 2 * Y ^ 2 := by gcongr
      _ ≤ (23 * Λ ^ (3/2 : ℝ) * Y) ^ 2 := by nlinarith [sq_nonneg (Λ ^ (3/2 : ℝ) * Y)]
  exact le_of_sq_le_sq' (by positivity) hsq

theorem E3_estimate {α M n B D₁ D₂ E Λ N₁ N₂ G κ : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) (hM : 0 < M)
    (hn : 1 ≤ n) (hB : 1 ≤ B) (hBκ : B ≤ κ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hE : 1 ≤ E)
    (hΛ : 1 ≤ Λ) (hG : 0 ≤ G) (hN₂ : 0 ≤ N₂)
    (hN₁b : N₁ ≤ G * (2 * n / D₁ + 2 * (2 * B) ^ α))
    (hN₂b : N₂ ≤ G * (2 * n / D₂ + 2 * (2 * B) ^ α))
    (hD : D₁ * D₂ ≤ 2 * Λ * (n * Real.sqrt (E / (M * B)))) :
    M / E * Real.sqrt (2 * Λ * n) * Real.sqrt (D₁ * D₂) * Real.sqrt (N₁ * N₂) *
        n ^ (-(3/2 : ℝ)) ≤
      64 * G * Λ ^ (3/2 : ℝ) * (M + Real.sqrt M * κ ^ (α - 1/2)) := by
  have hn0 : 0 < n := by linarith
  have hB0 : 0 < B := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hE0 : 0 < E := by linarith
  have hb0 : 0 ≤ 2 * (2 * B) ^ α := by positivity
  have hb8 : 2 * (2 * B) ^ α ≤ 8 * B ^ α := by
    rw [Real.mul_rpow (by norm_num) hB0.le]
    have h4 : (2 : ℝ) ^ α ≤ 4 := by
      calc (2 : ℝ) ^ α ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2
        _ = 4 := by norm_num
    have := Real.rpow_pos_of_pos hB0 α
    nlinarith
  have hD1 : 1 ≤ D₁ * D₂ := by nlinarith
  have h1 := est_step1 hG (by positivity : (0:ℝ) ≤ 2 * n / D₁) (by positivity : (0:ℝ) ≤ 2 * n / D₂)
    hb0 hN₂ hN₁b hN₂b
  have h2 := est_step2 hn0 hD₁ hD₂ hb0
  have hT1 := est_T1 hM hE hΛ hn0
  have hT2 := est_T2 hα1 hM hn0 hB hBκ hE hΛ hb8 (by positivity) hD
  have hT3 := est_T3 hα1 hM hn0 hB hBκ hE hΛ hb8 hD1 hD
  set Y := Real.sqrt M * κ ^ (α - 1/2) with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ κ ^ (α - 1/2) := Real.rpow_nonneg (by linarith) _
    positivity
  have hΛ32pos : 0 < Λ ^ (3/2 : ℝ) := by positivity
  have hΛle : Λ ≤ Λ ^ (3/2 : ℝ) := by
    rw [rpow_three_halves hΛ0]
    have : 1 ≤ Real.sqrt Λ := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hΛ
    nlinarith
  set S1 := (Real.sqrt (2 * n / D₁) + Real.sqrt (2 * (2 * B) ^ α)) *
    (Real.sqrt (2 * n / D₂) + Real.sqrt (2 * (2 * B) ^ α)) with hS1
  have hpre := est_pre hΛ0.le hn0
  have hME0 : 0 ≤ M / E * (Real.sqrt (2 * Λ) / n) := by positivity
  calc M / E * Real.sqrt (2 * Λ * n) * Real.sqrt (D₁ * D₂) * Real.sqrt (N₁ * N₂) *
        n ^ (-(3/2 : ℝ))
      = M / E * (Real.sqrt (2 * Λ * n) * n ^ (-(3/2 : ℝ))) * (Real.sqrt (D₁ * D₂) *
          Real.sqrt (N₁ * N₂)) := by ring
    _ = M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt (D₁ * D₂) * Real.sqrt (N₁ * N₂)) := by
        rw [hpre]
    _ ≤ M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt (D₁ * D₂) * (G * S1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)) hME0
    _ = G * (M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt (D₁ * D₂) * S1)) := by ring
    _ ≤ G * (M / E * (Real.sqrt (2 * Λ) / n) * (2 * n + 2 * (Real.sqrt (2 * n * (D₁ * D₂)) *
          Real.sqrt (2 * (2 * B) ^ α)) + Real.sqrt (D₁ * D₂) * (2 * (2 * B) ^ α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hME0) hG
    _ = G * (M / E * (Real.sqrt (2 * Λ) / n) * (2 * n) +
          M / E * (Real.sqrt (2 * Λ) / n) * (2 * (Real.sqrt (2 * n * (D₁ * D₂)) *
            Real.sqrt (2 * (2 * B) ^ α))) +
          M / E * (Real.sqrt (2 * Λ) / n) * (Real.sqrt (D₁ * D₂) * (2 * (2 * B) ^ α))) := by
        ring
    _ ≤ G * (4 * Λ ^ (3/2 : ℝ) * M + 8 * Λ * (M + Y) + 23 * Λ ^ (3/2 : ℝ) * Y) := by
        gcongr
    _ ≤ 64 * G * Λ ^ (3/2 : ℝ) * (M + Y) := by
        have h8 : 8 * Λ * (M + Y) ≤ 8 * Λ ^ (3/2 : ℝ) * (M + Y) := by
          have : 0 ≤ M + Y := by linarith
          nlinarith
        have : 4 * Λ ^ (3/2 : ℝ) * M + 8 * Λ * (M + Y) + 23 * Λ ^ (3/2 : ℝ) * Y ≤
            64 * Λ ^ (3/2 : ℝ) * (M + Y) := by nlinarith
        calc G * (4 * Λ ^ (3/2 : ℝ) * M + 8 * Λ * (M + Y) + 23 * Λ ^ (3/2 : ℝ) * Y)
            ≤ G * (64 * Λ ^ (3/2 : ℝ) * (M + Y)) := mul_le_mul_of_nonneg_left this hG
          _ = 64 * G * Λ ^ (3/2 : ℝ) * (M + Y) := by ring

end ArtinPrimitiveRoots.A2.QSC3
