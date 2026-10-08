import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Tools

/-!
# B0: the high-core bound

Cases: `M < 1/3` (no rows); bounded `N < 2^r` or `MN < N(bad)^{2/η}` (trivial bound);
otherwise `r` descent levels with `G = N^{1/r}` (`level_bound`, `unroll`) down to column length
`2^r`, with `r ≥ 64/δ'`, `δ' = min δ 1`, and the margin `N(bad) ≤ (MN)^{η/2}` for C4.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSB0

open QSC2 QSC3

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

theorem ceil_logb_le {γ : ℝ} (hγ : 0 < γ) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ X : ℝ, 1 ≤ X → ((Nat.ceil (Real.logb 2 X) + 1 : ℕ) : ℝ) ≤ CL * X ^ γ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (γ * Real.log 2) + 2, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hXγ : 1 ≤ X ^ γ := Real.one_le_rpow hX hγ.le
  have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h1 : (Nat.ceil (Real.logb 2 X) : ℝ) < Real.logb 2 X + 1 := Nat.ceil_lt_add_one hlb
  have h2 : Real.logb 2 X ≤ X ^ γ / (γ * Real.log 2) := by
    rw [Real.logb, div_le_div_iff₀ hl2 (by positivity)]
    have := Real.log_le_rpow_div hX0.le hγ
    rw [le_div_iff₀ hγ] at this
    nlinarith
  push_cast
  have h3 : X ^ γ / (γ * Real.log 2) = 1 / (γ * Real.log 2) * X ^ γ := by ring
  nlinarith

theorem ceil_logb_mono {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    Nat.ceil (Real.logb 2 X) ≤ Nat.ceil (Real.logb 2 Y) :=
  Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) (by linarith) hXY)

theorem M_nonneg {M N η : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hη2 : η < 1/2)
    (h : 2 * N * (M * N) ^ η ≤ M) : 0 ≤ M := by
  by_contra hM
  push Not at hM
  have hP : M * N < 0 := by nlinarith
  have hpos : 0 < (M * N) ^ η := by
    rw [Real.rpow_def_of_neg hP]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  nlinarith

theorem P_gt_one {M N η : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hη1 : η ≤ 1) (hM : 0 < M)
    (h : 2 * N * (M * N) ^ η ≤ M) : 1 < M * N := by
  by_contra hP
  push Not at hP
  have hP0 : 0 < M * N := by positivity
  have h1 : (M * N) ^ (1 : ℝ) ≤ (M * N) ^ η :=
    Real.rpow_le_rpow_of_exponent_ge hP0 hP hη1
  rw [Real.rpow_one] at h1
  nlinarith

open Classical in
/-- The descent recursion unrolled `r` times, down to column length `2^r`. -/
theorem b0_recursion (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (α : ℝ) {Wm : ℝ} (hWm : ∀ x : ℝ, 0 ≤ x → W x ≤ Wm)
    {C₄ δ₄ θ Cd η' : ℝ} (hC₄ : 0 < C₄) (hδ₄ : 0 ≤ δ₄) (hCd : 0 < Cd) (hη' : 0 ≤ η')
    (hC4 : ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
          C₄ * qsN 𝔮 ^ 8 * (M * n) ^ δ₄ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2)
    (hdesc : ∀ (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ N → 1 ≤ G →
      (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N) →
      ‖∑ g ∈ ((cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)).filter (fun g => G < qsN g),
          qsGcdBlock F W M κ g cols z‖ ≤
        Cd * N ^ η' * qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2)
    (M N κ G Sh : ℝ) (r : ℕ) (hM : 0 < M) (hN : 1 ≤ N) (hG : 2 ≤ G) (hGr : G ^ r = N)
    (hκ : 1 ≤ κ) (hκM : 2 * κ ≤ M)
    (hmargin : ∀ X : ℝ, X ≤ N → ∀ (g : Ideal (𝓞 K)) (n : ℝ), 0 < qsN g → qsN g ≤ G → 1 ≤ n →
      n * qsN g ≤ X → qsN (qsBadRad m qS * g) * n ^ 2 * (M * n) ^ θ ≤ κ * M)
    (hshape : ∀ n : ℝ, 1 ≤ n → n ≤ N → qsBlockShape M n κ α ≤ Sh) (hSh : 0 ≤ Sh) :
    qsHighNorm F W M N κ ≤
      ((Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
          ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ)) *
        ((rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
          idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * N) ^ δ₄ * Sh)) *
        (r * (1 + ((Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
          ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ)) * Cd * N ^ η') ^ r) +
      (1 + ((Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
          ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ)) * Cd * N ^ η') ^ r *
        ((rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 ^ r))) := by
  have hWm0 : 0 ≤ Wm := le_trans (hW.2.1 0) (hWm 0 le_rfl)
  have hG0 : 0 < G := by linarith
  have hN0 : 0 < N := by linarith
  set L := (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
    ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  set A₀ := (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
    idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * N) ^ δ₄ * Sh) with hA₀
  have hA₀0 : 0 ≤ A₀ := by
    have : 0 ≤ qsN (qsBadRad m qS) := Nat.cast_nonneg _
    positivity
  set b := L * Cd * N ^ η' with hb
  have hb0 : 0 ≤ b := by positivity
  set Hs : ℕ → ℝ := fun i => qsHighNorm F W M (N * (2 / G) ^ i) κ with hHs
  have hHs0 : ∀ i, 0 ≤ Hs i := fun i => by simp only [hHs, qsHighNorm]; positivity
  have h2G : 2 / G ≤ 1 := by rw [div_le_one hG0]; exact hG
  have h2G0 : 0 < 2 / G := by positivity
  have hXr : N * (2 / G) ^ r = 2 ^ r := by
    rw [div_pow, ← hGr]; field_simp
  have hstep : ∀ k < r, Hs k ≤ L * A₀ + b * Hs (k + 1) := by
    intro k hk
    set X := N * (2 / G) ^ k with hX
    have hXN : X ≤ N := by
      rw [hX]; exact mul_le_of_le_one_right hN0.le (pow_le_one₀ h2G0.le h2G)
    have hX1 : 1 ≤ X := by
      have : (2 / G) ^ r ≤ (2 / G) ^ k := pow_le_pow_of_le_one h2G0.le h2G hk.le
      have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
      calc (1 : ℝ) ≤ 2 ^ r := h2r
        _ = N * (2 / G) ^ r := hXr.symm
        _ ≤ X := mul_le_mul_of_nonneg_left this hN0.le
    have hlev := level_bound F hrf hqS W hW α hWm hC₄ hδ₄ hCd hη' hC4 hdesc M κ X G Sh hM hX1
      (by linarith) hκ hκM (hmargin X hXN) (fun n hn hnX => hshape n hn (hnX.trans hXN)) hSh
    have hnext : 2 * X / G = N * (2 / G) ^ (k + 1) := by rw [hX, pow_succ]; ring
    rw [hnext] at hlev
    have hLX : (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
        ((Nat.ceil (Real.logb 2 X) + 1 : ℕ) : ℝ) ≤ L := by
      rw [hL]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.add_le_add_right (ceil_logb_mono hX1 hXN) 1
    have hMX : (M * X) ^ δ₄ ≤ (M * N) ^ δ₄ :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hXN hM.le) hδ₄
    have hXη : X ^ η' ≤ N ^ η' := Real.rpow_le_rpow (by linarith) hXN hη'
    have hNB : 0 ≤ qsN (qsBadRad m qS) := Nat.cast_nonneg _
    have hin : (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
          idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) +
          Cd * X ^ η' * Hs (k + 1) ≤ A₀ + Cd * N ^ η' * Hs (k + 1) := by
      rw [hA₀]
      have h1 : idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) ≤
          idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * N) ^ δ₄ * Sh) := by
        gcongr
      have h2 : Cd * X ^ η' * Hs (k + 1) ≤ Cd * N ^ η' * Hs (k + 1) := by
        have := hHs0 (k + 1)
        gcongr
      linarith
    have hin0 : 0 ≤ (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
          idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) +
          Cd * X ^ η' * Hs (k + 1) := by
      have := hHs0 (k + 1)
      positivity
    calc Hs k ≤ _ := hlev
      _ ≤ L * (A₀ + Cd * N ^ η' * Hs (k + 1)) := mul_le_mul hLX hin hin0 hL0
      _ = L * A₀ + b * Hs (k + 1) := by rw [hb]; ring
  have hun := unroll (H := Hs) (mul_nonneg hL0 hA₀0) hb0 r hstep
  have hgeom := geom_le hb0 r
  have h0 : Hs 0 = qsHighNorm F W M N κ := by simp [hHs]
  have hr' : Hs r ≤ (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 ^ r)) := by
    simp only [hHs]
    rw [hXr]
    exact highNorm_trivial F hW hWm hM
  have hbr : b ^ r ≤ (1 + b) ^ r := pow_le_pow_left₀ hb0 (by linarith) r
  rw [← h0]
  calc Hs 0 ≤ L * A₀ * ∑ i ∈ Finset.range r, b ^ i + b ^ r * Hs r := hun
    _ ≤ L * A₀ * (r * (1 + b) ^ r) +
        (1 + b) ^ r * ((rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 ^ r))) := by
        have := hHs0 r
        gcongr

/-! ### Counting estimates -/

theorem rowSet_card_le {CI ε : ℝ} (hCI : 0 < CI) (hε : 0 < ε)
    (hcount : ∀ X : ℝ, 1 ≤ X → idealCount K X ≤ CI * X ^ (1 + ε)) {M P : ℝ} (hM : 1 ≤ M)
    (hMP : M ≤ P) :
    ((rowSet K (5 / 2 * M)).card : ℝ) ≤ CI * (5 / 2) ^ (1 + ε) * (M * P ^ ε) := by
  have hM0 : 0 < M := by linarith
  have h1 : ((rowSet K (5 / 2 * M)).card : ℝ) ≤ idealCount K (5 / 2 * M) := by
    exact_mod_cast card_rowSet_le (K := K) (5 / 2 * M)
  refine h1.trans ((hcount _ (by linarith)).trans ?_)
  rw [Real.mul_rpow (by norm_num) hM0.le, Real.rpow_add hM0, Real.rpow_one]
  have : M ^ ε ≤ P ^ ε := Real.rpow_le_rpow hM0.le hMP hε.le
  have h52 : 0 ≤ (5 / 2 : ℝ) ^ (1 + ε) := by positivity
  calc CI * ((5 / 2) ^ (1 + ε) * (M * M ^ ε)) = CI * (5 / 2) ^ (1 + ε) * (M * M ^ ε) := by ring
    _ ≤ CI * (5 / 2) ^ (1 + ε) * (M * P ^ ε) := by gcongr

theorem idealCount_le_sq {CI ε : ℝ} (hCI : 0 < CI) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcount : ∀ X : ℝ, 1 ≤ X → idealCount K X ≤ CI * X ^ (1 + ε)) {X : ℝ} (hX : 1 ≤ X) :
    idealCount K X ≤ CI * X ^ 2 := by
  refine (hcount X hX).trans (mul_le_mul_of_nonneg_left ?_ hCI.le)
  have := Real.rpow_le_rpow_of_exponent_le hX (show 1 + ε ≤ 2 by linarith)
  rwa [Real.rpow_two] at this

theorem idealCount_nonneg (X : ℝ) : 0 ≤ idealCount K X := Nat.cast_nonneg _

end ArtinPrimitiveRoots.A2.QSB0
