import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Main

/-!
# B0: parameters and the final bound
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

theorem b0_final_arith {H L A₀ b rows i2r T M Pd p1 p2 p3 p4 p5 h CL K₁ K₂ R₀ Wm CI r2 : ℝ}
    (r : ℕ) (hH : H ≤ L * A₀ * (r * (1 + b) ^ r) + (1 + b) ^ r * (rows * (Wm * i2r)))
    (hL : L ≤ h * CL * p1) (hb : (1 + b) ^ r ≤ K₂ * p4) (hA₀ : A₀ ≤ K₁ * p2 * p3 * T)
    (hrows : rows ≤ R₀ * (M * p5)) (hi2r : i2r ≤ CI * r2)
    (hP1 : p1 * p2 * p3 * p4 ≤ Pd) (hP2 : p4 * p5 ≤ Pd) (hMT : M ≤ T)
    (hL0 : 0 ≤ L) (hA₀0 : 0 ≤ A₀) (hb0 : 0 ≤ b) (hrows0 : 0 ≤ rows) (hi2r0 : 0 ≤ i2r)
    (hM0 : 0 ≤ M) (hWm : 0 ≤ Wm) (hh : 0 ≤ h) (hCL : 0 ≤ CL) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hR₀ : 0 ≤ R₀) (hCI : 0 ≤ CI) (hr2 : 0 ≤ r2) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3)
    (hp4 : 0 ≤ p4) (hp5 : 0 ≤ p5) (hT : 0 ≤ T) :
    H ≤ (h * CL * K₁ * r * K₂ + K₂ * R₀ * Wm * (CI * r2)) * Pd * T := by
  have hbr : 0 ≤ (1 + b) ^ r := by positivity
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have e1 : L * A₀ * (r * (1 + b) ^ r) ≤ (h * CL * p1) * (K₁ * p2 * p3 * T) * (r * (K₂ * p4)) := by
    gcongr
  have e2 : (1 + b) ^ r * (rows * (Wm * i2r)) ≤ (K₂ * p4) * (R₀ * (M * p5) * (Wm * (CI * r2))) := by
    gcongr
  have e3 : (h * CL * p1) * (K₁ * p2 * p3 * T) * (r * (K₂ * p4)) =
      h * CL * K₁ * r * K₂ * (p1 * p2 * p3 * p4) * T := by ring
  have e4 : (K₂ * p4) * (R₀ * (M * p5) * (Wm * (CI * r2))) =
      K₂ * R₀ * Wm * (CI * r2) * (p4 * p5) * M := by ring
  have hc1 : 0 ≤ h * CL * K₁ * r * K₂ := by positivity
  have hc2 : 0 ≤ K₂ * R₀ * Wm * (CI * r2) := by positivity
  have f1 : h * CL * K₁ * r * K₂ * (p1 * p2 * p3 * p4) * T ≤ h * CL * K₁ * r * K₂ * Pd * T := by
    gcongr
  have f2 : K₂ * R₀ * Wm * (CI * r2) * (p4 * p5) * M ≤ K₂ * R₀ * Wm * (CI * r2) * Pd * T := by
    have hPd : 0 ≤ Pd := le_trans (by positivity) hP2
    calc K₂ * R₀ * Wm * (CI * r2) * (p4 * p5) * M ≤ K₂ * R₀ * Wm * (CI * r2) * Pd * M := by
          gcongr
      _ ≤ K₂ * R₀ * Wm * (CI * r2) * Pd * T := by gcongr
  calc H ≤ L * A₀ * (r * (1 + b) ^ r) + (1 + b) ^ r * (rows * (Wm * i2r)) := hH
    _ ≤ h * CL * K₁ * r * K₂ * Pd * T + K₂ * R₀ * Wm * (CI * r2) * Pd * T := by
        rw [e3] at e1; rw [e4] at e2; linarith
    _ = (h * CL * K₁ * r * K₂ + K₂ * R₀ * Wm * (CI * r2)) * Pd * T := by ring

theorem rpow_inv_pow {N : ℝ} (hN : 0 ≤ N) {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    (N ^ ((1 : ℝ) / r)) ^ k = N ^ ((k : ℝ) / r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; congr 1; ring

theorem b0_A0_bound {rows i2G iG Wm C₄ NB G Pδ₄ Sh R₀ M Pε CI T P2η Pexp g10 : ℝ}
    (hrows : rows ≤ R₀ * (M * Pε)) (hi2G : i2G ≤ CI * (2 * G) ^ 2) (hiG : iG ≤ CI * G ^ 2)
    (hSh : Sh = 2 * P2η * T) (hG1 : 1 ≤ G) (hg10 : G ^ 10 ≤ g10)
    (hPε : Pε ≤ Pexp) (hPδη : Pδ₄ * P2η ≤ Pexp) (hMT : M ≤ T)
    (hrows0 : 0 ≤ rows) (hi2G0 : 0 ≤ i2G) (hiG0 : 0 ≤ iG) (hWm : 0 ≤ Wm) (hC₄ : 0 ≤ C₄)
    (hNB : 0 ≤ NB) (hPδ₄ : 0 ≤ Pδ₄) (hR₀ : 0 ≤ R₀) (hM : 0 ≤ M) (hPε0 : 0 ≤ Pε) (hCI : 0 ≤ CI)
    (hT : 0 ≤ T) (hP2η : 0 ≤ P2η) :
    rows * (Wm * i2G) + iG * (C₄ * (NB * G) ^ 8 * Pδ₄ * Sh) ≤
      (4 * R₀ * Wm * CI + 2 * CI * C₄ * NB ^ 8) * g10 * Pexp * T := by
  have hG0 : 0 ≤ G := by linarith
  have hG2 : G ^ 2 ≤ G ^ 10 := pow_le_pow_right₀ hG1 (by norm_num)
  have hG10 : G ^ 10 ≤ g10 := hg10
  have hPexp0 : 0 ≤ Pexp := le_trans hPε0 hPε
  have hg100 : 0 ≤ g10 := le_trans (by positivity) hg10
  have hG2g : G ^ 2 ≤ g10 := hG2.trans hG10
  have e1 : rows * (Wm * i2G) ≤ 4 * R₀ * Wm * CI * g10 * Pexp * T := by
    calc rows * (Wm * i2G) ≤ (R₀ * (M * Pε)) * (Wm * (CI * (2 * G) ^ 2)) := by gcongr
      _ = 4 * R₀ * Wm * CI * G ^ 2 * Pε * M := by ring
      _ ≤ 4 * R₀ * Wm * CI * g10 * Pexp * T := by
          have : 0 ≤ 4 * R₀ * Wm * CI := by positivity
          gcongr
  have e2 : iG * (C₄ * (NB * G) ^ 8 * Pδ₄ * Sh) ≤ 2 * CI * C₄ * NB ^ 8 * g10 * Pexp * T := by
    rw [hSh]
    calc iG * (C₄ * (NB * G) ^ 8 * Pδ₄ * (2 * P2η * T))
        ≤ (CI * G ^ 2) * (C₄ * (NB * G) ^ 8 * Pδ₄ * (2 * P2η * T)) := by gcongr
      _ = 2 * CI * C₄ * NB ^ 8 * (G ^ 2 * G ^ 8) * (Pδ₄ * P2η) * T := by ring
      _ = 2 * CI * C₄ * NB ^ 8 * G ^ 10 * (Pδ₄ * P2η) * T := by rw [← pow_add]
      _ ≤ 2 * CI * C₄ * NB ^ 8 * g10 * Pexp * T := by
          have : 0 ≤ 2 * CI * C₄ * NB ^ 8 := by positivity
          gcongr
  linarith

theorem b0_pow_bound {N P h CL Cd γL η' δ' L b : ℝ} {r : ℕ} (hN : 1 ≤ N) (hNP : N ≤ P)
    (hr : (γL + η') * (r : ℝ) = δ' / 8) (hLN : L ≤ h * (CL * N ^ γL)) (hb : b = L * Cd * N ^ η')
    (hh : 0 ≤ h) (hCL : 0 ≤ CL) (hCd : 0 ≤ Cd) (hγL : 0 ≤ γL) (hη' : 0 ≤ η') (hδ' : 0 ≤ δ')
    (hb0 : 0 ≤ b) :
    (1 + b) ^ r ≤ (1 + h * CL * Cd) ^ r * P ^ (δ' / 8) := by
  have hN0 : 0 < N := by linarith
  have hNe : 1 ≤ N ^ (γL + η') := Real.one_le_rpow hN (by positivity)
  have hb' : b ≤ h * CL * Cd * N ^ (γL + η') := by
    rw [hb, Real.rpow_add hN0]
    have hNη : 0 ≤ N ^ η' := by positivity
    calc L * Cd * N ^ η' ≤ (h * (CL * N ^ γL)) * Cd * N ^ η' := by gcongr
      _ = h * CL * Cd * (N ^ γL * N ^ η') := by ring
  have h1b : 1 + b ≤ (1 + h * CL * Cd) * N ^ (γL + η') := by
    have e : (1 + h * CL * Cd) * N ^ (γL + η') = N ^ (γL + η') + h * CL * Cd * N ^ (γL + η') := by
      ring
    rw [e]; linarith
  have hexpo : (N ^ (γL + η')) ^ r = N ^ (δ' / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, hr]
  calc (1 + b) ^ r ≤ ((1 + h * CL * Cd) * N ^ (γL + η')) ^ r :=
        pow_le_pow_left₀ (by positivity) h1b r
    _ = (1 + h * CL * Cd) ^ r * (N ^ (γL + η')) ^ r := by rw [mul_pow]
    _ = (1 + h * CL * Cd) ^ r * N ^ (δ' / 8) := by rw [hexpo]
    _ ≤ (1 + h * CL * Cd) ^ r * P ^ (δ' / 8) := by
        have : 0 ≤ (1 + h * CL * Cd) ^ r := by positivity
        gcongr

theorem b0_G10 {N P δ' : ℝ} {r : ℕ} (hr0 : r ≠ 0) (hN : 1 ≤ N) (hNP : N ≤ P)
    (h10 : (10 : ℝ) / r ≤ δ' / 6) (hδ' : 0 ≤ δ') :
    (N ^ ((1 : ℝ) / r)) ^ 10 ≤ P ^ (δ' / 6) := by
  have hN0 : 0 < N := by linarith
  rw [rpow_inv_pow hN0.le hr0]
  calc N ^ (((10 : ℕ) : ℝ) / (r : ℝ)) ≤ N ^ (δ' / 6) :=
        Real.rpow_le_rpow_of_exponent_le hN (by push_cast; exact h10)
    _ ≤ P ^ (δ' / 6) := Real.rpow_le_rpow hN0.le hNP (by positivity)

theorem b0_kappa {M N η : ℝ} (hM : 0 < M) (hN : 1 ≤ N) (hPη : 1 ≤ (M * N) ^ η)
    (h1 : 2 * N * (M * N) ^ η ≤ M) (h2 : M ≤ N ^ (2 : ℝ)) :
    1 ≤ N ^ (2 : ℝ) / M * (M * N) ^ η ∧ 2 * (N ^ (2 : ℝ) / M * (M * N) ^ η) ≤ M ∧
      N ^ (2 : ℝ) / M * (M * N) ^ η * M = N ^ 2 * (M * N) ^ η := by
  have hN2 : N ^ (2 : ℝ) = N ^ 2 := Real.rpow_two N
  have hκMeq : N ^ (2 : ℝ) / M * (M * N) ^ η * M = N ^ 2 * (M * N) ^ η := by
    rw [hN2]; field_simp
  refine ⟨?_, ?_, hκMeq⟩
  · have h' : 1 ≤ N ^ (2 : ℝ) / M := by rw [le_div_iff₀ hM]; linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ N ^ (2 : ℝ) / M * (M * N) ^ η := mul_le_mul h' hPη zero_le_one (by linarith)
  · set Q := (M * N) ^ η with hQ
    have hsq : (2 * N * Q) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have hPη2 : Q ≤ Q ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by positivity) hPη
    have hN2' : 0 ≤ N ^ 2 := sq_nonneg N
    have hA : 2 * (N ^ 2 * Q) ≤ (2 * N * Q) ^ 2 := by
      calc 2 * (N ^ 2 * Q) ≤ 4 * (N ^ 2 * Q) := by
            have : 0 ≤ N ^ 2 * Q := by positivity
            linarith
        _ ≤ 4 * (N ^ 2 * Q ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPη2 hN2') (by norm_num)
        _ = (2 * N * Q) ^ 2 := by ring
    have hB : 2 * (N ^ (2 : ℝ) / M * Q) * M ≤ M * M := by
      calc 2 * (N ^ (2 : ℝ) / M * Q) * M = 2 * (N ^ (2 : ℝ) / M * Q * M) := by ring
        _ = 2 * (N ^ 2 * Q) := by rw [hκMeq]
        _ ≤ (2 * N * Q) ^ 2 := hA
        _ ≤ M ^ 2 := hsq
        _ = M * M := sq M
    exact le_of_mul_le_mul_right hB hM

theorem b0_margin_real {NB Ng n M N X P θ η : ℝ} (hNB : 0 ≤ NB) (hNg : 1 ≤ Ng) (hn : 1 ≤ n)
    (hnX : n * Ng ≤ X) (hXN : X ≤ N) (hM : 0 ≤ M) (hN0 : 0 ≤ N) (hP : P = M * N) (hP0 : 0 < P)
    (hθ : θ = η / 2) (hθ0 : 0 ≤ θ) (hNBP : NB ≤ P ^ (η / 2)) :
    NB * Ng * n ^ 2 * (M * n) ^ θ ≤ N ^ 2 * P ^ η := by
  have hnN' : n * Ng ≤ N := hnX.trans hXN
  have hnN : n ≤ N := le_trans (by nlinarith) hnN'
  have hMn : (M * n) ^ θ ≤ P ^ θ := by
    rw [hP]
    exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hnN hM) hθ0
  have hPθ : P ^ θ * P ^ (η / 2) = P ^ η := by
    rw [← Real.rpow_add hP0, hθ]; congr 1; ring
  have hθp : 0 ≤ P ^ θ := by positivity
  have hn0 : 0 ≤ n := by linarith
  calc NB * Ng * n ^ 2 * (M * n) ^ θ = NB * (n * Ng) * n * (M * n) ^ θ := by ring
    _ ≤ NB * N * N * P ^ θ := by gcongr
    _ ≤ P ^ (η / 2) * N * N * P ^ θ := by gcongr
    _ = N ^ 2 * (P ^ θ * P ^ (η / 2)) := by ring
    _ = N ^ 2 * P ^ η := by rw [hPθ]

set_option maxHeartbeats 1000000 in
open Classical in
/-- The main regime of B0: `N ≥ 2^r` and `N(bad)^{2/η} ≤ MN`. -/
theorem b0_regime [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    {Wm C₄ Cd CI CL δ' : ℝ} (r : ℕ) (hr0 : r ≠ 0)
    (hWm0 : 0 ≤ Wm) (hWm : ∀ x : ℝ, 0 ≤ x → W x ≤ Wm) (hC₄ : 0 < C₄) (hCd : 0 < Cd)
    (hCI : 0 < CI) (hCL : 0 < CL) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (h10r : (10 : ℝ) / r ≤ δ' / 6)
    (hC4 : ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ (δ' / 16 / 2) ≤ κ * M →
        ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
          C₄ * qsN 𝔮 ^ 8 * (M * n) ^ (δ' / 16) * qsBlockShape M n κ α *
            ∑ c ∈ cols, ‖z c‖ ^ 2)
    (hdesc : ∀ (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ N → 1 ≤ G →
      (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N) →
      ‖∑ g ∈ ((cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)).filter (fun g => G < qsN g),
          qsGcdBlock F W M κ g cols z‖ ≤
        Cd * N ^ (δ' / (16 * r)) * qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2)
    (hcount : ∀ X : ℝ, 1 ≤ X → idealCount K X ≤ CI * X ^ (1 + δ' / 16))
    (hlog : ∀ X : ℝ, 1 ≤ X →
      ((Nat.ceil (Real.logb 2 X) + 1 : ℕ) : ℝ) ≤ CL * X ^ (δ' / (16 * r)))
    (M N : ℝ) (hN : 1 ≤ N) (h1 : 2 * N * (M * N) ^ (δ' / 16) ≤ M) (h2 : M ≤ N ^ (2 : ℝ))
    (hMs : 1 / 3 ≤ M) (hNr : (2 : ℝ) ^ r ≤ N)
    (hPP₀ : qsN (qsBadRad m qS) ^ (2 / (δ' / 16)) ≤ M * N) :
    qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16)) ≤
      ((Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL *
          (4 * (CI * (5 / 2) ^ (1 + δ' / 16)) * Wm * CI +
            2 * CI * C₄ * qsN (qsBadRad m qS) ^ 8) * r *
          (1 + (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL * Cd) ^ r +
        (1 + (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL * Cd) ^ r *
          (CI * (5 / 2) ^ (1 + δ' / 16)) * Wm * (CI * ((2 : ℝ) ^ r) ^ 2)) *
        (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
  have hη0 : (0 : ℝ) < δ' / 16 := by positivity
  have hγ0 : (0 : ℝ) < δ' / (16 * r) := by positivity
  have hh0 : (0 : ℝ) ≤ (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) := Nat.cast_nonneg _
  have hNB : 0 < qsN (qsBadRad m qS) := qsN_badRad_pos hqS
  have hN0 : 0 < N := by linarith
  have hMpos : 0 < M := by linarith
  have hM0 : 0 ≤ M := hMpos.le
  have hP1 : 1 < M * N := P_gt_one hN hη0 (by linarith) hMpos h1
  have hP0 : 0 < M * N := by linarith
  have hPη : 1 ≤ (M * N) ^ (δ' / 16) := Real.one_le_rpow hP1.le hη0.le
  have hM2 : 2 * N ≤ M := by
    have := mul_le_mul_of_nonneg_left hPη (by positivity : (0:ℝ) ≤ 2 * N)
    linarith
  have hM1 : 1 ≤ M := by linarith
  have hMP : M ≤ M * N := le_mul_of_one_le_right hM0 hN
  have hNP : N ≤ M * N := le_mul_of_one_le_left hN0.le hM1
  have hT3 : 0 ≤ N ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  have hT0 : 0 ≤ M + N + N ^ (2 * α - 1) * M ^ (1 - α) := by linarith
  have hMT : M ≤ M + N + N ^ (2 * α - 1) * M ^ (1 - α) := by linarith
  have hε0 : (0 : ℝ) < δ' / 16 := hη0
  have hrows := rowSet_card_le (K := K) hCI hε0 hcount hM1 hMP
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = N ^ ((1 : ℝ) / r) := ⟨_, rfl⟩
  have hGr : G ^ r = N := by
    rw [hGdef, rpow_inv_pow hN0.le hr0, div_self hrR.ne', Real.rpow_one]
  have hG2 : 2 ≤ G := by
    have h2r : ((2 : ℝ) ^ r) ^ ((1 : ℝ) / r) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_one_div_cancel hrR.ne', Real.rpow_one]
    rw [hGdef]
    calc (2 : ℝ) = ((2 : ℝ) ^ r) ^ ((1 : ℝ) / r) := h2r.symm
      _ ≤ N ^ ((1 : ℝ) / r) := Real.rpow_le_rpow (by positivity) hNr (by positivity)
  have hG1 : 1 ≤ G := by linarith
  obtain ⟨hκ1, hκM, hκMeq⟩ := b0_kappa hMpos hN hPη h1 h2
  have hNBP : qsN (qsBadRad m qS) ≤ (M * N) ^ (δ' / 16 / 2) := by
    have e : 2 / (δ' / 16) * (δ' / 16 / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm (2 : ℝ) (δ' / 16)]; exact div_self (by positivity)
    calc qsN (qsBadRad m qS) = (qsN (qsBadRad m qS) ^ (2 / (δ' / 16))) ^ (δ' / 16 / 2) := by
          rw [← Real.rpow_mul hNB.le, e, Real.rpow_one]
      _ ≤ (M * N) ^ (δ' / 16 / 2) := Real.rpow_le_rpow (by positivity) hPP₀ (by positivity)
  have hmargin : ∀ X : ℝ, X ≤ N → ∀ (g : Ideal (𝓞 K)) (n : ℝ), 0 < qsN g → qsN g ≤ G →
      1 ≤ n → n * qsN g ≤ X →
      qsN (qsBadRad m qS * g) * n ^ 2 * (M * n) ^ (δ' / 16 / 2) ≤
        N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16) * M := by
    intro X hXN g n hg _ hn hnX
    have hg0 : g ≠ ⊥ := fun h0 => by rw [h0] at hg; simp [qsN] at hg
    rw [qsN_mul, hκMeq]
    exact b0_margin_real hNB.le (one_le_qsN hg0) hn hnX hXN hM0 hN0.le rfl hP0 rfl
      (by positivity) hNBP
  have hshape : ∀ n : ℝ, 1 ≤ n → n ≤ N →
      qsBlockShape M n (N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16)) α ≤
        2 * (M * N) ^ (2 * (δ' / 16)) * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) :=
    fun n hn hnN => shape_le hMpos hN (by linarith) hnN hη0.le hα1 hα2 hP1.le
  have hrec := b0_recursion F hrf hqS W hW α hWm hC₄ (by positivity) hCd hγ0.le hC4 hdesc
    M N (N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16)) G
    (2 * (M * N) ^ (2 * (δ' / 16)) * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) r hMpos hN hG2
    hGr hκ1 hκM hmargin hshape (by positivity)
  have hLN : (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
      ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ≤
      (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * (CL * N ^ (δ' / (16 * r))) :=
    mul_le_mul_of_nonneg_left (hlog N hN) hh0
  have hLb : (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
      ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ≤
      (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL * (M * N) ^ (δ' / (16 * r)) := by
    have hNγ : N ^ (δ' / (16 * r)) ≤ (M * N) ^ (δ' / (16 * r)) :=
      Real.rpow_le_rpow hN0.le hNP hγ0.le
    calc _ ≤ (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * (CL * N ^ (δ' / (16 * r))) :=
          hLN
      _ ≤ (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            (CL * (M * N) ^ (δ' / (16 * r))) := by gcongr
      _ = _ := by ring
  have hrγ : (δ' / (16 * r) + δ' / (16 * r)) * (r : ℝ) = δ' / 8 := by
    field_simp; ring
  have hbr := b0_pow_bound (P := M * N)
    (b := (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
      ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) * Cd * N ^ (δ' / (16 * r)))
    hN hNP hrγ hLN rfl hh0 hCL.le hCd.le hγ0.le hγ0.le hδ'0.le (by positivity)
  have hG10 : G ^ 10 ≤ (M * N) ^ (δ' / 6) := by
    rw [hGdef]; exact b0_G10 hr0 hN hNP h10r hδ'0.le
  have hi2G : idealCount K (2 * G) ≤ CI * (2 * G) ^ 2 :=
    idealCount_le_sq hCI hε0 (by linarith) hcount (by linarith)
  have hiG : idealCount K G ≤ CI * G ^ 2 :=
    idealCount_le_sq hCI hε0 (by linarith) hcount hG1
  have hPexp : (M * N) ^ (δ' / 16) ≤ (M * N) ^ (δ' / 16 + δ' / 16 + 2 * (δ' / 16)) :=
    Real.rpow_le_rpow_of_exponent_le hP1.le (by linarith)
  have hPδη : (M * N) ^ (δ' / 16) * (M * N) ^ (2 * (δ' / 16)) ≤
      (M * N) ^ (δ' / 16 + δ' / 16 + 2 * (δ' / 16)) := by
    rw [← Real.rpow_add hP0]
    exact Real.rpow_le_rpow_of_exponent_le hP1.le (by linarith)
  have hA₀ := b0_A0_bound (Wm := Wm) (C₄ := C₄) (NB := qsN (qsBadRad m qS))
    (Pδ₄ := (M * N) ^ (δ' / 16)) (R₀ := CI * (5 / 2) ^ (1 + δ' / 16)) (M := M) (CI := CI)
    (T := M + N + N ^ (2 * α - 1) * M ^ (1 - α)) (P2η := (M * N) ^ (2 * (δ' / 16)))
    hrows hi2G hiG rfl hG1 hG10 hPexp hPδη hMT (Nat.cast_nonneg _) (idealCount_nonneg _)
    (idealCount_nonneg _) hWm0 hC₄.le hNB.le (by positivity) (by positivity) hM0
    (by positivity) hCI.le hT0 (by positivity)
  have hi2r : idealCount K (2 ^ r) ≤ CI * ((2 : ℝ) ^ r) ^ 2 :=
    idealCount_le_sq hCI hε0 (by linarith) hcount (one_le_pow₀ (by norm_num))
  have hP1' : (M * N) ^ (δ' / (16 * r)) * (M * N) ^ (δ' / 6) *
      (M * N) ^ (δ' / 16 + δ' / 16 + 2 * (δ' / 16)) * (M * N) ^ (δ' / 8) ≤ (M * N) ^ δ' := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0, ← Real.rpow_add hP0]
    refine Real.rpow_le_rpow_of_exponent_le hP1.le ?_
    have hγ : δ' / (16 * r) ≤ δ' / 16 :=
      div_le_div_of_nonneg_left hδ'0.le (by norm_num) (by
        have : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
        linarith)
    linarith
  have hP2' : (M * N) ^ (δ' / 8) * (M * N) ^ (δ' / 16) ≤ (M * N) ^ δ' := by
    rw [← Real.rpow_add hP0]
    exact Real.rpow_le_rpow_of_exponent_le hP1.le (by linarith)
  have hA₀0 : 0 ≤ ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * idealCount K (2 * G)) +
      idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * N) ^ (δ' / 16) *
        (2 * (M * N) ^ (2 * (δ' / 16)) * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)))) := by
    refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hWm0 (idealCount_nonneg _)))
      (mul_nonneg (idealCount_nonneg _) ?_)
    refine mul_nonneg (mul_nonneg (mul_nonneg hC₄.le (pow_nonneg (mul_nonneg hNB.le
      (by linarith)) 8)) (by positivity)) ?_
    exact mul_nonneg (by positivity) hT0
  exact b0_final_arith r hrec hLb hbr hA₀ hrows hi2r hP1' hP2' hMT (by positivity)
    hA₀0 (by positivity) (Nat.cast_nonneg _) (idealCount_nonneg _) hM0 hWm0 hh0 hCL.le
    (by positivity) (by positivity) (by positivity) hCI.le (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) hT0

set_option maxHeartbeats 400000 in
open Classical in
/-- B0. -/
theorem b0_main [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N →
      2 * N * (M * N) ^ η ≤ M → M ≤ N ^ (2 : ℝ) →
      qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ η) ≤
        C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = min δ 1 := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ'def]; exact lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := by rw [hδ'def]; exact min_le_right _ _
  have hδ'δ : δ' ≤ δ := by rw [hδ'def]; exact min_le_left _ _
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ⌈64 / δ'⌉₊ + 1 := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
  have hr64 : 64 / δ' ≤ r := by
    have h1 := Nat.le_ceil (64 / δ')
    have h2 : ((⌈64 / δ'⌉₊ : ℕ) : ℝ) ≤ r := by rw [hrdef]; push_cast; linarith
    linarith
  have h10r : (10 : ℝ) / r ≤ δ' / 6 := by
    rw [div_le_div_iff₀ hrR (by norm_num)]
    rw [div_le_iff₀ hδ'0] at hr64
    nlinarith
  obtain ⟨C₄, hC₄, hC4⟩ := qs_residual_block_bound_C4 F hrf hqS W hW α hα1 hα2 hexp
    (δ' / 16 / 2) (by positivity) (δ' / 16) (by positivity)
  obtain ⟨Cd, hCd, hdesc⟩ := qs_gcd_descent_S0 F hrf W hW (δ' / (16 * r)) (by positivity)
  obtain ⟨CI, hCI, hcount⟩ := qs_ideal_count_M1 (K := K) (δ' / 16) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := ceil_logb_le (show (0 : ℝ) < δ' / (16 * r) by positivity)
  obtain ⟨Wm, hWm0, hWm⟩ := capWeight_bounded hW
  have hNB : 0 < qsN (qsBadRad m qS) := qsN_badRad_pos hqS
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, N₁ = max ((2 : ℝ) ^ r) (qsN (qsBadRad m qS) ^ (2 / (δ' / 16))) :=
    ⟨_, rfl⟩
  obtain ⟨Ktriv, hKtriv⟩ : ∃ K : ℝ, K = CI * (5 / 2) ^ (1 + δ' / 16) * Wm * (CI * N₁ ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨Kmain, hKmain⟩ : ∃ K : ℝ, K =
      (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL *
          (4 * (CI * (5 / 2) ^ (1 + δ' / 16)) * Wm * CI +
            2 * CI * C₄ * qsN (qsBadRad m qS) ^ 8) * r *
          (1 + (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL * Cd) ^ r +
        (1 + (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) * CL * Cd) ^ r *
          (CI * (5 / 2) ^ (1 + δ' / 16)) * Wm * (CI * ((2 : ℝ) ^ r) ^ 2) := ⟨_, rfl⟩
  have hKtriv0 : 0 ≤ Ktriv := by rw [hKtriv]; positivity
  have hKmain0 : 0 ≤ Kmain := by
    rw [hKmain]
    have : (0 : ℝ) ≤ Nat.card (ClassFieldTheory.RayClassGroup m) := Nat.cast_nonneg _
    positivity
  refine ⟨δ' / 16, by positivity, by linarith, Ktriv + Kmain + 1, by positivity, ?_⟩
  intro M N hN h1 h2
  have hM0 : 0 ≤ M := M_nonneg hN (by positivity) (by linarith) h1
  have hN0 : 0 < N := by linarith
  have hT3 : 0 ≤ N ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  have hT0 : 0 ≤ M + N + N ^ (2 * α - 1) * M ^ (1 - α) := by linarith
  have hMT : M ≤ M + N + N ^ (2 * α - 1) * M ^ (1 - α) := by linarith
  by_cases hMs : M < 1 / 3
  · rw [qsHighNorm_eq_zero_of_small_M F W hMs]
    have : 0 ≤ (M * N) ^ δ := Real.rpow_nonneg (by positivity) _
    positivity
  push Not at hMs
  have hMpos : 0 < M := by linarith
  have hP1 : 1 < M * N := P_gt_one hN (by positivity) (by linarith) hMpos h1
  have hP0 : 0 < M * N := by linarith
  have hPη : 1 ≤ (M * N) ^ (δ' / 16) := Real.one_le_rpow hP1.le (by positivity)
  have hM1 : 1 ≤ M := by
    have := mul_le_mul_of_nonneg_left hPη (by positivity : (0:ℝ) ≤ 2 * N)
    linarith
  have hMP : M ≤ M * N := le_mul_of_one_le_right hM0 hN
  have hNP : N ≤ M * N := le_mul_of_one_le_left hN0.le hM1
  have hPδ : (M * N) ^ δ' ≤ (M * N) ^ δ := Real.rpow_le_rpow_of_exponent_le hP1.le hδ'δ
  suffices hK : qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16)) ≤
      (Ktriv + Kmain) * (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) by
    refine hK.trans ?_
    have : 0 ≤ (M * N) ^ δ' := by positivity
    exact mul_le_mul (mul_le_mul (by linarith) hPδ this (by positivity)) le_rfl hT0
      (by positivity)
  by_cases hbig : (2 : ℝ) ^ r ≤ N ∧ qsN (qsBadRad m qS) ^ (2 / (δ' / 16)) ≤ M * N
  · have hreg := b0_regime F hrf hqS W hW α hα1 hα2 r hr0 hWm0 hWm hC₄ hCd hCI hCL hδ'0 hδ'1
      h10r hC4 hdesc hcount hlog M N hN h1 h2 hMs hbig.1 hbig.2
    rw [← hKmain] at hreg
    refine hreg.trans ?_
    have hXY : 0 ≤ (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) :=
      mul_nonneg (by positivity) hT0
    calc Kmain * (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))
        = Kmain * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) := by ring
      _ ≤ Ktriv * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) +
          Kmain * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) :=
          le_add_of_nonneg_left (mul_nonneg hKtriv0 hXY)
      _ = (Ktriv + Kmain) * (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by ring
  · have hNN₁ : N ≤ N₁ := by
      rw [hN₁]
      rcases not_and_or.mp hbig with h | h
      · exact le_max_of_le_left (not_le.mp h).le
      · exact le_max_of_le_right (hNP.trans (not_le.mp h).le)
    have htr := highNorm_trivial F hW hWm (X := N) (κ := N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16))
      hMpos
    have hiN : idealCount K N ≤ CI * N₁ ^ 2 :=
      (idealCount_le_sq hCI (by positivity) (by linarith) hcount hN).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN0.le hNN₁ 2) hCI.le)
    have hrows := rowSet_card_le (K := K) hCI (by positivity) hcount hM1 hMP
    have hPε : (M * N) ^ (δ' / 16) ≤ (M * N) ^ δ' :=
      Real.rpow_le_rpow_of_exponent_le hP1.le (by linarith)
    have hiN0 : 0 ≤ idealCount K N := idealCount_nonneg N
    have hR0 : 0 ≤ CI * (5 / 2) ^ (1 + δ' / 16) := by positivity
    calc qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ (δ' / 16))
        ≤ (rowSet K (5 / 2 * M)).card * (Wm * idealCount K N) := htr
      _ ≤ CI * (5 / 2) ^ (1 + δ' / 16) * (M * (M * N) ^ (δ' / 16)) * (Wm * (CI * N₁ ^ 2)) := by
          gcongr
      _ = Ktriv * ((M * N) ^ (δ' / 16) * M) := by rw [hKtriv]; ring
      _ ≤ Ktriv * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) := by
          have : 0 ≤ (M * N) ^ (δ' / 16) := by positivity
          gcongr
      _ ≤ (Ktriv + Kmain) * (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
          have hXY : 0 ≤ (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) :=
            mul_nonneg (by positivity) hT0
          calc Ktriv * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)))
              ≤ Ktriv * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) +
                Kmain * ((M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) :=
                le_add_of_nonneg_right (mul_nonneg hKmain0 hXY)
            _ = (Ktriv + Kmain) * (M * N) ^ δ' * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
                ring

end ArtinPrimitiveRoots.A2.QSB0
