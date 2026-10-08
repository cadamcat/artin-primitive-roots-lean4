import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.TransBound

/-!
# C3c: the dual transition remainder

Assembly: the per-pair block decomposition (`dualTrans_decomp`), pulling the finite block sums
out of the pair sum, the block bound (`block_bound`) uniformly in the block, and the counts
`#{e ∣ 𝔮} ≪ N𝔮`, `#{a₂ ∣ R} = O(1)`, `#{row dyads}, #{divisor dyads} ≪ (Mn)^{δ/16}`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSC2 QSP2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

theorem log_count_le {X γ : ℝ} (hX : 1 ≤ X) (hγ : 0 < γ) :
    ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (1 / (γ * Real.log 2) + 1) * X ^ γ := by
  have hX0 : 0 < X := by linarith
  have hN : ⌊X⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hX
    omega
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := Nat.log 2 ⌊X⌋₊ with hL
  have h2L : ((2 : ℝ) ^ L) ≤ X := by
    have h1 : 2 ^ L ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 hN
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
    calc ((2 : ℝ) ^ L) = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ X := h2
  have hlog : (L : ℝ) * Real.log 2 ≤ X ^ γ / γ := by
    calc (L : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ L) := by rw [Real.log_pow]
      _ ≤ Real.log X := Real.log_le_log (by positivity) h2L
      _ ≤ X ^ γ / γ := Real.log_le_rpow_div hX0.le hγ
  have hXγ : 1 ≤ X ^ γ := Real.one_le_rpow hX hγ.le
  have hL' : (L : ℝ) ≤ X ^ γ / (γ * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (L : ℝ) * (γ * Real.log 2) = γ * ((L : ℝ) * Real.log 2) := by ring
      _ ≤ γ * (X ^ γ / γ) := mul_le_mul_of_nonneg_left hlog hγ.le
      _ = X ^ γ := by field_simp
  push_cast
  calc (L : ℝ) + 1 ≤ X ^ γ / (γ * Real.log 2) + X ^ γ := by linarith
    _ = (1 / (γ * Real.log 2) + 1) * X ^ γ := by ring

theorem two_pow_le_of_lt_log {X : ℝ} (hX : 1 ≤ X) {k : ℕ} (hk : k < Nat.log 2 ⌊X⌋₊ + 1) :
    (2 : ℝ) ^ k ≤ X := by
  have hX0 : 0 < X := by linarith
  have hN : ⌊X⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hX
    omega
  have h1 : 2 ^ k ≤ 2 ^ Nat.log 2 ⌊X⌋₊ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.log 2 ⌊X⌋₊ ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 hN
  have h3 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  calc ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ X := h3

theorem lt_two_pow_log {X : ℝ} (hX : 0 ≤ X) : X < 2 ^ (Nat.log 2 ⌊X⌋₊ + 1) := by
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊X⌋₊
  have h2 := Nat.lt_floor_add_one X
  have h3 : ((⌊X⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊X⌋₊).succ : ℕ) : ℝ) := by
    exact_mod_cast h1
  calc X < ⌊X⌋₊ + 1 := h2
    _ ≤ ((2 ^ (Nat.log 2 ⌊X⌋₊).succ : ℕ) : ℝ) := h3
    _ = 2 ^ (Nat.log 2 ⌊X⌋₊ + 1) := by push_cast; rfl

theorem norm_sum5_le {ι₁ ι₂ ι₃ ι₄ ι₅ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (s₃ : Finset ι₃) (s₄ : Finset ι₄) (s₅ : Finset ι₅) (f : ι₁ → ι₂ → ι₃ → ι₄ → ι₅ → ℂ)
    (U : ℝ) (hU : ∀ a ∈ s₁, ∀ b ∈ s₂, ∀ c ∈ s₃, ∀ d ∈ s₄, ∀ e ∈ s₅, ‖f a b c d e‖ ≤ U) :
    ‖∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ e ∈ s₅, f a b c d e‖ ≤
      (s₁.card : ℝ) * s₂.card * s₃.card * s₄.card * s₅.card * U := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ s₁, ‖∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ e ∈ s₅, f a b c d e‖
      ≤ ∑ a ∈ s₁, ((s₂.card : ℝ) * s₃.card * s₄.card * s₅.card * U) := by
        refine Finset.sum_le_sum fun a ha => (norm_sum_le _ _).trans ?_
        calc ∑ b ∈ s₂, ‖∑ c ∈ s₃, ∑ d ∈ s₄, ∑ e ∈ s₅, f a b c d e‖
            ≤ ∑ b ∈ s₂, ((s₃.card : ℝ) * s₄.card * s₅.card * U) := by
              refine Finset.sum_le_sum fun b hb => (norm_sum_le _ _).trans ?_
              calc ∑ c ∈ s₃, ‖∑ d ∈ s₄, ∑ e ∈ s₅, f a b c d e‖
                  ≤ ∑ c ∈ s₃, ((s₄.card : ℝ) * s₅.card * U) := by
                    refine Finset.sum_le_sum fun c hc => (norm_sum_le _ _).trans ?_
                    calc ∑ d ∈ s₄, ‖∑ e ∈ s₅, f a b c d e‖
                        ≤ ∑ d ∈ s₄, ((s₅.card : ℝ) * U) := by
                          refine Finset.sum_le_sum fun d hd => (norm_sum_le _ _).trans ?_
                          calc ∑ e ∈ s₅, ‖f a b c d e‖ ≤ ∑ e ∈ s₅, U :=
                                Finset.sum_le_sum fun e he => hU a ha b hb c hc d hd e he
                            _ = (s₅.card : ℝ) * U := by rw [Finset.sum_const, nsmul_eq_mul]
                      _ = (s₄.card : ℝ) * s₅.card * U := by
                          rw [Finset.sum_const, nsmul_eq_mul]; ring
                _ = (s₃.card : ℝ) * s₄.card * s₅.card * U := by
                    rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ = (s₂.card : ℝ) * s₃.card * s₄.card * s₅.card * U := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = (s₁.card : ℝ) * s₂.card * s₃.card * s₄.card * s₅.card * U := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem final_arith {A1 A2 A3 A4 A5 U Cd TR CL Cb N8 P γ δ Y Sz shape c4 : ℝ}
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hA4 : 0 ≤ A4) (hA5 : 0 ≤ A5) (hU0 : 0 ≤ U)
    (hCd : 0 ≤ Cd) (hTR : 0 ≤ TR) (hCL : 0 ≤ CL) (hCb : 0 ≤ Cb) (hN8 : 0 ≤ N8) (hP : 0 < P)
    (hc4 : 0 ≤ c4) (hY : 0 ≤ Y) (hSz : 0 ≤ Sz)
    (h1 : A1 ≤ Cd * N8) (h2 : A2 ≤ TR + 1) (h3 : A3 ≤ CL * P ^ γ) (h4 : A4 ≤ CL * P ^ γ)
    (h5 : A5 ≤ CL * P ^ γ)
    (hU : U ≤ Cb * P ^ (δ / 8) * (c4 * P ^ (δ / 8)) * P ^ (3 * δ / 16) * Y * Sz)
    (hPδ : P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3 ≤ P ^ δ)
    (hYs : Y ≤ shape) :
    A1 * A2 * A3 * A4 * A5 * U ≤ Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 * P ^ δ * shape * Sz := by
  have hPγ : 0 ≤ P ^ γ := by positivity
  calc A1 * A2 * A3 * A4 * A5 * U
      ≤ (Cd * N8) * (TR + 1) * (CL * P ^ γ) * (CL * P ^ γ) * (CL * P ^ γ) *
          (Cb * P ^ (δ / 8) * (c4 * P ^ (δ / 8)) * P ^ (3 * δ / 16) * Y * Sz) := by
        gcongr
    _ = Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 *
          (P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3) * Y * Sz := by ring
    _ ≤ Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 * P ^ δ * shape * Sz := by
        have h0 : 0 ≤ Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 := by positivity
        have hPd0 : 0 ≤ P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3 := by
          positivity
        calc Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 *
              (P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3) * Y * Sz
            ≤ Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 * P ^ δ * Y * Sz := by gcongr
          _ ≤ Cd * (TR + 1) * CL ^ 3 * c4 * Cb * N8 * P ^ δ * shape * Sz := by
              have : 0 ≤ P ^ δ := by positivity
              gcongr

set_option maxHeartbeats 400000 in
open Classical in
/-- C3c. -/
theorem c3c_main [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨Cb, hCb, hblk⟩ := block_bound F hrf W hW α hα1 hα2 hexp (δ / 8) (by positivity)
    (δ / 8) (by positivity)
  obtain ⟨Cd, hCd, hdiv⟩ := qs_divisor_bound_M1 (K := K) 1 one_pos
  set TR : ℝ := ((qsDivisors (badIdeal m qS)).card : ℝ) with hTR
  set γ : ℝ := δ / 16 with hγ
  have hγ0 : 0 < γ := by positivity
  set CL : ℝ := (1 / (γ * Real.log 2) + 1) * 2 ^ γ with hCL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL0 : 0 < CL := by positivity
  refine ⟨δ / 8, by positivity, fun η hη hηδ => ?_⟩
  refine ⟨Cd * (TR + 1) * CL ^ 3 * 4 ^ (δ / 8) * Cb, by positivity, ?_⟩
  intro M n κ 𝔮 cols z hn hκ hMκ hblock
  have hM : 0 < M := by linarith
  have hn0 : 0 < n := by linarith
  set P : ℝ := M * n with hPdef
  have hP1 : 1 ≤ P := by nlinarith
  have hP0 : 0 < P := by linarith
  set Λ : ℝ := P ^ η with hΛdef
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hP1 hη.le
  set KB := Nat.log 2 ⌊κ⌋₊ + 1 with hKBdef
  set J := Nat.log 2 ⌊2 * n⌋₊ + 1 with hJdef
  have hKB : κ < 2 ^ KB := lt_two_pow_log (by linarith)
  have hJ : 2 * n < 2 ^ J := lt_two_pow_log (by linarith)
  obtain ⟨h𝔮sq, h𝔮bad, hcols, hcl⟩ := hblock
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    rintro rfl
    exact bot_ne_top (Ideal.isUnit_iff.mp (h𝔮sq ⊥ (Ideal.dvd_iff_le.mpr bot_le)))
  have hblock : QSBlockCols m qS 𝔮 n cols := ⟨h𝔮sq, h𝔮bad, hcols, hcl⟩
  set S := qsSqfUpTo (K := K) κ ⊤ with hS
  set R := badIdeal m qS with hR
  -- the block decomposition of the pair sum
  have hdec : qsPairSum cols z (qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮) =
      ∑ e ∈ qsDivisors 𝔮, ∑ a₂ ∈ qsDivisors R, ∑ k ∈ Finset.range KB,
        ∑ j₁ ∈ Finset.range J, ∑ j₂ ∈ Finset.range J,
          ∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
            (((qsMu e : ℂ) * twist F c e * twist F c a₂) * (twistInv F d e * twistInv F d a₂) *
              ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
                ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                  (qsMu (e₁ * e₂) : ℂ) *
                    ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
                      rhoT S R a₂ k a₁ *
                        (F.character c).idealValue a₁ * (F.character d).idealValue a₁ *
                          phiT K W M n Λ (qsN e) (qsN a₂) k (2 ^ j₁ * 2 ^ j₂) (qsN a₁)
                            (qsN (e₁ * e₂)) (qsN (c * d))) else 0 := by
    unfold qsPairSum
    simp only [← pair_sum_sum]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    by_cases hcd : IsCoprime c d
    · rw [if_pos hcd, if_pos hcd,
        dualTrans_decomp F hrf hqS W M κ Λ n 𝔮 cols hblock KB J hKB hJ hc hd hcd]
      simp only [Finset.mul_sum]
      rfl
    · rw [if_neg hcd, if_neg hcd]
  rw [hdec]
  have hκM : κ ≤ M := by linarith
  have hκ0 : 0 < κ := by linarith
  set Y := M + Real.sqrt M * κ ^ (α - 1/2) with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ κ ^ (α - 1/2) := Real.rpow_nonneg hκ0.le _
    positivity
  set Sz := ∑ c ∈ cols, ‖z c‖ ^ 2 with hSz
  have hSz0 : 0 ≤ Sz := Finset.sum_nonneg fun c _ => sq_nonneg _
  set U := Cb * (n * κ) ^ (δ / 8) * (4 * n * κ) ^ (δ / 8) * Λ ^ (3/2 : ℝ) * Y * Sz with hUdef
  have hU : ∀ e ∈ qsDivisors 𝔮, ∀ a₂ ∈ qsDivisors R, ∀ k ∈ Finset.range KB,
      ∀ j₁ ∈ Finset.range J, ∀ j₂ ∈ Finset.range J,
      ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
          (((qsMu e : ℂ) * twist F c e * twist F c a₂) * (twistInv F d e * twistInv F d a₂) *
            ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
              ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
                    rhoT S R a₂ k a₁ *
                      (F.character c).idealValue a₁ * (F.character d).idealValue a₁ *
                        phiT K W M n Λ (qsN e) (qsN a₂) k (2 ^ j₁ * 2 ^ j₂) (qsN a₁)
                          (qsN (e₁ * e₂)) (qsN (c * d))) else 0‖ ≤ U := by
    intro e he a₂ ha₂ k hk j₁ _ j₂ _
    have he0 : e ≠ ⊥ := by
      intro h0; rw [h0] at he
      exact h𝔮0 (le_bot_iff.mp (Ideal.le_of_dvd ((mem_qsDivisors h𝔮0).mp he)))
    have hk' : (2 : ℝ) ^ k ≤ κ := two_pow_le_of_lt_log hκ (Finset.mem_range.mp hk)
    have hR0 : R ≠ ⊥ := badIdeal_ne_bot hqS
    have ha₂0 : a₂ ≠ ⊥ := by
      intro h0; rw [h0] at ha₂
      exact hR0 (le_bot_iff.mp (Ideal.le_of_dvd ((mem_qsDivisors hR0).mp ha₂)))
    refine (hblk M n κ Λ 𝔮 cols z S R e a₂ k j₁ j₂ hM hn hΛ hblock he0 hk'
      (one_le_qsN ha₂0)).trans ?_
    rw [hUdef]
    have h1 : (n * 2 ^ k) ^ (δ / 8) ≤ (n * κ) ^ (δ / 8) :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
    have h2 : (4 * n * 2 ^ k) ^ (δ / 8) ≤ (4 * n * κ) ^ (δ / 8) :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
    have hΛ32 : 0 ≤ Λ ^ (3/2 : ℝ) := by positivity
    gcongr
  refine (norm_sum5_le _ _ _ _ _ _ U hU).trans ?_
  -- the counts
  have hM1 : 1 ≤ M := by linarith
  have hnPle : n ≤ P := by
    rw [hPdef]
    calc n = 1 * n := by ring
      _ ≤ M * n := mul_le_mul_of_nonneg_right hM1 hn0.le
  have hκPle : κ ≤ P := by
    rw [hPdef]
    calc κ ≤ M := hκM
      _ = M * 1 := by ring
      _ ≤ M * n := mul_le_mul_of_nonneg_left hn hM.le
  have hnκP : n * κ ≤ P := by
    rw [hPdef, mul_comm M n]
    exact mul_le_mul_of_nonneg_left hκM hn0.le
  have hN𝔮 : 1 ≤ qsN 𝔮 := one_le_qsN h𝔮0
  have hc1 : ((qsDivisors 𝔮).card : ℝ) ≤ Cd * qsN 𝔮 ^ 8 := by
    refine (hdiv 𝔮 h𝔮0).trans (mul_le_mul_of_nonneg_left ?_ hCd.le)
    rw [Real.rpow_one]
    calc (Ideal.absNorm 𝔮 : ℝ) = qsN 𝔮 ^ 1 := by rw [pow_one]
      _ ≤ qsN 𝔮 ^ 8 := pow_le_pow_right₀ hN𝔮 (by norm_num)
  have hc2 : TR ≤ TR + 1 := by linarith
  have hlogc : (1 / (γ * Real.log 2) + 1) ≤ CL := by
    rw [hCL]
    have : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ0.le
    have h0 : 0 ≤ 1 / (γ * Real.log 2) + 1 := by positivity
    nlinarith
  have hc3 : ((Finset.range KB).card : ℝ) ≤ CL * P ^ γ := by
    rw [Finset.card_range, hKBdef]
    refine (log_count_le hκ hγ0).trans ?_
    have hκP : κ ^ γ ≤ P ^ γ := Real.rpow_le_rpow hκ0.le hκPle hγ0.le
    exact mul_le_mul hlogc hκP (by positivity) hCL0.le
  have hc4 : ((Finset.range J).card : ℝ) ≤ CL * P ^ γ := by
    rw [Finset.card_range, hJdef]
    refine (log_count_le (by linarith : (1:ℝ) ≤ 2 * n) hγ0).trans ?_
    rw [Real.mul_rpow (by norm_num) hn0.le]
    have hnP : n ^ γ ≤ P ^ γ := Real.rpow_le_rpow hn0.le hnPle hγ0.le
    rw [hCL]
    have h0 : 0 ≤ 1 / (γ * Real.log 2) + 1 := by positivity
    have h2γ : 0 ≤ (2 : ℝ) ^ γ := by positivity
    calc (1 / (γ * Real.log 2) + 1) * (2 ^ γ * n ^ γ)
        = (1 / (γ * Real.log 2) + 1) * 2 ^ γ * n ^ γ := by ring
      _ ≤ (1 / (γ * Real.log 2) + 1) * 2 ^ γ * P ^ γ := by gcongr
  -- the powers of P
  have hp1 : (n * κ) ^ (δ / 8) ≤ P ^ (δ / 8) :=
    Real.rpow_le_rpow (by positivity) hnκP (by positivity)
  have hp2 : (4 * n * κ) ^ (δ / 8) ≤ 4 ^ (δ / 8) * P ^ (δ / 8) := by
    rw [show 4 * n * κ = 4 * (n * κ) by ring, Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
  have hp3 : Λ ^ (3/2 : ℝ) ≤ P ^ (3 * δ / 16) := by
    rw [hΛdef, ← Real.rpow_mul hP0.le]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hYshape : Y ≤ qsBlockShape M n κ α := by
    unfold qsBlockShape
    have : 0 ≤ n * Real.sqrt (M / κ) := by positivity
    rw [hY]; linarith
  have hexpo : P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3 =
      P ^ (5 * δ / 8) := by
    rw [← Real.rpow_natCast (P ^ γ) 3, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0,
      ← Real.rpow_add hP0, ← Real.rpow_add hP0]
    congr 1
    rw [hγ]; push_cast; ring
  have hPδ : P ^ (δ / 8) * P ^ (δ / 8) * P ^ (3 * δ / 16) * (P ^ γ) ^ 3 ≤ P ^ δ := by
    rw [hexpo]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hTR0 : 0 ≤ TR := by positivity
  have hU' : U ≤ Cb * P ^ (δ / 8) * (4 ^ (δ / 8) * P ^ (δ / 8)) * P ^ (3 * δ / 16) * Y * Sz := by
    rw [hUdef]
    have : 0 ≤ Λ ^ (3/2 : ℝ) := by positivity
    gcongr
  have hU0 : 0 ≤ U := by rw [hUdef]; positivity
  have hc2' : ((qsDivisors R).card : ℝ) ≤ TR + 1 := by
    have : ((qsDivisors R).card : ℝ) = TR := rfl
    linarith
  have hN80 : 0 ≤ qsN 𝔮 ^ 8 := by positivity
  have h40 : (0 : ℝ) ≤ 4 ^ (δ / 8) := by positivity
  exact final_arith (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hU0 hCd.le hTR0 hCL0.le hCb.le hN80 hP0 h40 hY0 hSz0
    hc1 hc2' hc3 hc4 hc4 hU' hPδ hYshape

end ArtinPrimitiveRoots.A2.QSC3
