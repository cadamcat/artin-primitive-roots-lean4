import ArtinPrimitiveRoots.Proofs.qs_c_p.C3DualResExpand
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Main

/-! The dual zero-residue remainder at the C3b scale. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

set_option maxHeartbeats 1000000 in
/-- The full dual zero-residue component has the target C3b bound. -/
theorem dual_residue_C3b_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (α : ℝ) (hα : 1 < α) (hα₂ : α ≤ 2) (hexp : QSHasExponent F α)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
        (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS q n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n q)‖ ≤
          C * qsN q ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεpow : 2 * ε = δ / 4 := by dsimp [ε]; ring
  obtain ⟨Cshell, hCshell, hShell⟩ := dual_residue_shell_bound F hrf α ε hε hα hα₂ hexp
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := qs_divisor_bound_M1 (K := K) 1 (by norm_num)
  obtain ⟨Ccount, hCcount, hCount⟩ := qs_c3_shell_count_cube (δ / 2) (by positivity)
  let R₀ : ℂ := qsResidueZero K (QSC3.F0 K W)
  let TR : ℝ := (qsDivisors (QSC3.badIdeal m qS)).card
  let C₀ : ℝ := ‖R₀‖ * Cdiv * TR * Ccount * Cshell * (4 : ℝ) ^ ε
  have hTR : 0 ≤ TR := by dsimp [TR]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨δ / 6, by positivity, ?_⟩
  intro η hη hη₀
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro M n κ q cols z hn hκ hκM hblock
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  have hblock : QSBlockCols m qS q n cols := ⟨hq, hbad, hcol, hclass⟩
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hqN : 1 ≤ qsN q := QSC3.one_le_qsN hq0
  have hRbad0 : QSC3.badIdeal m qS ≠ ⊥ := QSC3.badIdeal_ne_bot hqS
  have hM : 0 < M := by linarith
  have hκM' : κ ≤ M := by linarith
  let X : ℝ := M * n
  have hX2 : 2 ≤ X := by dsimp [X]; nlinarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  let Λ : ℝ := X ^ η
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hX1 hη.le
  have hΛ0 : 0 < Λ := by linarith
  let Energy : ℝ := ∑ c ∈ cols, ‖z c‖ ^ 2
  have hEnergy : 0 ≤ Energy := by dsimp [Energy]; positivity
  let SH : ℝ := M + Real.sqrt M * κ ^ (α - 1 / 2)
  have hSH : 0 ≤ SH := by dsimp [SH]; positivity
  let U : ℝ := Cshell * (4 : ℝ) ^ ε * X ^ (δ / 4) * Λ ^ (3/2 : ℝ) * SH * Energy
  have hU : 0 ≤ U := by dsimp [U]; positivity
  let S₀ := qsDivisors q
  let SR := qsDivisors (QSC3.badIdeal m qS)
  let S₁ := Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)
  let S₂ := Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)
  have hterm : ∀ e ∈ S₀, ∀ a₂ ∈ SR, ∀ k ∈ S₁, ∀ l ∈ S₂, ∀ r ∈ S₂,
      ‖(qsMu e : ℂ) * qsPairSum cols z
        (dualResidueShellKernel F e a₂ κ n Λ M k l r)‖ ≤ U := by
    intro e he a₂ ha₂ k hk l hl r hr
    let B : ℝ := 2 ^ k
    let D₁ : ℝ := 2 ^ l
    let D₂ : ℝ := 2 ^ r
    let E : ℝ := qsN e
    let A : ℝ := qsN a₂
    let rows := (qsUpTo m qS κ).filter (fun a =>
      (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1))
    let p₁ : Ideal (𝓞 K) → Prop := fun e =>
      (2 ^ l : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (l + 1)
    let p₂ : Ideal (𝓞 K) → Prop := fun e =>
      (2 ^ r : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (r + 1)
    let ρ : Ideal (𝓞 K) → ℂ := dualRowWeight m qS κ a₂
    let z₁ : Ideal (𝓞 K) → ℂ := fun c =>
      (z c * QSC3.twist F c e * QSC3.twist F c a₂) / (Real.sqrt (qsN c) : ℂ)
    let z₂ : Ideal (𝓞 K) → ℂ := fun c =>
      (conj (z c) * QSC3.twistInv F c e * QSC3.twistInv F c a₂) / (Real.sqrt (qsN c) : ℂ)
    have hB : 1 ≤ B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
    have hD₁ : 1 ≤ D₁ := by dsimp [D₁]; exact one_le_pow₀ (by norm_num)
    have hD₂ : 1 ≤ D₂ := by dsimp [D₂]; exact one_le_pow₀ (by norm_num)
    have hB0 : 0 < B := by linarith
    have hBκ : B ≤ κ := qs_c3_shell_scale_le κ hκ k hk
    have he0 : e ≠ ⊥ := by
      intro hz
      subst e
      exact hq0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hq0).mp he)))
    have ha₂0 : a₂ ≠ ⊥ := by
      intro hz
      subst a₂
      exact hRbad0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hRbad0).mp ha₂)))
    have hE : 1 ≤ E := QSC3.one_le_qsN he0
    have hA : 1 ≤ A := QSC3.one_le_qsN ha₂0
    have hE0 : 0 < E := by linarith
    have hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁ := by
      intro e he
      refine ⟨he.1, ?_⟩
      calc
        qsN e ≤ (2 ^ (l + 1) : ℝ) := he.2.le
        _ = 2 * D₁ := by dsimp [D₁]; rw [pow_succ]; ring
    have hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂ := by
      intro e he
      refine ⟨he.1, ?_⟩
      calc
        qsN e ≤ (2 ^ (r + 1) : ℝ) := he.2.le
        _ = 2 * D₂ := by dsimp [D₂]; rw [pow_succ]; ring
    have hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n :=
      fun c hc => ⟨(hcol c hc).1, (hcol c hc).2.2.2⟩
    have hrows : ∀ a ∈ rows, QSAdm m qS a ∧ B ≤ qsN a ∧ qsN a ≤ 2 * B := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      refine ⟨(QSC2.mem_qsUpTo.mp ha'.1).1, ha'.2.1, ?_⟩
      calc
        qsN a ≤ (2 ^ (k + 1) : ℝ) := ha'.2.2.le
        _ = 2 * B := by dsimp [B]; rw [pow_succ]; ring
    have hρ : ∀ a, ‖ρ a‖ ≤ 1 := by
      intro a
      dsimp [ρ, dualRowWeight]
      split_ifs <;> simp
    have hn0 : 0 < n := by linarith
    have hz₁ : ∀ c ∈ cols, ‖z₁ c‖ ≤ ‖z c‖ / Real.sqrt n := by
      intro c hc
      have htw : ‖z c * QSC3.twist F c e * QSC3.twist F c a₂‖ ≤ ‖z c‖ := by
        rw [norm_mul, norm_mul]
        calc
          _ ≤ ‖z c‖ * 1 * 1 := by
            gcongr
            · exact QSC3.norm_twist_le F (hcol c hc).1 e
            · exact QSC3.norm_twist_le F (hcol c hc).1 a₂
          _ = _ := by ring
      dsimp only [z₁]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ ‖z c‖ / Real.sqrt (qsN c) :=
          div_le_div_of_nonneg_right htw (Real.sqrt_nonneg _)
        _ ≤ ‖z c‖ / Real.sqrt n :=
          div_le_div_of_nonneg_left (norm_nonneg _) (Real.sqrt_pos.mpr hn0)
            (Real.sqrt_le_sqrt (hcol c hc).2.2.1.le)
    have hz₂ : ∀ c ∈ cols, ‖z₂ c‖ ≤ ‖z c‖ / Real.sqrt n := by
      intro c hc
      have htw : ‖conj (z c) * QSC3.twistInv F c e * QSC3.twistInv F c a₂‖ ≤ ‖z c‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj]
        calc
          _ ≤ ‖z c‖ * 1 * 1 := by
            gcongr
            · exact QSC3.norm_twistInv_le F (hcol c hc).1 e
            · exact QSC3.norm_twistInv_le F (hcol c hc).1 a₂
          _ = _ := by ring
      dsimp only [z₂]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ ‖z c‖ / Real.sqrt (qsN c) :=
          div_le_div_of_nonneg_right htw (Real.sqrt_nonneg _)
        _ ≤ ‖z c‖ / Real.sqrt n :=
          div_le_div_of_nonneg_left (norm_nonneg _) (Real.sqrt_pos.mpr hn0)
            (Real.sqrt_le_sqrt (hcol c hc).2.2.1.le)
    have hPairEq : qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r) =
        ∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
          ∑ ec ∈ (qsDivisors c).filter p₁,
            ∑ ed ∈ (qsDivisors d).filter p₂,
              (qsMu (ec * ed) : ℂ) *
                ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                  (F.character d).idealValue a *
                    dualResidueWeight M n Λ E A (qsN a) (qsN (ec * ed)) else 0 := by
      unfold qsPairSum dualResidueShellKernel
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcd : IsCoprime c d
      · simp only [hcd, ite_true]
        dsimp only [z₁, z₂, ρ, E, A, rows, p₁, p₂]
        have hcN : 0 < qsN c := QSC2.qsN_pos (QSC2.ne_bot_of_QSAdm (hcol c hc).1)
        have hroot : Real.sqrt (qsN (c * d)) = Real.sqrt (qsN c) * Real.sqrt (qsN d) := by
          rw [QSC2.qsN_mul, Real.sqrt_mul hcN.le]
        rw [hroot]
        push_cast
        rw [div_mul_eq_div_div]
        ring
      · simp only [hcd, ite_false]
    have hShellBnd : ‖qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r)‖ ≤
        Cshell * (n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) * SH * Energy := by
      by_cases hcut : D₁ * D₂ ≤ 2 * Λ * (n * Real.sqrt (E / (M * B)))
      · have hrows' : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B :=
          fun a ha => ⟨(hrows a ha).1, (hrows a ha).2.2⟩
        have hb := hShell M n κ B D₁ D₂ Λ E A p₁ p₂ cols rows z₁ z₂ ρ (fun c => ‖z c‖)
          hM hn hB hBκ hD₁ hD₂ hΛ hE hp₁ hp₂ hcols hrows' hρ hz₁ hz₂ hcut
        rw [hPairEq]
        simpa only [Energy, SH] using hb
      · have hzero : ∀ c d, dualResidueShellKernel F e a₂ κ n Λ M k l r c d = 0 := by
          intro c d
          unfold dualResidueShellKernel
          simp only [Finset.mul_sum]
          apply Finset.sum_eq_zero
          intro ec hec
          apply Finset.sum_eq_zero
          intro ed hed
          apply Finset.sum_eq_zero
          intro a ha
          have hNa := hrows a ha
          have hNa0 : 0 < qsN a := hB0.trans_le hNa.2.1
          have hec' := hp₁ ec (Finset.mem_filter.mp hec).2
          have hed' := hp₂ ed (Finset.mem_filter.mp hed).2
          have hprod : D₁ * D₂ ≤ qsN (ec * ed) := by
            rw [QSC2.qsN_mul]
            exact mul_le_mul hec'.1 hed'.1 (by positivity) (by positivity)
          have hArow : B ≤ A * qsN a := by
            calc
              B ≤ qsN a := hNa.2.1
              _ ≤ A * qsN a := le_mul_of_one_le_left hNa0.le hA
          have hupper : 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A * qsN a)) ≤
              2 * Λ * (n * Real.sqrt (E / (M * B))) := by
            calc
              _ = QSC3.zhi M n Λ E (A * qsN a) := by simp only [QSC3.zhi, mul_assoc]
              _ ≤ QSC3.zhi M n Λ E B :=
                QSC3.zhi_anti hM hE0.le hΛ0.le hn0.le hB0 hArow
              _ = _ := QSC3.zhi_eq hn0.le
          have hfalse : ¬ qsN (ec * ed) ≤ 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A * qsN a)) := by
            intro h
            exact hcut (hprod.trans (h.trans hupper))
          dsimp only [E, A] at hfalse
          simp only [dualResidueWeight, hfalse, ite_false, mul_zero]
        have hpairzero : qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r) = 0 := by
          simp only [qsPairSum, hzero, mul_zero, ite_self, Finset.sum_const_zero]
        rw [hpairzero, norm_zero]
        positivity
    have hBn : n * B ≤ X := by
      calc
        n * B ≤ n * M := mul_le_mul_of_nonneg_left (hBκ.trans hκM') (by linarith)
        _ = X := by dsimp [X]; ring
    have hpow : (n * B) ^ (2 * ε) ≤ X ^ (δ / 4) := by
      rw [hεpow]
      exact Real.rpow_le_rpow (by positivity) hBn (by positivity)
    have hnormloss : (n * B) ^ ε * (4 * n * B) ^ ε ≤ (4 : ℝ) ^ ε * X ^ (δ / 4) := by
      calc
        _ = (4 : ℝ) ^ ε * (n * B) ^ (2 * ε) := by
          rw [show 4 * n * B = 4 * (n * B) by ring,
            Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ n * B),
            show 2 * ε = ε + ε by ring, Real.rpow_add (by positivity : 0 < n * B)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
    have hprod : (n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) * SH ≤
        (4 : ℝ) ^ ε * X ^ (δ / 4) * Λ ^ (3/2 : ℝ) * SH :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnormloss (by positivity)) hSH
    calc
      _ = ‖(qsMu e : ℂ)‖ *
          ‖qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r)‖ := norm_mul _ _
      _ ≤ 1 * (Cshell * (n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) * SH * Energy) :=
        mul_le_mul (QSC2.norm_qsMu_le e) hShellBnd (norm_nonneg _) (by norm_num)
      _ = Cshell * ((n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) * SH) * Energy := by ring
      _ ≤ Cshell * ((4 : ℝ) ^ ε * X ^ (δ / 4) * Λ ^ (3/2 : ℝ) * SH) * Energy :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCshell.le) hEnergy
      _ = U := by dsimp [U]; ring
  have hsum := QSC3.norm_sum5_le S₀ SR S₁ S₂ S₂
    (fun e a₂ k l r => (qsMu e : ℂ) *
      qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r)) U hterm
  have hκX : κ ≤ X := by dsimp [X]; nlinarith
  have h2nX : 2 * n ≤ X := by dsimp [X]; nlinarith
  let L : ℝ := ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ)
  have hcardbound (Y : ℝ) (hYX : Y ≤ X) :
      ((Finset.range (Nat.log 2 ⌊Y⌋₊ + 1)).card : ℝ) ≤ L := by
    simp only [Finset.card_range]
    have hnat : Nat.log 2 ⌊Y⌋₊ + 1 ≤ Nat.log 2 ⌊X⌋₊ + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono hYX)) 1
    dsimp only [L]
    exact_mod_cast hnat
  have hcardκ : (S₁.card : ℝ) ≤ L := hcardbound κ hκX
  have hcardn : (S₂.card : ℝ) ≤ L := hcardbound (2 * n) h2nX
  have hcardShells : (S₁.card : ℝ) * (S₂.card : ℝ) ^ 2 ≤ Ccount * X ^ (δ / 2) := by
    calc
      _ ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
      _ ≤ Ccount * X ^ (δ / 2) := hCount X hX2
  have hqpow : qsN q ≤ qsN q ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hqN (show (1 : ℕ) ≤ 8 by norm_num)
  have hqcard : (S₀.card : ℝ) ≤ Cdiv * qsN q ^ 8 := by
    have hd : (S₀.card : ℝ) ≤ Cdiv * qsN q := by
      simpa only [S₀, qsN, Real.rpow_one] using hDiv q hq0
    exact hd.trans (mul_le_mul_of_nonneg_left hqpow hCdiv.le)
  have hcards : (S₀.card : ℝ) * (SR.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₂.card : ℝ) ≤
      (Cdiv * qsN q ^ 8) * TR * (Ccount * X ^ (δ / 2)) := by
    calc
      _ = (S₀.card : ℝ) * TR * ((S₁.card : ℝ) * (S₂.card : ℝ) ^ 2) := by
        dsimp [SR, TR]
        ring
      _ ≤ _ := by gcongr
  have hpower : X ^ (δ / 4) * X ^ (δ / 2) * Λ ^ (3/2 : ℝ) ≤ X ^ δ := by
    dsimp [Λ]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hshape : SH ≤ qsBlockShape M n κ α := by
    dsimp [SH, qsBlockShape]
    have htail : 0 ≤ n * Real.sqrt (M / κ) := by positivity
    linarith
  have hCmain : C₀ ≤ 1 + C₀ := by linarith
  have hExpand := dual_residue_pair_shell_expand F W hrf hqS M κ Λ n q cols z hblock
  rw [hExpand, norm_mul]
  change ‖R₀‖ * _ ≤ _
  calc
    _ = ‖R₀‖ * ‖∑ e ∈ S₀, ∑ a₂ ∈ SR, ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₂,
          (qsMu e : ℂ) * qsPairSum cols z (dualResidueShellKernel F e a₂ κ n Λ M k l r)‖ := by
      simp_rw [Finset.mul_sum]
      rfl
    _ ≤ ‖R₀‖ * ((S₀.card : ℝ) * (SR.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₂.card : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ ‖R₀‖ * ((Cdiv * qsN q ^ 8) * TR * (Ccount * X ^ (δ / 2)) * U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcards hU) (norm_nonneg _)
    _ = C₀ * qsN q ^ 8 * (X ^ (δ / 4) * X ^ (δ / 2) * Λ ^ (3/2 : ℝ)) * SH * Energy := by
      dsimp [C₀, U]
      ring
    _ ≤ (1 + C₀) * qsN q ^ 8 * X ^ δ * qsBlockShape M n κ α * Energy := by gcongr

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
