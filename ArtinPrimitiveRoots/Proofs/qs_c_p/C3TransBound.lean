import ArtinPrimitiveRoots.Proofs.qs_c_p.C3TransExpand

/-! The original transition remainder at the C3a scale. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

set_option maxHeartbeats 1000000 in
/-- The whole original transition term has the C3a bound when the cutoff
exponent is at most delta/20. -/
theorem orig_transition_C3a_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (α : ℝ) (hα : 1 < α)
    (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
        (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS q n cols →
        ‖qsPairSum cols z (qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) q)‖ ≤
          C * qsN q ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεpow : 2 * ε = δ / 4 := by dsimp [ε]; ring
  obtain ⟨Cshell, hCshell, hShell⟩ := orig_transition_shell_bound F hrf W hW α ε hε hα hexp
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := qs_divisor_bound_M1 (K := K) 1 (by norm_num)
  obtain ⟨Ccount, hCcount, hCount⟩ := qs_c3_shell_count_cube (δ / 2) (by positivity)
  let C₀ : ℝ := Cdiv * Ccount * Cshell
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨δ / 20, by positivity, ?_⟩
  intro η hη hηδ
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro M n κ q cols z hn hκ hκM hblock
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  have hblock : QSBlockCols m qS q n cols := ⟨hq, hbad, hcol, hclass⟩
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hqN : 1 ≤ qsN q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hM : 0 < M := by linarith
  have hκM' : κ ≤ M := by linarith
  let X : ℝ := M * n
  have hX2 : 2 ≤ X := by dsimp [X]; nlinarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  let Λ : ℝ := X ^ η
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hX1 hη.le
  have hΛ0 : 0 < Λ := by linarith
  let E : ℝ := ∑ c ∈ cols, ‖z c‖ ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let SH : ℝ := n + Real.sqrt M * κ ^ (α - 1 / 2)
  have hSH : 0 ≤ SH := by dsimp [SH]; positivity
  let A : ℝ := Cshell * X ^ (δ / 4) * Λ ^ 5 * SH * E
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let S₀ := qsDivisors q
  let S₁ := Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)
  let S₂ := Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)
  have hterm : ∀ eq ∈ S₀, ∀ k ∈ S₁, ∀ l ∈ S₂, ∀ r ∈ S₂,
      ‖(qsMu eq : ℂ) * qsPairSum cols z
        (origTransitionShellKernel F W q eq κ Λ M k l r)‖ ≤ A := by
    intro eq heq k hk l hl r hr
    let B : ℝ := 2 ^ k
    let D₁ : ℝ := 2 ^ l
    let D₂ : ℝ := 2 ^ r
    let Q : ℝ := qsN eq
    let rows := (qsSqfUpTo κ q).filter (fun a =>
      (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1))
    let p₁ : Ideal (𝓞 K) → Prop := fun e =>
      (2 ^ l : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (l + 1)
    let p₂ : Ideal (𝓞 K) → Prop := fun e =>
      (2 ^ r : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (r + 1)
    have hB : 1 ≤ B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
    have hD₁ : 1 ≤ D₁ := by dsimp [D₁]; exact one_le_pow₀ (by norm_num)
    have hD₂ : 1 ≤ D₂ := by dsimp [D₂]; exact one_le_pow₀ (by norm_num)
    have hB0 : 0 < B := by linarith
    have hBκ : B ≤ κ := qs_c3_shell_scale_le κ hκ k hk
    have h2B : 2 * B ≤ M :=
      (mul_le_mul_of_nonneg_left hBκ (by norm_num)).trans hκM
    have hD₁n : D₁ ≤ 2 * n := qs_c3_shell_scale_le (2 * n) (by linarith) l hl
    have hD₂n : D₂ ≤ 2 * n := qs_c3_shell_scale_le (2 * n) (by linarith) r hr
    have heq0 : eq ≠ ⊥ := by
      intro hz
      subst eq
      exact hq0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hq0).mp heq)))
    have hQ : 1 ≤ Q := by
      dsimp only [Q, qsN]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => heq0 (Ideal.absNorm_eq_zero_iff.mp hz))
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
      refine ⟨(qs_c3_orig_row_admissible hqS hbad κ ha'.1).1, ha'.2.1, ?_⟩
      calc
        qsN a ≤ (2 ^ (k + 1) : ℝ) := ha'.2.2.le
        _ = 2 * B := by dsimp [B]; rw [pow_succ]; ring
    have hρ : ∀ a, ‖qsC3RowTwist F a‖ ≤ 1 := qs_c3_rowTwist_norm_le F
    have hShellBnd : ‖qsPairSum cols z (origTransitionShellKernel F W q eq κ Λ M k l r)‖ ≤
        Cshell * (n * B) ^ (2 * ε) * Λ ^ 5 * (n + B ^ α * Real.sqrt (M / B)) * E := by
      by_cases hcut : Real.sqrt (M / (2 * B)) < 4 * Λ * Q * D₁ * D₂
      · have hb := hShell M n B D₁ D₂ Λ Q p₁ p₂ cols rows z (qsC3RowTwist F)
          hM hn hB hD₁ hD₂ hΛ hQ h2B hD₁n hD₂n hp₁ hp₂ hcols hrows hρ hcut
        unfold origTransitionShellKernel
        simpa only [rows, p₁, p₂, Q, E] using hb
      · have hcut' : 4 * Λ * Q * D₁ * D₂ ≤ Real.sqrt (M / (2 * B)) := le_of_not_gt hcut
        have hzero : ∀ c d, origTransitionShellKernel F W q eq κ Λ M k l r c d = 0 := by
          intro c d
          unfold origTransitionShellKernel
          apply Finset.sum_eq_zero
          intro ec hec
          apply Finset.sum_eq_zero
          intro ed hed
          rw [Finset.mul_sum]
          apply Finset.sum_eq_zero
          intro a ha
          have hNa := hrows a ha
          have hNa0 : 0 < qsN a := hB0.trans_le hNa.2.1
          have hec' := hp₁ ec (Finset.mem_filter.mp hec).2
          have hed' := hp₂ ed (Finset.mem_filter.mp hed).2
          have hprod : qsN (ec * ed) ≤ (2 * D₁) * (2 * D₂) := by
            rw [QSC2.qsN_mul]
            exact mul_le_mul hec'.2 hed'.2 (by positivity) (by positivity)
          have hupper : Λ * Q * qsN (ec * ed) ≤ 4 * Λ * Q * D₁ * D₂ := by
            calc
              _ ≤ Λ * Q * ((2 * D₁) * (2 * D₂)) :=
                mul_le_mul_of_nonneg_left hprod (by positivity)
              _ = _ := by ring
          have hdiv : M / (2 * B) ≤ M / qsN a := by
            rw [div_le_div_iff₀ (by positivity : 0 < 2 * B) hNa0]
            exact mul_le_mul_of_nonneg_left hNa.2.2 hM.le
          have hbound : (Q * qsN (ec * ed)) * Λ ≤ Real.sqrt (M / qsN a) := by
            calc
              _ = Λ * Q * qsN (ec * ed) := by ring
              _ ≤ 4 * Λ * Q * D₁ * D₂ := hupper
              _ ≤ Real.sqrt (M / (2 * B)) := hcut'
              _ ≤ Real.sqrt (M / qsN a) := Real.sqrt_le_sqrt hdiv
          have hlow : qsN eq * qsN (ec * ed) ≤ Real.sqrt (M / qsN a) / Λ :=
            (le_div_iff₀ hΛ0).2 hbound
          have hfalse : ¬ Real.sqrt (M / qsN a) / Λ < qsN eq * qsN (ec * ed) :=
            not_lt_of_ge hlow
          simp only [origTransitionWeight, hfalse, false_and, ite_false, mul_zero]
        have hpairzero : qsPairSum cols z (origTransitionShellKernel F W q eq κ Λ M k l r) = 0 := by
          simp only [qsPairSum, hzero, mul_zero, ite_self, Finset.sum_const_zero]
        rw [hpairzero, norm_zero]
        positivity
    have hBn : n * B ≤ X := by
      calc
        n * B ≤ n * M :=
          mul_le_mul_of_nonneg_left (hBκ.trans hκM') (by linarith)
        _ = X := by dsimp [X]; ring
    have hpow : (n * B) ^ (2 * ε) ≤ X ^ (δ / 4) := by
      rw [hεpow]
      exact Real.rpow_le_rpow (by positivity) hBn (by positivity)
    have hscale : n + B ^ α * Real.sqrt (M / B) ≤ SH := by
      simpa only [SH, add_comm] using
        add_le_add_left (qs_c3_residue_scale_mono M B κ α hM hB0 hBκ hα) n
    have hprod : (n * B) ^ (2 * ε) * (n + B ^ α * Real.sqrt (M / B)) ≤
        X ^ (δ / 4) * SH :=
      mul_le_mul hpow hscale (by positivity) (by positivity)
    calc
      _ = ‖(qsMu eq : ℂ)‖ *
          ‖qsPairSum cols z (origTransitionShellKernel F W q eq κ Λ M k l r)‖ := norm_mul _ _
      _ ≤ 1 * (Cshell * (n * B) ^ (2 * ε) * Λ ^ 5 * (n + B ^ α * Real.sqrt (M / B)) * E) :=
        mul_le_mul (QSC2.norm_qsMu_le eq) hShellBnd (norm_nonneg _) (by norm_num)
      _ = (Cshell * Λ ^ 5) *
          ((n * B) ^ (2 * ε) * (n + B ^ α * Real.sqrt (M / B))) * E := by ring
      _ ≤ (Cshell * Λ ^ 5) * (X ^ (δ / 4) * SH) * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by positivity)) hE
      _ = A := by dsimp [A]; ring
  have hsum := qs_c3_norm_sum4_bound S₀ S₁ S₂ S₂
    (fun eq k l r => (qsMu eq : ℂ) *
      qsPairSum cols z (origTransitionShellKernel F W q eq κ Λ M k l r)) A hterm
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
  have hcards : (S₀.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₂.card : ℝ) ≤
      (Cdiv * qsN q ^ 8) * (Ccount * X ^ (δ / 2)) := by
    calc
      _ = (S₀.card : ℝ) * ((S₁.card : ℝ) * (S₂.card : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul hqcard hcardShells (by positivity) (by positivity)
  have hΛ5 : Λ ^ 5 = X ^ (η * 5) := by
    dsimp only [Λ]
    exact (Real.rpow_mul_natCast hX0.le η 5).symm
  have hpower : X ^ (δ / 4) * X ^ (δ / 2) * Λ ^ 5 ≤ X ^ δ := by
    rw [hΛ5, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hshape : SH ≤ qsBlockShape M n κ α := by
    dsimp [SH, qsBlockShape]
    have htail : 0 ≤ n * Real.sqrt (M / κ) := by positivity
    linarith
  have hCmain : C₀ ≤ 1 + C₀ := by linarith
  have hExpand := orig_transition_pair_shell_expand F W hrf hqS M κ Λ n q cols z hblock
  rw [hExpand]
  calc
    _ = ‖∑ eq ∈ S₀, ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₂,
          (qsMu eq : ℂ) * qsPairSum cols z
            (origTransitionShellKernel F W q eq κ Λ M k l r)‖ := by
      simp_rw [Finset.mul_sum]
      rfl
    _ ≤ (S₀.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₂.card : ℝ) * A := hsum
    _ ≤ (Cdiv * qsN q ^ 8) * (Ccount * X ^ (δ / 2)) * A :=
      mul_le_mul_of_nonneg_right hcards hA
    _ = C₀ * qsN q ^ 8 * (X ^ (δ / 4) * X ^ (δ / 2) * Λ ^ 5) * SH * E := by
      dsimp [C₀, A]
      ring
    _ ≤ (1 + C₀) * qsN q ^ 8 * X ^ δ * qsBlockShape M n κ α * E := by gcongr

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
