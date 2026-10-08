import ArtinPrimitiveRoots.Proofs.qs_c_p.C3Helpers

/-! The high-divisor C3a estimate on one row/divisor shell. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

/-- The original high-divisor weight pays for one C2u shell uniformly in the
row scale, the divisor scales and the fixed q-divisor norm. -/
theorem orig_highdiv_shell_bound {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n B D₁ D₂ Λ Q : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
        [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ),
        0 < M → 1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ → 1 ≤ Λ → 1 ≤ Q →
        2 * B ≤ M → D₁ ≤ 2 * n → D₂ ≤ 2 * n →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ B ≤ qsN a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) →
        Λ * Real.sqrt (M / (2 * B)) < 4 * Q * D₁ * D₂ →
        ‖qsPairSum cols z (fun c d =>
          ∑ ec ∈ (qsDivisors c).filter p₁,
            ∑ ed ∈ (qsDivisors d).filter p₂,
              (qsMu (ec * ed) : ℂ) *
                ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                  (F.character d).idealValue a *
                    (if Λ * Real.sqrt (M / qsN a) < Q * qsN (ec * ed) then
                      ((Real.sqrt (M / qsN a) / (Q * qsN (ec * ed)) : ℝ) : ℂ)
                    else 0))‖ ≤
          C * (n * B) ^ (2 * ε) * (n + B ^ α * Real.sqrt (M / B)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hpair⟩ :=
    qs_c3_shell_pair_bound_uniform F hrf α ε hε hα hexp
  refine ⟨16 * C₂, by positivity, ?_⟩
  intro M n B D₁ D₂ Λ Q p₁ p₂ _ _ cols rows z ρ hM hn hB hD₁ hD₂ hΛ hQ
    h2B hD₁n hD₂n hp₁ hp₂ hcols hrows hρ hcut
  have hB0 : 0 < B := by linarith
  have hQ0 : 0 < Q := by linarith
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD0 : 0 < D₁ * D₂ := mul_pos hD₁0 hD₂0
  let R : ℝ := Real.sqrt (M / B) / (Q * (D₁ * D₂))
  let w : ℝ → ℝ → ℂ := fun y u =>
    if B ≤ y ∧ D₁ * D₂ ≤ u then
      (if Λ * Real.sqrt (M / y) < Q * u then
        ((Real.sqrt (M / y) / (Q * u) : ℝ) : ℂ) else 0)
    else 0
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hw : ∀ y u, ‖w y u‖ ≤ R := by
    intro y u
    dsimp [w]
    split_ifs with hguard hsupport
    · have hy0 : 0 < y := hB0.trans_le hguard.1
      have hu0 : 0 < u := hD0.trans_le hguard.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hroot : Real.sqrt (M / y) ≤ Real.sqrt (M / B) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_div_iff₀ hy0 hB0]
        exact mul_le_mul_of_nonneg_left hguard.1 hM.le
      dsimp [R]
      calc
        Real.sqrt (M / y) / (Q * u) ≤ Real.sqrt (M / B) / (Q * u) := by
          gcongr
        _ ≤ Real.sqrt (M / B) / (Q * (D₁ * D₂)) := by
          gcongr
          exact hguard.2
    · simpa using hR
    · simpa using hR
  have hrows' : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B := by
    intro a ha
    exact ⟨(hrows a ha).1, (hrows a ha).2.2⟩
  have hbase := hpair n B D₁ D₂ p₁ p₂ cols rows z ρ w R
    hn hB hD₁ hD₂ hD₁n hD₂n hp₁ hp₂ hcols hrows' hρ hR hw
  have hkernel : (fun c d =>
      ∑ ec ∈ (qsDivisors c).filter p₁,
        ∑ ed ∈ (qsDivisors d).filter p₂,
          (qsMu (ec * ed) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
              (F.character d).idealValue a * w (qsN a) (qsN (ec * ed))) =
      (fun c d =>
        ∑ ec ∈ (qsDivisors c).filter p₁,
          ∑ ed ∈ (qsDivisors d).filter p₂,
            (qsMu (ec * ed) : ℂ) *
              ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                (F.character d).idealValue a *
                  (if Λ * Real.sqrt (M / qsN a) < Q * qsN (ec * ed) then
                    ((Real.sqrt (M / qsN a) / (Q * qsN (ec * ed)) : ℝ) : ℂ)
                  else 0)) := by
    funext c d
    apply Finset.sum_congr rfl
    intro ec hec
    apply Finset.sum_congr rfl
    intro ed hed
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have hec' := hp₁ ec (Finset.mem_filter.mp hec).2
    have hed' := hp₂ ed (Finset.mem_filter.mp hed).2
    have hprod : D₁ * D₂ ≤ qsN (ec * ed) := by
      rw [QSC2.qsN_mul]
      exact mul_le_mul hec'.1 hed'.1 hD₂0.le (hD₁0.le.trans hec'.1)
    have hguard : B ≤ qsN a ∧ D₁ * D₂ ≤ qsN (ec * ed) :=
      ⟨(hrows a ha).2.1, hprod⟩
    simp only [w, hguard, and_self, ite_true]
  rw [hkernel] at hbase
  have h4Q : 1 ≤ 4 * Q := by linarith
  have harith := qs_c3_highdiv_shell_arith M n B D₁ D₂ Λ (4 * Q) α
    hM hn hB hΛ h4Q hD₁ hD₂ h2B hcut
  have hR4 : R = 4 * (Real.sqrt (M / B) / ((4 * Q) * (D₁ * D₂))) := by
    dsimp [R]
    field_simp
  have harith' : R * Real.sqrt (D₁ * D₂) *
      (n / Real.sqrt (D₁ * D₂) +
        Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) ≤
        16 * (n + B ^ α * Real.sqrt (M / B)) := by
    rw [hR4]
    calc
      _ = 4 * (Real.sqrt (M / B) / ((4 * Q) * (D₁ * D₂)) *
          Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) := by ring
      _ ≤ 4 * (4 * (n + B ^ α * Real.sqrt (M / B))) :=
        mul_le_mul_of_nonneg_left harith (by norm_num)
      _ = _ := by ring
  have hcoef : 0 ≤ C₂ * (n * B) ^ (2 * ε) := by positivity
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
  calc
    _ ≤ C₂ * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := hbase
    _ = (C₂ * (n * B) ^ (2 * ε)) *
          (R * Real.sqrt (D₁ * D₂) *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
    _ ≤ (C₂ * (n * B) ^ (2 * ε)) *
          (16 * (n + B ^ α * Real.sqrt (M / B))) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left harith' hcoef) henergy
    _ = (16 * C₂) * (n * B) ^ (2 * ε) *
          (n + B ^ α * Real.sqrt (M / B)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
