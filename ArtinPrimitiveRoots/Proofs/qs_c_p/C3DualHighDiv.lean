import ArtinPrimitiveRoots.Proofs.qs_c_p.C3DualPair
import ArtinPrimitiveRoots.Proofs.qs_c_p.C3DualArith

/-! The high-divisor C3b estimate on one row/divisor shell. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2

/-- The exact dual high-divisor weight after cancelling the column norm. -/
def dualHighDivWeight (M n Λ E A y u : ℝ) : ℂ :=
  if 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A * y)) < u then
    ((Real.sqrt (M / (E * A * y)) / u : ℝ) : ℂ)
  else 0

open Classical in
/-- The active-shell support pays for the high-divisor shell uniformly in the
fixed outer divisor and bad-row norms, with separate column coefficients. -/
theorem dual_highdiv_shell_bound {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n B D₁ D₂ Λ E A : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
        [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z₁ z₂ ρ : Ideal (𝓞 K) → ℂ)
        (Z : Ideal (𝓞 K) → ℝ),
        0 < M → 1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ →
        1 ≤ Λ → 1 ≤ E → 1 ≤ A → D₁ ≤ 2 * n → D₂ ≤ 2 * n →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ B ≤ qsN a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) →
        (∀ c ∈ cols, ‖z₁ c‖ ≤ Z c) → (∀ c ∈ cols, ‖z₂ c‖ ≤ Z c) →
        Real.sqrt (E * n ^ 2 / (M * A * (2 * B))) < 8 * Λ * (D₁ * D₂) →
        ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
            ∑ ec ∈ (qsDivisors c).filter p₁,
              ∑ ed ∈ (qsDivisors d).filter p₂,
                (qsMu (ec * ed) : ℂ) *
                  ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                    (F.character d).idealValue a *
                      dualHighDivWeight M n Λ E A (qsN a) (qsN (ec * ed))
            else 0‖ ≤
          C * (n * B) ^ (2 * ε) * Λ * (M + B ^ α * Real.sqrt (M / B)) *
            ∑ c ∈ cols, Z c ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hpair⟩ := dual_shell_pair_bound_uniform F hrf α ε hε hα hexp
  refine ⟨32 * C₂, by positivity, ?_⟩
  intro M n B D₁ D₂ Λ E A p₁ p₂ _ _ cols rows z₁ z₂ ρ Z
    hM hn hB hD₁ hD₂ hΛ hE hA hD₁n hD₂n hp₁ hp₂ hcols hrows hρ hz₁ hz₂ hcut
  have hB0 : 0 < B := by linarith
  have hE0 : 0 < E := by linarith
  have hA0 : 0 < A := by linarith
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD0 : 0 < D₁ * D₂ := mul_pos hD₁0 hD₂0
  let R : ℝ := Real.sqrt (M / (E * A * B)) / (D₁ * D₂)
  let w : ℝ → ℝ → ℂ := fun y u =>
    if B ≤ y ∧ D₁ * D₂ ≤ u then dualHighDivWeight M n Λ E A y u else 0
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hw : ∀ y u, ‖w y u‖ ≤ R := by
    intro y u
    dsimp [w, dualHighDivWeight]
    split_ifs with hguard hsupport
    · have hy0 : 0 < y := hB0.trans_le hguard.1
      have hu0 : 0 < u := hD0.trans_le hguard.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hroot : Real.sqrt (M / (E * A * y)) ≤ Real.sqrt (M / (E * A * B)) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_div_iff₀ (by positivity : 0 < E * A * y)
          (by positivity : 0 < E * A * B)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hguard.1 (by positivity : 0 ≤ E * A)) hM.le
      dsimp [R]
      calc
        Real.sqrt (M / (E * A * y)) / u ≤ Real.sqrt (M / (E * A * B)) / u := by
          gcongr
        _ ≤ Real.sqrt (M / (E * A * B)) / (D₁ * D₂) := by
          gcongr
          exact hguard.2
    · simpa using hR
    · simpa using hR
  have hrows' : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B := by
    intro a ha
    exact ⟨(hrows a ha).1, (hrows a ha).2.2⟩
  have hbase := hpair n B D₁ D₂ p₁ p₂ cols rows z₁ z₂ ρ Z w R
    hn hB hD₁ hD₂ hD₁n hD₂n hp₁ hp₂ hcols hrows' hρ hR hw hz₁ hz₂
  have hkernel (c d : Ideal (𝓞 K)) :
      (∑ ec ∈ (qsDivisors c).filter p₁,
        ∑ ed ∈ (qsDivisors d).filter p₂,
          (qsMu (ec * ed) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
              (F.character d).idealValue a * w (qsN a) (qsN (ec * ed))) =
      (∑ ec ∈ (qsDivisors c).filter p₁,
        ∑ ed ∈ (qsDivisors d).filter p₂,
          (qsMu (ec * ed) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
              (F.character d).idealValue a *
                dualHighDivWeight M n Λ E A (qsN a) (qsN (ec * ed))) := by
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
  simp_rw [hkernel] at hbase
  have harith := dual_highdiv_shell_arith M n B D₁ D₂ Λ E A α
    hM hn hB hD₁ hD₂ hΛ hE hA hcut
  have hcoef : 0 ≤ C₂ * (n * B) ^ (2 * ε) := by positivity
  have henergy : 0 ≤ ∑ c ∈ cols, Z c ^ 2 := by positivity
  calc
    _ ≤ C₂ * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
          ∑ c ∈ cols, Z c ^ 2 := hbase
    _ = (C₂ * (n * B) ^ (2 * ε)) *
          (R * Real.sqrt (D₁ * D₂) *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) *
          ∑ c ∈ cols, Z c ^ 2 := by ring
    _ ≤ (C₂ * (n * B) ^ (2 * ε)) *
          (32 * Λ * (M + B ^ α * Real.sqrt (M / B))) *
          ∑ c ∈ cols, Z c ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left harith hcoef) henergy
    _ = (32 * C₂) * (n * B) ^ (2 * ε) * Λ *
          (M + B ^ α * Real.sqrt (M / B)) * ∑ c ∈ cols, Z c ^ 2 := by ring

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
