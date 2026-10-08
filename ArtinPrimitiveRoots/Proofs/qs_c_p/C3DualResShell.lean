import ArtinPrimitiveRoots.Proofs.qs_c_p.C3DualPair
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.TransBound

/-! The dual residue shell with normalized column coefficients. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2

/-- The exact closed upper cutoff of the dual zero-residue term. -/
def dualResidueWeight (M n Λ E A y u : ℝ) : ℂ :=
  if u ≤ 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A * y)) then
    ((M / E : ℝ) : ℂ)
  else 0

open Classical in
/-- Normalizing both columns by their square-root norms gives the E3 scalar
envelope for every residue shell satisfying the dual upper support. -/
theorem dual_residue_shell_bound {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hα₂ : α ≤ 2)
    (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ B D₁ D₂ Λ E A : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
        [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z₁ z₂ ρ : Ideal (𝓞 K) → ℂ)
        (Z : Ideal (𝓞 K) → ℝ),
        0 < M → 1 ≤ n → 1 ≤ B → B ≤ κ → 1 ≤ D₁ → 1 ≤ D₂ →
        1 ≤ Λ → 1 ≤ E →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) →
        (∀ c ∈ cols, ‖z₁ c‖ ≤ Z c / Real.sqrt n) →
        (∀ c ∈ cols, ‖z₂ c‖ ≤ Z c / Real.sqrt n) →
        D₁ * D₂ ≤ 2 * Λ * (n * Real.sqrt (E / (M * B))) →
        ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
            ∑ ec ∈ (qsDivisors c).filter p₁,
              ∑ ed ∈ (qsDivisors d).filter p₂,
                (qsMu (ec * ed) : ℂ) *
                  ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                    (F.character d).idealValue a *
                      dualResidueWeight M n Λ E A (qsN a) (qsN (ec * ed))
            else 0‖ ≤
          C * (n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) *
            (M + Real.sqrt M * κ ^ (α - 1/2)) * ∑ c ∈ cols, Z c ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hpair⟩ := QSC3.pair_mellin_bound F hrf ε hε
  obtain ⟨Cα, hCα, hHE⟩ := hexp ε hε
  refine ⟨64 * C₂ * Cα, by positivity, ?_⟩
  intro M n κ B D₁ D₂ Λ E A p₁ p₂ _ _ cols rows z₁ z₂ ρ Z
    hM hn hB hBκ hD₁ hD₂ hΛ hE hp₁ hp₂ hcols hrows hρ hz₁ hz₂ hcut
  have hn0 : 0 < n := by linarith
  have hE0 : 0 < E := by linarith
  have hR : 0 ≤ M / E := by positivity
  let w : ℝ → ℝ → ℂ := dualResidueWeight M n Λ E A
  have hw : ∀ y u, ‖w y u‖ ≤ M / E := by
    intro y u
    dsimp [w, dualResidueWeight]
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
    · simpa using hR
  let μ : Measure ℝ := Measure.dirac (0 : ℝ)
  let s : ℝ → ℂ := fun _ => 0
  let φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let Φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let gmaj : ℝ → ℝ := fun _ => M / E
  let Z' : Ideal (𝓞 K) → ℝ := fun c => Z c / Real.sqrt n
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hsc : Continuous s := continuous_const
  have hs : ∀ t, (s t).re = (0 : ℝ) := by intro t; simp [s]
  have hΦ : ∀ y u x : ℝ, 0 < x →
      Φ y u x = ∫ t, ((x : ℂ) ^ (s t)) * φ y u t ∂μ := by
    intro y u x _hx
    simp [Φ, φ, s, μ]
  have hgm : Integrable gmaj μ := by simp [gmaj, μ]
  have hφ : ∀ y u t, ‖φ y u t‖ ≤ gmaj t := by
    intro y u t
    exact hw y u
  have hmass : ∫ t, gmaj t ∂μ ≤ M / E := by simp [gmaj, μ]
  have hz₁' : ∀ c ∈ cols, ‖z₁ c‖ * qsN c ^ (0 : ℝ) ≤ Z' c := by
    simpa only [Real.rpow_zero, mul_one] using hz₁
  have hz₂' : ∀ c ∈ cols, ‖z₂ c‖ * qsN c ^ (0 : ℝ) ≤ Z' c := by
    simpa only [Real.rpow_zero, mul_one] using hz₂
  have hbase := hpair n B D₁ D₂ (M / E) 0 p₁ p₂ cols rows z₁ z₂ ρ Z'
    μ s φ Φ gmaj hn hB hD₁ hD₂ hp₁ hp₂ hcols hrows hρ hsc hs hΦ hgm hφ hmass hz₁' hz₂'
  have henergy_eq : (∑ c ∈ cols, Z' c ^ 2) = (∑ c ∈ cols, Z c ^ 2) / n := by
    simp only [Z', div_pow, Real.sq_sqrt hn0.le, Finset.sum_div]
  have henergy : 0 ≤ ∑ c ∈ cols, Z c ^ 2 := by positivity
  have hN₂ : 0 ≤ qsNorm F (2 * B) (2 * n / D₂) := by rw [qsNorm]; positivity
  have hN₁b := QSC3.norm_bound_hexp F hrf hHE hε hCα (by linarith : 0 < α) hn hB hD₁
  have hN₂b := QSC3.norm_bound_hexp F hrf hHE hε hCα (by linarith : 0 < α) hn hB hD₂
  have hE3 := QSC3.E3_estimate hα hα₂ hM hn hB hBκ hD₁ hD₂ hE hΛ
    (by positivity : 0 ≤ Cα * (4 * n * B) ^ ε) hN₂ hN₁b hN₂b hcut
  have hrootone : 1 ≤ Real.sqrt (2 * Λ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (2 * Λ) := Real.sqrt_le_sqrt (by linarith)
  have hscalar :
      M / E * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) / n ≤
        64 * (Cα * (4 * n * B) ^ ε) * Λ ^ (3/2 : ℝ) *
          (M + Real.sqrt M * κ ^ (α - 1/2)) := by
    calc
      _ ≤ (M / E * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) / n) *
            Real.sqrt (2 * Λ) := by
        exact le_mul_of_one_le_right (by positivity) hrootone
      _ = M / E * Real.sqrt (2 * Λ * n) * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            n ^ (-(3/2 : ℝ)) := by
        calc
          _ = M / E * (Real.sqrt (2 * Λ) / n) * Real.sqrt (D₁ * D₂) *
              Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) := by ring
          _ = _ := by rw [← QSC3.est_pre (by linarith : 0 ≤ Λ) hn0]; ring
      _ ≤ _ := hE3
  rw [henergy_eq] at hbase
  have hcoef : 0 ≤ C₂ * (n * B) ^ ε := by positivity
  calc
    _ ≤ C₂ * (n * B) ^ ε * (M / E) * Real.sqrt (D₁ * D₂) *
        Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
          ((∑ c ∈ cols, Z c ^ 2) / n) := hbase
    _ = (C₂ * (n * B) ^ ε) *
        (M / E * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) / n) *
            ∑ c ∈ cols, Z c ^ 2 := by ring
    _ ≤ (C₂ * (n * B) ^ ε) *
        (64 * (Cα * (4 * n * B) ^ ε) * Λ ^ (3/2 : ℝ) *
          (M + Real.sqrt M * κ ^ (α - 1/2))) * ∑ c ∈ cols, Z c ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar hcoef) henergy
    _ = (64 * C₂ * Cα) * (n * B) ^ ε * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) *
        (M + Real.sqrt M * κ ^ (α - 1/2)) * ∑ c ∈ cols, Z c ^ 2 := by ring

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
