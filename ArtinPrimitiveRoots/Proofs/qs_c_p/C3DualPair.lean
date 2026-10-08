import ArtinPrimitiveRoots.Proofs.qs_c_p.C3Helpers
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Pair

/-! Uniform shell bounds for independently twisted column coefficients. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

open Classical in
/-- A bounded column-independent shell weight admits separate column
coefficients with one common energy majorant. -/
theorem dual_shell_pair_bound_uniform {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n B D₁ D₂ : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
        [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z₁ z₂ ρ : Ideal (𝓞 K) → ℂ)
        (Z : Ideal (𝓞 K) → ℝ) (w : ℝ → ℝ → ℂ) (R : ℝ),
        1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ →
        D₁ ≤ 2 * n → D₂ ≤ 2 * n →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) → 0 ≤ R → (∀ y u, ‖w y u‖ ≤ R) →
        (∀ c ∈ cols, ‖z₁ c‖ ≤ Z c) → (∀ c ∈ cols, ‖z₂ c‖ ≤ Z c) →
        ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
            ∑ e₁ ∈ (qsDivisors c).filter p₁,
              ∑ e₂ ∈ (qsDivisors d).filter p₂,
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                    (F.character d).idealValue a * w (qsN a) (qsN (e₁ * e₂))
            else 0‖ ≤
          C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, Z c ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hC₂bound⟩ := QSC3.pair_mellin_bound F hrf ε hε
  obtain ⟨C₁, hC₁, hNormFor⟩ :=
    qs_c3_sqrt_norm_product_envelope F hrf α ε hε hα hexp
  let C : ℝ := C₂ * C₁
  refine ⟨C, mul_pos hC₂ hC₁, ?_⟩
  intro n B D₁ D₂ p₁ p₂ _ _ cols rows z₁ z₂ ρ Z w R hn hB hD₁ hD₂ hD₁n hD₂n
    hp₁ hp₂ hcols hrows hρ hR hw hz₁ hz₂
  let μ : Measure ℝ := Measure.dirac (0 : ℝ)
  let s : ℝ → ℂ := fun _ => 0
  let φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let Φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let gmaj : ℝ → ℝ := fun _ => R
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
  have hmass : ∫ t, gmaj t ∂μ ≤ R := by simp [gmaj, μ]
  have hz₁' : ∀ c ∈ cols, ‖z₁ c‖ * qsN c ^ (0 : ℝ) ≤ Z c := by
    simpa only [Real.rpow_zero, mul_one] using hz₁
  have hz₂' : ∀ c ∈ cols, ‖z₂ c‖ * qsN c ^ (0 : ℝ) ≤ Z c := by
    simpa only [Real.rpow_zero, mul_one] using hz₂
  have hpair := hC₂bound n B D₁ D₂ R 0 p₁ p₂ cols rows z₁ z₂ ρ Z μ s φ Φ gmaj
    hn hB hD₁ hD₂ hp₁ hp₂ hcols hrows hρ hsc hs hΦ hgm hφ hmass hz₁' hz₂'
  have hNorm := hNormFor B n D₁ D₂ hB hn hD₁ hD₂ hD₁n hD₂n
  have henergy : 0 ≤ ∑ c ∈ cols, Z c ^ 2 := by positivity
  calc
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            ∑ c ∈ cols, Z c ^ 2 := hpair
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          (C₁ * (n * B) ^ ε *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) *
              ∑ c ∈ cols, Z c ^ 2 := by gcongr
    _ = C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, Z c ^ 2 := by
        calc
          _ = C₂ * C₁ * ((n * B) ^ ε * (n * B) ^ ε) * R * Real.sqrt (D₁ * D₂) *
                (n / Real.sqrt (D₁ * D₂) +
                  Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
                  ∑ c ∈ cols, Z c ^ 2 := by ring
          _ = _ := by
            rw [← Real.rpow_add (by positivity : 0 < n * B)]
            dsimp [C]
            ring

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
