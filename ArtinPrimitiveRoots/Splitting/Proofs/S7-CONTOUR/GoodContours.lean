import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HorizontalLimits

set_option autoImplicit false

open scoped NumberField Interval Topology
open Filter NumberField MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Select lower and upper sharp-zeta contours with vanishing weighted horizontal integrals. -/
theorem good_contour_sequences (K : Type*) [Field K] [NumberField K]
    (W : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ s : ℂ, (-1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖W s‖ ≤ C * Real.rpow (1 + |s.im|) (-6 : ℝ)) :
    ∃ a b : ℕ → ℝ,
      Tendsto a atTop atBot ∧ Tendsto b atTop atTop ∧
      (∀ n : ℕ, a n < 0 ∧ 0 < b n) ∧
      (∀ (n : ℕ) (ρ : ℂ), ρ ∈ nontrivialZeros K →
        ρ.im ≠ a n ∧ ρ.im ≠ b n) ∧
      Tendsto (fun n : ℕ => ∫ σ : ℝ in (-1 / 2 : ℝ)..2,
        dedekindZetaLogDerivative K ((σ : ℂ) + (a n : ℂ) * Complex.I) *
          W ((σ : ℂ) + (a n : ℂ) * Complex.I)) atTop (𝓝 (0 : ℂ)) ∧
      Tendsto (fun n : ℕ => ∫ σ : ℝ in (-1 / 2 : ℝ)..2,
        dedekindZetaLogDerivative K ((σ : ℂ) + (b n : ℂ) * Complex.I) *
          W ((σ : ℂ) + (b n : ℂ) * Complex.I)) atTop (𝓝 (0 : ℂ)) := by
  classical
  obtain ⟨A, hA, hheight⟩ := sharp_good_height K
  let α : ℕ → ℝ := fun n => -(n : ℝ) - 4
  let β : ℕ → ℝ := fun n => (n : ℝ) + 3
  have hNeg (n : ℕ) := hheight (α n) (Or.inr (by
    dsimp [α]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith))
  have hPos (n : ℕ) := hheight (β n) (Or.inl (by
    dsimp [β]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith))
  choose a haBin haSharp haL using hNeg
  choose b hbBin hbSharp hbL using hPos
  have haUpper (n : ℕ) : a n ≤ -(n : ℝ) - 3 := by
    have h := (haBin n).2
    dsimp [α] at h
    linarith
  have hbLower (n : ℕ) : (n : ℝ) + 3 ≤ b n := by
    simpa [β] using (hbBin n).1
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have haBot : Tendsto a atTop atBot := by
    apply tendsto_atBot.mpr
    intro r
    filter_upwards [hNat.eventually (eventually_ge_atTop (-r))] with n hn
    linarith [haUpper n]
  have hbTop : Tendsto b atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hbLower n]) hNat
  have hsign (n : ℕ) : a n < 0 ∧ 0 < b n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor <;> linarith [haUpper n, hbLower n]
  have hnozero (n : ℕ) (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) :
      ρ.im ≠ a n ∧ ρ.im ≠ b n := by
    constructor
    · intro heq
      exact (haSharp n ρ heq).2 hρ.2.2
    · intro heq
      exact (hbSharp n ρ heq).2 hρ.2.2
  have hαAbs : Tendsto (fun n : ℕ => |α n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    dsimp [α]
    rw [abs_of_nonpos (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)]
    linarith
  have hβAbs : Tendsto (fun n : ℕ => |β n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    dsimp [β]
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hlimNeg := horizontal_integral_tendsto_zero (dedekindZetaLogDerivative K) W
    A C hA.le hC α a haBin hαAbs haL hdecay
  have hlimPos := horizontal_integral_tendsto_zero (dedekindZetaLogDerivative K) W
    A C hA.le hC β b hbBin hβAbs hbL hdecay
  exact ⟨a, b, haBot, hbTop, hsign, hnozero, hlimNeg, hlimPos⟩

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
