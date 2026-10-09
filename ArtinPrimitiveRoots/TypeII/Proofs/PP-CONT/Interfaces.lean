import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.Interfaces

/-! Exact interfaces for the PP Dirichlet-series continuation estimates. -/

namespace ArtinPrimitiveRoots.Proofs.pp_cont_p

open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

noncomputable def contPrefix (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊u⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
    χ (n : ZMod q)

noncomputable def contDiscrepancy (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) : ℂ := contPrefix q χ u - characterMean q χ * (u : ℂ)

noncomputable def contTail (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ) : ℂ :=
  -contDiscrepancy q χ Y * Complex.exp (-s * (Real.log Y : ℂ)) +
    s * ∫ u : ℝ in Set.Ioi Y,
      contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))

theorem cont_characterMean_norm_le_one {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) : ‖characterMean q χ‖ ≤ 1 := by
  rw [characterMean, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ a ∈ Finset.range q, χ (a : ZMod q)‖ ≤ q := by
    calc
      _ ≤ ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Finset.range q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact χ.norm_le_one _
      _ = q := by simp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (q : ℝ)⁻¹ * ‖∑ a ∈ Finset.range q, χ (a : ZMod q)‖
        ≤ (q : ℝ)⁻¹ * q :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

theorem cont_discrepancy_bound {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 0 ≤ u) :
    ‖contDiscrepancy q χ u‖ ≤ 2 * (q : ℝ) := by
  sorry

theorem cont_tail_integrable {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) :
    IntegrableOn
      (fun u : ℝ => contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))) (Set.Ioi Y) := by
  sorry

theorem contDiscrepancy_aestronglyMeasurable (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    AEStronglyMeasurable (contDiscrepancy q χ) volume := by
  sorry

theorem contTail_differentiableAt {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (contTail q χ Y) s := by
  sorry

theorem cont_tail_bound {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) :
    ‖contTail q χ Y s‖ ≤
      2 * (q : ℝ) * (1 + ‖s‖ / s.re) * Real.rpow Y (-s.re) := by
  sorry

theorem cont_abel_identity {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  sorry

theorem cont_approximation {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hσlo : 1 / 2 ≤ s.re) (hσhi : s.re ≤ 2)
    (him : 1 / 2 ≤ |s.im|) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
      characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1)‖ ≤
      4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-s.re) := by
  sorry

theorem cont_partial_sum_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    {Y σ v : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletPartialSum q χ Y (⟨σ, v⟩ : ℂ)‖ ≤
      (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := by
  sorry

theorem cont_growth_bound
    (hLog : ArtinPrimitiveRoots.Proofs.pp_phase_p.phaseLogPhaseStatement) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              ∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                1 / 2 ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                  ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                    Real.exp (C₀ * T ^ 2) := by
  sorry

end ArtinPrimitiveRoots.Proofs.pp_cont_p
