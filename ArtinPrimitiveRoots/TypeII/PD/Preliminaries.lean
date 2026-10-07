import ArtinPrimitiveRoots.TypeII.PD.Defs

/-! Elementary mean-value, rough-count, and moderate-phase estimates from PD
`02-preliminaries.tex:73-235`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

/-- A finite Dirichlet polynomial in logarithmic coordinates. -/
noncomputable def dirichletPolynomial (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (Y + 1), coeff n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- Integers in a real interval that are rough above `W`. -/
noncomputable def roughIntegersInInterval (lo hi W : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun n => lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W

/-- Rough integers in an interval occupying one specified residue class. -/
noncomputable def roughResidueCount (lo hi W : ℝ) (d : ℕ) (b : ZMod d) : ℝ :=
  (((Finset.range (⌊hi⌋₊ + 1)).filter fun (n : ℕ) =>
    lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W ∧ (n : ZMod d) = b).card : ℝ)

/-- `t2:pd.moment-bounds` — PD `02-preliminaries.tex:73-114`, Lemma 2.2. -/
theorem moment_bounds :
    (∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧ ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k) ≤
            Ck * Y * Real.rpow (Real.log (2 * Y)) Ck ∧
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k / (n + 1 : ℝ)) ≤
            Ck * Real.rpow (Real.log (2 * Y)) Ck) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ Y : ℕ, ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2 ≤
          C₀ * (b - a + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
            ∑ n ∈ Finset.range (Y + 1), ‖coeff n‖ ^ 2) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ Y : ℕ, ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∀ T : Finset ℝ,
          (∀ t ∈ T, a ≤ t ∧ t ≤ b) →
          (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
            (∑ t ∈ T, ‖dirichletPolynomial Y coeff t‖ ^ 2) ≤
              C₁ * (b - a + 1 + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
                Real.rpow (Real.log (2 * (Y : ℝ))) 2 *
                ∑ n ∈ Finset.range (Y + 1), ‖coeff n‖ ^ 2) := by
  sorry

/-- `t2:pd.rough-counts` — PD `02-preliminaries.tex:175-235`, Lemma 2.5. -/
theorem rough_counts :
    ∀ δ C aExp A : ℝ, 0 < δ → 0 < C → 0 < aExp → aExp < 1 → 0 < A →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let W := roughCutoff x
          ∀ H : ℝ, Real.rpow x δ ≤ H → H ≤ Real.rpow x C →
            ∀ l r : ℝ, H ≤ l → l ≤ r → r ≤ 2 * H →
              (|((roughIntegersInInterval l r W).card : ℝ) -
                roughSieveProduct W * (r - l + 1)| ≤ H * Real.rpow L (-A)) ∧
              (∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.exp (Real.rpow L aExp) →
                roughAbove d W →
                ∀ b : ZMod d,
                  |roughResidueCount l r W d b -
                    roughSieveProduct W * (r - l + 1) / (d : ℝ)| ≤
                    (H / d) * Real.rpow L (-A)) ∧
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                ∀ χ : DirichletCharacter ℂ q,
                  ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
                        l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W),
                      (χ (n : ZMod q) : ℂ)) -
                    (if χ = 1 then
                      (roughSieveProduct W * (r - l + 1) : ℝ) else 0 : ℂ)‖ ≤
                    H * Real.rpow L (-A) := by
  sorry

/-- The residue-restricted sum in the moderate-frequency estimate. -/
noncomputable def integerResiduePhaseSum (q : ℕ) (a : ZMod q)
    (t : ℝ) (l r : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a),
    Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- `t2:pd.moderate-phase` — PD `02-preliminaries.tex:160-173` and `05-major-arcs.tex:89-104`.
-/
theorem moderate_phase (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.exp (L / Real.log L ^ 2)
        ∀ N : ℝ, Real.rpow x δ ≤ N →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ a : ZMod q, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
              ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                ‖integerResiduePhaseSum q a t l r -
                  ((1 / (q : ℂ)) *
                    ∫ y in l..r, Complex.exp (Complex.I * t * Real.log y))‖ ≤
                  C₀ * (1 + |t|) ∧
                ‖∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤
                  C₀ * N / |t| ∧
                ((q : ℝ) / N) *
                    ‖integerResiduePhaseSum q a t l r‖ ≤
                  C₀ * (|t|⁻¹ + Real.rpow x (-cδ)) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PD
