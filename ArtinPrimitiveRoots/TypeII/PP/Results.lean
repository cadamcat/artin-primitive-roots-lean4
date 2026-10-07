import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.Proofs.pp1.HalaszMeanValue

/-! Statements in the Prime Predecessors long-prime chain, PP
`02-long-prime.tex:8-579`. -/

namespace ArtinPrimitiveRoots.TypeII.PP

open Classical
open ArtinPrimitiveRoots.TypeII

/-- `t2:pp.mean-value` — PP `02-long-prime.tex:48-183`, Lemma 3.2. -/
theorem mean_value :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ k : ℕ, 2 ≤ k →
        ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧
          ∀ M : ℕ, 1 ≤ M →
            (vinogradovCount s k M : ℝ) ≤
              Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
                Real.rpow (M : ℝ)
                  (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 : ℝ) := by
  exact mean_value_from_halasz

/-- `t2:pp.log-phase` — PP `02-long-prime.tex:185-310`, Lemma 3.3; also PD Lemma 2.4. `I` is an interval in
`[N', 2N']`, as in the paper (an arbitrary subset makes it false; lane `pp1`, 2026-10-07). -/
theorem log_phase :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ C : ℝ, 0 < C →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            let L := Real.log x
            let T := Real.log L
            ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' → N' ≤ 2 * Real.rpow x 5 →
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                ∀ a : ZMod q, ∀ v : ℝ,
                  Real.exp (L / (2 * T ^ 2)) ≤ |v| → |v| ≤ 4 * Real.rpow x 3 →
                    ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
                      ‖residuePhaseSum N' q a v {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                        C₀ * (N' / q) * Real.exp (-L / Real.rpow T C₃) := by
  sorry

/-- `t2:pp.L-upper` — PP `02-long-prime.tex:312-368`, including the finite Dirichlet-series
approximation and the logarithmic growth bound in the window around `Re(s)=1`. -/
theorem L_upper :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              (∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
                  s.re ≤ 2 → 1 / 2 ≤ |s.im| →
                    ∀ Y : ℝ, 1 ≤ Y →
                      ‖dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
                        characterMean q χ *
                          Complex.exp ((1 - s) * Real.log Y) / (s - 1)‖ ≤
                        C₀ * q * (1 + ‖s‖) * Real.rpow Y (-s.re)) ∧
              (∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                (1 / 2 : ℝ) ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                  ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                    Real.exp (C₀ * T ^ 2)) := by
  sorry

/-- `t2:pp.local-logderiv` — PP `02-long-prime.tex:370-424`, Lemma 3.5. The finite zero list
records multiplicity by repetition, which is the convention in the logarithmic-derivative sum. -/
theorem local_logderiv :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q, ∀ v : ℝ,
              1 ≤ |v| → |v| ≤ (5 / 2 : ℝ) * Real.rpow x 3 →
                let s₀ : ℂ := ⟨1 + rstar, v⟩
                ∃ R : ℝ, 4 * rstar ≤ R ∧ R ≤ 5 * rstar ∧
                  ∃ Z : List ℂ, (Z.length : ℝ) ≤ C₀ * T ^ 2 ∧
                    (∀ ρ ∈ Z, dirichletLValue q hq χ ρ = 0 ∧
                      ‖ρ - s₀‖ < R) ∧
                    (∀ ρ : ℂ, dirichletLValue q hq χ ρ = 0 →
                      ‖ρ - s₀‖ < R → ρ ∈ Z) ∧
                    (∀ z : ℂ, ‖z - s₀‖ = R →
                      dirichletLValue q hq χ z ≠ 0) ∧
                    (∀ z : ℂ, ‖z - s₀‖ ≤ 2 * rstar →
                      dirichletLValue q hq χ z ≠ 0 →
                        ‖deriv (dirichletLValue q hq χ) z /
                            dirichletLValue q hq χ z -
                          (Z.map fun ρ => (1 : ℂ) / (z - ρ)).sum‖ ≤
                          C₀ * T ^ 2 / rstar) := by
  sorry

/-- `t2:pp.zero-free` — PP `02-long-prime.tex:426-481`, Lemma 3.6. -/
theorem zero_free :
    ∀ C : ℝ, 0 < C →
      ∃ c C₀ x₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let width := c * T ^ 2 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              (∀ s : ℂ, 1 - width ≤ s.re →
                1 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 →
                  dirichletLValue q hq χ s ≠ 0) ∧
              (∀ s : ℂ, 1 - width / 2 ≤ s.re → s.re ≤ 1 + 1 / L →
                2 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 / 2 →
                  ‖deriv (dirichletLValue q hq χ) s /
                    dirichletLValue q hq χ s‖ ≤ C₀ * L) := by
  sorry

/-- `t2:pp.prime-polynomial` — PP `02-long-prime.tex:8-21, 483-579`, Lemma 3.1; also PD
Lemma 2.3. Correction 5 from review lane `rev-b` requires the prime set to be an interval. -/
theorem prime_polynomial :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                    ‖primeDirichletPolynomial N q χ t I‖ ≤
                      C₀ * Real.rpow L (-A) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PP
