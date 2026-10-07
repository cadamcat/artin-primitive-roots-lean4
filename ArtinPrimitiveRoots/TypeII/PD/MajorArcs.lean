import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PP.Results

/-! Major-arc frequency bounds and assembly, PD `05-major-arcs.tex:9-465`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

/-- Small-prime polynomial on one prime band. -/
noncomputable def bandPrimePolynomial (P : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi t : ℝ) : ℂ :=
  (1 / P) * ∑ p ∈ Pset,
    chiValue p * Complex.exp (Complex.I * (t + xi) * Real.log (p : ℝ))

/-- The long coefficient polynomial `M_α(t)`. -/
noncomputable def alphaFrequency {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x t : ℝ) (chiValue : ℕ → ℂ) : ℂ :=
  (1 / family.Hm x) *
    ∑ m ∈ familyTerms family x,
      family.alpha x m * chiValue m * Complex.exp (Complex.I * t * Real.log (m : ℝ))

/-- The second-variable polynomial `N_β(t)`. -/
noncomputable def betaFrequency (Hn : ℝ) (beta chiValue : ℕ → ℂ) (t : ℝ) : ℂ :=
  (1 / Hn) *
    ∑ n ∈ dyadicIntegers Hn,
      beta n * chiValue n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- The small-prime factor `B_λ(t)` after isolating one marked band. -/
noncomputable def majorSmallPrimeFactor (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (lambda xi t : ℝ) (chiValues : Fin K → ℕ → ℂ) : ℂ :=
  Complex.exp (Complex.I * lambda * t) *
    ∏ i : Fin K,
      ((1 / bandMass x (a i)) *
        ∑ p ∈ primeBand x (a i),
          chiValues i p * Complex.exp (Complex.I * (t + xi) * Real.log (p : ℝ)))

/-- The finite family of unit intervals that meet the large-frequency set. -/
def sparseUnitIntervals (x X B P A_s : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi : ℝ) : Set ℤ :=
  {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ 2 * X * Real.rpow (Real.log x) B ∧
    Real.rpow (Real.log x) A_s *
      ‖bandPrimePolynomial P Pset chiValue xi t‖ > 1}

/-- Supremum of the `N_β` energy on one unit interval. -/
noncomputable def betaUnitIntervalEnergy (Hn : ℝ) (beta chiValue : ℕ → ℂ)
    (j : ℤ) : ℝ :=
  sSup ((fun t : ℝ => ‖betaFrequency Hn beta chiValue t‖ ^ 2) ''
    Set.Icc (j : ℝ) ((j : ℝ) + 1))

/-- The energy integral in `maj:energy`. -/
noncomputable def majorEnergyIntegral (T : ℝ) (B M N : ℝ → ℂ) : ℝ :=
  ∫ t in (-T)..T, ‖B t * M t * N t‖ ^ 2

/-- `maj:sparse-frequency` — PD `05-major-arcs.tex:165-255`, Lemma 5.3. -/
theorem sparse_frequency (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∀ B A_s : ℝ, 0 < B → 0 < A_s →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ X : ℝ, x / 2 ≤ X → X ≤ 2 * x →
            ∀ P : ℝ, (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) ≤ Real.log P →
              ∀ C₁ : ℝ, 0 < C₁ → Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ) →
              ∀ Pset : Finset ℕ,
                (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
                ∀ q : ℕ, 1 ≤ q →
                  ∀ χ : DirichletCharacter ℂ q, ∀ xi : ℝ,
                    ∀ Hn : ℝ, Real.rpow x δ ≤ Hn → Hn ≤ 2 * x →
                      ∀ beta chiN : ℕ → ℂ,
                        (∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C) →
                        (∀ n, ‖chiN n‖ ≤ 1) →
                          let bad := sparseUnitIntervals x X B P A_s Pset
                            (fun p => (χ (p : ZMod q) : ℂ)) xi
                          (Set.ncard bad : ℝ) ≤
                            Real.exp (C₀ * Real.rpow L (91 / 100 : ℝ)) ∧
                          (∑' j : ℤ, if j ∈ bad then
                            betaUnitIntervalEnergy Hn beta chiN j else 0) ≤
                            C₀ * Real.rpow L (2 * C + 1) := by
  sorry

/-- Product energy after the six-character major-arc separation. -/
noncomputable def separatedMajorEnergy (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (lambda xi B₁ : ℝ)
    (chiSmall : Fin K → ℕ → ℂ) (chiAlpha chiBeta : ℕ → ℂ) : ℝ :=
  let X := family.Hm x * family.Hn x
  majorEnergyIntegral (2 * X * Real.rpow (Real.log x) B₁)
    (fun t => majorSmallPrimeFactor x K a lambda xi t chiSmall)
    (fun t => alphaFrequency family x t chiAlpha)
    (fun t => betaFrequency (family.Hn x) beta chiBeta t)

/-- The isolated-band energy estimate used for the major-arc separation. -/
noncomputable def isolatedMajorEnergy (x P Hn : ℝ) (Pset : Finset ℕ)
    (chiSmall : ℕ → ℂ) (xi : ℝ)
    (family : ℝ → ℂ) (betaPoly : ℝ → ℂ) (B₁ : ℝ) : ℝ :=
  ∫ t in (-(2 * Hn * Real.rpow (Real.log x) B₁))..
      (2 * Hn * Real.rpow (Real.log x) B₁),
    ‖bandPrimePolynomial P Pset chiSmall xi t * family t * betaPoly t‖ ^ 2

/-- `t2:pd.major-separation` — PD `05-major-arcs.tex:257-376`. The six-character Fourier
expansion and Mellin separation reduce the major bound to the uniform energy estimate
`separatedMajorEnergy`. -/
theorem major_separation
    (δ C q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A₀ A' : ℝ, 0 < A₀ → 0 < A' →
      ∃ B₁ C_A x₀ : ℝ, 0 < B₁ ∧ 0 < C_A ∧ 2 ≤ x₀ ∧
        ∀ family : CoefficientFamily δ C c₁ c₂,
          HasLongCoefficientCancellation family →
          ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              ∀ chiSmall : Fin K → ℕ → ℂ,
                ∀ i p, ‖chiSmall i p‖ ≤ 1 →
                  ∀ chiAlpha chiBeta : ℕ → ℂ,
                    (∀ m, ‖chiAlpha m‖ ≤ 1) → (∀ n, ‖chiBeta n‖ ≤ 1) →
                      ∀ lambda xi : ℝ, |lambda| ≤ 2 * Real.rpow (Real.log x) A₀ →
                        separatedMajorEnergy x K a family beta lambda xi B₁
                          chiSmall chiAlpha chiBeta ≤
                          C_A * Real.rpow (Real.log x) (-A') := by
  sorry

/-- `t2:pd.major-energy` — PD `05-major-arcs.tex:371-433`. -/
theorem major_energy
    (δ C c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (ha : ValidBands K a) :
    ∀ A₀ A : ℝ, 0 < A₀ → 0 < A →
      ∃ B₁ C_A x₀ : ℝ, 0 < B₁ ∧ 0 < C_A ∧ 2 ≤ x₀ ∧
        ∀ family : CoefficientFamily δ C c₁ c₂,
          HasLongCoefficientCancellation family →
          ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              ∀ P : ℝ, (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
                  Real.log P → Real.log P ≤ 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) →
                ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧
                    P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
                  ∀ chiSmall chiAlpha chiBeta : ℕ → ℂ,
                    (∀ p, ‖chiSmall p‖ ≤ 1) →
                    (∀ m, ‖chiAlpha m‖ ≤ 1) →
                    (∀ n, ‖chiBeta n‖ ≤ 1) →
                    ∀ xi : ℝ,
                    isolatedMajorEnergy x P (family.Hn x) Pset chiSmall xi
                        (fun t => alphaFrequency family x t chiAlpha)
                        (fun t => betaFrequency (family.Hn x) beta chiBeta t) B₁ ≤
                        C_A * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `prop:major-term` — PD `05-major-arcs.tex:9-30`, Proposition 5.1. -/
theorem major_term
    (δ C Dstar q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A₀ : ℝ, 0 < A₀ →
      ∃ C_D x₀ : ℝ, 0 < C_D ∧ 2 ≤ x₀ ∧
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∀ eta psi : ℝ → ℝ, IsDyadicPartition eta →
          ContDiff ℝ ⊤ psi → HasCompactSupport psi →
          (∀ t ∈ Set.Icc (-4) 4, psi t = 1) →
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Y, Y ∈ dyadicScales x K →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
                ‖majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                  C_D * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-Dstar) := by
  sorry

/-- `t2:pd.completion` — PD `05-major-arcs.tex:435-465` and 08-type-ii.tex:236-250. The
parameter order chooses `D₁`, then the minor-moment parameters, then the marked-band threshold. -/
theorem completion
    (δ C Dstar q_d c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
              ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                  (family.interval x) (family.alpha x) beta‖ ≤
                    C' * (family.Hm x * family.Hn x) *
                      Real.rpow (Real.log x) (-Dstar) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PD
