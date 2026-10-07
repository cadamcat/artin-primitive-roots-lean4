import ArtinPrimitiveRoots.TypeII.PD.Defs

/-! Determinant and root-counting statements, PD `03-determinant.tex:68-737`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII

/-- `t2:pd.cauchy` — PD `03-determinant.tex:68-169`. The dyadic decomposition, Cauchy square,
coprime reduction, and progression-divisor estimate used to reduce the marked bilinear form to
the determinant moment. Fixed parameters precede all asymptotic constants. -/
theorem cauchy_decomposition
    (δ C Dstar q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A : ℝ, 0 < A →
      ∃ C_A Cscale Cmain CDiv x₀ : ℝ,
        0 < C_A ∧ 0 < Cscale ∧ 0 < Cmain ∧ 0 < CDiv ∧ 2 ≤ x₀ ∧
          ∀ family : CoefficientFamily δ C c₁ c₂,
            HasLongCoefficientCancellation family →
            ∀ x : ℝ, x₀ ≤ x →
              ∀ eta : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta →
                Function.support eta ⊆ Set.Icc 1 4 →
                (∀ y, 0 ≤ eta y) → IsDyadicPartition eta →
                ∀ beta : ℕ → ℂ,
                  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers (family.Hn x),
                    ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                  ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                    let X := family.Hm x * family.Hn x
                    let Sigma := coefficientBilinearSum x K a q_d family beta F
                    (‖Sigma - ∑ Y ∈ dyadicScales x K,
                        dyadicCauchyPiece x K a q_d Y family beta F eta‖ ≤
                      C_A * X * Real.rpow (Real.log x) (-A)) ∧
                    (∀ Y ∈ dyadicScales x K,
                      0 ≤ cauchySquare x K a Y family beta eta ∧
                      ‖dyadicCauchyPiece x K a q_d Y family beta F eta‖ ^ 2 ≤
                        Cmain * (X / Y) * cauchySquare x K a Y family beta eta ∧
                      |cauchySquare x K a Y family beta eta -
                        coprimeCauchySquare x K a Y family beta eta| ≤
                        C_A * X * Y * Real.rpow (Real.log x) (-A)) ∧
                    (∀ ta tb : Fin K → ℕ,
                      IsMarkedPrimeTuple x K a ta → IsMarkedPrimeTuple x K a tb →
                      Nat.Coprime (tupleProduct ta) (tupleProduct tb) →
                      ∀ m n r s : ℕ,
                        ((∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                          r * s - 1 = tupleProduct tb * h) ↔
                          ((tupleProduct tb : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) -
                            ((tupleProduct ta : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) =
                              (tupleProduct tb : ℤ) - (tupleProduct ta : ℤ))) ∧
                    (∀ Y ∈ dyadicScales x K, ∀ l : ℕ,
                      Y / 2 ≤ (l : ℝ) → (l : ℝ) ≤ 2 * Y →
                        (∑ h ∈ Finset.range (⌊X / Y⌋₊ + 1),
                          (tau (1 + l * h) : ℝ) ^ 2) ≤
                          CDiv * (X / Y) * Real.rpow (Real.log x) 3) ∧
                    (Finset.card (dyadicScales x K) : ℝ) ≤ Cscale * Real.log x ∧
                    (∀ Y ∈ dyadicScales x K,
                      (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
                        Real.log Y ∧ Real.log Y ≤ Cscale * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
  sorry

/-- `det:good-state` — PD `03-determinant.tex:269-293`. For fixed valid marked lists, the
Lebesgue measure of ratios failing either physical-position test is exponentially small. -/
theorem good_state
    (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ c x₀ : ℝ, 0 < c ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ d₀ : ℕ, d₀ ∈ padScales x K →
          ∀ Y ∈ dyadicScales x K,
            ∀ p : PrimeLists x K, ValidPrimeLists x K a p →
              (∫ r in (0 : ℝ)..1,
                if IsGoodRatio x Y (d₀ : ℝ) K a p r then (0 : ℝ) else 1) ≤
                Real.exp (-c * Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
  sorry

/-- `t2:pd.endpoints` — PD `03-determinant.tex:295-341`. The endpoint vectors are supported on
lists with exactly `M_J` distinct marked primes in every group, have the indicated coordinates,
and satisfy the norm and pointwise bounds uniform in `K,J`. -/
theorem endpoint_bounds
    (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ C_e : ℝ, 0 < C_e ∧
      ∀ K : ℕ, ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ family : CoefficientFamily δ C c₁ c₂, ∀ x : ℝ, 2 ≤ x →
        ∀ d₀ : ℕ, d₀ ∈ padScales x K →
          ∀ Y, Y ∈ dyadicScales x K →
          ∀ beta : ℕ → ℂ,
            (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
            Real.sqrt (physicalNormSq x K a
              (endpointFVector x K a ((d₀ : ℝ) * Y)
                (family.Hm x) (family.Hn x) family beta)) ≤
                Real.rpow ((d₀ : ℝ) * Y * family.Hm x * family.Hn x)
                  (1 / 2 : ℝ) * Real.rpow (Real.log x) C_e ∧
            Real.sqrt (physicalNormSq x K a
              (endpointGVector x K a ((d₀ : ℝ) * Y)
                (family.Hm x) (family.Hn x) family beta)) ≤
                Real.rpow ((d₀ : ℝ) * Y * family.Hm x * family.Hn x)
                  (1 / 2 : ℝ) * Real.rpow (Real.log x) C_e ∧
            physicalSupNorm x K a
                (endpointFVector x K a ((d₀ : ℝ) * Y)
                  (family.Hm x) (family.Hn x) family beta) +
              physicalSupNorm x K a
                (endpointGVector x K a ((d₀ : ℝ) * Y)
                  (family.Hm x) (family.Hn x) family beta) ≤
              Real.rpow (Real.log x) C_e := by
  sorry

/-- `t2:pd.weak-kloosterman` — PD `03-determinant.tex:445-480`. -/
theorem weak_kloosterman (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ m h k : ℕ, 1 ≤ m →
        ‖kloostermanSum m h k‖ ≤
          Cε * Real.rpow m (3 / 4 + ε) * Real.rpow (Nat.gcd (Nat.gcd h k) m) (1 / 4 : ℝ) := by
  sorry

/-- `lem:root-residue` — PD `03-determinant.tex:413-591`. Primitive roots of determinant-one
matrices are equidistributed in boxes and residue classes modulo squarefree `S`, with the stated
uniform power-saving error. -/
theorem root_residue
    (δ C_K : ℝ) (hδ : 0 < δ) (hCK : 0 < C_K) :
    ∃ cδ C₀ x₀ : ℝ, cδ = δ / 1000 ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ U V : ℝ, Real.rpow x δ ≤ U → Real.rpow x δ ≤ V →
        ∀ S : ℕ, Squarefree S → ∀ hS : 0 < S, (S : ℝ) ≤
          Real.exp (C_K * Real.rpow (Real.log x) (98 / 100 : ℝ)) →
          ∀ g₀ : Matrix (Fin 2) (Fin 2) (ZMod S),
            Matrix.det g₀ = 1 →
            ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
              1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 16 →
              1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 2 →
              0 ≤ l₃ → l₃ ≤ r₃ → r₃ ≤ 1 →
              |rootResidueCount U V S g₀
                  l₁ r₁ l₂ r₂ l₃ r₃ -
                U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) /
                    ((Real.pi ^ 2 / 6) * sl2Card S hS)| ≤
                C₀ * U * V * Real.rpow x (-cδ) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PD
