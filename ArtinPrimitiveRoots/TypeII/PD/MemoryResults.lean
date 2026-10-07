import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant

/-! Estimates for the memory construction in PD `04-memory.tex:11-1117`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII

/-- The primewise denominator product in the memory identity. -/
noncomputable def memoryPrimeProduct (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) : ℝ :=
  ∏ p ∈ markedPrimes x K a, memoryBPrime x q_d p

/-- `t2:pd.memory-identity` — PD `04-memory.tex:43-274`. The independent-line path expansion,
after division by the primewise baseline factors, equals the ghost-edge history pairing with
global distinctness of births. -/
theorem memory_identity
    (x q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a)
    (hq₀ : 0 < q_d) (hq₁ : q_d < 1) (M : MemoryModel x K a q_d) :
    M.independentLineExpansion / (memoryPrimeProduct x K a q_d : ℂ) =
      historyValue M ∧
    (∀ j : Fin (pathLength x + 1),
      memoryQ x q_d j.val =
        if j.val = 0 ∨ j.val = pathLength x then Real.sqrt q_d else q_d) := by
  sorry

/-- `t2:pd.truncation-adjoint` — PD `04-memory.tex:276-363`. -/
theorem truncation_adjoint
    (q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (hq₀ : 0 < q_d) (hq₁ : q_d < 1) :
    ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : MemoryModel x K a q_d,
            let B := ⌈Real.rpow (Real.log x) 2⌉₊
            ‖historyValue M -
              vectorInner M.boundary
                (Matrix.mulVec (truncatedHistoryMatrix M B) M.boundary)‖ ≤
              C_A * Real.rpow (Real.log x) (-A * (pathLength x : ℝ)) ∧
            (∀ j, Matrix.conjTranspose (M.ghost j) = M.ghostAdjoint j) ∧
            (∀ j, Matrix.conjTranspose (M.edge j) = M.edgeAdjoint j) := by
  sorry

/-- `t2:pd.ghost-edge-crude` — PD `04-memory.tex:365-435`. The Schur row and column bounds are
stated with the paper's weight `v₀^{k_tot}`. -/
theorem ghost_edge_crude
    (q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (hq₀ : 0 < q_d) (hq₁ : q_d < 1) :
    ∃ v₀ C_K : ℝ, 1 < v₀ ∧ 0 < C_K ∧
      ∀ A₀ : ℝ, 0 < A₀ → ∃ Cexp x₀ : ℝ, 0 < Cexp ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : MemoryModel x K a q_d,
            let B := ⌈Real.rpow (Real.log x) 2⌉₊
            (∀ j : Fin (pathLength x + 1),
              matrixOperatorNorm (M.ghost j) ≤ C_K) ∧
            (∀ j : Fin (pathLength x),
              (∀ i, schurRowSum (M.edge j) M.sizeIndex v₀ i ≤
                  C_K * Real.rpow (B : ℝ) K *
                    (1 + Real.rpow (Real.log x) (3 * A₀))) ∧
              (∀ i, schurColumnSum (M.edge j) M.sizeIndex v₀ i ≤
                  C_K * Real.rpow (B : ℝ) K *
                    (1 + Real.rpow (Real.log x) (3 * A₀)))) ∧
            C_K * Real.rpow (B : ℝ) K *
                (1 + Real.rpow (Real.log x) (3 * A₀)) ≤
              Real.rpow (Real.log x) Cexp := by
  sorry

/-- `t2:pd.lattice-clean` — PD `04-memory.tex:437-603`. -/
theorem lattice_clean
    (q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (hqd : 0 < q_d) :
    ∀ G : ℝ, 0 < G →
      ∃ C₀ A₀ x₀ : ℝ, 0 < C₀ ∧ 0 < A₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Y ∈ dyadicScales x K,
            ∀ M : MemoryModel x K a q_d,
              (∀ j : Fin (pathLength x), ∀ source : Fin M.dimension,
                M.goodState source →
                  ∃ A' B' : ℝ, 0 < A' ∧ 0 < B' ∧
                    A' * B' ≤ C₀ * Y ∧
                    Real.rpow Y (1 / 10 : ℝ) ≤ A' ∧
                    A' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
                    Real.rpow Y (1 / 10 : ℝ) ≤ B' ∧
                    B' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
                    ∃ a₀ b₀ c₀ d₀ : ℤ, a₀ * d₀ - b₀ * c₀ = 1 ∧
                      (∀ v ∈ M.targetVectors j source,
                        |d₀ * v.1 - b₀ * v.2| ≤ A' ∧
                          |a₀ * v.2 - c₀ * v.1| ≤ B')) ∧
              (∀ j : Fin (pathLength x),
                matrixOperatorNorm (M.edgeClean j) ≤
                  Real.rpow (Real.log x) (-G)) := by
  sorry

/-- `t2:pd.dirty-raw` — PD `04-memory.tex:605-714`. -/
theorem dirty_raw
    (q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (hq₀ : 0 < q_d) (hq₁ : q_d < 1) :
    ∃ C_K c : ℝ, 0 < C_K ∧ 0 < c ∧
      ∀ A : ℝ, 0 < A → ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : MemoryModel x K a q_d,
            let B := ⌈Real.rpow (Real.log x) 2⌉₊
            let M_J := slotCount x
            let ε_K := C_K * ((B : ℝ) / (M_J : ℝ) ^ K +
              Real.rpow (B : ℝ) K *
                Real.exp (-c * Real.rpow (Real.log x) (1 / 10 : ℝ)))
            (ε_K ≤ 1 →
            (∀ j : Fin (pathLength x),
                (∀ i, schurRowSum (M.edgeDirtyRaw j) M.sizeIndex
                    (Real.exp (1 : ℝ)) i ≤ C_K * ε_K) ∧
                (∀ i, schurColumnSum (M.edgeDirtyRaw j) M.sizeIndex
                    (Real.exp (1 : ℝ)) i ≤ C_K * ε_K) ∧
                matrixOperatorNorm (M.edgeDirtyRaw j) ≤ C_K * Real.sqrt ε_K)) ∧
            ∀ j : Fin (pathLength x),
              matrixOperatorNorm (M.edgeDirtyRaw j) ≤
                C_K * Real.rpow (Real.log x) (1 - (1 / 200 : ℝ) * K) +
                  C_A * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:pd.dirty-comparison` — PD `04-memory.tex:716-782`. -/
theorem dirty_comparison
    (q_d : ℝ) (K : ℕ) (a : Fin K → ℝ) (hq₀ : 0 < q_d) (hq₁ : q_d < 1) :
    ∀ A A₀ : ℝ, 0 < A → 0 < A₀ →
      ∃ C_K x₀ : ℝ, 0 < C_K ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : MemoryModel x K a q_d, ∀ Y ∈ dyadicScales x K,
            ∀ pMin : ℝ, Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ pMin →
              let B := ⌈Real.rpow (Real.log x) 2⌉₊
              let ζK := C_K * Real.rpow (Real.log x) (3 * A₀) *
                Real.rpow (B : ℝ) K * (pMin⁻¹ + Real.rpow Y (-1 / 10 : ℝ))
              ζK ≤ Real.rpow (Real.log x) (-A) ∧
              ∀ j : Fin (pathLength x),
                (∀ i, schurRowSum (M.edgeComparison j) M.sizeIndex
                    (Real.exp (1 : ℝ)) i ≤ C_K * Real.rpow (Real.log x) (-A)) ∧
                (∀ i, schurColumnSum (M.edgeComparison j) M.sizeIndex
                    (Real.exp (1 : ℝ)) i ≤ C_K * Real.rpow (Real.log x) (-A)) ∧
                matrixOperatorNorm (M.edgeComparison j) ≤
                  C_K * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:pd.birth-distinctness` — PD `04-memory.tex:784-966`; the conclusion is
`mem:moment-bound`. -/
theorem birth_distinctness
    (δ C q_d : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hq₀ : 0 < q_d) (hq₁ : q_d < 1) :
    ∀ E₀ : ℝ, 0 < E₀ →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
        ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧
            ∀ x : ℝ, x₀ ≤ x →
              ∀ U V : ℝ, Real.rpow x δ ≤ U → Real.rpow x δ ≤ V →
                x / 4 ≤ U * V → U * V ≤ 2 * x →
                ∀ M : MemoryModel x K a q_d,
                  memoryMoment M (momentR x) / (U * V) ≤
                    Real.rpow (Real.log x) (-E₀ * (pathLength x : ℝ)) := by
  sorry

/-- `t2:pd.strip-goodness-pads` — PD `04-memory.tex:968-1117`; the replacement-interface
conclusion is uniform in all pad scales. -/
theorem strip_goodness_pads
    (δ C q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧
        ∀ family : CoefficientFamily δ C c₁ c₂,
          HasLongCoefficientCancellation family →
          ∀ eta psi : ℝ → ℝ, IsDyadicPartition eta →
            ContDiff ℝ ⊤ psi → HasCompactSupport psi →
            (∀ t ∈ Set.Icc (-4) 4, psi t = 1) →
              ∀ A₀ : ℝ, 0 < A₀ →
              ∀ x : ℝ, x₀ ≤ x →
                ∀ beta : ℕ → ℂ,
                  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers (family.Hn x),
                    ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                  ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                    ∀ Y, Y ∈ dyadicScales x K →
                      ‖(cauchySquare x K a Y family beta eta : ℂ) -
                        majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                        C_A * (family.Hm x * family.Hn x) * Y *
                          Real.rpow (Real.log x) (-A) := by
  sorry

/-- `prop:minor-moment` — PD `04-memory.tex:11-35`, Proposition 4.1. -/
theorem minor_moment
    (δ C q_d : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) :
    ∀ E₀ : ℝ, 0 < E₀ →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
        ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
          ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
            ∀ family : CoefficientFamily δ C c₁ c₂,
              HasLongCoefficientCancellation family →
              ∃ x₀ : ℝ, 2 ≤ x₀ ∧
                ∀ x : ℝ, x₀ ≤ x →
                ∀ M : MemoryModel x K a q_d, ∀ U V : ℝ,
                  Real.rpow x δ ≤ U → Real.rpow x δ ≤ V →
                  x / 4 ≤ U * V → U * V ≤ 2 * x →
                    (memoryMoment M (momentR x) / (U * V) ≤
                      Real.rpow (Real.log x) (-E₀ * (pathLength x : ℝ))) ∧
                    (∀ A : ℝ, 0 < A →
                      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧
                        ∀ x : ℝ, x₀ ≤ x →
                          ∀ beta : ℕ → ℂ,
                            (∀ n, beta n ≠ 0 →
                              n ∈ dyadicIntegers (family.Hn x) ∧
                                roughAbove n (roughCutoff x)) →
                            (∀ n ∈ dyadicIntegers (family.Hn x),
                              ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                            ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                              ∀ eta psi : ℝ → ℝ, IsDyadicPartition eta →
                                ContDiff ℝ ⊤ psi → HasCompactSupport psi →
                                (∀ t ∈ Set.Icc (-4) 4, psi t = 1) →
                                ∀ Y, Y ∈ dyadicScales x K →
                                  ‖(cauchySquare x K a Y family beta eta : ℂ) -
                                    majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                                    C_A * U * V * Y * Real.rpow (Real.log x) (-A)) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PD
