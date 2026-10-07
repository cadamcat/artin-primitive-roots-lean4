import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PP.Results

/-! The rough-factor Type II estimate and its coefficient (`08-type-ii.tex:321-536`). -/

namespace ArtinPrimitiveRoots.TypeII.Rough

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII.PP

/-- `def:rough-density` — 08-type-ii.tex:253-270. Alias of the shared Buchstab rough density; the
body is exactly the existing `ArtinPrimitiveRoots.Sieve.roughDensity` definition. -/
noncomputable abbrev roughDensity := ArtinPrimitiveRoots.Sieve.roughDensity

/-- The coefficient in equation `eq:rough-type-ii-coefficient`. -/
noncomputable def roughCoefficient (x γ v : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
    (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
        roughDensity γ (Real.log (m : ℝ) / Real.log x) /
          (Real.log x * roughSieveProduct (roughCutoff x)) *
            (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)

/-- The prime-indicator coefficient `1_{P⁻(m)>x^γ}`. -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ :=
  if roughAbove m (Real.rpow x γ) then 1 else 0

/-- The proxy coefficient `D_γ(log m/log x)/(log x V(W))` on `W`-rough integers. -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ :=
  roughDensity γ (Real.log (m : ℝ) / Real.log x) /
    (Real.log x * roughSieveProduct (roughCutoff x)) *
      if roughAbove m (roughCutoff x) then 1 else 0

/-- The finite ordered-prime convolution `T_γ(m)` from `eq:rough-convolution-square-error`. -/
noncomputable def roughConvolutionTerm (x γ M : ℝ) (j m : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
      if (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m then 1 else 0

noncomputable def roughConvolution (x γ wMax M : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M j m

/-- Prime set in a closed real interval, explicitly truncated at the upper endpoint. -/
noncomputable def primesInInterval (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun p => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi

/-- Product-measure integral over ordered `j`-tuples of primes in logarithmic coordinates. -/
noncomputable def roughTupleIntegral (x γ lo hi : ℝ) (j : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∫ t : Fin j → ℝ,
      if (∀ i, Real.rpow x γ < t i) ∧
          lo ≤ ∏ i : Fin j, t i ∧ (∏ i : Fin j, t i) ≤ hi then
        ∏ i : Fin j, 1 / Real.log (t i) else 0

/-- `prop:rough-type-ii` — `08-type-ii.tex:321-536`. Fix the parameters in the
paper. Uniformly over admissible dyads, intervals, real twists, rough second-variable coefficients,
and marked-invariant multipliers, the coefficient `roughCoefficient` has the Type II saving once
`K` is sufficiently large. -/
theorem rough_type_ii
    (γ wMin wMax δ C Dstar q_d c₁ c₂ : ℝ)
    (hγ : 0 < γ) (hγwMin : γ < wMin) (hwMinMax : wMin < wMax)
    (hwMax : wMax < 1)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ a : Fin K → ℝ, ValidBands K a →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
              ∀ I : Set ℕ, I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ v : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                  ∀ beta : ℕ → ℂ,
                    (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                      roughAbove n (roughCutoff x)) →
                    (∀ n ∈ dyadicIntegers Hn,
                      ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                    ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                      ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                        ∑ n ∈ dyadicIntegers Hn,
                          roughCoefficient x γ v m * beta n * F (m * n - 1) *
                            (markedWeight x K a q_d (m * n - 1) : ℂ)‖ ≤
                        C' * (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by
  sorry

/-- `t2:square-error` — 08-type-ii.tex:351-371. -/
theorem square_error (γ wMax δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hγw : γ < wMax) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 1 ≤ M → Real.rpow x δ ≤ M →
          let Jγ := ⌊wMax / γ⌋₊
          (∑ m ∈ dyadicIntegers M,
            |roughIndicator x γ m - roughConvolution x γ wMax M m|) ≤
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊) ∧
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ C * M * Real.rpow x (-γ) := by
  sorry

/-- `t2:sw-slot` — 08-type-ii.tex:385-407, `eq:rough-slot-siegel-walfisz`. -/
theorem sw_slot (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₂ : ℝ, 0 < A₀ → 0 < A₂ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                P ≤ l → l ≤ r → r ≤ 2 * P →
                  ‖∑ p ∈ (primesInInterval l r),
                    (χ (p : ZMod k) : ℂ) -
                    (if χ = 1 then (1 : ℂ) else 0) *
                      (∫ y in l..r, (1 / Real.log y : ℝ) : ℂ)‖ ≤
                    C * P * Real.rpow (Real.log x) (-A₂) := by
  sorry

/-- `t2:density-pushforward` — 08-type-ii.tex:272-294. -/
theorem density_pushforward (γ : ℝ) (hγ : 0 < γ) :
    ∀ x : ℝ, 2 ≤ x → ∀ j : ℕ, 1 ≤ j → ∀ l r : ℝ,
      Real.rpow x γ < l → l ≤ r →
        roughTupleIntegral x γ l r j =
          (1 / Real.log x) *
            ∫ y in l..r,
              ArtinPrimitiveRoots.Sieve.roughDensityTerm γ
                (Real.log y / Real.log x) j := by
  sorry

/-- `t2:density-regularity` — 08-type-ii.tex:296-315. Joint continuity, local Lipschitz
continuity in the second variable, and bounded variation of `w D_γ(w)`. -/
theorem density_regularity :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, w₀ ≤ u → u ≤ w₁ → w₀ ≤ v → v ≤ w₁ →
        |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤ C * |u - v|) ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      BoundedVariationOn (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w)
        (Set.uIcc w₀ w₁)) := by
  sorry

/-- `t2:low-count` — 08-type-ii.tex:373-427, `eq:rough-convolution-low-count`. -/
theorem low_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                M ≤ l → l ≤ r → r ≤ 2 * M →
                  ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                      (roughIndicator x γ m : ℂ) * χ (m : ZMod k)) -
                    (if χ = 1 then
                      ((1 / Real.log x) *
                        ∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity γ
                          (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
                    C * M * Real.rpow (Real.log x) (-A₁) := by
  sorry

/-- `t2:low-frequency` — 08-type-ii.tex:439-453. -/
theorem low_frequency (γ wMin wMax C δ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax) (hδ : 0 < δ)
    (hC : 0 < C) :
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          roughCoefficient x γ v m * χ (m : ZMod k) *
                            Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:prime-high` — 08-type-ii.tex:455-480. -/
theorem prime_high (γ wMax : ℝ) (hγ : 0 < γ) (hw : wMax < 1) :
    ∀ τ θ A₀ A₃ : ℝ, 0 < τ → τ < γ → wMax < θ → θ < 1 →
      0 < A₀ → 0 < A₃ →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x τ / 2 ≤ M → M ≤ Real.rpow x θ →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ u : ℝ,
                Real.rpow (Real.log x) B₀ ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
                          Complex.exp (Complex.I * u * Real.log (m : ℝ)))‖ ≤
                      C₀ * M * Real.rpow (Real.log x) (-A₃) := by
  sorry

/-- `t2:proxy-high` — 08-type-ii.tex:482-516; the source estimate is also the proof of PD
Lemma 5.2 (`05-major-arcs.tex:57-125`). -/
theorem proxy_high :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ δ γ wMin wMax : ℝ, 0 < δ → 0 < γ → γ < wMin → wMin < wMax → wMax < 1 →
        ∀ A₀ : ℝ, 0 < A₀ →
          ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
            ∀ A₄ : ℝ, 0 < A₄ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
              ∀ x : ℝ, x₀ ≤ x →
              let L := Real.log x
              let Tstar := Real.exp (L / Real.log L ^ 2)
              ∀ M : ℝ, Real.rpow x δ ≤ M →
                Real.log M / L ∈ Set.Icc wMin wMax →
                Real.log (2 * M) / L ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
                  ∀ χ : DirichletCharacter ℂ k, ∀ l r u : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M → 1 ≤ |u| → |u| < Real.rpow x 2 →
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                            Real.log (m : ℝ)) /
                        (M * roughSieveProduct (roughCutoff x))‖ ≤
                      Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) ∧
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                            roughProxy x γ m) / M‖ ≤
                        Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) := by
  sorry

/-- `t2:high-frequency` — 08-type-ii.tex:513-527. -/
theorem high_frequency
    (γ wMin wMax δ C A : ℝ) (hγ : 0 < γ) (hγw : γ < wMin)
    (hw : wMin < wMax) (hwMax : wMax < 1) (hδ : 0 < δ)
    (hC : 0 < C) (hA : 0 < A) :
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
            x / 2 ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
            Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                  ∀ l r : ℝ, Hm ≤ l → l ≤ r → r ≤ 2 * Hm →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        roughCoefficient x γ v m * χ (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
                      C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

end ArtinPrimitiveRoots.TypeII.Rough
