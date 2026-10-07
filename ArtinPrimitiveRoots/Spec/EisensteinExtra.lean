import ArtinPrimitiveRoots.Spec.Energy

/-! Remaining Eisenstein and resolvent nodes E3--E7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- E3 `spec:eis-smooth` — P-SPEC.md:239, 385–388. In the convergence region, the series is
smooth with normally convergent coordinate derivatives and is an eigenfunction of every partial
Laplacian. -/
theorem E3_eis_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) :
    IsSmoothX F (eisSeries F Γ σ s) ∧
    (∀ w z, partialLap F w (eisSeries F Γ σ s) z =
      (1 - 4 * s ^ 2) * eisSeries F Γ σ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
          ∀ q, ∀ p, p ∈ K →
            ‖iteratedFDeriv ℝ n
              (fun p => eisTerm F Γ σ s (ptX F p) q) p v‖ ≤ m q) := by
  sorry

/-- E4 `spec:eis-siegel` — P-SPEC.md:240, 390–395. On each Siegel set there is at most one
upper-triangular seed coset; the remaining terms and their gradients are uniformly summable on
compact parameter sets in `2 < Re s < 3`. -/
theorem E4_eis_siegel (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F))
    (Kₛ : Set ℂ) (hKₛ : IsCompact Kₛ)
    (hKₛstrip : Kₛ ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3}) :
    ∀ i : d.ι,
      (∀ q q' : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F → q = q') ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
        (∑' q' : {q : CuspCosets F Γ σ //
          σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F},
          (‖eisTerm F Γ σ s ((d.σ i) • z) q'.1‖ +
            ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q'.1) z‖)) ≤ C) ∧
      (∀ q : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
          ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧
          eisTerm F Γ σ s ((d.σ i) • z) q =
            ((absUnitNorm F ε : ℝ) : ℂ) ^ (-(1 + 2 * s)) *
              ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  sorry

/-- E5 `spec:seed` — P-SPEC.md:241, 131–133. The truncated seed and its defect are locally finite,
smooth and invariant; the defect is compactly supported modulo `Γ`, entire as an `L²` family, and
has the explicit height-only formula in the active cusp. -/
theorem E5_seed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∀ s z,
      {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0}.Finite ∧
      (Nat.card {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0} ≤ 1)) ∧
    (∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
      ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
        spectralParameter F s * eisSeed F Γ σ τ s z = eisSeedDefect F Γ σ τ s z) ∧
    (∃ K : Set (X F), IsCompact K ∧ ∀ s,
      {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ orbitSaturation F Γ K) ∧
    (∃ G : ℂ → L2Space F D, AnalyticOnNhd ℂ G Set.univ ∧
      ∀ s, ∀ᵐ z ∂(volX F), z ∈ D → G s z = eisSeedDefect F Γ σ τ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
          ∀ s p, Φ s p = iteratedFDeriv ℝ n
            (fun q => eisSeed F Γ σ τ s (ptX F q)) p v) ∧
    (∀ s z, z ∈ cuspTail F Γ σ A₀ →
      ∃ γ : Γ,
        eisSeedDefect F Γ σ τ s z =
          -(placeCount F : ℂ) *
            (((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ 2 *
                deriv (deriv (fun t : ℝ => (τ t : ℂ)))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) +
              (1 + 4 * s) *
                ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) *
                deriv (fun t : ℝ => (τ t : ℂ))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) ) *
            ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  sorry

/-- E6 `spec:identify` — P-SPEC.md:242, 397–400. On the convergence ball, the series minus its
cutoff seed is bounded with bounded gradient, lies in the energy graph, and solves the weak
resolvent equation with source equal to the negative seed defect. -/
theorem E6_identify (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext (T := testSubmodule F Γ) E)
    (gL2 : L2Space F D)
    (hg : ∀ᵐ z ∂(volX F), z ∈ D →
      gL2 z = eisSeedDefect F Γ σ τ s z) :
    let w := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖w z‖ ≤ B ∧ ‖fullGradient F w z‖ ≤ B) ∧
    (∃ x : E.V, (∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z) ∧
      (∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z) ∧
      E.M x = faResolvent E (spectralParameter F s) (-gL2)) := by
  sorry

/-- E7 `spec:l2-cont` — P-SPEC.md:243, 402–404. The correction is analytic on the connected
continuation domain and has a simple pole at `s₁` with the stated projected-resolvent residue. -/
theorem E7_l2_cont (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (s₁ : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1 / 2)
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (G : ℂ → L2Space F D) (hG : AnalyticOnNhd ℂ G Set.univ)
    (τ : ℝ → ℝ) (lam₁ : ℝ)
    (hLam1 : lam₁ = placeCount F * (1 - 4 * s₁ ^ 2))
    (P : E.V →L[ℂ] E.V) (N : Submodule ℂ E.V)
    (hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P ∧
      N = (E.A (lam₁ : ℂ)).toLinearMap.ker)
    (κ : ℝ) (hκ : κ = (lam₁ + 1) / (8 * placeCount F * s₁)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s₁ ∧
      let u : ℂ → L2Space F D := fun s =>
        faResolvent E (spectralParameter F s) (-G s)
      let θ : L2Space F D := -κ • (E.M.comp (P.comp E.M.adjoint)) (G (s₁ : ℂ))
      AnalyticOnNhd ℂ u (contDomain s₁ ε) ∧
      (∃ Ψ : ℂ → L2Space F D,
        AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s) ∧
      ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
        ∀ᵐ z ∂(volX F), z ∈ D →
          l2Lift F Γ D (u s) z =
            eisSeries F Γ σ s z - eisSeed F Γ σ τ s z := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
