import ArtinPrimitiveRoots.Spec.EisensteinExtra

/-! Smoothing and pointwise continuation nodes S1--S4. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- S1 `spec:Lk` — P-SPEC.md:244, 406–409. A small compactly supported radial kernel gives
an isometry-equivariant smoothing operator with bounded coordinate derivatives on compact sets. -/
theorem S1_smoothing (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    ∃ k₀ : ℝ → ℝ,
      ContDiff ℝ ∞ k₀ ∧ (∀ t, 0 ≤ k₀ t) ∧
      {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100) ∧
      (∃ t, k₀ t ≠ 0) ∧
      (∀ g : InfinitePlace F → SL(2,ℂ), ∀ f : X F → ℂ, ∀ z,
        smoothingOperator F k₀ (fun x => f (actAtPlaces F g x)) z =
          smoothingOperator F k₀ f (actAtPlaces F g z)) ∧
      (∀ f : X F → ℂ, IsGammaInvariant F Γ f →
        IsGammaInvariant F Γ (smoothingOperator F k₀ f)) ∧
      (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
        ∀ n : ℕ, ∀ v : Fin n → Coord F,
          ∃ T : L2Space F D →L[ℂ] (K →ᵇ ℂ),
            ∀ u p, T u p = iteratedFDeriv ℝ n
              (fun q => smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F q)) p.1 v) ∧
      (∀ u : L2Space F D,
        IsSmoothX F (smoothingOperator F k₀ (l2Lift F Γ D u))) ∧
      (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
        ∃ T : L2Space F D →L[ℂ]
            Lp ℂ 2 ((volX F).restrict (ptX F '' K)),
          ∀ u, ∀ᵐ z ∂(volX F), z ∈ ptX F '' K →
            T u z = smoothingOperator F k₀ (l2Lift F Γ D u) z) ∧
      (∀ u v : L2Space F D, u = v → ∀ z,
        smoothingOperator F k₀ (l2Lift F Γ D u) z =
          smoothingOperator F k₀ (l2Lift F Γ D v) z) := by
  sorry

/-- S2 `spec:Lk-seed` — P-SPEC.md:245, 411–415. Radial powers are eigenfunctions of the
smoothing kernel, the one-factor transform is entire and nonvanishing in the required ball, and
the operator commutes with the Eisenstein series in its convergence region. -/
theorem S2_smoothing_seed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (k₀ : ℝ → ℝ) :
    (∀ g : InfinitePlace F → SL(2,ℂ), ∀ a : ℂ, ∀ z : X F,
      smoothingOperator F k₀
        (fun w => ((normHeight F (actAtPlaces F g w) : ℝ) : ℂ) ^ a) z =
          radialTransform F k₀ a *
            ((normHeight F (actAtPlaces F g z) : ℝ) : ℂ) ^ a) ∧
    AnalyticOnNhd ℂ (radialTransform₀ k₀) Set.univ ∧
    (∀ s : ℂ, ‖s‖ ≤ 5 → 0 < (radialTransform₀ k₀ (1 + 2 * s)).re) ∧
    (∀ s : ℂ, 1 / 2 < s.re → ∀ z : X F,
      smoothingOperator F k₀ (eisSeries F Γ σ s) z =
        radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z) := by
  sorry

/-- S3 `spec:econt` — P-SPEC.md:246, 417–420. The smoothed resolvent correction gives a
pointwise continuation with the same convergence values and residue as the `L²` continuation. -/
theorem S3_continuation (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ)
    (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1 / 2)
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A) (hτ : IsCuspCutoff A τ)
    (u : ℂ → L2Space F D) (hu : AnalyticOnNhd ℂ u (contDomain s₁ 1))
    (θ : L2Space F D) (ε : ℝ) (hε : 0 < ε ∧ ε ≤ s₁)
    (hhat : ∀ s ∈ contDomain s₁ ε, radialTransform F k₀ (1 + 2 * s) ≠ 0)
    (hres : ∃ Ψ : ℂ → L2Space F D,
      AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s)
    (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      smoothingOperator F k₀ (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
        radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z) :
    ∃ d : ContinuedEisenstein F Γ σ s₁,
      d.ε = ε ∧
      d.E = pointwiseEisContinuation F Γ σ D k₀ τ u ∧
      d.res = (fun z => (radialTransform F k₀ (1 + 2 * s₁))⁻¹ *
        smoothingOperator F k₀ (l2Lift F Γ D θ) z) ∧
      ∀ s ∈ contDomain s₁ ε, ∀ K : Set (X F), IsCompact K →
        ∀ᵐ z ∂(volX F), z ∈ K →
          smoothingOperator F k₀
            (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
            radialTransform F k₀ (1 + 2 * s) *
              (eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z) := by
  sorry

/-- S4 `spec:res-props` — P-SPEC.md:247, 422–425. The residue is smooth, invariant, square
integrable on every fundamental domain, and an eigenfunction of every partial Laplacian. -/
theorem S4_residue_props {Γ : Subgroup SL(2,𝓞 F)} {σ : SL(2,F)} {s₁ : ℝ}
    (d : ContinuedEisenstein F Γ σ s₁) :
    ContDiffOn ℝ ∞ (fun p => d.res (ptX F p)) (posSet F) ∧
    (∀ γ ∈ Γ, ∀ z, d.res ((γ : SL(2,𝓞 F)) • z) = d.res z) ∧
    (∀ D : Set (X F), IsFundamentalDomain Γ D (volX F) →
      IntegrableOn (fun z => ‖d.res z‖ ^ 2) D (volX F)) ∧
    (∀ w z, partialLap F w d.res z = (1 - 4 * (s₁ : ℂ) ^ 2) * d.res z) := by
  exact ⟨d.res_smooth, d.res_invariant, d.res_sq, d.res_eigen⟩

end ArtinPrimitiveRoots.A1.Spec
