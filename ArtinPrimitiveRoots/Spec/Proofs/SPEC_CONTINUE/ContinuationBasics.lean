import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SeedProperties
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.Equivariance

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

open ArtinPrimitiveRoots.A1.Spec

namespace ArtinPrimitiveRoots.Proofs.spec_continue_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

theorem pointwiseEisContinuation_series {Γ : Subgroup SL(2,𝓞 F)}
    (σ : SL(2,F)) (D : Set (X F)) (k₀ τ : ℝ → ℝ)
    (u : ℂ → L2Space F D) (ε s₁ : ℝ)
    (hhat : ∀ s ∈ contDomain s₁ ε, radialTransform F k₀ (1 + 2 * s) ≠ 0)
    (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
        radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z) :
    ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      pointwiseEisContinuation F Γ σ D k₀ τ u s z = eisSeries F Γ σ s z := by
  intro s hs z
  have hdom : s ∈ contDomain s₁ ε := by
    simp only [contDomain, Set.mem_union]
    exact Or.inl (Or.inr hs)
  have hnonzero := hhat s hdom
  unfold pointwiseEisContinuation
  rw [hseries s hs z]
  field_simp [hnonzero]

theorem pointwiseEisContinuation_invariant {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (k₀ τ : ℝ → ℝ) (u : ℂ → L2Space F D)
    (hseedInv : ∀ s, ∀ γ ∈ Γ, ∀ z,
      eisSeed F Γ σ τ s (γ • z) = eisSeed F Γ σ τ s z) :
    ∀ s, ∀ γ ∈ Γ, ∀ z,
      pointwiseEisContinuation F Γ σ D k₀ τ u s (γ • z) =
        pointwiseEisContinuation F Γ σ D k₀ τ u s z := by
  intro s γ hγ z
  let g : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F γ)
  have hact (x : X F) : actAtPlaces F g x = γ • x := rfl
  let f : X F → ℂ := fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w
  have hinv : (fun x => f (actAtPlaces F g x)) = f := by
    funext x
    rw [hact]
    simp only [f]
    rw [hseedInv s γ hγ x, (T1_l2 Γ D hD).1 (u s) |>.2 γ hγ x]
  have hcov := smoothing_isometry_equivariant_of_Geometry k₀ g f z
  have hsmoothed : smoothingOperator F k₀ f (γ • z) = smoothingOperator F k₀ f z := by
    have h := hcov
    rw [hinv, hact z] at h
    exact h.symm
  unfold pointwiseEisContinuation
  rw [hsmoothed]

theorem pointwiseEisContinuation_smooth {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F))
    (k₀ τ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s))
    (u : ℂ → L2Space F D) (s : ℂ) :
    ContDiffOn ℝ ∞
      (fun p => pointwiseEisContinuation F Γ σ D k₀ τ u s (ptX F p)) (posSet F) := by
  have hsmooth := smoothing_seed_add_lift_isSmooth Γ D hD σ k₀ τ hkSmooth hkSupport
    A hA hsep hτ hseed (u s) s
  change ContDiffOn ℝ ∞
    (fun p => (radialTransform F k₀ (1 + 2 * s))⁻¹ *
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F p))
      (posSet F)
  simpa [smul_eq_mul] using
    hsmooth.const_smul ((radialTransform F k₀ (1 + 2 * s))⁻¹)

end ArtinPrimitiveRoots.Proofs.spec_continue_p
