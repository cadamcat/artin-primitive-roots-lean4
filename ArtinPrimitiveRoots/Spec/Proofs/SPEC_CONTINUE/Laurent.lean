import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SmoothingSeedAnalytic

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

open ArtinPrimitiveRoots.A1.Spec
open ArtinPrimitiveRoots.Proofs.spec_continue_p

namespace ArtinPrimitiveRoots.Proofs.spec_cont_sol

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem laurent_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

/-- The supplied L² Laurent numerator gives a locally uniform numerator for every
coordinate derivative of the smoothed pointwise continuation, on the same residue ball. -/
theorem pointwiseEisContinuation_laurent (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (u : ℂ → L2Space F D) (θ : L2Space F D) (s₁ ε : ℝ)
    (hhat : ∀ s ∈ contDomain s₁ ε, radialTransform F k₀ (1 + 2 * s) ≠ 0)
    (hhatCenter : radialTransform F k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0)
    (hres : ∃ Ψ : ℂ → L2Space F D,
      AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s) :
    ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ (n : ℕ) (v : Fin n → Coord F),
      ∃ Ψ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧
        (∀ p : K, Ψ s₁ p = iteratedFDeriv ℝ n
          (fun q => (radialTransform F k₀ (1 + 2 * (s₁ : ℂ)))⁻¹ *
            smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 v) ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → ∀ p : K,
          Ψ s p = (s - s₁) * iteratedFDeriv ℝ n
            (fun q => pointwiseEisContinuation F Γ σ D k₀ τ u s (ptX F q)) p.1 v := by
  have hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hseed (s : ℂ) : IsSmoothX F (eisSeed F Γ σ τ s) := (hseedData.1 s).1
  let E : ℂ → X F → ℂ := pointwiseEisContinuation F Γ σ D k₀ τ u
  let r : X F → ℂ := fun z => (radialTransform F k₀ (1 + 2 * (s₁ : ℂ)))⁻¹ *
    smoothingOperator F k₀ (l2Lift F Γ D θ) z
  obtain ⟨Ψu, hΨu, hΨuCenter, hΨurel⟩ := hres
  intro K hK hKpos n v
  obtain ⟨Φseed, T, hΦseed, hΦseedval, hT, hAdd⟩ :=
    smoothingSeedLift_derivative_data Γ D hD σ τ A hA hsep hτ k₀ hkSmooth hkSupport
      K hK hKpos n v
  let B : Set ℂ := Metric.ball (s₁ : ℂ) ε
  have hhatBall : ∀ s ∈ B, radialTransform F k₀ (1 + 2 * s) ≠ 0 := by
    intro s hs
    by_cases hcenter : s = (s₁ : ℂ)
    · subst s
      exact hhatCenter
    · apply hhat s
      have hnotSingleton : s ∉ ({(s₁ : ℂ)} : Set ℂ) := by simpa using hcenter
      change s ∈ contDomain s₁ ε
      simp only [contDomain, Set.mem_union]
      exact Or.inr ⟨hs, hnotSingleton⟩
  have hR : AnalyticOnNhd ℂ
      (fun s : ℂ => radialTransform F k₀ (1 + 2 * s)) B :=
    (radialTransformParam_analytic k₀ hkSmooth hkSupport).mono (by
      intro s hs
      exact Set.mem_univ _)
  have hRinv : AnalyticOnNhd ℂ
      (fun s : ℂ => (radialTransform F k₀ (1 + 2 * s))⁻¹) B := by
    apply hR.inv
    exact hhatBall
  have hseedB : AnalyticOnNhd ℂ Φseed B := hΦseed.mono (Set.subset_univ B)
  have hlin : AnalyticOnNhd ℂ (fun s : ℂ => (s - (s₁ : ℂ))) B := by
    fun_prop
  have hseedTerm : AnalyticOnNhd ℂ
      (fun s => (s - (s₁ : ℂ)) • Φseed s) B := hlin.smul hseedB
  have hliftTerm : AnalyticOnNhd ℂ (fun s => T (Ψu s)) B :=
    T.comp_analyticOnNhd hΨu
  let Ψ : ℂ → (K →ᵇ ℂ) := fun s => (radialTransform F k₀ (1 + 2 * s))⁻¹ •
    ((s - (s₁ : ℂ)) • Φseed s + T (Ψu s))
  have hΨ : AnalyticOnNhd ℂ Ψ B := by
    simpa [Ψ] using hRinv.smul (hseedTerm.add hliftTerm)
  refine ⟨Ψ, hΨ, ?_, ?_⟩
  · intro p
    have hresSmooth0 := smoothing_smooth_representative Γ D hD k₀ hkSmooth hkSupport θ
    have hresAt : ContDiffAt ℝ n
        (fun q => smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 := by
      have hc : ContDiffAt ℝ ∞
          (fun q => smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 :=
        hresSmooth0.contDiffAt (laurent_posSet_open.mem_nhds (hKpos p.2))
      exact hc.of_le (by simp)
    let c₁ : ℂ := (radialTransform F k₀ (1 + 2 * (s₁ : ℂ)))⁻¹
    have hresfun : (fun q => r (ptX F q)) =
        fun q => c₁ • smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q) := by
      funext q
      simp [r, c₁, smul_eq_mul]
    have hder := iteratedFDeriv_const_smul_apply'
      (𝕜 := ℝ) (i := n) (a := c₁)
      (f := fun q => smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q))
      (x := p.1) hresAt
    have hderV : iteratedFDeriv ℝ n
        (fun q => c₁ • smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 v =
        c₁ * iteratedFDeriv ℝ n
          (fun q => smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 v := by
      simpa [smul_eq_mul] using congrArg (fun D => D v) hder
    calc
      Ψ (s₁ : ℂ) p = c₁ * T θ p := by
        simp [Ψ, c₁, hΨuCenter, smul_eq_mul]
      _ = iteratedFDeriv ℝ n (fun q => r (ptX F q)) p.1 v := by
        calc
          c₁ * T θ p = c₁ * iteratedFDeriv ℝ n
              (fun q => smoothingOperator F k₀ (l2Lift F Γ D θ) (ptX F q)) p.1 v := by
            rw [hT θ p]
          _ = iteratedFDeriv ℝ n
              (fun q => c₁ • smoothingOperator F k₀
                (l2Lift F Γ D θ) (ptX F q)) p.1 v := hderV.symm
          _ = iteratedFDeriv ℝ n (fun q => r (ptX F q)) p.1 v := by
            rw [← hresfun]
  · intro s hs hsne p
    have hdom : s ∈ contDomain s₁ ε := by
      change s ∈ contDomain s₁ ε
      simp only [contDomain, Set.mem_union]
      exact Or.inr ⟨hs, by simpa using hsne⟩
    have hpPos : p.1 ∈ posSet F := hKpos p.2
    have hsmSmooth := smoothing_seed_add_lift_isSmooth Γ D hD σ k₀ τ hkSmooth hkSupport
      A hA hsep hτ hseed (u s) s
    have hsmAt : ContDiffAt ℝ n
        (fun q => smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 := by
      have hc : ContDiffAt ℝ ∞
          (fun q => smoothingOperator F k₀
            (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 :=
        hsmSmooth.contDiffAt (laurent_posSet_open.mem_nhds hpPos)
      exact hc.of_le (by simp)
    have hEfun : (fun q => E s (ptX F q)) =
        fun q => (radialTransform F k₀ (1 + 2 * s))⁻¹ •
          smoothingOperator F k₀
            (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q) := by
      funext q
      simp [E, pointwiseEisContinuation, smul_eq_mul]
    have hEder : iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p.1 v =
        (radialTransform F k₀ (1 + 2 * s))⁻¹ *
          iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀
              (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v := by
      rw [hEfun]
      have hder := iteratedFDeriv_const_smul_apply'
        (𝕜 := ℝ) (i := n) (a := (radialTransform F k₀ (1 + 2 * s))⁻¹)
        (f := fun q => smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q))
        (x := p.1) hsmAt
      simpa [smul_eq_mul] using congrArg (fun D => D v) hder
    have hTrel : T (Ψu s) p = (s - (s₁ : ℂ)) * T (u s) p := by
      calc
        T (Ψu s) p = T ((s - (s₁ : ℂ)) • u s) p := by rw [hΨurel s hs hsne]
        _ = ((s - (s₁ : ℂ)) • T (u s)) p := by simp
        _ = (s - (s₁ : ℂ)) * T (u s) p := by simp [smul_eq_mul]
    calc
      Ψ s p = (radialTransform F k₀ (1 + 2 * s))⁻¹ *
          ((s - (s₁ : ℂ)) * Φseed s p + T (Ψu s) p) := by
        simp [Ψ, smul_eq_mul, mul_add]
      _ = (s - (s₁ : ℂ)) *
          ((radialTransform F k₀ (1 + 2 * s))⁻¹ *
            (Φseed s p + T (u s) p)) := by
        rw [hTrel]
        ring
      _ = (s - (s₁ : ℂ)) *
          ((radialTransform F k₀ (1 + 2 * s))⁻¹ *
            iteratedFDeriv ℝ n
              (fun q => smoothingOperator F k₀
                (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v) := by
        rw [← hAdd s (u s) p]
      _ = (s - (s₁ : ℂ)) * iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p.1 v := by
        rw [← hEder]

end ArtinPrimitiveRoots.Proofs.spec_cont_sol
