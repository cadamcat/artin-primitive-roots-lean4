import ArtinPrimitiveRoots.Spec.EisensteinExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.All
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.Equivariance
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.RadialTransform
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.EisensteinInterchange
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SeedProperties
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.ContinuationBasics
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SmoothingSeedAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Smoothing and pointwise continuation nodes S1--S4. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

open ArtinPrimitiveRoots.Proofs.spec_continue_p

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
  obtain ⟨k₀, hkSmooth, hkNonneg, hkSupport, hkNonzero⟩ := radialKernel_bump
  refine ⟨k₀, hkSmooth, hkNonneg, hkSupport, hkNonzero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothing_isometry_equivariant k₀
  · intro f hf γ hγ z
    let g : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F γ)
    have hact (x : X F) : actAtPlaces F g x = (γ : SL(2,𝓞 F)) • x := rfl
    have hinv : (fun x => f (actAtPlaces F g x)) = f := by
      funext x
      rw [hact]
      exact hf γ hγ x
    have heq := smoothing_isometry_equivariant k₀ g f z
    rw [hinv] at heq
    simpa only [hact] using heq.symm
  · intro K hK hKpos n v
    obtain ⟨W, C, T, _, _, _, hT⟩ :=
      smoothing_uniform_eval_bound Γ D hD k₀ hkSmooth hkSupport K hK hKpos n v
    exact ⟨T, hT⟩
  · exact smoothing_smooth_representative Γ D hD k₀ hkSmooth hkSupport
  · exact smoothing_toLp Γ D hD k₀ hkSmooth hkSupport
  · intro u v huv z
    exact congrArg (fun t => smoothingOperator F k₀ (l2Lift F Γ D t) z) huv

/-- S2 `spec:Lk-seed` — P-SPEC.md:245, 411–415. Radial powers are eigenfunctions of the
smoothing kernel, the one-factor transform is entire and nonvanishing in the required ball, and
the operator commutes with the Eisenstein series in its convergence region. Correction from review
lane `rev-spec`: require the smooth, nonnegative, supported, nonzero kernel hypotheses from S1. -/
theorem S2_smoothing_seed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (hkNonneg : ∀ t, 0 ≤ k₀ t)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (hkNonzero : ∃ t, k₀ t ≠ 0) :
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g a z
    calc
      smoothingOperator F k₀
          (fun w => ((normHeight F (actAtPlaces F g w) : ℝ) : ℂ) ^ a) z =
          smoothingOperator F k₀
            (fun w => ((normHeight F w : ℝ) : ℂ) ^ a) (actAtPlaces F g z) :=
          smoothing_isometry_equivariant_of_Geometry k₀ g
            (fun w => ((normHeight F w : ℝ) : ℂ) ^ a) z
      _ = radialTransform F k₀ a *
          ((normHeight F (actAtPlaces F g z) : ℝ) : ℂ) ^ a :=
          smoothing_radial_power k₀ a _
  · rw [Complex.analyticOnNhd_univ_iff_differentiable]
    intro a
    exact radialTransform₀_differentiableAt F k₀ hkSmooth hkSupport a
  · intro s hs
    exact radialTransform₀_realPart_pos F k₀ hkSmooth hkNonneg hkSupport hkNonzero s hs
  · intro s hs z
    exact smoothing_eisSeries_interchange Γ σ k₀ hkSmooth hkSupport s hs z

/-- The unsmoothed equality on the original convergence ball, needed to identify the continuation
with the Eisenstein series before applying the smoothing operator. -/
def S3_unsmoothed_base (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (D : Set (X F)) (τ : ℝ → ℝ) (u : ℂ → L2Space F D) : Prop :=
  ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ᵐ z ∂(volX F),
    eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z = eisSeries F Γ σ s z

private theorem s3_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

/-- S3 `spec:econt` — P-SPEC.md:246, 417–420. The smoothed resolvent correction gives a
pointwise continuation with the same convergence values and residue as the `L²` continuation.
Correction from review lane `rev-spec`: supply kernel data and cusp separation, and require the
transform to be nonzero at the residue center. Correction from `sol-gate-spec`: require the
unsmoothed base identity on the convergence ball.  On 2026-10-07 `hu` was weakened from radius `1` to the returned radius `ε` (the Eisenstein pole at `1/2` made the radius-one input unsatisfiable for small `s₁`; lane `sol-gate-spec2`). -/
theorem S3_continuation (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ)
    (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1 / 2)
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ τ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (A : ℝ) (hA : 0 < A) (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ)
    (u : ℂ → L2Space F D)
    (θ : L2Space F D) (ε : ℝ) (hε : 0 < ε ∧ ε ≤ s₁)
    (hu : AnalyticOnNhd ℂ u (contDomain s₁ ε))
    (hhat : ∀ s ∈ contDomain s₁ ε, radialTransform F k₀ (1 + 2 * s) ≠ 0)
    (hhatCenter : radialTransform F k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0)
    (hres : ∃ Ψ : ℂ → L2Space F D,
      AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s)
    (hbase : S3_unsmoothed_base Γ σ D τ u)
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
  let hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hseed (s : ℂ) : IsSmoothX F (eisSeed F Γ σ τ s) := (hseedData.1 s).1
  have hseedInv (s : ℂ) : IsGammaInvariant F Γ (eisSeed F Γ σ τ s) := (hseedData.1 s).2
  let E : ℂ → X F → ℂ := pointwiseEisContinuation F Γ σ D k₀ τ u
  let r : X F → ℂ := fun z => (radialTransform F k₀ (1 + 2 * s₁))⁻¹ *
    smoothingOperator F k₀ (l2Lift F Γ D θ) z
  have hEseries := pointwiseEisContinuation_series σ D k₀ τ u ε s₁ hhat hseries
  have hEinv := pointwiseEisContinuation_invariant D hD σ k₀ τ u hseedInv
  have hEsmooth := pointwiseEisContinuation_smooth D hD σ k₀ τ hkSmooth hkSupport A hA
    hsep hτ hseed u
  have hresSmooth0 := smoothing_smooth_representative Γ D hD k₀ hkSmooth hkSupport θ
  have hresSmooth : ContDiffOn ℝ ∞ (fun p => r (ptX F p)) (posSet F) := by
    simpa [r, smul_eq_mul] using
      hresSmooth0.const_smul ((radialTransform F k₀ (1 + 2 * s₁))⁻¹)
  have hresInv : IsGammaInvariant F Γ r := by
    intro γ hγ z
    let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F γ)
    have hact (x : X F) : actAtPlaces F gPlaces x = (γ : SL(2,𝓞 F)) • x := rfl
    let f : X F → ℂ := l2Lift F Γ D θ
    have hinv : (fun x => f (actAtPlaces F gPlaces x)) = f := by
      funext x
      rw [hact]
      exact (T1_l2 Γ D hD).1 θ |>.2 γ hγ x
    have hcov := smoothing_isometry_equivariant_of_Geometry k₀ gPlaces f z
    have hsm : smoothingOperator F k₀ f ((γ : SL(2,𝓞 F)) • z) =
        smoothingOperator F k₀ f z := by
      rw [hinv, hact z] at hcov
      exact hcov.symm
    simpa [r] using congrArg
      (fun x => (radialTransform F k₀ (1 + 2 * s₁))⁻¹ * x) hsm
  refine ⟨{
    ε := ε
    ε_pos := hε.1
    ε_le := hε.2
    E := E
    E_series := ?_
    E_invariant := ?_
    E_smooth := ?_
    E_analytic := ?_
    res := r
    laurent := ?_
    res_smooth := hresSmooth
    res_invariant := hresInv
    res_eigen := ?_
    res_sq := ?_
  }, rfl, rfl, rfl, ?_⟩
  · exact hEseries
  · intro s hs
    exact hEinv s
  · intro s hs
    exact hEsmooth s
  · intro K hK hKpos n v
    exact pointwiseEisContinuation_derivative_analytic Γ D hD σ τ A hA hsep hτ
      k₀ hkSmooth hkSupport K hK hKpos u (contDomain s₁ ε) hu hhat n v
  · obtain ⟨Ψu, hΨu, hΨuCenter, hΨurel⟩ := hres
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
          hresSmooth0.contDiffAt (s3_posSet_open.mem_nhds (hKpos p.2))
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
          hsmSmooth.contDiffAt (s3_posSet_open.mem_nhds hpPos)
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
  · sorry
  · sorry
  · sorry

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
