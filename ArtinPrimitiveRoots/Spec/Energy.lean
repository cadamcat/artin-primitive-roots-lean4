import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.SiegelData
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.CuspSums
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.T5Core

/-! L² and energy-space nodes T1--T7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- T1 `spec:l2` — P-SPEC.md:228. The invariant lift, compact-overlap bound, unfolding formula,
and independence of the chosen fundamental domain. -/
theorem T1_l2 (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ u : L2Space F D, AEStronglyMeasurable (l2Lift F Γ D u) (volX F) ∧
      ∀ γ ∈ Γ, ∀ z, l2Lift F Γ D u ((γ : SL(2,𝓞 F)) • z) = l2Lift F Γ D u z) ∧
    (∀ K : Set (X F), IsCompact K →
      Set.Finite (overlapSet F Γ K K) ∧
      ∀ u : L2Space F D,
        ∫ z in K, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) ≤
          (overlapMultiplicity F Γ K : ℝ) * ‖u‖ ^ 2) ∧
    (∀ f : X F → ℂ, Integrable f (volX F) →
      ∫ z in D, (∑' γ : Γ, f ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
        ∫ z, f z ∂(volX F)) ∧
    (∀ D' : Set (X F), IsFundamentalDomain Γ D' (volX F) →
      ∀ f : X F → ℂ, Integrable f (volX F) →
        (∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z) →
        ∫ z in D, f z ∂(volX F) = ∫ z in D', f z ∂(volX F)) := by
  sorry

/-- T2 `spec:tests` — P-SPEC.md:229, 349–352. Test functions form the stated submodule, their
mass and gradient have the quotient representatives, and an automorphic partition of unity is
locally finite and reconstructs each test function. -/
theorem T2_tests (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f) ∧
    ∃ (toL2 : testSubmodule F Γ →ₗ[ℂ] L2Space F D)
      (gradL2 : testSubmodule F Γ →ₗ[ℂ] GradientL2Space F D),
      (∀ f, ∀ᵐ z ∂(volX F), z ∈ D → toL2 f z = (f : X F → ℂ) z) ∧
      (∀ f, ∀ᵐ z ∂(volX F), z ∈ D → gradL2 f z = fullGradient F (f : X F → ℂ) z) ∧
      (∀ K : Set (X F), IsCompact K →
        ∃ ψ : X F → ℝ,
          IsSmoothRealX F ψ ∧ HasCompactSupportX F (fun z => (ψ z : ℂ)) ∧
          (∀ z, 0 ≤ ψ z) ∧
          (∀ z, ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
            {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0}.Finite) ∧
          (∃ U : Set (X F), IsOpen U ∧ orbitSaturation F Γ K ⊆ U ∧
            ∀ z ∈ U, ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1) ∧
          ∀ f ∈ testSubmodule F Γ,
            {z | (f : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ K →
            ∀ z, (f : X F → ℂ) z =
              ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) * (f : X F → ℂ) ((γ : SL(2,𝓞 F)) • z)) := by
  sorry

/-- T3 `spec:green-q` — P-SPEC.md:230, 349–352. Green's identity on a finite-volume
fundamental domain with one test factor and one invariant smooth factor. -/
theorem T3_green_q (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ →
      ∀ g : X F → ℂ, IsGammaInvariant F Γ g → IsSmoothX F g →
      ∀ w : InfinitePlace F,
        ∫ z in D, star (f z) * partialLap F w g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) ∧
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ →
      ∀ g : X F → ℂ, IsGammaInvariant F Γ g → IsSmoothX F g →
      ∀ w : InfinitePlace F,
        ∫ z in D, star (partialLap F w f z) * g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) := by
  sorry

/-- T4 `spec:energy-space` — P-SPEC.md:231. The energy space is the closed graph closure of the
mass and gradient maps; its test graph is dense and its norm splits into the two components.
Correction from `sol-gate-spec`: require the maps' actual quotient-representative calibrations. -/
theorem T4_energy_space (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (toL2 : testSubmodule F Γ →ₗ[ℂ] L2Space F D)
    (gradL2 : testSubmodule F Γ →ₗ[ℂ] GradientL2Space F D)
    (hmass_rep : ∀ f, ∀ᵐ z ∂(volX F), z ∈ D → toL2 f z = (f : X F → ℂ) z)
    (hgradient_rep : ∀ f, ∀ᵐ z ∂(volX F), z ∈ D →
      gradL2 f z = fullGradient F (f : X F → ℂ) z) :
    ∃ E : FAEnergySpace (L2Space F D) (GradientL2Space F D),
      ∃ e : EnergyContext F Γ D E,
        e.toL2 = toL2 ∧ e.gradL2 = gradL2 ∧
        (∀ x : E.V, ‖x‖ ^ 2 = ‖E.M x‖ ^ 2 + ‖E.Gr x‖ ^ 2) := by
  sorry

/-- T5 `spec:cutoff` — P-SPEC.md:232, 354–357. A bounded invariant smooth function with bounded
gradient is represented by an energy vector with those mass and gradient components. Correction
from `sol-gate-spec`: use a context calibrated to the quotient representatives. -/
theorem T5_cutoff (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (f : X F → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hInv : IsGammaInvariant F Γ f) (hSmooth : IsSmoothX F f)
    (hBound : ∀ z, ‖f z‖ ≤ B)
    (hGradBound : ∀ z, ‖fullGradient F f z‖ ≤ B)
    (fL2 : L2Space F D) (grad : GradientL2Space F D)
    (hfL2 : ∀ᵐ z ∂(volX F), z ∈ D → fL2 z = f z)
    (hgrad : ∀ᵐ z ∂(volX F), z ∈ D → grad z = fullGradient F f z) :
    ∃ x : E.V, E.M x = fL2 ∧ E.Gr x = grad := by
  classical
  let d : SiegelData F Γ := Classical.choice (specGap_siegelData_exists Γ)
  obtain ⟨A₀, hA₀, hsepRaw⟩ := (R10_cusp_separation Γ).2.1 d
  have hA₀pos : 0 < A₀ := lt_of_lt_of_le (by norm_num) hA₀
  have hsepBase : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i) := by
    intro i j γ γ' z hi hj
    exact hsepRaw A₀ le_rfl i j γ γ' z hi hj
  have hsepIndex := specGapAllCuspIndex_eq_of_separation d A₀ hsepBase
  let a : ℕ → ℝ := fun n => A₀ + (n : ℝ) + 1
  have hA₀n (n : ℕ) : A₀ ≤ a n := by
    dsimp [a]
    calc
      A₀ ≤ A₀ + (n : ℝ) := le_add_of_nonneg_right (by positivity)
      _ ≤ A₀ + (n : ℝ) + 1 := by linarith
  have hAn (n : ℕ) : 0 < a n := lt_of_lt_of_le hA₀pos (hA₀n n)
  have hsepN (n : ℕ) : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      a n ≤ specGapAllCuspHeight Γ d p z →
      a n ≤ specGapAllCuspHeight Γ d p' z → p = p' := by
    intro p p' z hp hp'
    exact hsepIndex p p' z (le_trans (hA₀n n) hp) (le_trans (hA₀n n) hp')
  obtain ⟨L, hL, hLderiv⟩ := specGapHeightCutoff_deriv_bound_uniform
  let C : ℝ := 2 * L * Real.sqrt (placeCount F)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let ρ : ℕ → X F → ℝ := fun n z => specGapAllCuspRho Γ d (a n) z
  let fn : ℕ → X F → ℂ := fun n z => (ρ n z : ℂ) * f z
  have hρRange (n : ℕ) (z : X F) : 0 ≤ ρ n z ∧ ρ n z ≤ 1 := by
    exact specGapAllCuspRho_bounds d (a n) (hAn n) (hsepN n) z
  have hρSmooth (n : ℕ) : IsSmoothRealX F (ρ n) := by
    exact specGapAllCuspRho_smooth d (a n) (hAn n)
  have hρSmoothC (n : ℕ) : IsSmoothX F (fun x => (ρ n x : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun p => ((ρ n (ptX F p) : ℝ) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hρSmooth n)
  have hρInv (n : ℕ) (γ : Γ) (z : X F) :
      ρ n ((γ : SL(2,𝓞 F)) • z) = ρ n z :=
    specGapAllCuspRho_invariant d (a n) γ z
  have hρGrad (n : ℕ) (z : X F) :
      ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ C := by
    exact specGapAllCuspRho_gradient_bound d (a n) L (hAn n) hL
      (hLderiv (a n) (hAn n)) (hsepN n) z
  have hρSupport (n : ℕ) : ∃ K : Set (X F), IsCompact K ∧
      {z | ρ n z ≠ 0} ⊆ orbitSaturation F Γ K := by
    exact specGapAllCuspRho_support d (a n) (hAn n) (hsepN n)
  have hfnTest (n : ℕ) : IsGammaTest F Γ (fn n) := by
    constructor
    · intro γ hγ z
      simp only [fn]
      rw [hρInv n ⟨γ, hγ⟩ z, hInv γ hγ z]
    constructor
    · change ContDiffOn ℝ ∞
        (fun p => ((ρ n (ptX F p) : ℝ) : ℂ) * f (ptX F p)) (posSet F)
      exact (hρSmoothC n).mul hSmooth
    · rcases hρSupport n with ⟨K, hK, hKsupport⟩
      refine ⟨K, hK, ?_⟩
      intro z hz
      apply hKsupport
      intro hzero
      apply hz
      simp [fn, hzero]
  have hT2 := (T2_tests Γ D hD).1
  have hfnMem (n : ℕ) : fn n ∈ testSubmodule F Γ := (hT2 (fn n)).2 (hfnTest n)
  let t : ℕ → testSubmodule F Γ := fun n => ⟨fn n, hfnMem n⟩
  let μ : Measure (X F) := (volX F).restrict D
  let massErr : ℕ → L2Space F D := fun n => e.toL2 (t n) - fL2
  let gradErr : ℕ → GradientL2Space F D := fun n => e.gradL2 (t n) - grad
  have hfμ : ∀ᵐ z ∂μ, fL2 z = f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hfL2
  have hgradμ : ∀ᵐ z ∂μ, grad z = fullGradient F f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hgrad
  have hmassRepμ (n : ℕ) : ∀ᵐ z ∂μ, e.toL2 (t n) z = fn n z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.mass_rep (t n))
  have hgradRepμ (n : ℕ) : ∀ᵐ z ∂μ, e.gradL2 (t n) z = fullGradient F (fn n) z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.gradient_rep (t n))
  have hmassRepAll : ∀ᵐ z ∂μ, ∀ n : ℕ, e.toL2 (t n) z = fn n z :=
    ae_all_iff.2 hmassRepμ
  have hgradRepAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      e.gradL2 (t n) z = fullGradient F (fn n) z := ae_all_iff.2 hgradRepμ
  have hmassSubμ (n : ℕ) : ∀ᵐ z ∂μ,
      massErr n z = e.toL2 (t n) z - fL2 z := by
    change (fun z => (e.toL2 (t n) - fL2) z) =ᵐ[μ] _
    exact Lp.coeFn_sub (e.toL2 (t n)) fL2
  have hgradSubμ (n : ℕ) : ∀ᵐ z ∂μ,
      gradErr n z = e.gradL2 (t n) z - grad z := by
    change (fun z => (e.gradL2 (t n) - grad) z) =ᵐ[μ] _
    exact Lp.coeFn_sub (e.gradL2 (t n)) grad
  have hmassSubAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      massErr n z = e.toL2 (t n) z - fL2 z := ae_all_iff.2 hmassSubμ
  have hgradSubAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      gradErr n z = e.gradL2 (t n) z - grad z := ae_all_iff.2 hgradSubμ
  have hfSq : Integrable (fun z => ‖fL2 z‖ ^ 2) μ := specGapLpTwo_integrable_norm_sq μ fL2
  have hgradSq : Integrable (fun z => ‖grad z‖ ^ 2) μ := specGapLpTwo_integrable_norm_sq μ grad
  let massDom : X F → ℝ := fun z => 4 * ‖fL2 z‖ ^ 2
  have hmassDomInt : Integrable massDom μ := by
    dsimp [massDom]
    exact hfSq.const_mul 4
  have hmassBound (n : ℕ) : ∀ᵐ z ∂μ,
      ‖massErr n z‖ ^ 2 ≤ massDom z := by
    filter_upwards [hmassRepAll, hmassSubAll, hfμ] with z hrep hsub hfz
    have hr := hρRange n z
    have hnormρ : ‖(ρ n z : ℂ)‖ = ρ n z := by
      calc
        _ = |ρ n z| := RCLike.norm_ofReal _
        _ = ρ n z := abs_of_nonneg hr.1
    have hnorm : ‖massErr n z‖ ≤ 2 * ‖fL2 z‖ := by
      rw [hsub n, hrep n, hfz]
      calc
        ‖(ρ n z : ℂ) * f z - f z‖ ≤ ‖(ρ n z : ℂ) * f z‖ + ‖f z‖ := norm_sub_le _ _
        _ = ‖(ρ n z : ℂ)‖ * ‖f z‖ + ‖f z‖ := by rw [norm_mul]
        _ ≤ 2 * ‖f z‖ := by rw [hnormρ]; nlinarith [hr.2, norm_nonneg (f z)]
    have hsq := (sq_le_sq₀ (norm_nonneg (massErr n z)) (by positivity)).2 hnorm
    dsimp [massDom]
    nlinarith [hsq]
  have hmassPointwise : ∀ᵐ z ∂μ,
      Tendsto (fun n => ‖massErr n z‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hmassRepAll, hmassSubAll, hfμ] with z hrep hsub hfz
    have hzero : ∀ᶠ n : ℕ in atTop, massErr n z = 0 := by
      filter_upwards [specGapAllCuspRho_eventually_one_zero_grad d A₀ hA₀pos z] with n hn
      rw [hsub n, hrep n, hfz]
      simp [fn, ρ, a, hn.1]
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with n hn
    change (0 : ℝ) = ‖massErr n z‖ ^ 2
    rw [hn]
    simp
  have hmassMeas (n : ℕ) : AEStronglyMeasurable (fun z => ‖massErr n z‖ ^ 2) μ :=
    ((Lp.aestronglyMeasurable (massErr n)).norm).pow 2
  have hmassDomAE (n : ℕ) : ∀ᵐ z ∂μ,
      ‖‖massErr n z‖ ^ 2‖ ≤ massDom z := by
    filter_upwards [hmassBound n] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  have hmassIntegral : Tendsto (fun n => ∫ z, ‖massErr n z‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : X F => (0 : ℝ))
      massDom hmassMeas hmassDomInt hmassDomAE hmassPointwise
    simpa using h
  have hmassTendsto : Tendsto massErr atTop (𝓝 0) :=
    specGapLpTwo_tendsto_zero μ massErr hmassIntegral
  let gradDom : X F → ℝ := fun z => 8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2
  have hgradDomInt : Integrable gradDom μ := by
    have h1 : Integrable (fun z => 8 * ‖grad z‖ ^ 2) μ := hgradSq.const_mul 8
    have h2 : Integrable (fun z => 2 * C ^ 2 * ‖fL2 z‖ ^ 2) μ := hfSq.const_mul (2 * C ^ 2)
    change Integrable (fun z => 8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2) μ
    exact h1.add h2
  have hgradBound (n : ℕ) : ∀ᵐ z ∂μ,
      ‖gradErr n z‖ ^ 2 ≤ gradDom z := by
    filter_upwards [hgradRepAll, hgradSubAll, hgradμ, hfμ] with z hrep hsub hgr hzf
    have hr := hρRange n z
    have hnρ : ‖(ρ n z : ℂ)‖ = ρ n z := by
      calc
        _ = |ρ n z| := RCLike.norm_ofReal _
        _ = ρ n z := abs_of_nonneg hr.1
    have hprod : fullGradient F (fn n) z =
        (ρ n z : ℂ) • fullGradient F f z + f z • fullGradient F (fun x => (ρ n x : ℂ)) z := by
      simpa [fn] using fullGradient_mul (fun x => (ρ n x : ℂ)) f (hρSmoothC n) hSmooth z
    have hnorm : ‖gradErr n z‖ ≤ 2 * ‖grad z‖ + C * ‖fL2 z‖ := by
      rw [hsub n, hrep n]
      rw [hprod]
      calc
        ‖((ρ n z : ℂ) • fullGradient F f z +
              f z • fullGradient F (fun x => (ρ n x : ℂ)) z) - grad z‖ ≤
            ‖(ρ n z : ℂ) • fullGradient F f z‖ +
              ‖f z • fullGradient F (fun x => (ρ n x : ℂ)) z‖ +
              ‖grad z‖ := by
                exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ = ‖(ρ n z : ℂ)‖ * ‖fullGradient F f z‖ +
              ‖f z‖ * ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ +
              ‖grad z‖ := by simp [norm_smul]
        _ ≤ 2 * ‖grad z‖ + C * ‖fL2 z‖ := by
              have hgmul : ‖fL2 z‖ *
                  ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ ‖fL2 z‖ * C :=
                mul_le_mul_of_nonneg_left (hρGrad n z) (norm_nonneg (fL2 z))
              have hfmul : ‖f z‖ *
                  ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ ‖f z‖ * C :=
                mul_le_mul_of_nonneg_left (hρGrad n z) (norm_nonneg (f z))
              have hrmul : ρ n z * ‖grad z‖ ≤ ‖grad z‖ := by
                nlinarith [hr.2, norm_nonneg (grad z)]
              have hgrnorm : ‖fullGradient F f z‖ = ‖grad z‖ := by rw [hgr]
              have hfnorm : ‖f z‖ = ‖fL2 z‖ := by rw [← hzf]
              rw [hnρ]
              nlinarith [hgmul, hrmul, hgrnorm, hfnorm, hC,
                norm_nonneg (fL2 z), norm_nonneg (grad z)]
    have hsq := (sq_le_sq₀ (norm_nonneg (gradErr n z)) (by positivity)).2 hnorm
    have hsqAdd : (2 * ‖grad z‖ + C * ‖fL2 z‖) ^ 2 ≤
        8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2 := by
      nlinarith [sq_nonneg (2 * ‖grad z‖ - C * ‖fL2 z‖)]
    dsimp [gradDom]
    exact le_trans hsq hsqAdd
  have hgradPointwise : ∀ᵐ z ∂μ,
      Tendsto (fun n => ‖gradErr n z‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hgradRepAll, hgradSubAll, hgradμ, hfμ] with z hrep hsub hgr hfz
    have hzero : ∀ᶠ n : ℕ in atTop, gradErr n z = 0 := by
      filter_upwards [specGapAllCuspRho_eventually_one_zero_grad d A₀ hA₀pos z] with n hn
      have hprodRule : fullGradient F (fn n) z =
          (ρ n z : ℂ) • fullGradient F f z +
            f z • fullGradient F (fun x => (ρ n x : ℂ)) z := by
        simpa [fn] using fullGradient_mul (fun x => (ρ n x : ℂ)) f
          (hρSmoothC n) hSmooth z
      have hrhoEq : ρ n z = 1 := by simpa [ρ, a] using hn.1
      have hrhoGrad : fullGradient F (fun x => (ρ n x : ℂ)) z = 0 := by
        simpa [ρ, a] using hn.2
      have hprod : fullGradient F (fn n) z = fullGradient F f z := by
        calc
          _ = (ρ n z : ℂ) • fullGradient F f z +
              f z • fullGradient F (fun x => (ρ n x : ℂ)) z := hprodRule
          _ = fullGradient F f z := by rw [hrhoEq, hrhoGrad]; simp
      rw [hsub n, hrep n, hgr]
      rw [hprod]
      simp
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with n hn
    change (0 : ℝ) = ‖gradErr n z‖ ^ 2
    rw [hn]
    simp
  have hgradMeas (n : ℕ) : AEStronglyMeasurable (fun z => ‖gradErr n z‖ ^ 2) μ :=
    ((Lp.aestronglyMeasurable (gradErr n)).norm).pow 2
  have hgradDomAE (n : ℕ) : ∀ᵐ z ∂μ,
      ‖‖gradErr n z‖ ^ 2‖ ≤ gradDom z := by
    filter_upwards [hgradBound n] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  have hgradIntegral : Tendsto (fun n => ∫ z, ‖gradErr n z‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : X F => (0 : ℝ))
      gradDom hgradMeas hgradDomInt hgradDomAE hgradPointwise
    simpa using h
  have hgradTendsto : Tendsto gradErr atTop (𝓝 0) :=
    specGapLpTwo_tendsto_zero μ gradErr hgradIntegral
  have hmassL2 : Tendsto (fun n => e.toL2 (t n)) atTop (𝓝 fL2) := by
    have h := hmassTendsto.add_const fL2
    simpa [massErr] using h
  have hgradL2 : Tendsto (fun n => e.gradL2 (t n)) atTop (𝓝 grad) := by
    have h := hgradTendsto.add_const grad
    simpa [gradErr] using h
  have hpair : Tendsto (fun n => (e.toL2 (t n), e.gradL2 (t n))) atTop (𝓝 (fL2, grad)) :=
    hmassL2.prodMk_nhds hgradL2
  have htoLp : Continuous (fun p : L2Space F D × GradientL2Space F D => WithLp.toLp 2 p) :=
    WithLp.prod_continuous_toLp 2 (L2Space F D) (GradientL2Space F D)
  have hgraphlim : Tendsto
      (fun n => energyGraphMap e.toL2 e.gradL2 (t n)) atTop
      (𝓝 (WithLp.toLp 2 (fL2, grad))) := by
    change Tendsto (fun n => WithLp.toLp 2 (e.toL2 (t n), e.gradL2 (t n)))
      atTop (𝓝 (WithLp.toLp 2 (fL2, grad)))
    exact (htoLp.tendsto (fL2, grad)).comp hpair
  have hgraphmem := specGap_energyGraph_limit e.toL2 e.gradL2 t fL2 grad hgraphlim
  have hmem : WithLp.toLp 2 (fL2, grad) ∈ E.V := by
    rw [e.graph_eq]
    exact hgraphmem
  refine ⟨⟨WithLp.toLp 2 (fL2, grad), hmem⟩, ?_, ?_⟩ <;>
    simp [FAEnergySpace.M, FAEnergySpace.Gr]

/-- T6 `spec:rellich` — P-SPEC.md:233, 358–362. Restriction of mass to the orbit of a compact
set is a compact operator from the energy graph to the quotient `L²` space. Correction from
`sol-gate-spec`: tie the energy maps to the geometric representatives. -/
theorem T6_rellich (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) (K : Set (X F)) (hK : IsCompact K) :
    ∃ R : E.V →L[ℂ] L2Space F D,
      IsCompactOperator R ∧
      ∀ x : E.V, ∀ᵐ z ∂(volX F), z ∈ D →
        R x z = orbitRestrictedMass F D E Γ K x z := by
  sorry

/-- T7 `spec:ground-state` — P-SPEC.md:234, 364–368. The ground-state transform gives the
coercivity estimate with compact error at every height cutoff above all cusp thresholds. Correction
from review lane `rev-spec`: include separation of distinct cusp representatives at the cutoff.
Correction from `sol-gate-spec`: require a calibrated energy context. -/
theorem T7_ground_state (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (d : SiegelData F Γ)
    (A₀ : d.ι → ℝ) (hA₀ : ∀ i, 0 < A₀ i)
    (hA₀sep : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀ i ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ j ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (A : ℝ) (hA : ∀ i, A₀ i ≤ A) :
    ∃ K : Set (X F), IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ R : E.V →L[ℂ] L2Space F D,
        IsCompactOperator R ∧
        (∀ x : E.V, placeCount F * (1 - 1 / (2 * A)) * ‖E.M x‖ ^ 2 ≤
          ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2) ∧
        (∀ x : E.V, ∀ᵐ z ∂(volX F), z ∈ D →
          R x z = orbitRestrictedMass F D E Γ K x z) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
