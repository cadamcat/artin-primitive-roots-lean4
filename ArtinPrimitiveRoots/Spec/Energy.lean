import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Assembly

/-! L² and energy-space nodes T1--T7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

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
  sorry

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
  classical
  have hT1 := T1_l2 Γ D hD
  have hT2 := T2_tests Γ D hD
  obtain ⟨hSat, I, hI⟩ := orbitRestrictedMass_eq_indicator Γ D hD K hK
  obtain ⟨toL2, gradL2, hmass, hgrad, hpartition⟩ := hT2.2
  obtain ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψfinite, hψpartition, hreconstruct⟩ :=
    hpartition K hK
  let hψ : RellichPartition Γ K ψ :=
    ⟨hψsmooth, hψcompact, hψnonneg, hψfinite, hψpartition⟩
  have hlocal := quotient_to_chart_finite_overlap Γ D hD E e hT2.1 hT1.2.1
  obtain ⟨c⟩ := localized_chart_H1_membership Γ hT2.1 ψ hψsmooth hψcompact
  obtain ⟨C, hC, hbound⟩ :=
    localized_chart_H1_bound Γ D hD E e hT2.1 hlocal ψ hψsmooth hψcompact c
  obtain ⟨A, B, hA, hB, hAB⟩ := localized_chart_extension Γ D E e ψ c C hC hbound
  obtain ⟨L, hLcompact, hL⟩ := complex_chart_rellich_compact c.support c.compact A B hAB
  have hLrep := rellich_recombine_test_rep Γ D E e ψ c A B hA hB L hL
  obtain ⟨C', hC', hmassbound⟩ :=
    periodization_L2_bound Γ D hD E e hT2.1 hT1.2.1 hT1.2.2.1 K hK ψ hψ I hI L hLrep
  refine ⟨I.comp E.M, ?_, ?_⟩
  · apply rellich_compact_of_test_bound Γ D E e (I.comp E.M) L hLcompact C' hC'
    intro f
    change ‖I (e.toL2 f)‖ ≤ C' * ‖L (rellichTestVector e f)‖
    exact hmassbound f
  · intro x
    filter_upwards [hI.2 (E.M x)] with z hz
    intro hzD
    simpa [orbitRestrictedMass, Set.indicator] using hz hzD

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
