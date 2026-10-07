import ArtinPrimitiveRoots.Spec.Stage1

/-! Remaining reduction-theory nodes R8--R10 and R12--R14. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- R8 `spec:siegel-cover` — P-SPEC.md:221, 308–313. The Siegel sets with the R1 translation
domains, R4 balance constants, and R7 Minkowski scale cover every point modulo `Γ`. Correction
from review lane `rev-spec`: use the Siegel sets with the doubled balance bound. -/
theorem R8_siegel_cover (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∀ z : X F, ∃ i : d.ι, ∃ γ : Γ,
      (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z) ∈ SiegelData.setAt F d i := by
  sorry

/-- R9 `spec:proper` — P-SPEC.md:222, 315–324. Arithmetic compact intersections and Siegel-set
intersections are finite; freeness gives disjoint neighborhoods for nonidentity elements. -/
theorem R9_proper (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ K K' : Set (X F), IsCompact K → IsCompact K' →
      {γ : SL(2,𝓞 F) | ∃ z ∈ K, γ • z ∈ K'}.Finite) ∧
    {γ : Γ | ∃ z ∈ SiegelData.unionSet F d,
      (γ : SL(2,𝓞 F)) • z ∈ SiegelData.unionSet F d}.Finite ∧
    (∀ (hfree : FreeAction F Γ) (z : X F),
      ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
        ∀ γ : Γ, γ ≠ 1 → Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U) := by
  sorry

/-- R10 `spec:cusp-separation` — P-SPEC.md:223, 326–328. Above a uniform height threshold,
large representatives at one cusp differ by its stabilizer; compact sets meet only finitely many
high-height cusp cosets. Correction from review lane `rev-spec`: require a common sufficiently
large threshold for each representative set. -/
theorem R10_cusp_separation (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ σ : SL(2,F), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ) ∧
    (∀ (d : SiegelData F Γ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i)) ∧
    (∀ σ : SL(2,F), ∀ K : Set (X F), IsCompact K → ∀ A : ℝ, 0 < A →
      {q : CuspCosets F Γ σ | ∃ z ∈ K,
        A ≤ normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}.Finite) := by
  sorry

/-- R12 `spec:fund-domain` — P-SPEC.md:225, 338–342. The lexicographically least point in each
Siegel-covered orbit is a measurable finite-volume fundamental domain when the action is free. -/
theorem R12_fund_domain (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (d : SiegelData F Γ) :
    let D := fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)
    MeasurableSet D ∧ IsFundamentalDomain Γ D (volX F) ∧ volX F D < ⊤ := by
  sorry

/-- R13 `spec:compact-part` — P-SPEC.md:226. Bounded cusp heights reduce to the union of the
compact balanced boxes from the R8 Siegel sets. -/
theorem R13_compact_part (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ A : ℝ, 0 ≤ A → ∀ i : d.ι, IsCompact (SiegelData.compactBox F d i A)) ∧
    (∀ A : ℝ, 0 ≤ A → ∀ z : X F,
      (∀ i : d.ι, ∀ γ : Γ,
        normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ A) →
      z ∈ SiegelData.compactOrbit F d A) := by
  sorry

/-- R14 `spec:cusp-fubini` — P-SPEC.md:227, 344–347. The invariant integral over a high cusp
tail is the integral over a unit-height domain and a signed-translation domain. -/
theorem R14_cusp_fubini (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (Y : Set (InfinitePlace F → ℝ))
    (hYmeas : MeasurableSet Y)
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P')
    (hP'meas : MeasurableSet P')
    (G : X F → ℂ) (hGinv : IsGammaInvariant F Γ G)
    (hGint : Integrable G (volX F)) :
    ∫ z in D ∩ cuspTail F Γ σ A, G z ∂(volX F) =
      ∫ y in {y ∈ Y | A < ∏ w : InfinitePlace F, y w},
        (∫ x in P', G (σ • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) ∂volume := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
