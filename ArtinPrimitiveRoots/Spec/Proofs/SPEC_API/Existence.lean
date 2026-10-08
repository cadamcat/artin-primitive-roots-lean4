import ArtinPrimitiveRoots.Spec.Geometry
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Spec.Reduction
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Energy
import ArtinPrimitiveRoots.Spec.Functional
import ArtinPrimitiveRoots.Spec.EisensteinExtra
import ArtinPrimitiveRoots.Spec.Smoothing
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.All

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

instance instCountableRingOfIntegers : Countable (𝓞 F) := inferInstance


section LatticeHelpers

theorem lattice_domain_with_pointwise_coverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E) (μ : Measure E) :
    ∃ P : Set E,
      IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup P μ ∧
      Bornology.IsBounded P ∧ MeasurableSet P ∧
      ∀ x : E, ∃ g : (Submodule.span ℤ (Set.range b)).toAddSubgroup, g +ᵥ x ∈ P := by
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.isAddFundamentalDomain' b μ,
    ZSpan.fundamentalDomain_isBounded b, ZSpan.fundamentalDomain_measurableSet b, ?_⟩
  intro x
  exact (ZSpan.exist_unique_vadd_mem_fundamentalDomain b x).exists

theorem cusp_domain_of_full_lattice (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (hfull : IsFullZLattice (cuspTranslationsZ F Γ σ)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧
      Bornology.IsBounded P ∧ MeasurableSet P ∧
      ∀ x : InfinitePlace F → ℂ,
        ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
  obtain ⟨hdisc, hlattice⟩ := hfull
  letI := hdisc
  letI := hlattice
  let b := Module.Free.chooseBasis ℤ (cuspTranslationsZ F Γ σ)
  obtain ⟨P, hP, hbound, hmeas, hcovers⟩ :=
    lattice_domain_with_pointwise_coverage (b.ofZLatticeBasis ℝ) volume
  have hL : (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))).toAddSubgroup =
      cuspTranslations F Γ σ := by
    rw [b.ofZLatticeBasis_span ℝ]
    exact Submodule.span_int_eq (cuspTranslations F Γ σ)
  rw [hL] at hP hcovers
  refine ⟨P, hP, hbound, hmeas, ?_⟩
  intro x
  obtain ⟨g, hg⟩ := hcovers x
  exact ⟨g, g.property, hg⟩

theorem siegel_data_of_reduction_outputs (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hcusps : ∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))))
    (hfull : ∀ σ : SL(2,F), IsFullZLattice (cuspTranslationsZ F Γ σ))
    (hbalance : ∀ σ : SL(2,F), ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
        ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∀ w,
          |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B)
    (hminkowski : ∃ C_M : ℝ, 0 < C_M ∧ ∀ z : X F, ∃ v : 𝓞 F × 𝓞 F,
      v ≠ (0, 0) ∧ ∏ w : InfinitePlace F,
        rowHeightForm F (algebraMap (𝓞 F) F v.1, algebraMap (𝓞 F) F v.2) z w ≤ C_M) :
    Nonempty (SiegelData F Γ) := by
  classical
  obtain ⟨ι, hι, σ, hσ⟩ := hcusps
  obtain ⟨C_M, hCMpos, hCM⟩ := hminkowski
  letI := hι
  have hP := fun i : ι => cusp_domain_of_full_lattice Γ (σ i) (hfull (σ i))
  choose P hPfd hPbound hPmeas hPcover using hP
  have hB := fun i : ι => hbalance (σ i)
  choose B hBnonneg hBbalance using hB
  exact ⟨{
    ι := ι
    fintype := hι
    σ := σ
    P := P
    B := B
    C_M := C_M
    C_M_pos := hCMpos
    minkowski := hCM
    P_fundamental := hPfd
    P_covers := hPcover
    P_bounded := hPbound
    P_measurable := hPmeas
    balanced := hBbalance
    reps_bijective := hσ }⟩

theorem exists_siegelData (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (hfree : FreeAction F Γ) :
    Nonempty (SiegelData F Γ) := by
  have hbalance : ∀ σ : SL(2,F), ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
        ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∀ w,
          |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
    intro σ
    have : (cuspUnits F Γ σ).FiniteIndex := (R2_cusp_units Γ hfree σ).1
    exact R4_unit_balance (cuspUnits F Γ σ)
  exact siegel_data_of_reduction_outputs Γ (R3_cusps_finite Γ).1
    (fun σ => (R1_cusp_lattice Γ σ).2.2.2.1.1)
    hbalance
    (R7_minkowski (F := F))

end LatticeHelpers

section CutoffHelpers

noncomputable def cuspCutoff (A : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((t - A) / A)

theorem isCuspCutoff_cuspCutoff {A : ℝ} (hA : 0 < A) : IsCuspCutoff A (cuspCutoff A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t - A) / A))
    fun_prop
  · intro x y hxy
    apply Real.smoothTransition.monotone
    exact div_le_div_of_nonneg_right (sub_le_sub_right hxy A) hA.le
  · intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hA.le
  · intro t ht
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hA]
    linarith

end CutoffHelpers

section Core

theorem exists_continuedEisenstein_core (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ)
    (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) :
    Nonempty (ContinuedEisenstein F Γ σ s₁) := by
  obtain ⟨d_siegel⟩ := exists_siegelData Γ hfree
  let D := fundamentalDomainCandidate F Γ (SiegelData.unionSet F d_siegel)
  have hD : IsFundamentalDomain Γ D (volX F) := (R12_fund_domain Γ hfree d_siegel).2.1
  obtain ⟨k₀, hkSmooth, hkNonneg, hkSupport, hkNonzero⟩ := radialKernel_bump
  obtain ⟨A₀, hA₀_ge, hsep_σ⟩ := (R10_cusp_separation Γ).1 σ
  obtain ⟨A₁, hA₁_ge, hsep_d⟩ := (R10_cusp_separation Γ).2.1 d_siegel
  let A := max (max A₀ A₁) (1 + 1 / (8 * s₁ ^ 2))
  have hA : 0 < A := by
    have : 1 ≤ A₀ := hA₀_ge
    have : A₀ ≤ max A₀ A₁ := le_max_left A₀ A₁
    have : max A₀ A₁ ≤ A := le_max_left _ _
    linarith
  have hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ := by
    intro γ γ' z h1 h2
    have hle : A₀ ≤ A := (le_max_left A₀ A₁).trans (le_max_left _ _)
    exact hsep_σ A hle γ γ' z h1 h2
  let τ := cuspCutoff A
  have hτ : IsCuspCutoff A τ := isCuspCutoff_cuspCutoff hA
  sorry

end Core

end ArtinPrimitiveRoots.A1.Spec
