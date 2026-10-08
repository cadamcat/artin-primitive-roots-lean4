import ArtinPrimitiveRoots.Spec.Geometry
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Spec.Reduction
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Energy
import ArtinPrimitiveRoots.Spec.Functional
import ArtinPrimitiveRoots.Spec.EisensteinExtra
import ArtinPrimitiveRoots.Spec.Smoothing
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.All
import Mathlib.LinearAlgebra.Countable

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

instance instCountableRingOfIntegers : Countable (𝓞 F) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine (show Function.Injective (fun x : 𝓞 F => (x : F)) from ?_).countable
  intro x y hxy
  exact Subtype.ext hxy


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

private theorem secondCountable_X_SPEC_API : SecondCountableTopology (X F) := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
  exact e.symm.secondCountableTopology

private theorem secondCountable_H3_SPEC_API (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] : SecondCountableTopology H3 := by
  letI : SecondCountableTopology (X F) := secondCountable_X_SPEC_API (F := F)
  let w₀ : InfinitePlace F := Classical.choice inferInstance
  let c : H3 → X F := fun z _ => z
  let eval : X F → H3 := fun z => z w₀
  have hc : Continuous c := by
    change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
    apply continuous_pi
    intro w
    exact continuous_id
  have heval : Continuous eval := continuous_apply w₀
  have hleft : Function.LeftInverse eval c := by
    intro z
    simp [eval, c]
  exact hleft.isEmbedding heval hc |>.secondCountableTopology

private theorem borelSpace_X_SPEC_API : BorelSpace (X F) := by
  letI : SecondCountableTopology (X F) := secondCountable_X_SPEC_API (F := F)
  letI : SecondCountableTopology H3 := secondCountable_H3_SPEC_API F
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : Countable (InfinitePlace F) := Finite.to_countable
  change BorelSpace (∀ w : InfinitePlace F, H3)
  exact Pi.borelSpace

private theorem continuous_h3_action_SPEC_API (g : SL(2,ℂ)) :
    Continuous (fun z : H3 => g • z) := by
  have hmul : Continuous (fun h : SL(2,ℂ) => g * h) := by
    apply Continuous.subtype_mk
    change Continuous (fun h : SL(2,ℂ) =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_const.mul continuous_subtype_val
  apply (QuotientGroup.isQuotientMap_mk SU2).continuous_iff.mpr
  exact continuous_quotient_mk'.comp hmul

private theorem continuousSL2FAction_SPEC_API (g : SL(2,F)) :
    Continuous (fun z : X F => g • z) := by
  apply continuous_pi
  intro w
  exact (continuous_h3_action_SPEC_API (toInf F g w)).comp (continuous_apply w)

private theorem ae_eq_of_invariant_on_fundamentalDomain
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F))
    (f g : X F → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z)
    (hg : ∀ γ ∈ Γ, ∀ z, g ((γ : SL(2,𝓞 F)) • z) = g z)
    (hfg : ∀ᵐ z ∂(volX F), z ∈ D → f z = g z) :
    ∀ᵐ z ∂(volX F), f z = g z := by
  have hRow : Countable (Fin 2 → 𝓞 F) := by
    have hset : (Set.univ : Set (Fin 2 → 𝓞 F)).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => 𝓞 F)
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa using h
    letI : Countable (↥(Set.univ : Set (Fin 2 → 𝓞 F))) := hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  have hMatrix : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    letI : Countable (Fin 2 → 𝓞 F) := hRow
    have hset : (Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F))).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => (Fin 2 → 𝓞 F))
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa [Matrix] using h
    letI : Countable (↥(Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F)))) :=
      hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := hMatrix
  letI : Countable (SL(2,𝓞 F)) := Subtype.val_injective.countable
  letI : Countable Γ := Subtype.val_injective.countable
  letI : BorelSpace (X F) := borelSpace_X_SPEC_API (F := F)
  have hmp (γ : Γ) : MeasurePreserving
      (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) (volX F) := by
    have hfun : (fun z : X F => (γ : SL(2,𝓞 F)) • z) =
        (fun z : X F => toSLF F (γ : SL(2,𝓞 F)) • z) := by
      funext z
      rfl
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (continuousSL2FAction_SPEC_API (F := F) (toSLF F (γ : SL(2,𝓞 F)))).measurable
    · rw [hfun]
      exact (G3_volume (F := F)).1 (toInf F (toSLF F (γ : SL(2,𝓞 F))))
  have htrans : ∀ᵐ z ∂(volX F),
      ∀ γ : Γ, (γ : SL(2,𝓞 F)) • z ∈ D →
        f ((γ : SL(2,𝓞 F)) • z) = g ((γ : SL(2,𝓞 F)) • z) := by
    apply ae_all_iff.2
    intro γ
    exact (hmp γ).quasiMeasurePreserving.tendsto_ae hfg
  filter_upwards [hD.ae_covers, htrans] with z hzcover hztrans
  obtain ⟨γ, hγ⟩ := hzcover
  calc
    f z = f ((γ : SL(2,𝓞 F)) • z) := (hf γ γ.property z).symm
    _ = g ((γ : SL(2,𝓞 F)) • z) := hztrans γ hγ
    _ = g z := hg γ γ.property z

section Core

theorem exists_continuedEisenstein_core (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ)
    (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) :
    Nonempty (ContinuedEisenstein F Γ σ s₁) := by
  classical
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
  have hA₀_le_A : A₀ ≤ A := (le_max_left A₀ A₁).trans (le_max_left _ _)
  have hA₁_le_A : A₁ ≤ A := (le_max_right A₀ A₁).trans (le_max_left _ _)
  have hA_ge_one : 1 ≤ A := hA₀_ge.trans hA₀_le_A
  have hA_threshold : 1 / (8 * s₁ ^ 2) < A := by
    have hlt : 1 / (8 * s₁ ^ 2) < 1 + 1 / (8 * s₁ ^ 2) := by linarith
    exact hlt.trans_le (le_max_right _ _)
  have hsepA₀ : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ := by
    intro γ γ' z hγ hγ'
    exact hsep_σ A₀ le_rfl γ γ' z hγ hγ'
  let cut : CutoffData F Γ σ τ := {
    A₀ := A₀
    A := A
    A₀_ge := hA₀_ge
    A_ge := hA₀_le_A
    separation := hsepA₀
    cutoff := hτ }

  have hE5 := E5_seed Γ D hD σ A₀ A hA₀_ge hA₀_le_A hsepA₀ τ hτ
  rcases hE5 with ⟨_, hseed, _, ⟨G, hG, hsource⟩, _, _⟩

  obtain ⟨toL2, gradL2, hmass_rep, hgradient_rep, _⟩ := (T2_tests Γ D hD).2
  obtain ⟨E, e, _, _, _⟩ :=
    T4_energy_space Γ D hD toL2 gradL2 hmass_rep hgradient_rep

  let A₀d : d_siegel.ι → ℝ := fun _ => A₁
  have hA₀d : ∀ i, 0 < A₀d i := by
    intro i
    dsimp [A₀d]
    exact lt_of_lt_of_le one_pos hA₁_ge
  have hA₀dsep : ∀ i j : d_siegel.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀d i ≤ normHeight F ((d_siegel.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀d j ≤ normHeight F ((d_siegel.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d_siegel.σ i) := by
    intro i j γ γ' z hi hj
    exact hsep_d A₁ le_rfl i j γ γ' z hi hj
  have hA₀d_le_A : ∀ i, A₀d i ≤ A := by
    intro i
    dsimp [A₀d]
    exact hA₁_le_A
  obtain ⟨K, hK, C₀, hC₀, R, hRcompact, hRestimate, _⟩ :=
    T7_ground_state Γ D hD d_siegel A₀d hA₀d hA₀dsep E e A hA₀d_le_A
  let a : ℝ := placeCount F * (1 - 1 / (2 * A))
  have ha : 0 < a := by
    dsimp [a]
    have hplace : 0 < placeCount F := by
      unfold placeCount
      positivity
    have hAhalf : 1 / (2 * A) < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * A)).2
      nlinarith [hA_ge_one]
    exact mul_pos hplace (by linarith)
  let c : ℝ := a⁻¹
  let C : ℝ := C₀ / a
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg hC₀ ha.le
  have hestimate : ∀ x : E.V,
      ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
    intro x
    have heq : c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 =
        (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) / a := by
      dsimp [c, C]
      field_simp [ha.ne']
    calc
      ‖E.M x‖ ^ 2 ≤
          (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) / a :=
        (le_div_iff₀ ha).2 (by simpa [a, mul_comm] using hRestimate x)
      _ = c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := heq.symm
  have hbelow : placeCount F * (1 - 4 * s₁ ^ 2) < 1 / c := by
    have hproduct : 1 < 8 * s₁ ^ 2 * A := by
      have := (div_lt_iff₀ (by positivity : 0 < 8 * s₁ ^ 2)).mp hA_threshold
      nlinarith
    have hratio : 1 / (2 * A) < 4 * s₁ ^ 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * A)).2
      nlinarith
    have hplace : 0 < placeCount F := by
      unfold placeCount
      positivity
    have hcoef : 1 - 4 * s₁ ^ 2 < 1 - 1 / (2 * A) := by linarith
    have hlt : placeCount F * (1 - 4 * s₁ ^ 2) < a := by
      dsimp [a]
      exact mul_lt_mul_of_pos_left hcoef hplace
    have hcinv : 1 / c = a := by
      dsimp [c]
      field_simp
    rw [hcinv]
    exact hlt
  let gap : SpectralGapData E s₁ := {
    K := R
    compact := hRcompact
    c := c
    C := C
    c_pos := hc
    C_nonneg := hC
    estimate := hestimate
    below := hbelow }

  let lam₁ : ℝ := placeCount F * (1 - 4 * s₁ ^ 2)
  have hLam₁ : lam₁ = placeCount F * (1 - 4 * s₁ ^ 2) := rfl
  have hlam₁_nonneg : 0 ≤ lam₁ := by
    dsimp [lam₁]
    have hplace : 0 ≤ placeCount F := by
      unfold placeCount
      positivity
    have hsquare : s₁ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [h₀, h₁]
    nlinarith
  let N : Submodule ℂ E.V := (E.A (lam₁ : ℂ)).toLinearMap.ker
  obtain ⟨P, hPproj, hPrange, hPself, _⟩ :=
    (F2_resolvent E R hRcompact c C hc hC hestimate).2.2.2.2.2.2
      lam₁ hlam₁_nonneg hbelow
  have hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P ∧
      N = (E.A (lam₁ : ℂ)).toLinearMap.ker := by
    exact ⟨hPrange, hPproj, hPself, rfl⟩
  let κ : ℝ := (lam₁ + 1) / (8 * placeCount F * s₁)
  have hκ : κ = (lam₁ + 1) / (8 * placeCount F * s₁) := rfl
  obtain ⟨ε, hεpos, hεle, hu, hres, hbaseE7⟩ :=
    E7_l2_cont Γ D hD σ s₁ h₀ h₁ E e gap G hG τ cut hsource
      lam₁ hLam₁ P N hP κ hκ
  let u : ℂ → L2Space F D := fun s =>
    faResolvent E (spectralParameter F s) (-G s)
  let θ : L2Space F D := -κ • (E.M.comp (P.comp E.M.adjoint)) (G (s₁ : ℂ))
  have hbase : S3_unsmoothed_base Γ σ D τ u := by
    intro s hs
    let f : X F → ℂ := fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z
    let g : X F → ℂ := fun z => eisSeries F Γ σ s z
    have hf : ∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z := by
      intro γ hγ z
      dsimp [f]
      rw [(hseed s).2.1 γ hγ z, ((T1_l2 Γ D hD).1 (u s)).2 γ hγ z]
    have hsre : 1 / 2 < s.re := by
      have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hs
      rw [dist_eq_norm] at hdist
      have hre : |(s - (5 / 2 : ℂ)).re| < 1 / 2 :=
        lt_of_le_of_lt (Complex.abs_re_le_norm _) hdist
      have hreal := (abs_lt.mp hre).1
      norm_num at hreal
      linarith
    have hg : ∀ γ ∈ Γ, ∀ z, g ((γ : SL(2,𝓞 F)) • z) = g z := by
      intro γ hγ z
      dsimp [g]
      exact (E2_eis_converge Γ σ).2.1 s hsre γ hγ z
    have hfgD : ∀ᵐ z ∂(volX F), z ∈ D → f z = g z :=
      Filter.Eventually.mono (hbaseE7 s hs) (fun z hz hzD => by
        dsimp [f, g]
        rw [hz hzD]
        ring)
    have hfg := ae_eq_of_invariant_on_fundamentalDomain Γ D hD f g hf hg hfgD
    simpa [f, g] using hfg

  have hS2 := S2_smoothing_seed Γ σ k₀ hkSmooth hkNonneg hkSupport hkNonzero
  have hnorm_contDomain : ∀ s ∈ contDomain s₁ ε, ‖s‖ ≤ 5 := by
    intro s hs
    simp only [contDomain, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hs
    rcases hs with (⟨hre, hrel, him, himl⟩ | hball) | ⟨hball, _⟩
    · have hsdecomp : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      rw [hsdecomp]
      calc
        ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ ≤
            ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |s.re| + |s.im| := by simp [Complex.norm_real]
        _ = s.re + s.im := by rw [abs_of_pos hre, abs_of_pos him]
        _ ≤ 5 := by linarith
    · have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hball
      have htriangle : ‖s‖ ≤ ‖s - (5 / 2 : ℂ)‖ + ‖(5 / 2 : ℂ)‖ := by
        calc
          ‖s‖ = ‖(s - (5 / 2 : ℂ)) + (5 / 2 : ℂ)‖ := by congr 1 <;> ring
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hdist
      have hcenter : ‖(5 / 2 : ℂ)‖ = 5 / 2 := by norm_num
      linarith [htriangle, hcenter]
    · have hdist : dist s (s₁ : ℂ) < ε := by
        simpa [Metric.mem_ball] using hball
      have htriangle : ‖s‖ ≤ ‖s - (s₁ : ℂ)‖ + ‖(s₁ : ℂ)‖ := by
        calc
          ‖s‖ = ‖(s - (s₁ : ℂ)) + (s₁ : ℂ)‖ := by congr 1 <;> ring
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hdist
      have hcenter : ‖(s₁ : ℂ)‖ = s₁ := by
        rw [Complex.norm_real, Real.norm_of_nonneg h₀.le]
      linarith [htriangle, hcenter, hεle, h₁]
  have hnorm_center : ‖(s₁ : ℂ)‖ ≤ 5 := by
    rw [Complex.norm_real, Real.norm_of_nonneg h₀.le]
    linarith [h₁]
  have hhat : ∀ s ∈ contDomain s₁ ε,
      radialTransform F k₀ (1 + 2 * s) ≠ 0 := by
    intro s hs
    have hfactor : radialTransform₀ k₀ (1 + 2 * s) ≠ 0 := by
      have hp := hS2.2.2.1 s (hnorm_contDomain s hs)
      intro hz
      rw [hz] at hp
      simp at hp
    rw [radialTransform]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hfactor)
  have hhatCenter : radialTransform F k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0 := by
    have hfactor : radialTransform₀ k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0 := by
      have hp := hS2.2.2.1 (s₁ : ℂ) hnorm_center
      intro hz
      rw [hz] at hp
      simp at hp
    rw [radialTransform]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hfactor)

  have hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
      radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z := by
    intro s hs z
    have hsre : 1 / 2 < s.re := by
      have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hs
      rw [dist_eq_norm] at hdist
      have hre : |s.re - 5 / 2| ≤ ‖s - (5 / 2 : ℂ)‖ := by
        simpa using (Complex.abs_re_le_norm (s - (5 / 2 : ℂ)))
      have hreal := abs_lt.mp (lt_of_le_of_lt hre hdist)
      have : s.re > 2 := by linarith [hreal.1]
      linarith
    have hlocal : ∀ W : Set (X F), IsCompact W →
        ∀ᵐ w ∂(volX F), w ∈ W →
          eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w = eisSeries F Γ σ s w := by
      intro W hW
      exact Filter.Eventually.mono (hbase s hs) (fun w hw _ => hw)
    have hsmoothEq := smoothing_representative_independent k₀ hkSmooth hkSupport
      (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w)
      (eisSeries F Γ σ s) hlocal z
    rw [hsmoothEq]
    exact hS2.2.2.2 s hsre z
  obtain ⟨d, _, _, _, _⟩ :=
    S3_continuation Γ hfree σ s₁ h₀ h₁ D hD k₀ τ hkSmooth hkSupport A hA hsep hτ
      u θ ε ⟨hεpos, hεle⟩ hu hhat hhatCenter hres hbase hseries
  exact ⟨d⟩

end Core

end ArtinPrimitiveRoots.A1.Spec
