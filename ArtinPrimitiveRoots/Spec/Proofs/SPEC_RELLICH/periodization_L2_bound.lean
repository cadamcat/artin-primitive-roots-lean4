import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs
import ArtinPrimitiveRoots.Proofs.spec_rellich_b.ChartMeasure

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Periodization and cutoff reconstruction give mass domination by the chart L² norm.
Uses T1 compact overlaps and
unfolding, T2's locally finite partition, G3_volume, and calibrated test representatives.
Cauchy-Schwarz gives the finite-overlap bound; positive compact chart density compares
Lebesgue and hyperbolic norms. Only this norm estimate is needed by the compact assembly. -/
theorem periodization_L2_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hOverlap : RellichOverlapControl Γ D) (hUnfold : RellichUnfolding Γ D)
    (K : Set (X F)) (hK : IsCompact K)
    (ψ : X F → ℝ) (hψ : RellichPartition Γ K ψ)
    (I : L2Space F D →L[ℂ] L2Space F D) (hI : RellichIndicator Γ D K I)
    (L : E.V →L[ℂ] RellichChartL2 F)
    (hLrep : ∀ f : testSubmodule F Γ, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
      L (rellichTestVector e f) p = rellichLocalized F ψ (f : X F → ℂ) p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : testSubmodule F Γ,
      ‖I (e.toL2 f)‖ ≤ C * ‖L (rellichTestVector e f)‖ := by
  classical
  obtain ⟨Kψ, hKψ, hψsupport⟩ := hψ.compact
  have hψsupportR : {z | ψ z ≠ 0} ⊆ Kψ := by
    intro z hz
    apply hψsupport
    simpa using hz
  let pbase : Coord F := fun _ => (0, 1)
  have hpbase : pbase ∈ posSet F := by
    intro w
    norm_num [pbase, posSet]
  let zbase : X F := ptX F pbase
  let Kbar : Set (X F) := insert zbase Kψ
  have hKbar : IsCompact Kbar := hKψ.insert zbase
  let Active : X F → Set Γ := fun z =>
    {γ | ψ ((γ : SL(2,𝓞 F)) • z) ≠ 0}
  have hActiveData : ∀ z, (Active z).Finite ∧
      (Active z).ncard ≤ overlapMultiplicity F Γ Kbar := by
    intro z
    have hOverlapFinite := (hOverlap Kbar hKbar).1
    by_cases hEmpty : Active z = ∅
    · constructor
      · simpa [hEmpty]
      · simp [hEmpty, overlapMultiplicity]
    · obtain ⟨γ₀, hγ₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      let τ : Γ → Γ := fun γ => γ * γ₀⁻¹
      have hMaps : Set.MapsTo τ (Active z) (overlapSet F Γ Kbar Kbar) := by
        intro γ hγ
        have hγK : (γ : SL(2,𝓞 F)) • z ∈ Kbar := by
          apply Set.mem_insert_of_mem
          exact hψsupportR hγ
        have hγ₀K : (γ₀ : SL(2,𝓞 F)) • z ∈ Kbar := by
          apply Set.mem_insert_of_mem
          exact hψsupportR hγ₀
        change ∃ x ∈ Kbar, ((τ γ : Γ) : SL(2,𝓞 F)) • x ∈ Kbar
        refine ⟨(γ₀ : SL(2,𝓞 F)) • z, hγ₀K, ?_⟩
        simpa [τ, smul_smul, mul_assoc] using hγK
      have hInj : Set.InjOn τ (Active z) := by
        intro γ hγ γ' hγ' heq
        apply Subtype.ext
        have h := congrArg (fun x : Γ => x * γ₀) heq
        simpa [τ, mul_assoc] using h
      constructor
      · exact Set.Finite.of_injOn hMaps hInj hOverlapFinite
      · have hcard := Set.ncard_le_ncard_of_injOn τ hMaps hInj hOverlapFinite
        simpa [overlapMultiplicity, Nat.card_coe_set_eq] using hcard
  obtain ⟨U, hUopen, hUsat, hpart⟩ := hψ.partition
  have hcoordCont : Continuous (coordsX F) :=
    RellichChartMeasure.coordsX_continuous
  have hKcoord : IsCompact (coordsX F '' Kbar) := hKbar.image hcoordCont
  have hKcoordNe : (coordsX F '' Kbar).Nonempty := by
    refine ⟨coordsX F zbase, ?_⟩
    exact ⟨zbase, Set.mem_insert _ _, rfl⟩
  have hheightMin : ∀ w : InfinitePlace F,
      ∃ m : ℝ, 0 < m ∧ ∀ p ∈ coordsX F '' Kbar, m ≤ (p w).2 := by
    intro w
    have hcont : Continuous (fun p : Coord F => (p w).2) := by fun_prop
    obtain ⟨p₀, hp₀, hmin⟩ := hKcoord.exists_isMinOn hKcoordNe hcont.continuousOn
    have hp₀pos : 0 < (p₀ w).2 := by
      rcases hp₀ with ⟨z, hz, rfl⟩
      exact (RellichChartMeasure.coordsX_mem_pos z) w
    refine ⟨(p₀ w).2, hp₀pos, ?_⟩
    intro p hp
    exact hmin hp
  let m : InfinitePlace F → ℝ := fun w => Classical.choose (hheightMin w)
  have hmPos : ∀ w, 0 < m w := fun w => (Classical.choose_spec (hheightMin w)).1
  have hmLe : ∀ w, ∀ p ∈ coordsX F '' Kbar, m w ≤ (p w).2 :=
    fun w => (Classical.choose_spec (hheightMin w)).2
  let M : ℝ := ∏ w, ((m w) ^ 3)⁻¹
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.prod_nonneg
    intro w hw
    exact inv_nonneg.mpr (pow_nonneg (le_of_lt (hmPos w)) _)
  let Nreal : ℝ := (overlapMultiplicity F Γ Kbar : ℝ)
  have hN : 0 ≤ Nreal := by dsimp [Nreal]; positivity
  let C : ℝ := Real.sqrt ((Nreal + 1) * M)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  obtain ⟨_, hG3formula, hG3compact, hG3open, _⟩ := G3_volume (F := F)
  letI : IsFiniteMeasureOnCompacts (volX F) := ⟨hG3compact⟩
  letI : Measure.IsOpenPosMeasure (volX F) := ⟨hG3open⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : SecondCountableTopology (X F) := eChartX.symm.secondCountableTopology
  letI : Nonempty (InfinitePlace F) := inferInstance
  let w₀ : InfinitePlace F := Classical.choice ‹Nonempty (InfinitePlace F)›
  let diag : H3 → X F := fun z _ => z
  have hdiag : Continuous diag := by
    apply continuous_pi
    intro w
    exact continuous_id
  have hleft : Function.LeftInverse (fun z : X F => z w₀) diag := by
    intro z
    rfl
  letI : SecondCountableTopology H3 :=
    (hleft.isEmbedding (continuous_apply w₀) hdiag).secondCountableTopology
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : BorelSpace (X F) := inferInstance
  letI : OpensMeasurableSpace (X F) := inferInstance
  letI : T2Space (X F) := eChartX.t2Space
  refine ⟨C, hC, ?_⟩
  intro f
  classical
  have htest : IsGammaTest F Γ (f : X F → ℂ) := (htests (f : X F → ℂ)).mp f.property
  have hInv := htest.1
  have hfCont : Continuous (f : X F → ℂ) :=
    RellichChartMeasure.continuous_of_isSmoothX htest.2.1
  have hψCont : Continuous ψ :=
    RellichChartMeasure.continuous_of_isSmoothRealX hψ.smooth
  let φ : X F → ℂ := fun z => (ψ z : ℂ) * (f : X F → ℂ) z
  let g : X F → ℝ := fun z => Complex.normSq (φ z)
  have hφCont : Continuous φ := by
    dsimp [φ]
    exact (Complex.ofRealCLM.continuous.comp hψCont).mul hfCont
  have hgCont : Continuous g := by
    dsimp [g]
    exact Complex.continuous_normSq.comp hφCont
  have hgSupport : Function.support g ⊆ Kψ := by
    intro z hz
    have hφ : φ z ≠ 0 := by
      intro hzero
      apply hz
      simp [g, hzero]
    have hψz : (ψ z : ℂ) ≠ 0 := (mul_ne_zero_iff.mp hφ).1
    exact hψsupport (by simpa using hψz)
  have hgCompact : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact hKψ hgSupport
  have hgInt : Integrable g (volX F) :=
    hgCont.integrable_of_hasCompactSupport hgCompact
  have hgNonneg : ∀ z, 0 ≤ g z := fun z => Complex.normSq_nonneg _
  let H : X F → ℝ := fun z => ∑' γ : Γ, g ((γ : SL(2,𝓞 F)) • z)
  have hPsiTsum (z : X F) :
      (∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z)) =
        ∑ γ ∈ (hActiveData z).1.toFinset,
          ψ ((γ : SL(2,𝓞 F)) • z) := by
    apply tsum_eq_sum
    intro γ hγ
    have hnot : γ ∉ Active z := by simpa using hγ
    by_contra hne
    exact hnot hne
  have hPhiTsum (z : X F) :
      (∑' γ : Γ, φ ((γ : SL(2,𝓞 F)) • z)) =
        ∑ γ ∈ (hActiveData z).1.toFinset,
          φ ((γ : SL(2,𝓞 F)) • z) := by
    apply tsum_eq_sum
    intro γ hγ
    have hnot : γ ∉ Active z := by simpa using hγ
    have hψzero : ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
      by_contra hne
      exact hnot hne
    simp [φ, hψzero]
  have hGTsum (z : X F) :
      H z = ∑ γ ∈ (hActiveData z).1.toFinset,
        ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := by
    dsimp [H]
    rw [tsum_eq_sum (s := (hActiveData z).1.toFinset)]
    · simp [g, Complex.normSq_eq_norm_sq]
    · intro γ hγ
      have hnot : γ ∉ Active z := by simpa using hγ
      have hψzero : ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
        by_contra hne
        exact hnot hne
      simp [g, φ, hψzero]
  have hReconstruct : ∀ z, z ∈ orbitSaturation F Γ K →
      (∑' γ : Γ, φ ((γ : SL(2,𝓞 F)) • z)) = (f : X F → ℂ) z := by
    intro z hz
    have hpartz := hpart z (hUsat hz)
    have hsumR : ∑ γ ∈ (hActiveData z).1.toFinset,
        ψ ((γ : SL(2,𝓞 F)) • z) = 1 := by
      calc
        _ = ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) := (hPsiTsum z).symm
        _ = 1 := hpartz
    have hsumC : ∑ γ ∈ (hActiveData z).1.toFinset,
        (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) = 1 := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) hsumR
      simpa using h
    calc
      _ = ∑ γ ∈ (hActiveData z).1.toFinset,
          φ ((γ : SL(2,𝓞 F)) • z) := hPhiTsum z
      _ = (∑ γ ∈ (hActiveData z).1.toFinset,
            (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) * (f : X F → ℂ) z := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro γ hγ
          simp [φ, hInv (γ : SL(2,𝓞 F)) γ.property z]
      _ = (f : X F → ℂ) z := by rw [hsumC]; simp
  have hCauchy : ∀ z,
      ‖∑' γ : Γ, φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 ≤
        ((Active z).ncard : ℝ) * H z := by
    intro z
    let s := (hActiveData z).1.toFinset
    have htriangle :
        ‖∑ γ ∈ s, φ ((γ : SL(2,𝓞 F)) • z)‖ ≤
          ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ := norm_sum_le s _
    have hsumNormNonneg : 0 ≤ ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ :=
      Finset.sum_nonneg fun γ hγ => norm_nonneg _
    have hCSraw := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun γ => ‖φ ((γ : SL(2,𝓞 F)) • z)‖) (fun _ => (1 : ℝ))
    have hCS :
        (∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖) ^ 2 ≤
          (s.card : ℝ) * ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := by
      calc
        _ = (∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ * 1) ^ 2 := by simp
        _ ≤ (∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2) *
              (∑ γ ∈ s, (1 : ℝ) ^ 2) := hCSraw
        _ = (s.card : ℝ) * ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := by simp [mul_comm]
    have hnorm :
        ‖∑ γ ∈ s, φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 ≤
          (s.card : ℝ) * ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := by
      have hnormNonneg := norm_nonneg (∑ γ ∈ s, φ ((γ : SL(2,𝓞 F)) • z))
      nlinarith
    have hsumSqNonneg : 0 ≤ ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 :=
      Finset.sum_nonneg fun γ hγ => sq_nonneg _
    have hcardEq : s.card = (Active z).ncard := by
      dsimp [s]
      exact (Set.ncard_eq_toFinset_card (Active z) (hActiveData z).1).symm
    calc
      ‖∑' γ : Γ, φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 =
          ‖∑ γ ∈ s, φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := by rw [hPhiTsum]
      _ ≤ (s.card : ℝ) * ∑ γ ∈ s, ‖φ ((γ : SL(2,𝓞 F)) • z)‖ ^ 2 := hnorm
      _ = ((Active z).ncard : ℝ) * H z := by rw [hcardEq, ← hGTsum z]
  have hHNonneg : ∀ z, 0 ≤ H z := by
    intro z
    rw [hGTsum z]
    exact Finset.sum_nonneg fun γ hγ => sq_nonneg _
  let u : L2Space F D := I (e.toL2 f)
  have hIVal : ∀ᵐ z ∂(volX F).restrict D,
      u z = (orbitSaturation F Γ K).indicator (fun z => (f : X F → ℂ) z) z := by
    have hle : (volX F).restrict D ≤ volX F := Measure.restrict_le_self
    have hI' := ae_mono hle (hI.2 (e.toL2 f))
    have hm' := ae_mono hle (e.mass_rep f)
    filter_upwards [hI', hm', ae_restrict_mem₀ hD.nullMeasurableSet] with z hi hm hzD
    rw [hi hzD]
    by_cases hs : z ∈ orbitSaturation F Γ K <;> simp [hs, hm hzD]
  by_cases hgzero : ∀ z, g z = 0
  · have hφzero : ∀ z, φ z = 0 := by
      intro z
      have hz := hgzero z
      dsimp [g] at hz
      exact Complex.normSq_eq_zero.mp hz
    have hfsat : ∀ z, z ∈ orbitSaturation F Γ K → (f : X F → ℂ) z = 0 := by
      intro z hz
      have hrec := hReconstruct z hz
      have hsumzero : (∑' γ : Γ, φ ((γ : SL(2,𝓞 F)) • z)) = 0 := by
        rw [hPhiTsum z]
        simp [hφzero]
      rw [hsumzero] at hrec
      exact hrec.symm
    have huZero : u = 0 := by
      apply (Lp.eq_zero_iff_ae_eq_zero).2
      filter_upwards [hIVal] with z hz
      by_cases hs : z ∈ orbitSaturation F Γ K
      · simp [hz, hs, hfsat z hs]
      · simp [hz, hs]
    change ‖u‖ ≤ C * ‖L (rellichTestVector e f)‖
    simpa [huZero] using mul_nonneg hC (norm_nonneg (L (rellichTestVector e f)))
  · push_neg at hgzero
    obtain ⟨z₀, hz₀⟩ := hgzero
    have hgIntegralPos : 0 < ∫ z, g z ∂(volX F) :=
      integral_pos_of_integrable_nonneg_nonzero hgCont hgInt hgNonneg hz₀
    let gC : X F → ℂ := fun z => (g z : ℂ)
    have hgCInt : Integrable gC (volX F) := by
      simpa [gC] using (Complex.ofRealCLM.integrable_comp hgInt)
    have hHComplex (z : X F) :
        (∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z)) = (H z : ℂ) := by
      have htsum := tsum_eq_sum (L := SummationFilter.unconditional Γ)
        (s := (hActiveData z).1.toFinset) (f := fun γ : Γ =>
          gC ((γ : SL(2,𝓞 F)) • z)) (by
            intro γ hγ
            have hnot : γ ∉ Active z := by
              intro hmem
              exact hγ ((hActiveData z).1.mem_toFinset.mpr hmem)
            have hψzero : ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
              by_contra hne
              exact hnot hne
            simp [gC, g, φ, hψzero])
      rw [htsum, hGTsum z]
      simp [gC, g, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
    have hUnfoldC := hUnfold gC hgCInt
    have hRealIntegral :
        Complex.re (∫ z, gC z ∂(volX F)) = ∫ z, g z ∂(volX F) := by
      calc
        Complex.re (∫ z, gC z ∂(volX F)) =
            ∫ z, Complex.re (gC z) ∂(volX F) := (integral_re hgCInt).symm
        _ = ∫ z, g z ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards with z
          simp [gC]
    have hPerInt : Integrable (fun z => ∑' γ : Γ,
        gC ((γ : SL(2,𝓞 F)) • z)) ((volX F).restrict D) := by
      apply Integrable.of_integral_ne_zero
      have hne : (∫ z, (∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z))
          ∂((volX F).restrict D)) ≠ 0 := by
        change (∫ z in D, (∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z)) ∂(volX F)) ≠ 0
        intro hzero
        have hzeroC : (∫ z, gC z ∂(volX F)) = 0 := hUnfoldC.symm.trans hzero
        rw [hzeroC] at hRealIntegral
        simp at hRealIntegral
        linarith
      exact hne
    have hUnfoldEq : ∫ z, H z ∂(volX F).restrict D = ∫ z, g z ∂(volX F) := by
      calc
        ∫ z, H z ∂(volX F).restrict D =
            ∫ z, Complex.re (∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z))
              ∂(volX F).restrict D := by
          apply integral_congr_ae
          filter_upwards with z
          rw [hHComplex z]
          simp [gC]
        _ = Complex.re (∫ z, ∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z)
              ∂(volX F).restrict D) := integral_re hPerInt
        _ = Complex.re (∫ z, gC z ∂(volX F)) := by rw [hUnfoldC]
        _ = ∫ z, g z ∂(volX F) := by
          calc
            Complex.re (∫ z, gC z ∂(volX F)) =
                ∫ z, Complex.re (gC z) ∂(volX F) := (integral_re hgCInt).symm
            _ = ∫ z, g z ∂(volX F) := by
              apply integral_congr_ae
              filter_upwards with z
              simp [gC]
    have hHInt : Integrable H ((volX F).restrict D) := by
      have hHEq : H =ᵐ[(volX F).restrict D]
          (fun z => Complex.re (∑' γ : Γ, gC ((γ : SL(2,𝓞 F)) • z))) := by
        filter_upwards with z
        rw [hHComplex z]
        simp [gC]
      exact hPerInt.re.congr hHEq.symm
    have huSqInt : Integrable (fun z => ‖u z‖ ^ 2) ((volX F).restrict D) := by
      exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
    have hscaledInt : Integrable (fun z => (Nreal + 1) * H z) ((volX F).restrict D) :=
      hHInt.const_mul (Nreal + 1)
    have hpoint : ∀ᵐ z ∂((volX F).restrict D),
        ‖u z‖ ^ 2 ≤ (Nreal + 1) * H z := by
      filter_upwards [hIVal] with z hz
      by_cases hs : z ∈ orbitSaturation F Γ K
      · have hrec := hReconstruct z hs
        rw [hz]
        simp [hs]
        rw [← hrec]
        exact (hCauchy z).trans <| mul_le_mul_of_nonneg_right
          (by
            have hnat : (Active z).ncard ≤ Nat.succ (overlapMultiplicity F Γ Kbar) :=
              Nat.le_succ_of_le (hActiveData z).2
            change ((Active z).ncard : ℝ) ≤
              (overlapMultiplicity F Γ Kbar : ℝ) + 1
            exact_mod_cast hnat)
          (hHNonneg z)
      · rw [hz]
        simp [hs]
        exact mul_nonneg (by linarith) (hHNonneg z)
    have hquotSq : ‖u‖ ^ 2 ≤ (Nreal + 1) * (∫ z, g z ∂(volX F)) := by
      calc
        ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂((volX F).restrict D) :=
          RellichChartMeasure.lp_two_norm_sq_eq_integral_norm_sq _ _
        _ ≤ ∫ z, (Nreal + 1) * H z ∂((volX F).restrict D) :=
          MeasureTheory.integral_mono_ae huSqInt hscaledInt hpoint
        _ = (Nreal + 1) * ∫ z, H z ∂((volX F).restrict D) := by rw [integral_const_mul]
        _ = (Nreal + 1) * ∫ z, g z ∂(volX F) := by rw [hUnfoldEq]
    let vChart : RellichChartL2 F := L (rellichTestVector e f)
    let chartFun : RellichCoord F → ℂ := rellichLocalized F ψ (f : X F → ℂ)
    have hchartAES : AEStronglyMeasurable chartFun (volume : Measure (RellichCoord F)) :=
      (Lp.aestronglyMeasurable vChart).congr (hLrep f)
    have hchartMem : MemLp chartFun 2 (volume : Measure (RellichCoord F)) :=
      (Lp.memLp vChart).congr_norm hchartAES
        ((hLrep f).mono fun p hp => by rw [hp])
    let gChart : RellichCoord F → ℝ := fun p => Complex.normSq (chartFun p)
    have hchartInt : Integrable gChart (volume : Measure (RellichCoord F)) := by
      simpa [gChart, Complex.normSq_eq_norm_sq] using
        (MeasureTheory.memLp_two_iff_integrable_sq_norm hchartMem.aestronglyMeasurable).mp hchartMem
    have hvChartNorm : ‖vChart‖ ^ 2 =
        ∫ p, gChart p ∂(volume : Measure (RellichCoord F)) := by
      calc
        ‖vChart‖ ^ 2 = ∫ p, ‖vChart p‖ ^ 2 ∂(volume : Measure (RellichCoord F)) :=
          RellichChartMeasure.lp_two_norm_sq_eq_integral_norm_sq _ _
        _ = ∫ p, gChart p ∂(volume : Measure (RellichCoord F)) := by
          apply integral_congr_ae
          filter_upwards [hLrep f] with p hp
          rw [hp]
          change ‖rellichLocalized F ψ (f : X F → ℂ) p‖ ^ 2 =
            Complex.normSq (chartFun p)
          rw [Complex.normSq_eq_norm_sq]
    let coordEquiv := RellichChartMeasure.rellichCoordMeasurableEquiv F
    let invChart := coordEquiv.symm
    have hInvChart : MeasurePreserving invChart
        (volume : Measure (Coord F)) (volume : Measure (RellichCoord F)) :=
      (RellichChartMeasure.rellichCoordMeasurableEquiv_measurePreserving F).symm
    let gCoord : Coord F → ℝ := fun q => gChart (RellichChartMeasure.coordToRellich F q)
    have hcoordInt : Integrable gCoord (volume : Measure (Coord F)) := by
      exact hInvChart.integrable_comp_of_integrable hchartInt
    have hcoordIntegral :
        ∫ q, gCoord q ∂(volume : Measure (Coord F)) =
          ∫ p, gChart p ∂(volume : Measure (RellichCoord F)) := by
      dsimp [gCoord]
      exact hInvChart.integral_comp invChart.measurableEmbedding gChart
    have hposEquiv (q : Coord F) :
        RellichChartMeasure.coordToRellich F q ∈ rellichPosSet F ↔ q ∈ posSet F := by
      simp [RellichChartMeasure.coordToRellich, rellichPosSet, posSet]
    have hcoordEval (q : Coord F) :
        gCoord q = if q ∈ posSet F then g (ptX F q) else 0 := by
      by_cases hq : q ∈ posSet F
      · have hp : RellichChartMeasure.coordToRellich F q ∈ rellichPosSet F :=
          (hposEquiv q).2 hq
        have hround := RellichChartMeasure.rellichToCoord_coordToRellich F q
        simp [gCoord, gChart, chartFun, rellichLocalized, g, φ, hq, hp, hround]
      · have hp : RellichChartMeasure.coordToRellich F q ∉ rellichPosSet F :=
          fun hh => hq ((hposEquiv q).1 hh)
        simp [gCoord, gChart, chartFun, rellichLocalized, hp, hq]
    have hcoordSupport : Function.support gCoord ⊆ coordsX F '' Kbar := by
      intro q hqg
      change gCoord q ≠ 0 at hqg
      have hqPos : q ∈ posSet F := by
        by_contra hq
        rw [hcoordEval q, if_neg hq] at hqg
        exact hqg rfl
      have hgq : g (ptX F q) ≠ 0 := by
        rw [hcoordEval q, if_pos hqPos] at hqg
        exact hqg
      have hφq : φ (ptX F q) ≠ 0 := by
        intro hzero
        apply hgq
        simp [g, hzero]
      have hψqC : (ψ (ptX F q) : ℂ) ≠ 0 := (mul_ne_zero_iff.mp hφq).1
      have hψq : ψ (ptX F q) ≠ 0 := by
        intro hz
        apply hψqC
        simp [hz]
      have hzK : ptX F q ∈ Kψ := hψsupportR hψq
      have hcoords := RellichChartMeasure.coordsX_ptX q hqPos
      exact ⟨ptX F q, Set.mem_insert_of_mem zbase hzK, hcoords⟩
    let J : Coord F → ℝ := fun q => ∏ w, (((q w).2) ^ 3)⁻¹
    have hJbound (q : Coord F) (hq : q ∈ coordsX F '' Kbar) : J q ≤ M := by
      dsimp [J, M]
      have hqPos : q ∈ posSet F := by
        rcases hq with ⟨z, hz, rfl⟩
        exact RellichChartMeasure.coordsX_mem_pos z
      apply Finset.prod_le_prod₀
      · intro w hw
        exact inv_nonneg.mpr (pow_nonneg (le_of_lt (hqPos w)) _)
      · intro w hw
        have hpow : (m w) ^ 3 ≤ (q w).2 ^ 3 := by
          exact pow_le_pow_left₀ (le_of_lt (hmPos w)) (hmLe w q hq) 3
        exact inv_anti₀ (pow_pos (hmPos w) 3) hpow
    have hcoordEvalNonneg : ∀ q, 0 ≤ gCoord q := by
      intro q
      rw [hcoordEval q]
      split_ifs with hq
      · exact hgNonneg (ptX F q)
      · simp
    have hJmeas : Measurable J := by
      dsimp [J]
      measurability
    have hprodAES : AEStronglyMeasurable (fun q => gCoord q * J q)
        (volume : Measure (Coord F)) :=
      hcoordInt.aestronglyMeasurable.mul hJmeas.aestronglyMeasurable
    have hprodNonneg : ∀ q, 0 ≤ gCoord q * J q := by
      intro q
      by_cases hzero : gCoord q = 0
      · simp [hzero]
      · have hqK := hcoordSupport hzero
        have hqPos : q ∈ posSet F := by
          rcases hqK with ⟨z, hz, rfl⟩
          exact RellichChartMeasure.coordsX_mem_pos z
        dsimp [J]
        apply mul_nonneg (hcoordEvalNonneg q)
        apply Finset.prod_nonneg
        intro w hw
        exact inv_nonneg.mpr (pow_nonneg (le_of_lt (hqPos w)) _)
    have hDensity : ∀ q, gCoord q * J q ≤ M * gCoord q := by
      intro q
      by_cases hzero : gCoord q = 0
      · simp [hzero]
      · have hJ := hJbound q (hcoordSupport hzero)
        calc
          gCoord q * J q ≤ gCoord q * M := mul_le_mul_of_nonneg_left hJ (hcoordEvalNonneg q)
          _ = M * gCoord q := by ring
    have hscaledInt : Integrable (fun q => M * gCoord q) (volume : Measure (Coord F)) :=
      hcoordInt.const_mul M
    have hprodInt : Integrable (fun q => gCoord q * J q) (volume : Measure (Coord F)) :=
      hscaledInt.mono hprodAES (ae_of_all _ fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hprodNonneg q),
          Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (hcoordEvalNonneg q))]
        exact hDensity q)
    have hcoordDensityIntegral :
        ∫ q, gCoord q * J q ∂(volume : Measure (Coord F)) ≤
          M * ∫ q, gCoord q ∂(volume : Measure (Coord F)) := by
      calc
        ∫ q, gCoord q * J q ∂(volume : Measure (Coord F)) ≤
            ∫ q, M * gCoord q ∂(volume : Measure (Coord F)) :=
          MeasureTheory.integral_mono_ae hprodInt hscaledInt (ae_of_all _ hDensity)
        _ = M * ∫ q, gCoord q ∂(volume : Measure (Coord F)) := by
          rw [integral_const_mul]
    have hcoordIndicator (q : Coord F) :
        (posSet F).indicator (fun q => g (ptX F q) * J q) q = gCoord q * J q := by
      by_cases hq : q ∈ posSet F
      · rw [Set.indicator_of_mem hq, hcoordEval q, if_pos hq]
      · rw [Set.indicator_of_notMem hq, hcoordEval q, if_neg hq]
        simp
    have hposMeas : MeasurableSet (posSet F) := by
      change MeasurableSet {q : Coord F | ∀ w, 0 < (q w).2}
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun w =>
        measurableSet_lt measurable_const (measurable_snd.comp (measurable_pi_apply w))
    have hG3coord :
        ∫ z, g z ∂(volX F) = ∫ q, gCoord q * J q ∂(volume : Measure (Coord F)) := by
      rw [hG3formula g hgInt]
      calc
        ∫ q in posSet F, g (ptX F q) * J q ∂(volume : Measure (Coord F)) =
            ∫ q, (posSet F).indicator (fun q => g (ptX F q) * J q) q
              ∂(volume : Measure (Coord F)) := (integral_indicator hposMeas).symm
        _ = ∫ q, gCoord q * J q ∂(volume : Measure (Coord F)) := by
          apply integral_congr_ae
          exact ae_of_all _ hcoordIndicator
    have hfullBound : ∫ z, g z ∂(volX F) ≤ M * ‖vChart‖ ^ 2 := by
      calc
        ∫ z, g z ∂(volX F) = ∫ q, gCoord q * J q ∂(volume : Measure (Coord F)) := hG3coord
        _ ≤ M * ∫ q, gCoord q ∂(volume : Measure (Coord F)) := hcoordDensityIntegral
        _ = M * ‖vChart‖ ^ 2 := by rw [hcoordIntegral, hvChartNorm]
    have hcoef : 0 ≤ Nreal + 1 := by linarith [hN]
    have hfinalSq : ‖u‖ ^ 2 ≤ C ^ 2 * ‖vChart‖ ^ 2 := by
      calc
        ‖u‖ ^ 2 ≤ (Nreal + 1) * ∫ z, g z ∂(volX F) := hquotSq
        _ ≤ (Nreal + 1) * (M * ‖vChart‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hfullBound hcoef
        _ = C ^ 2 * ‖vChart‖ ^ 2 := by
          dsimp [C]
          rw [Real.sq_sqrt (mul_nonneg hcoef hM)]
          ring
    have hfinal : ‖u‖ ≤ C * ‖vChart‖ := by
      apply (sq_le_sq₀ (norm_nonneg u) (mul_nonneg hC (norm_nonneg vChart))).mp
      simpa [mul_pow] using hfinalSq
    change ‖u‖ ≤ C * ‖L (rellichTestVector e f)‖
    exact hfinal

end ArtinPrimitiveRoots.A1.Spec
