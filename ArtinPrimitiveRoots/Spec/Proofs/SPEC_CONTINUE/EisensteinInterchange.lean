import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.RadialTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.LinearAlgebra.Countable

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

local instance : TopologicalSpace (SL(2, ℂ)) := OAI.CubicEisenstein.complexSLTopology
local instance : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace :=
  QuotientGroup.instTopologicalSpace OAI.CubicEisenstein.compactSubgroup
local instance : TopologicalSpace H3 := H3_eq_OAI.symm ▸ inferInstance
local instance : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
  borel OAI.CubicEisenstein.HyperbolicSpace
local instance : BorelSpace OAI.CubicEisenstein.HyperbolicSpace := ⟨rfl⟩
local instance : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := by
  exact BorelSpace.opensMeasurable
local instance : T2Space OAI.CubicEisenstein.UpperCoordinates := inferInstance
local instance : T2Space OAI.CubicEisenstein.HyperbolicSpace :=
  OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space

open OAI.CubicEisenstein

private theorem ppi_continuous_at (p : H3) :
    Continuous (fun q : H3 => ppi p q) := by
  have hh : Continuous height := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_continuous
  have hx : Continuous horiz := by
    rw [horiz_eq_hyperbolicHorizontal]
    exact hyperbolicHorizontal_continuous
  have hpos (q : H3) : 0 < height q := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_pos q
  have hp : 0 < height p := hpos p
  have hnum : Continuous (fun q : H3 =>
      Complex.normSq (horiz p - horiz q) + height p ^ 2 + height q ^ 2) := by
    fun_prop
  have hden : Continuous (fun q : H3 => 2 * height p * height q) := by
    fun_prop
  have hquot : Continuous (fun q : H3 =>
      (Complex.normSq (horiz p - horiz q) + height p ^ 2 + height q ^ 2) /
        (2 * height p * height q)) :=
    hnum.div hden (fun q =>
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hp) (hpos q)).ne')
  have hformula (q : H3) : ppi p q =
      (Complex.normSq (horiz p - horiz q) + height p ^ 2 + height q ^ 2) /
        (2 * height p * height q) := by rfl
  exact hquot.congr fun q => (hformula q).symm

private theorem radialKernel_continuous (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (z : X F) :
    Continuous (fun w => radialKernel F k₀ z w) := by
  unfold radialKernel
  apply continuous_finset_prod
  intro v hv
  exact Complex.continuous_ofReal.comp <|
    hkSmooth.continuous.comp <| (ppi_continuous_at (z v)).comp (continuous_apply v)

private theorem normHeight_continuous : Continuous (normHeight F) := by
  have hh : Continuous height := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_continuous
  unfold normHeight
  apply continuous_finset_prod
  intro v hv
  exact hh.comp (continuous_apply v)

private theorem actAtPlaces_continuous (g : InfinitePlace F → SL(2, ℂ)) :
    Continuous (actAtPlaces F g) := by
  apply continuous_pi
  intro v
  exact (OAI.CubicEisenstein.continuous_hyperbolic_action (g v)).comp (continuous_apply v)

private theorem normHeight_pos' (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro v hv
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)

private theorem eisTerm_continuous (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F))
    (s : ℂ) (q : CuspCosets F Γ σ) : Continuous (fun z : X F => eisTerm F Γ σ s z q) := by
  let γ : SL(2,F) := toSLF F (q.out : Γ)
  let δ : SL(2,F) := σ⁻¹ * γ
  have hterm (z : X F) : eisTerm F Γ σ s z q =
      ((normHeight F (δ • z) : ℝ) : ℂ) ^ (1 + 2 * s) := by
    dsimp [eisTerm]
    have hγ (w : X F) :
        ((q.out : Γ) : SL(2, 𝓞 F)) • w = γ • w := rfl
    rw [hγ, ← smul_smul]
  have hnorm : Continuous (fun z : X F => normHeight F (δ • z)) :=
    normHeight_continuous.comp (actAtPlaces_continuous (toInf F δ))
  have hbase : Continuous (fun z : X F => (normHeight F (δ • z) : ℂ)) :=
    Complex.continuous_ofReal.comp hnorm
  have hpow : Continuous (fun z : X F =>
      (normHeight F (δ • z) : ℂ) ^ (1 + 2 * s)) := by
    apply hbase.cpow continuous_const
    intro z
    exact Complex.ofReal_mem_slitPlane.mpr (normHeight_pos' (δ • z))
  exact hpow.congr fun z => (hterm z).symm

private theorem radialKernel_norm_bound (k₀ : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t, |k₀ t| ≤ B) (z w : X F) :
    ‖radialKernel F k₀ z w‖ ≤ B ^ Fintype.card (InfinitePlace F) := by
  unfold radialKernel
  rw [norm_prod]
  calc
    ∏ v : InfinitePlace F, ‖(k₀ (ppi (z v) (w v)) : ℂ)‖ ≤
        ∏ _v : InfinitePlace F, B := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact norm_nonneg _
      · intro v hv
        simpa [Complex.norm_real] using hbound (ppi (z v) (w v))
    _ = B ^ Fintype.card (InfinitePlace F) := by simp

private theorem smoothing_eisTerm_eigen (k₀ : ℝ → ℝ)
    (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) (s : ℂ)
    (q : CuspCosets F Γ σ) (z : X F) :
    smoothingOperator F k₀ (fun w => eisTerm F Γ σ s w q) z =
      radialTransform F k₀ (1 + 2 * s) * eisTerm F Γ σ s z q := by
  let δ : SL(2,F) := σ⁻¹ * toSLF F (q.out : Γ)
  let g : InfinitePlace F → SL(2, ℂ) := toInf F δ
  have hAction (w : X F) :
      σ⁻¹ • (((q.out : Γ) : SL(2, 𝓞 F)) • w) = actAtPlaces F g w := by
    have hγ : ((q.out : Γ) : SL(2, 𝓞 F)) • w =
        (toSLF F (q.out : Γ)) • w := rfl
    calc
      σ⁻¹ • (((q.out : Γ) : SL(2, 𝓞 F)) • w) =
          σ⁻¹ • ((toSLF F (q.out : Γ)) • w) := by rw [hγ]
      _ = (σ⁻¹ * toSLF F (q.out : Γ)) • w := by rw [smul_smul]
      _ = actAtPlaces F g w := by
        funext v
        rfl
  have hterm (w : X F) : eisTerm F Γ σ s w q =
      ((normHeight F (actAtPlaces F g w) : ℝ) : ℂ) ^ (1 + 2 * s) := by
    unfold eisTerm
    rw [hAction]
  have hfun : (fun w => eisTerm F Γ σ s w q) =
      fun w => ((normHeight F (actAtPlaces F g w) : ℝ) : ℂ) ^ (1 + 2 * s) :=
    funext hterm
  rw [hfun]
  calc
    smoothingOperator F k₀
        (fun w => ((normHeight F (actAtPlaces F g w) : ℝ) : ℂ) ^ (1 + 2 * s)) z =
      smoothingOperator F k₀ (fun w => ((normHeight F w : ℝ) : ℂ) ^ (1 + 2 * s))
        (actAtPlaces F g z) :=
      smoothing_isometry_equivariant_of_Geometry k₀ g
        (fun w => ((normHeight F w : ℝ) : ℂ) ^ (1 + 2 * s)) z
    _ = radialTransform F k₀ (1 + 2 * s) *
        ((normHeight F (actAtPlaces F g z) : ℝ) : ℂ) ^ (1 + 2 * s) :=
      smoothing_radial_power k₀ (1 + 2 * s) (actAtPlaces F g z)
    _ = radialTransform F k₀ (1 + 2 * s) * eisTerm F Γ σ s z q := by
      rw [← hterm z]

theorem smoothing_eisSeries_interchange (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (s : ℂ) (hs : 1 / 2 < s.re) (z : X F) :
    smoothingOperator F k₀ (eisSeries F Γ σ s) z =
      radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z := by
  classical
  letI : T2Space H3 := OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
  letI : SecondCountableTopology H3 :=
    OAI.CubicEisenstein.upperCoordinatesHomeomorph.symm.secondCountableTopology
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : SecondCountableTopology (X F) := eChartX.symm.secondCountableTopology
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : BorelSpace (X F) := inferInstance
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  obtain ⟨_, _, hG3compact, _, _⟩ := G3_volume (F := F)
  letI : IsFiniteMeasureOnCompacts (volX F) := ⟨hG3compact⟩
  obtain ⟨K, hKc, hKz, hKsupport⟩ := radialKernel_support_compact F k₀ hkSupport z
  have hKmeas : MeasurableSet K := hKc.measurableSet
  let σ₀ : ℝ := (1 / 2 + s.re) / 2
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀s : σ₀ ≤ s.re := by dsimp [σ₀]; linarith
  obtain ⟨m, hmSum, hmBound⟩ :=
    (E2_eis_converge (F := F) Γ σ).1 K hKc σ₀ s.re hσ₀
  have hImage : IsCompact ((fun t : ℝ => |k₀ t|) '' Set.Icc 1 (1 + 1 / 100)) :=
    isCompact_Icc.image (continuous_abs.comp hkSmooth.continuous)
  obtain ⟨B, hB⟩ := hImage.bddAbove
  change ∀ x ∈ (fun t : ℝ => |k₀ t|) '' Set.Icc 1 (1 + 1 / 100), x ≤ B at hB
  have hBnonneg : 0 ≤ B := by
    have hmem : |k₀ 1| ∈ (fun t : ℝ => |k₀ t|) '' Set.Icc 1 (1 + 1 / 100) :=
      ⟨1, ⟨le_rfl, by norm_num⟩, rfl⟩
    exact (abs_nonneg _).trans (hB _ hmem)
  let C : ℝ := B ^ Fintype.card (InfinitePlace F)
  have hC : 0 ≤ C := by positivity
  have hKernelNorm (w : X F) : ‖radialKernel F k₀ z w‖ ≤ C := by
    simpa [C] using radialKernel_norm_bound k₀ B hBnonneg
      (fun t => by
        by_cases ht : k₀ t = 0
        · simpa [ht] using hBnonneg
        · exact hB _ ⟨t, hkSupport ht, rfl⟩) z w
  let f : CuspCosets F Γ σ → X F → ℂ :=
    fun q w => radialKernel F k₀ z w * eisTerm F Γ σ s w q
  have hfCont (q : CuspCosets F Γ σ) : Continuous (f q) := by
    dsimp [f]
    exact (radialKernel_continuous k₀ hkSmooth z).mul (eisTerm_continuous Γ σ s q)
  have hfInt (q : CuspCosets F Γ σ) : Integrable (f q) (volX F) := by
    have hOn : IntegrableOn (f q) K (volX F) := by
      exact @ContinuousOn.integrableOn_compact' (X F) ℂ
        (inferInstance : MeasurableSpace (X F)) (inferInstance : TopologicalSpace (X F))
        (inferInstance : NormedAddCommGroup ℂ) (volX F) (inferInstance : OpensMeasurableSpace (X F))
        K (f q) (inferInstance : IsFiniteMeasureOnCompacts (volX F))
        hKc hKmeas (hfCont q).continuousOn
    have hOn' : Integrable (Set.indicator K (f q)) (volX F) :=
      (integrable_indicator_iff hKmeas).2 hOn
    have hEq : Set.indicator K (f q) = f q := by
      funext w
      by_cases hw : w ∈ K
      · rw [Set.indicator_of_mem hw]
      · have hker : radialKernel F k₀ z w = 0 := by
          by_contra hne
          exact hw (hKsupport w hne)
        simp [f, hw, hker]
    rw [← hEq]
    exact hOn'
  let interval : Set ℝ := Set.Icc 1 (1 + 1 / 100)
  have hCabs : IsCompact ((fun t : ℝ => |k₀ t|) '' interval) := by
    dsimp [interval]
    exact isCompact_Icc.image (continuous_abs.comp hkSmooth.continuous)
  obtain ⟨D, hD⟩ := hCabs.bddAbove
  change ∀ x ∈ (fun t : ℝ => |k₀ t|) '' interval, x ≤ D at hD
  have hDnonneg : 0 ≤ D := by
    have hmem : |k₀ 1| ∈ (fun t : ℝ => |k₀ t|) '' interval := by
      refine ⟨1, ?_, rfl⟩
      simp [interval]
    exact (abs_nonneg _).trans (hD _ hmem)
  let kernelBound : ℝ := D ^ Fintype.card (InfinitePlace F)
  have hKernelBoundNonneg : 0 ≤ kernelBound := by positivity
  have hKernelBound (w : X F) : ‖radialKernel F k₀ z w‖ ≤ kernelBound :=
    radialKernel_norm_bound k₀ D hDnonneg (fun t => by
      by_cases ht : k₀ t = 0
      · simpa [ht] using hDnonneg
      · exact hD _ ⟨t, hkSupport ht, rfl⟩) z w
  have hmNonneg (q : CuspCosets F Γ σ) : 0 ≤ m q :=
    (norm_nonneg _).trans (hmBound z hKz s hσ₀s le_rfl q)
  let dom (q : CuspCosets F Γ σ) : X F → ℂ :=
    Set.indicator K (fun _ => ((kernelBound * m q : ℝ) : ℂ))
  have hDomInt (q : CuspCosets F Γ σ) : Integrable (dom q) (volX F) := by
    apply (integrable_indicator_iff hKmeas).2
    exact integrableOn_const hKc.measure_ne_top
  have hPointBound (q : CuspCosets F Γ σ) (w : X F) :
      ‖f q w‖ ≤ ‖dom q w‖ := by
    by_cases hw : w ∈ K
    · have hterm := hmBound w hw s hσ₀s le_rfl q
      have hmul : ‖radialKernel F k₀ z w‖ * ‖eisTerm F Γ σ s w q‖ ≤ kernelBound * m q :=
        mul_le_mul (hKernelBound w) hterm (norm_nonneg _) hKernelBoundNonneg
      have hDomVal : ‖dom q w‖ = kernelBound * m q := by
        calc
          ‖dom q w‖ = |kernelBound * m q| := by
            simp [dom, hw, Complex.norm_real]
          _ = kernelBound * m q :=
            abs_of_nonneg (mul_nonneg hKernelBoundNonneg (hmNonneg q))
      calc
        ‖f q w‖ = ‖radialKernel F k₀ z w‖ * ‖eisTerm F Γ σ s w q‖ := by
          simp [f, norm_mul]
        _ ≤ kernelBound * m q := hmul
        _ = ‖dom q w‖ := hDomVal.symm
    · have hker : radialKernel F k₀ z w = 0 := by
        by_contra hne
        exact hw (hKsupport w hne)
      simp [f, dom, hw, hker]
  have hNormIntegralBound (q : CuspCosets F Γ σ) :
      ∫ w, ‖f q w‖ ∂(volX F) ≤ (volX F).real K * (kernelBound * m q) := by
    have hDomNormEq : (fun w => ‖dom q w‖) =
        Set.indicator K (fun _ => kernelBound * m q) := by
      funext w
      by_cases hw : w ∈ K
      · rw [Set.indicator_of_mem hw]
        calc
          ‖dom q w‖ = |kernelBound * m q| := by
            simp [dom, hw, Complex.norm_real]
          _ = kernelBound * m q :=
            abs_of_nonneg (mul_nonneg hKernelBoundNonneg (hmNonneg q))
      · simp [dom, hw]
    calc
      _ ≤ ∫ w, ‖dom q w‖ ∂(volX F) := by
        apply integral_mono_ae (hfInt q).norm (hDomInt q).norm
        exact Filter.Eventually.of_forall (hPointBound q)
      _ = (volX F).real K * (kernelBound * m q) := by
        rw [hDomNormEq, integral_indicator_const _ hKmeas]
        simp [smul_eq_mul]
  let Dtotal : ℝ := (volX F).real K * kernelBound
  have hDtotal : 0 ≤ Dtotal := by
    dsimp [Dtotal]
    positivity
  have hNormIntegralBound' (q : CuspCosets F Γ σ) :
      ∫ w, ‖f q w‖ ∂(volX F) ≤ Dtotal * m q := by
    simpa [Dtotal, mul_assoc] using hNormIntegralBound q
  have hNormSummable : Summable (fun q => ∫ w, ‖f q w‖ ∂(volX F)) := by
    refine (hmSum.mul_left Dtotal).of_norm_bounded ?_
    intro q
    rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg (f q w))]
    exact hNormIntegralBound' q
  letI : Countable ℚ := inferInstance
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have hOInjective : Function.Injective (fun x : 𝓞 F => (x : F)) := by
    intro x y h
    exact Subtype.ext h
  letI : Countable (𝓞 F) := hOInjective.countable
  let e₁ : (Fin 2 → Fin 2 → 𝓞 F) ≃ (Fin 2 → 𝓞 F × 𝓞 F) :=
    Equiv.piCongrRight (fun _ : Fin 2 => finTwoArrowEquiv (𝓞 F))
  let e₂ : (Fin 2 → 𝓞 F × 𝓞 F) ≃ ((𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F)) :=
    finTwoArrowEquiv (𝓞 F × 𝓞 F)
  let eMatrix : Matrix (Fin 2) (Fin 2) (𝓞 F) ≃
      ((𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F)) := e₁.trans e₂
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) :=
    Countable.of_equiv _ eMatrix.symm
  have hSLinj : Function.Injective
      (fun g : SL(2, 𝓞 F) => (g : Matrix (Fin 2) (Fin 2) (𝓞 F))) := by
    intro a b h
    exact Subtype.ext h
  letI : Countable (SL(2, 𝓞 F)) := hSLinj.countable
  letI : Countable Γ := inferInstance
  letI : Countable (CuspCosets F Γ σ) := by
    dsimp [CuspCosets]
    infer_instance
  have hInterchange : ∑' q, ∫ w, f q w ∂(volX F) =
      ∫ w, ∑' q, f q w ∂(volX F) :=
    integral_tsum_of_summable_integral_norm hfInt hNormSummable
  have hPointwise (w : X F) : radialKernel F k₀ z w * eisSeries F Γ σ s w =
      ∑' q, f q w := by
    by_cases hker : radialKernel F k₀ z w = 0
    · simp [eisSeries, f, hker]
    · have hwK := hKsupport w hker
      have htermSummable : Summable (fun q => eisTerm F Γ σ s w q) :=
        Summable.of_norm_bounded hmSum (fun q => hmBound w hwK s hσ₀s le_rfl q)
      rw [eisSeries]
      simp only [f]
      exact (htermSummable.tsum_mul_left (radialKernel F k₀ z w)).symm
  have hsmoothedTsum : smoothingOperator F k₀ (eisSeries F Γ σ s) z =
      ∑' q, ∫ w, f q w ∂(volX F) := by
    unfold smoothingOperator
    calc
      _ = ∫ w, ∑' q, f q w ∂(volX F) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun w => hPointwise w)
      _ = _ := hInterchange.symm
  have hTermAtCenter : Summable (fun q => eisTerm F Γ σ s z q) :=
    Summable.of_norm_bounded hmSum (fun q => hmBound z hKz s hσ₀s le_rfl q)
  calc
    smoothingOperator F k₀ (eisSeries F Γ σ s) z =
        ∑' q, ∫ w, f q w ∂(volX F) := hsmoothedTsum
    _ = ∑' q, radialTransform F k₀ (1 + 2 * s) * eisTerm F Γ σ s z q :=
      tsum_congr (fun q => smoothing_eisTerm_eigen k₀ Γ σ s q z)
    _ = radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z := by
      rw [eisSeries, ← hTermAtCenter.tsum_mul_left]

end ArtinPrimitiveRoots.A1.Spec
