import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.PuncturedHalfPlane
import ArtinPrimitiveRoots.A2.ZeroFree.Missing
import ArtinPrimitiveRoots.A2.Proofs.A2_PRINCIPAL_INPUTS.LSeries
import ArtinPrimitiveRoots.Hecke.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000
 open NumberField IsDedekindDomain MeasureTheory ClassFieldTheory Filter Asymptotics
 open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

section EulerProductDictionary
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η) (HA : HeckeAnalysis F)
  (HC : EulerCorrection R η U)

/-- `prop:euler-product` with the canonical complete/incomplete continuation dictionary supplied
explicitly; its analytic proof remains an obligation (05:407–433; 06:165–185). -/
def eulerProductWithDictionaryStatement
    (K : IncompleteDictionary η U HA) : Prop :=
  (∀ u h s, 997 / 1000 < s.re →
    (K.incomplete u h).value s = HA.LS S (η * (U.kummer u)⁻¹) s) ∧
  EulerHypotheses R η → HasPoHProduct R η U HC ∧
    (∀ u ξ w z, initialRegion ξ w z →
      calF R η U u ξ w z = HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
        HC.H u ![ξ, w, z] / HA.LS S (η * (U.kummer u)⁻¹) ξ) ∧
    ((∀ v hv p, eulerNeighborhood p →
      ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
        ∀ p, eulerNeighborhood p → HC.H U.one p ≠ 0)

/-- Explicit dictionary-consuming producer for the §5 Euler product; this is the coherence edge
from `HeckeAnalysis` to the stored incomplete continuation values. -/
theorem prop_euler_product_with_dictionary (K : IncompleteDictionary η U HA) :
    eulerProductWithDictionaryStatement R η U HA HC K := by
  sorry

end EulerProductDictionary

/-! ## §5–6 endpoint inputs and the frozen boundary adapter -/

/-- Endpoint package consumed by the Mellin identity. `H` is the actual Euler correction and `L`
the actual incomplete Hecke series (06:691–752). -/
structure MellinInputs (H L : ℂ → ℂ) : Prop where
  H_holomorphic : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re}
  H_nonzero : ∀ s : ℂ, 998 / 1000 < s.re → H s ≠ 0
  H_bound : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B
  L_holomorphic : DifferentiableOn ℂ L {s : ℂ | 1 < s.re}
  L_nonzero : ∀ s : ℂ, 1 < s.re → L s ≠ 0
  L_reciprocal_bound : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B
  small : ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ,
    0 < Z → Z ≤ 1 → ‖fEta H L Z‖ ≤ C * Z ^ A0
  large : ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z : ℝ,
    Z0 ≤ Z → ‖fEta H L Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ))

/-- Signal endpoint contract with the split Gauss input required by the corrected
`prop:probe-low` consumer (`sol-gate-a2b`, 06:682–707). -/
def signalBoundsStatement
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
    {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
    {v0 : InfinitePlace F} (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (sd : S.SelfDualMeasure A) (W : PoissonWeights (S := S)) (η : HeckeChar F)
    (U : FrequencyData S D η) (HA : HeckeAnalysis F) (HC : EulerCorrection R η U) : Prop :=
  GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η →
    EulerHypotheses R η →
    (∀ v hv p, eulerNeighborhood p →
      ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
    WeightSpec R sd W →
      ContinuousOn (principalSignal R η U HA HC) (Set.Ioi 0) ∧
      (∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) ∧
      ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z, 0 < Z → Z ≤ 1 →
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ A0

/-- Producer obligation for the actual §5 `Hη` and §6 signal endpoints to supply MellinInputs.
The premises are the outputs of `po:H-eta` and `zf:f-bounds` (06:682–752). -/
def principalMellinInputsStatement
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
    {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
    {v0 : InfinitePlace F} (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (sd : S.SelfDualMeasure A) (W : PoissonWeights (S := S)) (η : HeckeChar F)
    (U : FrequencyData S D η) (HA : HeckeAnalysis F) (HC : EulerCorrection R η U) : Prop :=
  GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η →
    EulerHypotheses R η →
    (∀ v hv p, eulerNeighborhood p →
      ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
    WeightSpec R sd W → MellinInputs (Heta R η U HC) (HA.LS S η)

/-- The §5–6 result shapes assemble into the endpoint package by narrowing the holomorphic strip
and transferring the bound; this adapter is proved. -/
theorem mellinInputs_of_nodes
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
    {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
    {v0 : InfinitePlace F} (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (sd : S.SelfDualMeasure A) (W : PoissonWeights (S := S)) (η : HeckeChar F)
    (U : FrequencyData S D η) (HA : HeckeAnalysis F) (HC : EulerCorrection R η U)
    (hH : DifferentiableOn ℂ (Heta R η U HC)
        {s | 998 / 1000 - 1 / 100000 < s.re} ∧
      (∀ s, 998 / 1000 - 1 / 100000 < s.re → Heta R η U HC s ≠ 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ s, 998 / 1000 - 1 / 100000 < s.re →
        ‖Heta R η U HC s‖ ≤ C)
    (hL : DifferentiableOn ℂ (HA.LS S η) {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → HA.LS S η s ≠ 0)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(HA.LS S η s)⁻¹‖ ≤ B)
    (hends : ContinuousOn (principalSignal R η U HA HC) (Set.Ioi 0) ∧
      (∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) ∧
      ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z, 0 < Z → Z ≤ 1 →
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ A0) :
    MellinInputs (Heta R η U HC) (HA.LS S η) := by
  refine ⟨hH.1.mono (by intro s hs; dsimp at hs ⊢; linarith), ?_, ?_, hL, hL0, hLb,
    hends.2.2, hends.2.1⟩
  · intro s hs
    exact hH.2.1 s (by linarith)
  · obtain ⟨C, hC, hb⟩ := hH.2.2
    exact ⟨C, fun s hs => hb s (by linarith)⟩

/-- Producer obligation for the actual principal signal to satisfy the endpoint package; it
keeps the corrected split input visible across `zf:f-bounds` (06:682–752). -/
theorem principal_mellin_inputs
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
    {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
    {v0 : InfinitePlace F} (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (sd : S.SelfDualMeasure A) (W : PoissonWeights (S := S)) (η : HeckeChar F)
    (U : FrequencyData S D η) (HA : HeckeAnalysis F) (HC : EulerCorrection R η U) :
    principalMellinInputsStatement R sd W η U HA HC := by
  intro hSplit hEuler hloc hWeight
  have hH := po_H_eta_properties R η U HC hEuler hloc
  have hEnds := zf_f_bounds R sd W η U HA HC hSplit hEuler hloc hWeight
  have hL := principalLS_right_half_plane_inputs (S := S) η HA hEuler.1
  obtain ⟨B, hB, hLrecip⟩ := hL.2.2
  exact mellinInputs_of_nodes R sd W η U HA HC
    hH hL.1 hL.2.1 ⟨B, hLrecip⟩ hEnds

/-- Mellin transform identity and analytic continuation for the actual `fEta`/amplitude pair;
the line identity is stated explicitly (06:691–752). -/
def mellinIdentificationStatement : Prop := ∀ H L : ℂ → ℂ, MellinInputs H L →
  DifferentiableOn ℂ (mellinT (fEta H L)) {s : ℂ | 1 - 1 / 20000 < s.re} ∧
    (∀ t : ℝ, mellinT (fEta H L) (2 + t * Complex.I) = amplitude H L (2 + t * Complex.I)) ∧
    ∀ P : Finset ℂ, ∀ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({s : ℂ | 1 - 1 / 20000 < s.re} \ ↑P) →
      (∀ s : ℂ, 1 < s.re → Λ s = L s) →
      ∀ s : ℂ, 1 - 1 / 20000 < s.re → s ∉ P → Λ s ≠ 0

/-- New analytic producer obligation for `mellinIdentificationStatement` (06:691–752). -/
theorem mellin_identification_from_inputs : mellinIdentificationStatement := by
  intro H L hI
  let p : ℝ := (7 : ℝ) / 15 - 1 / 20000
  have hlarge : ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ‖fEta H L Z‖ ≤ C * Real.rpow Z (7 / 15 - 1 / 20000) := by
    obtain ⟨C, Z0, hC, hZ0, hbound⟩ := hI.large
    exact ⟨C, Z0, hC, le_trans (by norm_num) hZ0, hbound⟩
  have hcont := fEta_continuousOn_of_bounds H L hI.H_holomorphic hI.L_holomorphic
    hI.L_nonzero hI.H_bound hI.L_reciprocal_bound
  have hloc : LocallyIntegrableOn (fEta H L) (Set.Ioi 0) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have htop : fEta H L =O[atTop] (fun Z : ℝ => Z ^ p) := by
    obtain ⟨C, Z0, hC, hZ0, hbound⟩ := hI.large
    apply IsBigO.of_bound (C + 1)
    filter_upwards [eventually_ge_atTop Z0] with Z hZ
    have hZpos : 0 < Z := lt_of_lt_of_le (by linarith) hZ
    have hpow : 0 ≤ Z ^ p := Real.rpow_nonneg hZpos.le _
    calc
      ‖fEta H L Z‖ ≤ C * Z ^ p := by simpa [p] using hbound Z hZ
      _ ≤ (C + 1) * Z ^ p :=
        mul_le_mul_of_nonneg_right (by linarith) hpow
      _ = (C + 1) * ‖Z ^ p‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow]
  have hbot (A0 : ℝ) (hA0 : 0 < A0) :
      fEta H L =O[𝓝[>] (0 : ℝ)] (fun Z : ℝ => Z ^ A0) := by
    obtain ⟨C, hC, hbound⟩ := hI.small A0 hA0
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with Z hZ hZ1
    have hZpos : 0 < Z := by simpa using hZ
    have hZle : Z ≤ 1 := by simpa using hZ1
    have hsmall := hbound Z hZpos hZle
    have hpow : 0 ≤ Z ^ A0 := Real.rpow_nonneg hZpos.le _
    calc
      ‖fEta H L Z‖ ≤ C * Z ^ A0 := hsmall
      _ = C * ‖Z ^ A0‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow]
  have hdifferentiable : DifferentiableOn ℂ (mellinT (fEta H L))
      {s : ℂ | 1 - 1 / 20000 < s.re} := by
    intro s hs
    let A0 : ℝ := max 0 (s.re - 8 / 15) + 1
    have hA0 : 0 < A0 := by
      dsimp [A0]
      linarith [le_max_left 0 (s.re - 8 / 15)]
    have hAgt : s.re - 8 / 15 < A0 := by
      dsimp [A0]
      linarith [le_max_right 0 (s.re - 8 / 15)]
    have hqre : (-Cstar s).re = 8 / 15 - s.re := by simp [Cstar]
    change 1 - 1 / 20000 < s.re at hs
    have htop' : fEta H L =O[atTop] (fun Z : ℝ => Z ^ (-(-p))) := by
      simpa only [neg_neg] using htop
    have hbot' : fEta H L =O[𝓝[>] (0 : ℝ)]
        (fun Z : ℝ => Z ^ (-(-A0))) := by
      simpa only [neg_neg] using hbot A0 hA0
    have hqtop : (-Cstar s).re < -p := by
      rw [hqre]
      dsimp [p]
      linarith [hs]
    have hqbot : -A0 < (-Cstar s).re := by
      rw [hqre]
      linarith [hAgt]
    have hmellin : DifferentiableAt ℂ (mellin (fEta H L)) (-Cstar s) :=
      mellin_differentiableAt_of_isBigO_rpow (a := -p) (b := -A0)
        hloc htop' hqtop hbot' hqbot
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => -Cstar z) s := by
      fun_prop [Cstar]
    have hAt : DifferentiableAt ℂ (mellinT (fEta H L)) s := by
      change DifferentiableAt ℂ (mellin (fEta H L) ∘ (fun z : ℂ => -Cstar z)) s
      exact hmellin.comp s hcomp
    exact hAt.differentiableWithinAt
  have hline : ∀ t : ℝ,
      mellinT (fEta H L) (2 + t * Complex.I) = amplitude H L (2 + t * Complex.I) :=
    fun t => mellinT_fEta_line_eq_amplitude_of_bounds H L hI.H_holomorphic
      hI.L_holomorphic hI.L_nonzero hI.H_bound hI.L_reciprocal_bound hlarge t
  refine ⟨hdifferentiable, hline, ?_⟩
  exact mellin_identification H L hI.H_holomorphic hI.H_nonzero hI.H_bound
    hI.L_holomorphic hI.L_nonzero hI.L_reciprocal_bound hI.small hlarge

/-- Boundary-width version of Mellin identification. It matches the frozen `δ₀ = 10⁻⁶`
continuation domain in `Hecke/Boundary.lean`; its analytic proof is a separate obligation
(`sol-gate-a2b`, 06:691–764). -/
def mellinIdentificationNarrowStatement : Prop := ∀ H L : ℂ → ℂ, MellinInputs H L →
  ∀ P : Finset ℂ, ∀ Λ : ℂ → ℂ,
    DifferentiableOn ℂ Λ ({s : ℂ | 1 - a2Delta0 < s.re} \ ↑P) →
    (∀ s : ℂ, 1 < s.re → Λ s = L s) →
    ∀ s : ℂ, 1 - a2Delta0 < s.re → s ∉ P → Λ s ≠ 0

/-- New analytic producer obligation on the frozen narrow half-plane. The wider `1/20000` result
does not itself accept a continuation known only on this smaller domain. -/
theorem mellin_identification_narrow : mellinIdentificationNarrowStatement := by
  intro H L hInputs P Λ hΛ hΛL s hs hsP
  let M : ℂ → ℂ := mellinT (fEta H L)
  let E : ℂ → ℂ := fun z => Complex.exp ((z - 5 / 6) ^ 2) * H z
  let D₁ : Set ℂ := {z | 1 < z.re}
  let D₀ : Set ℂ := {z | 1 - a2Delta0 < z.re} \ ↑P
  obtain ⟨hMdiff, hMline, _⟩ := mellin_identification_from_inputs H L hInputs
  have hExpDiff : Differentiable ℂ (fun z : ℂ => Complex.exp ((z - 5 / 6) ^ 2)) := by
    fun_prop
  have hD₁open : IsOpen D₁ := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hD₁pre : IsPreconnected D₁ := by
    simpa [D₁] using (convex_halfSpace_re_gt (1 : ℝ)).isPreconnected
  have hMdiff₁ : DifferentiableOn ℂ M D₁ := by
    apply hMdiff.mono
    intro z hz
    dsimp [D₁] at hz ⊢
    exact lt_trans (by norm_num : (1 : ℝ) - 1 / 20000 < 1) hz
  have hLdiff₁ : DifferentiableOn ℂ L D₁ := by
    simpa [D₁] using hInputs.L_holomorphic
  have hHdiff₁ : DifferentiableOn ℂ H D₁ := by
    apply hInputs.H_holomorphic.mono
    intro z hz
    dsimp [D₁] at hz ⊢
    linarith
  have hEdiff₁ : DifferentiableOn ℂ E D₁ := by
    dsimp [E]
    exact hExpDiff.differentiableOn.mul hHdiff₁
  have hMprodAnalytic₁ : AnalyticOnNhd ℂ (fun z => M z * L z) D₁ := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hD₁open).2
    exact hMdiff₁.mul hLdiff₁
  have hEanalytic₁ : AnalyticOnNhd ℂ E D₁ :=
    (Complex.analyticOnNhd_iff_differentiableOn hD₁open).2 hEdiff₁
  let line : ℝ → ℂ := fun t => (2 : ℂ) + (t : ℂ) * Complex.I
  have hlineCont : ContinuousAt line 0 := by
    fun_prop
  have hlineNe (t : ℝ) (ht : t ≠ 0) : line t ≠ (2 : ℂ) := by
    intro heq
    have him := congrArg Complex.im heq
    exact ht (by simpa [line] using him)
  have hlineTendsto : Tendsto line (𝓝[≠] (0 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont := hlineCont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      simpa [line] using hcont
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hlineNe t (by simpa using ht)
  have hlineEq (t : ℝ) : M (line t) * L (line t) = E (line t) := by
    have hM := hMline t
    have hL0 := hInputs.L_nonzero (line t) (by simp [line])
    calc
      M (line t) * L (line t) = amplitude H L (line t) * L (line t) := by
        simpa [M, line] using congrArg (fun z : ℂ => z * L (2 + t * Complex.I)) hM
      _ = E (line t) := by
        simp [amplitude, E]
        field_simp [hL0]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), M z * L z = E z := by
    rw [frequently_iff]
    intro V hV
    have hlineV : ∀ᶠ t in 𝓝[≠] (0 : ℝ), line t ∈ V := hlineTendsto hV
    obtain ⟨t, htV⟩ := hlineV.exists
    exact ⟨line t, htV, hlineEq t⟩
  have hprodEq₁ := hMprodAnalytic₁.eqOn_of_preconnected_of_frequently_eq
    hEanalytic₁ hD₁pre (by norm_num [D₁]) hfreq
  have hprodEq₁' : ∀ z : ℂ, 1 < z.re → M z * L z = E z := by
    intro z hz
    exact hprodEq₁ (by simpa [D₁] using hz)

  have hPfinite : (↑P : Set ℂ).Finite := by simp
  have hPcount : (↑P : Set ℂ).Countable := hPfinite.countable
  have hPopen : IsOpen ((↑P : Set ℂ)ᶜ) := hPfinite.isClosed.isOpen_compl
  have hD₀open : IsOpen D₀ := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter hPopen
  have hD₀pre : IsPreconnected D₀ := by
    have hUopen : IsOpen {z : ℂ | 1 - a2Delta0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hUconv : Convex ℝ {z : ℂ | 1 - a2Delta0 < z.re} :=
      convex_halfSpace_re_gt _
    have hUne : ({z : ℂ | 1 - a2Delta0 < z.re} : Set ℂ).Nonempty :=
      ⟨2, by norm_num [a2Delta0]⟩
    have hpath := convex_open_diff_countable_isPathConnected hUconv hUopen hUne hPcount
    simpa [D₀] using hpath.isConnected.isPreconnected
  have hwideNarrow : {z : ℂ | 1 - 1 / 20000 < z.re} ⊇
      {z : ℂ | 1 - a2Delta0 < z.re} := by
    intro z hz
    exact lt_trans (by norm_num [a2Delta0] : (1 : ℝ) - 1 / 20000 < 1 - a2Delta0) hz
  have hMdiff₀ : DifferentiableOn ℂ M D₀ := by
    apply hMdiff.mono
    intro z hz
    exact hwideNarrow (by simpa [D₀] using hz.1)
  have hHdiff₀ : DifferentiableOn ℂ H D₀ := by
    apply hInputs.H_holomorphic.mono
    intro z hz
    have hm : (998 / 1000 : ℝ) < 1 - a2Delta0 := by norm_num [a2Delta0]
    exact lt_trans hm (by simpa [D₀] using hz.1)
  have hEdiff₀ : DifferentiableOn ℂ E D₀ := by
    dsimp [E]
    exact hExpDiff.differentiableOn.mul hHdiff₀
  have hMprodAnalytic₀ : AnalyticOnNhd ℂ (fun z => M z * Λ z) D₀ := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hD₀open).2
    exact hMdiff₀.mul hΛ
  have hEanalytic₀ : AnalyticOnNhd ℂ E D₀ :=
    (Complex.analyticOnNhd_iff_differentiableOn hD₀open).2 hEdiff₀
  have hD₁openAt (z : ℂ) (hz : z ∈ D₁) : D₁ ∈ 𝓝 z := hD₁open.mem_nhds hz
  have hPopenAt (z : ℂ) (hz : z ∉ (↑P : Set ℂ)) :
      (↑P : Set ℂ)ᶜ ∈ 𝓝 z := hPopen.mem_nhds hz
  obtain ⟨z₀, hz₀P, hz₀D₁⟩ :=
    hPcount.dense_compl ℝ |>.exists_mem_open hD₁open ⟨2, by norm_num [D₁]⟩
  have hevent : (fun z => M z * Λ z) =ᶠ[𝓝 z₀] E := by
    filter_upwards [hD₁openAt z₀ hz₀D₁, hPopenAt z₀ hz₀P] with z hzD₁ hzP
    calc
      M z * Λ z = M z * L z := by rw [hΛL z (by simpa [D₁] using hzD₁)]
      _ = E z := hprodEq₁' z (by simpa [D₁] using hzD₁)
  have hz₀D₀ : z₀ ∈ D₀ := by
    have hmargin : 1 - a2Delta0 < (1 : ℝ) := by norm_num [a2Delta0]
    exact ⟨lt_trans hmargin (by simpa [D₁] using hz₀D₁), hz₀P⟩
  have hprodEq₀ := hMprodAnalytic₀.eqOn_of_preconnected_of_eventuallyEq
    hEanalytic₀ hD₀pre hz₀D₀ hevent
  have hprodAt : M s * Λ s = E s := hprodEq₀ ⟨hs, hsP⟩
  have hEnonzero : E s ≠ 0 := by
    apply mul_ne_zero (Complex.exp_ne_zero _)
    exact hInputs.H_nonzero s (lt_trans (by norm_num [a2Delta0]) hs)
  intro hΛzero
  apply hEnonzero
  rw [← hprodAt, hΛzero, mul_zero]

/-- Deleted finite Euler factors relating the actual S-incomplete Hecke series to the ray-class
series. Constructing this relation needs the modulus dictionary (06:754–764). -/
structure RayDeletion (S : SData F CE condη) (χ : HeckeChar F)
    (m : RayClassModulus F) (η : RayClassGroup m →* ℂˣ) (HA : HeckeAnalysis F) where
  factor : ℂ → ℂ
  factor_holomorphic : Differentiable ℂ factor
  factor_nonzero : ∀ s : ℂ, 0 < s.re → factor s ≠ 0
  agrees : ∀ s : ℂ, 1 < s.re →
    HA.LS S χ s = ArtinPrimitiveRoots.Hecke.LSeriesRay η s * factor s

/-- Conditional Mellin-to-boundary adapter. The frozen `δ₀` domain and finite ray deletion factor
are used explicitly. The proof introduces no analytic axiom and leaves the frozen statements
untouched. -/
theorem boundary_from_mellin (hM : mellinIdentificationNarrowStatement)
    (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    {CEc : ℕ} {condχ : Ideal (𝓞 (CyclotomicField n ℚ))}
    {S : SData (CyclotomicField n ℚ) CEc condχ}
    (χ : HeckeChar (CyclotomicField n ℚ))
    (m : RayClassModulus (CyclotomicField n ℚ)) (η : RayClassGroup m →* ℂˣ)
    (HA : HeckeAnalysis (CyclotomicField n ℚ)) (H : ℂ → ℂ)
    (hInputs : MellinInputs H (HA.LS S χ)) (RD : RayDeletion S χ m η HA)
    (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ
      ({s : ℂ | 1 - a2Delta0 < s.re} \ {s | η = 1 ∧ s = 1}))
    (hL : ∀ s : ℂ, 1 < s.re → Λ s = ArtinPrimitiveRoots.Hecke.LSeriesRay η s) :
    ∀ s : ℂ, 1 - a2Delta0 < s.re → (η ≠ 1 ∨ s ≠ 1) → Λ s ≠ 0 := by
  let P : Finset ℂ := if η = 1 then {1} else ∅
  have hP : (↑P : Set ℂ) = {s | η = 1 ∧ s = 1} := by
    ext s
    by_cases hη : η = 1 <;> simp [P, hη]
  have hd : DifferentiableOn ℂ (fun s => Λ s * RD.factor s)
      ({s : ℂ | 1 - a2Delta0 < s.re} \ ↑P) := by
    rw [hP]
    exact hΛ.mul RD.factor_holomorphic.differentiableOn
  have he : ∀ s : ℂ, 1 < s.re → Λ s * RD.factor s = HA.LS S χ s := by
    intro s hs
    rw [hL s hs]
    exact (RD.agrees s hs).symm
  intro s hs hex
  have hp : s ∉ P := by
    rw [← Finset.mem_coe, hP]
    intro hpole
    rcases hex with hn | hn
    · exact hn hpole.1
    · exact hn hpole.2
  have hn := hM H (HA.LS S χ) hInputs P (fun s => Λ s * RD.factor s) hd he s hs hp
  intro hz
  exact hn (by rw [hz, zero_mul])

end ArtinPrimitiveRoots.A2
