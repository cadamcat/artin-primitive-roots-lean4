import ArtinPrimitiveRoots.A2.ZeroFree.Missing
import ArtinPrimitiveRoots.Hecke.Boundary

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory ClassFieldTheory
open scoped Classical
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
    Z0 ≤ Z → ‖fEta H L Z‖ ≤ C * Z ^ (7 / 15 - 1 / 20000)

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
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ (7 / 15 - 1 / 20000)) ∧
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
        ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ (7 / 15 - 1 / 20000)) ∧
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
  sorry

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
  sorry

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
  sorry

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
