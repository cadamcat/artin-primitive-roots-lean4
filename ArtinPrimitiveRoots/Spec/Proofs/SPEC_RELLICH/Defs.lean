import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

/-! Shared chart, localization, and calibration objects for SPEC-RELLICH. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

namespace RellichChart

/-- Match the Borel chart σ-algebra fixed in the upstream Euclidean H¹ API. -/
scoped instance rellichMeasurableSpace {ι : Type*} [Fintype ι] :
    MeasurableSpace (EuclideanSpace ℝ ι) := borel (EuclideanSpace ℝ ι)

scoped instance rellichBorelSpace {ι : Type*} [Fintype ι] :
    @BorelSpace (EuclideanSpace ℝ ι) _ rellichMeasurableSpace := ⟨rfl⟩

end RellichChart

open scoped RellichChart

namespace RellichEuclidean
export RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
  (h1 h1On h1ToL2 h1ToL2Grad h1OnToL2 grad
    isClosed_range_extendByZero isCompactOperator_h1OnToL2)
end RellichEuclidean

/-- The supported H¹ space is closed, so bounded test maps can be extended into it. -/
theorem rellich_h1On_closed {ι : Type*} [Fintype ι]
    (C : Set (EuclideanSpace ℝ ι)) (hC : MeasurableSet C) :
    IsClosed (RellichEuclidean.h1On C hC : Set
      ↥(RellichEuclidean.h1 (μ := (volume : Measure (EuclideanSpace ℝ ι))))) := by
  exact (RellichEuclidean.isClosed_range_extendByZero C hC).preimage
    (RellichEuclidean.h1ToL2 (μ := (volume : Measure (EuclideanSpace ℝ ι)))).continuous

instance rellich_h1On_complete {ι : Type*} [Fintype ι]
    (C : Set (EuclideanSpace ℝ ι)) (hC : MeasurableSet C) :
    CompleteSpace ↥(RellichEuclidean.h1On C hC) :=
  (rellich_h1On_closed C hC).completeSpace_coe

/-- Real Euclidean coordinates for the three variables at each infinite place. -/
abbrev RellichCoord (F : Type) [Field F] [NumberField F] :=
  EuclideanSpace ℝ (InfinitePlace F × Fin 3)

variable (F : Type) [Field F] [NumberField F]

/-- Convert the Euclidean chart to the existing complex-horizontal/real-height chart. -/
def rellichToCoord (p : RellichCoord F) : Coord F :=
  fun w => ((p (w, 0) : ℂ) + Complex.I * (p (w, 1) : ℂ), p (w, 2))

/-- The positive-height locus in real Euclidean coordinates. -/
def rellichPosSet : Set (RellichCoord F) := {p | ∀ w, 0 < p (w, 2)}

/-- Pull a localized test to the global chart and extend it by zero. -/
def rellichLocalized (ψ : X F → ℝ) (f : X F → ℂ) (p : RellichCoord F) : ℂ :=
  if p ∈ rellichPosSet F then
    (ψ (ptX F (rellichToCoord F p)) : ℂ) * f (ptX F (rellichToCoord F p))
  else 0

/-- Complex-valued chart L² with Lebesgue volume. -/
abbrev RellichChartL2 := Lp ℂ 2 (volume : Measure (RellichCoord F))

/-- Real-valued chart L² with Lebesgue volume. -/
abbrev RellichChartRealL2 := Lp ℝ 2 (volume : Measure (RellichCoord F))

/-- Inclusion of real L² into complex L², for any measure. -/
def rellichRealToComplex {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  Complex.ofRealCLM.compLpL 2 μ

/-- Recombine two real supported H¹ localizations after their L² inclusions. -/
def rellichRecombine {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : Set (EuclideanSpace ℝ ι)) (hC : MeasurableSet C)
    (A B : V →L[ℝ] ↥(RellichEuclidean.h1On C hC)) :
    V →L[ℝ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  (rellichRealToComplex (volume : Measure (EuclideanSpace ℝ ι))).comp
      ((RellichEuclidean.h1OnToL2 C hC).comp A) +
    Complex.I • (rellichRealToComplex (volume : Measure (EuclideanSpace ℝ ι))).comp
      ((RellichEuclidean.h1OnToL2 C hC).comp B)

/-- Gradient projection on the supported real H¹ chart space. -/
def rellichChartGradient {ι : Type*} [Fintype ι]
    (C : Set (EuclideanSpace ℝ ι)) (hC : MeasurableSet C) :
    ↥(RellichEuclidean.h1On C hC) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  (RellichEuclidean.h1ToL2Grad (μ := (volume : Measure (EuclideanSpace ℝ ι)))).comp
    (RellichEuclidean.h1On C hC).subtypeL

variable {F}

/-- The exact compact-overlap estimate extracted from T1, without freeness. -/
def RellichOverlapControl (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F)) : Prop :=
  ∀ K : Set (X F), IsCompact K →
    Set.Finite (overlapSet F Γ K K) ∧
    ∀ u : L2Space F D,
      ∫ z in K, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) ≤
        (overlapMultiplicity F Γ K : ℝ) * ‖u‖ ^ 2

/-- The unfolding equality extracted from T1. -/
def RellichUnfolding (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F)) : Prop :=
  ∀ f : X F → ℂ, Integrable f (volX F) →
    ∫ z in D, (∑' γ : Γ, f ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
      ∫ z, f z ∂(volX F)

/-- The portion of the T2 partition used for localization and reconstruction. -/
structure RellichPartition (Γ : Subgroup SL(2,𝓞 F)) (K : Set (X F))
    (ψ : X F → ℝ) : Prop where
  smooth : IsSmoothRealX F ψ
  compact : HasCompactSupportX F (fun z => (ψ z : ℂ))
  nonneg : ∀ z, 0 ≤ ψ z
  locallyFinite : ∀ z, ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
    {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0}.Finite
  partition : ∃ U : Set (X F), IsOpen U ∧ orbitSaturation F Γ K ⊆ U ∧
    ∀ z ∈ U, ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1

/-- Indicator multiplication, with the representative and contraction needed by T6. -/
def RellichIndicator (Γ : Subgroup SL(2,𝓞 F)) (D K : Set (X F))
    (I : L2Space F D →L[ℂ] L2Space F D) : Prop :=
  (∀ u, ‖I u‖ ≤ ‖u‖) ∧
    ∀ u, ∀ᵐ z ∂(volX F), z ∈ D →
      I u z = (orbitSaturation F Γ K).indicator (fun z => u z) z

/-- Local control of the geometric energy of every calibrated quotient test. -/
def RellichLocalEnergyBound (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) : Prop :=
  ∀ S : Set (X F), IsCompact S → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : testSubmodule F Γ,
      ∫ z in S, (‖(f : X F → ℂ) z‖ ^ 2 +
        ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) ∂(volX F) ≤
          C * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2)

/-- The calibrated test graph, as a linear map into the closed energy space. -/
def rellichTestVector {Γ : Subgroup SL(2,𝓞 F)} {D : Set (X F)}
    {E : FAEnergySpace (L2Space F D) (GradientL2Space F D)}
    (e : EnergyContext F Γ D E) : testSubmodule F Γ →ₗ[ℂ] E.V :=
  (energyGraphMap e.toL2 e.gradL2).codRestrict E.V (by
    intro f
    rw [e.graph_eq]
    exact (energyGraphMap e.toL2 e.gradL2).range.le_topologicalClosure ⟨f, rfl⟩)

/-- A supported real/imaginary test localization, including its actual gradient representatives.
The gradient fields rule out arbitrary uncalibrated H¹ maps with the same mass component. -/
structure RellichTestChart (Γ : Subgroup SL(2,𝓞 F)) (ψ : X F → ℝ) where
  support : Set (RellichCoord F)
  compact : IsCompact support
  re : testSubmodule F Γ →ₗ[ℝ] ↥(RellichEuclidean.h1On support compact.measurableSet)
  im : testSubmodule F Γ →ₗ[ℝ] ↥(RellichEuclidean.h1On support compact.measurableSet)
  re_rep : ∀ f, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
    RellichEuclidean.h1OnToL2 support compact.measurableSet (re f) p =
      (rellichLocalized F ψ (f : X F → ℂ) p).re
  im_rep : ∀ f, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
    RellichEuclidean.h1OnToL2 support compact.measurableSet (im f) p =
      (rellichLocalized F ψ (f : X F → ℂ) p).im
  re_grad_rep : ∀ f, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
    rellichChartGradient support compact.measurableSet (re f) p =
      RellichEuclidean.grad (fun q => (rellichLocalized F ψ (f : X F → ℂ) q).re) p
  im_grad_rep : ∀ f, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
    rellichChartGradient support compact.measurableSet (im f) p =
      RellichEuclidean.grad (fun q => (rellichLocalized F ψ (f : X F → ℂ) q).im) p
  re_I : ∀ f, re (Complex.I • f) = -im f
  im_I : ∀ f, im (Complex.I • f) = re f

end ArtinPrimitiveRoots.A1.Spec
