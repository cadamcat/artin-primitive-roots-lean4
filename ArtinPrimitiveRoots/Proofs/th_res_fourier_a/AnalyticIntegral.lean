import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
open MeasureTheory NumberField Set
open scoped Classical BoundedContinuousFunction
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

lemma psiC_norm_one (z : ℂ) : ‖ArtinPrimitiveRoots.A1.psiC z‖ = 1 := by
  simp [ArtinPrimitiveRoots.A1.psiC, Complex.norm_exp]

lemma psiInf_norm_one {F : Type} [Field F] [NumberField F] (ν : F)
    (x : InfinitePlace F → ℂ) : ‖psiInf ν x‖ = 1 := by
  simp [psiInf, psiC_norm_one]

private theorem boundedContinuousFunction_integrable {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X →ᵇ ℂ) :
    Integrable (fun x => f x) μ := by
  apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
  filter_upwards [] with x
  exact f.norm_coe_le_norm x

noncomputable def boundedIntegralCLM {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℂ) →L[ℂ] ℂ := by
  let L : (X →ᵇ ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f : X →ᵇ ℂ => ∫ x : X, f x ∂μ
    map_add' := fun f g => by
      change (∫ x : X, f x + g x ∂μ) = _
      exact integral_add (boundedContinuousFunction_integrable μ f)
        (boundedContinuousFunction_integrable μ g)
    map_smul' := fun c f => by
      change (∫ x : X, c • f x ∂μ) = _
      exact integral_smul c (fun x : X => f x) }
  exact L.mkContinuous (μ.real univ) (by
    intro f
    have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ :=
      Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
    have hi := norm_integral_le_of_norm_le_const hbound
    calc
      ‖L f‖ = ‖∫ x, f x ∂μ‖ := rfl
      _ ≤ ‖f‖ * μ.real univ := hi
      _ = μ.real univ * ‖f‖ := by ring)

@[simp]
theorem boundedIntegralCLM_apply {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℂ) :
    boundedIntegralCLM μ f = ∫ x, f x ∂μ := rfl

noncomputable def boundedMulRightCLM {X : Type*} [TopologicalSpace X]
    (ψ : X →ᵇ ℂ) : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ) := by
  let L : (X →ᵇ ℂ) →ₗ[ℂ] (X →ᵇ ℂ) := {
    toFun := fun f => f * ψ
    map_add' := by intro f g; ext x; simp [add_mul]
    map_smul' := by intro c f; ext x; simp [smul_eq_mul] }
  exact L.mkContinuous ‖ψ‖ (by
    intro f
    calc
      ‖L f‖ = ‖f * ψ‖ := rfl
      _ ≤ ‖f‖ * ‖ψ‖ := norm_mul_le _ _
      _ = ‖ψ‖ * ‖f‖ := by ring)

@[simp]
theorem boundedMulRightCLM_apply {X : Type*} [TopologicalSpace X] (ψ f : X →ᵇ ℂ) :
    boundedMulRightCLM ψ f = f * ψ := rfl

theorem analytic_boundedIntegral {K Y : Type*} [TopologicalSpace K] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (p : C(Y, K)) (ψ : Y →ᵇ ℂ)
    (u : ℂ → K →ᵇ ℂ) {U : Set ℂ} (hu : AnalyticOnNhd ℂ u U) :
    AnalyticOnNhd ℂ (fun s =>
      boundedIntegralCLM μ (boundedMulRightCLM ψ
        (BoundedContinuousFunction.compContinuousCLM ℂ ℂ p (u s)))) U := by
  let L : (K →ᵇ ℂ) →L[ℂ] ℂ :=
    (boundedIntegralCLM μ).comp
      ((boundedMulRightCLM ψ).comp (BoundedContinuousFunction.compContinuousCLM ℂ ℂ p))
  change AnalyticOnNhd ℂ (L ∘ u) U
  exact L.comp_analyticOnNhd hu

lemma continuous_psiInf {F : Type} [Field F] [NumberField F] (ν : F) :
    Continuous (fun x : InfinitePlace F → ℂ => psiInf ν x) := by
  simp only [psiInf, ArtinPrimitiveRoots.A1.psiC]
  fun_prop

def psiInfBounded {F : Type} [Field F] [NumberField F]
    (Q : Set (InfinitePlace F → ℂ)) (ν : F) : Q →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => psiInf ν (x : InfinitePlace F → ℂ))
    ((continuous_psiInf ν).comp continuous_subtype_val) 1
    (fun x => by simp [psiInf_norm_one])

end ArtinPrimitiveRoots.A1.Theta
