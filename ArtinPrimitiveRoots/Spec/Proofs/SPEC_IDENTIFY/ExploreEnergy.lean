import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise NNReal

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

set_option maxHeartbeats 10000000 in
private theorem probe_bounded_smooth_energy_repr
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (w : X F → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hInv : IsGammaInvariant F Γ w) (hSmooth : IsSmoothX F w)
    (hBound : ∀ z, ‖w z‖ ≤ B)
    (hGradBound : ∀ z, ‖fullGradient F w z‖ ≤ B)
    (hWmeas : AEStronglyMeasurable w ((volX F).restrict D))
    (hGradMeas : AEStronglyMeasurable (fullGradient F w) ((volX F).restrict D)) :
    ∃ x : E.V,
      (∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z) ∧
      (∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z) := by
  classical
  let μ := (volX F).restrict D
  have hμfinite : μ Set.univ < ⊤ := by
    simpa [μ, Measure.restrict_apply_univ] using spec_finiteVolume_any_fd Γ D hD
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  let hwLp : MemLp w 2 μ := MemLp.of_bound hWmeas B
    (Filter.Eventually.of_forall fun z => hBound z)
  let hgradLp : MemLp (fullGradient F w) 2 μ := MemLp.of_bound hGradMeas B
    (Filter.Eventually.of_forall fun z => hGradBound z)
  let wL2 : L2Space F D := hwLp.toLp w
  let gradL2 : GradientL2Space F D := hgradLp.toLp (fullGradient F w)
  have hwAE : ∀ᵐ z ∂(volX F), z ∈ D → wL2 z = w z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).1 hwLp.coeFn_toLp
  have hgradAE : ∀ᵐ z ∂(volX F), z ∈ D → gradL2 z = fullGradient F w z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).1 hgradLp.coeFn_toLp
  obtain ⟨x, hMx, hGrx⟩ := T5_cutoff Γ D hD E e w B hB hInv hSmooth
    hBound hGradBound wL2 gradL2 hwAE hgradAE
  refine ⟨x, ?_, ?_⟩
  · filter_upwards [hwAE] with z hz
    intro hzD
    rw [hMx]
    exact hz hzD
  · filter_upwards [hgradAE] with z hz
    intro hzD
    rw [hGrx]
    exact hz hzD

end ArtinPrimitiveRoots.A1.Spec
