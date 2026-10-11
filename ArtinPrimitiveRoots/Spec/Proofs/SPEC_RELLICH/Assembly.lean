import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.orbitRestrictedMass_eq_indicator
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.quotient_to_chart_finite_overlap
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.localized_chart_H1_membership
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.localized_chart_H1_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.localized_chart_extension
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.complex_chart_rellich_compact
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.periodization_L2_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.rellich_compact_of_test_bound

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F]

/-- Recombination has the original localized complex representative on the test graph.
Uses the two test-chart mass
representatives and the extension identities; this is the representative glue for T6. -/
theorem rellich_recombine_test_rep
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (ψ : X F → ℝ) (c : RellichTestChart Γ ψ)
    (A B : E.V →L[ℝ] ↥(RellichEuclidean.h1On c.support c.compact.measurableSet))
    (hA : ∀ f, A (rellichTestVector e f) = c.re f)
    (hB : ∀ f, B (rellichTestVector e f) = c.im f)
    (L : E.V →L[ℂ] RellichChartL2 F)
    (hL : L.restrictScalars ℝ = rellichRecombine c.support c.compact.measurableSet A B) :
    ∀ f : testSubmodule F Γ, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
      L (rellichTestVector e f) p = rellichLocalized F ψ (f : X F → ℂ) p := by
  intro f
  let u := RellichEuclidean.h1OnToL2 c.support c.compact.measurableSet (c.re f)
  let v := RellichEuclidean.h1OnToL2 c.support c.compact.measurableSet (c.im f)
  let J := rellichRealToComplex (volume : Measure (RellichCoord F))
  have hLf : L (rellichTestVector e f) = J u + Complex.I • J v := by
    have h := congrArg (fun T => T (rellichTestVector e f)) hL
    simpa [rellichRecombine, hA f, hB f, J, u, v] using h
  rw [hLf]
  filter_upwards [Lp.coeFn_add (J u) (Complex.I • J v), Lp.coeFn_smul Complex.I (J v),
    Complex.ofRealCLM.coeFn_compLpL (p := 2) u,
    Complex.ofRealCLM.coeFn_compLpL (p := 2) v, c.re_rep f, c.im_rep f]
    with p hadd hsmul hu hv hre him
  change (J u + Complex.I • J v) p = _
  rw [hadd]
  change J u p + (Complex.I • J v) p = _
  rw [hsmul]
  change J u p + Complex.I * J v p = _
  change J u p = (u p : ℂ) at hu
  change J v p = (v p : ℂ) at hv
  rw [hu, hv]
  change u p = _ at hre
  change v p = _ at him
  rw [hre, him]
  simpa only [mul_comm Complex.I] using Complex.re_add_im (rellichLocalized F ψ (f : X F → ℂ) p)

end ArtinPrimitiveRoots.A1.Spec
