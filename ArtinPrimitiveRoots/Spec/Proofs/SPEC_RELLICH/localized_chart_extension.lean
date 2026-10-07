import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Extend bounded test localizations over the closed energy graph and retain I compatibility.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:320. Uses localized_chart_H1_bound and
e.graph_eq. ExtendOfNorm on the dense graph gives the maps; test I identities extend
by continuity. This lemma contains only completion and linear-map algebra. -/
theorem localized_chart_extension
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (ψ : X F → ℝ) (c : RellichTestChart Γ ψ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : testSubmodule F Γ,
      ‖c.re f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ∧
      ‖c.im f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) :
    ∃ A B : E.V →L[ℝ] ↥(RellichEuclidean.h1On c.support c.compact.measurableSet),
      (∀ f, A (rellichTestVector e f) = c.re f) ∧
      (∀ f, B (rellichTestVector e f) = c.im f) ∧
      (∀ x, A (Complex.I • x) = -B x ∧ B (Complex.I • x) = A x) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
