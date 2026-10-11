import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Extend norm domination from the dense test graph and transfer compactness.
Uses e.graph_eq, the estimate
periodization_L2_bound, and the compact chart map complex_chart_rellich_compact.
Factor R through the closure of the range of L by LinearMap.extendOfNorm. -/
theorem rellich_compact_of_test_bound
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (R : E.V →L[ℂ] L2Space F D) (L : E.V →L[ℂ] RellichChartL2 F)
    (hL : IsCompactOperator L) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : testSubmodule F Γ,
      ‖R (rellichTestVector e f)‖ ≤ C * ‖L (rellichTestVector e f)‖) :
    IsCompactOperator R := by
  have htestDense : DenseRange (rellichTestVector e) := by
    change DenseRange ((energyGraphMap e.toL2 e.gradL2).codRestrict E.V _)
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    change (E.V : Set (WithLp 2 (L2Space F D × GradientL2Space F D))) ⊆
      closure (Set.range (energyGraphMap e.toL2 e.gradL2))
    rw [e.graph_eq]
    rfl
  have hboundClosed : IsClosed {x : E.V | ‖R x‖ ≤ C * ‖L x‖} :=
    isClosed_le (R.continuous.norm) (continuous_const.mul L.continuous.norm)
  have hboundAll (x : E.V) : ‖R x‖ ≤ C * ‖L x‖ :=
    htestDense.induction_on x hboundClosed hbound

  let S : Submodule ℂ (RellichChartL2 F) :=
    (LinearMap.range L.toLinearMap).topologicalClosure
  have hSclosed : IsClosed (S : Set (RellichChartL2 F)) :=
    (LinearMap.range L.toLinearMap).isClosed_topologicalClosure
  have hLmem : ∀ x, L x ∈ S := fun x =>
    (LinearMap.range L.toLinearMap).le_topologicalClosure ⟨x, rfl⟩
  let Lrange : E.V →L[ℂ] S := L.codRestrict S hLmem
  have hLrangeDense : DenseRange Lrange := by
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    change closure (Set.range (L : E.V → RellichChartL2 F)) ⊆
      closure (Set.range (L : E.V → RellichChartL2 F))
    exact Set.Subset.rfl
  have hLrangeCompact : IsCompactOperator Lrange := by
    change IsCompactOperator (Set.codRestrict L S hLmem)
    exact hL.codRestrict hLmem hSclosed

  have hnormRange : ∀ x : E.V, ‖R.toLinearMap x‖ ≤ C * ‖Lrange.toLinearMap x‖ := by
    intro x
    exact hboundAll x
  let Q : S →L[ℂ] L2Space F D :=
    R.toLinearMap.extendOfNorm Lrange.toLinearMap
  have hfactor : R = Q.comp Lrange := by
    exact ContinuousLinearMap.ext fun x =>
      (LinearMap.extendOfNorm_eq hLrangeDense ⟨C, hnormRange⟩ x).symm
  rw [hfactor]
  exact hLrangeCompact.clm_comp Q

end ArtinPrimitiveRoots.A1.Spec
