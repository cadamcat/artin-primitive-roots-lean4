import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.compact_overlap_finite_SL2O

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec.SpecProperB

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

theorem locallyCompactX : LocallyCompactSpace (X F) := by
  classical
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, _, _⟩ := hchart
  letI : LocallyCompactSpace {p : Coord F // p ∈ posSet F} :=
    posSet_open.locallyCompactSpace
  exact e.symm.isOpenEmbedding.locallyCompactSpace

theorem t2SpaceX : T2Space (X F) := by
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, _, _⟩ := hchart
  exact e.t2Space

theorem continuousSL2OAction (g : SL(2, 𝓞 F)) :
    Continuous (fun z : X F => g • z) := by
  apply continuous_pi
  intro w
  exact (OAI.CubicEisenstein.continuous_hyperbolic_action
    (toInf F (toSLF F g) w)).comp (continuous_apply w)

end ArtinPrimitiveRoots.A1.Spec.SpecProperB
