import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.compact_overlap_finite_SL2O
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.siegel_compactBox_isCompact

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Low-height Siegel overlaps lie in finitely many pairs of compact cusp boxes.
Uses siegel_compactBox_isCompact and
compact_overlap_finite_SL2O; feeds R9_proper. -/
theorem siegel_low_height_overlap_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 ≤ A) :
    (siegelLowOverlap Γ d A).Finite := by
  classical
  letI : Fintype d.ι := d.fintype
  let K : d.ι → Set (X F) := fun i => SiegelData.compactBox F d i A
  let S : d.ι × d.ι → Set (SL(2,𝓞 F)) := fun ij =>
    {g | ∃ z ∈ K ij.1, g • z ∈ K ij.2}
  let T : d.ι × d.ι → Set Γ := fun ij => {γ | (γ : SL(2,𝓞 F)) ∈ S ij}
  have hS (ij : d.ι × d.ι) : (S ij).Finite := by
    dsimp [S, K]
    exact compact_overlap_finite_SL2O
      (SiegelData.compactBox F d ij.1 A) (SiegelData.compactBox F d ij.2 A)
      (siegel_compactBox_isCompact Γ d A hA ij.1)
      (siegel_compactBox_isCompact Γ d A hA ij.2)
  have hT (ij : d.ι × d.ι) : (T ij).Finite := by
    dsimp [T]
    exact (hS ij).preimage (Set.injOn_of_injective Subtype.val_injective)
  have hUnion : (⋃ ij : d.ι × d.ι, T ij).Finite := Set.finite_iUnion hT
  apply hUnion.subset
  intro γ hγ
  change ∃ (i j : d.ι) (z : X F), z ∈ SiegelData.setAt F d i ∧
    siegelOverlapTransition Γ d i j γ z ∈ SiegelData.setAt F d j ∧
    normHeight F z ≤ A ∧ normHeight F (siegelOverlapTransition Γ d i j γ z) ≤ A at hγ
  rcases hγ with ⟨i, j, z, hz, hdest, hheight, hheight'⟩
  change z ∈ siegelSet F (d.P i) (2 * d.B i) (SiegelData.lowerHeight F d i) at hz
  rcases hz with ⟨x, y, hzeq, hx, hbal, hfloor⟩
  change siegelOverlapTransition Γ d i j γ z ∈
    siegelSet F (d.P j) (2 * d.B j) (SiegelData.lowerHeight F d j) at hdest
  rcases hdest with ⟨x', y', hdestEq, hx', hbal', hfloor'⟩
  let src : X F := (d.σ i) • z
  let dst : X F := (d.σ j) • ptX' F x' y'
  have hsrcBox : src ∈ K i := by
    refine ⟨x, y, ?_, subset_closure hx, hbal, hfloor, ?_⟩
    · exact congrArg ((d.σ i) • ·) hzeq
    · simpa [hzeq] using hheight
  have hdstBox : dst ∈ K j := by
    refine ⟨x', y', rfl, subset_closure hx', hbal', hfloor', ?_⟩
    simpa [hdestEq] using hheight'
  have hmove : (γ : SL(2,𝓞 F)) • src = dst := by
    dsimp [src, dst]
    calc
      (γ : SL(2,𝓞 F)) • ((d.σ i) • z) =
          (d.σ j) • siegelOverlapTransition Γ d i j γ z := by
        simp [siegelOverlapTransition, smul_smul]
      _ = (d.σ j) • ptX' F x' y' := congrArg ((d.σ j) • ·) hdestEq
  exact Set.mem_iUnion.mpr ⟨(i, j), ⟨src, hsrcBox, hmove ▸ hdstBox⟩⟩
end ArtinPrimitiveRoots.A1.Spec
