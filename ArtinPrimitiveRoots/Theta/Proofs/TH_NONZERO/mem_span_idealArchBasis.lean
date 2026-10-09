import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.totallyComplexMixedEquiv_embedding

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- The real basis of the embedded fractional ideal in the complex
coordinates used by the theta torus. -/
def idealArchBasis : Basis (Module.Free.ChooseBasisIndex ℤ I) ℝ (InfinitePlace F → ℂ) :=
  (NumberField.mixedEmbedding.fractionalIdealLatticeBasis F I).map (totallyComplexMixedEquiv F)

/-- The integer span of the archimedean basis is exactly the embedded
fractional ideal. -/
theorem mem_span_idealArchBasis {x : InfinitePlace F → ℂ} :
    x ∈ Submodule.span ℤ (Set.range (idealArchBasis F I)) ↔
      ∃ y ∈ (I : Set F), (fun w : InfinitePlace F => w.embedding y) = x := by
  let e := (totallyComplexMixedEquiv F).restrictScalars ℤ
  have hrange : Set.range (idealArchBasis F I) =
      e.toLinearMap '' Set.range (NumberField.mixedEmbedding.fractionalIdealLatticeBasis F I) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span e.toLinearMap, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨y, hy, rfl⟩ :=
      (NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis F I).mp hz
    exact ⟨y, hy, (totallyComplexMixedEquiv_embedding F y).symm.trans hzx⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨NumberField.mixedEmbedding F y, ?_, ?_⟩
    · exact (NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis F I).mpr
        ⟨y, hy, rfl⟩
    · exact (totallyComplexMixedEquiv_embedding F y).trans hyx

end ArtinPrimitiveRoots.A1.Theta
