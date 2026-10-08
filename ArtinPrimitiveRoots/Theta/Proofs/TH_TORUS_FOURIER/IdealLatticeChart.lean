import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- A nonzero fractional ideal gives a real basis whose integer span is the exact
archimedean period subgroup in `torus_fourier_expansion`. -/
theorem ideal_lattice_chart (D : FieldData F)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
    ∃ b : Basis (Free.ChooseBasisIndex ℤ I) ℝ (InfinitePlace F → ℂ),
      (∀ i, b i = infEmbA (basisOfFractionalIdeal F I i)) ∧
      (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let b₀ := mixedEmbedding.fractionalIdealLatticeBasis F I
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let b := b₀.map e
  let f : mixedEmbedding.mixedSpace F →ₗ[ℤ] (InfinitePlace F → ℂ) :=
    e.toLinearMap.restrictScalars ℤ
  have hf (y : F) : f (mixedEmbedding F y) = infEmbA y := by
    ext w
    simp [f, e, ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv, infEmbA,
      mixedEmbedding]
  refine ⟨b, ?_, ?_⟩
  · intro i
    change e (mixedEmbedding.fractionalIdealLatticeBasis F I i) = _
    rw [mixedEmbedding.fractionalIdealLatticeBasis_apply]
    exact hf (basisOfFractionalIdeal F I i)
  · have hrange : Set.range b = f '' Set.range b₀ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b₀ i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    have hspanMap : Submodule.span ℤ (Set.range b) =
        (Submodule.span ℤ (Set.range b₀)).map f := by
      rw [hrange, ← Submodule.map_span]
    have hspan₀ : Submodule.span ℤ (Set.range b₀) = mixedEmbedding.idealLattice F I :=
      mixedEmbedding.span_idealLatticeBasis F I
    have hspan (x : InfinitePlace F → ℂ) :
        x ∈ Submodule.span ℤ (Set.range b) ↔
          ∃ y : F, y ∈ (I : Submodule (𝓞 F) F) ∧ infEmbA y = x := by
      rw [hspanMap, Submodule.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hspan₀] at hz
        obtain ⟨y, hy, rfl⟩ := (mixedEmbedding.mem_idealLattice F I).mp hz
        exact ⟨y, hy, hf y⟩
      · rintro ⟨y, hy, rfl⟩
        apply Submodule.mem_map.mpr
        refine ⟨mixedEmbedding F y, ?_, hf y⟩
        rw [hspan₀]
        exact (mixedEmbedding.mem_idealLattice F I).mpr ⟨y, hy, rfl⟩
    apply AddSubgroup.ext
    intro x
    change x ∈ Submodule.span ℤ (Set.range b) ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [hspan]
    rfl

end ArtinPrimitiveRoots.Proofs.thsol_torusf
