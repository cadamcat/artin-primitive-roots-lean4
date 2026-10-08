import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

theorem psiInf_one_integral (D : FieldData F)
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (A : AddCharData F) (x : 𝓞 F) :
    psiInf 1 (infEmbA (x : F)) = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hlocal (v : FinPlace F) :
      A.ψ v (algebraMap F (v.adicCompletion F) (x : F)) = 1 := by
    apply A.integral
    change Valued.v ((x : F) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one x
  have hfin :
      (∏ᶠ v : FinPlace F, A.ψ v (algebraMap F (v.adicCompletion F) (x : F))) = 1 := by
    exact finprod_eq_one_of_forall_eq_one hlocal
  have hglobal := (A.trivial_on_F (x : F)).2
  rw [hfin, one_mul] at hglobal
  have hdiag := S.e_diag_eq A (x : F) (x : F)
    (by intro v hv; simp)
    (by intro v hv; exact v.valuation_le_one x)
  have hSprod :
      (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (x : F))) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    exact hlocal v.1
  have hpsi : psiInf 1 (infEmbA (x : F)) =
      ∏ w : InfinitePlace F, psiC (w.embedding (x : F)) := by
    simp [psiInf, infEmbA]
  have hmatch : S.e A (S.diag (x : F)) = psiInf 1 (infEmbA (x : F)) := by
    calc
      S.e A (S.diag (x : F)) =
          (∏ v : S.Sf,
            A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (x : F))) *
            ∏ w : InfinitePlace F, psiC (w.embedding (x : F)) := by
              simp [SData.e, SData.diag]
      _ = ∏ w : InfinitePlace F, psiC (w.embedding (x : F)) := by rw [hSprod]; simp
      _ = psiInf 1 (infEmbA (x : F)) := hpsi.symm
  rw [hmatch] at hdiag
  exact hdiag.trans hglobal

theorem bounded_measurable_ideal_domain (D : FieldData F)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
    ∃ Pd : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain
        ((I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume ∧
      Bornology.IsBounded Pd ∧ MeasurableSet Pd := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let b₀ := NumberField.mixedEmbedding.fractionalIdealLatticeBasis F I
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let b := b₀.map e
  let f : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℤ] (InfinitePlace F → ℂ) :=
    e.toLinearMap.restrictScalars ℤ
  have hf (y : F) : f (NumberField.mixedEmbedding F y) = infEmbA y := by
    ext w
    simp [f, e, ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv, infEmbA,
      NumberField.mixedEmbedding]
  have hrange : Set.range b = f '' Set.range b₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b₀ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hspanMap : Submodule.span ℤ (Set.range b) =
      (Submodule.span ℤ (Set.range b₀)).map f := by
    rw [hrange, ← Submodule.map_span]
  have hspan₀ : Submodule.span ℤ (Set.range b₀) =
      NumberField.mixedEmbedding.idealLattice F I :=
    NumberField.mixedEmbedding.span_idealLatticeBasis F I
  have hspan (x : InfinitePlace F → ℂ) :
      x ∈ Submodule.span ℤ (Set.range b) ↔
        ∃ y : F, y ∈ (I : Submodule (𝓞 F) F) ∧ infEmbA y = x := by
    rw [hspanMap, Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hspan₀] at hz
      obtain ⟨y, hy, rfl⟩ := (NumberField.mixedEmbedding.mem_idealLattice F I).mp hz
      exact ⟨y, hy, hf y⟩
    · rintro ⟨y, hy, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨NumberField.mixedEmbedding F y, ?_, hf y⟩
      rw [hspan₀]
      exact (NumberField.mixedEmbedding.mem_idealLattice F I).mpr ⟨y, hy, rfl⟩
  have hgroup :
      (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    apply AddSubgroup.ext
    intro x
    change x ∈ Submodule.span ℤ (Set.range b) ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [hspan]
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
  let Pd := ZSpan.fundamentalDomain b
  have hfd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pd volume :=
    ZSpan.isAddFundamentalDomain' b volume
  rw [hgroup] at hfd
  exact ⟨Pd, hfd, ZSpan.fundamentalDomain_isBounded b,
    ZSpan.fundamentalDomain_measurableSet b⟩

end ArtinPrimitiveRoots.A1.Theta
