import ArtinPrimitiveRoots.A1.AddChar

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Module
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- A nonzero fractional ideal has a fundamental domain in the complex place coordinates. -/
theorem whit_fractional_lattice_domain (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0) :
    ∃ Pd : Set (InfinitePlace F → ℂ), IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map
        ((RingHom.pi fun w : InfinitePlace F => w.embedding) :
          F →+* (InfinitePlace F → ℂ)).toAddMonoidHom) Pd volume := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let e : NumberField.mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℂ) :=
    { toFun := fun x w => x.2 ⟨w, IsTotallyComplex.isComplex w⟩
      invFun := fun x => (fun _ => 0, fun w => x w.1)
      left_inv := by
        intro x
        apply Prod.ext
        · funext w
          exact False.elim ((InfinitePlace.not_isReal_iff_isComplex.mpr
            (IsTotallyComplex.isComplex w.1)) w.2)
        · funext w
          rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let B := NumberField.mixedEmbedding.fractionalIdealLatticeBasis F I
  let b := B.map e
  let eZ := e.toLinearMap.restrictScalars ℤ
  let emb : F →+ (InfinitePlace F → ℂ) :=
    ((RingHom.pi fun w : InfinitePlace F => w.embedding) :
      F →+* (InfinitePlace F → ℂ)).toAddMonoidHom
  have hemb (ξ : F) : e (NumberField.mixedEmbedding F ξ) = emb ξ := by
    funext w
    change (NumberField.mixedEmbedding F ξ).2 ⟨w, IsTotallyComplex.isComplex w⟩ =
      w.embedding ξ
    simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hrange : Set.range b = eZ '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map emb := by
    ext z
    change z ∈ Submodule.span ℤ (Set.range b) ↔
      ∃ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) ∧ emb ξ = z
    rw [hrange, ← Submodule.map_span, Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨ξ, hξ, hξu⟩ :=
        (NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis F I).1 hu
      refine ⟨ξ, hξ, ?_⟩
      rw [← hξu]
      exact (hemb ξ).symm
    · rintro ⟨ξ, hξ, rfl⟩
      refine ⟨NumberField.mixedEmbedding F ξ, ?_, ?_⟩
      · apply (NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis F I).2
        exact ⟨ξ, hξ, rfl⟩
      · exact hemb ξ
  refine ⟨ZSpan.fundamentalDomain b, ?_⟩
  rw [← hspan]
  exact ZSpan.isAddFundamentalDomain' b volume

/-- An integral period is trivial for the archimedean character. -/
theorem whit_integral_inf_character (D : FieldData F) {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (A : AddCharData F) (a : 𝓞 F) :
    (∏ w : InfinitePlace F, psiC (w.embedding (a : F))) = 1 := by
  sorry

/-- A nonzero ideal can impose finitely many prescribed local unipotent radii. -/
theorem whit_small_ideal (E : Finset (FinPlace F)) (m : E → ℕ) :
    ∃ I : Ideal (𝓞 F), I ≠ ⊥ ∧ ∀ a ∈ I, ∀ v : E,
      Valued.v (algebraMap (𝓞 F) (v.1.adicCompletion F) a) ≤
        WithZero.exp (-(m v : ℤ)) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
