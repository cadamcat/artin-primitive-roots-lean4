import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.GlobalRootComparison
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility

/-! Finite support and reciprocity of the sextic symbol over a totally complex field. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

open NumberField IsDedekindDomain KummerTheory
open scoped Classical BigOperators IsMulCommutative

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1
open GlobalClassFieldTheory.Reciprocity

variable {F : Type} [Field F] [NumberField F]

private theorem complexArtin_eq_one
    {L : Type} [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsAbelianGalois F L]
    (D : FieldData F) (v : InfinitePlace F) (x : v.Completionˣ) :
    chosenInfinitePlaceArtinMonoidHom (K := F) (L := L) v x = 1 := by
  have hw : (chosenInfinitePlaceAbove (L := L) v).IsUnramified F := by
    apply InfinitePlace.isUnramified_iff.mpr
    right
    rw [chosenInfinitePlaceAbove_comap (L := L) v]
    exact D.isTotallyComplex.isComplex v
  simp only [chosenInfinitePlaceArtinMonoidHom, infinitePlaceArtinMonoidHomOfPlace,
    dite_eq_left hw, MonoidHom.one_apply]

private theorem principalFiniteComponent (v : FinPlace F) (a : Fˣ) :
    IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F a) =
      Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a := by
  apply Units.ext
  calc
    _ = ((a : F) : v.adicCompletion F) := IdeleGroup.finiteComponent_principalIdele a v
    _ = algebraMap F (v.adicCompletion F) (a : F) := by
      symm
      have hmap := congrFun
        (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
          (R := 𝓞 F) (S := F) (K := F) (v := v)) (a : F)
      simpa using hmap

theorem finiteRootCharacter_reciprocity (D : FieldData F) (a b : Fˣ) :
    (Function.mulSupport fun v => finiteRootCharacter D v a b).Finite ∧
      ∏ᶠ v, finiteRootCharacter D v a b = 1 := by
  let L := globalRadical b
  letI : FiniteDimensional F L :=
    chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b
  letI : IsAbelianGalois F L :=
    chosenSimpleKummerExtension_isAbelianGalois F six globalSixNeZero
      (primitiveSixthRoots D) b
  letI : NumberField L := NumberField.of_module_finite F L
  let χ : Gal(L/F) →* rootsOfUnity 6 F := globalRootCharacter D b
  let f : FinPlace F → Gal(L/F) := fun v =>
    chosenFinitePlaceArtinMonoidHom (K := F) (L := L) v
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F a))
  have hf : Function.HasFiniteMulSupport f :=
    finitePlaceArtinFactors_hasFiniteMulSupport (K := F) (L := L)
      (IdeleGroup.principalIdele F a)
  have hfactor (v : FinPlace F) : χ (f v) = finiteRootCharacter D v a b := by
    dsimp only [f]
    rw [principalFiniteComponent v a]
    dsimp only [finiteRootCharacter, χ]
  have hfamily : (fun v => finiteRootCharacter D v a b) = fun v => χ (f v) :=
    funext fun v => (hfactor v).symm
  have hprod : ∏ᶠ v, f v = 1 := by
    have hArtin := chosenLocalArtin_product_principalIdele (K := F) (L := L) a
    have hinfinite : (∏ v : InfinitePlace F,
        chosenInfinitePlaceArtinMonoidHom (K := F) (L := L) v
          (IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele F a))) = 1 := by
      apply Finset.prod_eq_one
      intro v _
      exact complexArtin_eq_one D v _
    rw [hinfinite, one_mul] at hArtin
    exact hArtin
  rw [hfamily]
  refine ⟨hf.fun_comp χ.map_one, ?_⟩
  calc
    _ = χ (∏ᶠ v, f v) := (χ.map_finprod hf).symm
    _ = χ 1 := congrArg χ hprod
    _ = 1 := χ.map_one

theorem hilbert_global_reciprocity_H5 (D : FieldData F) :
    ∀ a b : Fˣ,
      (Function.mulSupport fun v => hilb D v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)).Finite ∧
      ∏ᶠ v, hilb D v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b) = 1 := by
  intro a b
  simpa only [hilbert_global_root_comparison] using finiteRootCharacter_reciprocity D a b

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
