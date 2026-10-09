import ArtinPrimitiveRoots.A1.Field
import ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CofinitelySplitFiniteExtension

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Local sixth roots force the simple Kummer extension to have degree one. -/
theorem global_sixth_of_local (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 6) (u : Fˣ)
    (hall : ∀ v : FinPlace F, ∃ c : (v.adicCompletion F)ˣ,
      Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom u = c ^ 6) :
    ∃ ε : Fˣ, u = ε ^ 6 := by
  classical
  obtain ⟨ζ, hζ⟩ := hmu
  let n : ℕ+ := ⟨6, by decide⟩
  have hn : ((n : ℕ) : F) ≠ 0 := by
    change (6 : F) ≠ 0
    norm_num
  have hroots : (primitiveRoots (n : ℕ) F).Nonempty := by
    refine ⟨ζ, ?_⟩
    exact (mem_primitiveRoots (by decide)).mpr hζ
  let E := KummerTheory.chosenSimpleKummerExtension F n hn u
  letI : FiniteDimensional F E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hn u
  letI : IsAbelianGalois F E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hn hroots u
  letI : NumberField E := NumberField.of_module_finite F E
  have hsplit (v : FinPlace F) : FinitePlaceSplitsCompletely (K := F) (L := E) v := by
    apply KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
      n hn hroots u v
    obtain ⟨c, hc⟩ := hall v
    exact ⟨c, hc.symm⟩
  have hfinite : {v : FinPlace F |
      ¬ FinitePlaceSplitsCompletelyInExtension (K := F) (E := E) v}.Finite := by
    apply (Set.finite_empty : (∅ : Set (FinPlace F)).Finite).subset
    intro v hv
    exact (hv ((finitePlaceSplitsCompletely_iff_inExtension (K := F) (E := E) v).mp
      (hsplit v))).elim
  let e : E ≃ₐ[F] F :=
    GlobalClassFieldTheory.Cohomology.algEquivBaseOfFiniteNonSplittingPlaces F E hfinite
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit F n hn u
  let f : Eˣ →* Fˣ := Units.map e.toAlgHom.toMonoidHom
  have hβ : β ^ 6 = Units.map (algebraMap F E).toMonoidHom u :=
    KummerTheory.chosenSimpleKummerRootUnit_pow F n hn u
  have hfu : f (Units.map (algebraMap F E).toMonoidHom u) = u := by
    apply Units.ext
    change e (algebraMap F E (u : F)) = (u : F)
    simpa using e.commutes (u : F)
  have heq := congrArg f hβ
  rw [map_pow, hfu] at heq
  exact ⟨f β, heq.symm⟩

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
