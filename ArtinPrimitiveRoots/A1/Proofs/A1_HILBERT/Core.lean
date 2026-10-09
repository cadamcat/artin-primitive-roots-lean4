import ArtinPrimitiveRoots.A1.Residue
import GaloisCohomology.Kummer.Concrete.SimpleExtension
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology

/-! A simple Kummer construction of the local sextic symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1

abbrev six : ℕ+ := ⟨6, by decide⟩

variable {F : Type} [Field F] [NumberField F]

theorem primitiveSixthRoots (D : FieldData F) : (primitiveRoots 6 F).Nonempty := by
  refine ⟨D.ζ12 ^ 2, (mem_primitiveRoots (by decide)).mpr ?_⟩
  exact D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)

abbrev completionValuativeRel (v : FinPlace F) : ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))

theorem completionIsLocalField (v : FinPlace F) :
    @IsNonarchimedeanLocalField (v.adicCompletion F) inferInstance
      (completionValuativeRel v) inferInstance := by
  let K := v.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let _ : ν.IsNontrivial := inferInstance
  let _ : ValuativeRel K := completionValuativeRel v
  let _ : ν.Compatible := Valuation.Compatible.ofValuation ν
  let _ : ValuativeRel.IsNontrivial K :=
    (ValuativeRel.isNontrivial_iff_isNontrivial ν).2 inferInstance
  let _ : IsValuativeTopology K :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      K (WithZero (Multiplicative ℤ))
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

section Local

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

def simpleArtin (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let E := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact abelianLocalArtinMonoidHom K E

def simpleSymbolHom (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* rootsOfUnity (n : ℕ) K :=
  (nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).toMonoidHom.comp
    ((nthRootsSubgroupEquivOfPrimitiveRoots
        K (chosenSimpleKummerExtension K n hnK b) n hmu).symm.toMonoidHom.comp
      ((chosenSimpleKummerRootCharacter K n hnK hmu b).comp
        (simpleArtin K n hnK hmu b)))

end Local

def rootEquiv (D : FieldData F) (v : FinPlace F) :
    rootsOfUnity 6 F ≃* rootsOfUnity 6 (v.adicCompletion F) :=
  rootsOfUnityEquivOfPrimitiveRoots
    (algebraMap F (v.adicCompletion F)).injective (primitiveSixthRoots D)

theorem completionPrimitiveRoots (D : FieldData F) (v : FinPlace F) :
    (primitiveRoots 6 (v.adicCompletion F)).Nonempty := by
  obtain ⟨ζ, hζ⟩ := primitiveSixthRoots D
  refine ⟨algebraMap F (v.adicCompletion F) ζ, (mem_primitiveRoots (by decide)).mpr ?_⟩
  exact ((mem_primitiveRoots (by decide)).mp hζ).map_of_injective
    (algebraMap F (v.adicCompletion F)).injective

theorem completionSixNeZero (v : FinPlace F) :
    ((six : ℕ) : v.adicCompletion F) ≠ 0 := by
  intro h
  change (6 : v.adicCompletion F) = 0 at h
  have hF : (6 : F) = 0 := (algebraMap F (v.adicCompletion F)).injective
    (by simpa only [map_ofNat, map_zero] using h)
  exact (by norm_num : (6 : F) ≠ 0) hF

def hilb (D : FieldData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) : rootsOfUnity 6 F :=
  letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
  (rootEquiv D v).symm
    (simpleSymbolHom (v.adicCompletion F) six
      (completionSixNeZero v) (completionPrimitiveRoots D v) b a)

theorem local_hilbert_symbol_H0 (D : FieldData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) :
    letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
    let K := v.adicCompletion F
    let hnK : ((six : ℕ) : K) ≠ 0 := completionSixNeZero v
    let E := chosenSimpleKummerExtension K six hnK b
    Units.map (algebraMap K E).toMonoidHom
        ((rootEquiv D v (hilb D v a b) : rootsOfUnity 6 K) : Kˣ) =
      rootQuotient (K := K) (L := E)
        (chosenSimpleKummerRootUnit K six hnK b)
        (simpleArtin K six hnK (completionPrimitiveRoots D v) b a) := by
  letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
  let K := v.adicCompletion F
  let hnK : ((six : ℕ) : K) ≠ 0 := completionSixNeZero v
  let E := chosenSimpleKummerExtension K six hnK b
  let hmu := completionPrimitiveRoots D v
  let e := nthRootsSubgroupEquivOfPrimitiveRoots K E six hmu
  let σ := simpleArtin K six hnK hmu b a
  change Units.map (algebraMap K E).toMonoidHom
      ((rootEquiv D v (hilb D v a b) : rootsOfUnity 6 K) : Kˣ) =
    rootQuotient (K := K) (L := E) (chosenSimpleKummerRootUnit K six hnK b) σ
  have hcancel : rootEquiv D v (hilb D v a b) =
      simpleSymbolHom K six hnK hmu b a :=
    (rootEquiv D v).apply_symm_apply _
  have hmap : Units.map (algebraMap K E).toMonoidHom
      ((simpleSymbolHom K six hnK hmu b a : rootsOfUnity 6 K) : Kˣ) =
      (chosenSimpleKummerRootCharacter K six hnK hmu b σ).1 := congrArg Subtype.val
    (e.apply_symm_apply (chosenSimpleKummerRootCharacter K six hnK hmu b σ))
  calc
    _ = Units.map (algebraMap K E).toMonoidHom
        ((simpleSymbolHom K six hnK hmu b a : rootsOfUnity 6 K) : Kˣ) :=
      congrArg (fun z : rootsOfUnity 6 K =>
        Units.map (algebraMap K E).toMonoidHom (z : Kˣ)) hcancel
    _ = (chosenSimpleKummerRootCharacter K six hnK hmu b σ).1 := hmap
    _ = rootQuotient (K := K) (L := E)
        (chosenSimpleKummerRootUnit K six hnK b) σ :=
      congrArg Subtype.val (chosenSimpleKummerRootCharacter_apply K six hnK hmu b σ)

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
