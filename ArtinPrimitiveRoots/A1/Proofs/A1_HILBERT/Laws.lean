import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Pairing

/-! Multiplicativity and the norm criterion for the constructed sextic symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem simpleArtin_ker (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (simpleArtin K n hnK hmu b).ker =
      localNormSubgroup K (chosenSimpleKummerExtension K n hnK b) := by
  let E := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact abelianLocalArtinMonoidHom_ker K E

private theorem simpleSymbolHom_ker (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (simpleSymbolHom K n hnK hmu b).ker =
      localNormSubgroup K (chosenSimpleKummerExtension K n hnK b) := by
  unfold simpleSymbolHom
  rw [MonoidHom.ker_comp_of_injective _ _
    (nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).injective]
  rw [MonoidHom.ker_comp_of_injective _ _
    (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu).symm.injective]
  rw [MonoidHom.ker_comp_of_injective _ _
    (chosenSimpleKummerRootCharacter_injective K n hnK hmu b)]
  exact simpleArtin_ker K n hnK hmu b

theorem simpleSymbolHom_norm_criterion (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    simpleSymbolHom K n hnK hmu b a = 1 ↔
      a ∈ localNormSubgroup K (chosenSimpleKummerExtension K n hnK b) := by
  rw [← MonoidHom.mem_ker, simpleSymbolHom_ker K n hnK hmu b]

variable {F : Type} [Field F] [NumberField F]

def hilbHomLeft (D : FieldData F) (v : FinPlace F) (b : (v.adicCompletion F)ˣ) :
    (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
  letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
  (rootEquiv D v).symm.toMonoidHom.comp
    (simpleSymbolHom (v.adicCompletion F) six
      (completionSixNeZero v) (completionPrimitiveRoots D v) b)

theorem hilbert_mul_norm_criterion_H1 (D : FieldData F) :
    (∀ v a a' b, hilb D v (a * a') b = hilb D v a b * hilb D v a' b) ∧
    (∀ v a b b', hilb D v a (b * b') = hilb D v a b * hilb D v a b') := by
  constructor
  · intro v a a' b
    exact map_mul (hilbHomLeft D v b) a a'
  · intro v a b b'
    letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
    change (rootEquiv D v).symm
      (simpleSymbolHom (v.adicCompletion F) six
        (completionSixNeZero v) (completionPrimitiveRoots D v) (b * b') a) = _
    exact (congrArg (rootEquiv D v).symm
      (simpleSymbolHom_mul_right (v.adicCompletion F) six
        (completionSixNeZero v) (completionPrimitiveRoots D v) a b b')).trans
      (map_mul (rootEquiv D v).symm _ _)

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
