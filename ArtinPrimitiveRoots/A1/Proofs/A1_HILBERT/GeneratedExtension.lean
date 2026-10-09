/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Root-quotient transport adapted from GlobalHilbertSymbol.Core.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Semilinear
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality

/-! Evaluate the radical symbol in any generated finite abelian extension. -/

set_option autoImplicit false

open KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

private theorem rootQuotientAlgEquiv
    {K M E : Type} [Field K] [Field M] [Field E] [Algebra K M] [Algebra K E]
    (e : M ≃ₐ[K] E) (β : Mˣ) (σ : Gal(M/K)) :
    rootQuotient (K := K) (L := E) (Units.map e.toMonoidHom β)
        (AlgEquiv.autCongr e σ) =
      Units.map e.toMonoidHom (rootQuotient (K := K) (L := M) β σ) := by
  apply Units.ext
  simp [rootQuotient, AlgEquiv.autCongr_apply]

theorem simpleSymbolHom_in_generated_extension
    (K E : Type) [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (β : Eˣ)
    (hβ : β ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b)
    (hgen : IntermediateField.adjoin K {(β : E)} = ⊤) :
    Units.map (algebraMap K E).toMonoidHom
        ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) =
      rootQuotient (K := K) (L := E) β (abelianLocalArtinMonoidHom K E a) := by
  let M := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K M := chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K M := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let βM : Mˣ := chosenSimpleKummerRootUnit K n hnK b
  let p := Polynomial.X ^ (n : ℕ) - Polynomial.C (b : K)
  letI : Polynomial.IsSplittingField K M p :=
    simpleKummerSplits K M n hmu (b : K) (βM : M)
      (congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hnK b))
      (chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b)
  letI : Polynomial.IsSplittingField K E p :=
    simpleKummerSplits K E n hmu (b : K) (β : E) (congrArg Units.val hβ) hgen
  let e : M ≃ₐ[K] E :=
    (Polynomial.IsSplittingField.algEquiv M p).trans
      (Polynomial.IsSplittingField.algEquiv E p).symm
  let γ : Eˣ := Units.map e.toMonoidHom βM
  let σ := simpleArtin K n hnK hmu b a
  let τ := abelianLocalArtinMonoidHom K E a
  have hartin : AlgEquiv.autCongr e σ = τ :=
    DFunLike.congr_fun (abelianLocalArtinMonoidHom_autCongr K M E e) a
  have hγ : γ ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b := by
    rw [show γ = Units.map e.toMonoidHom βM from rfl, ← map_pow,
      chosenSimpleKummerRootUnit_pow K n hnK b]
    apply Units.ext
    exact e.commutes (b : K)
  calc
    _ = Units.map e.toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom
          ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ)) := by
      apply Units.ext
      exact (e.commutes _).symm
    _ = Units.map e.toMonoidHom (rootQuotient (K := K) (L := M) βM σ) :=
      congrArg (Units.map e.toMonoidHom) (simpleSymbolRootQuotient K n hnK hmu a b)
    _ = rootQuotient (K := K) (L := E) γ (AlgEquiv.autCongr e σ) :=
      (rootQuotientAlgEquiv e βM σ).symm
    _ = rootQuotient (K := K) (L := E) γ τ := by rw [hartin]
    _ = rootQuotient (K := K) (L := E) β τ :=
      rootQuotientSamePow K E n hmu b γ β hγ hβ τ

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
