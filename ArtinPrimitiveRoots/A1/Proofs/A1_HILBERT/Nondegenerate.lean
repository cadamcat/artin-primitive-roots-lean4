import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core

/-! Nondegeneracy from the single radical extension and local Artin surjectivity. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem simpleSymbolHom_right_kernel
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (h : ∀ a : Kˣ, simpleSymbolHom K n hnK hmu b a = 1) :
    ∃ c : Kˣ, b = c ^ (n : ℕ) := by
  let E := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let β : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let χ := chosenSimpleKummerRootCharacter K n hnK hmu b
  let e := nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu
  let r := nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  have hchar (a : Kˣ) : χ (simpleArtin K n hnK hmu b a) = 1 := by
    apply e.symm.injective
    apply r.injective
    change simpleSymbolHom K n hnK hmu b a = r (e.symm 1)
    exact (h a).trans (by simp only [map_one])
  have hsurj : Function.Surjective (simpleArtin K n hnK hmu b) :=
    abelianLocalArtinMonoidHom_surjective K E
  have hσ (σ : Gal(E/K)) : σ = 1 := by
    obtain ⟨a, ha⟩ := hsurj σ
    apply chosenSimpleKummerRootCharacter_injective K n hnK hmu b
    exact ((congrArg χ ha).symm.trans (hchar a)).trans (map_one χ).symm
  have hfix : ∀ σ : Gal(E/K), σ (β : E) = (β : E) := by
    intro σ
    rw [hσ σ]
    rfl
  obtain ⟨c, hc⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := E) (β : E)).mpr hfix
  have hc0 : c ≠ 0 := by
    intro hzero
    apply β.ne_zero
    exact hc.symm.trans (by rw [hzero, map_zero])
  have hpow : (β : E) ^ (n : ℕ) = algebraMap K E (b : K) :=
    congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hnK b)
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  change (b : K) = c ^ (n : ℕ)
  apply (algebraMap K E).injective
  calc
    algebraMap K E (b : K) = (β : E) ^ (n : ℕ) := hpow.symm
    _ = (algebraMap K E c) ^ (n : ℕ) := congrArg (fun z : E => z ^ (n : ℕ)) hc.symm
    _ = algebraMap K E (c ^ (n : ℕ)) := (map_pow (algebraMap K E) c (n : ℕ)).symm

variable {F : Type} [Field F] [NumberField F]

theorem hilbert_right_nondegenerate_H3 (D : FieldData F) :
    ∀ v b, (∀ a, hilb D v a b = 1) → ∃ c : (v.adicCompletion F)ˣ, b = c ^ 6 := by
  intro v b h
  letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
  apply simpleSymbolHom_right_kernel (v.adicCompletion F) six
    (completionSixNeZero v) (completionPrimitiveRoots D v) b
  intro a
  have hcancel : rootEquiv D v (hilb D v a b) =
      simpleSymbolHom (v.adicCompletion F) six
        (completionSixNeZero v) (completionPrimitiveRoots D v) b a :=
    (rootEquiv D v).apply_symm_apply _
  exact hcancel.symm.trans
    ((congrArg (rootEquiv D v) (h a)).trans (map_one (rootEquiv D v)))

theorem hilbert_nondegenerate_of_skew_H3 (D : FieldData F)
    (hskew : ∀ v a b, hilb D v a b * hilb D v b a = 1) :
    ∀ v a, (∀ b, hilb D v a b = 1) → ∃ c : (v.adicCompletion F)ˣ, a = c ^ 6 := by
  intro v a h
  apply hilbert_right_nondegenerate_H3 D v a
  intro b
  have hs := hskew v a b
  rw [h b, one_mul] at hs
  exact hs

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
