import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.FiniteIdelic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Global quadratic Hilbert characters

The next helper, in this module's context, is:
```
theorem qs_nq0_quadratic_character_exists (D : FieldData K) (H : HilbertData K)
    (a : Kˣ) :
    ∃ χ : HeckeChar K, χ ^ 2 = 1 ∧
      (∀ (w : InfinitePlace K) (u : w.Completionˣ), χ.locInf w u = 1) ∧
      (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
```
Extend the finite character by the finite projection, descend along the
principal subgroup using the product formula, and evaluate one-place ideles.
-/

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The finite Hilbert product descends to a quadratic Hecke character. -/
theorem qs_nq0_quadratic_character_exists (D : FieldData K) (H : HilbertData K)
    (a : Kˣ) :
    ∃ χ : HeckeChar K, χ ^ 2 = 1 ∧
      (∀ (w : InfinitePlace K) (u : w.Completionˣ), χ.locInf w u = 1) ∧
      (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a)) := by
  classical
  obtain ⟨Ξ, hΞsq, hΞprod⟩ := qs_nq0_finite_idelic_character_exists D H a
  let p : NumberField.IdeleGroup (𝓞 K) K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  have hp : Continuous p := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_snd.comp Units.continuous_val,
      continuous_snd.comp Units.continuous_coe_inv⟩
  let F : NumberField.IdeleGroup (𝓞 K) K →* ℂˣ := Ξ.toMonoidHom.comp p
  have hF : Continuous F := Ξ.continuous.comp hp
  let N := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  have hN : N ≤ F.ker := by
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    change Ξ (p (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K b)) = 1
    rw [hΞprod]
    exact (qs_nq0_quadratic_product_formula D H a b).2
  let C : IdeleClassGroup (𝓞 K) K →* ℂˣ := QuotientGroup.lift N F hN
  have hC : Continuous C := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact hF
  let χ : HeckeChar K := ⟨C, hC⟩
  refine ⟨χ, ?_, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q (fun x => ?_)
    simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
    change Ξ (p x) ^ 2 = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] using
      congrArg (fun g : ContinuousMonoidHom (FiniteAdeleRing (𝓞 K) K)ˣ ℂˣ =>
        g (p x)) hΞsq
  · intro w u
    change Ξ (p (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w u)) = 1
    have hproj : p (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w u) = 1 := by
      apply Units.ext
      rfl
    rw [hproj, map_one]
  · intro v
    apply MonoidHom.ext
    intro u
    change Ξ (p (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) =
      qsNQQuadraticLocal D H v (toLoc v a) u
    rw [hΞprod]
    have hout (w : FinPlace K) (hw : w ≠ v) :
        RestrictedProduct.coeUnits (p (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) w = 1 := by
      apply Units.ext
      change FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K) w = 1
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ hw
    rw [finprod_eq_single _ v (fun w hw => by rw [hout w hw, map_one])]
    congr 1
    apply Units.ext
    change FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K) v =
      (u : v.adicCompletion K)
    exact RestrictedProduct.mulSingle_eq_same _ _ _

/-- Select the quadratic Hilbert character for each ideal-indexed generator. -/
theorem qs_nq0_quadratic_local_realization (D : FieldData K)
    (H : HilbertData K) (a : Ideal (𝓞 K) → Kˣ) :
    ∃ χ : Ideal (𝓞 K) → HeckeChar K,
      (∀ I, χ I ^ 2 = 1) ∧
      (∀ I (w : InfinitePlace K) (u : w.Completionˣ), (χ I).locInf w u = 1) ∧
      (∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
        (((χ I).loc v u : ℂˣ) : ℂ) =
          D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3) := by
  classical
  let χ (I : Ideal (𝓞 K)) : HeckeChar K :=
    (qs_nq0_quadratic_character_exists D H (a I)).choose
  have hχ (I : Ideal (𝓞 K)) :=
    (qs_nq0_quadratic_character_exists D H (a I)).choose_spec
  refine ⟨χ, fun I => (hχ I).1, fun I w u => (hχ I).2.1 w u, ?_⟩
  intro I v u
  rw [(hχ I).2.2 v]
  rfl

end ArtinPrimitiveRoots.A2
