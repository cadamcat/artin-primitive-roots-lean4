import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Logic.Equiv.Defs

/-! Component presentations of a restricted product with a finite exceptional set. -/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta.TH_COVER

open Filter

variable {I J X : Type} {L : I → Type} {M : J → Type}

/-- Finite components outside E use A; all other components are unrestricted. -/
def sumReference (E : Finset I) (A : ∀ i : I, i ∉ E → Set (L i)) :
    (p : I ⊕ J) → Set (Sum.elim L M p)
  | .inl i => if hi : i ∉ E then A i hi else Set.univ
  | .inr _ => Set.univ

/-- The component axioms identify X with the canonical restricted tuples.
This theorem makes no claim about the topology on X. -/
theorem restrictedSum_componentEquiv
    (E : Finset I) (A : ∀ i : I, i ∉ E → Set (L i))
    (cf : ∀ i : I, X → L i) (cc : ∀ j : J, X → M j)
    (hext : ∀ x y : X, (∀ i, cf i x = cf i y) → (∀ j, cc j x = cc j y) → x = y)
    (hres : ∀ x : X, Set.Finite {i : I | ∃ hi : i ∉ E, cf i x ∉ A i hi})
    (hsurj : ∀ (lf : ∀ i : I, L i) (lc : ∀ j : J, M j),
      Set.Finite {i : I | ∃ hi : i ∉ E, lf i ∉ A i hi} →
        ∃ x : X, (∀ i, cf i x = lf i) ∧ ∀ j, cc j x = lc j) :
    ∃ e : X ≃ RestrictedProduct (Sum.elim L M) (sumReference E A) cofinite,
      (∀ x i, e x (.inl i) = cf i x) ∧ ∀ x j, e x (.inr j) = cc j x := by
  classical
  let f : X → RestrictedProduct (Sum.elim L M) (sumReference E A) cofinite :=
    fun x => ⟨(fun p => match p with
      | .inl i => cf i x
      | .inr j => cc j x), by
      apply Filter.eventually_cofinite.mpr
      apply ((hres x).image Sum.inl).subset
      intro p hp
      cases p with
      | inl i =>
        refine ⟨i, ?_, rfl⟩
        by_cases hi : i ∉ E
        · refine ⟨hi, ?_⟩
          change cf i x ∉ (if h : i ∉ E then A i h else Set.univ) at hp
          rw [dif_pos hi] at hp
          exact hp
        · change cf i x ∉ (if h : i ∉ E then A i h else Set.univ) at hp
          rw [dif_neg hi] at hp
          exact False.elim (hp (Set.mem_univ _))
      | inr j =>
        change cc j x ∉ (Set.univ : Set (M j)) at hp
        exact False.elim (hp (Set.mem_univ _))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hext x y
      · intro i
        exact congrArg (fun r => r (.inl i)) hxy
      · intro j
        exact congrArg (fun r => r (.inr j)) hxy
    · intro r
      have hr : Set.Finite {i : I | ∃ hi : i ∉ E, r (.inl i) ∉ A i hi} := by
        have hb := Filter.eventually_cofinite.mp r.2
        apply (hb.preimage Sum.inl_injective.injOn).subset
        rintro i ⟨hi, hni⟩
        change r (.inl i) ∉ (if h : i ∉ E then A i h else Set.univ)
        rw [dif_pos hi]
        exact hni
      obtain ⟨x, hxF, hxC⟩ := hsurj (fun i => r (.inl i)) (fun j => r (.inr j)) hr
      refine ⟨x, ?_⟩
      apply RestrictedProduct.ext
      intro p
      cases p with
      | inl i => exact hxF i
      | inr j => exact hxC j
  exact ⟨Equiv.ofBijective f hf, (fun _ _ => rfl), fun _ _ => rfl⟩

end ArtinPrimitiveRoots.A1.Theta.TH_COVER
