import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.character_evaluation_fiber_card
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.prod_one_sub_rootsOfUnity

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The abelian character Euler polynomial.
Uses `character_evaluation_fiber_card` and
`prod_one_sub_rootsOfUnity`; feeds `upstairs_rhp_euler_identity`. -/
theorem prod_one_sub_character (G : Type*) [CommGroup G] [Finite G]
    (g : G) (z : ℂ) :
    (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  classical
  letI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  let evRoot : (G →* ℂˣ) → rootsOfUnity (orderOf g) ℂ := fun χ =>
    ⟨χ g, by
      rw [mem_rootsOfUnity]
      calc
        (χ g) ^ orderOf g = χ (g ^ orderOf g) := by rw [map_pow]
        _ = 1 := by simp⟩
  have hfiberEquiv (ξ : rootsOfUnity (orderOf g) ℂ) :
      {χ : G →* ℂˣ // evRoot χ = ξ} ≃
        {χ : G →* ℂˣ // χ g = (ξ : ℂˣ)} :=
    { toFun := fun χ =>
        ⟨χ.val, by
          have h := congrArg (fun r : rootsOfUnity (orderOf g) ℂ => (r : ℂˣ)) χ.property
          simpa [evRoot] using h⟩
      invFun := fun χ =>
        ⟨χ.val, by
          apply Subtype.ext
          exact χ.property⟩
      left_inv := by intro χ; apply Subtype.ext; rfl
      right_inv := by intro χ; apply Subtype.ext; rfl }
  have hfiberCard (ξ : rootsOfUnity (orderOf g) ℂ) :
      Nat.card {χ : G →* ℂˣ // evRoot χ = ξ} = Nat.card G / orderOf g := by
    have hξ : (ξ : ℂˣ) ^ orderOf g = 1 := by
      exact (mem_rootsOfUnity (orderOf g) (ξ : ℂˣ)).mp ξ.property
    calc
      _ = Nat.card {χ : G →* ℂˣ // χ g = (ξ : ℂˣ)} := Nat.card_congr (hfiberEquiv ξ)
      _ = Nat.card G / orderOf g := character_evaluation_fiber_card G g ξ hξ
  let f : (G →* ℂˣ) → ℂ := fun χ => 1 - ((evRoot χ : ℂˣ) : ℂ) * z
  have hfiberConst (ξ : rootsOfUnity (orderOf g) ℂ) :
      (∏ χ : {χ : G →* ℂˣ // evRoot χ = ξ}, f χ) =
        (1 - ((ξ : ℂˣ) : ℂ) * z) ^ (Nat.card G / orderOf g) := by
    let S := {χ : G →* ℂˣ // evRoot χ = ξ}
    have hcard : Fintype.card S = Nat.card G / orderOf g := by
      simpa only [Fintype.card_eq_nat_card] using hfiberCard ξ
    calc
      _ = ∏ _χ : S, (1 - ((ξ : ℂˣ) : ℂ) * z) := by
        apply Fintype.prod_congr
        intro χ
        simp [f, χ.property]
      _ = (1 - ((ξ : ℂˣ) : ℂ) * z) ^ Fintype.card S := by simp
      _ = (1 - ((ξ : ℂˣ) : ℂ) * z) ^ (Nat.card G / orderOf g) := by rw [hcard]
  have hgroup :
      (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
        ∏ ξ : rootsOfUnity (orderOf g) ℂ,
          (1 - ((ξ : ℂˣ) : ℂ) * z) ^ (Nat.card G / orderOf g) := by
    calc
      _ = ∏ χ : G →* ℂˣ, f χ := by
        apply Fintype.prod_congr
        intro χ
        simp [f, evRoot]
      _ = ∏ ξ : rootsOfUnity (orderOf g) ℂ,
            ∏ χ : {χ : G →* ℂˣ // evRoot χ = ξ}, f χ :=
          (Fintype.prod_fiberwise evRoot f).symm
      _ = _ := by
        apply Fintype.prod_congr
        intro ξ
        exact hfiberConst ξ
  calc
    _ = (∏ ξ : rootsOfUnity (orderOf g) ℂ,
          (1 - ((ξ : ℂˣ) : ℂ) * z)) ^ (Nat.card G / orderOf g) := by
      rw [← Finset.prod_pow]
      exact hgroup
    _ = (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
      rw [prod_one_sub_rootsOfUnity]

end ArtinPrimitiveRoots.Splitting
end
