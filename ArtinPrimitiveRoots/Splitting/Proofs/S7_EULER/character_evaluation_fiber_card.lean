import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- Every prescribed value at `g` that is an `orderOf g`th root of unity has
`|G| / orderOf g` character extensions.
Uses Mathlib finite abelian duality; feeds `prod_one_sub_character`. -/
theorem character_evaluation_fiber_card (G : Type*) [CommGroup G] [Finite G]
    (g : G) (ζ : ℂˣ) (hζ : ζ ^ orderOf g = 1) :
    Nat.card {χ : G →* ℂˣ // χ g = ζ} = Nat.card G / orderOf g := by
  classical
  letI : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := G))⟩
  letI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  let H : Subgroup G := Subgroup.zpowers g
  let ev : (G →* ℂˣ) →* ℂˣ :=
    { toFun := fun χ => χ g
      map_one' := by simp
      map_mul' := by intro χ ψ; simp }
  let restr : (G →* ℂˣ) →* (H →* ℂˣ) :=
    MonoidHom.domRestrictHom H ℂˣ
  have hker : ev.ker = restr.ker := by
    ext χ
    change χ g = 1 ↔ χ.domRestrict H = 1
    rw [MonoidHom.domRestrict_eq_one_iff]
    constructor
    · intro hg x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [map_zpow, hg]
      simp
    · intro hx
      exact hx g (by simp [H])
  have hkerCard : Nat.card ev.ker = Nat.card (G ⧸ H) := by
    rw [hker]
    exact CommGroup.card_domRestrictHom_ker ℂ H
  have hcharCard : Nat.card (G →* ℂˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have hcardG : Nat.card G = Nat.card (G ⧸ H) * orderOf g := by
    simpa [H, Nat.card_zpowers] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup H)
  have hindex : ev.ker.index = orderOf g := by
    apply Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card ev.ker)
    calc
      Nat.card ev.ker * ev.ker.index = Nat.card (G →* ℂˣ) := ev.ker.card_mul_index
      _ = Nat.card G := hcharCard
      _ = Nat.card (G ⧸ H) * orderOf g := hcardG
      _ = Nat.card ev.ker * orderOf g := by rw [← hkerCard]
  have hRangeCard : Nat.card ev.range = orderOf g := by
    calc
      Nat.card ev.range = ev.ker.index := (Subgroup.index_ker ev).symm
      _ = orderOf g := hindex
  have hRangeLe : ev.range ≤ rootsOfUnity (orderOf g) ℂ := by
    intro u hu
    rcases hu with ⟨χ, rfl⟩
    rw [mem_rootsOfUnity]
    change (χ g) ^ orderOf g = 1
    rw [← map_pow, pow_orderOf_eq_one]
    simp
  have hRangeEq : ev.range = rootsOfUnity (orderOf g) ℂ := by
    apply Subgroup.eq_of_le_of_card_ge hRangeLe
    rw [Complex.card_rootsOfUnity, hRangeCard]
  have hζmem : ζ ∈ rootsOfUnity (orderOf g) ℂ := by
    rw [mem_rootsOfUnity]
    exact hζ
  have hζrange : ζ ∈ ev.range := by
    rw [hRangeEq]
    exact hζmem
  obtain ⟨χ₀, hχ₀⟩ := hζrange
  change ev χ₀ = ζ at hχ₀
  let fiberKer : {χ : G →* ℂˣ // χ g = ζ} ≃ ev.ker :=
    { toFun := fun χ =>
        ⟨χ.val * χ₀⁻¹, MonoidHom.mem_ker.mpr (by
          change ev χ.val * (ev χ₀)⁻¹ = 1
          have hχ : ev χ.val = ζ := by simpa [ev] using χ.property
          rw [hχ, hχ₀]
          simp)⟩
      invFun := fun k =>
        ⟨k.val * χ₀, by
          have hk : ev k.val = 1 := MonoidHom.mem_ker.mp k.property
          change ev k.val * ev χ₀ = ζ
          rw [hk, hχ₀, one_mul]⟩
      left_inv := by
        intro χ
        apply Subtype.ext
        change (χ.val * χ₀⁻¹) * χ₀ = χ.val
        exact inv_mul_cancel_right (χ.val : G →* ℂˣ) χ₀
      right_inv := by
        intro k
        apply Subtype.ext
        change (k.val * χ₀) * χ₀⁻¹ = k.val
        exact mul_inv_cancel_right (k.val : G →* ℂˣ) χ₀ }
  calc
    Nat.card {χ : G →* ℂˣ // χ g = ζ} = Nat.card ev.ker := Nat.card_congr fiberKer
    _ = Nat.card (G ⧸ H) := hkerCard
    _ = Nat.card G / orderOf g := by
      rw [hcardG, ← Nat.mul_comm, Nat.mul_div_right _ (orderOf_pos g)]

end ArtinPrimitiveRoots.Splitting
end
