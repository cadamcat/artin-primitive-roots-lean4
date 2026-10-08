import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-! Central extensions from normalized cocycles, modulo a central split subgroup. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta.TH_COVER

variable {B Z : Type} [Group B] [CommGroup Z]

/-- Multiplicative normalization and associativity for the twisting factor. -/
class CocycleLaw (σ : B → B → Z) : Prop where
  one_left : ∀ g, σ 1 g = 1
  one_right : ∀ g, σ g 1 = 1
  assoc : ∀ g h k, σ g h * σ (g * h) k = σ g (h * k) * σ h k

/-- The algebraic part of a central cover after its scalar section is removed. -/
structure CocycleQuotient (N : Subgroup B) [N.Normal] (σ : B → B → Z) where
  E : Type
  [grp : Group E]
  z : Z →* E
  z_inj : Function.Injective z
  z_central : ∀ c x, z c * x = x * z c
  pr : E →* B ⧸ N
  pr_surj : Function.Surjective pr
  pr_ker : pr.ker = z.range
  sec : B → E
  sec_mul : ∀ g h, sec g * sec h = z (σ g h) * sec (g * h)
  sec_pr : ∀ g, pr (sec g) = QuotientGroup.mk g
  sec_triv : ∀ g ∈ N, sec g = 1

attribute [instance] CocycleQuotient.grp

/-- The cocycle group before removing its central scalar section. -/
@[ext]
structure Twisted (σ : B → B → Z) where
  base : B
  phase : Z

instance twistedGroup (σ : B → B → Z) [CocycleLaw σ] : Group (Twisted σ) where
  one := ⟨1, 1⟩
  mul x y := ⟨x.base * y.base, x.phase * y.phase * σ x.base y.base⟩
  inv x := ⟨x.base⁻¹, x.phase⁻¹ * (σ x.base⁻¹ x.base)⁻¹⟩
  mul_assoc x y t := by
    apply Twisted.ext
    · exact mul_assoc _ _ _
    · change (x.phase * y.phase * σ x.base y.base) * t.phase *
          σ (x.base * y.base) t.base =
        x.phase * (y.phase * t.phase * σ y.base t.base) *
          σ x.base (y.base * t.base)
      calc
        _ = (x.phase * y.phase * t.phase) *
            (σ x.base y.base * σ (x.base * y.base) t.base) := by ac_rfl
        _ = (x.phase * y.phase * t.phase) *
            (σ x.base (y.base * t.base) * σ y.base t.base) := by
          rw [CocycleLaw.assoc (σ := σ)]
        _ = _ := by ac_rfl
  one_mul x := by
    apply Twisted.ext
    · exact one_mul _
    · change 1 * x.phase * σ 1 x.base = x.phase
      rw [CocycleLaw.one_left (σ := σ)]
      simp
  mul_one x := by
    apply Twisted.ext
    · exact mul_one _
    · change x.phase * 1 * σ x.base 1 = x.phase
      rw [CocycleLaw.one_right (σ := σ)]
      simp
  inv_mul_cancel x := by
    apply Twisted.ext
    · exact inv_mul_cancel _
    · change (x.phase⁻¹ * (σ x.base⁻¹ x.base)⁻¹) * x.phase *
        σ x.base⁻¹ x.base = 1
      calc
        _ = (x.phase⁻¹ * x.phase) *
            ((σ x.base⁻¹ x.base)⁻¹ * σ x.base⁻¹ x.base) := by ac_rfl
        _ = 1 := by simp

/-- Quotient the twisted group by its central section of N. -/
theorem exists_cocycleQuotient (N : Subgroup B) [N.Normal] (σ : B → B → Z)
    (hlaw : CocycleLaw σ)
    (htriv : ∀ g ∈ N, ∀ h ∈ N, σ g h = 1)
    (hcent : ∀ g ∈ N, ∀ h : B, g * h = h * g)
    (hsym : ∀ g ∈ N, ∀ h : B, σ g h = σ h g) :
    Nonempty (CocycleQuotient N σ) := by
  letI : CocycleLaw σ := hlaw
  let scalar : N →* Twisted σ := {
    toFun := fun n => ⟨n.1, 1⟩
    map_one' := rfl
    map_mul' := by
      intro n m
      apply Twisted.ext
      · rfl
      · change 1 = 1 * 1 * σ n.1 m.1
        rw [htriv _ n.2 _ m.2]
        simp
  }
  have scalar_comm : ∀ (n : N) (t : Twisted σ), scalar n * t = t * scalar n := by
    intro n t
    apply Twisted.ext
    · exact hcent _ n.2 t.base
    · change 1 * t.phase * σ n.1 t.base = t.phase * 1 * σ t.base n.1
      rw [hsym _ n.2 t.base]
      simp
  let K : Subgroup (Twisted σ) := scalar.range
  letI : K.Normal := {
    conj_mem := by
      intro t ht u
      obtain ⟨n, rfl⟩ := ht
      refine ⟨n, ?_⟩
      rw [← scalar_comm n u, mul_assoc, mul_inv_cancel, mul_one]
  }
  let z0 : Z →* Twisted σ := {
    toFun := fun c => ⟨1, c⟩
    map_one' := rfl
    map_mul' := by
      intro c d
      apply Twisted.ext
      · exact (one_mul _).symm
      · change c * d = c * d * σ 1 1
        rw [hlaw.one_left]
        simp
  }
  let z : Z →* Twisted σ ⧸ K := (QuotientGroup.mk' K).comp z0
  let base : Twisted σ →* B := {
    toFun := Twisted.base
    map_one' := rfl
    map_mul' := fun _ _ => rfl
  }
  let pr0 : Twisted σ →* B ⧸ N := (QuotientGroup.mk' N).comp base
  have hK : K ≤ pr0.ker := by
    rintro t ⟨n, rfl⟩
    change (QuotientGroup.mk n.1 : B ⧸ N) = 1
    exact (QuotientGroup.eq_one_iff _).mpr n.2
  let pr : (Twisted σ ⧸ K) →* B ⧸ N := QuotientGroup.lift K pr0 hK
  let sec : B → Twisted σ ⧸ K := fun g => QuotientGroup.mk (⟨g, 1⟩ : Twisted σ)
  have sec_pr : ∀ g : B, pr (sec g) = QuotientGroup.mk g := by
    intro g
    exact QuotientGroup.lift_mk K hK _
  have z_inj : Function.Injective z := by
    apply (injective_iff_map_eq_one z).mpr
    intro c hc
    have hzc : z0 c ∈ K := (QuotientGroup.eq_one_iff _).mp hc
    obtain ⟨n, hn⟩ := hzc
    have hp := congrArg Twisted.phase hn
    exact hp.symm
  have z_central : ∀ c x, z c * x = x * z c := by
    intro c x
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective K x
    change QuotientGroup.mk' K (z0 c) * QuotientGroup.mk' K t =
      QuotientGroup.mk' K t * QuotientGroup.mk' K (z0 c)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Twisted.ext
    · exact (one_mul _).trans (mul_one _).symm
    · change c * t.phase * σ 1 t.base = t.phase * c * σ t.base 1
      rw [hlaw.one_left, hlaw.one_right]
      simp [mul_comm]
  have pr_ker : pr.ker = z.range := by
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective K x
      have ht : t.base ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact hx
      let n : N := ⟨t.base, ht⟩
      have heq : scalar n * z0 t.phase = t := by
        apply Twisted.ext
        · exact mul_one _
        · change 1 * t.phase * σ t.base 1 = t.phase
          rw [hlaw.one_right]
          simp
      have hs : QuotientGroup.mk' K (scalar n) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨n, rfl⟩
      refine ⟨t.phase, ?_⟩
      change QuotientGroup.mk' K (z0 t.phase) = QuotientGroup.mk' K t
      calc
        _ = QuotientGroup.mk' K (scalar n * z0 t.phase) := by
          rw [map_mul, hs, one_mul]
        _ = _ := congrArg (QuotientGroup.mk' K) heq
    · rintro ⟨c, rfl⟩
      change pr (QuotientGroup.mk (z0 c)) = 1
      rw [QuotientGroup.lift_mk]
      rfl
  have sec_mul : ∀ g h : B, sec g * sec h = z (σ g h) * sec (g * h) := by
    intro g h
    change QuotientGroup.mk' K (⟨g, 1⟩ : Twisted σ) *
        QuotientGroup.mk' K (⟨h, 1⟩ : Twisted σ) =
      QuotientGroup.mk' K (z0 (σ g h)) *
        QuotientGroup.mk' K (⟨g * h, 1⟩ : Twisted σ)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Twisted.ext
    · exact (one_mul _).symm
    · change 1 * 1 * σ g h = σ g h * 1 * σ 1 (g * h)
      rw [hlaw.one_left]
      simp
  refine ⟨{
    E := Twisted σ ⧸ K
    z := z
    z_inj := z_inj
    z_central := z_central
    pr := pr
    pr_surj := ?_
    pr_ker := pr_ker
    sec := sec
    sec_mul := sec_mul
    sec_pr := sec_pr
    sec_triv := ?_
  }⟩
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨sec g, sec_pr g⟩
  · intro g hg
    change QuotientGroup.mk' K (scalar ⟨g, hg⟩) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨g, hg⟩, rfl⟩

end ArtinPrimitiveRoots.A1.Theta.TH_COVER
