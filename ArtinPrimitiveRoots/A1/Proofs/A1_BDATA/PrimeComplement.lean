import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.Symplectic
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

set_option backward.isDefEq.respectTransparency.types false in
/-- Transfer the isotropic complement construction to a finite group of prime
exponent by identifying its root-of-unity pairing with a ZMod bilinear form. -/
theorem prime_exponent_complement {p : ℕ} [Fact p.Prime]
    {F G : Type} [Field F] [CommGroup G] [Finite G]
    (hmu : ∃ ζ : F, IsPrimitiveRoot ζ p) (hexp : ∀ x : G, x ^ p = 1)
    (β : G →* (G →* rootsOfUnity p F))
    (ha : ∀ x : G, β x x = 1)
    (hn : ∀ x : G, (∀ y : G, β x y = 1) → x = 1)
    (E : Subgroup G) (hcard : Nat.card G = (Nat.card E) ^ 2)
    (hE : ∀ x ∈ E, ∀ y ∈ E, β x y = 1) :
    ∃ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, β x y = 1) ∧ IsCompl E B := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  let p := k.succ
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  let eμ : rootsOfUnity p F ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hζ.card_rootsOfUnity
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p)).trans
        (Nat.card_zmod p))
  letI : CommSemiring (ZMod p) := (ZMod.commRing p).toCommSemiring
  letI : Semiring (ZMod p) := (ZMod.commRing p).toSemiring
  letI : AddCommMonoid (Additive G) :=
    (inferInstance : AddCommGroup (Additive G)).toAddCommMonoid
  letI modp : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (n := p) (fun x => by
    apply Additive.toMul.injective
    change Additive.toMul x ^ p = 1
    exact hexp (Additive.toMul x))
  let oAdd := AddSubgroup.toZModSubmodule (M := Additive G) p
  let oGroup := Subgroup.toAddSubgroup (G := G)
  let o := @OrderIso.trans _ _ _ _ _
    ((@Submodule.instPartialOrder (ZMod p) (Additive G)
      (ZMod.commRing p).toSemiring
      (inferInstance : AddCommGroup (Additive G)).toAddCommMonoid modp).toLE) oGroup oAdd
  let f (x : Additive G) : Additive G →+ ZMod p :=
    (eμ.toMonoidHom.comp (β x.toMul)).toAdditiveLeft
  let χ : Additive G →+ (Additive G →+ ZMod p) :=
    { toFun := f
      map_zero' := by
        apply AddMonoidHom.ext
        intro y
        change (eμ (β 1 y.toMul)).toAdd = 0
        rw [β.map_one]
        change (eμ 1).toAdd = 0
        rw [eμ.map_one]
        rfl
      map_add' := by
        intro x y
        apply AddMonoidHom.ext
        intro z
        change (eμ (β (x.toMul * y.toMul) z.toMul)).toAdd =
          (eμ (β x.toMul z.toMul)).toAdd + (eμ (β y.toMul z.toMul)).toAdd
        rw [β.map_mul]
        change (eμ (β x.toMul z.toMul * β y.toMul z.toMul)).toAdd = _
        rw [eμ.map_mul]
        rfl }
  let γ : LinearMap.BilinForm (ZMod p) (Additive G) :=
    LinearMap.mk₂ (ZMod p) (fun x y => χ x y)
      (fun x y z => by
        simpa only [AddMonoidHom.add_apply] using
          congrArg (fun a : Additive G →+ ZMod p => a z) (χ.map_add x y))
      (fun c x y => by
        simpa only [AddMonoidHom.smul_apply, smul_eq_mul] using
          congrArg (fun a : Additive G →+ ZMod p => a y) (ZMod.map_smul χ c x))
      (fun x y z => (χ x).map_add y z)
      (fun c x y => by simpa only [smul_eq_mul] using ZMod.map_smul (χ x) c y)
  have hγ (x y : Additive G) :
      γ x y = (eμ (β x.toMul y.toMul)).toAdd := rfl
  have hzero (x y : Additive G) : γ x y = 0 ↔ β x.toMul y.toMul = 1 := by
    rw [hγ]
    constructor
    · intro h
      apply eμ.injective
      apply Multiplicative.toAdd.injective
      rw [eμ.map_one]
      exact h
    · intro h
      rw [h, eμ.map_one]
      rfl
  have halt : γ.IsAlt := by
    intro x
    exact (hzero x x).mpr (ha x.toMul)
  have hleft : γ.SeparatingLeft := by
    intro x hx
    apply Additive.toMul.injective
    change x.toMul = 1
    apply hn
    intro y
    exact (hzero x (Additive.ofMul y)).mp (hx (Additive.ofMul y))
  have hnondeg : γ.Nondegenerate := by
    constructor
    · exact hleft
    · intro x hx
      apply hleft x
      intro y
      rw [← halt.neg_eq, hx y, neg_zero]
  let eE : E ≃ o E :=
    { toFun := fun x => ⟨Additive.ofMul (x : G), x.property⟩
      invFun := fun x => ⟨Additive.toMul (x : Additive G), x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hGcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) :=
    (Nat.card_congr (Additive.ofMul : G ≃ Additive G)).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)))
  have hEcard : Nat.card E = p ^ Module.finrank (ZMod p) (o E) :=
    (Nat.card_congr eE).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod p) (V := o E)))
  have hpow : p ^ Module.finrank (ZMod p) (Additive G) =
      p ^ (2 * Module.finrank (ZMod p) (o E)) := by
    rw [← hGcard, hcard, hEcard, ← pow_mul, Nat.mul_comm]
  have hdim : Module.finrank (ZMod p) (Additive G) =
      2 * Module.finrank (ZMod p) (o E) := by
    have hfac := congrArg (fun n : ℕ => n.factorization p) hpow
    simpa only [p, Nat.factorization_pow_self hp] using hfac
  have hisoE : ∀ x y : o E, γ x y = 0 := by
    intro x y
    apply (hzero (x : Additive G) (y : Additive G)).mpr
    exact hE (x : Additive G).toMul x.property (y : Additive G).toMul y.property
  obtain ⟨B, hiso, hcompl⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_bdata_sol.lagrangian_complement γ halt hnondeg
      (o E) hisoE hdim
  refine ⟨o.symm B, ?_, ?_⟩
  · intro x hx y hy
    have hxB : Additive.ofMul x ∈ B := hx
    have hyB : Additive.ofMul y ∈ B := hy
    exact (hzero (Additive.ofMul x) (Additive.ofMul y)).mp
      (hiso ⟨Additive.ofMul x, hxB⟩ ⟨Additive.ofMul y, hyB⟩)
  · simpa only [o.symm_apply_apply E] using hcompl.map o.symm

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
