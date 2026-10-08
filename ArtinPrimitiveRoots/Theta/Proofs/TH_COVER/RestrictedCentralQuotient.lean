import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false
open Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol.RestrictedCentral

variable {I J Z : Type} {G : I → Type} {H : J → Type}
variable [CommGroup Z] [∀ i, Group (G i)] [∀ j, Group (H j)]

/-- Finite-place groups and the independent infinite-place groups. -/
abbrev Component : I ⊕ J → Type
  | .inl i => G i
  | .inr j => H j

instance componentGroup (p : I ⊕ J) : Group (Component (G := G) (H := H) p) := by
  cases p with
  | inl i => exact inferInstanceAs (Group (G i))
  | inr j => exact inferInstanceAs (Group (H j))

/-- The infinite places are unrestricted. -/
def reference (B : ∀ i, Subgroup (G i)) : ∀ p, Subgroup (Component (G := G) (H := H) p)
  | .inl i => B i
  | .inr _ => ⊤

abbrev RP (B : ∀ i, Subgroup (G i)) :=
  RestrictedProduct (Component (G := G) (H := H)) (fun p => (reference (H := H) B p : Set (Component (G := G) (H := H) p))) cofinite

instance rpGroup (B : ∀ i, Subgroup (G i)) : Group (RP (H := H) B) := inferInstance

variable [∀ i, TopologicalSpace (G i)] [∀ j, TopologicalSpace (H j)]

instance componentTopology (p : I ⊕ J) : TopologicalSpace (Component (G := G) (H := H) p) := by
  cases p with
  | inl i => exact inferInstanceAs (TopologicalSpace (G i))
  | inr j => exact inferInstanceAs (TopologicalSpace (H j))

instance componentTopGroup [∀ i, IsTopologicalGroup (G i)] [∀ j, IsTopologicalGroup (H j)]
    (p : I ⊕ J) : IsTopologicalGroup (Component (G := G) (H := H) p) := by
  cases p with
  | inl i => exact inferInstanceAs (IsTopologicalGroup (G i))
  | inr j => exact inferInstanceAs (IsTopologicalGroup (H j))

/-- The native restricted-product quotient, with its exact central equivalence relation. -/
structure CentralQuotient (B : ∀ i, Subgroup (G i)) (z : ∀ i, Z →* G i) where
  Q : Type
  [grp : Group Q]
  [top : TopologicalSpace Q]
  [tg : IsTopologicalGroup Q]
  q : RP (H := H) B →* Q
  q_surj : Function.Surjective q
  q_quotient : IsQuotientMap q
  q_eq : ∀ x y, q x = q y ↔ ∃ ζ : I → Z,
    (Function.mulSupport ζ).Finite ∧ (∏ᶠ i, ζ i) = 1 ∧
    (∀ i, (x (.inl i) : G i) = z i (ζ i) * (y (.inl i) : G i)) ∧ ∀ j, x (.inr j) = y (.inr j)
  incl_inj : ∀ i, Function.Injective
    (q.comp (RestrictedProduct.mulSingleMonoidHom (reference (H := H) B) (.inl i)))
  incl_comm : ∀ (p p' : I ⊕ J), p ≠ p' → ∀ g h,
    q (RestrictedProduct.mulSingle (reference (H := H) B) p g) *
      q (RestrictedProduct.mulSingle (reference (H := H) B) p' h) =
    q (RestrictedProduct.mulSingle (reference (H := H) B) p' h) *
      q (RestrictedProduct.mulSingle (reference (H := H) B) p g)
  incl_z : ∀ i i' ζ,
    q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ)) =
    q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i') (z i' ζ))
  phase_central : ∀ i ζ g,
    q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ)) * g =
      g * q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ))

attribute [instance] CentralQuotient.grp CentralQuotient.top CentralQuotient.tg

/-- Divide by finitely supported central phases of product one. -/
theorem exists_centralQuotient [∀ i, IsTopologicalGroup (G i)] [∀ j, IsTopologicalGroup (H j)]
    (B : ∀ i, Subgroup (G i)) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (z : ∀ i, Z →* G i) (hz : ∀ i, Function.Injective (z i))
    (hc : ∀ i ζ g, z i ζ * g = g * z i ζ) :
    Nonempty (CentralQuotient (H := H) B z) := by
  classical
  let N : Subgroup (RP (H := H) B) := {
    carrier := {x | ∃ ζ : I → Z, (Function.mulSupport ζ).Finite ∧
      (∏ᶠ i, ζ i) = 1 ∧
      (∀ i, (x (.inl i) : G i) = z i (ζ i)) ∧ ∀ j, x (.inr j) = 1}
    one_mem' := by
      refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩ <;> simp
    mul_mem' := by
      rintro x y ⟨ζ, hζ, hpζ, hx, hxC⟩ ⟨ξ, hξ, hpξ, hy, hyC⟩
      refine ⟨fun i => ζ i * ξ i, Function.HasFiniteMulSupport.mul hζ hξ, ?_, ?_, ?_⟩
      · rw [finprod_mul_distrib hζ hξ, hpζ, hpξ, one_mul]
      · intro i
        change (x (.inl i) : G i) * y (.inl i) = z i (ζ i * ξ i)
        rw [hx, hy, map_mul]
      · intro j
        change x (.inr j) * y (.inr j) = 1
        rw [hxC, hyC, one_mul]
    inv_mem' := by
      rintro x ⟨ζ, hζ, hpζ, hx, hxC⟩
      refine ⟨fun i => (ζ i)⁻¹, Function.HasFiniteMulSupport.inv hζ, ?_, ?_, ?_⟩
      · rw [finprod_inv_distrib, hpζ, inv_one]
      · intro i
        change ((x (.inl i) : G i))⁻¹ = z i ((ζ i)⁻¹)
        rw [hx, map_inv]
      · intro j
        change (x (.inr j))⁻¹ = 1
        rw [hxC, inv_one]
  }
  have hNcent : ∀ n ∈ N, ∀ g : RP (H := H) B, n * g = g * n := by
    rintro n ⟨ζ, hζ, hpζ, hn, hnC⟩ g
    apply RestrictedProduct.ext
    intro p
    cases p with
    | inl i =>
      change (n (.inl i) : G i) * g (.inl i) = g (.inl i) * n (.inl i)
      rw [hn]
      exact hc i (ζ i) (g (.inl i))
    | inr j =>
      change n (.inr j) * g (.inr j) = g (.inr j) * n (.inr j)
      rw [hnC, one_mul, mul_one]
  letI : N.Normal := {
    conj_mem := by
      intro n hn g
      rw [← hNcent n hn g, mul_assoc, mul_inv_cancel, mul_one]
      exact hn
  }
  letI : Fact (∀ p : I ⊕ J, IsOpen (reference (H := H) B p : Set (Component (G := G) (H := H) p))) := ⟨by
    intro p
    cases p with
    | inl i => exact hB i
    | inr j => exact isOpen_univ⟩
  letI : IsTopologicalGroup (RP (H := H) B) := inferInstance
  let Q := RP (H := H) B ⧸ N
  let q : RP (H := H) B →* Q := QuotientGroup.mk' N
  have hq : ∀ x y, q x = q y ↔ ∃ ζ : I → Z,
      (Function.mulSupport ζ).Finite ∧ (∏ᶠ i, ζ i) = 1 ∧
      (∀ i, (x (.inl i) : G i) = z i (ζ i) * (y (.inl i) : G i)) ∧
      ∀ j, x (.inr j) = y (.inr j) := by
    intro x y
    change ((x : RP (H := H) B ⧸ N) = (y : RP (H := H) B ⧸ N)) ↔ _
    rw [QuotientGroup.eq_iff_div_mem]
    constructor
    · rintro ⟨ζ, hζ, hpζ, hf, hC⟩
      refine ⟨ζ, hζ, hpζ, ?_, ?_⟩
      · intro i
        exact div_eq_iff_eq_mul.mp (hf i)
      · intro j
        exact div_eq_one.mp (hC j)
    · rintro ⟨ζ, hζ, hpζ, hf, hC⟩
      refine ⟨ζ, hζ, hpζ, ?_, ?_⟩
      · intro i
        exact div_eq_iff_eq_mul.mpr (hf i)
      · intro j
        exact div_eq_one.mpr (hC j)
  have hsingleInj : ∀ i, Function.Injective
      (q.comp (RestrictedProduct.mulSingleMonoidHom (reference (H := H) B) (.inl i))) := by
    intro i g h heq
    obtain ⟨ζ, hζ, hpζ, hf, hC⟩ := (hq _ _).mp heq
    have hout : ∀ k, k ≠ i → ζ k = 1 := by
      intro k hki
      have hk := hf k
      have hk' : z k (ζ k) = 1 := by
        simpa [RestrictedProduct.coe_mulSingle_apply, hki] using hk.symm
      exact hz k (hk'.trans (map_one (z k)).symm)
    have hprod : (∏ᶠ k, ζ k) = ζ i := finprod_eq_single ζ i hout
    have hi : ζ i = 1 := hprod.symm.trans hpζ
    have he := hf i
    simpa [RestrictedProduct.coe_mulSingle_apply, hi] using he
  have hsingleComm : ∀ (p p' : I ⊕ J), p ≠ p' → ∀ g h,
      q (RestrictedProduct.mulSingle (reference (H := H) B) p g) *
        q (RestrictedProduct.mulSingle (reference (H := H) B) p' h) =
      q (RestrictedProduct.mulSingle (reference (H := H) B) p' h) *
        q (RestrictedProduct.mulSingle (reference (H := H) B) p g) := by
    intro p p' hpp g h
    rw [← map_mul, ← map_mul]
    congr 1
    apply RestrictedProduct.ext
    intro r
    by_cases hr : r = p
    · subst r
      simp [RestrictedProduct.coe_mulSingle_apply, hpp]
    · by_cases hr' : r = p'
      · subst r
        simp [RestrictedProduct.coe_mulSingle_apply, hpp.symm]
      · simp [RestrictedProduct.coe_mulSingle_apply, hr, hr']
  have hphaseSame : ∀ i i' ζ,
      q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ)) =
      q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i') (z i' ζ)) := by
    intro i i' ζ
    by_cases hii : i = i'
    · subst i'
      rfl
    let s : I → Z := Pi.mulSingle i ζ
    let t : I → Z := Pi.mulSingle i' ζ
    have hs : (Function.mulSupport s).Finite :=
      (Set.finite_singleton i).subset Pi.mulSupport_mulSingle_subset
    have ht : (Function.mulSupport t).Finite :=
      (Set.finite_singleton i').subset Pi.mulSupport_mulSingle_subset
    apply (hq _ _).mpr
    refine ⟨fun k => s k / t k, Function.HasFiniteMulSupport.div hs ht, ?_, ?_, ?_⟩
    · rw [finprod_div_distrib hs ht,
        finprod_eq_single s i (fun k hk => by simpa [s] using (Pi.mulSingle_eq_of_ne (M := fun _ : I => Z) hk ζ)),
        finprod_eq_single t i' (fun k hk => by simpa [t] using (Pi.mulSingle_eq_of_ne (M := fun _ : I => Z) hk ζ))]
      simp [s, t]
    · intro k
      by_cases hki : k = i
      · subst k
        simp [s, t, RestrictedProduct.coe_mulSingle_apply, hii]
      · by_cases hki' : k = i'
        · subst k
          simp [s, t, RestrictedProduct.coe_mulSingle_apply, (Ne.symm hii)]
        · simp [s, t, RestrictedProduct.coe_mulSingle_apply, hki, hki']
    · intro j
      simp [RestrictedProduct.coe_mulSingle_apply]
  have hphaseCentral : ∀ i ζ g,
      q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ)) * g =
        g * q (RestrictedProduct.mulSingle (reference (H := H) B) (.inl i) (z i ζ)) := by
    intro i ζ g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N g
    rw [← map_mul, ← map_mul]
    congr 1
    apply RestrictedProduct.ext
    intro p
    cases p with
    | inl k =>
      by_cases hki : k = i
      · subst k
        simpa [RestrictedProduct.coe_mulSingle_apply] using hc i ζ (x (.inl i))
      · simp [RestrictedProduct.coe_mulSingle_apply, hki]
    | inr j => simp [RestrictedProduct.coe_mulSingle_apply]
  exact ⟨{
    Q := Q
    grp := inferInstance
    top := inferInstance
    tg := inferInstance
    q := q
    q_surj := QuotientGroup.mk'_surjective N
    q_quotient := QuotientGroup.isQuotientMap_mk N
    q_eq := hq
    incl_inj := hsingleInj
    incl_comm := hsingleComm
    incl_z := hphaseSame
    phase_central := hphaseCentral
  }⟩

end ArtinPrimitiveRoots.Proofs.th_cover_sol.RestrictedCentral
