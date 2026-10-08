import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RestrictedProduct

set_option autoImplicit false

open MeasureTheory Topology Set
open scoped Classical Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem addFundamentalDomain_refine_finite (α : Type*) [NormedAddCommGroup α]
    [MeasurableSpace α] (μ : Measure α) (A B : AddSubgroup α) (hBA : B ≤ A)
    (hfinite : Finite (A ⧸ B.comap A.subtype)) (Pd : Set α)
    (htransMeas : ∀ a : α, MeasurableSet (a +ᵥ Pd))
    (hPd : IsAddFundamentalDomain A Pd μ)
    (hPdBound : Bornology.IsBounded Pd) :
    ∃ D : Set α, IsAddFundamentalDomain B D μ ∧
      Bornology.IsBounded D ∧ MeasurableSet D := by
  classical
  let B' : AddSubgroup A := B.comap A.subtype
  letI : Finite (A ⧸ B') := hfinite
  let rep : A ⧸ B' → A := fun q => q.out
  let inc (b : B) : A := ⟨(b : α), hBA b.2⟩
  let D : Set α := ⋃ q : A ⧸ B', (rep q : α) +ᵥ Pd
  have htransMeas' (q : A ⧸ B') : MeasurableSet ((rep q : α) +ᵥ Pd) := htransMeas _
  have hDMeas : MeasurableSet D := by
    dsimp [D]
    exact MeasurableSet.iUnion htransMeas'
  have htransBound (q : A ⧸ B') : Bornology.IsBounded ((rep q : α) +ᵥ Pd) := by
    change Bornology.IsBounded ((fun x : α => (rep q : α) + x) '' Pd)
    have hIso : Isometry (fun x : α => (rep q : α) + x) := by
      intro x y
      simp [dist_eq_norm, add_sub_add_left_eq_sub]
    exact hIso.lipschitz.isBounded_image hPdBound
  have hDBound : Bornology.IsBounded D := by
    dsimp [D]
    rw [Bornology.isBounded_iUnion]
    exact htransBound
  have hCover : ∀ᵐ x ∂μ, ∃ b : B, b +ᵥ x ∈ D := by
    filter_upwards [hPd.ae_covers] with x hx
    obtain ⟨a, ha⟩ := hx
    let q : A ⧸ B' := QuotientAddGroup.mk (s := B') (-a)
    have hqrep : QuotientAddGroup.mk (s := B') (rep q) = q :=
      QuotientAddGroup.out_eq' q
    have hqsum : QuotientAddGroup.mk (s := B') (rep q + a) = 0 := by
      rw [QuotientAddGroup.mk_add, hqrep]
      simp [q]
    have hbA : rep q + a ∈ B' := (QuotientAddGroup.eq_zero_iff _).mp hqsum
    let bA : A := ⟨rep q + a, A.add_mem (rep q).2 a.2⟩
    have hbA' : bA ∈ B' := by
      change (rep q + a : A) ∈ B'
      exact hbA
    let b : B := ⟨(bA : α), by
      change (rep q + a : A) ∈ B'
      exact hbA'⟩
    refine ⟨b, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    rw [Set.mem_vadd_set]
    refine ⟨a +ᵥ x, ha, ?_⟩
    change (rep q : α) + ((a : α) + x) = (b : α) + x
    change (rep q : α) + ((a : α) + x) = (rep q : α) + (a : α) + x
    calc
      (rep q : α) + ((a : α) + x) = ((rep q : α) + (a : α)) + x :=
        (add_assoc _ _ _).symm
      _ = (b : α) + x := rfl
  have htranslate (b : B) :
      b +ᵥ D = ⋃ q : A ⧸ B', ((inc b + rep q : A) : α) +ᵥ Pd := by
    ext x
    simp only [D, Set.vadd_iUnion, Set.mem_vadd_set, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨q, z, hz, rfl⟩, rfl⟩
      refine ⟨q, z, hz, ?_⟩
      change ((inc b + rep q : A) : α) + z = (b : α) + ((rep q : α) + z)
      exact add_assoc _ _ _
    · rintro ⟨q, z, hz, rfl⟩
      refine ⟨(rep q : α) +ᵥ z, ⟨q, z, hz, rfl⟩, ?_⟩
      change (b : α) + ((rep q : α) + z) = ((inc b + rep q : A) : α) + z
      exact (add_assoc _ _ _).symm
  have hDisjoint : ∀ b₁ b₂ : B, b₁ ≠ b₂ → AEDisjoint μ (b₁ +ᵥ D) (b₂ +ᵥ D) := by
    intro b₁ b₂ hne
    rw [htranslate b₁, htranslate b₂]
    simp only [AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    intro q₁ q₂
    apply hPd.aedisjoint
    intro hEq
    let b₁A : A := ⟨(b₁ : α), hBA b₁.2⟩
    let b₂A : A := ⟨(b₂ : α), hBA b₂.2⟩
    have hb₁' : b₁A ∈ B' := by
      change (b₁A : α) ∈ B
      exact b₁.2
    have hb₂' : b₂A ∈ B' := by
      change (b₂A : α) ∈ B
      exact b₂.2
    have hqL : QuotientAddGroup.mk (s := B') (b₁A + rep q₂) = q₂ := by
      rw [add_comm b₁A (rep q₂), QuotientAddGroup.mk_add_of_mem (rep q₂) hb₁']
      exact QuotientAddGroup.out_eq' q₂
    have hqR : QuotientAddGroup.mk (s := B') (b₂A + rep q₁) = q₁ := by
      rw [add_comm b₂A (rep q₁), QuotientAddGroup.mk_add_of_mem (rep q₁) hb₂']
      exact QuotientAddGroup.out_eq' q₁
    have hq : q₁ = q₂ := by
      have h := congrArg (QuotientAddGroup.mk (s := B')) hEq
      rw [hqL, hqR] at h
      exact h.symm
    subst q₂
    have hbEq : b₁A = b₂A := add_right_cancel hEq
    apply hne
    have hval : (b₁ : α) = (b₂ : α) := congrArg (fun y : A => (y : α)) hbEq
    exact Subtype.ext hval
  refine ⟨D, ⟨hDMeas.nullMeasurableSet, hCover, ?_⟩, hDBound, hDMeas⟩
  intro b₁ b₂ hne
  exact hDisjoint b₁ b₂ hne

end ArtinPrimitiveRoots.A1.Theta
