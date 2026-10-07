import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_positive_choice_rows
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private def pd5_birthLayer {K : ℕ} : BirthAddress K → ℕ
  | .initial _ _ => 0
  | .ghost j _ _ => 2 * j + 1
  | .edge j _ => 2 * j + 2

private def pd5_birthGroup {K : ℕ} : BirthAddress K → ℕ
  | .initial i _ => i.val
  | .ghost _ i _ => i.val
  | .edge _ i => i.val

private def pd5_birthOffset {K : ℕ} : BirthAddress K → ℕ
  | .initial _ k => k
  | .ghost _ _ k => k
  | .edge _ _ => 0

private theorem pd5_mul_add_injective (q r q' r' d : ℕ) (hd : 0 < d)
    (hr : r < d) (hr' : r' < d) (h : q * d + r = q' * d + r') :
    q = q' ∧ r = r' := by
  have hq : q = q' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : q + 1 ≤ q' := Nat.succ_le_of_lt hlt
      have hmul : (q + 1) * d ≤ q' * d := Nat.mul_le_mul_right d hlt'
      have hupper : q * d + r < (q + 1) * d := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left hr (q * d)
      have hle : q' * d ≤ q' * d + r' := Nat.le_add_right _ _
      exact (Nat.ne_of_lt (lt_of_lt_of_le hupper (le_trans hmul hle))) h
    · have hlt' : q' + 1 ≤ q := Nat.succ_le_of_lt hgt
      have hmul : (q' + 1) * d ≤ q * d := Nat.mul_le_mul_right d hlt'
      have hupper : q' * d + r' < (q' + 1) * d := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left hr' (q' * d)
      have hle : q * d ≤ q * d + r := Nat.le_add_right _ _
      exact (Nat.ne_of_lt (lt_of_lt_of_le hupper (le_trans hmul hle))) h.symm
  constructor
  · exact hq
  · rw [hq] at h
    exact Nat.add_left_cancel h

private theorem pd5_birthIndex_eq_row (K : ℕ) (S : PDScale) (B : ℕ)
    (a : BirthAddress K) :
    pd5_birthIndex S B a =
      (pd5_birthLayer a * K + pd5_birthGroup a) * (max (slotCount S.x) B + 1) +
        pd5_birthOffset a := by
  cases a <;> simp [pd5_birthIndex, pd5_birthLayer, pd5_birthGroup, pd5_birthOffset]

private theorem pd5_birthIndex_injective_on {K : ℕ} (S : PDScale) (B : ℕ)
    {a b : BirthAddress K}
    (ha : a ∈ birthAddresses S.x K B) (hb : b ∈ birthAddresses S.x K B)
    (h : pd5_birthIndex S B a = pd5_birthIndex S B b) : a = b := by
  have hradix : 0 < max (slotCount S.x) B + 1 := by omega
  have hoff (a : BirthAddress K) (ha : a ∈ birthAddresses S.x K B) :
      pd5_birthOffset a < max (slotCount S.x) B + 1 := by
    cases a with
    | initial i k =>
        have hk : k < slotCount S.x := by
          simpa [birthAddresses] using ha
        dsimp [pd5_birthOffset]
        have hm : slotCount S.x ≤ max (slotCount S.x) B := Nat.le_max_left _ _
        omega
    | ghost j i k =>
        have hk : k < B := by
          have hh : j ≤ pathLength S.x ∧ k < B := by
            simpa [birthAddresses] using ha
          exact hh.2
        dsimp [pd5_birthOffset]
        have hm : B ≤ max (slotCount S.x) B := Nat.le_max_right _ _
        omega
    | edge j i =>
        dsimp [pd5_birthOffset]
        omega
  have hdecomp := pd5_mul_add_injective
    ((pd5_birthLayer a * K + pd5_birthGroup a)) (pd5_birthOffset a)
    ((pd5_birthLayer b * K + pd5_birthGroup b)) (pd5_birthOffset b)
    (max (slotCount S.x) B + 1) hradix (hoff a ha) (hoff b hb) (by
      simpa only [pd5_birthIndex_eq_row] using h)
  have hK : 0 < K := by
    cases a with
    | initial i k => have hi := i.isLt; omega
    | ghost j i k => have hi := i.isLt; omega
    | edge j i => have hi := i.isLt; omega
  have hgroupA : pd5_birthGroup a < K := by
    cases a <;> exact Fin.isLt _
  have hgroupB : pd5_birthGroup b < K := by
    cases b <;> exact Fin.isLt _
  have hrow := pd5_mul_add_injective (pd5_birthLayer a) (pd5_birthGroup a)
    (pd5_birthLayer b) (pd5_birthGroup b) K hK hgroupA hgroupB
    hdecomp.1
  have hlayer : pd5_birthLayer a = pd5_birthLayer b := hrow.1
  have hgroup : pd5_birthGroup a = pd5_birthGroup b := hrow.2
  have hoffset : pd5_birthOffset a = pd5_birthOffset b := hdecomp.2
  cases a with
  | initial ia ka =>
      cases b with
      | initial ib kb =>
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          have hk : ka = kb := by simpa [pd5_birthOffset] using hoffset
          cases Fin.ext hi
          cases hk
          rfl
      | ghost jb ib kb =>
          have hbad : 0 = 2 * jb + 1 := by simpa [pd5_birthLayer] using hlayer
          omega
      | edge jb ib =>
          have hbad : 0 = 2 * jb + 2 := by simpa [pd5_birthLayer] using hlayer
          omega
  | ghost ja ia ka =>
      cases b with
      | initial ib kb =>
          have hbad : 2 * ja + 1 = 0 := by simpa [pd5_birthLayer] using hlayer
          omega
      | ghost jb ib kb =>
          have hj : ja = jb := by
            have := hlayer
            simp [pd5_birthLayer] at this
            omega
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          have hk : ka = kb := by simpa [pd5_birthOffset] using hoffset
          cases hj
          cases Fin.ext hi
          cases hk
          rfl
      | edge jb ib =>
          have hbad : 2 * ja + 1 = 2 * jb + 2 := by
            simpa [pd5_birthLayer] using hlayer
          omega
  | edge ja ia =>
      cases b with
      | initial ib kb =>
          have hbad : 2 * ja + 2 = 0 := by simpa [pd5_birthLayer] using hlayer
          omega
      | ghost jb ib kb =>
          have hbad : 2 * ja + 2 = 2 * jb + 1 := by
            simpa [pd5_birthLayer] using hlayer
          omega
      | edge jb ib =>
          have hj : ja = jb := by
            have := hlayer
            simp [pd5_birthLayer] at this
            omega
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          cases hj
          cases Fin.ext hi
          rfl

private theorem pd5_exists_min_birth_index {K : ℕ} (S : PDScale) (B : ℕ)
    {D : Finset (BirthAddress K)} (hD : 2 ≤ D.card) :
    ∃ p ∈ D, ∀ a ∈ D, pd5_birthIndex S B p ≤ pd5_birthIndex S B a := by
  classical
  let I := D.image (pd5_birthIndex S B)
  have hDne : D.Nonempty := Finset.card_pos.mpr (by omega)
  have hIne : I.Nonempty := Finset.image_nonempty.mpr hDne
  have hmem : I.min' hIne ∈ I := Finset.min'_mem I hIne
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hmin⟩
  refine ⟨p, hp, ?_⟩
  intro a ha
  have hle := Finset.min'_le I (pd5_birthIndex S B a)
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  simpa [I, hmin] using hle

private theorem pd5_min_birth_index_strict {K : ℕ} (S : PDScale) (B : ℕ)
    {D : Finset (BirthAddress K)} (hD : 2 ≤ D.card)
    (hsub : D ⊆ birthAddresses S.x K B)
    {p a : BirthAddress K} (hp : p ∈ D) (ha : a ∈ D)
    (hmin : ∀ b ∈ D, pd5_birthIndex S B p ≤ pd5_birthIndex S B b)
    (hne : a ≠ p) : pd5_birthIndex S B p < pd5_birthIndex S B a := by
  have hle := hmin a ha
  by_contra hnot
  have heq : pd5_birthIndex S B p = pd5_birthIndex S B a := by omega
  exact hne (pd5_birthIndex_injective_on S B (hsub hp) (hsub ha) heq)

/-- Fixed-system absolute bound from positive choices, with chronological pivots.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:328–397`; uses pd5_positive_choice_rows,
pd5_triangular_birth_sum_le, pd5_chronological_model and pd5_scale_facts;
feeds pd5_high_rank_tail and frozen history_rank_high. Constants precede S,w and the system. -/
theorem pd5_fixed_system_abs_estimate (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hrows : PD5PositiveRowsAvailable δ c₁ c₂ F ρ) :
    ∃ Cabs aAtom x₀ : ℝ, 0 < Cabs ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
            Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
              (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
