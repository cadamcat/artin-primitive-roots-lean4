import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.ConstraintPhases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

private theorem pd5b_finset_prod_indicator {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] :
    s.prod (fun a => if P a then (1 : ℂ) else 0) =
      if ∀ a ∈ s, P a then 1 else 0 := by
  classical
  by_cases h : ∀ a ∈ s, P a
  · rw [if_pos h]
    exact Finset.prod_eq_one fun a ha => by simp [h a ha]
  · have hex : ∃ a ∈ s, ¬ P a := by
      push_neg at h
      exact h
    rcases hex with ⟨a, ha, hPa⟩
    have hz : s.prod (fun a => if P a then (1 : ℂ) else 0) = 0 := by
      exact Finset.prod_eq_zero ha (if_neg hPa)
    rw [if_neg h, hz]

private theorem pd5b_blockPairCondition_iff {K : ℕ}
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) :
    (∀ D ∈ C, ∃ v, ∀ a ∈ D, (a, v) ∈ log) ↔
      ∀ p ∈ pd5_systemPairs A C hC,
        ∃ v, pd5b_label log p.1.1 = some v ∧ pd5b_label log p.2.1 = some v := by
  constructor
  · intro h p hp
    obtain ⟨D, hD, hpD⟩ := (pd5_systemPairs_mem_iff A C hC p).mp hp
    have hprops := hC.1 D hD
    obtain ⟨b, hb, hpeq⟩ :=
      (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 p).mp hpD
    obtain ⟨v, hv⟩ := h D hD
    have hpivotVal :
        pd5b_label log (pd5_blockPivot D hprops.2).1 = some v :=
      (pd5b_label_spec hnodup _ v).2 (hv _ (pd5_blockPivot D hprops.2).2)
    have hbVal : pd5b_label log b.1 = some v :=
      (pd5b_label_spec hnodup _ v).2 (hv _ b.2)
    rw [hpeq]
    exact ⟨v, by simpa [pd5_toA] using hpivotVal,
      by simpa [pd5_toA] using hbVal⟩
  · intro h D hD
    have hprops := hC.1 D hD
    let pivot := pd5_blockPivot D hprops.2
    have hsize : 1 < D.card := by omega
    obtain ⟨other, hother, hotherNe⟩ := Finset.exists_mem_ne hsize pivot.1
    let b : {a // a ∈ D} := ⟨other, hother⟩
    have hbNe : b ≠ pivot := by
      intro hEq
      apply hotherNe
      exact congrArg Subtype.val hEq
    have hbErase : b ∈ D.attach.erase pivot :=
      Finset.mem_erase.mpr ⟨hbNe, by simp [b]⟩
    have hpBlock :
        (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b) ∈
          pd5_blockPairs A D hprops.1 hprops.2 :=
      (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 _).2
        ⟨b, hbErase, rfl⟩
    have hpairs :
        (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b) ∈
          pd5_systemPairs A C hC :=
      (pd5_systemPairs_mem_iff A C hC _).2 ⟨D, hD, hpBlock⟩
    obtain ⟨v, hpivotVal, hbVal⟩ := h _ hpairs
    have hpivotVal' : pd5b_label log pivot.1 = some v := by
      simpa [pd5_toA] using hpivotVal
    refine ⟨v, ?_⟩
    intro a ha
    let b' : {a // a ∈ D} := ⟨a, ha⟩
    by_cases hbp : b' = pivot
    · have haddr : a = pivot.1 := congrArg Subtype.val hbp
      subst a
      exact (pd5b_label_spec hnodup pivot.1 v).1 hpivotVal'
    · have hbErase' : b' ∈ D.attach.erase pivot :=
        Finset.mem_erase.mpr ⟨hbp, by simp [b']⟩
      have hpBlock' :
          (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b') ∈
            pd5_blockPairs A D hprops.1 hprops.2 :=
        (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 _).2
          ⟨b', hbErase', rfl⟩
      have hpairs' :
          (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b') ∈
            pd5_systemPairs A C hC :=
        (pd5_systemPairs_mem_iff A C hC _).2 ⟨D, hD, hpBlock'⟩
      obtain ⟨v', hpivotVal'', haVal⟩ := h _ hpairs'
      have hsame : v' = v := by
        exact Option.some.inj (hpivotVal''.symm.trans hpivotVal')
      have hval : pd5b_label log a = some v := by
        have hvalA : pd5b_label log a = some v' := by
          simpa [pd5_toA, b'] using haVal
        rw [hvalA, hsame]
      exact (pd5b_label_spec hnodup a v).1 hval

/-- For a log with unique addresses, the block-equality indicator is the product of the
pairwise star constraints selected by `pd5_systemPairs`. -/
theorem pd5b_constraintWeight_pairIndicator {K : ℕ}
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) :
    constraintWeight C log =
      ∏ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
        if ∃ v, pd5b_label log p.1.1.1 = some v ∧
            pd5b_label log p.1.2.1 = some v then (1 : ℂ) else 0 := by
  classical
  let BlockOK : Finset (BirthAddress K) → Prop :=
    fun D => ∃ v, ∀ a ∈ D, (a, v) ∈ log
  let PairOK : A × A → Prop :=
    fun p => ∃ v, pd5b_label log p.1.1 = some v ∧ pd5b_label log p.2.1 = some v
  have hiff : (∀ D ∈ C, BlockOK D) ↔
      ∀ p ∈ pd5_systemPairs A C hC, PairOK p := by
    exact pd5b_blockPairCondition_iff A C hC log hnodup
  by_cases hBlock : ∀ D ∈ C, BlockOK D
  · have hPair := hiff.mp hBlock
    unfold constraintWeight
    have hleft : C.prod (fun D => if BlockOK D then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (by
        intro D hD
        simp [hBlock D hD, BlockOK])
    have hright :
        (∏ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
          if PairOK p.1 then (1 : ℂ) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp [hPair p.1 p.2, PairOK]
    simpa [BlockOK] using hleft.trans hright.symm
  · have hPairNot : ¬ ∀ p ∈ pd5_systemPairs A C hC, PairOK p := by
      intro hPair
      exact hBlock (hiff.mpr hPair)
    push_neg at hBlock hPairNot
    rcases hBlock with ⟨D, hD, hDnot⟩
    rcases hPairNot with ⟨p, hp, hpnot⟩
    unfold constraintWeight
    have hleft : C.prod (fun D => if BlockOK D then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero hD (if_neg hDnot)
    let p' : {p : A × A // p ∈ pd5_systemPairs A C hC} := ⟨p, hp⟩
    have hright :
        (∏ q : {q : A × A // q ∈ pd5_systemPairs A C hC},
          if PairOK q.1 then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p') (if_neg hpnot)
    simpa [BlockOK, PairOK, p'] using hleft.trans hright.symm

/-- Finite additive characters express one `constraintWeight` as an average of phase products.
The finite modulus must exceed every possible prime label. -/
theorem pd5b_constraintWeight_fourier {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup)
    (hlabelBound : ∀ a ∈ A, ∀ p, pd5b_label log a = some p → p < T) :
    constraintWeight C log =
      ((Fintype.card
        ({p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) : ℂ)⁻¹) *
        ∑ θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T,
          pd5b_systemPairPhase A C hC log θ := by
  classical
  rw [pd5b_constraintWeight_pairIndicator A C hC log hnodup]
  symm
  exact pd5b_systemPairPhase_average A C hC log hlabelBound

end

end ArtinPrimitiveRoots.TypeII.PD
