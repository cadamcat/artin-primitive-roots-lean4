import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Ranks
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.Characters

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- The unique value assigned to an address in a log with no repeated address. -/
noncomputable def pd5b_label {K : ℕ} (log : BirthLog K)
    (a : BirthAddress K) : Option ℕ :=
  if h : ∃ v, (a, v) ∈ log then some (Classical.choose h) else none

theorem pd5b_label_spec {K : ℕ} {log : BirthLog K}
    (hnodup : (log.map Prod.fst).Nodup) (a : BirthAddress K) (v : ℕ) :
    pd5b_label log a = some v ↔ (a, v) ∈ log := by
  classical
  have hunique {v w : ℕ} (hv : (a, v) ∈ log) (hw : (a, w) ∈ log) : v = w := by
    have hp : (a, v) = (a, w) :=
      List.inj_on_of_nodup_map (f := Prod.fst) hnodup hv hw rfl
    exact congrArg Prod.snd hp
  unfold pd5b_label
  by_cases h : ∃ u, (a, u) ∈ log
  · simp only [dif_pos h, Option.some.injEq]
    constructor
    · intro hv
      subst v
      exact Classical.choose_spec h
    · intro hv
      exact hunique (Classical.choose_spec h) hv
  · simp only [dif_neg h]
    constructor
    · intro hv
      cases hv
    · intro hv
      exact (h ⟨v, hv⟩).elim

/-- The modulus-reduced difference at one star pair. A missing birth has value `none`. -/
noncomputable def pd5b_pairDifference {K T : ℕ} (log : BirthLog K)
    (p : BirthAddress K × BirthAddress K) : Option (ZMod T) :=
  match pd5b_label log p.1, pd5b_label log p.2 with
  | some u, some v => some ((u : ZMod T) - (v : ZMod T))
  | _, _ => none

/-- A phase for each star constraint (pivot, other address) of a constraint system. Missing
addresses contribute zero, so an unperformed block has zero phase weight. -/
noncomputable def pd5b_systemPairPhase {K T : ℕ} [NeZero T] (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) (hC : IsConstraintSystem A C)
    (log : BirthLog K)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) : ℂ :=
  ∏ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
    match pd5b_pairDifference log (p.1.1.1, p.1.2.1) with
    | some t => ZMod.stdAddChar (θ p * t)
    | none => 0

/-- Averaging the star phases imposes equality of performed prime labels at every pair. -/
theorem pd5b_systemPairPhase_average {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (log : BirthLog K)
    (hlabelBound : ∀ a ∈ A, ∀ p, pd5b_label log a = some p → p < T) :
    ((Fintype.card
        ({p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) : ℂ)⁻¹) *
      ∑ θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T,
        pd5b_systemPairPhase A C hC log θ =
      ∏ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
        if ∃ v, pd5b_label log p.1.1.1 = some v ∧
            pd5b_label log p.1.2.1 = some v then (1 : ℂ) else 0 := by
  classical
  let Pair := {p : A × A // p ∈ pd5_systemPairs A C hC}
  letI : DecidableEq Pair := Subtype.instDecidableEq
  let d : Pair → Option (ZMod T) := fun p =>
    pd5b_pairDifference log (p.1.1.1, p.1.2.1)
  have hsum := pd5b_product_character_average_option (ι := Pair) (T := T) d
  have hd (p : Pair) :
      d p = some 0 ↔ ∃ v, pd5b_label log p.1.1.1 = some v ∧
        pd5b_label log p.1.2.1 = some v := by
    cases hL : pd5b_label log p.1.1.1 with
    | none => simp [d, pd5b_pairDifference, hL]
    | some u =>
        cases hR : pd5b_label log p.1.2.1 with
        | none => simp [d, pd5b_pairDifference, hL, hR]
        | some v =>
            have hu := hlabelBound p.1.1.1 p.1.1.2 u hL
            have hv := hlabelBound p.1.2.1 p.1.2.2 v hR
            have hcast : ((u : ZMod T) - (v : ZMod T) = 0) ↔ u = v := by
              rw [sub_eq_zero]
              constructor
              · intro heq
                have h := congrArg (fun z : ZMod T => z.val) heq
                rw [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at h
                exact h
              · rintro rfl
                rfl
            simp [d, pd5b_pairDifference, hL, hR, hcast, eq_comm]
  have hphaseAvg :
      ((Fintype.card (Pair → ZMod T) : ℂ)⁻¹) *
        ∑ θ : Pair → ZMod T, pd5b_systemPairPhase A C hC log θ =
      ∏ p : Pair, if d p = some 0 then (1 : ℂ) else 0 := by
    change ((Fintype.card (Pair → ZMod T) : ℂ)⁻¹) *
      ∑ θ : Pair → ZMod T,
        ∏ p : Pair, (match d p with
          | some t => ZMod.stdAddChar (θ p * t)
          | none => 0) =
      ∏ p : Pair, if d p = some 0 then (1 : ℂ) else 0
    exact hsum
  simpa only [hd] using hphaseAvg

end

end ArtinPrimitiveRoots.TypeII.PD
