import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.HistoryPhases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- The additive-character coefficient carried by one address after expanding each star-pair
phase into a left and a right factor. -/
noncomputable def pd5b_pairAddressCoeff {K T : ℕ} (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) (hC : IsConstraintSystem A C)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T)
    (a : BirthAddress K) : ZMod T :=
  (∑ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
      if p.1.1.1 = a then θ p else 0) -
    ∑ p : {p : A × A // p ∈ pd5_systemPairs A C hC},
      if p.1.2.1 = a then θ p else 0

/-- Phase multiplier for the births of one operation. `Ops` is the finite set of addresses that
could be born in this operation; a required address that was not performed contributes zero. -/
noncomputable def pd5b_localOperationPhase {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T)
    (U Ops : Finset (BirthAddress K)) (log : BirthLog K) : ℂ :=
  ∏ a ∈ Ops, if a ∈ U then
    match pd5b_label log a with
    | none => 0
    | some p => ZMod.stdAddChar
        (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))
  else 1

/-- Each local birth phase is a contraction. -/
theorem pd5b_localOperationPhase_norm_le_one {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T)
    (U Ops : Finset (BirthAddress K)) (log : BirthLog K) :
    ‖pd5b_localOperationPhase A C hC θ U Ops log‖ ≤ 1 := by
  classical
  let factor : BirthAddress K → ℂ := fun a =>
    if a ∈ U then
      (match pd5b_label log a with
      | none => 0
      | some p => ZMod.stdAddChar (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T)))
    else 1
  have hfactor (a : BirthAddress K) : ‖factor a‖ ≤ 1 := by
    by_cases hU : a ∈ U
    · simp only [factor, if_pos hU]
      cases hlabel : pd5b_label log a with
      | none => simp
      | some p =>
          rw [pd5b_finite_birth_character_norm]
    · simp [factor, hU]
  have hprod :
      pd5b_localOperationPhase A C hC θ U Ops log = ∏ a ∈ Ops, factor a := rfl
  calc
    ‖pd5b_localOperationPhase A C hC θ U Ops log‖ =
        ∏ a ∈ Ops, ‖factor a‖ := by rw [hprod, norm_prod]
    _ ≤ ∏ _a ∈ Ops, (1 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro a ha
            exact norm_nonneg _
          · intro a ha
            exact hfactor a
    _ = 1 := by simp

end

end ArtinPrimitiveRoots.TypeII.PD
