import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroWindows

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Among one more evenly spaced heights than ordinates, one stays uniformly separated. -/
theorem finite_ordinates_gap (S : Finset ℝ) (a : ℝ) :
    ∃ T : ℝ, T ∈ Set.Icc a (a + 1) ∧
      ∀ u ∈ S, (1 : ℝ) / (4 * ((S.card : ℝ) + 1)) ≤ |T - u| := by
  classical
  let n : ℝ := (S.card : ℝ) + 1
  have hn : 0 < n := by dsimp [n]; positivity
  let ε : ℝ := 1 / (4 * n)
  let p : Fin (S.card + 1) → ℝ := fun i => a + (i.val : ℝ) / n
  have hpoints (i : Fin (S.card + 1)) : p i ∈ Set.Icc a (a + 1) := by
    have hnum : (i.val : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast (Nat.le_of_lt i.is_lt)
    have hquot : (i.val : ℝ) / n ≤ 1 :=
      (div_le_iff₀ hn).2 (by simpa using hnum)
    have hquot₀ : 0 ≤ (i.val : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn.le
    exact ⟨le_add_of_nonneg_right hquot₀, by dsimp [p]; linarith⟩
  have hspacing (i j : Fin (S.card + 1)) (hij : i ≠ j) : 1 / n ≤ |p i - p j| := by
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hindex : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hlt)
        rw [abs_of_nonpos (by linarith : (i.val : ℝ) - (j.val : ℝ) ≤ 0)]
        linarith
      · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hgt)
        rw [abs_of_nonneg (by linarith : 0 ≤ (i.val : ℝ) - (j.val : ℝ))]
        linarith
    have hp : p i - p j = ((i.val : ℝ) - (j.val : ℝ)) / n := by dsimp [p]; ring
    rw [hp, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right hindex hn.le
  have hε : 2 * ε < 1 / n := by
    have heq : 2 * ε = (1 / n) / 2 := by
      dsimp [ε]
      field_simp [hn.ne'] <;> ring
    have hpos : 0 < (1 : ℝ) / n := one_div_pos.mpr hn
    rw [heq]
    linarith
  by_contra h
  have hbad (i : Fin (S.card + 1)) : ∃ u : ℝ, u ∈ S ∧ |p i - u| < ε := by
    by_contra hnone
    apply h
    refine ⟨p i, hpoints i, ?_⟩
    intro u hu
    by_contra hdist
    exact hnone ⟨u, hu, lt_of_not_ge hdist⟩
  let bad : Fin (S.card + 1) → S := fun i =>
    ⟨(hbad i).choose, (hbad i).choose_spec.1⟩
  have hclose (i : Fin (S.card + 1)) : |p i - (bad i : ℝ)| < ε :=
    (hbad i).choose_spec.2
  have hinj : Function.Injective bad := by
    intro i j hij
    by_contra hne
    have hval : (bad i : ℝ) = (bad j : ℝ) := congrArg Subtype.val hij
    have hclosej : |(bad i : ℝ) - p j| < ε := by
      rw [hval, abs_sub_comm]
      exact hclose j
    have hnear : |p i - p j| < 2 * ε :=
      (abs_sub_le (p i) (bad i : ℝ) (p j)).trans_lt (by linarith [hclose i, hclosej])
    exact not_lt_of_ge (hspacing i j hne) (hnear.trans hε)
  have hcard := Fintype.card_le_of_injective bad hinj
  rw [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
