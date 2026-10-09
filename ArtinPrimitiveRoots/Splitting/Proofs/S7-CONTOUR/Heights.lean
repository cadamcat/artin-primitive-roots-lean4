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

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Ext.SplittingInputs
open NumberField

/-- Every real unit interval contains a height quantitatively separated from all zero ordinates. -/
theorem zero_ordinates_gap (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, ∃ T : ℝ, T ∈ Set.Icc a (a + 1) ∧
      ∀ ρ : ℂ, ρ ∈ nontrivialZeros K → c / (1 + |a|) ≤ |T - ρ.im| := by
  classical
  obtain ⟨Czero, hCzero, hcount⟩ := ext_dedekind_zero_count
  have hD : 1 ≤ absoluteDiscriminant K := by
    have hNat : 1 ≤ (NumberField.discr K).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
    simpa [absoluteDiscriminant, Nat.cast_natAbs] using
      (show (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) by exact_mod_cast hNat)
  let d : ℝ := Real.log (absoluteDiscriminant K)
  let n : ℝ := Module.finrank ℚ K
  have hd : 0 ≤ d := Real.log_nonneg hD
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let W : ℝ := d + n
  have hW : 0 ≤ W := add_nonneg hd hn
  let A : ℝ := 6 * Czero * W + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let c : ℝ := 1 / (4 * (A + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₁ : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (A + 1))).2
    linarith
  refine ⟨c, hc, ?_⟩
  intro a
  let Z : ℝ → Set ℂ := fun b =>
    {ρ | ρ ∈ nontrivialZeros K ∧ b ≤ ρ.im ∧ ρ.im < b + 1}
  have hZfinite (b : ℝ) : (Z b).Finite := (zero_window_finite_count K b).1
  have hZbound (b : ℝ) (hb : |b| ≤ |a| + 1) :
      ((Z b).ncard : ℝ) ≤ Czero * (d + n * (2 + |a|)) := by
    have hlog : Real.log (2 + |b|) ≤ 2 + |a| := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |b|)
      linarith
    have hlogs := mul_le_mul_of_nonneg_left hlog hn
    calc
      _ ≤ dedekindZeroWindowCount K b := (zero_window_finite_count K b).2
      _ ≤ Czero * (d + n * Real.log (2 + |b|)) := (hcount K b).2
      _ ≤ Czero * (d + n * (2 + |a|)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCzero.le
  let U : Set ℂ := (Z (a - 1) ∪ Z a) ∪ Z (a + 1)
  have hUfinite : U.Finite := ((hZfinite (a - 1)).union (hZfinite a)).union (hZfinite (a + 1))
  let S : Finset ℝ := hUfinite.toFinset.image Complex.im
  have hScard : (S.card : ℝ) ≤
      ((Z (a - 1)).ncard : ℝ) + ((Z a).ncard : ℝ) + ((Z (a + 1)).ncard : ℝ) := by
    have hnat : S.card ≤ (Z (a - 1)).ncard + (Z a).ncard + (Z (a + 1)).ncard := by
      calc
        S.card ≤ hUfinite.toFinset.card := Finset.card_image_le
        _ = U.ncard := (Set.ncard_eq_toFinset_card U hUfinite).symm
        _ ≤ _ := by
          have houter := Set.ncard_union_le (Z (a - 1) ∪ Z a) (Z (a + 1))
          have hinner := Set.ncard_union_le (Z (a - 1)) (Z a)
          dsimp [U]
          omega
    exact_mod_cast hnat
  have hminus : |a - 1| ≤ |a| + 1 := by simpa using abs_sub_le a 0 1
  have hplus : |a + 1| ≤ |a| + 1 := by simpa using abs_sub_le a 0 (-1)
  have hmid : |a| ≤ |a| + 1 := by linarith
  have hthree : (S.card : ℝ) ≤ 3 * Czero * (d + n * (2 + |a|)) := by
    linarith [hScard, hZbound (a - 1) hminus, hZbound a hmid, hZbound (a + 1) hplus]
  have hweight : d + n * (2 + |a|) ≤ 2 * W * (1 + |a|) := by
    dsimp [W]
    nlinarith [mul_nonneg hd (abs_nonneg a), mul_nonneg hn (abs_nonneg a)]
  have hScardA : (S.card : ℝ) ≤ A * (1 + |a|) := by
    calc
      _ ≤ 3 * Czero * (d + n * (2 + |a|)) := hthree
      _ ≤ 3 * Czero * (2 * W * (1 + |a|)) :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = (6 * Czero * W) * (1 + |a|) := by ring
      _ ≤ A * (1 + |a|) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        dsimp [A]
        linarith
  have ha : 0 < 1 + |a| := by positivity
  have hden : 4 * ((S.card : ℝ) + 1) ≤ 4 * ((A + 1) * (1 + |a|)) := by
    nlinarith [hScardA, abs_nonneg a]
  have hsmall : c / (1 + |a|) ≤ 1 / (4 * ((S.card : ℝ) + 1)) := by
    have heq : c / (1 + |a|) = 1 / (4 * ((A + 1) * (1 + |a|))) := by
      dsimp [c]
      rw [div_div]
      congr 1 <;> ring
    rw [heq]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hcsmall : c / (1 + |a|) ≤ 1 := by
    apply (div_le_iff₀ ha).2
    linarith [hc₁, abs_nonneg a]
  obtain ⟨T, hT, hsep⟩ := finite_ordinates_gap S a
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  by_cases hu : ρ ∈ U
  · have him : ρ.im ∈ S := Finset.mem_image.mpr
      ⟨ρ, hUfinite.mem_toFinset.mpr hu, rfl⟩
    exact hsmall.trans (hsep ρ.im him)
  · have hout : ρ.im < a - 1 ∨ a + 2 ≤ ρ.im := by
      by_cases hlo : ρ.im < a - 1
      · exact Or.inl hlo
      · right
        by_contra hhi
        have hlow : a - 1 ≤ ρ.im := le_of_not_gt hlo
        have hhigh : ρ.im < a + 2 := lt_of_not_ge hhi
        apply hu
        change (ρ ∈ Z (a - 1) ∨ ρ ∈ Z a) ∨ ρ ∈ Z (a + 1)
        by_cases hfirst : ρ.im < a
        · exact Or.inl (Or.inl ⟨hρ, hlow, by linarith⟩)
        · by_cases hsecond : ρ.im < a + 1
          · exact Or.inl (Or.inr ⟨hρ, le_of_not_gt hfirst, hsecond⟩)
          · exact Or.inr ⟨hρ, le_of_not_gt hsecond, by linarith⟩
    have hdist : 1 ≤ |T - ρ.im| := by
      rcases hout with hlo | hhi
      · rw [abs_of_nonneg (by linarith [hT.1] : 0 ≤ T - ρ.im)]
        linarith [hT.1]
      · rw [abs_of_nonpos (by linarith [hT.2] : T - ρ.im ≤ 0)]
        linarith [hT.2]
    exact hcsmall.trans hdist

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
