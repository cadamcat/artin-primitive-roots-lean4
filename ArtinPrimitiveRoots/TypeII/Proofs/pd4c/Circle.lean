import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The infimum definition agrees with the nearest-integer distance. -/
theorem pd4c_circleDistance_eq_round (x : ℝ) :
    circleDistance x = |x - (round x : ℤ)| := by
  unfold circleDistance
  have hb : BddBelow (Set.range fun z : ℤ => |x - (z : ℝ)|) := by
    refine ⟨0, ?_⟩
    rintro y ⟨z, rfl⟩
    exact abs_nonneg _
  apply le_antisymm
  · exact csInf_le hb ⟨round x, rfl⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨z, rfl⟩
    exact round_le x z

theorem pd4c_circleDistance_le_abs_sub_int (x : ℝ) (k : ℤ) :
    circleDistance x ≤ |x - (k : ℝ)| := by
  rw [pd4c_circleDistance_eq_round]
  exact round_le x k

theorem pd4c_circleDistance_nonneg (x : ℝ) : 0 ≤ circleDistance x := by
  rw [pd4c_circleDistance_eq_round]
  exact abs_nonneg _

theorem pd4c_circleDistance_add_le (x y : ℝ) :
    circleDistance (x + y) ≤ circleDistance x + circleDistance y := by
  calc
    _ ≤ |x + y - ((round x + round y : ℤ) : ℝ)| :=
      pd4c_circleDistance_le_abs_sub_int _ _
    _ = |(x - (round x : ℤ)) + (y - (round y : ℤ))| := by push_cast; congr 1; ring
    _ ≤ |x - (round x : ℤ)| + |y - (round y : ℤ)| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (x - (round x : ℤ)) (y - (round y : ℤ))
    _ = _ := by rw [pd4c_circleDistance_eq_round, pd4c_circleDistance_eq_round]

theorem pd4c_circleDistance_neg (x : ℝ) : circleDistance (-x) = circleDistance x := by
  have hle (y : ℝ) : circleDistance (-y) ≤ circleDistance y := by
    calc
      _ ≤ |-y - ((-round y : ℤ) : ℝ)| := pd4c_circleDistance_le_abs_sub_int _ _
      _ = |-(y - (round y : ℤ))| := by push_cast; congr 1; ring
      _ = |y - (round y : ℤ)| := abs_neg _
      _ = _ := (pd4c_circleDistance_eq_round _).symm
  exact le_antisymm (hle x) (by simpa using hle (-x))

theorem pd4c_circleDistance_sub_le (x y : ℝ) :
    circleDistance (x - y) ≤ circleDistance x + circleDistance y := by
  simpa only [sub_eq_add_neg, pd4c_circleDistance_neg] using pd4c_circleDistance_add_le x (-y)

theorem pd4c_circleDistance_lipschitz (x y : ℝ) :
    circleDistance x ≤ circleDistance y + |x - y| := by
  calc
    _ = circleDistance ((x - y) + y) := by congr 1; ring
    _ ≤ circleDistance (x - y) + circleDistance y := pd4c_circleDistance_add_le _ _
    _ ≤ |x - y| + circleDistance y := by
      exact add_le_add (by simpa using pd4c_circleDistance_le_abs_sub_int (x - y) 0) le_rfl
    _ = _ := add_comm _ _

/-- A phase-separated trial set meets a short circle window in at most one numeric value. -/
theorem pd4c_good_trial_window_unique {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (r center radius sep : ℝ)
    (hsep : ∀ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ →
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ → n₁ ≠ n₂ →
        sep < circleDistance (((n₁ : ℝ) - n₂) * r))
    (hwindow : 2 * radius ≤ sep) (n₁ n₂ : ℕ)
    (h₁ : IsGoodnessTrialValue a p d₀ I iStar fresh n₁)
    (h₂ : IsGoodnessTrialValue a p d₀ I iStar fresh n₂)
    (hw₁ : circleDistance ((n₁ : ℝ) * r - center) ≤ radius)
    (hw₂ : circleDistance ((n₂ : ℝ) * r - center) ≤ radius) : n₁ = n₂ := by
  by_contra hne
  have hlower := hsep n₁ n₂ h₁ h₂ hne
  have hupper : circleDistance (((n₁ : ℝ) - n₂) * r) ≤ 2 * radius := by
    calc
      _ = circleDistance (((n₁ : ℝ) * r - center) - ((n₂ : ℝ) * r - center)) := by
        congr 1
        ring
      _ ≤ circleDistance ((n₁ : ℝ) * r - center) +
          circleDistance ((n₂ : ℝ) * r - center) := pd4c_circleDistance_sub_le _ _
      _ ≤ radius + radius := add_le_add hw₁ hw₂
      _ = _ := by ring
  exact (not_lt_of_ge (le_trans hupper hwindow)) hlower

end

end ArtinPrimitiveRoots.TypeII.PD
