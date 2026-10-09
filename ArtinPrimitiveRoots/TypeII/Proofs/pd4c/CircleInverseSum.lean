import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CircleShell

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A separated circle set has a reciprocal-distance sum bounded by a finite harmonic sum. -/
theorem circle_inverse_sum_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (d : ℕ) (B : ℝ)
    (hd : 2 ≤ d) (hB : 0 ≤ B)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      1/(2*(d:ℝ)) ≤ circleDistance (φ i-φ j)) :
    (∑ i ∈ T, if circleDistance (φ i)=0 then B
      else min B (1/circleDistance (φ i))) ≤
    B+16*(d:ℝ)*(∑ j ∈ Finset.Icc 1 (4*d), 1/(j:ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let δ := 1/(2*(d:ℝ))
  let step := δ/4
  let J := Finset.Icc 1 (4*d)
  let t (i : α) := circleDistance (φ i)
  let W (i : α) := if t i=0 then B else min B (1/t i)
  let near := T.filter fun i => t i ≤ step
  let shell (i : α) (j : ℕ) : ℝ :=
    if (j:ℝ)*step < t i ∧ t i ≤ (j:ℝ)*step+step then 8*(d:ℝ)/(j:ℝ) else 0
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hs : 0 < step := div_pos hδ (by norm_num)
  have hstep : step = 1/(8*(d:ℝ)) := by dsimp only [step, δ]; ring
  have hNstep : ((4*d:ℕ):ℝ)*step = 1/2 := by
    push_cast
    rw [hstep]
    field_simp [hdpos.ne'] <;> ring
  have ht (i : α) : t i ≤ 1/2 := by
    dsimp only [t]
    rw [pd4c_circleDistance_eq_round]
    exact abs_sub_round _
  have hW (i : α) : W i ≤ B := by
    dsimp only [W]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hshell0 (i : α) (j : ℕ) : 0 ≤ shell i j := by
    dsimp only [shell]
    split_ifs <;> positivity
  have hindex (i : α) (houtside : step < t i) :
      ∃ j ∈ J, (j:ℝ)*step < t i ∧ t i ≤ (j:ℝ)*step+step := by
    let x := t i/step
    let k := Nat.ceil x
    let j := k-1
    have hx1 : 1 < x := (lt_div_iff₀ hs).mpr (by simpa using houtside)
    have hx0 : 0 ≤ x := by linarith
    have hk2 : 2 ≤ k := by
      have hkR : (1:ℝ) < k := hx1.trans_le (Nat.le_ceil x)
      have hkN : (1:ℕ) < k := by exact_mod_cast hkR
      omega
    have hkupper : k ≤ 4*d := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hs).mpr
      exact (ht i).trans_eq hNstep.symm
    have hj : j ∈ J := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hjadd : (j:ℝ)+1 = (k:ℝ) := by
      have h : j+1=k := Nat.sub_add_cancel (by omega : 1 ≤ k)
      exact_mod_cast h
    have hklt : (k:ℝ) < x+1 := Nat.ceil_lt_add_one hx0
    have hjx : (j:ℝ) < x := by linarith only [hklt, hjadd]
    have hlo := (lt_div_iff₀ hs).mp hjx
    have hhi := (div_le_iff₀ hs).mp (show x ≤ (j:ℝ)+1 by rw [hjadd]; exact Nat.le_ceil x)
    refine ⟨j, hj, hlo, ?_⟩
    nlinarith only [hhi]
  have hpoint (i : α) : W i ≤ (if t i ≤ step then B else 0)+∑ j ∈ J, shell i j := by
    by_cases hnear : t i ≤ step
    · rw [if_pos hnear]
      exact (hW i).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => hshell0 i j))
    · rw [if_neg hnear, zero_add]
      have houtside : step < t i := lt_of_not_ge hnear
      obtain ⟨j, hj, hlo, hhi⟩ := hindex i houtside
      have hjpos : (0:ℝ) < j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) (Finset.mem_Icc.mp hj).1)
      have htpos : 0 < t i := hs.trans houtside
      have hrecip : 1/t i ≤ 8*(d:ℝ)/(j:ℝ) := by
        calc
          _ ≤ 1/((j:ℝ)*step) := one_div_le_one_div_of_le (mul_pos hjpos hs) hlo.le
          _ = _ := by rw [hstep]; field_simp [hjpos.ne', hdpos.ne'] <;> ring
      have hselected : shell i j = 8*(d:ℝ)/(j:ℝ) := if_pos ⟨hlo,hhi⟩
      have hsingle := Finset.single_le_sum (fun j hj => hshell0 i j) hj
      dsimp only [W]
      rw [if_neg htpos.ne']
      exact (min_le_right _ _).trans (hrecip.trans (hselected ▸ hsingle))
  have hnearR := circle_window_card_bound T φ δ step hδ hs.le hsep
  have hnearCoef : 2*step/δ+1 = (3/2:ℝ) := by
    dsimp only [step]
    field_simp [hδ.ne'] <;> ring
  rw [hnearCoef] at hnearR
  have hnearNat : near.card ≤ 1 := by
    by_contra hn
    have htwo : (2:ℝ) ≤ near.card := by exact_mod_cast (by omega : 2 ≤ near.card)
    change (near.card:ℝ) ≤ 3/2 at hnearR
    linarith only [hnearR, htwo]
  have hnearSum : (∑ i ∈ T, if t i ≤ step then B else 0) ≤ B := by
    have heq : (∑ i ∈ T, if t i ≤ step then B else 0) = (near.card:ℝ)*B := by
      rw [← Finset.sum_filter]
      simp only [near, Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (show (near.card:ℝ) ≤ 1 by exact_mod_cast hnearNat) hB).trans_eq (one_mul B)
  have hshellSum (j : ℕ) : (∑ i ∈ T, shell i j) ≤ 2*(8*(d:ℝ)/(j:ℝ)) := by
    let U := T.filter fun i => (j:ℝ)*step < t i ∧ t i ≤ (j:ℝ)*step+step
    have hc : U.card ≤ 2 := circle_shell_card_le_two T φ δ ((j:ℝ)*step) hδ hsep
    have heq : (∑ i ∈ T, shell i j) = (U.card:ℝ)*(8*(d:ℝ)/(j:ℝ)) := by
      dsimp only [shell]
      rw [← Finset.sum_filter]
      simp only [U, Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  have hsum : (∑ i ∈ T, ∑ j ∈ J, shell i j) ≤
      16*(d:ℝ)*(∑ j ∈ J, 1/(j:ℝ)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j ∈ J, 2*(8*(d:ℝ)/(j:ℝ)) := Finset.sum_le_sum (fun j hj => hshellSum j)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  change (∑ i ∈ T, W i) ≤ B+16*(d:ℝ)*(∑ j ∈ J, 1/(j:ℝ))
  calc
    _ ≤ ∑ i ∈ T, ((if t i ≤ step then B else 0)+(∑ j ∈ J, shell i j)) :=
      Finset.sum_le_sum (fun i hi => hpoint i)
    _ = (∑ i ∈ T, if t i ≤ step then B else 0)+(∑ i ∈ T, ∑ j ∈ J, shell i j) :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add hnearSum hsum

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
