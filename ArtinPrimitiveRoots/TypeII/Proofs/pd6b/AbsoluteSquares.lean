import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TupleCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Count factor pairs through their first positive divisor. -/
theorem factorPair_card_le_tau (M N : Finset ℕ) (k : ℕ) (hk : 0 < k) :
    ((M ×ˢ N).filter fun mn => mn.1 * mn.2 = k).card ≤ tau k := by
  let T := (M ×ˢ N).filter fun mn => mn.1 * mn.2 = k
  have hmap : Set.MapsTo Prod.fst (T : Set (ℕ × ℕ)) (k.divisors : Set ℕ) := by
    intro mn hmn
    have heq := (Finset.mem_filter.mp hmn).2
    exact Nat.mem_divisors.mpr ⟨⟨mn.2, heq.symm⟩, hk.ne'⟩
  have hinj : (T : Set (ℕ × ℕ)).InjOn Prod.fst := by
    intro mn hmn rs hrs hfirst
    have heq := (Finset.mem_filter.mp hmn).2
    have heq' := (Finset.mem_filter.mp hrs).2
    have hpos : 0 < mn.1 := by
      by_contra h
      have hzero : mn.1 = 0 := by omega
      simp [hzero] at heq
      omega
    have hsecond : mn.2 = rs.2 := by
      have hmul : mn.1 * mn.2 = mn.1 * rs.2 := by
        rw [heq, hfirst, heq']
      exact Nat.eq_of_mul_eq_mul_left hpos hmul
    exact Prod.ext hfirst hsecond
  have hdivisors : k.divisors = (Finset.range (k + 1)).filter (fun d => d ∣ k) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · intro hd
      exact ⟨Nat.le_of_dvd hk hd.1, hd.1⟩
    · intro hd
      exact ⟨hd.2, hk.ne'⟩
  simpa only [T, tau, hdivisors] using
    (Finset.card_le_card_of_injOn Prod.fst hmap hinj)

/-- A bounded-degree relation costs only a divisor second moment. -/
theorem boundedDegree_square_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (R : ι → κ → Prop) (u : ι → ℝ) (v : κ → ℝ)
    (D : ℝ)
    (hrow : ∀ i ∈ I, ((J.filter (R i)).card : ℝ) ≤ D)
    (hcol : ∀ j ∈ J, ((I.filter fun i => R i j).card : ℝ) ≤ D) :
    (∑ i ∈ I, ∑ j ∈ J, if R i j then u i * v j else 0) ≤
      D / 2 * ((∑ i ∈ I, u i ^ 2) + ∑ j ∈ J, v j ^ 2) := by
  have hrowSum (i : ι) :
      (∑ j ∈ J, if R i j then u i ^ 2 else 0) =
        ((J.filter (R i)).card : ℝ) * u i ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  have hcolSum (j : κ) :
      (∑ i ∈ I, if R i j then v j ^ 2 else 0) =
        ((I.filter fun i => R i j).card : ℝ) * v j ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  have htwice :
      2 * (∑ i ∈ I, ∑ j ∈ J, if R i j then u i * v j else 0) ≤
        (∑ i ∈ I, ∑ j ∈ J, if R i j then u i ^ 2 else 0) +
          (∑ i ∈ I, ∑ j ∈ J, if R i j then v j ^ 2 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · nlinarith [sq_nonneg (u i - v j)]
    · simp
  have hrows :
      (∑ i ∈ I, ∑ j ∈ J, if R i j then u i ^ 2 else 0) ≤
        D * ∑ i ∈ I, u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hrowSum]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
  have hcols :
      (∑ i ∈ I, ∑ j ∈ J, if R i j then v j ^ 2 else 0) ≤
        D * ∑ j ∈ J, v j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [hcolSum]
    exact mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
  nlinarith

/-- Two individual square bounds control the mixed progression sum. -/
theorem sum_mul_le_of_square_bounds {ι : Type*} (I : Finset ι) (u v : ι → ℝ)
    (D : ℝ) (hu : (∑ i ∈ I, u i ^ 2) ≤ D) (hv : (∑ i ∈ I, v i ^ 2) ≤ D) :
    (∑ i ∈ I, u i * v i) ≤ D := by
  have htwice : 2 * (∑ i ∈ I, u i * v i) ≤
      (∑ i ∈ I, u i ^ 2) + ∑ i ∈ I, v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i hi => by nlinarith [sq_nonneg (u i - v i)])
  linarith

end
end ArtinPrimitiveRoots.TypeII.PD
