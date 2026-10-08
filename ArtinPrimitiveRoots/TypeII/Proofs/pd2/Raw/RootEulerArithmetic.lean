import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_totient_real_product (n : ℕ) :
    (Nat.totient n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv, one_div] using h

lemma pd2a_prime_euler_factor_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  apply sub_pos.mpr
  apply (div_lt_one (by linarith : 0 < (p : ℝ))).mpr
  linarith

lemma pd2a_rootShared_primeFactors (u S : ℕ) (hu : 0 < u) (hS : 0 < S) :
    (pd2a_rootShared u S).primeFactors = u.primeFactors.filter (fun p => p ∣ S) := by
  unfold pd2a_rootShared
  rw [Nat.primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)]
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, hu.ne', hS.ne', not_false_eq_true, and_true]
  constructor
  · rintro ⟨⟨hpp, hpS, hS0⟩, hpu⟩
    exact ⟨⟨hpp, hpu, hu.ne'⟩, hpS⟩
  · rintro ⟨⟨hpp, hpu, hu0⟩, hpS⟩
    exact ⟨⟨hpp, hpS, hS.ne'⟩, hpu⟩

lemma pd2a_root_euler_totient_ratio (u S : ℕ) (hu : 0 < u) (hS : 0 < S) :
    (Nat.totient (u * pd2a_rootShared u S) : ℝ) / Nat.totient (pd2a_rootShared u S) =
      (u : ℝ) * ∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ)) := by
  let D := pd2a_rootShared u S
  have hD : 0 < D := pd2a_rootShared_pos u S
  have hφD : 0 < (Nat.totient D : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hD
  have hpartition : (∏ p ∈ u.primeFactors, (1 - 1 / (p : ℝ))) =
      (∏ p ∈ u.primeFactors.filter (fun p => p ∣ S), (1 - 1 / (p : ℝ))) *
        (∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ))) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  apply (div_eq_iff hφD.ne').mpr
  rw [pd2a_root_totientShared_mul, Nat.cast_mul, pd2a_totient_real_product u,
    pd2a_totient_real_product D, pd2a_rootShared_primeFactors u S hu hS, hpartition]
  ring

end ArtinPrimitiveRoots.TypeII.PD
