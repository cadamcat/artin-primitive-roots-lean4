import ArtinPrimitiveRoots.Target

/-!
# Non-vacuity checks for the infinitude form of Artin's primitive root conjecture

This file provides machine-checked evidence that the main theorem
`ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite` is not vacuous:
its hypotheses are satisfiable, its definitions take the intended values on
small inputs, it implies the plain mathematical reading, and its hypotheses
are needed (the excluded cases are finite).
-/

namespace ArtinPrimitiveRootsConjecture
namespace NonVacuity

/-- The integer 2 satisfies both hypotheses of the main theorem. -/
theorem nonvac_admissible_2 : (2 : ℤ) ≠ -1 ∧ ¬ IsSquare (2 : ℤ) := by
  constructor
  · norm_num
  · norm_num

/-- The integer 3 satisfies both hypotheses of the main theorem. -/
theorem nonvac_admissible_3 : (3 : ℤ) ≠ -1 ∧ ¬ IsSquare (3 : ℤ) := by
  constructor
  · norm_num
  · norm_num

/-- The integer -2 satisfies both hypotheses of the main theorem. -/
theorem nonvac_admissible_neg2 : (-2 : ℤ) ≠ -1 ∧ ¬ IsSquare (-2 : ℤ) := by
  constructor
  · norm_num
  · norm_num

/-- Applying the main theorem at a = 2 gives infinitude of S 2. -/
theorem nonvac_S2_infinite : (S (2 : ℤ)).Infinite := by
  obtain ⟨h1, h2⟩ := nonvac_admissible_2
  exact artin_primitive_roots_infinite 2 h1 h2

/-- Applying the main theorem at a = 3 gives infinitude of S 3. -/
theorem nonvac_S3_infinite : (S (3 : ℤ)).Infinite := by
  obtain ⟨h1, h2⟩ := nonvac_admissible_3
  exact artin_primitive_roots_infinite 3 h1 h2

/-- Applying the main theorem at a = -2 gives infinitude of S (-2). -/
theorem nonvac_Sneg2_infinite : (S (-2 : ℤ)).Infinite := by
  obtain ⟨h1, h2⟩ := nonvac_admissible_neg2
  exact artin_primitive_roots_infinite (-2) h1 h2

/-- The order of 2 in ZMod 5 is 4, as intended. -/
theorem nonvac_order_2_mod5 : orderOf (((2 : ℤ)) : ZMod 5) = 4 := by
  have hcast : (((2 : ℤ)) : ZMod 5) = (2 : ZMod 5) := by simp
  have h4 : (2 : ZMod 5) ^ 4 = 1 := by decide
  have h1 : (2 : ZMod 5) ^ 1 ≠ 1 := by decide
  have h2 : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
  have h3 : (2 : ZMod 5) ^ 3 ≠ 1 := by decide
  have hord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (n := 4) (by norm_num)]
    refine ⟨h4, fun m hm1 hm2 => ?_⟩
    interval_cases m
    · exact h1
    · exact h2
    · exact h3
  rw [hcast]
  exact hord

/-- 5 is in S 2: 2 is a primitive root modulo 5. -/
theorem nonvac_mem_5_S2 : 5 ∈ S (2 : ℤ) := by
  refine ⟨by norm_num, ?_⟩
  have h41 : (5 - 1 : ℕ) = 4 := by norm_num
  rw [h41]
  exact nonvac_order_2_mod5

/-- The order of 2 in ZMod 3 is 2, as intended. -/
theorem nonvac_order_2_mod3 : orderOf (((2 : ℤ)) : ZMod 3) = 2 := by
  have hcast : (((2 : ℤ)) : ZMod 3) = (2 : ZMod 3) := by simp
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h1 : (2 : ZMod 3) ^ 1 ≠ 1 := by decide
  have hord : orderOf (2 : ZMod 3) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨h2, fun m hm1 hm2 => ?_⟩
    interval_cases m
    · exact h1
  rw [hcast]
  exact hord

/-- 3 is in S 2: 2 is a primitive root modulo 3. -/
theorem nonvac_mem_3_S2 : 3 ∈ S (2 : ℤ) := by
  refine ⟨by norm_num, ?_⟩
  have h31 : (3 - 1 : ℕ) = 2 := by norm_num
  rw [h31]
  exact nonvac_order_2_mod3

/-- The order of 2 in ZMod 7 is 3, not 6. -/
theorem nonvac_order_2_mod7 : orderOf (((2 : ℤ)) : ZMod 7) = 3 := by
  have hcast : (((2 : ℤ)) : ZMod 7) = (2 : ZMod 7) := by simp
  have h3 : (2 : ZMod 7) ^ 3 = 1 := by decide
  have h1 : (2 : ZMod 7) ^ 1 ≠ 1 := by decide
  have h2 : (2 : ZMod 7) ^ 2 ≠ 1 := by decide
  have hord : orderOf (2 : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨h3, fun m hm1 hm2 => ?_⟩
    interval_cases m
    · exact h1
    · exact h2
  rw [hcast]
  exact hord

/-- 7 is not in S 2: 2 is not a primitive root modulo 7. -/
theorem nonvac_mem_7_not_S2 : 7 ∉ S (2 : ℤ) := by
  intro hmem
  have hord : orderOf (((2 : ℤ)) : ZMod 7) = 7 - 1 := hmem.2
  have h71 : (7 - 1 : ℕ) = 6 := by norm_num
  rw [h71, nonvac_order_2_mod7] at hord
  norm_num at hord

/-- 2 is not in S 2: an even base vanishes mod 2 (p = 2 case). -/
theorem nonvac_mem_2_not_S2 : 2 ∉ S (2 : ℤ) := by
  intro hmem
  have hord : orderOf (((2 : ℤ)) : ZMod 2) = 2 - 1 := hmem.2
  have hcast : (((2 : ℤ)) : ZMod 2) = 0 := by decide
  have h21 : (2 - 1 : ℕ) = 1 := by norm_num
  rw [h21, hcast, orderOf_zero (ZMod 2)] at hord
  norm_num at hord

/-- 2 is in S 3: an odd base is 1 mod 2 (p = 2 case). -/
theorem nonvac_mem_2_S3 : 2 ∈ S (3 : ℤ) := by
  refine ⟨by norm_num, ?_⟩
  have h21 : (2 - 1 : ℕ) = 1 := by norm_num
  rw [h21]
  have hcast : (((3 : ℤ)) : ZMod 2) = 1 := by decide
  rw [hcast, orderOf_one]

/-- Primes dividing the base are never in S (zero has order 0). -/
theorem nonvac_dvd_not_mem (a : ℤ) (p : ℕ) (hp : p.Prime) (hdvd : (p : ℤ) ∣ a) :
    p ∉ S a := by
  intro hmem
  have hfact1 : Fact p.Prime := ⟨hp⟩
  have hfact2 : Fact (1 < p) := ⟨hp.one_lt⟩
  have hzero : ((a : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hdvd
  have hord : orderOf ((a : ℤ) : ZMod p) = p - 1 := hmem.2
  rw [hzero, orderOf_zero (ZMod p)] at hord
  have h2le := hp.two_le
  omega

/-- The natural-number subtractions `p - 1` used in `S` take their true values at small primes. -/
theorem nonvac_nat_sub_pred :
    (5 - 1 : ℕ) = 4 ∧ (7 - 1 : ℕ) = 6 ∧ (3 - 1 : ℕ) = 2 ∧ (2 - 1 : ℕ) = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Every member p of S a satisfies 2 ≤ p and p - 1 ≠ 0. -/
theorem nonvac_S_mem_two_le (a : ℤ) (p : ℕ) (hmem : p ∈ S a) :
    2 ≤ p ∧ (p - 1 : ℕ) ≠ 0 ∧ 0 < p - 1 := by
  have hp := hmem.1
  have h2le := hp.two_le
  refine ⟨h2le, by omega, by omega⟩

/-- S 2 is nontrivial: nonempty and not everything. -/
theorem nonvac_S2_proper : (S (2 : ℤ)).Nonempty ∧ S (2 : ℤ) ≠ Set.univ := by
  constructor
  · exact ⟨5, nonvac_mem_5_S2⟩
  · intro huniv
    have h7 : (7 : ℕ) ∈ S (2 : ℤ) := by rw [huniv]; exact Set.mem_univ 7
    exact nonvac_mem_7_not_S2 h7

/-- Membership in S a is the same as Mathlib's IsPrimitiveRoot. -/
theorem nonvac_isPrimRoot_of_mem (a : ℤ) (p : ℕ) (hmem : p ∈ S a) :
    IsPrimitiveRoot ((a : ℤ) : ZMod p) (p - 1) := by
  exact IsPrimitiveRoot.iff_orderOf.mpr hmem.2

/-- The IsPrimitiveRoot form of the theorem: infinitely many such primes. -/
theorem nonvac_isPrimRoot_infinite (a : ℤ) (ha : a ≠ -1) (hns : ¬ IsSquare a) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRoot ((a : ℤ) : ZMod p) (p - 1)}.Infinite := by
  have hinf := artin_primitive_roots_infinite a ha hns
  have hset : S a = {p : ℕ | p.Prime ∧ IsPrimitiveRoot ((a : ℤ) : ZMod p) (p - 1)} := by
    ext p
    show (p.Prime ∧ orderOf ((a : ℤ) : ZMod p) = (p - 1 : ℕ)) ↔
      (p.Prime ∧ IsPrimitiveRoot ((a : ℤ) : ZMod p) (p - 1))
    exact and_congr Iff.rfl IsPrimitiveRoot.iff_orderOf.symm
  rw [← hset]
  exact hinf

/-- The unbounded form: for every N there is such a prime above N. -/
theorem nonvac_isPrimRoot_unbounded (a : ℤ) (ha : a ≠ -1) (hns : ¬ IsSquare a)
    (N : ℕ) : ∃ p, N < p ∧ p.Prime ∧ IsPrimitiveRoot ((a : ℤ) : ZMod p) (p - 1) := by
  have hinf := nonvac_isPrimRoot_infinite a ha hns
  obtain ⟨p, hpmem, hpnot⟩ := hinf.exists_notMem_finite (Set.finite_Iic N)
  have hNlt : N < p := by simpa only [Set.mem_Iic, not_le] using hpnot
  exact ⟨p, hNlt, hpmem.1, hpmem.2⟩

/-- The units-generator form: the unit above a is primitive, unbounded. -/
theorem nonvac_units_isPrimRoot_unbounded (a : ℤ) (ha : a ≠ -1) (hns : ¬ IsSquare a)
    (N : ℕ) : ∃ p, N < p ∧ ∃ (_ : p.Prime) (u : (ZMod p)ˣ),
      IsPrimitiveRoot u (p - 1) ∧ ((u : ZMod p) = ((a : ℤ) : ZMod p)) := by
  obtain ⟨p, hNp, hpprime, hprim⟩ := nonvac_isPrimRoot_unbounded a ha hns N
  have h2le := hpprime.two_le
  have hne : (p - 1 : ℕ) ≠ 0 := by omega
  have hunit : IsUnit (((a : ℤ)) : ZMod p) := hprim.isUnit hne
  refine ⟨p, hNp, hpprime, hunit.unit, ?_, hunit.unit_spec⟩
  have hspec : ((hunit.unit : (ZMod p)ˣ) : ZMod p) = (((a : ℤ)) : ZMod p) :=
    hunit.unit_spec
  have hprim' : IsPrimitiveRoot ((hunit.unit : (ZMod p)ˣ) : ZMod p) (p - 1) := by
    rw [hspec]
    exact hprim
  exact IsPrimitiveRoot.coe_units_iff.mp hprim'

/-- S (-1) is contained in {2, 3}: (-1)^2 = 1 forces p - 1 ∣ 2. -/
theorem nonvac_S_neg1_subset : S (-1 : ℤ) ⊆ {2, 3} := by
  intro p hmem
  have hp : p.Prime := hmem.1
  have hord : orderOf (((-1 : ℤ)) : ZMod p) = p - 1 := hmem.2
  have hcast : (((-1 : ℤ)) : ZMod p) = (-1 : ZMod p) := by simp
  have hsq : (((-1 : ℤ)) : ZMod p) ^ 2 = 1 := by
    rw [hcast]
    simp
  have hdvd : orderOf (((-1 : ℤ)) : ZMod p) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  rw [hord] at hdvd
  have h2le := hp.two_le
  have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h_eq : p = 2 ∨ p = 3 := by omega
  rcases h_eq with rfl | rfl
  · simp
  · simp

/-- S (-1) is finite: the first excluded hypothesis is needed. -/
theorem nonvac_S_neg1_finite : (S (-1 : ℤ)).Finite := by
  exact ((Set.finite_singleton 3).insert 2).subset nonvac_S_neg1_subset

/-- S (-1) takes the intended values: 2 and 3 in, 5 out. -/
theorem nonvac_Sneg1_values :
    2 ∈ S (-1 : ℤ) ∧ 3 ∈ S (-1 : ℤ) ∧ 5 ∉ S (-1 : ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    have h21 : (2 - 1 : ℕ) = 1 := by norm_num
    rw [h21]
    have hcast : (((-1 : ℤ)) : ZMod 2) = 1 := by decide
    rw [hcast, orderOf_one]
  · refine ⟨by norm_num, ?_⟩
    have h31 : (3 - 1 : ℕ) = 2 := by norm_num
    rw [h31]
    have hcast : (((-1 : ℤ)) : ZMod 3) = (-1 : ZMod 3) := by simp
    have h2 : (-1 : ZMod 3) ^ 2 = 1 := by simp
    have h1 : (-1 : ZMod 3) ^ 1 ≠ 1 := by decide
    have hord : orderOf (-1 : ZMod 3) = 2 := by
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨h2, fun m hm1 hm2 => ?_⟩
      interval_cases m
      · exact h1
    rw [hcast]
    exact hord
  · intro hmem
    have hord : orderOf (((-1 : ℤ)) : ZMod 5) = 5 - 1 := hmem.2
    have hcast : (((-1 : ℤ)) : ZMod 5) = (-1 : ZMod 5) := by simp
    have hsq : (((-1 : ℤ)) : ZMod 5) ^ 2 = 1 := by
      rw [hcast]
      simp
    have hdvd : orderOf (((-1 : ℤ)) : ZMod 5) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    have h51 : (5 - 1 : ℕ) = 4 := by norm_num
    rw [h51] at hord
    rw [hord] at hdvd
    norm_num at hdvd

/-- Every S (b^2) is contained in {2}: by Fermat, a square has order dividing (p - 1) / 2 for odd p. -/
theorem nonvac_S_sq_subset_two (b : ℤ) : S (b ^ 2) ⊆ {2} := by
  intro p hmem
  have hp : p.Prime := hmem.1
  have hord : orderOf (((b ^ 2 : ℤ)) : ZMod p) = p - 1 := hmem.2
  by_cases heq : p = 2
  · simp [heq]
  · exfalso
    have h2le := hp.two_le
    have h2lt : 2 < p := by omega
    have hfact : Fact p.Prime := ⟨hp⟩
    have h1lt : Fact (1 < p) := ⟨hp.one_lt⟩
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two heq
    have hkpos : 0 < k := by omega
    have hpred : p - 1 = 2 * k := by omega
    have hxeq : (((b ^ 2 : ℤ)) : ZMod p) = ((((b : ℤ)) : ZMod p)) ^ 2 := by
      push_cast
      ring
    by_cases hy0 : ((((b : ℤ)) : ZMod p)) = 0
    · have hx0 : (((b ^ 2 : ℤ)) : ZMod p) = 0 := by
        rw [hxeq, hy0]
        simp
      rw [hx0, orderOf_zero (ZMod p)] at hord
      omega
    · have hF : ((((b : ℤ)) : ZMod p)) ^ (p - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one hy0
      have hxk : (((b ^ 2 : ℤ)) : ZMod p) ^ k = 1 := by
        rw [hxeq, ← pow_mul]
        have h2k : 2 * k = p - 1 := by omega
        rw [h2k]
        exact hF
      have hdvd : orderOf (((b ^ 2 : ℤ)) : ZMod p) ∣ k :=
        orderOf_dvd_of_pow_eq_one hxk
      rw [hord] at hdvd
      have hle : p - 1 ≤ k := Nat.le_of_dvd hkpos hdvd
      omega

/-- Every S (b^2) is finite: the squareness hypothesis is needed. -/
theorem nonvac_S_sq_finite (b : ℤ) : (S (b ^ 2)).Finite := by
  exact (Set.finite_singleton 2).subset (nonvac_S_sq_subset_two b)

#print axioms nonvac_admissible_2
#print axioms nonvac_admissible_3
#print axioms nonvac_admissible_neg2
#print axioms nonvac_S2_infinite
#print axioms nonvac_S3_infinite
#print axioms nonvac_Sneg2_infinite
#print axioms nonvac_order_2_mod5
#print axioms nonvac_mem_5_S2
#print axioms nonvac_order_2_mod3
#print axioms nonvac_mem_3_S2
#print axioms nonvac_order_2_mod7
#print axioms nonvac_mem_7_not_S2
#print axioms nonvac_mem_2_not_S2
#print axioms nonvac_mem_2_S3
#print axioms nonvac_dvd_not_mem
#print axioms nonvac_nat_sub_pred
#print axioms nonvac_S_mem_two_le
#print axioms nonvac_S2_proper
#print axioms nonvac_isPrimRoot_of_mem
#print axioms nonvac_isPrimRoot_infinite
#print axioms nonvac_isPrimRoot_unbounded
#print axioms nonvac_units_isPrimRoot_unbounded
#print axioms nonvac_S_neg1_subset
#print axioms nonvac_S_neg1_finite
#print axioms nonvac_Sneg1_values
#print axioms nonvac_S_sq_subset_two
#print axioms nonvac_S_sq_finite

end NonVacuity
end ArtinPrimitiveRootsConjecture
