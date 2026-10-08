import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootEulerArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArithmeticFunction
set_option maxHeartbeats 1000000

lemma pd1c_mobius_divisor_product (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d) =
      ∏ p ∈ n.primeFactors, (1 - f p) := by
  let g := ((ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul f) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  let e := ArithmeticFunction.prodPrimeFactors (fun p => 1 - f p)
  have hg : g.IsMultiplicative := (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul hf).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have he : e.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hPrimePow : ∀ p i : ℕ, p.Prime → g (p ^ i) = e (p ^ i) := by
    intro p i hp
    by_cases hi : i = 0
    · subst i
      simp only [pow_zero, hg.map_one, he.map_one]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hTail : (∑ k ∈ Finset.range j,
          (ArithmeticFunction.moebius (p ^ (k + 2)) : ℝ) * f (p ^ (k + 2))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega), Int.cast_zero, zero_mul]
      have hsum : (∑ k ∈ Finset.range (j + 2),
          (ArithmeticFunction.moebius (p ^ k) : ℝ) * f (p ^ k)) = 1 - f p := by
        rw [show j + 2 = (j + 1) + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [Nat.zero_add, pow_zero, pow_one, ArithmeticFunction.isMultiplicative_moebius.map_one, Int.cast_one,
          hf.map_one, one_mul, ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, neg_mul, Int.cast_one]
        have hshift : (∑ k ∈ Finset.range j,
            (ArithmeticFunction.moebius (p ^ (k + 1 + 1)) : ℝ) * f (p ^ (k + 1 + 1))) = 0 := by
          simpa only [Nat.add_assoc] using hTail
        rw [hshift]
        ring
      have hG : g (p ^ (j + 1)) = ∑ k ∈ Finset.range (j + 2),
          (ArithmeticFunction.moebius (p ^ k) : ℝ) * f (p ^ k) := by
        change (((ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul f) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ (j + 1)) = _
        rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
        simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply]
      have hE : e (p ^ (j + 1)) = 1 - f p := by
        simp only [e, ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
          Nat.primeFactors_prime_pow (by omega : j + 1 ≠ 0) hp, Finset.prod_singleton]
      exact hG.trans (hsum.trans hE.symm)
  have hge : g = e := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers g hg e he).mpr hPrimePow
  have h := congrArg (fun k : ArithmeticFunction ℝ => k n) hge
  simpa only [g, e, ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.prodPrimeFactors_apply hn.ne'] using h

noncomputable def pd1c_coprimeReciprocal (S : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n S then (n : ℝ)⁻¹ else 0, by split_ifs <;> simp⟩

lemma pd1c_coprimeReciprocal_multiplicative (S : ℕ) : (pd1c_coprimeReciprocal S).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [pd1c_coprimeReciprocal], ?_⟩
  intro m n hm hn hcop
  have hcnm : Nat.Coprime (m * n) S ↔ Nat.Coprime m S ∧ Nat.Coprime n S := by
    constructor
    · intro h
      exact ⟨h.of_dvd_left (dvd_mul_right m n), h.of_dvd_left (dvd_mul_left n m)⟩
    · rintro ⟨hm, hn⟩
      exact hm.mul_left hn
  change (if Nat.Coprime (m * n) S then ((m * n : ℕ) : ℝ)⁻¹ else 0) =
    (if Nat.Coprime m S then (m : ℝ)⁻¹ else 0) * (if Nat.Coprime n S then (n : ℝ)⁻¹ else 0)
  simp only [hcnm, Nat.cast_mul, mul_inv_rev]
  by_cases hcM : Nat.Coprime m S <;> by_cases hcN : Nat.Coprime n S <;>
    simp [Nat.Coprime, hcM, hcN, mul_comm]

lemma pd1c_root_euler_divisor_expansion (u S : ℕ) (hu : 0 < u) :
    (∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ))) =
      ∑ d ∈ u.divisors, if Nat.Coprime d S then (ArithmeticFunction.moebius d : ℝ) / d else 0 := by
  have heq := pd1c_mobius_divisor_product (pd1c_coprimeReciprocal S) (pd1c_coprimeReciprocal_multiplicative S) u hu
  have hprod : (∏ p ∈ u.primeFactors, (1 - pd1c_coprimeReciprocal S p)) =
      ∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ)) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    change (1 - if Nat.Coprime p S then (p : ℝ)⁻¹ else 0) =
      if ¬p ∣ S then 1 - 1 / (p : ℝ) else 1
    simp only [hpp.coprime_iff_not_dvd]
    by_cases hd : p ∣ S <;> simp [hd, one_div]
  rw [hprod] at heq
  rw [← heq]
  symm
  apply Finset.sum_congr rfl
  intro d hd
  change (if Nat.Coprime d S then (ArithmeticFunction.moebius d : ℝ) / d else 0) =
    (ArithmeticFunction.moebius d : ℝ) * (if Nat.Coprime d S then (d : ℝ)⁻¹ else 0)
  by_cases hc : Nat.Coprime d S <;> simp [Nat.Coprime, hc, div_eq_mul_inv]

end ArtinPrimitiveRoots.TypeII.PD
