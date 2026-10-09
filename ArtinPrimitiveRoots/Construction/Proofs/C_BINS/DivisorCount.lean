import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical

/-- Distinct prime divisors above a fixed power have bounded multiplicity on the support. -/
theorem large_prime_divisor_count (x b : ℝ) (d : ℕ) (P : Finset ℕ)
    (hx : 2 ≤ x) (hb : 0 < b) (hdpos : 0 < d) (hd : (d : ℝ) < 2 * x)
    (hP : ∀ p ∈ P, p.Prime ∧ p ∣ d ∧ Real.rpow x b < (p : ℝ)) :
    (P.card : ℝ) ≤ 2 / b := by
  classical
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsubset : P ⊆ d.primeFactors := by
    intro p hp
    exact (hP p hp).1.mem_primeFactors (hP p hp).2.1 (ne_of_gt hdpos)
  have hprodDvd : (∏ p ∈ P, p) ∣ d :=
    (Finset.prod_dvd_prod_of_subset P d.primeFactors (fun p : ℕ => p) hsubset).trans
      (Nat.prod_primeFactors_dvd d)
  have hprodPos : 0 < (∏ p ∈ P, p) :=
    Finset.prod_pos (fun p hp => (hP p hp).1.pos)
  have hprodRealPos : 0 < ((∏ p ∈ P, p : ℕ) : ℝ) := by exact_mod_cast hprodPos
  have hprodLe : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hdpos hprodDvd
  have hcastProd : ((∏ p ∈ P, p : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) := by simp
  have hNonzero : ∀ p ∈ P, (p : ℝ) ≠ 0 := by
    intro p hp
    apply ne_of_gt
    exact_mod_cast (hP p hp).1.pos
  have hSumLog : (∑ p ∈ P, Real.log (p : ℝ)) =
      Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by
    rw [hcastProd]
    exact (Real.log_prod hNonzero).symm
  have hLower (p : ℕ) (hp : p ∈ P) : b * Real.log x < Real.log (p : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos b) (hP p hp).2.2
    rw [Real.rpow_def_of_pos hxpos b, Real.log_exp] at h
    simpa only [mul_comm] using h
  have hCardLog : (P.card : ℝ) * (b * Real.log x) ≤ Real.log (d : ℝ) := by
    calc
      (P.card : ℝ) * (b * Real.log x) = ∑ p ∈ P, b * Real.log x := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ P, Real.log (p : ℝ) :=
        Finset.sum_le_sum (fun p hp => (hLower p hp).le)
      _ = Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := hSumLog
      _ ≤ Real.log (d : ℝ) := Real.log_le_log hprodRealPos hprodLe
  have hdRealPos : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hLogTwo : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hDlog : Real.log (d : ℝ) ≤ 2 * Real.log x := by
    calc
      Real.log (d : ℝ) ≤ Real.log (2 * x) := (Real.log_lt_log hdRealPos hd).le
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (ne_of_gt hxpos)
      _ ≤ 2 * Real.log x := by linarith
  have hScaled : ((P.card : ℝ) * b) * Real.log x ≤ 2 * Real.log x := by
    simpa only [mul_assoc] using hCardLog.trans hDlog
  have hCardb : (P.card : ℝ) * b ≤ 2 :=
    (mul_le_mul_iff_of_pos_right hLpos).mp hScaled
  exact (le_div_iff₀ hb).mpr hCardb

end ArtinPrimitiveRoots.Proofs.c_bins_sol
