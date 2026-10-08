import ArtinPrimitiveRoots.TypeII.Defs

/-!
Finite inclusion–exclusion and reciprocal-mass bounds for the R-PROXY
rough-prime sieve.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- The inclusion–exclusion sum truncated before subsets of size `r`. -/
noncomputable def smallPrimeTruncation (x : ℝ) (r m : ℕ) : ℝ :=
  ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter (fun S => S.card < r),
    ((-1 : ℝ) ^ S.card) * (if (∏ p ∈ S, p) ∣ m then 1 else 0)

/-- Alternating partial binomial sums are a single boundary row of Pascal's
triangle. -/
private theorem alternating_choose_partial (s r : ℕ) (hs : 0 < s) :
    ∑ i ∈ Finset.range (r + 1), ((-1 : ℝ) ^ i) * (s.choose i : ℝ) =
      ((-1 : ℝ) ^ r) * ((s - 1).choose r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hpascal : (s.choose (r + 1) : ℝ) =
          ((s - 1).choose r : ℝ) + ((s - 1).choose (r + 1) : ℝ) := by
        rw [← Nat.succ_pred_eq_of_pos hs, Nat.choose_succ_succ]
        norm_cast
      rw [ih, hpascal]
      rw [pow_succ]
      ring

/-- The pointwise truncation error is bounded by the count of omitted `r`-fold
divisors. -/
theorem sieve_remainder_pointwise (x : ℝ) (r m : ℕ)
    (hr : 1 ≤ r) (hm : 0 < m) :
    |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
        smallPrimeTruncation x r m| ≤
      ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card = r),
        if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := by
  sorry

/-- The elementary symmetric reciprocal sum is dominated by the full power
sum divided by `r!`. -/
theorem elementary_symmetric_reciprocals (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => S.card = r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) ^ r / (r.factorial : ℝ) := by
  sorry

/-- Casting a finite natural product to `ℝ` agrees with the product of its
real casts. -/
private theorem cast_nat_product (S : Finset ℕ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [Finset.prod_insert, hp, ih]

/-- Expand the finite Euler product over all subsets. -/
private theorem reciprocal_powerset_euler (P : Finset ℕ) :
    (∑ S ∈ P.powerset, ∏ p ∈ S, (p : ℝ)⁻¹) =
      ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.sum_powerset_insert hp]
      have hinsert : ∀ S ∈ P.powerset,
          (∏ q ∈ insert p S, (q : ℝ)⁻¹) =
            (p : ℝ)⁻¹ * (∏ q ∈ S, (q : ℝ)⁻¹) := by
        intro S hS
        have hpn : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
        rw [Finset.prod_insert hpn]
      have hsum_insert :
          (∑ S ∈ P.powerset, ∏ q ∈ insert p S, (q : ℝ)⁻¹) =
            (p : ℝ)⁻¹ * ∑ S ∈ P.powerset, ∏ q ∈ S, (q : ℝ)⁻¹ := by
        calc
          _ = ∑ S ∈ P.powerset,
              (p : ℝ)⁻¹ * (∏ q ∈ S, (q : ℝ)⁻¹) := by
                apply Finset.sum_congr rfl
                intro S hS
                exact hinsert S hS
          _ = _ := by rw [← Finset.mul_sum]
      rw [hsum_insert, Finset.prod_insert hp, ← ih]
      ring

/-- The reciprocal mass of a truncated powerset is bounded by the full
Euler-product expansion. -/
theorem truncated_divisor_reciprocal_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ) ≤
      ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by
  classical
  let f : Finset ℕ → ℝ := fun S => 1 / ((∏ p ∈ S, p : ℕ) : ℝ)
  let g : Finset ℕ → ℝ := fun S => ∏ p ∈ S, (p : ℝ)⁻¹
  have hsub : P.powerset.filter (fun S => S.card < r) ⊆ P.powerset :=
    Finset.filter_subset _ _
  have hsumle :
      (∑ S ∈ P.powerset.filter (fun S => S.card < r), f S) ≤
        ∑ S ∈ P.powerset, f S :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub (by
      intro S hS hnot
      dsimp [f]
      positivity)
  have hfg : ∀ S ∈ P.powerset, f S = g S := by
    intro S hS
    dsimp [f, g]
    rw [cast_nat_product, one_div, Finset.prod_inv_distrib]
  have hEuler : (∑ S ∈ P.powerset, g S) = ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
    simpa [g] using reciprocal_powerset_euler P
  calc
    _ ≤ ∑ S ∈ P.powerset, f S := by simpa [f] using hsumle
    _ = ∑ S ∈ P.powerset, g S := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hfg S hS
    _ = ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := hEuler
    _ = ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by simp [one_div]

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
