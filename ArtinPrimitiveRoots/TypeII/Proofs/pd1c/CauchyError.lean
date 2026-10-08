import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyCounting

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd1c_weight_difference_bound {x q B : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 0 ≤ B)
    (hMass : ∀ i : Fin K, 0 ≤ bandMass x (a i))
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) (hW : markedWeight x K a q z ≤ B) :
    |markedWeight x K a q z - pd1c_replacedWeight x K a q z| ≤
      B * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), if p ^ 2 ∣ z then (1 : ℝ) else 0) := by
  have hr := pd1c_replacedWeight_bounds hq₀ hq₁ hMass hSep z
  by_cases hs : ∀ p ∈ markedPrimes x K a, ¬p ^ 2 ∣ z
  · rw [pd1c_replacedWeight_eq_of_no_square hSep z hs, sub_self, abs_zero]
    exact mul_nonneg hB (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)))
  · obtain ⟨p, hp⟩ := not_forall.mp hs
    have hp' : p ∈ markedPrimes x K a := by
      by_contra hn
      exact hp (fun h => (hn h).elim)
    have hd' : p ^ 2 ∣ z := by by_contra hn; exact hp (fun h => hn)
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp'
    have h1 : (1 : ℝ) ≤ ∑ q ∈ primeBand x (a i), if q ^ 2 ∣ z then (1 : ℝ) else 0 := by
      have hs := Finset.single_le_sum (s := primeBand x (a i))
        (f := fun q => if q ^ 2 ∣ z then (1 : ℝ) else 0) (fun q hq => by split_ifs <;> norm_num) hpi
      rw [if_pos hd'] at hs
      exact hs
    have h2 : (∑ q ∈ primeBand x (a i), if q ^ 2 ∣ z then (1 : ℝ) else 0) ≤
        ∑ j : Fin K, ∑ q ∈ primeBand x (a j), if q ^ 2 ∣ z then (1 : ℝ) else 0 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin K => ∑ q ∈ primeBand x (a j), if q ^ 2 ∣ z then (1 : ℝ) else 0)
        (fun j hj => Finset.sum_nonneg (fun q hq => by split_ifs <;> norm_num)) (Finset.mem_univ i)
    rw [abs_of_nonneg (sub_nonneg.mpr hr.2)]
    calc
      _ ≤ B := by linarith [hr.1]
      _ = B * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) hB

lemma pd1c_squareful_pair_count
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂)
    (hHm : 1 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x)
    (hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n)
    (hSquare : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) ^ 2 ≤ family.Hn x) :
    (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
      ∑ i : Fin K, ∑ p ∈ primeBand x (a i), if p ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) ≤
      9 * (family.Hm x * family.Hn x) *
        (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := by
  let M := familyTerms family x
  let N := dyadicIntegers (family.Hn x)
  let f := fun m n : ℕ => fun i : Fin K => fun p : ℕ => if p ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0
  have hcard : (M.card : ℝ) ≤ 3 * family.Hm x := by
    have hc : M.card ≤ (dyadicIntegers (family.Hm x)).card := Finset.card_filter_le _ _
    exact (show (M.card : ℝ) ≤ ((dyadicIntegers (family.Hm x)).card : ℝ) by exact_mod_cast hc).trans
      (pd1c_dyadic_card_bound _ hHm)
  have hFixed : ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
      (∑ m ∈ M, ∑ n ∈ N, f m n i p) ≤ 9 * (family.Hm x * family.Hn x) * (1 / (p : ℝ)) ^ 2 := by
    intro i p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
    calc
      _ ≤ ∑ m ∈ M, 3 * family.Hn x / (p ^ 2 : ℕ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact pd1c_dyadic_product_minus_one_count _ m (p ^ 2) hHn (pow_pos hpp.pos _) (by simpa using hSquare i p hp) (hPos m hm)
      _ = (M.card : ℝ) * (3 * family.Hn x / (p ^ 2 : ℕ)) := by simp
      _ ≤ (3 * family.Hm x) * (3 * family.Hn x / (p ^ 2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by push_cast; ring
  change (∑ m ∈ M, ∑ n ∈ N, ∑ i : Fin K, ∑ p ∈ primeBand x (a i), f m n i p) ≤ _
  calc
    _ = ∑ i : Fin K, ∑ p ∈ primeBand x (a i), ∑ m ∈ M, ∑ n ∈ N, f m n i p := by
      simp_rw [Finset.sum_comm (s := N) (t := Finset.univ)]
      rw [Finset.sum_comm (s := M) (t := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [Finset.sum_comm (s := N) (t := primeBand x (a i))]
      rw [Finset.sum_comm (s := M) (t := primeBand x (a i))]
    _ ≤ ∑ i : Fin K, ∑ p ∈ primeBand x (a i), 9 * (family.Hm x * family.Hn x) * (1 / (p : ℝ)) ^ 2 :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun p hp => hFixed i p hp
    _ = _ := by simp only [Finset.mul_sum]

lemma pd1c_replacement_error_bound
    {δ C c₁ c₂ x q T B : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hMass : ∀ i : Fin K, 0 ≤ bandMass x (a i))
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hW : ∀ z, markedWeight x K a q z ≤ B)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ T)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ T) (hF : ∀ z, ‖F z‖ ≤ 1)
    (hHm : 1 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x)
    (hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n)
    (hSquare : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) ^ 2 ≤ family.Hn x) :
    ‖coefficientBilinearSum x K a q family beta F -
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        family.alpha x m * beta n * F (m * n - 1) * (pd1c_replacedWeight x K a q (m * n - 1) : ℂ)‖ ≤
      9 * B * T ^ 2 * (family.Hm x * family.Hn x) *
        (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := by
  have heq : coefficientBilinearSum x K a q family beta F -
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        family.alpha x m * beta n * F (m * n - 1) * (pd1c_replacedWeight x K a q (m * n - 1) : ℂ) =
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        family.alpha x m * beta n * F (m * n - 1) *
          ((markedWeight x K a q (m * n - 1) - pd1c_replacedWeight x K a q (m * n - 1) : ℝ) : ℂ) := by
    simp only [coefficientBilinearSum, markedBilinearSum, familyTerms, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [heq]
  have hpoint : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖family.alpha x m * beta n * F (m * n - 1) *
          ((markedWeight x K a q (m * n - 1) - pd1c_replacedWeight x K a q (m * n - 1) : ℝ) : ℂ)‖ ≤
        B * T ^ 2 * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), if p ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by
    intro m hm n hn
    have hcoef : ‖family.alpha x m * beta n * F (m * n - 1)‖ ≤ T ^ 2 := by
      simp only [norm_mul]
      calc
        _ ≤ T * T * 1 := mul_le_mul (mul_le_mul (hAlpha m hm) (hBeta n hn) (norm_nonneg _) hT) (hF _) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hw := pd1c_weight_difference_bound hq₀ hq₁ hB hMass hSep (m * n - 1) (hW _)
    have hbound := mul_le_mul hcoef hw (abs_nonneg _) (sq_nonneg T)
    exact hbound.trans_eq (by ring)
  calc
    _ ≤ ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        ‖family.alpha x m * beta n * F (m * n - 1) *
          ((markedWeight x K a q (m * n - 1) - pd1c_replacedWeight x K a q (m * n - 1) : ℝ) : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => norm_sum_le _ _)
    _ ≤ ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        B * T ^ 2 * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), if p ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpoint m hm n hn
    _ = B * T ^ 2 * (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
      ∑ i : Fin K, ∑ p ∈ primeBand x (a i), if p ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by simp only [Finset.mul_sum]
    _ ≤ B * T ^ 2 * (9 * (family.Hm x * family.Hn x) *
        (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (pd1c_squareful_pair_count family hHm hHn hPos hSquare) (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
