import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyFinite
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyDivisor

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd1c_product_fiber_norm {δ C c₁ c₂ x T : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (b h : ℕ)
    (hT : 0 ≤ T)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ T)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ T)
    (hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n) :
    ‖∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
      if m * n - 1 = b * h then family.alpha x m * beta n else 0‖ ≤
      T ^ 2 * tau (1 + b * h) := by
  let pairs := (familyTerms family x).product (dyadicIntegers (family.Hn x))
  let s := pairs.filter (fun mn => mn.1 * mn.2 - 1 = b * h)
  let divisors := (Finset.range (1 + b * h + 1)).filter (fun d => d ∣ 1 + b * h)
  have hprod : ∀ mn ∈ s, mn.1 * mn.2 = 1 + b * h := by
    intro mn hmn
    have hm := Finset.mem_filter.mp hmn
    have hPair := Finset.mem_product.mp hm.1
    have hp := hPos mn.1 hPair.1 mn.2 hPair.2
    omega
  have hmpos : ∀ mn ∈ s, 0 < mn.1 := by
    intro mn hmn
    have hp := hprod mn hmn
    have : 0 < mn.1 * mn.2 := by omega
    exact Nat.pos_of_mul_pos_right this
  letI : Fintype s := Fintype.ofFinset s (by intro mn; rfl)
  letI : Fintype divisors := Fintype.ofFinset divisors (by intro d; rfl)
  let f : s → divisors := fun mn => ⟨mn.1.1, by
    have heq := hprod mn.1 mn.2
    have hd : mn.1.1 ∣ 1 + b * h := ⟨mn.1.2, heq.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)), hd⟩⟩
  have hf : Function.Injective f := by
    intro mn rs hEq
    have hm : mn.1.1 = rs.1.1 := congrArg Subtype.val hEq
    have hmn := hprod mn.1 mn.2
    have hrs := hprod rs.1 rs.2
    have hn : mn.1.2 = rs.1.2 := Nat.mul_left_cancel (hmpos mn.1 mn.2) (by rw [← hmn, ← hm] at hrs; exact hrs.symm)
    exact Subtype.ext (Prod.ext hm hn)
  have hcard : s.card ≤ tau (1 + b * h) := by
    simpa [Fintype.card_coe, divisors, tau] using Fintype.card_le_of_injective f hf
  have heq : (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
      if m * n - 1 = b * h then family.alpha x m * beta n else 0) =
      ∑ mn ∈ s, family.alpha x mn.1 * beta mn.2 := by
    rw [Finset.sum_filter]
    simpa only [pairs, Finset.product_eq_sprod] using
      (Finset.sum_product (familyTerms family x) (dyadicIntegers (family.Hn x))
        (fun mn : ℕ × ℕ => if mn.1 * mn.2 - 1 = b * h then family.alpha x mn.1 * beta mn.2 else 0)).symm
  rw [heq]
  calc
    _ ≤ ∑ mn ∈ s, ‖family.alpha x mn.1 * beta mn.2‖ := norm_sum_le _ _
    _ ≤ ∑ mn ∈ s, T ^ 2 := by
      apply Finset.sum_le_sum
      intro mn hmn
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp hmn).1
      rw [norm_mul, pow_two]
      exact mul_le_mul (hAlpha mn.1 hm.1) (hBeta mn.2 hm.2) (norm_nonneg _) hT
    _ = (s.card : ℝ) * T ^ 2 := by simp
    _ ≤ (tau (1 + b * h) : ℝ) * T ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = _ := by ring

lemma pd1c_finite_cross_gram {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (H : Finset ℕ)
    (k : ι → ℕ) (l : κ → ℕ) (z : ι → ℂ) (w : κ → ℂ)
    (hk : ∀ i ∈ I, z i ≠ 0 → k i ∈ H) (hl : ∀ j ∈ J, w j ≠ 0 → l j ∈ H) :
    (∑ i ∈ I, ∑ j ∈ J, if k i = l j then z i * star (w j) else 0) =
      ∑ h ∈ H, (∑ i ∈ I, if k i = h then z i else 0) *
        star (∑ j ∈ J, if l j = h then w j else 0) := by
  symm
  simp only [star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : z i = 0
  · simp [hz]
  · by_cases hw : w j = 0
    · simp [hw]
    · by_cases hkl : k i = l j
      · rw [if_pos hkl, Finset.sum_eq_single (k i)]
        · simp [hkl]
        · intro h hh hne
          simp [Ne.symm hne]
        · intro hn
          exact (hn (hk i hi hz)).elim
      · simp only [hkl, ite_false]
        apply Finset.sum_eq_zero
        intro h hh
        by_cases hki : k i = h
        · have hlj : l j ≠ h := by intro he; exact hkl (hki.trans he.symm)
          simp [hlj]
        · simp [hki]

end ArtinPrimitiveRoots.TypeII.PD
