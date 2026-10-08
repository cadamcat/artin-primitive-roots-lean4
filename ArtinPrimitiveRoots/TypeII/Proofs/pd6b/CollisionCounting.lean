import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TupleCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

def supportedTupleChoices (x Y : ℝ) {K : ℕ} (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  (markedTupleChoices x a).filter fun t => Y ≤ (tupleProduct t : ℝ) ∧ (tupleProduct t : ℝ) ≤ 4 * Y

/-- Count products divisible by p via their positive quotients, then use tuple injectivity. -/
theorem supportedTuple_divisor_count_le {x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hY : 1 ≤ Y)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (p : ℕ) (hp : 0 < p) :
    (((supportedTupleChoices x Y a).filter fun t => p ∣ tupleProduct t).card : ℝ) ≤
      4 * Y / (p : ℝ) := by
  let T := (supportedTupleChoices x Y a).filter fun t => p ∣ tupleProduct t
  let code (t : Fin K → ℕ) := tupleProduct t / p - 1
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hquot (t : Fin K → ℕ) (ht : t ∈ T) : 0 < tupleProduct t / p := by
    have hdiv := (Finset.mem_filter.mp ht).2
    have hlow := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2.1
    have hnpos : 0 < tupleProduct t := by
      have hnr : 0 < (tupleProduct t : ℝ) := lt_of_lt_of_le hYpos hlow
      exact_mod_cast hnr
    have heq := Nat.mul_div_cancel' hdiv
    by_contra hnot
    have hzero : tupleProduct t / p = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, mul_zero] at heq
    exact hnpos.ne' heq.symm
  have hmap : Set.MapsTo code (T : Set (Fin K → ℕ))
      (Finset.range ⌊4 * Y / (p : ℝ)⌋₊ : Set ℕ) := by
    intro t ht
    have hdiv := (Finset.mem_filter.mp ht).2
    have hhi := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2.2
    have hqreal : (tupleProduct t / p : ℕ) ≤ ⌊4 * Y / (p : ℝ)⌋₊ := by
      apply (Nat.le_floor_iff (div_nonneg (by linarith) hpR.le)).mpr
      apply (le_div_iff₀ hpR).mpr
      have heq : (p : ℝ) * ((tupleProduct t / p : ℕ) : ℝ) = (tupleProduct t : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' hdiv
      nlinarith
    exact Finset.mem_range.mpr (by have := hquot t ht; dsimp [code]; omega)
  have hinj : (T : Set (Fin K → ℕ)).InjOn code := by
    intro t ht u hu heq
    have htq := hquot t ht
    have huq := hquot u hu
    have hcode : tupleProduct t / p = tupleProduct u / p := by dsimp [code] at heq; omega
    have hprod : tupleProduct t = tupleProduct u := by
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp ht).2,
        ← Nat.mul_div_cancel' (Finset.mem_filter.mp hu).2, hcode]
    exact markedTupleProduct_injective hbands
      (mem_markedTupleChoices.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1)
      (mem_markedTupleChoices.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1) hprod
  have hcard : T.card ≤ ⌊4 * Y / (p : ℝ)⌋₊ := by
    simpa using Finset.card_le_card_of_injOn code hmap hinj
  have hcardR : (T.card : ℝ) ≤ (⌊4 * Y / (p : ℝ)⌋₊ : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (Nat.floor_le (div_nonneg (by linarith) hpR.le))

private theorem prime_dvd_tuple_mem_marked {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (t : Fin K → ℕ) (ht : IsMarkedPrimeTuple x K a t) (p : ℕ) (hp : p.Prime)
    (hdiv : p ∣ tupleProduct t) : p ∈ markedPrimes x K a := by
  obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff t).mp hdiv
  have heq : p = t i := (Nat.prime_dvd_prime_iff_eq hp (Finset.mem_filter.mp (ht i)).2.1).mp hpi
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa only [heq] using ht i⟩

/-- Numeric products sharing a marked prime form a small set of pairs. -/
theorem supportedTuple_noncoprime_count_le {x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hY : 1 ≤ Y)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    ((((supportedTupleChoices x Y a) ×ˢ (supportedTupleChoices x Y a)).filter fun tu =>
      ¬ Nat.Coprime (tupleProduct tu.1) (tupleProduct tu.2)).card : ℝ) ≤
      16 * Y ^ 2 * ∑ p ∈ markedPrimes x K a, ((p : ℝ)⁻¹) ^ 2 := by
  let T := supportedTupleChoices x Y a
  let Tp (p : ℕ) := T.filter fun t => p ∣ tupleProduct t
  let C := (T ×ˢ T).filter fun tu => ¬ Nat.Coprime (tupleProduct tu.1) (tupleProduct tu.2)
  have hsub : C ⊆ (markedPrimes x K a).biUnion (fun p => (Tp p) ×ˢ (Tp p)) := by
    intro tu htu
    obtain ⟨htuT, hcop⟩ := Finset.mem_filter.mp htu
    obtain ⟨htT, huT⟩ := Finset.mem_product.mp htuT
    obtain ⟨p, hp, hpt, hpu⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have ht : IsMarkedPrimeTuple x K a tu.1 :=
      mem_markedTupleChoices.mp (Finset.mem_filter.mp htT).1
    have hmarked := prime_dvd_tuple_mem_marked tu.1 ht p hp hpt
    exact Finset.mem_biUnion.mpr ⟨p, hmarked, Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨htT, hpt⟩, Finset.mem_filter.mpr ⟨huT, hpu⟩⟩⟩
  have hcard : C.card ≤ ∑ p ∈ markedPrimes x K a, (Tp p).card ^ 2 := by
    calc
      _ ≤ ((markedPrimes x K a).biUnion (fun p => (Tp p) ×ˢ (Tp p))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ p ∈ markedPrimes x K a, ((Tp p) ×ˢ (Tp p)).card := Finset.card_biUnion_le
      _ = _ := by simp [pow_two]
  have hcardR : (C.card : ℝ) ≤ ∑ p ∈ markedPrimes x K a, ((Tp p).card : ℝ) ^ 2 := by
    exact_mod_cast hcard
  change (C.card : ℝ) ≤ _
  apply hcardR.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  have hprime : p.Prime := (Finset.mem_filter.mp hpi).2.1
  have hcount : ((Tp p).card : ℝ) ≤ 4 * Y / (p : ℝ) :=
    supportedTuple_divisor_count_le hY hbands p hprime.pos
  calc
    _ ≤ (4 * Y / (p : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
    _ = 16 * Y ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by rw [div_eq_mul_inv]; ring

/-- Harmonic band mass controls the reciprocal-square collision sum. -/
theorem markedReciprocalSquares_le {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (Pmin B : ℝ) (hP : 0 < Pmin)
    (hlower : ∀ p ∈ markedPrimes x K a, Pmin ≤ (p : ℝ))
    (hMass : ∀ i : Fin K, bandMass x (a i) ≤ B) :
    (∑ p ∈ markedPrimes x K a, ((p : ℝ)⁻¹) ^ 2) ≤ (K : ℝ) * B / Pmin := by
  have htotal : (∑ p ∈ markedPrimes x K a, (p : ℝ)⁻¹) ≤ (K : ℝ) * B := by
    unfold markedPrimes
    rw [Finset.sum_biUnion]
    · calc
        _ ≤ ∑ i : Fin K, B := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [bandMass, one_div] using hMass i
        _ = _ := by simp
    · intro i hi j hj hne
      exact hbands i j hne
  calc
    _ ≤ ∑ p ∈ markedPrimes x K a, Pmin⁻¹ * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPos : 0 < (p : ℝ) := hP.trans_le (hlower p hp)
      have hInv : (p : ℝ)⁻¹ ≤ Pmin⁻¹ := (inv_le_inv₀ hpPos hP).mpr (hlower p hp)
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hInv (inv_nonneg.mpr hpPos.le)
    _ = Pmin⁻¹ * (∑ p ∈ markedPrimes x K a, (p : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ Pmin⁻¹ * ((K : ℝ) * B) := mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hP.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

end
end ArtinPrimitiveRoots.TypeII.PD
