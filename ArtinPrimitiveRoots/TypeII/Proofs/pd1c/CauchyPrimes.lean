import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchySquare
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.BandGeometry

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_tuple_entry_prime {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t) (i : Fin K) : (t i).Prime :=
  (Finset.mem_filter.mp (ht i)).2.1

lemma pd1c_marked_tuple_prime_factor
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (i : Fin K) (p : ℕ) (hp : p ∈ primeBand x (a i)) :
    p ∣ tupleProduct t ↔ p = t i := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  constructor
  · intro hdiv
    obtain ⟨j, hj, hDj⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hdiv
    have hpEq : p = t j := by
      rcases (Nat.dvd_prime (pd1c_tuple_entry_prime ht j)).mp hDj with hone | heq
      · exact (hprime.ne_one hone).elim
      · exact heq
    by_cases hij : i = j
    · simpa only [hij] using hpEq
    · have hmemj : p ∈ primeBand x (a j) := by rw [hpEq]; exact ht j
      exact (Finset.disjoint_left.mp (hSep i j hij) hp hmemj).elim
  · intro heq
    rw [heq]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

lemma pd1c_tupleProduct_injective_on
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Set.InjOn tupleProduct {t : Fin K → ℕ | IsMarkedPrimeTuple x K a t} := by
  intro t ht s hs heq
  funext i
  have hd : t i ∣ tupleProduct s := by
    rw [← heq]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  exact (pd1c_marked_tuple_prime_factor hs hSep i (t i) (ht i)).mp hd

lemma pd1c_bandOmega_mul_tuple
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (h : ℕ) (i : Fin K) :
    (primeBand x (a i)).filter (fun p => p ∣ tupleProduct t * h) =
      insert (t i) ((primeBand x (a i)).filter (fun p => p ∣ h)) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hdiv⟩
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    rcases hprime.dvd_mul.mp hdiv with hd | hd
    · exact Or.inl ((pd1c_marked_tuple_prime_factor ht hSep i p hp).mp hd)
    · exact Or.inr ⟨hp, hd⟩
  · rintro (heq | ⟨hp, hd⟩)
    · subst p
      exact ⟨ht i, dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _⟩
    · exact ⟨hp, dvd_mul_of_dvd_right hd _⟩

lemma pd1c_bandOmega_mul_tuple_le
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (h : ℕ) (i : Fin K) :
    bandOmega x (a i) h ≤ bandOmega x (a i) (tupleProduct t * h) ∧
      bandOmega x (a i) (tupleProduct t * h) ≤ bandOmega x (a i) h + 1 := by
  unfold bandOmega
  rw [pd1c_bandOmega_mul_tuple ht hSep]
  exact ⟨Finset.card_le_card (Finset.subset_insert _ _), Finset.card_insert_le _ _⟩

lemma pd1c_bandOmega_mul_tuple_eq
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (h : ℕ) (i : Fin K) (hnot : ¬t i ∣ h) :
    bandOmega x (a i) (tupleProduct t * h) = bandOmega x (a i) h + 1 := by
  unfold bandOmega
  rw [pd1c_bandOmega_mul_tuple ht hSep, Finset.card_insert_of_notMem (by simp [hnot])]

lemma pd1c_markedOmega_mul_tuple_le
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) (h : ℕ) :
    markedOmega x K a h ≤ markedOmega x K a (tupleProduct t * h) ∧
      markedOmega x K a (tupleProduct t * h) ≤ markedOmega x K a h + K := by
  constructor
  · exact Finset.sum_le_sum fun i hi => (pd1c_bandOmega_mul_tuple_le ht hSep h i).1
  · calc
      _ ≤ ∑ i : Fin K, (bandOmega x (a i) h + 1) :=
        Finset.sum_le_sum fun i hi => (pd1c_bandOmega_mul_tuple_le ht hSep h i).2
      _ = _ := by simp [markedOmega, Finset.sum_add_distrib]

lemma pd1c_markedOmega_mul_tuple_eq
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (h : ℕ) (hnot : ∀ i, ¬t i ∣ h) :
    markedOmega x K a (tupleProduct t * h) = markedOmega x K a h + K := by
  unfold markedOmega
  simp_rw [pd1c_bandOmega_mul_tuple_eq ht hSep h _ (hnot _)]
  simp [Finset.sum_add_distrib]

lemma pd1c_marked_invariant_tuple_mul
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (F : ℕ → ℂ) (hF : IsMarkedInvariant x K a F)
    (t : Fin K → ℕ) (ht : IsMarkedPrimeTuple x K a t) (h : ℕ) : F (tupleProduct t * h) = F h := by
  have hmul : ∀ s : Finset (Fin K), ∀ h : ℕ, F ((∏ i ∈ s, t i) * h) = F h := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        intro h
        rw [Finset.prod_insert hi, mul_assoc]
        have hMarked : t i ∈ markedPrimes x K a :=
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht i⟩
        rw [hF.2 (t i) _ hMarked (pd1c_tuple_entry_prime ht i), ih]
  exact hmul Finset.univ h

end ArtinPrimitiveRoots.TypeII.PD
