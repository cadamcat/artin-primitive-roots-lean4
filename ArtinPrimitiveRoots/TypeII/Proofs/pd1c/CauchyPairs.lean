import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyWeights

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd1c_injective_multiple_count {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (b : ι → ℕ) (Z : ℝ) (hZ : 0 ≤ Z)
    (hpos : ∀ t ∈ T, 0 < b t) (hbound : ∀ t ∈ T, (b t : ℝ) ≤ Z)
    (hinj : Set.InjOn b (T : Set ι)) (p : ℕ) (hp : 0 < p) :
    (((T.filter (fun t => p ∣ b t)).card : ℕ) : ℝ) ≤ Z / p := by
  let s := T.filter (fun t => p ∣ b t)
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq : ∀ t ∈ s, 1 ≤ b t / p ∧ b t / p ≤ ⌊Z / p⌋₊ := by
    intro t ht
    have hm := Finset.mem_filter.mp ht
    have hqpos : 0 < b t / p := Nat.div_pos (Nat.le_of_dvd (hpos t hm.1) hm.2) hp
    refine ⟨hqpos, ?_⟩
    apply (Nat.le_floor_iff (by positivity : 0 ≤ Z / p)).mpr
    apply (le_div_iff₀ hppos).mpr
    have heq : ((b t / p : ℕ) : ℝ) * p = (b t : ℝ) := by exact_mod_cast Nat.div_mul_cancel hm.2
    rw [heq]
    exact hbound t hm.1
  letI : Fintype s := Fintype.ofFinset s (by intro t; rfl)
  let f : s → Fin ⌊Z / p⌋₊ := fun t => ⟨b t.1 / p - 1, by have h := hq t.1 t.2; omega⟩
  have hf : Function.Injective f := by
    intro t s hs
    have heq : b t.1 / p - 1 = b s.1 / p - 1 := congrArg Fin.val hs
    have htq := hq t.1 t.2
    have hsq := hq s.1 s.2
    have hquot : b t.1 / p = b s.1 / p := by omega
    apply Subtype.ext
    apply hinj (Finset.mem_filter.mp t.2).1 (Finset.mem_filter.mp s.2).1
    calc
      b t.1 = (b t.1 / p) * p := (Nat.div_mul_cancel (Finset.mem_filter.mp t.2).2).symm
      _ = (b s.1 / p) * p := by rw [hquot]
      _ = b s.1 := Nat.div_mul_cancel (Finset.mem_filter.mp s.2).2
  have hc := Fintype.card_le_of_injective f hf
  have hc' : (s.card : ℝ) ≤ (⌊Z / p⌋₊ : ℝ) := by simpa [Fintype.card_coe] using (show ((Fintype.card s : ℕ) : ℝ) ≤ Fintype.card (Fin ⌊Z / p⌋₊) by exact_mod_cast hc)
  exact hc'.trans (Nat.floor_le (by positivity))

lemma pd1c_non_coprime_marked_prime {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {t s : Fin K → ℕ} (ht : IsMarkedPrimeTuple x K a t) (hs : IsMarkedPrimeTuple x K a s)
    (hnot : ¬Nat.Coprime (tupleProduct t) (tupleProduct s)) :
    ∃ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ tupleProduct t ∧ p ∣ tupleProduct s := by
  obtain ⟨p, hp, hpt, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  obtain ⟨i, hi, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpt
  have heq : p = t i := by
    rcases (Nat.dvd_prime (pd1c_tuple_entry_prime ht i)).mp hd with h1 | heq
    · exact (hp.ne_one h1).elim
    · exact heq
  exact ⟨i, p, by rw [heq]; exact ht i, hpt, hps⟩

lemma pd1c_non_coprime_tuple_count {x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (T : Finset (Fin K → ℕ)) (hY : 0 < Y)
    (hT : ∀ t ∈ T, IsMarkedPrimeTuple x K a t)
    (hbound : ∀ t ∈ T, (tupleProduct t : ℝ) ≤ 4 * Y)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    (∑ t ∈ T, ∑ s ∈ T, if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then (1 : ℝ) else 0) ≤
      16 * Y ^ 2 * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := by
  let f := fun t s : Fin K → ℕ => fun i : Fin K => fun p : ℕ =>
    if p ∣ tupleProduct t ∧ p ∣ tupleProduct s then (1 : ℝ) else 0
  have hpoint : ∀ t ∈ T, ∀ s ∈ T,
      (if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then (1 : ℝ) else 0) ≤
        ∑ i : Fin K, ∑ p ∈ primeBand x (a i), f t s i p := by
    intro t ht s hs
    by_cases hnot : ¬Nat.Coprime (tupleProduct t) (tupleProduct s)
    · obtain ⟨i, p, hp, hpt, hps⟩ := pd1c_non_coprime_marked_prime (hT t ht) (hT s hs) hnot
      rw [if_pos hnot]
      have h1 : f t s i p ≤ ∑ q ∈ primeBand x (a i), f t s i q :=
        Finset.single_le_sum (fun q hq => by dsimp [f]; split_ifs <;> norm_num) hp
      have h2 : (∑ q ∈ primeBand x (a i), f t s i q) ≤ ∑ j : Fin K, ∑ q ∈ primeBand x (a j), f t s j q :=
        Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin K => ∑ q ∈ primeBand x (a j), f t s j q)
          (fun j hj => Finset.sum_nonneg (fun q hq => by dsimp [f]; split_ifs <;> norm_num)) (Finset.mem_univ i)
      simpa [f, hpt, hps] using h1.trans h2
    · simp only [hnot, ite_false]
      exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun p hp => by dsimp [f]; split_ifs <;> norm_num
  have hcount : ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
      (∑ t ∈ T, ∑ s ∈ T, f t s i p) ≤ 16 * Y ^ 2 * (1 / (p : ℝ)) ^ 2 := by
    intro i p hp
    let g := fun t : Fin K → ℕ => if p ∣ tupleProduct t then (1 : ℝ) else 0
    have heq : (∑ t ∈ T, ∑ s ∈ T, f t s i p) = (∑ t ∈ T, g t) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hpt : p ∣ tupleProduct t <;> by_cases hps : p ∣ tupleProduct s <;> simp [f, g, hpt, hps]
    rw [heq]
    have hcard : (∑ t ∈ T, g t) ≤ 4 * Y / p := by
      simp only [g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact pd1c_injective_multiple_count T tupleProduct (4 * Y) (by positivity)
        (fun t ht => pd1c_tupleProduct_pos (hT t ht)) hbound
        ((pd1c_tupleProduct_injective_on hSep).mono (fun t ht => hT t ht)) p
        (Finset.mem_filter.mp hp).2.1.pos
    have hnn : 0 ≤ ∑ t ∈ T, g t := Finset.sum_nonneg fun t ht => by dsimp [g]; split_ifs <;> norm_num
    calc
      _ ≤ (4 * Y / p) ^ 2 := pow_le_pow_left₀ hnn hcard 2
      _ = _ := by ring
  calc
    _ ≤ ∑ t ∈ T, ∑ s ∈ T, ∑ i : Fin K, ∑ p ∈ primeBand x (a i), f t s i p :=
      Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun s hs => hpoint t ht s hs
    _ = ∑ i : Fin K, ∑ p ∈ primeBand x (a i), ∑ t ∈ T, ∑ s ∈ T, f t s i p := by
      simp_rw [Finset.sum_comm (s := T) (t := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [Finset.sum_comm (s := T) (t := primeBand x (a i))]
    _ ≤ ∑ i : Fin K, ∑ p ∈ primeBand x (a i), 16 * Y ^ 2 * (1 / (p : ℝ)) ^ 2 :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun p hp => hcount i p hp
    _ = _ := by simp only [Finset.mul_sum]

end ArtinPrimitiveRoots.TypeII.PD
