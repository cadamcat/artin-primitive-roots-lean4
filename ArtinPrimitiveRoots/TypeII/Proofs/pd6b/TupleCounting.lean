import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

/-- Finite band-valued tuples, retaining the original natural-valued function type. -/
def markedTupleChoices (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset (fun i => primeBand x (a i))

@[simp] theorem mem_markedTupleChoices {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {t : Fin K → ℕ} : t ∈ markedTupleChoices x a ↔ IsMarkedPrimeTuple x K a t := by
  simp [markedTupleChoices, IsMarkedPrimeTuple]

/-- Separated prime bands make a numeric product determine every tuple entry. -/
theorem markedTupleProduct_injective {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    {ta tb : Fin K → ℕ} (hta : IsMarkedPrimeTuple x K a ta)
    (htb : IsMarkedPrimeTuple x K a tb)
    (hprod : tupleProduct ta = tupleProduct tb) : ta = tb := by
  funext i
  have hp : (ta i).Prime := (Finset.mem_filter.mp (hta i)).2.1
  have hpd : ta i ∣ tupleProduct tb := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem ta (Finset.mem_univ i)
  obtain ⟨j, _, hj⟩ := (hp.prime.dvd_finsetProd_iff tb).mp hpd
  have heq : ta i = tb j := by
    rcases (Nat.dvd_prime ((Finset.mem_filter.mp (htb j)).2.1)).mp hj with h1 | heq
    · exact (hp.ne_one h1).elim
    · exact heq
  have hij : i = j := by
    by_contra hne
    have hnot := Finset.disjoint_left.mp (hbands i j hne) (hta i)
    exact hnot (by simpa [heq] using htb j)
  simpa [← hij] using heq

/-- Count eta-supported tuples through their distinct numeric products. -/
theorem markedTupleChoices_card_le {x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hY : 1 ≤ Y)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    (((markedTupleChoices x a).filter fun t =>
      Y ≤ (tupleProduct t : ℝ) ∧ (tupleProduct t : ℝ) ≤ 4 * Y).card : ℝ) ≤ 5 * Y := by
  let T := (markedTupleChoices x a).filter fun t =>
    Y ≤ (tupleProduct t : ℝ) ∧ (tupleProduct t : ℝ) ≤ 4 * Y
  have hcard : T.card ≤ ⌊4 * Y⌋₊ + 1 := by
    have hmap : Set.MapsTo tupleProduct (T : Set (Fin K → ℕ))
        (Finset.range (⌊4 * Y⌋₊ + 1) : Set ℕ) := by
      intro t ht
      have htY := (Finset.mem_filter.mp ht).2.2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 4 * Y)).2 htY))
    have hinj : (T : Set (Fin K → ℕ)).InjOn tupleProduct := by
      intro ta hta tb htb heq
      exact markedTupleProduct_injective hbands
        (mem_markedTupleChoices.mp (Finset.mem_filter.mp hta).1)
        (mem_markedTupleChoices.mp (Finset.mem_filter.mp htb).1) heq
    simpa using Finset.card_le_card_of_injOn tupleProduct hmap hinj
  have hcardR : (T.card : ℝ) ≤ (⌊4 * Y⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  have hfloor : (⌊4 * Y⌋₊ : ℝ) ≤ 4 * Y := Nat.floor_le (by positivity)
  change (T.card : ℝ) ≤ 5 * Y
  linarith

end
end ArtinPrimitiveRoots.TypeII.PD
