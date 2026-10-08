import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadReindexing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical Filter

noncomputable section

/-- Eventually every marked prime lies below the roughness cutoff. -/
theorem markedPrimes_below_rough_eventually {K : ℕ} (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) ≤ roughCutoff x := by
  have hevent : ∀ᶠ x : ℝ in atTop,
      ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) ≤ roughCutoff x := by
    rw [Filter.eventually_all]
    intro i
    have hgap : 0 < (24 / 100 : ℝ) - a i := by linarith [(ha.2.1 i).2]
    have ht : Tendsto (fun x : ℝ => Real.rpow (Real.log x) ((24 / 100 : ℝ) - a i))
        atTop atTop := (tendsto_rpow_atTop hgap).comp Real.tendsto_log_atTop
    filter_upwards [ht.eventually_ge_atTop 2, Filter.eventually_ge_atTop (2 : ℝ)] with x hg hx
    intro p hp
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hpos : 0 < Real.rpow (Real.log x) (a i) := Real.rpow_pos_of_pos hL _
    have hprod : Real.rpow (Real.log x) (24 / 100 : ℝ) =
        Real.rpow (Real.log x) (a i) *
          Real.rpow (Real.log x) ((24 / 100 : ℝ) - a i) := by
      calc
        _ = Real.rpow (Real.log x) (a i + ((24 / 100 : ℝ) - a i)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hL _ _
    have hsep : 2 * Real.rpow (Real.log x) (a i) ≤
        Real.rpow (Real.log x) (24 / 100 : ℝ) := by
      rw [hprod]
      nlinarith [mul_le_mul_of_nonneg_left hg hpos.le]
    exact ((Finset.mem_filter.mp hp).2.2.2).trans
      (Real.exp_le_exp.mpr hsep)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨max 2 x₁, le_max_left _ _, fun x hx => hx₁ x ((le_max_right _ _).trans hx)⟩

/-- A rough residual factor introduces no extra marked prime to a valid list product. -/
theorem markedOmega_listProduct_mul {x W : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hsmall : ∀ i : Fin K, ∀ q ∈ primeBand x (a i), (q : ℝ) ≤ W)
    (m : ℕ) (hm : roughAbove m W) :
    markedOmega x K a ((∏ i : Fin K, ∏ j : Fin (slotCount x), p i j) * m) =
      K * slotCount x := by
  let G := ∏ i : Fin K, ∏ j : Fin (slotCount x), p i j
  have hfilter (i : Fin K) :
      (primeBand x (a i)).filter (fun q => q ∣ G * m) =
        Finset.univ.image (p i) := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqband, hqdiv⟩
      have hqprime : q.Prime := (Finset.mem_filter.mp hqband).2.1
      rcases hqprime.dvd_mul.mp hqdiv with hqG | hqm
      · obtain ⟨i', hi', hinner⟩ := (hqprime.prime.dvd_finsetProd_iff _).mp hqG
        obtain ⟨j, hj, hlabel⟩ := (hqprime.prime.dvd_finsetProd_iff _).mp hinner
        have heq : q = p i' j := (Nat.prime_dvd_prime_iff_eq hqprime (hp.1 i' j).1).mp hlabel
        have hii : i = i' := by
          by_contra hne
          have hnot := Finset.disjoint_left.mp (hbands i i' hne) hqband
          exact hnot (by simpa [heq] using (hp.1 i' j).2)
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simpa [← hii] using heq.symm⟩
      · exact (not_lt_of_ge (hsmall i q hqband) (hm q hqprime hqm)).elim
    · intro hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      refine Finset.mem_filter.mpr ⟨(hp.1 i j).2, ?_⟩
      have hinner : p i j ∣ ∏ j : Fin (slotCount x), p i j :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have houter : (∏ j : Fin (slotCount x), p i j) ∣ G :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      exact dvd_mul_of_dvd_left (hinner.trans houter) m
  have hcount (i : Fin K) : bandOmega x (a i) (G * m) = slotCount x := by
    unfold bandOmega
    rw [hfilter]
    have hinj : Function.Injective (p i) := by
      intro j j' heq
      by_contra hne
      exact hp.2 i j j' hne heq
    simp [Finset.card_image_of_injective _ hinj]
  change (∑ i : Fin K, bandOmega x (a i) (G * m)) = _
  simp_rw [hcount]
  simp

/-- On rough coefficient support the physical damping is exactly one. -/
theorem dampingHalf_listProduct_mul {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (hp : ValidPrimeLists S.x K F.a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (hsmall : ∀ i : Fin K, ∀ q ∈ primeBand S.x (F.a i), (q : ℝ) ≤ roughCutoff S.x)
    (m : ℕ) (hm : roughAbove m (roughCutoff S.x)) :
    dampingHalf F S ((∏ i : Fin K, ∏ j : Fin (slotCount S.x), p i j) * m) = 1 := by
  have hω := markedOmega_listProduct_mul p hp hbands hsmall m hm
  simp [dampingHalf, hω]

end
end ArtinPrimitiveRoots.TypeII.PD
