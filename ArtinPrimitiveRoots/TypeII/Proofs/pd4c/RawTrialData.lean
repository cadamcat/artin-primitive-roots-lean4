import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawOmissionFiber
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TupleCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Compatibility retaining the endpoint and the other promoted numeric labels. -/
def RawAnchorEndpoint {K : ℕ} (S : PDScale) (a : Fin K → ℝ)
    (p : PrimeLists S.x K) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (w : ArchRoot) (e : Particle) (z : ℤ × ℤ)
    (om : Fin K → Fin (slotCount S.x)) (t : Fin K → ℕ) (z' : ℤ × ℤ) : Prop :=
  (∀ i, i ∈ I ∧ i ≠ iStar → t i ∈ primeBand S.x (a i)) ∧
  (∀ i, i ∈ I ∧ i ≠ iStar → ∀ j k, t i ≠ p j k) ∧
  (S.d₀ : ℝ) ≤ (omissionProduct p om : ℝ) ∧
  (omissionProduct p om : ℝ) < 2 * (S.d₀ : ℝ) ∧
  envBox S w z' ∧ particleHits e z' ∧
  det2 z z' = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) *
    (omissionProduct p om *
      (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t i else 1) *
      (∏ i : Fin K, if i ∉ I then fresh i else 1) : ℕ)

/-- A separated fresh draw and a fixed promoted anchor determine the omission,
the determinant, and every other promoted numeric label. -/
theorem raw_good_anchor_endpoint_unique {K : ℕ} (S : PDScale) (a : Fin K → ℝ)
    (p : PrimeLists S.x K) (hp : ValidPrimeLists S.x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand S.x (a i)) (primeBand S.x (a j)))
    (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ)
    (hfresh : IsFreshChoice S.x a I fresh) (w : ArchRoot) (e : Particle)
    (he : e.1.Prime) (hband : e.1 ∈ primeBand S.x (a iStar))
    (hban : ∀ i j, e.1 ≠ p i j) (z : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hU : 0 < S.U) (hw : w.InRegion S) (hbox : envBox S w z)
    (hsep : ∀ n₁ n₂, IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₁ →
      IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₂ → n₁ ≠ n₂ →
      100 * Real.exp (-Real.rpow (Real.log S.x) (a iStar)) <
        circleDistance (((n₁ : ℝ) - n₂) * transportedRatio w z))
    (om₁ om₂ : Fin K → Fin (slotCount S.x)) (t₁ t₂ : Fin K → ℕ) (z₁ z₂ : ℤ × ℤ)
    (h₁ : RawAnchorEndpoint S a p I iStar fresh w e z om₁ t₁ z₁)
    (h₂ : RawAnchorEndpoint S a p I iStar fresh w e z om₂ t₂ z₂) :
    om₁ = om₂ ∧ det2 z z₁ = det2 z z₂ ∧
      ∀ i, i ∈ I ∧ i ≠ iStar → t₁ i = t₂ i := by
  obtain ⟨ht₁, hban₁, hlo₁, hhi₁, hbox₁, hh₁, hd₁⟩ := h₁
  obtain ⟨ht₂, hban₂, hlo₂, hhi₂, hbox₂, hh₂, hd₂⟩ := h₂
  have hprime : ∀ i j, (p i j).Prime := fun i j => (hp.1 i j).1
  have hP : ((pd4c_fullPrimeProduct p : ℤ) : ZMod e.1) ≠ 0 := by
    intro hzero
    apply pd4c_prime_not_dvd_fullProduct p hprime e.1 he hban
    exact (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hzero)
  let T : ℕ := ∏ i : Fin K, if i ∉ I then fresh i else 1
  let Z₁ : ℕ := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t₁ i else 1
  let Z₂ : ℕ := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t₂ i else 1
  let n₁ := omissionProduct p om₁ * Z₁ * T
  let n₂ := omissionProduct p om₂ * Z₂ * T
  have hT : T ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    by_cases hmem : i ∉ I
    · rw [if_pos hmem]
      exact (Finset.mem_filter.mp (hfresh.2 i hmem)).2.1.ne_zero
    · rw [if_neg hmem]
      exact one_ne_zero
  have htrial₁ : IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₁ :=
    ⟨om₁, t₁, rfl, hlo₁, hhi₁, ht₁⟩
  have htrial₂ : IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₂ :=
    ⟨om₂, t₂, rfl, hlo₂, hhi₂, ht₂⟩
  have hn : n₁ = n₂ := pd4c_raw_good_trial_unique a p (S.d₀ : ℝ) I iStar fresh
    S w e he hband z z₁ z₂ hz hU hw hbox hbox₁ hbox₂ hP hh₁ hh₂
    n₁ n₂ hd₁ hd₂ htrial₁ htrial₂ hsep
  have hcross₁ : Nat.Coprime (omissionProduct p om₁) Z₂ :=
    pd4c_omission_promoted_coprime p hprime om₁ I iStar t₂
      (fun i hi => (Finset.mem_filter.mp (ht₂ i hi)).2.1) hban₂
  have hcross₂ : Nat.Coprime (omissionProduct p om₂) Z₁ :=
    pd4c_omission_promoted_coprime p hprime om₂ I iStar t₁
      (fun i hi => (Finset.mem_filter.mp (ht₁ i hi)).2.1) hban₁
  have hom : om₁ = om₂ := pd4c_trial_omission_unique p hprime
    (pd4c_validPrimeLists_global_injective p hp hbands)
    om₁ om₂ Z₁ Z₂ T hT hcross₁ hcross₂ hn
  have hdet : det2 z z₁ = det2 z z₂ := by
    calc
      _ = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) * n₁ := hd₁
      _ = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) * n₂ := by rw [hn]
      _ = _ := hd₂.symm
  have hD : omissionProduct p om₁ ≠ 0 := by
    unfold omissionProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    by_cases hkeep : j ≠ om₁ i
    · simp only [if_pos hkeep]
      exact (hprime i j).ne_zero
    · simp only [if_neg hkeep, ne_eq, one_ne_zero, not_false_eq_true]
  have hZ : Z₁ = Z₂ := by
    have hprod : omissionProduct p om₁ * Z₁ * T = omissionProduct p om₁ * Z₂ * T := by
      simpa only [n₁, n₂, ← hom] using hn
    exact mul_left_cancel₀ hD (mul_right_cancel₀ hT hprod)
  let u₁ : Fin K → ℕ := fun i => if i ∈ I ∧ i ≠ iStar then t₁ i else p i (lastSlot S.x)
  let u₂ : Fin K → ℕ := fun i => if i ∈ I ∧ i ≠ iStar then t₂ i else p i (lastSlot S.x)
  have hu₁ : IsMarkedPrimeTuple S.x K a u₁ := by
    intro i
    by_cases hi : i ∈ I ∧ i ≠ iStar
    · simpa only [u₁, if_pos hi] using ht₁ i hi
    · simpa only [u₁, if_neg hi] using (hp.1 i (lastSlot S.x)).2
  have hu₂ : IsMarkedPrimeTuple S.x K a u₂ := by
    intro i
    by_cases hi : i ∈ I ∧ i ≠ iStar
    · simpa only [u₂, if_pos hi] using ht₂ i hi
    · simpa only [u₂, if_neg hi] using (hp.1 i (lastSlot S.x)).2
  let R : ℕ := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then 1 else p i (lastSlot S.x)
  have hfactor (t : Fin K → ℕ) :
      tupleProduct (fun i => if i ∈ I ∧ i ≠ iStar then t i else p i (lastSlot S.x)) =
        (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t i else 1) * R := by
    dsimp only [tupleProduct, R]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hmem : i ∈ I ∧ i ≠ iStar
    · simp only [if_pos hmem, mul_one]
    · simp only [if_neg hmem, one_mul]
  have huproduct : tupleProduct u₁ = tupleProduct u₂ := by
    change tupleProduct (fun i => if i ∈ I ∧ i ≠ iStar then t₁ i else p i (lastSlot S.x)) =
      tupleProduct (fun i => if i ∈ I ∧ i ≠ iStar then t₂ i else p i (lastSlot S.x))
    rw [hfactor t₁, hfactor t₂]
    exact congrArg (fun Z : ℕ => Z * R) hZ
  have hu : u₁ = u₂ := markedTupleProduct_injective hbands hu₁ hu₂ huproduct
  refine ⟨hom, hdet, ?_⟩
  intro i hi
  simpa only [u₁, u₂, if_pos hi] using congrFun hu i

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
