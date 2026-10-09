import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawAnchor

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A raw endpoint after fixing the fresh labels and one promoted particle.
The other promoted labels remain free, subject to their bands and the source ban. -/
def RawAnchorCompatible {K : ℕ} (S : PDScale) (a : Fin K → ℝ)
    (p : PrimeLists S.x K) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (w : ArchRoot) (e : Particle) (z : ℤ × ℤ)
    (om : Fin K → Fin (slotCount S.x)) : Prop :=
  ∃ t : Fin K → ℕ, ∃ z' : ℤ × ℤ,
    (∀ i, i ∈ I ∧ i ≠ iStar → t i ∈ primeBand S.x (a i)) ∧
    (∀ i, i ∈ I ∧ i ≠ iStar → ∀ j k, t i ≠ p j k) ∧
    (S.d₀ : ℝ) ≤ (omissionProduct p om : ℝ) ∧
    (omissionProduct p om : ℝ) < 2 * (S.d₀ : ℝ) ∧
    envBox S w z' ∧ particleHits e z' ∧
    det2 z z' = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) *
      (omissionProduct p om *
        (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t i else 1) *
        (∏ i : Fin K, if i ∉ I then fresh i else 1) : ℕ)

/-- On a separated fresh draw, all compatible raw endpoints occupy one omission fiber.
Uniform source symmetrization gives that fiber mass `M⁻ᴷ`, including its internal orders. -/
theorem raw_good_anchor_omission_average {K : ℕ} (S : PDScale) (a : Fin K → ℝ)
    (p : PrimeLists S.x K) (hp : ∀ i j, (p i j).Prime)
    (hinj : Function.Injective (fun ij : Fin K × Fin (slotCount S.x) => p ij.1 ij.2))
    (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ)
    (hfresh : IsFreshChoice S.x a I fresh) (w : ArchRoot) (e : Particle)
    (he : e.1.Prime) (hband : e.1 ∈ primeBand S.x (a iStar))
    (hban : ∀ i j, e.1 ≠ p i j) (z : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hU : 0 < S.U) (hw : w.InRegion S) (hbox : envBox S w z)
    (hsep : ∀ n₁ n₂, IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₁ →
      IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₂ → n₁ ≠ n₂ →
        100 * Real.exp (-Real.rpow (Real.log S.x) (a iStar)) <
          circleDistance (((n₁ : ℝ) - n₂) * transportedRatio w z))
    (W : (Fin K → Equiv.Perm (Fin (slotCount S.x))) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ σ, W σ ≤ C)
    (hsupport : ∀ σ, W σ ≠ 0 →
      RawAnchorCompatible S a p I iStar fresh w e z (fun i => σ i (lastSlot S.x))) :
    (permCount S.x K : ℝ)⁻¹ *
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), W σ ≤
        C / (slotCount S.x : ℝ) ^ K := by
  have hP : ((pd4c_fullPrimeProduct p : ℤ) : ZMod e.1) ≠ 0 := by
    intro hzero
    apply pd4c_prime_not_dvd_fullProduct p hp e.1 he hban
    exact (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hzero)
  let T : ℕ := ∏ i : Fin K, if i ∉ I then fresh i else 1
  have hT : T ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    by_cases hmem : i ∉ I
    · rw [if_pos hmem]
      exact (Finset.mem_filter.mp (hfresh.2 i hmem)).2.1.ne_zero
    · rw [if_neg hmem]
      exact one_ne_zero
  have hunique (om₁ om₂ : Fin K → Fin (slotCount S.x))
      (h₁ : RawAnchorCompatible S a p I iStar fresh w e z om₁)
      (h₂ : RawAnchorCompatible S a p I iStar fresh w e z om₂) : om₁ = om₂ := by
    obtain ⟨t₁, z₁, ht₁, hban₁, hlo₁, hhi₁, hbox₁, hh₁, hd₁⟩ := h₁
    obtain ⟨t₂, z₂, ht₂, hban₂, hlo₂, hhi₂, hbox₂, hh₂, hd₂⟩ := h₂
    let Z₁ := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t₁ i else 1
    let Z₂ := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then t₂ i else 1
    let n₁ := omissionProduct p om₁ * Z₁ * T
    let n₂ := omissionProduct p om₂ * Z₂ * T
    have htrial₁ : IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₁ :=
      ⟨om₁, t₁, rfl, hlo₁, hhi₁, ht₁⟩
    have htrial₂ : IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₂ :=
      ⟨om₂, t₂, rfl, hlo₂, hhi₂, ht₂⟩
    have hn : n₁ = n₂ := pd4c_raw_good_trial_unique a p (S.d₀ : ℝ) I iStar fresh
      S w e he hband z z₁ z₂ hz hU hw hbox hbox₁ hbox₂ hP hh₁ hh₂
      n₁ n₂ hd₁ hd₂ htrial₁ htrial₂ hsep
    have hcross₁ : Nat.Coprime (omissionProduct p om₁) Z₂ :=
      pd4c_omission_promoted_coprime p hp om₁ I iStar t₂
        (fun i hi => (Finset.mem_filter.mp (ht₂ i hi)).2.1) hban₂
    have hcross₂ : Nat.Coprime (omissionProduct p om₂) Z₁ :=
      pd4c_omission_promoted_coprime p hp om₂ I iStar t₁
        (fun i hi => (Finset.mem_filter.mp (ht₁ i hi)).2.1) hban₁
    exact pd4c_trial_omission_unique p hp hinj om₁ om₂ Z₁ Z₂ T hT hcross₁ hcross₂ hn
  by_cases hex : ∃ σ, W σ ≠ 0
  · obtain ⟨σ₀, hσ₀⟩ := hex
    let P := RawAnchorCompatible S a p I iStar fresh w e z
    have hprob := omission_probability_le_singleton K (slotCount S.x)
      (by unfold slotCount; omega) (fun _ => lastSlot S.x) P
      (fun i => σ₀ i (lastSlot S.x))
      (fun om hom => hunique om _ hom (hsupport σ₀ hσ₀))
    have hterm (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
        W σ ≤ C * (if P (fun i => σ i (lastSlot S.x)) then (1 : ℝ) else 0) := by
      by_cases hs : P (fun i => σ i (lastSlot S.x))
      · simpa only [if_pos hs, mul_one] using hW σ
      · have hzero : W σ = 0 := by
          by_contra hne
          exact hs (hsupport σ hne)
        simp only [hzero, if_neg hs, mul_zero, le_refl]
    calc
      _ ≤ (permCount S.x K : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            C * (if P (fun i => σ i (lastSlot S.x)) then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ hσ => hterm σ) (by positivity)
      _ = C * ((permCount S.x K : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            if P (fun i => σ i (lastSlot S.x)) then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ C * (1 / (slotCount S.x : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left hprob hC
      _ = _ := by ring
  · have hzero : ∀ σ, W σ = 0 := by
      intro σ
      by_contra hne
      exact hex ⟨σ, hne⟩
    simp only [hzero, Finset.sum_const_zero, mul_zero]
    exact div_nonneg hC (pow_nonneg (Nat.cast_nonneg _) _)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
