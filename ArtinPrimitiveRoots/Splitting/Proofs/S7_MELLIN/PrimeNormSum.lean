import ArtinPrimitiveRoots.Ext.SplittingInputs

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Prime norm powers are summable and bounded uniformly by the field degree. -/
theorem prime_norm_power_sum_bound (K : Type*) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-σ)) ∧
    (∑' v : HeightOneSpectrum (𝓞 K), Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-σ)) ≤
      (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, Real.rpow (m : ℝ) (-σ) := by
  classical
  let pBelow : HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  have hspan (v : HeightOneSpectrum (𝓞 K)) :
      Ideal.under ℤ v.asIdeal = Ideal.span {(pBelow v : ℤ)} := by
    dsimp only [pBelow]
    rw [Int.ideal_span_absNorm_eq_self]
  have hprime (v : HeightOneSpectrum (𝓞 K)) : (pBelow v).Prime := by
    have : NeZero v.asIdeal := ⟨v.ne_bot⟩
    exact Nat.absNorm_under_prime v.asIdeal
  have hnorm (v : HeightOneSpectrum (𝓞 K)) : pBelow v ≤ Ideal.absNorm v.asIdeal := by
    have hpow : Ideal.absNorm v.asIdeal = pBelow v ^ Ideal.inertiaDeg v.asIdeal ℤ :=
      (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ v.asIdeal) v.asIdeal).symm
    rw [hpow]
    simpa using Nat.pow_le_pow_right (hprime v).one_lt.le
      (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  have hcard (p : Ideal ℤ) [p.IsMaximal] (hp0 : p ≠ ⊥) :
      (IsDedekindDomain.primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K := by
    calc
      (IsDedekindDomain.primesOverFinset p (𝓞 K)).card = ∑ _q : p.primesOver (𝓞 K), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
          ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
          ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 K), Set.ncard_coe_finset]
      _ ≤ ∑ q : p.primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
        Finset.sum_le_sum fun q _ => Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
            (Ideal.inertiaDeg_pos q.1 ℤ).ne')
      _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
      _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K
  have hfibre (F : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) :
      (F.filter fun v => pBelow v = m).card ≤ Module.finrank ℚ K := by
    rcases Finset.eq_empty_or_nonempty (F.filter fun v => pBelow v = m) with h | ⟨v, hv⟩
    · simp [h]
    have key : ∀ q ∈ F.filter (fun v => pBelow v = m),
        Ideal.under ℤ q.asIdeal = Ideal.span {(m : ℤ)} := by
      intro q hq
      rw [← (Finset.mem_filter.mp hq).2, hspan]
    have hp : (Ideal.span {(m : ℤ)}).IsPrime := key v hv ▸ Ideal.IsPrime.under ℤ v.asIdeal
    have hp0 : (Ideal.span {(m : ℤ)} : Ideal ℤ) ≠ ⊥ :=
      key v hv ▸ Ideal.under_ne_bot (A := ℤ) v.ne_bot
    have : (Ideal.span {(m : ℤ)}).IsMaximal := hp.isMaximal hp0
    refine le_trans (Finset.card_le_card_of_injOn (fun q => q.asIdeal)
      (fun q hq => ?_) (fun q _ q' _ h => HeightOneSpectrum.ext h))
      (hcard _ hp0)
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨q.isPrime, ⟨(key q hq).symm⟩⟩
  let g : ℕ → ℝ := fun m => Real.rpow (m : ℝ) (-σ)
  have hg (m : ℕ) : 0 ≤ g m := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hgsum : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hsum (F : Finset (HeightOneSpectrum (𝓞 K))) :
      ∑ v ∈ F, Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-σ) ≤
        (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, g m := by
    have hFT : ∀ v ∈ F, pBelow v ∈ F.image pBelow := fun v hv =>
      Finset.mem_image_of_mem pBelow hv
    calc
      ∑ v ∈ F, Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-σ) ≤ ∑ v ∈ F, g (pBelow v) :=
        Finset.sum_le_sum fun v _ => Real.rpow_le_rpow_of_nonpos
          (by exact_mod_cast (hprime v).pos) (by exact_mod_cast hnorm v) (by linarith)
      _ ≤ (Module.finrank ℚ K : ℝ) * ∑ m ∈ F.image pBelow, g m := by
        rw [← Finset.sum_fiberwise_of_maps_to' hFT g, Finset.mul_sum]
        refine Finset.sum_le_sum fun m _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfibre F m) (hg m)
      _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, g m :=
        mul_le_mul_of_nonneg_left (hgsum.sum_le_tsum _ fun m _ => hg m) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ (fun v : HeightOneSpectrum (𝓞 K) =>
      Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-σ)) := fun _ =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact ⟨summable_of_sum_le hnonneg hsum, Real.tsum_le_of_sum_le hnonneg hsum⟩

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
