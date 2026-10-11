import ArtinPrimitiveRoots.Construction.Proofs.c4.PairBlock

/-! Uniform form of the pair block sieve and the pointwise survivor criterion for
`con_rough_pairs`. The block-sieve constant is chosen before all
sieve data, so that the leading constant of the rough-pair estimate is absolute. -/

namespace ArtinPrimitiveRoots.Construction.Proofs.CRP

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction.Proofs.C4

/-- `pairSieveBlock_upper` with the block-sieve constant `K` chosen before the sieve data. -/
theorem pairSieveBlock_upper_uniform (η C₀ : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (k : ℕ) (P : Finset ℕ) (W H₁ H₂ z : ℝ)
        (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime) (hcopBase : ∀ p ∈ P, Nat.Coprime k p),
        2 ≤ z → (∀ p ∈ P, (p : ℝ) ≤ z) → 2 ≤ H₁ → 2 ≤ H₂ →
        (∀ p ∈ P, 0 ≤ pairSieveG W p ∧ pairSieveG W p ≤ 1 - η) →
        (∀ v : ℝ, 1 < v →
          ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
            pairSieveG W p ≤ C₀) →
        ((pairSieveSurvivors H₁ H₂ k P W).card : ℝ) ≤
          K * ((H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
            ∏ p ∈ P, (1 - pairSieveG W p)) +
          K * ∑ D ∈ P.powerset.filter
            (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
              pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase := by
  obtain ⟨K, hK, H₀, hBlock⟩ := ArtinPrimitiveRoots.Sieve.lem_block η C₀ hη
  refine ⟨K, hK, ?_⟩
  intro k P W H₁ H₂ z hk hprime hcopBase hz hPz hH₁ hH₂ hgbounds hblock
  classical
  let A := pairSieveBasePairs H₁ H₂ k
  let bad : ℕ → ℕ × ℕ → Prop := fun p mn =>
    localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))
  let X' : ℝ := H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2
  have hX' : 0 ≤ X' := by
    have h1 : (0 : ℝ) ≤ H₁ := by linarith
    have h2 : (0 : ℝ) ≤ H₂ := by linarith
    dsimp [X']
    positivity
  have hwt : ∀ mn ∈ A, (0 : ℝ) ≤ (fun _ : ℕ × ℕ => (1 : ℝ)) mn := by intro _ _; norm_num
  have hErr : ∀ D ∈ P.powerset.filter
      (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      |(∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) -
          X' * ∏ p ∈ D, pairSieveG W p| ≤
        pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase := by
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hprimeD : ∀ p ∈ D, p.Prime := fun p hp => hprime p (hDP hp)
    have hcopD : ∀ p ∈ D, Nat.Coprime k p := fun p hp => hcopBase p (hDP hp)
    have hpos := pairSieveModuli_positive D hk hprimeD
    let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
    letI : NeZero q := ⟨Nat.ne_of_gt hpos.2⟩
    letI : ∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i) :=
      fun i => ⟨Nat.ne_of_gt (hpos.1 i)⟩
    have hfilter : A.filter (fun mn : ℕ × ℕ => ∀ p ∈ D, bad p mn) =
        pairSieveIntersectionPairs H₁ H₂ k D W := by
      ext mn
      simp [A, bad, pairSieveBasePairs, pairSieveIntersectionPairs,
        Finset.mem_filter, Finset.mem_product, and_assoc]
    have hsum : (∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) =
        (pairSieveIntersectionPairs H₁ H₂ k D W).card := by
      rw [Finset.sum_filter]
      simp [hfilter]
    have hcount :
        (pairSieveIntersectionPairs H₁ H₂ k D W).card =
          dyadicPairResidueClassCount H₁ H₂ q
            (pairSieveResidues D W hprimeD hcopD) := by
      simpa [q, pairSieveIntersectionPairs] using
        pairSieveIntersection_card_eq D W H₁ H₂ hprimeD hcopD
    have hmain := pairSieveMainTerm_eq D W H₁ H₂ hk hprimeD hcopD
    have hlat : pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase =
        |(pairSieveIntersectionPairs H₁ H₂ k D W).card -
          X' * ∏ p ∈ D, pairSieveG W p| := by
      rw [pairSieveLatticeError]
      simp only [hDP, ↓reduceDIte]
      dsimp [q] at hcount hmain ⊢
      rw [hcount]
      rw [hmain]
    rw [hsum, hlat]
  have hUpper := (hBlock (ℕ × ℕ) A (fun _ : ℕ × ℕ => (1 : ℝ)) hwt z hz P
    (by intro p hp; exact ⟨hprime p hp, hPz p hp⟩) bad X' (fun p => pairSieveG W p) hX'
    hgbounds hblock).2
  have hsurvivors :
      (∑ mn ∈ A with ∀ p ∈ P, ¬ bad p mn, (1 : ℝ)) =
        (pairSieveSurvivors H₁ H₂ k P W).card := by
    rw [Finset.sum_filter]
    have hset : A.filter (fun mn : ℕ × ℕ => ∀ p ∈ P, ¬ bad p mn) =
        pairSieveSurvivors H₁ H₂ k P W := by
      ext mn
      simp [A, bad, pairSieveSurvivors, pairSieveBasePairs]
    simp [hset]
  have hErrSum :
      (∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
          |(∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) -
            X' * ∏ p ∈ D, pairSieveG W p|) ≤
        ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
          pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase :=
    Finset.sum_le_sum hErr
  rw [← hsurvivors]
  calc
    (∑ mn ∈ A with ∀ p ∈ P, ¬ bad p mn, (1 : ℝ)) ≤
        K * (X' * ∏ p ∈ P, (1 - pairSieveG W p)) +
          K * ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
            |(∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) -
              X' * ∏ p ∈ D, pairSieveG W p| := by
      simpa using hUpper
    _ ≤ K * (X' * ∏ p ∈ P, (1 - pairSieveG W p)) +
          K * ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
            pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase := by
      gcongr

/-- Step 1 of §13: a rough pair whose product is `c·r·Q+1`, with `Q` a prime above the sieve
level, survives the pair sieve modulo `c·r` at every odd prime `p ≤ z` not dividing `r`. -/
theorem mem_pairSieveSurvivors_of_factor {H₁ H₂ W z : ℝ} {c r Q m n : ℕ}
    (hc : c = 2 ∨ c = 4)
    (hm : m ∈ dyadicIntegers H₁) (hn : n ∈ dyadicIntegers H₂)
    (hmr : roughAbove m W) (hnr : roughAbove n W)
    (hQ : Q.Prime) (hzQ : z < (Q : ℝ))
    (hmn : m * n = c * r * Q + 1) :
    (m, n) ∈ pairSieveSurvivors H₁ H₂ (c * r)
      ((primesUpTo z).filter (fun p : ℕ => 2 < p ∧ ¬ p ∣ r)) W := by
  classical
  have hbase : ((m : ZMod (c * r)) * (n : ZMod (c * r))) = 1 := by
    have h : ((m * n : ℕ) : ZMod (c * r)) = ((c * r * Q + 1 : ℕ) : ZMod (c * r)) := by
      rw [hmn]
    push_cast at h
    rw [h]
    have hz : ((c : ZMod (c * r)) * (r : ZMod (c * r))) = 0 := by
      have : ((c * r : ℕ) : ZMod (c * r)) = 0 := ZMod.natCast_self _
      push_cast at this
      exact this
    rw [hz]
    ring
  simp only [pairSieveSurvivors, pairSieveBasePairs, Finset.mem_filter]
  refine ⟨⟨Finset.mem_product.mpr ⟨hm, hn⟩, hbase⟩, ?_⟩
  intro p hp
  obtain ⟨hpz, hp2, hpr⟩ := hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpz).2
  have hpLe : (p : ℝ) ≤ z := by
    have hmem := Finset.mem_filter.mp hpz
    have hlt := Finset.mem_range.mp hmem.1
    have hfloor : p ≤ ⌊z⌋₊ := Nat.lt_succ_iff.mp hlt
    have hz0 : 0 ≤ z := by
      by_contra hneg
      push Not at hneg
      have : ⌊z⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have : p = 0 := by omega
      exact hpPrime.ne_zero this
    exact (Nat.le_floor_iff hz0).mp hfloor
  intro hbad
  rcases hbad with hone | ⟨hpW, hzero⟩
  · -- `p ∣ c*r*Q`
    have h : ((m * n : ℕ) : ZMod p) = ((c * r * Q + 1 : ℕ) : ZMod p) := by rw [hmn]
    push_cast at h
    have hcrQ : ((c * r * Q : ℕ) : ZMod p) = 0 := by
      push_cast
      have h1 : (m : ZMod p) * (n : ZMod p) = (c : ZMod p) * r * Q + 1 := h
      rw [hone] at h1
      linear_combination -h1
    have hdvd : p ∣ c * r * Q := (ZMod.natCast_eq_zero_iff _ _).mp hcrQ
    rcases (Nat.Prime.dvd_mul hpPrime).mp hdvd with hcr | hpQ
    · rcases (Nat.Prime.dvd_mul hpPrime).mp hcr with hpc | hpr'
      · have hc4 : c ∣ 4 := by rcases hc with h | h <;> subst h <;> norm_num
        have hp4 : p ∣ 2 ^ 2 := by simpa using dvd_trans hpc hc4
        have hp2' : p ∣ 2 := hpPrime.dvd_of_dvd_pow hp4
        have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2'
        omega
      · exact hpr hpr'
    · have hpQ' : p = Q := ((Nat.prime_dvd_prime_iff_eq hpPrime hQ).mp hpQ)
      subst hpQ'
      linarith
  · have hprod : ((m * n : ℕ) : ZMod p) = 0 := by push_cast; exact hzero
    have hdvd : p ∣ m * n := (ZMod.natCast_eq_zero_iff _ _).mp hprod
    rcases (Nat.Prime.dvd_mul hpPrime).mp hdvd with hpm | hpn
    · have := hmr p hpPrime hpm
      linarith
    · have := hnr p hpPrime hpn
      linarith

end ArtinPrimitiveRoots.Construction.Proofs.CRP
