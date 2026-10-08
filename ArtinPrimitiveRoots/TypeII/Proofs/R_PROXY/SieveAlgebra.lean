import ArtinPrimitiveRoots.TypeII.Defs

/-!
Finite inclusion–exclusion and reciprocal-mass bounds for the R-PROXY
rough-prime sieve.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- The inclusion–exclusion sum truncated before subsets of size `r`. -/
noncomputable def smallPrimeTruncation (x : ℝ) (r m : ℕ) : ℝ :=
  ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter (fun S => S.card < r),
    ((-1 : ℝ) ^ S.card) * (if (∏ p ∈ S, p) ∣ m then 1 else 0)

/-- Alternating partial binomial sums are a single boundary row of Pascal's
triangle. -/
private theorem alternating_choose_partial (s r : ℕ) (hs : 0 < s) :
    ∑ i ∈ Finset.range (r + 1), ((-1 : ℝ) ^ i) * (s.choose i : ℝ) =
      ((-1 : ℝ) ^ r) * ((s - 1).choose r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hpascal : (s.choose (r + 1) : ℝ) =
          ((s - 1).choose r : ℝ) + ((s - 1).choose (r + 1) : ℝ) := by
        rw [← Nat.succ_pred_eq_of_pos hs, Nat.choose_succ_succ]
        norm_cast
      rw [ih, hpascal]
      rw [pow_succ]
      ring

/-- The pointwise truncation error is bounded by the count of omitted `r`-fold
divisors. -/
theorem sieve_remainder_pointwise (x : ℝ) (r m : ℕ)
    (hr : 1 ≤ r) (hm : 0 < m) :
    |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
        smallPrimeTruncation x r m| ≤
      ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card = r),
        if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := by
  classical
  let W := roughCutoff x
  let P := primesUpTo W
  let D := P.filter (fun p => p ∣ m)
  have hWnonneg : 0 ≤ W := (Real.exp_pos _).le
  have hPmem (p : ℕ) : p ∈ P ↔ p.Prime ∧ (p : ℝ) ≤ W := by
    dsimp [P]
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff hWnonneg]
    exact and_comm
  have hDsub : D ⊆ P := Finset.filter_subset _ _
  have hprodDvd (S : Finset ℕ) (hS : S ⊆ P) :
      (∏ p ∈ S, p) ∣ m ↔ S ⊆ D := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
        have hSsub : S ⊆ P := by
          intro q hq
          exact hS (Finset.mem_insert_of_mem hq)
        have hpP : p ∈ P := hS (Finset.mem_insert_self p S)
        have hpPrime : p.Prime := (hPmem p).mp hpP |>.1
        have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
          apply Nat.coprime_prod_right_iff.mpr
          intro q hq
          have hqPrime : q.Prime := (hPmem q).mp (hSsub hq) |>.1
          have hpq : p ≠ q := by
            intro hpq
            subst q
            exact hp hq
          exact (Nat.coprime_primes hpPrime hqPrime).2 hpq
        have hmul : p * (∏ q ∈ S, q) ∣ m ↔
            p ∣ m ∧ (∏ q ∈ S, q) ∣ m := by
          constructor
          · intro hdiv
            exact ⟨dvd_trans (dvd_mul_of_dvd_left dvd_rfl _) hdiv,
              dvd_trans (dvd_mul_of_dvd_right dvd_rfl _) hdiv⟩
          · rintro ⟨hpdiv, hSdiv⟩
            exact hcop.mul_dvd_of_dvd_of_dvd hpdiv hSdiv
        rw [Finset.prod_insert hp, hmul, ih hSsub]
        simp [D, Finset.insert_subset_iff, Finset.mem_filter, hpP]
  have hroughFilter : roughAbove m W ↔ D = ∅ := by
    constructor
    · intro hrough
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hpD
      rcases Finset.mem_filter.mp hpD with ⟨hpP, hpdiv⟩
      rcases (hPmem p).mp hpP with ⟨hpPrime, hpLe⟩
      exact (not_lt_of_ge hpLe) (hrough p hpPrime hpdiv)
    · intro hD p hpPrime hpdiv
      by_contra hpW
      have hpLe : (p : ℝ) ≤ W := le_of_not_gt hpW
      have hpP : p ∈ P := (hPmem p).mpr ⟨hpPrime, hpLe⟩
      have hpD : p ∈ D := Finset.mem_filter.mpr ⟨hpP, hpdiv⟩
      rw [hD] at hpD
      exact Finset.notMem_empty p hpD
  have htruncFilter :
      (P.powerset.filter (fun S => S.card < r)).filter
          (fun S => (∏ p ∈ S, p) ∣ m) =
        D.powerset.filter (fun S => S.card < r) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hSP, hcard⟩, hdiv⟩
      exact ⟨(hprodDvd S hSP).mp hdiv, hcard⟩
    · rintro ⟨hSD, hcard⟩
      exact ⟨⟨hSD.trans hDsub, hcard⟩,
        (hprodDvd S (hSD.trans hDsub)).mpr hSD⟩
  have htrunc : smallPrimeTruncation x r m =
      ∑ S ∈ D.powerset.filter (fun S => S.card < r), ((-1 : ℝ) ^ S.card) := by
    calc
      _ = ∑ S ∈ P.powerset.filter (fun S => S.card < r),
          if (∏ p ∈ S, p) ∣ m then ((-1 : ℝ) ^ S.card) else 0 := by
            unfold smallPrimeTruncation
            apply Finset.sum_congr rfl
            intro S hS
            by_cases hdiv : (∏ p ∈ S, p) ∣ m <;> simp [hdiv]
      _ = ∑ S ∈
          (P.powerset.filter (fun S => S.card < r)).filter
            (fun S => (∏ p ∈ S, p) ∣ m), ((-1 : ℝ) ^ S.card) := by
            rw [← Finset.sum_filter]
      _ = ∑ S ∈ D.powerset.filter (fun S => S.card < r),
          ((-1 : ℝ) ^ S.card) := by rw [htruncFilter]
  have hrhsFilter :
      (P.powerset.filter (fun S => S.card = r)).filter
          (fun S => (∏ p ∈ S, p) ∣ m) = D.powersetCard r := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hcard⟩, hdiv⟩
      exact ⟨(hprodDvd S hSP).mp hdiv, hcard⟩
    · rintro ⟨hSD, hcard⟩
      exact ⟨⟨hSD.trans hDsub, hcard⟩,
        (hprodDvd S (hSD.trans hDsub)).mpr hSD⟩
  have hrhs :
      (∑ S ∈ P.powerset.filter (fun S => S.card = r),
          if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0) =
        (D.card.choose r : ℝ) := by
    calc
      _ = ∑ S ∈ (P.powerset.filter (fun S => S.card = r)).filter
          (fun S => (∏ p ∈ S, p) ∣ m), (1 : ℝ) := by
            rw [← Finset.sum_filter]
      _ = (D.card.choose r : ℝ) := by
            rw [hrhsFilter]
            simp [Finset.card_powersetCard]
  have htruncUnion :
      D.powerset.filter (fun S => S.card < r) =
        (Finset.range r).biUnion (fun i => D.powersetCard i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSD, hcard⟩
      exact ⟨S.card, hcard, hSD, rfl⟩
    · rintro ⟨i, hi, hSD, hcard⟩
      exact ⟨hSD, by simpa [hcard] using hi⟩
  have hdisjoint : (↑(Finset.range r) : Set ℕ).PairwiseDisjoint
      (fun i => D.powersetCard i) := by
    intro i hi j hj hij
    exact Finset.disjoint_powersetCard_of_ne hij D D
  have hslice (i : ℕ) :
      (∑ S ∈ D.powersetCard i, ((-1 : ℝ) ^ S.card)) =
        ((-1 : ℝ) ^ i) * (D.card.choose i : ℝ) := by
    calc
      _ = ∑ S ∈ D.powersetCard i, ((-1 : ℝ) ^ i) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [(Finset.mem_powersetCard.mp hS).2]
      _ = _ := by simp [Finset.card_powersetCard, mul_comm]
  have htruncCount :
      (∑ S ∈ D.powerset.filter (fun S => S.card < r), ((-1 : ℝ) ^ S.card)) =
        ∑ i ∈ Finset.range r, ((-1 : ℝ) ^ i) * (D.card.choose i : ℝ) := by
    rw [htruncUnion, Finset.sum_biUnion hdisjoint]
    apply Finset.sum_congr rfl
    intro i hi
    exact hslice i
  have hpowsetEmpty :
      (Finset.powerset (∅ : Finset ℕ)).filter (fun S => S.card < r) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, _⟩
      exact Finset.eq_empty_iff_forall_notMem.mpr (by
        intro p hp
        exact Finset.notMem_empty p (hS hp))
    · intro hS
      subst S
      exact ⟨Finset.empty_subset _, by simpa using (show 0 < r by omega)⟩
  have hsmall : smallPrimeTruncation x r m =
      if D.card = 0 then 1 else
        ((-1 : ℝ) ^ (r - 1)) * ((D.card - 1).choose (r - 1) : ℝ) := by
    by_cases hs : D.card = 0
    · have hDempty : D = ∅ := Finset.card_eq_zero.mp hs
      rw [htrunc, hDempty, hpowsetEmpty]
      simp
    · have hspos : 0 < D.card := Nat.pos_of_ne_zero hs
      have hrEq : r = (r - 1) + 1 := by omega
      rw [htrunc, htruncCount, if_neg hs, hrEq]
      exact alternating_choose_partial D.card (r - 1) hspos
  by_cases hs : D.card = 0
  · have hDempty : D = ∅ := Finset.card_eq_zero.mp hs
    have hrough : roughAbove m W := hroughFilter.mpr hDempty
    have hrough' : roughAbove m (roughCutoff x) := by simpa [W] using hrough
    have hr0 : 0 < r := by omega
    rw [hrhs, hsmall]
    simp [hrough', hs, hr0]
  · have hspos : 0 < D.card := Nat.pos_of_ne_zero hs
    have hrough : ¬ roughAbove m W := by
      intro h
      have hDempty : D = ∅ := hroughFilter.mp h
      exact hs (by simp [hDempty])
    have hrough' : ¬ roughAbove m (roughCutoff x) := by simpa [W] using hrough
    have hDpred : Nat.succ (D.card - 1) = D.card :=
      Nat.succ_pred_eq_of_pos hspos
    have hrpred : Nat.succ (r - 1) = r :=
      Nat.succ_pred_eq_of_pos (n := r) (by omega)
    have hpascalNat : D.card.choose r =
        (D.card - 1).choose (r - 1) + (D.card - 1).choose r := by
      calc
        D.card.choose r = (Nat.succ (D.card - 1)).choose (Nat.succ (r - 1)) :=
          congrArg₂ Nat.choose hDpred.symm hrpred.symm
        _ = (D.card - 1).choose (r - 1) + (D.card - 1).choose r := by
          rw [Nat.choose_succ_succ, hrpred]
    have hpascal : (D.card.choose r : ℝ) =
        ((D.card - 1).choose (r - 1) : ℝ) +
          ((D.card - 1).choose r : ℝ) := by exact_mod_cast hpascalNat
    have hcoef : 0 ≤ ((D.card - 1).choose (r - 1) : ℝ) := by positivity
    have hnext : 0 ≤ ((D.card - 1).choose r : ℝ) := by positivity
    have hsign : |(-1 : ℝ) ^ (r - 1)| = 1 := by simp
    rw [hrhs, hsmall, if_neg hs, if_neg hrough', zero_sub, abs_neg]
    rw [abs_mul, hsign, abs_of_nonneg hcoef, hpascal]
    nlinarith [hnext]

/-- The elementary symmetric reciprocal sum is dominated by the full power
sum divided by `r!`. -/
theorem elementary_symmetric_reciprocals (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => S.card = r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) ^ r / (r.factorial : ℝ) := by
  sorry

/-- Casting a finite natural product to `ℝ` agrees with the product of its
real casts. -/
private theorem cast_nat_product (S : Finset ℕ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [Finset.prod_insert, hp, ih]

/-- Expand the finite Euler product over all subsets. -/
private theorem reciprocal_powerset_euler (P : Finset ℕ) :
    (∑ S ∈ P.powerset, ∏ p ∈ S, (p : ℝ)⁻¹) =
      ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.sum_powerset_insert hp]
      have hinsert : ∀ S ∈ P.powerset,
          (∏ q ∈ insert p S, (q : ℝ)⁻¹) =
            (p : ℝ)⁻¹ * (∏ q ∈ S, (q : ℝ)⁻¹) := by
        intro S hS
        have hpn : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
        rw [Finset.prod_insert hpn]
      have hsum_insert :
          (∑ S ∈ P.powerset, ∏ q ∈ insert p S, (q : ℝ)⁻¹) =
            (p : ℝ)⁻¹ * ∑ S ∈ P.powerset, ∏ q ∈ S, (q : ℝ)⁻¹ := by
        calc
          _ = ∑ S ∈ P.powerset,
              (p : ℝ)⁻¹ * (∏ q ∈ S, (q : ℝ)⁻¹) := by
                apply Finset.sum_congr rfl
                intro S hS
                exact hinsert S hS
          _ = _ := by rw [← Finset.mul_sum]
      rw [hsum_insert, Finset.prod_insert hp, ← ih]
      ring

/-- The reciprocal mass of a truncated powerset is bounded by the full
Euler-product expansion. -/
theorem truncated_divisor_reciprocal_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ) ≤
      ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by
  classical
  let f : Finset ℕ → ℝ := fun S => 1 / ((∏ p ∈ S, p : ℕ) : ℝ)
  let g : Finset ℕ → ℝ := fun S => ∏ p ∈ S, (p : ℝ)⁻¹
  have hsub : P.powerset.filter (fun S => S.card < r) ⊆ P.powerset :=
    Finset.filter_subset _ _
  have hsumle :
      (∑ S ∈ P.powerset.filter (fun S => S.card < r), f S) ≤
        ∑ S ∈ P.powerset, f S :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub (by
      intro S hS hnot
      dsimp [f]
      positivity)
  have hfg : ∀ S ∈ P.powerset, f S = g S := by
    intro S hS
    dsimp [f, g]
    rw [cast_nat_product, one_div, Finset.prod_inv_distrib]
  have hEuler : (∑ S ∈ P.powerset, g S) = ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
    simpa [g] using reciprocal_powerset_euler P
  calc
    _ ≤ ∑ S ∈ P.powerset, f S := by simpa [f] using hsumle
    _ = ∑ S ∈ P.powerset, g S := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hfg S hS
    _ = ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := hEuler
    _ = ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by simp [one_div]

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
