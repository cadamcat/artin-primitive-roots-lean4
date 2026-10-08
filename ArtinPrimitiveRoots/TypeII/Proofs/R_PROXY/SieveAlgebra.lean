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

/- Casting a finite natural product to `ℝ` agrees with the product of its
real casts. -/
private theorem cast_nat_product (S : Finset ℕ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [Finset.prod_insert, hp, ih]

/-- The first two terms of the binomial expansion are a lower bound when both
summands are nonnegative. -/
private theorem add_pow_lower_terms (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
    ∀ n : ℕ, s ^ n + (n : ℝ) * a * s ^ (n - 1) ≤ (s + a) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num [pow_one]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        have hpow : s ^ (n - 1) * s = s ^ n := by
          calc
            s ^ (n - 1) * s = s ^ (n - 1 + 1) := by rw [pow_succ]
            _ = s ^ n := by rw [hpred]
        have hpowmul : (n : ℝ) * a * s ^ (n - 1) * s =
            (n : ℝ) * a * s ^ n := by
          rw [mul_assoc, hpow]
        have hmul := mul_le_mul_of_nonneg_right ih (add_nonneg hs ha)
        have hexpand :
            (s ^ n + (n : ℝ) * a * s ^ (n - 1)) * (s + a) =
              s ^ (n + 1) + ((n : ℝ) + 1) * a * s ^ n +
                (n : ℝ) * a ^ 2 * s ^ (n - 1) := by
          calc
            (s ^ n + (n : ℝ) * a * s ^ (n - 1)) * (s + a) =
                s ^ n * s + (n : ℝ) * a * s ^ (n - 1) * s +
                  (s ^ n * a + (n : ℝ) * a * s ^ (n - 1) * a) := by ring
            _ = s ^ n * s + (n : ℝ) * a * s ^ n +
                  (s ^ n * a + (n : ℝ) * a * s ^ (n - 1) * a) := by rw [hpowmul]
            _ = s ^ (n + 1) + ((n : ℝ) + 1) * a * s ^ n +
                  (n : ℝ) * a ^ 2 * s ^ (n - 1) := by
                    rw [pow_succ]
                    ring
        have hcalc :
            s ^ (n + 1) + ((n : ℝ) + 1) * a * s ^ n ≤ (s + a) ^ (n + 1) := by
          calc
            s ^ (n + 1) + ((n : ℝ) + 1) * a * s ^ n ≤
                s ^ (n + 1) + ((n : ℝ) + 1) * a * s ^ n +
                (n : ℝ) * a ^ 2 * s ^ (n - 1) :=
                  le_add_of_nonneg_right (by positivity)
            _ = (s ^ n + (n : ℝ) * a * s ^ (n - 1)) * (s + a) := hexpand.symm
            _ ≤ (s + a) ^ n * (s + a) := hmul
            _ = (s + a) ^ (n + 1) := by rw [pow_succ]
        simpa [Nat.cast_add] using hcalc

/-- For nonnegative weights, the degree-`r` elementary symmetric sum is
bounded by the `r`th power of their sum divided by `r!`. -/
private theorem weighted_powersetCard_bound (P : Finset ℕ)
    (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) : ∀ r : ℕ,
    ∑ S ∈ P.powersetCard r, ∏ p ∈ S, a p ≤
      (∑ p ∈ P, a p) ^ r / (r.factorial : ℝ) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro r
      by_cases hr : r = 0
      · subst r
        simp
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        have hcard : (∅ : Finset ℕ).card < r := by simpa using hrpos
        rw [Finset.powersetCard_eq_empty.mpr hcard]
        simp [hr]
  | @insert p P hp ih =>
      intro r
      by_cases hr : r = 0
      · subst r
        simp
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
        let s : ℝ := ∑ q ∈ P, a q
        have haP : ∀ q ∈ P, 0 ≤ a q := by
          intro q hq
          exact ha q (Finset.mem_insert_of_mem hq)
        have hap : 0 ≤ a p := ha p (Finset.mem_insert_self p P)
        have hsum : (∑ q ∈ insert p P, a q) = a p + s := by
          simp [s, hp]
        have hdisj : Disjoint (P.powersetCard (Nat.succ n))
            ((P.powersetCard n).image (insert p)) := by
          rw [Finset.disjoint_left]
          intro S hS himage
          rcases Finset.mem_image.mp himage with ⟨T, hT, rfl⟩
          exact hp ((Finset.mem_powersetCard.mp hS).1
            (Finset.mem_insert_self p T))
        have hinj : Set.InjOn (insert p) (↑(P.powersetCard n) : Set (Finset ℕ)) := by
          intro S hS T hT hST
          have hpS : p ∉ S := by
            intro hpS
            exact hp ((Finset.mem_powersetCard.mp hS).1 hpS)
          have hpT : p ∉ T := by
            intro hpT
            exact hp ((Finset.mem_powersetCard.mp hT).1 hpT)
          have herase := congrArg (fun U : Finset ℕ => U.erase p) hST
          simpa [hpS, hpT] using herase
        have hdecomp :
            (∑ S ∈ (insert p P).powersetCard (Nat.succ n),
                ∏ q ∈ S, a q) =
              (∑ S ∈ P.powersetCard (Nat.succ n), ∏ q ∈ S, a q) +
                a p * (∑ S ∈ P.powersetCard n, ∏ q ∈ S, a q) := by
          have himageSum :
              (∑ S ∈ P.powersetCard n, ∏ q ∈ insert p S, a q) =
                a p * (∑ S ∈ P.powersetCard n, ∏ q ∈ S, a q) := by
            calc
              _ = ∑ S ∈ P.powersetCard n, a p * (∏ q ∈ S, a q) := by
                    apply Finset.sum_congr rfl
                    intro S hS
                    have hpS : p ∉ S := by
                      intro hpS
                      exact hp ((Finset.mem_powersetCard.mp hS).1 hpS)
                    rw [Finset.prod_insert hpS]
              _ = _ := by rw [Finset.mul_sum]
          calc
            _ = (∑ S ∈ P.powersetCard (Nat.succ n), ∏ q ∈ S, a q) +
                  (∑ S ∈ (P.powersetCard n).image (insert p), ∏ q ∈ S, a q) := by
                    rw [Finset.powersetCard_succ_insert hp, Finset.sum_union hdisj]
            _ = (∑ S ∈ P.powersetCard (Nat.succ n), ∏ q ∈ S, a q) +
                  (∑ S ∈ P.powersetCard n, ∏ q ∈ insert p S, a q) := by
                    rw [Finset.sum_image hinj]
            _ = _ := by rw [himageSum]
        have hih (j : ℕ) :
          (∑ S ∈ P.powersetCard j, ∏ q ∈ S, a q) ≤
              s ^ j / (j.factorial : ℝ) := by
          simpa [s] using ih haP j
        have hbound :
            (∑ S ∈ P.powersetCard (Nat.succ n), ∏ q ∈ S, a q) +
                a p * (∑ S ∈ P.powersetCard n, ∏ q ∈ S, a q) ≤
              s ^ Nat.succ n / ((Nat.succ n).factorial : ℝ) +
                a p * (s ^ n / (n.factorial : ℝ)) := by
          exact add_le_add (hih (Nat.succ n))
            (mul_le_mul_of_nonneg_left (hih n) hap)
        have hfac :
            ((Nat.succ n).factorial : ℝ) =
              (Nat.succ n : ℝ) * (n.factorial : ℝ) := by
          norm_cast
        have hfacpos : 0 < ((Nat.succ n).factorial : ℝ) := by positivity
        have hfn : (n.factorial : ℝ) ≠ 0 := by positivity
        have hratio :
            s ^ Nat.succ n / ((Nat.succ n).factorial : ℝ) +
                a p * (s ^ n / (n.factorial : ℝ)) =
              (s ^ Nat.succ n + (Nat.succ n : ℝ) * a p * s ^ n) /
                ((Nat.succ n).factorial : ℝ) := by
          rw [hfac]
          field_simp [hfn]
        have hs : 0 ≤ s := Finset.sum_nonneg (fun q hq => haP q hq)
        have hbin := add_pow_lower_terms s (a p) hs hap (Nat.succ n)
        have hbin' :
            s ^ Nat.succ n + (Nat.succ n : ℝ) * a p * s ^ n ≤
              (s + a p) ^ Nat.succ n := by
          simpa using hbin
        calc
          (∑ S ∈ (insert p P).powersetCard (Nat.succ n), ∏ q ∈ S, a q) =
              (∑ S ∈ P.powersetCard (Nat.succ n), ∏ q ∈ S, a q) +
                a p * (∑ S ∈ P.powersetCard n, ∏ q ∈ S, a q) := hdecomp
          _ ≤ s ^ Nat.succ n / ((Nat.succ n).factorial : ℝ) +
                a p * (s ^ n / (n.factorial : ℝ)) := hbound
          _ = (s ^ Nat.succ n + (Nat.succ n : ℝ) * a p * s ^ n) /
                ((Nat.succ n).factorial : ℝ) := hratio
          _ ≤ (s + a p) ^ Nat.succ n / ((Nat.succ n).factorial : ℝ) :=
                div_le_div_of_nonneg_right hbin' hfacpos.le
          _ = (∑ q ∈ insert p P, a q) ^ Nat.succ n /
                ((Nat.succ n).factorial : ℝ) := by rw [hsum, add_comm]

/-- The elementary symmetric reciprocal sum is dominated by the full power
sum divided by `r!`. -/
theorem elementary_symmetric_reciprocals (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => S.card = r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) ^ r / (r.factorial : ℝ) := by
  classical
  have hnonneg : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hsum :
      (∑ S ∈ P.powerset.filter (fun S => S.card = r),
          1 / ((∏ p ∈ S, p : ℕ) : ℝ)) =
        ∑ S ∈ P.powersetCard r, ∏ p ∈ S, (p : ℝ)⁻¹ := by
    rw [← Finset.powersetCard_eq_filter]
    apply Finset.sum_congr rfl
    intro S hS
    rw [cast_nat_product, one_div, Finset.prod_inv_distrib]
  rw [hsum]
  simpa [one_div] using weighted_powersetCard_bound P
    (fun p => 1 / (p : ℝ)) hnonneg r

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

/-- Positive multiples of `d` up to `2M` inject into the positive integers at
most `2M/d`, giving a count without an additive error. -/
theorem positive_multiple_count_bound (M : ℝ) (d : ℕ)
    (hM : 0 < M) (hd : 0 < d) (I : Finset ℕ)
    (hI : ∀ m ∈ I, 0 < m ∧ (m : ℝ) ≤ 2 * M) :
    ∑ m ∈ I, (if d ∣ m then (1 : ℝ) else 0) ≤ 2 * M / (d : ℝ) := by
  classical
  let J := I.filter (fun m => d ∣ m)
  let H := (Finset.range (⌊2 * M / (d : ℝ)⌋₊ + 1)).erase 0
  have hsum :
      (∑ m ∈ I, (if d ∣ m then (1 : ℝ) else 0)) = (J.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [J]
  have hqnonneg : 0 ≤ 2 * M / (d : ℝ) := by positivity
  have hmaps : Set.MapsTo (fun m : ℕ => m / d) (J : Set ℕ) (H : Set ℕ) := by
    intro m hm
    have hmI : m ∈ I := (Finset.mem_filter.mp hm).1
    have hdiv : d ∣ m := (Finset.mem_filter.mp hm).2
    have hmpos : 0 < m := (hI m hmI).1
    let q := m / d
    have hcancel : d * (m / d) = m := Nat.mul_div_cancel' hdiv
    have hqpos : 0 < q := by
      by_contra hq
      have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
      have hmzero : m = 0 := by simpa [q, hq0] using hcancel.symm
      exact (Nat.ne_of_gt hmpos) hmzero
    have hcancel' : (m / d) * d = m := by
      rw [Nat.mul_comm]
      exact hcancel
    have hcancelReal : (q : ℝ) * (d : ℝ) = (m : ℝ) := by
      change ((m / d : ℕ) : ℝ) * (d : ℝ) = (m : ℝ)
      exact_mod_cast hcancel'
    have hqbound : (q : ℝ) ≤ 2 * M / (d : ℝ) := by
      apply (le_div_iff₀ (Nat.cast_pos.mpr hd)).2
      rw [hcancelReal]
      exact (hI m hmI).2
    have hqfloor : q ≤ ⌊2 * M / (d : ℝ)⌋₊ :=
      (Nat.le_floor_iff hqnonneg).2 (by exact_mod_cast hqbound)
    have hqmem : q ∈ H := by
      dsimp [H]
      exact Finset.mem_erase.mpr
        ⟨Nat.ne_of_gt hqpos, Finset.mem_range.mpr (Nat.lt_succ_of_le hqfloor)⟩
    simpa [q] using hqmem
  have hinj : Set.InjOn (fun m : ℕ => m / d) (J : Set ℕ) := by
    intro m hm n hn hmn
    have hdm : d ∣ m := (Finset.mem_filter.mp hm).2
    have hdn : d ∣ n := (Finset.mem_filter.mp hn).2
    have hcancelm := Nat.mul_div_cancel' hdm
    have hcanceln := Nat.mul_div_cancel' hdn
    calc
      m = d * (m / d) := hcancelm.symm
      _ = d * (n / d) := congrArg (fun q : ℕ => d * q) hmn
      _ = n := hcanceln
  have hcard : J.card ≤ H.card := Finset.card_le_card_of_injOn
    (fun m : ℕ => m / d) hmaps hinj
  have hHcard : H.card = ⌊2 * M / (d : ℝ)⌋₊ := by
    simp [H]
  calc
    (∑ m ∈ I, (if d ∣ m then (1 : ℝ) else 0)) = (J.card : ℝ) := hsum
    _ ≤ (⌊2 * M / (d : ℝ)⌋₊ : ℝ) := by exact_mod_cast (hcard.trans_eq hHcard)
    _ ≤ 2 * M / (d : ℝ) := Nat.floor_le hqnonneg

/-- If the truncation order is at least twice `e` times the reciprocal-prime
mass, the elementary symmetric remainder has exponentially small factorial
tail. -/
theorem factorial_tail_bound (s : ℝ) (r : ℕ) (hs : 0 ≤ s) (hr : 1 ≤ r)
    (hrs : 2 * Real.exp 1 * s ≤ (r : ℝ)) :
    s ^ r / (r.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ r := by
  have hrNat : 0 < r := by omega
  have hrReal : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hrPos : 0 < (r : ℝ) := by positivity
  have htwoPi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hrootArg : 1 ≤ 2 * Real.pi * (r : ℝ) := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 * Real.pi) * (r : ℝ) :=
        mul_le_mul htwoPi hrReal (by norm_num) (by positivity)
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * (r : ℝ)) :=
    Real.one_le_sqrt.mpr hrootArg
  let a : ℝ := (r : ℝ) / Real.exp 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hfac : a ^ r ≤ (r.factorial : ℝ) := by
    dsimp [a]
    calc
      ((r : ℝ) / Real.exp 1) ^ r =
          1 * ((r : ℝ) / Real.exp 1) ^ r := by ring
      _ ≤ Real.sqrt (2 * Real.pi * (r : ℝ)) *
          ((r : ℝ) / Real.exp 1) ^ r :=
        mul_le_mul_of_nonneg_right hroot (by positivity)
      _ ≤ (r.factorial : ℝ) := Stirling.le_factorial_stirling r
  have hbase : s / a ≤ (1 / 2 : ℝ) := by
    dsimp [a]
    rw [div_le_iff₀ (div_pos hrPos (Real.exp_pos 1))]
    field_simp
    nlinarith [hrs]
  have hpow : (s / a) ^ r ≤ (1 / 2 : ℝ) ^ r :=
    pow_le_pow_left₀ (div_nonneg hs ha.le) hbase r
  have hnum : s ^ r ≤ (1 / 2 : ℝ) ^ r * (r.factorial : ℝ) := by
    have hmul : (s / a) ^ r * a ^ r ≤
        (1 / 2 : ℝ) ^ r * (r.factorial : ℝ) :=
      mul_le_mul hpow hfac (by positivity) (by positivity)
    have hrewrite : (s / a) ^ r * a ^ r = s ^ r := by
      rw [← mul_pow, div_mul_cancel₀ s ha.ne']
    simpa [hrewrite] using hmul
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (r.factorial : ℝ))).2 hnum

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
