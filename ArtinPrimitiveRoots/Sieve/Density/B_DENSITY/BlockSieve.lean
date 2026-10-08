import Mathlib
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Counting

/-! Uniform block-sieve estimates for the density comparison. -/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

/-- Uniform block-sieve error bound for the interval `(x,2x]` with divisibility conditions by
primes up to `z`. Its small-product error is bounded separately by counting prime products. -/
lemma roughIntegerCount_le_block :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℕ, ∀ (z : ℝ), 2 ≤ z → ∀ (x : ℝ), 0 ≤ x → ∀ H : ℕ,
      Even H → H₀ ≤ H →
      |roughIntegerCount x z - x * ∏ p ∈ roughSievePrimes z, (1 - 1 / (p : ℝ))| ≤
        K * Real.exp (-(H : ℝ)) *
            (x * ∏ p ∈ roughSievePrimes z, (1 - 1 / (p : ℝ))) +
          K * ∑ D ∈ (roughSievePrimes z).powerset with
            ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2),
            |(∑ n ∈ roughIntegerInterval x with ∀ p ∈ D, p ∣ n, (1 : ℝ)) -
              x * ∏ p ∈ D, (1 / (p : ℝ))| := by
  classical
  obtain ⟨C₀, hC₀, hband⟩ := exists_prime_reciprocal_band_bound
  obtain ⟨K, hK, H₀, hblock⟩ :=
    ArtinPrimitiveRoots.Sieve.lem_block (η₀ := 1 / 2) C₀ (by norm_num)
  refine ⟨K, hK, H₀, ?_⟩
  intro z hz x hx H hHeven hH
  let A := roughIntegerInterval x
  let P := roughSievePrimes z
  let bad : ℕ → ℕ → Prop := fun p n => p ∣ n
  let g : ℕ → ℝ := fun p => 1 / (p : ℝ)
  have hwt : ∀ n ∈ A, 0 ≤ (1 : ℝ) := by intro n hn; norm_num
  have hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z := by
    intro p hp
    simp only [P, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    refine ⟨hp.2, ?_⟩
    have hz0 : 0 ≤ z := by linarith
    exact (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le hz0)
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - (1 / 2 : ℝ) := by
    intro p hp
    have hpPrime : p.Prime := (hP p hp).1
    have hp2 : 2 ≤ p := hpPrime.two_le
    constructor
    · dsimp [g]
      positivity
    · have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      dsimp [g]
      rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by ring]
      exact (one_div_le_one_div_of_le (by norm_num) hpcast)
  have hlocal : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀ := by
    intro v hv
    have hsubset :
        P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2) ⊆
          ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => v < (p : ℝ)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpCond⟩
      rcases hpCond with ⟨hvlt, hpv⟩
      have hv20 : 0 ≤ v ^ 2 := sq_nonneg v
      have hpP' : (2 ≤ p ∧ p ≤ ⌊z⌋₊) ∧ p.Prime := by
        simpa [P, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] using hpP
      apply Finset.mem_filter.mpr
      refine ⟨?_, hvlt⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hpP'.1.1, ?_⟩, hpP'.2⟩
      exact (Nat.le_floor_iff hv20).2 hpv
    have hsum :
        (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p) ≤
          ∑ p ∈ ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => v < (p : ℝ)), g p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpB
      change 0 ≤ 1 / (p : ℝ)
      positivity
    exact hsum.trans (by simpa [g] using hband v hv)
  have happly := hblock ℕ A (fun _ => (1 : ℝ)) hwt z hz P hP bad x g hx hg hlocal
  have hfirst := happly.1 H hHeven hH
  simpa [roughIntegerCount, A, P, bad, g, mul_assoc, mul_left_comm, mul_comm] using hfirst

/-- The number of multiples of `d` in `(x, 2x]` differs from its expected length by at most
one. -/
lemma roughIntegerMultipleCount_error (x : ℝ) (hx : 0 ≤ x) (d : ℕ) (hd : 0 < d) :
    |(∑ n ∈ roughIntegerInterval x with d ∣ n, (1 : ℝ)) - x / (d : ℝ)| ≤ 1 := by
  classical
  let a : ℕ := ⌊x⌋₊
  let c : ℕ := ⌊2 * x⌋₊
  have hac : a ≤ c := by
    dsimp [a, c]
    apply Nat.floor_mono
    nlinarith
  have hinterval : roughIntegerInterval x = Finset.Ioc a c := by
    ext n
    simp [roughIntegerInterval, a, c, Finset.mem_Icc, Finset.mem_Ioc]
  rw [hinterval]
  have hsplit : Finset.Ioc 0 a ∪ Finset.Ioc a c = Finset.Ioc 0 c := by
    exact Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hac
  have hdisj : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a c) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hna hnc
    simp only [Finset.mem_Ioc] at hna hnc
    omega
  have hfilterUnion :
      (Finset.Ioc 0 a).filter (fun n : ℕ => d ∣ n) ∪
        (Finset.Ioc a c).filter (fun n : ℕ => d ∣ n) =
        (Finset.Ioc 0 c).filter (fun n : ℕ => d ∣ n) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    rw [← hsplit]
    simp only [Finset.mem_union, Finset.mem_Ioc]
    tauto
  have hdisj' : Disjoint
      ((Finset.Ioc 0 a).filter (fun n : ℕ => d ∣ n))
      ((Finset.Ioc a c).filter (fun n : ℕ => d ∣ n)) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hna hnc
    have hna' : n ∈ Finset.Ioc 0 a := (Finset.mem_filter.mp hna).1
    have hnc' : n ∈ Finset.Ioc a c := (Finset.mem_filter.mp hnc).1
    exact (Finset.disjoint_left.mp hdisj) hna' hnc'
  have hcardUnion := Finset.card_union_of_disjoint hdisj'
  rw [hfilterUnion, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hcardUnion
  have hdiv : a / d ≤ c / d := Nat.div_le_div_right hac
  have hcard : ((Finset.Ioc a c).filter (fun n : ℕ => d ∣ n)).card = c / d - a / d := by
    omega
  have hsum :
      (∑ n ∈ Finset.Ioc a c with d ∣ n, (1 : ℝ)) =
        ((c / d : ℕ) : ℝ) - ((a / d : ℕ) : ℝ) := by
    rw [show (∑ n ∈ Finset.Ioc a c with d ∣ n, (1 : ℝ)) =
        (((Finset.Ioc a c).filter (fun n : ℕ => d ∣ n)).card : ℝ) by simp]
    rw [hcard]
    rw [Nat.cast_sub hdiv]
  have hfloorA : ((a / d : ℕ) : ℝ) = ⌊x / (d : ℝ)⌋₊ := by
    simp [a, Nat.floor_div_natCast]
  have hfloorC : ((c / d : ℕ) : ℝ) = ⌊(2 * x) / (d : ℝ)⌋₊ := by
    simp [c, Nat.floor_div_natCast]
  rw [hsum, hfloorA, hfloorC]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht : 0 ≤ x / (d : ℝ) := div_nonneg hx (le_of_lt hdR)
  have hfloorLo (t : ℝ) : t - 1 ≤ (⌊t⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one t
    linarith
  have hfloorHi (t : ℝ) (ht : 0 ≤ t) : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hmul : (2 * x) / (d : ℝ) = 2 * (x / (d : ℝ)) := by field_simp
  rw [hmul]
  have hlow := hfloorLo (x / (d : ℝ))
  have hhigh := hfloorHi (x / (d : ℝ)) ht
  have hlow2 := hfloorLo (2 * (x / (d : ℝ)))
  have hhigh2 := hfloorHi (2 * (x / (d : ℝ))) (by positivity)
  rw [abs_le]
  constructor <;> nlinarith

/-- For a finite set of distinct primes, simultaneous divisibility is divisibility by their
product. -/
lemma primeSet_dvd_prod_iff (P D : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hD : D ⊆ P)
    (n : ℕ) : (∀ p ∈ D, p ∣ n) ↔ (∏ p ∈ D, p : ℕ) ∣ n := by
  classical
  revert hD n
  induction D using Finset.induction_on with
  | empty => intro hD n; simp
  | @insert p D hpD ih =>
      intro hD n
      have hpP : p.Prime := hP p (hD (Finset.mem_insert_self p D))
      have hDP : D ⊆ P := fun q hq => hD (Finset.mem_insert_of_mem hq)
      have hprodCop : Nat.Coprime p (∏ q ∈ D, q : ℕ) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        have hqP : q.Prime := hP q (hDP hq)
        have hpq : p ≠ q := by
          intro heq
          subst q
          exact hpD hq
        exact (Nat.coprime_primes hpP hqP).2 hpq
      constructor
      · intro hall
        have hp : p ∣ n := hall p (Finset.mem_insert_self p D)
        have hallD : ∀ q ∈ D, q ∣ n := fun q hq => hall q (Finset.mem_insert_of_mem hq)
        have hDvd : (∏ q ∈ D, q : ℕ) ∣ n := (ih hDP n).mp hallD
        rw [Finset.prod_insert hpD]
        exact hprodCop.mul_dvd_of_dvd_of_dvd hp hDvd
      · intro h
        rw [Finset.prod_insert hpD] at h
        simp only [Finset.forall_mem_insert]
        refine ⟨?_, ?_⟩
        · exact (dvd_mul_right p (∏ q ∈ D, q)).trans h
        · intro q hq
          exact (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) p).trans h

/-- A squarefree product of distinct primes determines its prime set. -/
lemma primeSetProduct_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ D ∈ P.powerset, ∀ E ∈ P.powerset,
      (∏ p ∈ D, p : ℕ) = ∏ p ∈ E, p → D = E := by
  classical
  intro D hD E hE hprod
  apply Finset.Subset.antisymm
  · intro p hpD
    have hpPrime : p.Prime := hP p ((Finset.mem_powerset.mp hD) hpD)
    have hpdivD : p ∣ ∏ q ∈ D, q := Finset.dvd_prod_of_mem _ hpD
    have hpdivE : p ∣ ∏ q ∈ E, q := by rw [← hprod]; exact hpdivD
    obtain ⟨q, hqE, hpq⟩ := (hpPrime.prime.dvd_finsetProd_iff id).mp hpdivE
    have hqPrime : q.Prime := hP q ((Finset.mem_powerset.mp hE) hqE)
    have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpq
    simpa [hpqeq] using hqE
  · intro p hpE
    have hpPrime : p.Prime := hP p ((Finset.mem_powerset.mp hE) hpE)
    have hpdivE : p ∣ ∏ q ∈ E, q := Finset.dvd_prod_of_mem _ hpE
    have hpdivD : p ∣ ∏ q ∈ D, q := by rw [hprod]; exact hpdivE
    obtain ⟨q, hqD, hpq⟩ := (hpPrime.prime.dvd_finsetProd_iff id).mp hpdivD
    have hqPrime : q.Prime := hP q ((Finset.mem_powerset.mp hD) hqD)
    have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpq
    simpa [hpqeq] using hqD

/-- There are at most `⌊y⌋ + 1` subsets of a finite prime set whose product is at most `y`. -/
lemma primeProducts_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (y : ℝ) (hy : 0 ≤ y) :
    ((P.powerset.filter fun D : Finset ℕ => (∏ p ∈ D, p : ℕ) ≤ y)).card ≤ ⌊y⌋₊ + 1 := by
  classical
  let S := P.powerset.filter fun D : Finset ℕ => (∏ p ∈ D, p : ℕ) ≤ y
  let f : Finset ℕ → ℕ := fun D => ∏ p ∈ D, p
  have hmaps : Set.MapsTo f S (Finset.range (⌊y⌋₊ + 1) : Set ℕ) := by
    intro D hD
    change D ∈ S at hD
    have hD' := Finset.mem_filter.mp hD
    change f D ∈ Finset.range (⌊y⌋₊ + 1)
    apply Finset.mem_range.mpr
    have hprod : f D ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hD'.2
    exact Nat.lt_succ_of_le hprod
  have hinj : (S : Set (Finset ℕ)).InjOn f := by
    intro D hD E hE hDE
    change D ∈ S at hD
    change E ∈ S at hE
    exact primeSetProduct_injective P hP D
      ((Finset.mem_filter.mp hD).1) E ((Finset.mem_filter.mp hE).1) hDE
  calc
    S.card ≤ (Finset.range (⌊y⌋₊ + 1)).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = ⌊y⌋₊ + 1 := by simp
    _ = ⌊y⌋₊ + 1 := rfl

/-- Every block-sieve divisibility error for `(x,2x]` is bounded by one. -/
lemma roughBlockDivisibilityError_le_one {z x : ℝ} (hz : 2 ≤ z) (hx : 0 ≤ x)
    (D : Finset ℕ) (hD : D ⊆ roughSievePrimes z) :
    |(∑ n ∈ roughIntegerInterval x with (∀ p ∈ D, p ∣ n), (1 : ℝ)) -
      x * ∏ p ∈ D, (1 / (p : ℝ))| ≤ 1 := by
  classical
  let P := roughSievePrimes z
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    have hp' : (2 ≤ p ∧ p ≤ ⌊z⌋₊) ∧ p.Prime := by
      simpa [P, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] using hp
    exact hp'.2
  let d : ℕ := ∏ p ∈ D, p
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hP p (hD hp)).pos
  have hpred : ∀ n : ℕ, (∀ p ∈ D, p ∣ n) ↔ d ∣ n := by
    intro n
    exact primeSet_dvd_prod_iff P D hP hD n
  have hsum :
      (∑ n ∈ roughIntegerInterval x with (∀ p ∈ D, p ∣ n), (1 : ℝ)) =
        ∑ n ∈ roughIntegerInterval x with d ∣ n, (1 : ℝ) := by
    have hfilter :
        (roughIntegerInterval x).filter (fun n => ∀ p ∈ D, p ∣ n) =
          (roughIntegerInterval x).filter (fun n => d ∣ n) := by
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn, hdiv⟩
        exact ⟨hn, (hpred n).mp hdiv⟩
      · rintro ⟨hn, hdiv⟩
        exact ⟨hn, (hpred n).mpr hdiv⟩
    rw [hfilter]
  have hweight : ∏ p ∈ D, (1 / (p : ℝ)) = 1 / (d : ℝ) := by
    simp [d, one_div, Finset.prod_inv_distrib]
  rw [hsum, hweight]
  simpa [div_eq_mul_inv] using roughIntegerMultipleCount_error x hx d hd

end ArtinPrimitiveRoots.Proofs.b_density_sol
