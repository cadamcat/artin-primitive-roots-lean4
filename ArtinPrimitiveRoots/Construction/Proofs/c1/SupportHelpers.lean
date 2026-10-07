import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Marked

namespace ArtinPrimitiveRoots.Construction

open Classical
open ArtinPrimitiveRoots.TypeII

lemma prime_of_mem_markedPrimes {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : ℕ}
    (hp : p ∈ markedPrimes x K a) : p.Prime := by
  simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
  obtain ⟨i, hi⟩ := hp
  exact (Finset.mem_filter.mp hi).2.1

lemma markedPart_mul_of_mem {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p h : ℕ}
    (hpmem : p ∈ markedPrimes x K a) (hp : p.Prime) (hh : h ≠ 0) :
    markedPart x K a (p * h) = p * markedPart x K a h := by
  classical
  let S := markedPrimes x K a
  have hval (q : ℕ) (hq : q ∈ S) :
      padicValNat q (p * h) = padicValNat q h + (if q = p then 1 else 0) := by
    have hqprime : q.Prime := prime_of_mem_markedPrimes (by simpa [S] using hq)
    letI : Fact q.Prime := ⟨hqprime⟩
    by_cases hqp : q = p
    · subst q
      rw [padicValNat_base_mul hp.one_lt hh]
      simp
    · have hnot : ¬ q ∣ p := by
        intro hdiv
        exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp hdiv)
      rw [padicValNat.mul hp.ne_zero hh]
      rw [padicValNat.eq_zero_of_not_dvd hnot]
      simp [hqp]
  have hdelta : ∏ q ∈ S, q ^ (if q = p then 1 else 0) = p := by
    rw [Finset.prod_eq_single_of_mem p hpmem (fun q hq hqp => by simp [hqp])]
    simp
  unfold markedPart
  calc
    (∏ q ∈ markedPrimes x K a, q ^ padicValNat q (p * h)) =
        ∏ q ∈ S, q ^ (padicValNat q h + (if q = p then 1 else 0)) := by
          apply Finset.prod_congr rfl
          intro q hq
          exact congrArg (fun n : ℕ => q ^ n) (hval q hq)
    _ = (∏ q ∈ S, q ^ padicValNat q h) *
          (∏ q ∈ S, q ^ (if q = p then 1 else 0)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro q hq
          exact Nat.pow_add _ _ _
    _ = p * (∏ q ∈ S, q ^ padicValNat q h) := by rw [hdelta]; ring

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (f : ℕ → ℕ) (hdiv : p ∣ s.prod f) : ∃ q ∈ s, p ∣ f q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty] at hdiv
      exact False.elim (hp.not_dvd_one hdiv)
  | @insert q s hqs ih =>
      rw [Finset.prod_insert hqs] at hdiv
      rcases hp.dvd_mul.mp hdiv with hqdiv | hrest
      · exact ⟨q, Finset.mem_insert_self q s, hqdiv⟩
      · obtain ⟨r, hrs, hrdiv⟩ := ih hrest
        exact ⟨r, Finset.mem_insert_of_mem hrs, hrdiv⟩

lemma prime_dvd_markedPart_mem {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p h : ℕ}
    (hp : p.Prime) (hdiv : p ∣ markedPart x K a h) :
    p ∈ markedPrimes x K a := by
  unfold markedPart at hdiv
  change p ∣ (markedPrimes x K a).prod (fun q : ℕ => q ^ padicValNat q h) at hdiv
  obtain ⟨q, hqmem, hqdiv⟩ :=
    prime_dvd_finset_prod hp (markedPrimes x K a) (fun q => q ^ padicValNat q h) hdiv
  have hqprime := prime_of_mem_markedPrimes hqmem
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hqdiv
  have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  simpa [hpqeq] using hqmem

lemma band_prime_scale_bounds {x a : ℝ} {p : ℕ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha₀ : 1 / 10 < a) (ha₁ : a < 1 / 5)
    (hp : p ∈ primeBand x a) :
    4 < (p : ℝ) ∧ (p : ℝ) < Real.rpow x (9 / 10 : ℝ) := by
  have hLpos : 0 < Real.log x := by
    have : 0 < (4 : ℝ) ^ 10 := by positivity
    linarith
  have hx1 : 1 < x := (Real.log_pos_iff hxpos.le).mp hLpos
  have hL1 : 1 ≤ Real.log x := by
    have : (1 : ℝ) ≤ (4 : ℝ) ^ 10 := by norm_num
    linarith
  have hL16 : 16 ≤ Real.log x := by
    have : (16 : ℝ) ≤ (4 : ℝ) ^ 10 := by norm_num
    linarith
  have hrootBase : (4 : ℝ) ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) := by
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 10) hL
      (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
    have hroot : ((4 : ℝ) ^ 10) ^ (1 / 10 : ℝ) = 4 := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow (4 : ℝ) 10]
      calc
        _ = Real.exp (Real.log 4) := by congr 1 <;> ring
        _ = 4 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    calc
      4 = Real.rpow ((4 : ℝ) ^ 10) (1 / 10 : ℝ) := hroot.symm
      _ ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) := hpow
  have hExp4 : 4 < Real.exp 4 := by
    have hh := Real.add_one_le_exp (4 : ℝ)
    norm_num at hh ⊢
    linarith
  have hsmallExp : 4 < Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
    lt_of_lt_of_le hExp4 (Real.exp_le_exp.mpr hrootBase)
  have hrootCmp : Real.rpow (Real.log x) (1 / 5 : ℝ) ≤ Real.sqrt (Real.log x) := by
    calc
      Real.rpow (Real.log x) (1 / 5 : ℝ) ≤
          Real.rpow (Real.log x) (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.sqrt (Real.log x) := (Real.sqrt_eq_rpow _).symm
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.log x / 4 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hLpos' : 0 < Real.log x := hLpos
      have hmul := mul_le_mul_of_nonneg_left hL16 (le_of_lt hLpos')
      nlinarith
  have hExpCmp : 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) <
      (9 / 10 : ℝ) * Real.log x := by
    calc
      2 * Real.rpow (Real.log x) (1 / 5 : ℝ) ≤ 2 * Real.sqrt (Real.log x) :=
        mul_le_mul_of_nonneg_left hrootCmp (by norm_num)
      _ ≤ 2 * (Real.log x / 4) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ < (9 / 10 : ℝ) * Real.log x := by nlinarith [hLpos]
  have hExpUpper : Real.exp (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) <
      Real.rpow x (9 / 10 : ℝ) := by
    have hexp := Real.exp_lt_exp.mpr hExpCmp
    calc
      _ < Real.exp ((9 / 10 : ℝ) * Real.log x) := hexp
      _ = Real.rpow x (9 / 10 : ℝ) := by
        have hdef : Real.rpow x (9 / 10 : ℝ) =
            Real.exp ((9 / 10 : ℝ) * Real.log x) := by
          simpa [mul_comm] using Real.rpow_def_of_pos hxpos (9 / 10 : ℝ)
        exact hdef.symm
  rcases Finset.mem_filter.mp hp with ⟨_, hpband⟩
  rcases hpband with ⟨hpPrime, hplow, hpup⟩
  have hlow : Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤
      Real.exp (Real.rpow (Real.log x) a) := by
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow_of_exponent_le hL1 ha₀.le
  have hupow : Real.rpow (Real.log x) a ≤
      Real.rpow (Real.log x) (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 ha₁.le
  constructor
  · exact lt_of_lt_of_le hsmallExp (le_trans hlow hplow)
  · calc
      (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) a) := hpup
      _ ≤ Real.exp (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        gcongr
      _ < Real.rpow x (9 / 10 : ℝ) := hExpUpper

lemma markedPrime_scale_bounds {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : ℕ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (ha : ValidBands K a)
    (hp : p ∈ markedPrimes x K a) :
    4 < (p : ℝ) ∧ (p : ℝ) < Real.rpow x (9 / 10 : ℝ) := by
  simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
  obtain ⟨i, hpi⟩ := hp
  exact band_prime_scale_bounds hxpos hL (ha.2.1 i).1 (ha.2.1 i).2 hpi

lemma markedWeight_eq_of_prime_dvd_iff {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {q : ℝ} {h r : ℕ}
    (hdvd : ∀ p, p ∈ markedPrimes x K a → p.Prime → (p ∣ h ↔ p ∣ r)) :
    markedWeight x K a q h = markedWeight x K a q r := by
  have hband (i : Fin K) : bandOmega x (a i) h = bandOmega x (a i) r := by
    unfold bandOmega
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hph⟩
      have hpmem : p ∈ markedPrimes x K a := by
        simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hp⟩
      exact ⟨hp, (hdvd p hpmem (prime_of_mem_markedPrimes hpmem)).mp hph⟩
    · rintro ⟨hp, hpr⟩
      have hpmem : p ∈ markedPrimes x K a := by
        simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hp⟩
      exact ⟨hp, (hdvd p hpmem (prime_of_mem_markedPrimes hpmem)).mpr hpr⟩
  have hmarked : markedOmega x K a h = markedOmega x K a r := by
    unfold markedOmega
    apply Finset.sum_congr rfl
    intro i hi
    exact hband i
  have hmeet : (∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ h) ↔
      (∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ r) := by
    constructor
    · intro hh i
      obtain ⟨p, hp, hph⟩ := hh i
      have hpmem : p ∈ markedPrimes x K a := by
        simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hp⟩
      exact ⟨p, hp, (hdvd p hpmem (prime_of_mem_markedPrimes hpmem)).mp hph⟩
    · intro hr i
      obtain ⟨p, hp, hpr⟩ := hr i
      have hpmem : p ∈ markedPrimes x K a := by
        simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hp⟩
      exact ⟨p, hp, (hdvd p hpmem (prime_of_mem_markedPrimes hpmem)).mpr hpr⟩
  simp only [markedWeight, hmeet, hmarked]
  simp_rw [hband]

lemma markedWeight_nonneg_le {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {h : ℕ}
    (hmass : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass x (a i)) :
    0 ≤ markedWeight x K a (1 / 2 : ℝ) h ∧
      markedWeight x K a (1 / 2 : ℝ) h ≤ (4 / Real.log 2) ^ K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 < Real.log 2 / 2 := by positivity
  have hC : 0 < (2 : ℝ) / Real.log 2 := by positivity
  let n : Fin K → ℕ := fun i => bandOmega x (a i) h
  let s : ℕ := ∑ i : Fin K, n i
  let e : ℕ := s - K
  by_cases hcond : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ h
  · have hn : ∀ i : Fin K, 1 ≤ n i := by
      intro i
      obtain ⟨p, hp, hph⟩ := hcond i
      have hp' : p ∈ (primeBand x (a i)).filter (fun q => q ∣ h) :=
        Finset.mem_filter.mpr ⟨hp, hph⟩
      have hcard : 0 < ((primeBand x (a i)).filter (fun q => q ∣ h)).card :=
        Finset.card_pos.mpr ⟨p, hp'⟩
      exact Nat.succ_le_iff.mpr (by simpa [n, bandOmega] using hcard)
    have hsumLower : K ≤ s := by
      calc
        K = ∑ i : Fin K, 1 := by simp
        _ ≤ ∑ i : Fin K, n i := Finset.sum_le_sum (fun i hi => hn i)
    have hsum : s = e + K := by
      dsimp [e]
      exact (Nat.sub_add_cancel hsumLower).symm
    have heq : s - K = e := rfl
    have hmarked : markedOmega x K a h = s := by simp [s, n, markedOmega]
    have hweight : markedWeight x K a (1 / 2 : ℝ) h =
        (1 / 2 : ℝ) ^ e * ∏ i : Fin K, (n i : ℝ) / bandMass x (a i) := by
      simp only [markedWeight, if_pos hcond, hmarked, heq, n]
    have hmassPos (i : Fin K) : 0 < bandMass x (a i) :=
      lt_of_lt_of_le hbase (hmass i)
    have hfactor : ∀ i : Fin K,
        (n i : ℝ) / bandMass x (a i) ≤
          ((2 : ℝ) / Real.log 2) * (2 : ℝ) ^ n i := by
      intro i
      have hiMass : 0 < bandMass x (a i) := hmassPos i
      have hinv : 1 / bandMass x (a i) ≤ (2 : ℝ) / Real.log 2 := by
        calc
          _ ≤ 1 / (Real.log 2 / 2) := one_div_le_one_div_of_le hbase (hmass i)
          _ = (2 : ℝ) / Real.log 2 := by field_simp
      have hnNat : n i ≤ 2 ^ n i := (Nat.lt_two_pow_self (n := n i)).le
      have hnReal : (n i : ℝ) ≤ (2 : ℝ) ^ n i := by exact_mod_cast hnNat
      calc
        (n i : ℝ) / bandMass x (a i) =
            (n i : ℝ) * (1 / bandMass x (a i)) := by ring
        _ ≤ ((2 : ℝ) ^ n i) * (1 / bandMass x (a i)) :=
          mul_le_mul_of_nonneg_right hnReal (by positivity)
        _ ≤ ((2 : ℝ) ^ n i) * ((2 : ℝ) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = ((2 : ℝ) / Real.log 2) * (2 : ℝ) ^ n i := by ring
    have hprod :
        (∏ i : Fin K, (n i : ℝ) / bandMass x (a i)) ≤
          ((2 : ℝ) / Real.log 2) ^ K * (2 : ℝ) ^ s := by
      have hconst : (∏ i : Fin K, (2 : ℝ) / Real.log 2) =
          ((2 : ℝ) / Real.log 2) ^ K := by
        simpa using (Finset.prod_const (s := (Finset.univ : Finset (Fin K)))
          (2 / Real.log 2 : ℝ))
      have hprodPow : (∏ i : Fin K, (2 : ℝ) ^ n i) =
          (2 : ℝ) ^ (∑ i : Fin K, n i) := by
        simpa using Finset.prod_pow_eq_pow_sum
          (Finset.univ : Finset (Fin K)) n (2 : ℝ)
      calc
        _ ≤ ∏ i : Fin K, ((2 : ℝ) / Real.log 2) * (2 : ℝ) ^ n i := by
          exact Finset.prod_le_prod₀
            (fun i hi => div_nonneg (Nat.cast_nonneg _) (le_of_lt (hmassPos i)))
            (fun i hi => hfactor i)
        _ = (∏ i : Fin K, (2 : ℝ) / Real.log 2) *
              (∏ i : Fin K, (2 : ℝ) ^ n i) := Finset.prod_mul_distrib
        _ = (∏ i : Fin K, (2 : ℝ) / Real.log 2) *
              (2 : ℝ) ^ (∑ i : Fin K, n i) := by rw [hprodPow]
        _ = ((2 : ℝ) / Real.log 2) ^ K * (2 : ℝ) ^ s := by rw [hconst]
    have hcancel : (1 / 2 : ℝ) ^ e * (2 : ℝ) ^ e = 1 := by
      rw [← mul_pow]
      norm_num
    have hpow :
        (1 / 2 : ℝ) ^ e *
            (((2 : ℝ) / Real.log 2) ^ K * (2 : ℝ) ^ (e + K)) =
          (4 / Real.log 2) ^ K := by
      rw [pow_add]
      calc
        _ = ((2 : ℝ) / Real.log 2) ^ K *
              (((1 / 2 : ℝ) ^ e * (2 : ℝ) ^ e) * (2 : ℝ) ^ K) := by ring
        _ = ((2 : ℝ) / Real.log 2) ^ K * (2 : ℝ) ^ K := by rw [hcancel]; ring
        _ = (((2 : ℝ) / Real.log 2) * 2) ^ K := by rw [← mul_pow]
        _ = (4 / Real.log 2) ^ K := by congr 1 <;> field_simp <;> ring
    rw [hweight]
    constructor
    · apply mul_nonneg
      · exact pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) e
      · apply Finset.prod_nonneg
        intro i hi
        exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hmassPos i))
    · calc
        _ ≤ (1 / 2 : ℝ) ^ e *
            (((2 : ℝ) / Real.log 2) ^ K * (2 : ℝ) ^ s) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (4 / Real.log 2) ^ K := by simpa [hsum] using hpow
  · constructor
    · simp only [markedWeight, if_neg hcond]
      exact le_rfl
    · simp only [markedWeight, if_neg hcond]
      exact pow_nonneg (by positivity : 0 ≤ (4 / Real.log 2 : ℝ)) K

lemma bandMass_lower_all {K : ℕ} {a : Fin K → ℝ} (ha : ValidBands K a) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ i : Fin K,
      Real.log 2 / 2 ≤ bandMass x (a i) := by
  have heach : ∀ i : Fin K, ∃ Xi : ℝ, 2 ≤ Xi ∧
      ∀ x : ℝ, Xi ≤ x → Real.log 2 / 2 ≤ bandMass x (a i) := by
    intro i
    have hai₀ := (ha.2.1 i).1
    have hai₁ := (ha.2.1 i).2
    obtain ⟨Xi, hXi, hband⟩ := band_mass (a i) (by linarith) (by linarith)
      (Real.log 2 / 2) (by positivity)
    refine ⟨Xi, hXi, ?_⟩
    intro x hx
    have habs := abs_le.mp (hband x hx).1
    linarith
  choose Xi hXi using heach
  let X := 2 + ∑ i : Fin K, Xi i
  have hsum_nonneg : 0 ≤ ∑ i : Fin K, Xi i :=
    Finset.sum_nonneg (fun i _ => le_trans (by norm_num) (hXi i).1)
  refine ⟨X, by dsimp [X]; linarith, ?_⟩
  intro x hx i
  have hXi_le : Xi i ≤ ∑ j : Fin K, Xi j :=
    Finset.single_le_sum (fun j _ => le_trans (by norm_num) (hXi j).1) (Finset.mem_univ i)
  apply (hXi i).2 x
  dsimp [X] at hx
  linarith

lemma conFactor_mul_marked {x : ℝ} {c K : ℕ} {a : Fin K → ℝ} {p h : ℕ}
    (hc : c ≠ 0) (hpmem : p ∈ markedPrimes x K a) (hp : p.Prime) :
    conFactor x c K a (p * h) = conFactor x c K a h := by
  classical
  by_cases hh : h = 0
  · subst h
    have hmark0 : markedPart x K a 0 = 1 := by simp [markedPart]
    have hno : ¬ ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
        0 = c * markedPart x K a 0 * Q := by
      rintro ⟨Q, hQ, _, hEq⟩
      rw [hmark0] at hEq
      have hpos : 0 < c * 1 * Q := by
        simpa using Nat.mul_pos (Nat.pos_of_ne_zero hc) hQ.pos
      exact (Nat.ne_of_gt hpos) hEq.symm
    simp [conFactor, hmark0, hno]
  · have hph : p * h ≠ 0 := Nat.mul_ne_zero hp.ne_zero hh
    have hmark := markedPart_mul_of_mem hpmem hp hh
    let P := fun n : ℕ => ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
      n = c * markedPart x K a n * Q
    have hP : P (p * h) ↔ P h := by
      dsimp [P]
      rw [hmark]
      constructor
      · rintro ⟨Q, hQ, hQlarge, hEq⟩
        refine ⟨Q, hQ, hQlarge, ?_⟩
        have heq : p * h = p * (c * markedPart x K a h * Q) := by
          calc
            p * h = c * (p * markedPart x K a h) * Q := hEq
            _ = p * (c * markedPart x K a h * Q) := by ring
        exact Nat.mul_left_cancel hp.pos heq
      · rintro ⟨Q, hQ, hQlarge, hEq⟩
        refine ⟨Q, hQ, hQlarge, ?_⟩
        calc
          p * h = p * (c * markedPart x K a h * Q) := congrArg (Nat.mul p) hEq
          _ = c * (p * markedPart x K a h) * Q := by ring
    change (if P (p * h) then 1 else 0) = (if P h then 1 else 0)
    by_cases he : P h
    · simp [he, hP.mpr he]
    · have hne : ¬P (p * h) := fun hhP => he (hP.mp hhP)
      simp [he, hne]

lemma exists_dyadic_scale_index {x κ : ℝ} {m : ℕ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (hκ0 : 0 < κ) (hκ1 : κ < 1 / 100)
    (hmlow : Real.rpow x (1 / 2 - κ) < (m : ℝ))
    (hmhigh : (m : ℝ) < 2 * Real.rpow x (1 / 2 + κ)) :
    ∃ i : ℕ, i < ⌊4 * κ * Real.log x⌋₊ + 4 ∧
      Real.rpow x (1 / 2 - κ) / 2 * (2 : ℝ) ^ i ≤ (m : ℝ) ∧
      (m : ℝ) < 2 * (Real.rpow x (1 / 2 - κ) / 2 * (2 : ℝ) ^ i) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLpos : 0 < Real.log x := by
    have h4 : 0 < (4 : ℝ) ^ 10 := by positivity
    linarith
  have hLone : 1 ≤ Real.log x := by
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ 10 := by norm_num
    linarith
  have hαpos : 0 < 1 / 2 - κ := by linarith
  have hH0 : 0 < Real.rpow x (1 / 2 - κ) / 2 := by
    exact div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num)
  let H0 := Real.rpow x (1 / 2 - κ) / 2
  let t := (m : ℝ) / H0
  have htpos : 0 < t := by
    dsimp [t, H0]
    exact div_pos (lt_trans (Real.rpow_pos_of_pos hxpos _) hmlow) hH0
  have htlarge : 1 < t := by
    have hH0m : H0 < (m : ℝ) := by
      have hWpos : 0 < Real.rpow x (1 / 2 - κ) := Real.rpow_pos_of_pos hxpos _
      have hhalf : Real.rpow x (1 / 2 - κ) / 2 < Real.rpow x (1 / 2 - κ) :=
        div_lt_self hWpos (by norm_num : (1 : ℝ) < 2)
      exact hhalf.trans hmlow
    exact (lt_div_iff₀ hH0).2 (by simpa [t, H0] using hH0m)
  have hratio : Real.rpow x (1 / 2 + κ) /
      Real.rpow x (1 / 2 - κ) = Real.rpow x (2 * κ) := by
    have hβ : Real.rpow x (1 / 2 + κ) = Real.exp (Real.log x * (1 / 2 + κ)) := by
      simpa [mul_comm] using Real.rpow_def_of_pos hxpos (1 / 2 + κ)
    have hα : Real.rpow x (1 / 2 - κ) = Real.exp (Real.log x * (1 / 2 - κ)) := by
      simpa [mul_comm] using Real.rpow_def_of_pos hxpos (1 / 2 - κ)
    have hγ : Real.rpow x (2 * κ) = Real.exp (Real.log x * (2 * κ)) := by
      simpa [mul_comm] using Real.rpow_def_of_pos hxpos (2 * κ)
    rw [hβ, hα, hγ, ← Real.exp_sub]
    congr 1
    ring
  have htm : t < 4 * Real.rpow x (2 * κ) := by
    dsimp [t, H0]
    calc
      (m : ℝ) / (Real.rpow x (1 / 2 - κ) / 2) <
          (2 * Real.rpow x (1 / 2 + κ)) / (Real.rpow x (1 / 2 - κ) / 2) :=
        div_lt_div_of_pos_right hmhigh (by positivity)
      _ = 4 * (Real.rpow x (1 / 2 + κ) / Real.rpow x (1 / 2 - κ)) := by ring
      _ = 4 * Real.rpow x (2 * κ) := by rw [hratio]
  have hlogt : Real.log t < Real.log 4 + 2 * κ * Real.log x := by
    have hloglt := Real.log_lt_log htpos htm
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hmul : Real.log (4 * Real.rpow x (2 * κ)) =
        Real.log 4 + 2 * κ * Real.log x := by
      have hlogpow : Real.log (Real.rpow x (2 * κ)) = 2 * κ * Real.log x := by
        simpa using Real.log_rpow hxpos (2 * κ)
      calc
        Real.log (4 * Real.rpow x (2 * κ)) =
            Real.log 4 + Real.log (Real.rpow x (2 * κ)) :=
              Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
                (ne_of_gt (Real.rpow_pos_of_pos hxpos _))
        _ = Real.log 4 + 2 * κ * Real.log x := by rw [hlogpow]
    rw [hmul] at hloglt
    exact hloglt
  let v := Real.log t / Real.log 2
  have hvpos : 0 < v := div_pos (Real.log_pos htlarge) hlog2
  have hvupper : v < 2 + 4 * κ * Real.log x := by
    have hdiv := div_lt_div_of_pos_right hlogt hlog2
    have hratioInv : 1 / Real.log 2 ≤ 2 := by
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlog2half
      norm_num at hh ⊢
      linarith
    have hterm : 2 * κ * Real.log x / Real.log 2 ≤ 4 * κ * Real.log x := by
      have hnonneg : 0 ≤ 2 * κ * Real.log x := by positivity
      calc
        _ = (2 * κ * Real.log x) * (1 / Real.log 2) := by ring
        _ ≤ (2 * κ * Real.log x) * 2 := mul_le_mul_of_nonneg_left hratioInv hnonneg
        _ = 4 * κ * Real.log x := by ring
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    dsimp [v]
    rw [hlog4] at hdiv
    calc
      _ < (2 * Real.log 2 + 2 * κ * Real.log x) / Real.log 2 := hdiv
      _ = 2 + 2 * κ * Real.log x / Real.log 2 := by field_simp
      _ ≤ 2 + 4 * κ * Real.log x := by linarith [hterm]
  let i := ⌊v⌋₊
  have hiLo : (i : ℝ) ≤ v := Nat.floor_le (le_of_lt hvpos)
  have hiHi : v < (i : ℝ) + 1 := Nat.lt_floor_add_one v
  have hlogLo : (i : ℝ) * Real.log 2 ≤ Real.log t := by
    have := mul_le_mul_of_nonneg_right hiLo hlog2.le
    dsimp [v] at this
    have hmul : (Real.log t / Real.log 2) * Real.log 2 = Real.log t := by
      field_simp
    linarith
  have hlogHi : Real.log t < ((i : ℝ) + 1) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hiHi hlog2
    dsimp [v] at this
    have hmul : (Real.log t / Real.log 2) * Real.log 2 = Real.log t := by
      field_simp
    nlinarith
  have hexpPow (n : ℕ) : Real.exp (Real.log 2 * (n : ℝ)) = (2 : ℝ) ^ n := by
    rw [show Real.log 2 * (n : ℝ) = (n : ℝ) * Real.log 2 by ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hpowLo : (2 : ℝ) ^ i ≤ t := by
    have hlogLo' : Real.log 2 * (i : ℝ) ≤ Real.log t := by
      simpa [mul_comm] using hlogLo
    calc
      (2 : ℝ) ^ i = Real.exp (Real.log 2 * (i : ℝ)) := (hexpPow i).symm
      _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr hlogLo'
      _ = t := Real.exp_log htpos
  have hpowHi : t < 2 * (2 : ℝ) ^ i := by
    have hrewrite : Real.exp (((i : ℝ) + 1) * Real.log 2) =
        2 * (2 : ℝ) ^ i := by
      have hiExp := hexpPow (i + 1)
      have harg : ((i : ℝ) + 1) * Real.log 2 = Real.log 2 * ((i + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [harg, hiExp]
      rw [pow_succ]
      ring
    calc
      t = Real.exp (Real.log t) := (Real.exp_log htpos).symm
      _ < Real.exp (((i : ℝ) + 1) * Real.log 2) := Real.exp_lt_exp.mpr hlogHi
      _ = 2 * (2 : ℝ) ^ i := hrewrite
  have hIreal : (i : ℝ) < (⌊4 * κ * Real.log x⌋₊ + 4 : ℕ) := by
    have hfloor : 4 * κ * Real.log x < (⌊4 * κ * Real.log x⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hi : (i : ℝ) < 2 + 4 * κ * Real.log x := lt_of_le_of_lt hiLo hvupper
    calc
      (i : ℝ) < 2 + 4 * κ * Real.log x := hi
      _ < (⌊4 * κ * Real.log x⌋₊ : ℝ) + 4 := by linarith
      _ = (⌊4 * κ * Real.log x⌋₊ + 4 : ℕ) := by norm_num
  have hI : i < ⌊4 * κ * Real.log x⌋₊ + 4 := by exact_mod_cast hIreal
  have hlo : H0 * (2 : ℝ) ^ i ≤ (m : ℝ) := by
    have := (le_div_iff₀ hH0).mp hpowLo
    dsimp [t] at this
    simpa [H0, mul_comm] using this
  have hhi : (m : ℝ) < 2 * (H0 * (2 : ℝ) ^ i) := by
    have := (div_lt_iff₀ hH0).mp hpowHi
    dsimp [t] at this
    calc
      (m : ℝ) < (2 * (2 : ℝ) ^ i) * H0 := this
      _ = 2 * (H0 * (2 : ℝ) ^ i) := by ring
  exact ⟨i, hI, by simpa [H0] using hlo, by simpa [H0] using hhi⟩

lemma rough_cutoff_cube_gt {x κ : ℝ} (hxpos : 0 < x)
    (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (hκ : κ < 1 / 100) :
    2 * x < Real.rpow x (1 / 2 - κ) ^ 3 := by
  have hLpos : 0 < Real.log x := by
    have h4 : 0 < (4 : ℝ) ^ 10 := by positivity
    linarith
  have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans_le (by norm_num)
  have hκL : κ * Real.log x < (1 / 100 : ℝ) * Real.log x :=
    mul_lt_mul_of_pos_right hκ hLpos
  have hExpCmp : Real.log 2 + Real.log x <
      3 * (Real.log x * (1 / 2 - κ)) := by
    nlinarith [hκL, hL]
  have htwox : 2 * x = Real.exp (Real.log 2 + Real.log x) := by
    calc
      2 * x = Real.exp (Real.log 2) * Real.exp (Real.log x) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hxpos]
      _ = Real.exp (Real.log 2 + Real.log x) := by rw [Real.exp_add]
  have hWcube : Real.rpow x (1 / 2 - κ) ^ 3 =
      Real.exp (3 * (Real.log x * (1 / 2 - κ))) := by
    have hdef : Real.rpow x (1 / 2 - κ) =
        Real.exp (Real.log x * (1 / 2 - κ)) := by
      simpa using Real.rpow_def_of_pos hxpos (1 / 2 - κ)
    calc
      Real.rpow x (1 / 2 - κ) ^ 3 =
          (Real.exp (Real.log x * (1 / 2 - κ))) ^ 3 := by rw [hdef]
      _ = Real.exp (3 * (Real.log x * (1 / 2 - κ))) :=
        (Real.exp_nat_mul (Real.log x * (1 / 2 - κ)) 3).symm
  calc
    2 * x = Real.exp (Real.log 2 + Real.log x) := htwox
    _ < Real.exp (3 * (Real.log x * (1 / 2 - κ))) := Real.exp_lt_exp.mpr hExpCmp
    _ = Real.rpow x (1 / 2 - κ) ^ 3 := hWcube.symm

lemma exists_rough_semiprime_factorization {x W : ℝ} {d : ℕ}
    (hx1 : 1 < x) (hdlo : x < (d : ℝ)) (hdhi : (d : ℝ) < 2 * x)
    (hrough : ∀ p, p.Prime → p ∣ d → W < (p : ℝ))
    (hcomp : ¬ d.Prime) (hWpos : 0 < W) (hWcube : 2 * x < W ^ 3) :
    ∃ m n : ℕ, m.Prime ∧ n.Prime ∧ d = m * n ∧
      W < (m : ℝ) ∧ W < (n : ℝ) := by
  have hdgt1 : 1 < d := by
    have : 1 < (d : ℝ) := lt_trans hx1 hdlo
    exact_mod_cast this
  obtain ⟨m, hm, hmdvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  let q := d / m
  have hmq : m * q = d := by
    dsimp [q]
    exact Nat.mul_div_cancel' hmdvd
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hn
    have hmq0 : m * 0 = d := by simpa [q, hqzero] using hmq
    simp at hmq0
    omega
  have hqne1 : q ≠ 1 := by
    intro hq
    have hdEq : d = m := by
      have hmq' : m * 1 = d := by simpa [q, hq] using hmq
      simpa using hmq'.symm
    exact hcomp (by simpa [hdEq] using hm)
  have hqd : q ∣ d := by
    rw [← hmq]
    exact dvd_mul_of_dvd_right (dvd_refl q) m
  have hqPrime : q.Prime := by
    by_contra hqnot
    obtain ⟨p₂, hp₂, hp₂q⟩ := Nat.exists_prime_and_dvd hqne1
    let s := q / p₂
    have hp₂s : p₂ * s = q := Nat.mul_div_cancel' hp₂q
    have hspos : 0 < s := by
      by_contra hs
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
      rw [hs0, Nat.mul_zero] at hp₂s
      omega
    have hsne1 : s ≠ 1 := by
      intro hs
      have hqEq : q = p₂ := by
        have hp₂s' : p₂ * 1 = q := by simpa [s, hs] using hp₂s
        simpa using hp₂s'.symm
      exact hqnot (by simpa [hqEq] using hp₂)
    obtain ⟨p₃, hp₃, hp₃s⟩ := Nat.exists_prime_and_dvd hsne1
    have hsq : s ∣ q := by
      rw [← hp₂s]
      exact dvd_mul_of_dvd_right (dvd_refl s) p₂
    have hp₂d : p₂ ∣ d := dvd_trans hp₂q hqd
    have hp₃d : p₃ ∣ d := dvd_trans hp₃s (dvd_trans hsq hqd)
    have hmW := hrough m hm hmdvd
    have hp₂W := hrough p₂ hp₂ hp₂d
    have hp₃W := hrough p₃ hp₃ hp₃d
    have hsp₃ : p₃ ≤ s := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_of_gt hspos)) hp₃s
    have hfac : d = m * p₂ * s := by
      calc
        d = m * q := hmq.symm
        _ = m * (p₂ * s) := by rw [hp₂s]
        _ = m * p₂ * s := by ring
    have hprod : W ^ 3 < (d : ℝ) := by
      have hmW' : W ≤ (m : ℝ) := hmW.le
      have hp₂W' : W ≤ (p₂ : ℝ) := hp₂W.le
      have hp₃W' : W ≤ (p₃ : ℝ) := hp₃W.le
      have hs' : (p₃ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsp₃
      calc
        W ^ 3 = W * W * W := by ring
        _ < (m : ℝ) * W * W := by gcongr
        _ ≤ (m : ℝ) * (p₂ : ℝ) * W := by gcongr
        _ ≤ (m : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) := by gcongr
        _ ≤ (m : ℝ) * (p₂ : ℝ) * (s : ℝ) := by gcongr
        _ = (d : ℝ) := by exact_mod_cast hfac.symm
    exact (not_lt_of_ge hdhi.le) (lt_trans hWcube hprod)
  have hqrough := hrough q hqPrime hqd
  exact ⟨m, q, hm, hqPrime, hmq.symm, hrough m hm hmdvd, hqrough⟩

lemma mem_dyadicIntegers_of_bounds {H : ℝ} {n : ℕ}
    (hlo : H ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * H) :
    n ∈ dyadicIntegers H := by
  unfold dyadicIntegers
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.le_floor hhi
  · exact ⟨hlo, hhi⟩

end ArtinPrimitiveRoots.Construction
