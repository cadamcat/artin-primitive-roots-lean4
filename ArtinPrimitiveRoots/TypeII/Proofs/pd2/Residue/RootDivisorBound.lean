import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

private lemma pd2r_one_add_mul_le_pow (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + (n : ℝ) * t ≤ (1 + t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
      calc
        1 + ((n + 1 : ℕ) : ℝ) * t = 1 + (n : ℝ) * t + t := by simp [Nat.cast_add]; ring
        _ ≤ (1 + (n : ℝ) * t) * (1 + t) := by nlinarith [mul_nonneg hn ht]
        _ ≤ (1 + t) ^ n * (1 + t) := by gcongr
        _ = (1 + t) ^ (n + 1) := by rw [pow_succ]

private lemma pd2r_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        n + 1 + 1 ≤ (n + 1) + (n + 1) := by omega
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

private noncomputable def pd2r_divisorLocalConstant (η : ℝ) (P p : ℕ) : ℝ :=
  if 2 ≤ p ∧ p ≤ P then 1 + 2 / ((p : ℝ) ^ η - 1) else 1

private lemma pd2r_divisor_local_factor_bound (η : ℝ) (hη : 0 < η) (P : ℕ)
    (hP : 2 ≤ (P : ℝ) ^ η) {p e : ℕ} (hp : 2 ≤ p) :
    ((e + 1 : ℕ) : ℝ) ≤ pd2r_divisorLocalConstant η P p *
      (p : ℝ) ^ (η * (e : ℝ)) := by
  by_cases hsmall : p ≤ P
  · have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have ht : 0 < (p : ℝ) ^ η - 1 := sub_pos.mpr (Real.one_lt_rpow hp1 hη)
    have hbern := pd2r_one_add_mul_le_pow ((p : ℝ) ^ η - 1) (le_of_lt ht) e
    have hpow : (p : ℝ) ^ (η * (e : ℝ)) = ((p : ℝ) ^ η) ^ e :=
      Real.rpow_mul_natCast (by positivity) η e
    have hmain : 1 + (e : ℝ) * ((p : ℝ) ^ η - 1) ≤
        (p : ℝ) ^ (η * (e : ℝ)) := by simpa [hpow] using hbern
    have hCpos : 0 < 1 + 2 / ((p : ℝ) ^ η - 1) := by positivity
    have hnum : (e : ℝ) + 1 ≤
        (1 + 2 / ((p : ℝ) ^ η - 1)) *
          (1 + (e : ℝ) * ((p : ℝ) ^ η - 1)) := by
      by_cases he : e = 0
      · subst e
        have ht' : 0 ≤ 2 / ((p : ℝ) ^ η - 1) := le_of_lt (by positivity)
        nlinarith
      · have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
        have heR : 1 ≤ (e : ℝ) := by exact_mod_cast he1
        have htwo : 2 / ((p : ℝ) ^ η - 1) ≤
            1 + 2 / ((p : ℝ) ^ η - 1) := by linarith
        have heterm : (e : ℝ) + 1 ≤ 2 * (e : ℝ) := by nlinarith
        have hmul : 2 * (e : ℝ) =
            (2 / ((p : ℝ) ^ η - 1)) * ((e : ℝ) * ((p : ℝ) ^ η - 1)) := by
          field_simp [ne_of_gt ht]
        have hle := mul_le_mul htwo
          (show (e : ℝ) * ((p : ℝ) ^ η - 1) ≤
            1 + (e : ℝ) * ((p : ℝ) ^ η - 1) by linarith)
          (by positivity) (by positivity)
        rw [← hmul] at hle
        exact heterm.trans hle
    unfold pd2r_divisorLocalConstant
    rw [if_pos ⟨hp, hsmall⟩]
    calc
      ((e + 1 : ℕ) : ℝ) ≤
          (1 + 2 / ((p : ℝ) ^ η - 1)) *
            (1 + (e : ℝ) * ((p : ℝ) ^ η - 1)) := by exact_mod_cast hnum
      _ ≤ (1 + 2 / ((p : ℝ) ^ η - 1)) * (p : ℝ) ^ (η * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hCpos)
  · have hpP : (P : ℝ) ≤ p := by
      have hpPnat : P ≤ p := by omega
      exact_mod_cast hpPnat
    have hpη : 2 ≤ (p : ℝ) ^ η := by
      calc
        2 ≤ (P : ℝ) ^ η := hP
        _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hpP hη.le
    have htwo : ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by
      exact_mod_cast pd2r_succ_le_two_pow e
    have hpowbase : (2 : ℝ) ^ e ≤ ((p : ℝ) ^ η) ^ e := by gcongr
    have hpow : ((p : ℝ) ^ η) ^ e = (p : ℝ) ^ (η * (e : ℝ)) :=
      (Real.rpow_mul_natCast (by positivity) η e).symm
    simpa [pd2r_divisorLocalConstant, hsmall, hpow] using htwo.trans hpowbase

theorem pd2r_divisor_card_rpow_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ η := by
  classical
  let P : ℕ := Nat.ceil ((2 : ℝ) ^ η⁻¹)
  let localC : ℕ → ℝ := pd2r_divisorLocalConstant η P
  let C : ℝ := ∏ p ∈ Finset.Icc 2 P, localC p
  have htarget : 1 < (2 : ℝ) ^ η⁻¹ := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hη)
  have hceil : (2 : ℝ) ^ η⁻¹ ≤ (P : ℝ) := by
    exact Nat.le_ceil ((2 : ℝ) ^ η⁻¹)
  have hPgt : 1 < P := by exact_mod_cast htarget.trans_le hceil
  have hP : 2 ≤ P := by omega
  have hPη : 2 ≤ (P : ℝ) ^ η := by
    calc
      2 = ((2 : ℝ) ^ η⁻¹) ^ η := by rw [Real.rpow_inv_rpow (by norm_num) hη.ne']
      _ ≤ (P : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hceil hη.le
  have hlocal1 : ∀ p, 1 ≤ localC p := by
    intro p
    by_cases hp2 : 2 ≤ p
    · by_cases hpP : p ≤ P
      · simp [localC, pd2r_divisorLocalConstant, hp2, hpP]
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
        have ht : 0 < (p : ℝ) ^ η - 1 := sub_pos.mpr (Real.one_lt_rpow hp1 hη)
        positivity
      · simp [localC, pd2r_divisorLocalConstant, hp2, hpP]
    · simp [localC, pd2r_divisorLocalConstant, hp2]
  have hCpos : 0 < C := Finset.prod_pos fun p hp =>
    lt_of_lt_of_le zero_lt_one (hlocal1 p)
  refine ⟨C, hCpos, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hcard : (m.divisors.card : ℝ) =
      ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.card_divisors hm0)
  have hlocal : ∀ p ∈ m.primeFactors,
      ((m.factorization p + 1 : ℕ) : ℝ) ≤
        localC p * (p : ℝ) ^ (η * (m.factorization p : ℝ)) := by
    intro p hp
    exact pd2r_divisor_local_factor_bound η hη P hPη
      ((Nat.prime_of_mem_primeFactors hp).two_le)
  have hprod := Finset.prod_le_prod₀
    (fun p hp => by positivity) hlocal
  have hpow : (∏ p ∈ m.primeFactors,
      (p : ℝ) ^ (η * (m.factorization p : ℝ))) = (m : ℝ) ^ η := by
    have hterm (p : ℕ) : (p : ℝ) ^ (η * (m.factorization p : ℝ)) =
        ((p : ℝ) ^ m.factorization p) ^ η := by
      rw [Real.rpow_mul_natCast (by positivity) η (m.factorization p)]
      exact Real.rpow_pow_comm (by positivity) η (m.factorization p)
    calc
      _ = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ η := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hterm p
      _ = (∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p) ^ η := by
        exact Real.finsetProd_rpow _ _ (by intro p hp; positivity) η
      _ = (m : ℝ) ^ η := by
        have hfac : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m :=
          Nat.prod_factorization_pow_eq_self hm0
        exact_mod_cast congrArg (fun z : ℕ => (z : ℝ) ^ η) hfac
  have hsmallProduct : (∏ p ∈ m.primeFactors, localC p) ≤ C := by
    let s := m.primeFactors.filter (fun p => p ≤ P)
    have heq : (∏ p ∈ m.primeFactors, localC p) = ∏ p ∈ s, localC p := by
      rw [show s = m.primeFactors.filter (fun p => p ≤ P) from rfl, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : p ≤ P <;> simp [localC, pd2r_divisorLocalConstant, h]
    rw [heq]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp'.1).two_le, hp'.2⟩
    · intro p hp
      exact le_trans zero_le_one (hlocal1 p)
    · intro p hp hnot
      exact hlocal1 p
  calc
    (m.divisors.card : ℝ) = ∏ p ∈ m.primeFactors,
        ((m.factorization p + 1 : ℕ) : ℝ) := hcard
    _ ≤ (∏ p ∈ m.primeFactors, localC p) *
        (∏ p ∈ m.primeFactors,
          (p : ℝ) ^ (η * (m.factorization p : ℝ))) := by
      calc
        _ ≤ ∏ p ∈ m.primeFactors,
            (localC p * (p : ℝ) ^ (η * (m.factorization p : ℝ))) := hprod
        _ = _ := Finset.prod_mul_distrib
    _ ≤ C * (m : ℝ) ^ η := by rw [hpow]; exact mul_le_mul hsmallProduct le_rfl (by positivity) (by positivity)

end ArtinPrimitiveRoots.TypeII.PD
