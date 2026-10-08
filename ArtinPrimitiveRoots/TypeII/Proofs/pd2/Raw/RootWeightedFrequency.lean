import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootFrequencyArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.MomentArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Proofs.pd0
set_option maxHeartbeats 1000000

lemma pd2a_multiples_interval (m d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 m).filter (fun n => d ∣ n)) = (Finset.Icc 1 (m / d)).image (fun j => d * j) := by
  ext n
  constructor
  · intro hn
    have hmem := Finset.mem_filter.mp hn
    have hb := Finset.mem_Icc.mp hmem.1
    have hpos : 0 < n := by omega
    have hqpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hpos hmem.2) hd
    exact Finset.mem_image.mpr ⟨n / d, Finset.mem_Icc.mpr ⟨hqpos, Nat.div_le_div_right hb.2⟩, Nat.mul_div_cancel' hmem.2⟩
  · rintro hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have hb := Finset.mem_Icc.mp hj
    have hjpos : 0 < j := by omega
    have hprod : d * j ≤ m := (Nat.mul_le_mul_left d hb.2).trans (by simpa [mul_comm] using Nat.div_mul_le_self m d)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨mul_pos hd hjpos, hprod⟩, dvd_mul_right d j⟩

lemma pd2a_multiple_harmonic_bound (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 m, if d ∣ n then 1 / (n : ℝ) else 0) ≤
      (1 / (d : ℝ)) * (1 + Real.log (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  rw [← Finset.sum_filter, pd2a_multiples_interval m d hd,
    Finset.sum_image (fun i hi j hj heq => Nat.mul_left_cancel hd heq)]
  have heq : (∑ j ∈ Finset.Icc 1 (m / d), 1 / ((d * j : ℕ) : ℝ)) =
      (1 / (d : ℝ)) * ∑ j ∈ Finset.Icc 1 (m / d), 1 / (j : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.cast_mul, one_div, mul_inv]
  rw [heq]
  by_cases hq : m / d = 0
  · simp [hq]
    positivity
  · have hqR : 0 < ((m / d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hharm : (∑ j ∈ Finset.Icc 1 (m / d), 1 / (j : ℝ)) ≤ 1 + Real.log ((m / d : ℕ) : ℝ) := by
      simpa only [positiveRange_eq_Icc, one_div] using harmonicRange_le_one_add_log (m / d)
    have hqle : ((m / d : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m d
    have hl : Real.log ((m / d : ℕ) : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hqR hqle
    exact mul_le_mul_of_nonneg_left (hharm.trans (by linarith)) (by positivity)

lemma pd2a_quarter_inverse_le_one (d : ℕ) (hd : 0 < d) :
    (d : ℝ) ^ (1 / 4 : ℝ) * (1 / (d : ℝ)) ≤ 1 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
  have heq : (d : ℝ) ^ (1 / 4 : ℝ) * (1 / (d : ℝ)) = (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
    calc
      _ = (d : ℝ) ^ (1 / 4 : ℝ) / (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
      _ = (d : ℝ) ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hdp _ _).symm
      _ = _ := by congr 1; norm_num
  rw [heq]
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hdR (by norm_num : (-(3 / 4 : ℝ)) ≤ 0)

lemma pd2a_weighted_gcd_harmonic (m u : ℕ) (hm : 0 < m) (hu : 0 < u) :
    (∑ n ∈ Finset.Icc 1 m, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ)) ≤
      (u.divisors.card : ℝ) * (1 + Real.log (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_nonneg hmR]
  have hpoint : ∀ n ∈ Finset.Icc 1 m,
      (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) ≤
        ∑ d ∈ u.divisors, if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0 := by
    intro n hn
    have hg : Nat.gcd n u ∈ u.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hu.ne'⟩
    have hG := Finset.single_le_sum (s := u.divisors)
      (f := fun d => if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0)
      (fun d hd => by split_ifs <;> positivity) hg
    simpa only [Nat.gcd_dvd_left, ite_true] using hG
  have hEach : ∀ d ∈ u.divisors,
      (∑ n ∈ Finset.Icc 1 m, if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0) ≤
        1 + Real.log (m : ℝ) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have heq : (∑ n ∈ Finset.Icc 1 m, if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0) =
      (d : ℝ) ^ (1 / 4 : ℝ) * ∑ n ∈ Finset.Icc 1 m, if d ∣ n then 1 / (n : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hdn : d ∣ n <;> simp [hdn, div_eq_mul_inv]
    rw [heq]
    calc
      _ ≤ (d : ℝ) ^ (1 / 4 : ℝ) * ((1 / (d : ℝ)) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul_of_nonneg_left (pd2a_multiple_harmonic_bound m d hm hdpos) (by positivity)
      _ = ((d : ℝ) ^ (1 / 4 : ℝ) * (1 / (d : ℝ))) * (1 + Real.log (m : ℝ)) := by ring
      _ ≤ 1 * (1 + Real.log (m : ℝ)) := mul_le_mul_of_nonneg_right (pd2a_quarter_inverse_le_one d hdpos) hlog
      _ = _ := one_mul _
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 m, ∑ d ∈ u.divisors, if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0 :=
      Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ = ∑ d ∈ u.divisors, ∑ n ∈ Finset.Icc 1 m, if d ∣ n then (d : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ d ∈ u.divisors, (1 + Real.log (m : ℝ)) := Finset.sum_le_sum fun d hd => hEach d hd
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

lemma pd2a_gcd_reflection (m u n : ℕ) (hu : 0 < u) (hdiv : u ∣ m) (hn : n ≤ m) :
    Nat.gcd (m - n) u = Nat.gcd n u := by
  letI : NeZero u := ⟨hu.ne'⟩
  have hm0 : (m : ZMod u) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hmod : ((m - n : ℕ) : ZMod u) = (-1 : ZMod u) * (n : ZMod u) := by
    rw [Nat.cast_sub hn, hm0]
    ring
  have hcast : (((( -1 : (ZMod u)ˣ) : ZMod u) * (n : ZMod u)).val : ZMod u) =
      (-1 : ZMod u) * (n : ZMod u) := by simp
  calc
    _ = Nat.gcd ((((-1 : (ZMod u)ˣ) : ZMod u) * (n : ZMod u)).val) u :=
      pd2a_gcd_modular_eq u _ _ (hmod.trans hcast.symm)
    _ = _ := pd2a_unit_frequency_gcd u u (dvd_refl u) (-1) n

lemma pd2a_interval_reflection_sum (m : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 (m - 1), F (m - n)) = ∑ n ∈ Finset.Icc 1 (m - 1), F n := by
  apply Finset.sum_nbij (fun n => m - n)
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    omega
  · intro n hn k hk heq
    have hn' := Finset.mem_Icc.mp hn
    have hk' := Finset.mem_Icc.mp hk
    dsimp only at heq
    omega
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    refine ⟨m - n, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      omega
    · change m - (m - n) = n
      omega
  · intro n hn
    rfl

lemma pd2a_min_frequency_gcd_sum (m u : ℕ) (hm : 0 < m) (hu : 0 < u) (hdiv : u ∣ m) :
    (∑ n ∈ Finset.Icc 1 (m - 1), (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) /
      (min n (m - n) : ℕ)) ≤ 2 * (u.divisors.card : ℝ) * (1 + Real.log (m : ℝ)) := by
  let I := Finset.Icc 1 (m - 1)
  have hEach : ∀ n ∈ I, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (min n (m - n) : ℕ) ≤
      (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n + (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (m - n : ℕ) := by
    intro n hn
    by_cases hcmp : n ≤ m - n
    · rw [min_eq_left hcmp]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hcmp))]
      exact le_add_of_nonneg_left (by positivity)
  have hReflect : (∑ n ∈ I, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (m - n : ℕ)) =
      ∑ n ∈ I, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n := by
    calc
      _ = ∑ n ∈ I, (Nat.gcd (m - n) u : ℝ) ^ (1 / 4 : ℝ) / (m - n : ℕ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hb := Finset.mem_Icc.mp hn
        rw [pd2a_gcd_reflection m u n hu hdiv (by omega)]
      _ = _ := pd2a_interval_reflection_sum m (fun n => (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n)
  have hSub : I ⊆ Finset.Icc 1 m := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (Nat.sub_le m 1)⟩
  calc
    _ ≤ ∑ n ∈ I, ((Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n + (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (m - n : ℕ)) :=
      Finset.sum_le_sum fun n hn => hEach n hn
    _ = 2 * (∑ n ∈ I, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n) := by rw [Finset.sum_add_distrib, hReflect]; ring
    _ ≤ 2 * (∑ n ∈ Finset.Icc 1 m, (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / n) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun n hn hn' => by positivity)) (by norm_num)
    _ ≤ 2 * ((u.divisors.card : ℝ) * (1 + Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (pd2a_weighted_gcd_harmonic m u hm hu) (by norm_num)
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
