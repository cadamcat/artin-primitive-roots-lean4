import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Construction.Proofs.c4.Density

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.Rough
open Classical

/-- Natural points between the two endpoints of a dyadic interval form an interval. -/
noncomputable def dyadicCoordinateInterval (H : ℝ) : Set ℕ :=
  {m : ℕ | H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H}
attribute [irreducible] dyadicCoordinateInterval

theorem mem_dyadicCoordinateInterval_iff (H : ℝ) (m : ℕ) :
    m ∈ dyadicCoordinateInterval H ↔ H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H := by
  unfold dyadicCoordinateInterval
  rfl

theorem dyadicCoordinateInterval_isNatInterval (H : ℝ) :
    IsNatInterval (dyadicCoordinateInterval H) := by
  change IsNatInterval (dyadicCoordinateInterval H)
  intro m n k hm hn hmin hmax
  rw [mem_dyadicCoordinateInterval_iff] at hm hn
  rw [mem_dyadicCoordinateInterval_iff]
  have hmin' : min (m : ℝ) (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmin
  have hmax' : (k : ℝ) ≤ max (m : ℝ) (n : ℝ) := by exact_mod_cast hmax
  constructor
  · exact (le_min (by exact_mod_cast hm.1) (by exact_mod_cast hn.1)).trans hmin'
  · exact hmax'.trans (max_le (by exact_mod_cast hm.2) (by exact_mod_cast hn.2))

theorem dyadicIntegers_subset_coordinateInterval (H : ℝ) :
    (dyadicIntegers H : Set ℕ) ⊆ dyadicCoordinateInterval H := by
  intro m hm
  rw [dyadicIntegers] at hm
  rw [mem_dyadicCoordinateInterval_iff]
  exact (Finset.mem_filter.mp hm).2

/-- Both endpoints of a dyadic scale lie in the fixed exponent window used by Type II. -/
theorem dyadic_log_scales_in_window {x H : ℝ} (hx : 1 < x)
    (hL : 200 ≤ Real.log x)
    (hlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
    (hhi : H ≤ 2 * Real.rpow x (54 / 100 : ℝ)) :
    Real.log H / Real.log x ∈ Set.Icc (45 / 100 : ℝ) (55 / 100 : ℝ) ∧
    Real.log (2 * H) / Real.log x ∈ Set.Icc (45 / 100 : ℝ) (55 / 100 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have he : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) he
      _ = 1 := Real.log_exp 1
  have hlog2small : Real.log 2 ≤ Real.log x / 100 := by
    have : (1 : ℝ) ≤ Real.log x / 100 := by linarith
    exact hlog2.trans this
  have hlowPos : 0 < Real.rpow x (46 / 100 : ℝ) / 2 :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num)
  have hHpos : 0 < H := lt_of_lt_of_le hlowPos hlo
  have hlogLowerArg :
      Real.log (Real.rpow x (46 / 100 : ℝ) / 2) =
        (46 / 100 : ℝ) * Real.log x - Real.log 2 := by
    calc
      _ = Real.log (x ^ (46 / 100 : ℝ) / 2) := by rw [Real.rpow_eq_pow]
      _ = Real.log (x ^ (46 / 100 : ℝ)) - Real.log 2 :=
        Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num)
      _ = _ := by rw [Real.log_rpow hxpos]
  have hlogUpperArg :
      Real.log (2 * Real.rpow x (54 / 100 : ℝ)) =
        Real.log 2 + (54 / 100 : ℝ) * Real.log x := by
    calc
      _ = Real.log (2 * (x ^ (54 / 100 : ℝ))) := by rw [Real.rpow_eq_pow]
      _ = Real.log 2 + Real.log (x ^ (54 / 100 : ℝ)) :=
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (Real.rpow_pos_of_pos hxpos _))
      _ = _ := by rw [Real.log_rpow hxpos]
  have hlowLog : (46 / 100 : ℝ) * Real.log x - Real.log 2 ≤ Real.log H := by
    have h := Real.log_le_log
      (div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num)) hlo
    have hlogLowerArg' : Real.log (x ^ (46 / 100 : ℝ) / 2) =
        (46 / 100 : ℝ) * Real.log x - Real.log 2 := by
      simpa only [Real.rpow_eq_pow] using hlogLowerArg
    rw [hlogLowerArg'] at h
    linarith
  have hhighLog : Real.log H ≤ Real.log 2 + (54 / 100 : ℝ) * Real.log x := by
    have h := Real.log_le_log hHpos hhi
    rw [hlogUpperArg] at h
    linarith
  have hlog2Hlow : (45 / 100 : ℝ) * Real.log x ≤ Real.log (2 * H) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne']
    nlinarith [hlowLog, hlog2pos]
  have hlog2Hhigh : Real.log (2 * H) ≤ (55 / 100 : ℝ) * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne']
    nlinarith [hhighLog, hlog2small]
  constructor
  · constructor
    · apply (le_div_iff₀ hLpos).2
      nlinarith [hlowLog, hlog2small]
    · apply (div_le_iff₀ hLpos).2
      nlinarith [hhighLog, hlog2small]
  · constructor
    · apply (le_div_iff₀ hLpos).2
      exact hlog2Hlow
    · apply (div_le_iff₀ hLpos).2
      exact hlog2Hhigh

/-- The wider dyadic lower scale retains its exponent, with the endpoint loss explicit. -/
theorem dyadic_log_lower_exact {x H : ℝ} (hx : 1 < x)
    (hlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H) :
    (46 / 100 : ℝ) * Real.log x - Real.log 2 ≤ Real.log H := by
  have hxpos : 0 < x := by linarith
  have hlowPos : 0 < Real.rpow x (46 / 100 : ℝ) / 2 :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num)
  have h := Real.log_le_log hlowPos hlo
  have hlogLowerArg :
      Real.log (Real.rpow x (46 / 100 : ℝ) / 2) =
        (46 / 100 : ℝ) * Real.log x - Real.log 2 := by
    calc
      _ = Real.log (x ^ (46 / 100 : ℝ) / 2) := by rw [Real.rpow_eq_pow]
      _ = Real.log (x ^ (46 / 100 : ℝ)) - Real.log 2 :=
        Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num)
      _ = _ := by rw [Real.log_rpow hxpos]
  rw [hlogLowerArg] at h
  exact h

theorem roughCutoff_lt_two_fifths {x : ℝ} (hx : 1 < x)
    (hL : 200 ≤ Real.log x) :
    roughCutoff x < Real.rpow x (2 / 5 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hLone : 1 ≤ Real.log x := by linarith
  have hpow : Real.rpow (Real.log x) (24 / 100 : ℝ) ≤
      Real.rpow (Real.log x) (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hsqrt : Real.rpow (Real.log x) (1 / 2 : ℝ) = Real.sqrt (Real.log x) := by
    simpa only [Real.rpow_eq_pow] using (Real.sqrt_eq_rpow (Real.log x)).symm
  have hrightpos : 0 < Real.log x / 10 := by positivity
  have hlarge : Real.log x < (Real.log x / 10) ^ 2 := by nlinarith [hL]
  have hlin : Real.sqrt (Real.log x) < Real.log x / 10 :=
    (Real.sqrt_lt' hrightpos).2 hlarge
  have hexp : Real.rpow (Real.log x) (24 / 100 : ℝ) <
      (2 / 5 : ℝ) * Real.log x := by
    calc
      _ ≤ Real.sqrt (Real.log x) := by rw [← hsqrt]; exact hpow
      _ < (2 / 5 : ℝ) * Real.log x := by nlinarith [hlin]
  have hxpow : Real.rpow x (2 / 5 : ℝ) =
      Real.exp (Real.log x * (2 / 5 : ℝ)) := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_def_of_pos hxpos (2 / 5 : ℝ)
  unfold roughCutoff
  rw [hxpow]
  exact Real.exp_lt_exp.mpr (by nlinarith [hexp])

theorem rpow_one_fifth_le_dyadic_lower {x : ℝ} (hx : 1 < x)
    (hL : 200 ≤ Real.log x) :
    Real.rpow x (1 / 5 : ℝ) ≤ Real.rpow x (46 / 100 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have he : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) he
      _ = 1 := Real.log_exp 1
  have hpow26 : Real.rpow x (26 / 100 : ℝ) =
      Real.exp (Real.log x * (26 / 100 : ℝ)) := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_def_of_pos hxpos (26 / 100 : ℝ)
  have hlarge26 : 2 ≤ Real.rpow x (26 / 100 : ℝ) := by
    rw [hpow26]
    have h2 : 2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    rw [h2]
    apply Real.exp_le_exp.mpr
    nlinarith [hL, hlog2]
  have hpow46 : Real.rpow x (46 / 100 : ℝ) =
      Real.rpow x (1 / 5 : ℝ) * Real.rpow x (26 / 100 : ℝ) := by
    have h := Real.rpow_add hxpos (1 / 5 : ℝ) (26 / 100 : ℝ)
    convert h using 1 <;> norm_num
  have hmul : 2 * Real.rpow x (1 / 5 : ℝ) ≤
      Real.rpow x (46 / 100 : ℝ) := by
    rw [hpow46]
    calc
      2 * Real.rpow x (1 / 5 : ℝ) = Real.rpow x (1 / 5 : ℝ) * 2 := by ring
      _ ≤ Real.rpow x (1 / 5 : ℝ) * Real.rpow x (26 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hlarge26
          (Real.rpow_nonneg hxpos.le (1 / 5 : ℝ))
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hmul])

theorem two_fifths_lt_dyadic_lower {x : ℝ} (hx : 1 < x)
    (hL : 200 ≤ Real.log x) :
    Real.rpow x (2 / 5 : ℝ) < Real.rpow x (46 / 100 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have he : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) he
      _ = 1 := Real.log_exp 1
  have hpow06 : Real.rpow x (6 / 100 : ℝ) =
      Real.exp (Real.log x * (6 / 100 : ℝ)) := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_def_of_pos hxpos (6 / 100 : ℝ)
  have hlarge06 : 2 < Real.rpow x (6 / 100 : ℝ) := by
    rw [hpow06]
    have h2 : 2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    rw [h2]
    apply Real.exp_lt_exp.mpr
    nlinarith [hL, hlog2]
  have hpow46 : Real.rpow x (46 / 100 : ℝ) =
      Real.rpow x (2 / 5 : ℝ) * Real.rpow x (6 / 100 : ℝ) := by
    have h := Real.rpow_add hxpos (2 / 5 : ℝ) (6 / 100 : ℝ)
    convert h using 1 <;> norm_num
  have hmul : 2 * Real.rpow x (2 / 5 : ℝ) < Real.rpow x (46 / 100 : ℝ) := by
    rw [hpow46]
    calc
      2 * Real.rpow x (2 / 5 : ℝ) = Real.rpow x (2 / 5 : ℝ) * 2 := by ring
      _ < Real.rpow x (2 / 5 : ℝ) * Real.rpow x (6 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hlarge06
          (Real.rpow_pos_of_pos hxpos (2 / 5 : ℝ))
  have hmul' : Real.rpow x (2 / 5 : ℝ) * 2 < Real.rpow x (46 / 100 : ℝ) := by
    simpa [mul_comm] using hmul
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 hmul'

theorem roughAbove_mono_cutoff {n : ℕ} {y z : ℝ} (hyz : y ≤ z)
    (h : roughAbove n z) : roughAbove n y := by
  intro p hp hpn
  exact lt_of_le_of_lt hyz (h p hp hpn)

theorem roughAbove_of_prime_gt {p : ℕ} {y : ℝ} (hp : p.Prime)
    (hy : y < (p : ℝ)) : roughAbove p y := by
  intro q hq hqp
  have hEq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  simpa [hEq] using hy

theorem roughProxy_eq_one_div_log {x γ : ℝ} {m : ℕ}
    (hL : 0 < Real.log x)
    (hV : 0 < roughSieveProduct (roughCutoff x))
    (hm : 0 < Real.log (m : ℝ))
    (hD : ArtinPrimitiveRoots.Sieve.roughDensity γ
      (Real.log (m : ℝ) / Real.log x) =
        1 / (Real.log (m : ℝ) / Real.log x)) :
    roughProxy x γ m = if roughAbove m (roughCutoff x) then
      1 / (roughSieveProduct (roughCutoff x) * Real.log (m : ℝ)) else 0 := by
  classical
  unfold roughProxy
  have hD' : roughDensity γ (Real.log (m : ℝ) / Real.log x) =
      1 / (Real.log (m : ℝ) / Real.log x) := by
    simpa [roughDensity] using hD
  rw [hD']
  by_cases hrough : roughAbove m (roughCutoff x)
  · simp [hrough]
    field_simp [ne_of_gt hL, ne_of_gt hV, ne_of_gt hm]
    <;> ring
  · simp [hrough]

end ArtinPrimitiveRoots.Construction.Proofs.C4
