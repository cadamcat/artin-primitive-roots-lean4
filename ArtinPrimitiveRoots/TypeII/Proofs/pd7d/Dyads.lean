import ArtinPrimitiveRoots.TypeII.PD.Defs
import Mathlib.Data.Nat.Log

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

set_option autoImplicit false

noncomputable def pd7dPrimeDyads (S : Finset ℕ) : Finset ℕ := S.image (Nat.log 2)

def pd7dPrimeDyad (S : Finset ℕ) (j : ℕ) : Finset ℕ := S.filter (fun p => Nat.log 2 p = j)

lemma pd7dPrimeDyad_bounds (S : Finset ℕ) (j p : ℕ)
    (hp : p ∈ pd7dPrimeDyad S j) (hpos : 0 < p) :
    (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * (2 : ℝ) ^ j := by
  have hj := (Finset.mem_filter.mp hp).2
  have hlo := Nat.pow_log_le_self 2 (ne_of_gt hpos)
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) p
  rw [hj] at hlo hhi
  constructor
  · exact_mod_cast hlo
  · have hh : (p : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hhi
    simpa [pow_succ, mul_comm] using hh

lemma pd7d_sum_prime_dyads (S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ p ∈ S, f p = ∑ j ∈ pd7dPrimeDyads S, ∑ p ∈ pd7dPrimeDyad S j, f p := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem (Nat.log 2) hp) f).symm

lemma pd7dPrimeDyads_nonempty_fiber (S : Finset ℕ) (j : ℕ)
    (hj : j ∈ pd7dPrimeDyads S) : (pd7dPrimeDyad S j).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

lemma pd7dPrimeDyads_card_le (S : Finset ℕ) (H : ℝ)
    (hH : 0 ≤ H) (hbound : ∀ p ∈ S, 0 < p ∧ Real.log (p : ℝ) ≤ H) :
    (pd7dPrimeDyads S).card ≤ ⌊H / Real.log 2⌋₊ + 1 := by
  apply (Finset.card_le_card (t := Finset.range (⌊H / Real.log 2⌋₊ + 1)) ?_).trans_eq
    (Finset.card_range _)
  intro j hj
  obtain ⟨p, hp, hjp⟩ := Finset.mem_image.mp hj
  have hp' := hbound p hp
  have hlo : (2 : ℝ) ^ j ≤ (p : ℝ) := by
    have hn := Nat.pow_log_le_self 2 (ne_of_gt hp'.1)
    rw [hjp] at hn
    exact_mod_cast hn
  have hlog := (Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) hlo).trans hp'.2
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjH : (j : ℝ) ≤ H / Real.log 2 := (le_div_iff₀ hlog2).2 hlog
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hjH))

lemma pd7d_prime_band_dyad_log_bounds (x e : ℝ) (j : ℕ)
    (hj : j ∈ pd7dPrimeDyads (ArtinPrimitiveRoots.TypeII.primeBand x e)) :
    Real.rpow (Real.log x) e - Real.log 2 < Real.log ((2 : ℝ) ^ j) ∧
      Real.log ((2 : ℝ) ^ j) ≤ 2 * Real.rpow (Real.log x) e := by
  obtain ⟨p, hp⟩ := pd7dPrimeDyads_nonempty_fiber (primeBand x e) j hj
  have hpS := (Finset.mem_filter.mp hp).1
  have hpB := (Finset.mem_filter.mp hpS).2
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hpB.1.pos
  obtain ⟨hlo, hhi⟩ := pd7dPrimeDyad_bounds _ j p hp hpB.1.pos
  have hloglo : Real.rpow (Real.log x) e ≤ Real.log (p : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hpB.2.1
    simpa using hh
  have hloghi : Real.log (p : ℝ) ≤ 2 * Real.rpow (Real.log x) e := by
    have hh := Real.log_le_log hppos hpB.2.2
    simpa using hh
  have hdyadhi := Real.log_lt_log hppos hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ j ≠ 0)] at hdyadhi
  exact ⟨by linarith, (Real.log_le_log (by positivity) hlo).trans hloghi⟩

lemma pd7d_prime_band_dyad_sparse_range (x e : ℝ) (j : ℕ)
    (hL : 1 ≤ Real.log x) (he : (1 / 10 : ℝ) ≤ e) (hehi : e ≤ 1 / 5)
    (hlarge : 2 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ))
    (hj : j ∈ pd7dPrimeDyads (ArtinPrimitiveRoots.TypeII.primeBand x e)) :
    (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log ((2 : ℝ) ^ j) ∧
      Real.log ((2 : ℝ) ^ j) ≤ 3 * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := pd7d_prime_band_dyad_log_bounds x e j hj
  have hpLo : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.rpow (Real.log x) e :=
    Real.rpow_le_rpow_of_exponent_le hL he
  have hpHi : Real.rpow (Real.log x) e ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL hehi
  have hpPos : 0 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hqPos : 0 ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.rpow_nonneg (by linarith) _
  constructor <;> linarith

lemma pd7d_prime_band_dyads_card (x e : ℝ) (hL : 1 ≤ Real.log x) (he : e ≤ 1) :
    ((pd7dPrimeDyads (ArtinPrimitiveRoots.TypeII.primeBand x e)).card : ℝ) ≤
      (2 / Real.log 2 + 1) * Real.log x := by
  have hLpos : 0 < Real.log x := by linarith
  have hp0 : 0 ≤ Real.rpow (Real.log x) e := Real.rpow_nonneg hLpos.le e
  have hpow : Real.rpow (Real.log x) e ≤ Real.log x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL he
  have hc := pd7dPrimeDyads_card_le (primeBand x e)
    (2 * Real.rpow (Real.log x) e) (mul_nonneg (by norm_num) hp0) (by
      intro p hp
      have hpB := (Finset.mem_filter.mp hp).2
      refine ⟨hpB.1.pos, ?_⟩
      have hh := Real.log_le_log (by exact_mod_cast hpB.1.pos) hpB.2.2
      simpa using hh)
  have hcR : ((pd7dPrimeDyads (primeBand x e)).card : ℝ) ≤
      (⌊2 * Real.rpow (Real.log x) e / Real.log 2⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf : (⌊2 * Real.rpow (Real.log x) e / Real.log 2⌋₊ : ℝ) ≤
      2 * Real.rpow (Real.log x) e / Real.log 2 := Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) hp0) hlog2.le)
  have hp : 2 * Real.rpow (Real.log x) e / Real.log 2 ≤
      (2 / Real.log 2) * Real.log x := by
    calc
      _ ≤ 2 * Real.log x / Real.log 2 := div_le_div_of_nonneg_right (by linarith) hlog2.le
      _ = _ := by ring
  nlinarith

end ArtinPrimitiveRoots.TypeII.PD
