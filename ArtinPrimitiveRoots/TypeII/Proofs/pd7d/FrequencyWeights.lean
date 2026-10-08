import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FrequencyWindows
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FourierWeightAlgebra

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

noncomputable def pd7dFrequencyWeight (H : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ((1 + |t| / H) ^ j)⁻¹

lemma pd7dFrequencyWeight_nonneg (H : ℝ) (hH : 0 < H) (j : ℕ) (t : ℝ) :
    0 ≤ pd7dFrequencyWeight H j t := by
  unfold pd7dFrequencyWeight
  positivity

lemma pd7dFrequencyWeight_eq_rpow (H : ℝ) (hH : 0 < H) (j : ℕ) (t : ℝ) :
    pd7dFrequencyWeight H j t = Real.rpow (1 + |t| / H) (-(j : ℝ)) :=
  (pd7d_inverse_nat_rpow _ (by positivity) j).symm

lemma pd7dFrequencyWeight_continuous (H : ℝ) (hH : 0 < H) (j : ℕ) :
    Continuous (pd7dFrequencyWeight H j) := by
  have hb : Continuous (fun t : ℝ => 1 + |t| / H) := continuous_const.add (continuous_abs.div_const H)
  exact (hb.pow j).inv₀ (fun t => ne_of_gt (pow_pos (by positivity) j))

lemma pd7dFrequencyWeight_integrable (H : ℝ) (hH : 0 < H) (j : ℕ) (hj : 2 ≤ j) :
    Integrable (pd7dFrequencyWeight H j) := by
  have hb : Integrable (fun t : ℝ => Real.rpow (1 + ‖t‖) (-(j : ℝ))) :=
    integrable_one_add_norm (by simp only [Module.finrank_self]; exact_mod_cast (by omega : 1 < j))
  have hh := hb.comp_div (ne_of_gt hH)
  apply hh.congr
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hH, ← pd7dFrequencyWeight_eq_rpow H hH j t]

lemma pd7d_shifted_pseries_summable (j : ℕ) (hj : 2 ≤ j) :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ j)) := by
  have hb : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ j)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  exact (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ j)) 1).mpr hb

lemma pd7d_frequency_weight_on_window (H S : ℝ) (hH : 0 < H) (hS : 0 < S)
    (j n : ℕ) (t : ℝ) (ht : t ∈ pd7dFrequencyWindow S n) :
    pd7dFrequencyWeight H j t ≤ (H / S) ^ j / (((n + 1 : ℕ) : ℝ) ^ j) := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have htp : 0 < t := lt_of_lt_of_le (by positivity : 0 < ((n + 1 : ℕ) : ℝ) * S) ht.1.le
  have hratio : 0 < (((n + 1 : ℕ) : ℝ) * S) / H := div_pos (mul_pos hn hS) hH
  have hbase : (((n + 1 : ℕ) : ℝ) * S) / H ≤ 1 + |t| / H := by
    rw [abs_of_pos htp]
    have hh := div_le_div_of_nonneg_right ht.1.le hH.le
    linarith
  unfold pd7dFrequencyWeight
  have hpow := pow_le_pow_left₀ hratio.le hbase j
  calc
    _ ≤ ((((n + 1 : ℕ) : ℝ) * S / H) ^ j)⁻¹ :=
      inv_le_inv₀ (pow_pos (by positivity) j) (pow_pos hratio j) |>.mpr hpow
    _ = _ := by rw [div_pow, mul_pow, div_pow]; field_simp <;> ring

lemma pd7dFrequencyWeight_le_one (H : ℝ) (hH : 0 < H) (j : ℕ) (t : ℝ) :
    pd7dFrequencyWeight H j t ≤ 1 := by
  have hb : 1 ≤ 1 + |t| / H := by
    have hh := div_nonneg (abs_nonneg t) hH.le
    linarith
  have hp : 1 ≤ (1 + |t| / H) ^ j := one_le_pow₀ hb
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  simpa only [pd7dFrequencyWeight, one_div, inv_one] using hh

lemma pd7dFrequencyWeight_even (H : ℝ) (j : ℕ) (t : ℝ) :
    pd7dFrequencyWeight H j (-t) = pd7dFrequencyWeight H j t := by simp [pd7dFrequencyWeight]

end ArtinPrimitiveRoots.TypeII.PD
