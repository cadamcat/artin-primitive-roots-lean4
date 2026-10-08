import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.WeightedTail

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_integral_reflect (f : ℝ → ℝ) : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
  have hh := Measure.integral_comp_smul (volume : Measure ℝ) f (-1 : ℝ)
  simpa only [Module.finrank_self, pow_one, inv_neg, inv_one, abs_neg, abs_one,
    neg_one_smul, one_smul] using hh

lemma pd7d_integral_Iio_reflect (S : ℝ) (f : ℝ → ℝ) :
    (∫ t in Set.Iio (-S), f t) = ∫ t in Set.Ioi S, f (-t) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  have hneg := pd7d_integral_reflect ((Set.Iio (-S)).indicator f)
  refine hneg.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : S < t
  · have htneg : -t ∈ Set.Iio (-S) := Set.mem_Iio.mpr (neg_lt_neg ht)
    rw [Set.indicator_of_mem htneg, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
  · have htneg : -t ∉ Set.Iio (-S) := by
      intro hn
      apply ht
      have hh := Set.mem_Iio.mp hn
      linarith
    rw [Set.indicator_of_notMem htneg, Set.indicator_of_notMem (by exact fun h => ht (Set.mem_Ioi.mp h))]

lemma pd7d_reflected_mean_bound (C : ℝ) (f : ℝ → ℝ)
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a))) :
    ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f (-t)) ≤ C * (1 + (b - a)) := by
  intro a b hab
  rw [intervalIntegral.integral_comp_neg]
  have hh := hmean (-b) (-a) (by linarith)
  convert hh using 1 <;> ring

lemma pd7d_reflected_weight_integrable (H : ℝ) (j : ℕ) (f : ℝ → ℝ)
    (hg : Integrable (fun t => pd7dFrequencyWeight H j t * f t)) :
    Integrable (fun t => pd7dFrequencyWeight H j t * f (-t)) := by
  have hh := hg.comp_smul (R := (-1 : ℝ)) (by norm_num)
  simpa only [neg_one_smul, pd7dFrequencyWeight_even] using hh

lemma pd7d_weighted_full (H C : ℝ) (hH : 1 ≤ H) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hweighted : Integrable (fun t => pd7dFrequencyWeight H j t * f t))
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a))) :
    (∫ t : ℝ, pd7dFrequencyWeight H j t * f t) ≤ 4 * C * H * (1 + pd7dPSeries j) := by
  have hHp : 0 < H := by linarith
  have hpos := pd7d_positive_weighted_full H C hHp hC j hj f hf hfn hweighted hmean
  have hneg := pd7d_positive_weighted_full H C hHp hC j hj (fun t => f (-t))
    (hf.comp continuous_neg) (fun t => hfn (-t)) (pd7d_reflected_weight_integrable H j f hweighted)
    (pd7d_reflected_mean_bound C f hmean)
  have hnegEq := pd7d_integral_Iio_reflect 0 (fun t => pd7dFrequencyWeight H j t * f t)
  simp only [neg_zero, pd7dFrequencyWeight_even] at hnegEq
  rw [← hnegEq] at hneg
  have hsplit := integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hweighted
  rw [Set.compl_Ioi, integral_Iic_eq_integral_Iio] at hsplit
  rw [← hsplit]
  have hZ : 0 ≤ 1 + pd7dPSeries j := by linarith [pd7dPSeries_nonneg j]
  calc
    _ ≤ 2 * (C * (1 + H) * (1 + pd7dPSeries j)) := by linarith
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (by linarith : 1 + H ≤ 2 * H) (mul_nonneg hC hZ)
      nlinarith

lemma pd7d_weighted_tails (H S C : ℝ) (hH : 0 < H) (hS : 1 ≤ S) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hweighted : Integrable (fun t => pd7dFrequencyWeight H j t * f t))
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a))) :
    (∫ t in Set.Iio (-S), pd7dFrequencyWeight H j t * f t) +
      (∫ t in Set.Ioi S, pd7dFrequencyWeight H j t * f t) ≤
        4 * C * S * (H / S) ^ j * (1 + pd7dPSeries j) := by
  have hSp : 0 < S := by linarith
  have hpos := pd7d_positive_weighted_tail H S C hH hSp hC j hj f hf hfn hweighted.integrableOn hmean
  have hneg := pd7d_positive_weighted_tail H S C hH hSp hC j hj (fun t => f (-t))
    (hf.comp continuous_neg) (fun t => hfn (-t))
    (pd7d_reflected_weight_integrable H j f hweighted).integrableOn (pd7d_reflected_mean_bound C f hmean)
  have hnegEq := pd7d_integral_Iio_reflect S (fun t => pd7dFrequencyWeight H j t * f t)
  simp only [pd7dFrequencyWeight_even] at hnegEq
  rw [← hnegEq] at hneg
  have hP : 0 ≤ pd7dPSeries j := pd7dPSeries_nonneg j
  have hratio : 0 ≤ (H / S) ^ j := by positivity
  calc
    _ ≤ 2 * (C * (1 + S) * (H / S) ^ j * pd7dPSeries j) := by linarith
    _ ≤ 4 * C * S * (H / S) ^ j * pd7dPSeries j := by
      have hh := mul_le_mul_of_nonneg_right (by linarith : 1 + S ≤ 2 * S)
        (mul_nonneg (mul_nonneg hC hratio) hP)
      nlinarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (by linarith : pd7dPSeries j ≤ 1 + pd7dPSeries j)
      positivity

end ArtinPrimitiveRoots.TypeII.PD
