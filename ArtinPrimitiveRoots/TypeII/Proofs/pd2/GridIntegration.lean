import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor

namespace ArtinPrimitiveRoots.TypeII.PD
open MeasureTheory Set

noncomputable section

lemma interval_indicator_Icc (a b l r : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, if t ∈ Icc l r then (1 : ℝ) else 0) =
      max 0 (min r b - max l a) := by
  have hi : (fun t : ℝ => if t ∈ Icc l r then (1 : ℝ) else 0) =
      (Icc l r).indicator (fun _ => (1 : ℝ)) := by
    funext t
    simp [Set.indicator_apply]
  rw [hi, intervalIntegral.integral_of_le hab,
    setIntegral_congr_set (Ioc_ae_eq_Icc : Ioc a b =ᵐ[volume] Icc a b),
    integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc l r ∩ Icc a b = Icc (max l a) (min r b) := by
    ext t
    simp only [mem_inter_iff, mem_Icc, max_le_iff, le_min_iff]
    tauto
  rw [hset, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
  simpa only [max_comm] using (ENNReal.toReal_ofReal' (r := min r b - max l a))

lemma interval_floor_indicator (a b h : ℝ) (hh : 0 < h) (hab : a ≤ b) (k : ℤ) :
    (∫ t in a..b, if ⌊t / h⌋ = k then (1 : ℝ) else 0) =
      max 0 (min (((k : ℝ) + 1) * h) b - max ((k : ℝ) * h) a) := by
  calc
    _ = ∫ t in a..b, if t ∈ Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) then (1 : ℝ) else 0 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (((k : ℝ) + 1) * h)] with t ht _
      have he : ⌊t / h⌋ = k ↔ t ∈ Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) := by
        rw [Int.floor_eq_iff]
        simp only [mem_Icc]
        constructor
        · rintro ⟨hl, hr⟩
          exact ⟨(le_div_iff₀ hh).1 hl, ((div_lt_iff₀ hh).1 hr).le⟩
        · rintro ⟨hl, hr⟩
          exact ⟨(le_div_iff₀ hh).2 hl, (div_lt_iff₀ hh).2 (lt_of_le_of_ne hr ht)⟩
      simp only [he]
    _ = _ := interval_indicator_Icc a b _ _ hab

lemma triple_rectangle_indicator
    (a₁ b₁ a₂ b₂ a₃ b₃ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) :
    (∫ u in a₁..b₁, ∫ v in a₂..b₂, ∫ r in a₃..b₃,
      if u ∈ Icc l₁ r₁ ∧ v ∈ Icc l₂ r₂ ∧ r ∈ Icc l₃ r₃ then (1 : ℝ) else 0) =
      max 0 (min r₁ b₁ - max l₁ a₁) *
        max 0 (min r₂ b₂ - max l₂ a₂) * max 0 (min r₃ b₃ - max l₃ a₃) := by
  have he (u v r : ℝ) :
      (if u ∈ Icc l₁ r₁ ∧ v ∈ Icc l₂ r₂ ∧ r ∈ Icc l₃ r₃ then (1 : ℝ) else 0) =
      (if u ∈ Icc l₁ r₁ then (1 : ℝ) else 0) *
      ((if v ∈ Icc l₂ r₂ then (1 : ℝ) else 0) * (if r ∈ Icc l₃ r₃ then (1 : ℝ) else 0)) := by
    by_cases hu : u ∈ Icc l₁ r₁ <;> by_cases hv : v ∈ Icc l₂ r₂ <;>
      by_cases hr : r ∈ Icc l₃ r₃ <;> simp [hu, hv, hr]
  simp_rw [he, intervalIntegral.integral_const_mul,
    interval_indicator_Icc a₃ b₃ l₃ r₃ h₃,
    intervalIntegral.integral_mul_const,
    interval_indicator_Icc a₂ b₂ l₂ r₂ h₂,
    interval_indicator_Icc a₁ b₁ l₁ r₁ h₁]
  ring

lemma triple_floor_indicator (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ) :
    (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      if (⌊u / h⌋, ⌊v / h⌋, ⌊r / h⌋) = k then (1 : ℝ) else 0) =
      max 0 (min (((k.1 : ℝ) + 1) * h) 16 - max ((k.1 : ℝ) * h) 1) *
        max 0 (min (((k.2.1 : ℝ) + 1) * h) 2 - max ((k.2.1 : ℝ) * h) 1) *
        max 0 (min (((k.2.2 : ℝ) + 1) * h) 1 - max ((k.2.2 : ℝ) * h) 0) := by
  have he (u v r : ℝ) :
      (if (⌊u / h⌋, ⌊v / h⌋, ⌊r / h⌋) = k then (1 : ℝ) else 0) =
      (if ⌊u / h⌋ = k.1 then (1 : ℝ) else 0) *
      ((if ⌊v / h⌋ = k.2.1 then (1 : ℝ) else 0) * (if ⌊r / h⌋ = k.2.2 then (1 : ℝ) else 0)) := by
    have hk : (⌊u / h⌋, ⌊v / h⌋, ⌊r / h⌋) = k ↔
      ⌊u / h⌋ = k.1 ∧ ⌊v / h⌋ = k.2.1 ∧ ⌊r / h⌋ = k.2.2 := by
      simp only [Prod.ext_iff]
    simp only [hk]
    by_cases hu : ⌊u / h⌋ = k.1 <;> by_cases hv : ⌊v / h⌋ = k.2.1 <;>
      by_cases hr : ⌊r / h⌋ = k.2.2 <;> simp [hu, hv, hr]
  simp_rw [he, intervalIntegral.integral_const_mul,
    interval_floor_indicator 0 1 h hh (by norm_num),
    intervalIntegral.integral_mul_const,
    interval_floor_indicator 1 2 h hh (by norm_num),
    interval_floor_indicator 1 16 h hh (by norm_num)]
  ring

end
end ArtinPrimitiveRoots.TypeII.PD
