import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open scoped Topology

set_option autoImplicit false

/-- The finite envelope of unit-interval suprema has integral equal to their sum. -/
lemma pd7d_unit_interval_envelope (J : Finset ℤ) (W : ℤ → ℝ)
    (hW : ∀ j ∈ J, 0 ≤ W j) :
    let E := fun t : ℝ => ∑ j ∈ J,
      (Set.Icc (j : ℝ) ((j : ℝ) + 1)).indicator (fun _ => W j) t
    Integrable E ∧ (∀ t, 0 ≤ E t) ∧ (∫ t : ℝ, E t) = ∑ j ∈ J, W j := by
  dsimp only
  have hi (j : ℤ) : Integrable
      ((Set.Icc (j : ℝ) ((j : ℝ) + 1)).indicator (fun _ : ℝ => W j)) := by
    exact (integrableOn_const (s := Set.Icc (j : ℝ) ((j : ℝ) + 1))
      (C := W j) (by simp)).integrable_indicator measurableSet_Icc
  refine ⟨integrable_finsetSum J (fun j _ => hi j), ?_, ?_⟩
  · intro t
    apply Finset.sum_nonneg
    intro j hj
    exact Set.indicator_nonneg (fun _ _ => hW j hj) t
  · rw [integral_finsetSum J (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_indicator_const _ measurableSet_Icc]
    simp

/-- Split an energy into a uniformly small prime factor and finitely many exceptional
unit intervals. No cancellation bound is required outside the integration interval. -/
lemma pd7d_sparse_energy_bound (P M N : ℝ → ℂ) (T s R m : ℝ)
    (J : Finset ℤ) (W : ℤ → ℝ)
    (hP : Continuous P) (hM : Continuous M) (hN : Continuous N)
    (hT : 0 ≤ T) (hs : 0 ≤ s) (hR : 0 ≤ R) (hm : 0 ≤ m)
    (hW : ∀ j ∈ J, 0 ≤ W j)
    (hRbound : ∀ t, ‖P t‖ ≤ R)
    (hMbound : ∀ t ∈ Set.Icc (-T) T, ‖M t‖ ≤ m)
    (hbad : ∀ t ∈ Set.Icc (-T) T, s < ‖P t‖ →
      ∃ j ∈ J, t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) ∧ ‖N t‖ ^ 2 ≤ W j) :
    ∫ t in (-T)..T, ‖P t * M t * N t‖ ^ 2 ≤
      s ^ 2 * (∫ t in (-T)..T, ‖M t * N t‖ ^ 2) +
        R ^ 2 * m ^ 2 * ∑ j ∈ J, W j := by
  let E := fun t : ℝ => ∑ j ∈ J,
    (Set.Icc (j : ℝ) ((j : ℝ) + 1)).indicator (fun _ => W j) t
  obtain ⟨hEi, hEn, hEsum⟩ := pd7d_unit_interval_envelope J W hW
  have hf : IntegrableOn (fun t => ‖P t * M t * N t‖ ^ 2) (Set.Icc (-T) T) :=
    (((hP.mul hM).mul hN).norm.pow 2).integrableOn_Icc
  have hmn : IntegrableOn (fun t => ‖M t * N t‖ ^ 2) (Set.Icc (-T) T) :=
    ((hM.mul hN).norm.pow 2).integrableOn_Icc
  have hupper : IntegrableOn
      (fun t => s ^ 2 * ‖M t * N t‖ ^ 2 + R ^ 2 * m ^ 2 * E t)
      (Set.Icc (-T) T) := (hmn.const_mul _).add (hEi.integrableOn.const_mul _)
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖P t * M t * N t‖ ^ 2 ≤
        s ^ 2 * ‖M t * N t‖ ^ 2 + R ^ 2 * m ^ 2 * E t := by
    intro t ht
    by_cases hp : ‖P t‖ ≤ s
    · have hps : ‖P t‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      calc
        _ = ‖P t‖ ^ 2 * ‖M t * N t‖ ^ 2 := by
          simp only [norm_mul, mul_pow, mul_assoc]
        _ ≤ s ^ 2 * ‖M t * N t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hps (sq_nonneg _)
        _ ≤ _ := le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hEn t))
    · obtain ⟨j, hj, htj, hNj⟩ := hbad t ht (lt_of_not_ge hp)
      have hNE : ‖N t‖ ^ 2 ≤ E t := by
        calc
          _ ≤ W j := hNj
          _ = (Set.Icc (j : ℝ) ((j : ℝ) + 1)).indicator (fun _ => W j) t := by
            rw [Set.indicator_of_mem htj]
          _ ≤ E t := by
            dsimp [E]
            apply Finset.single_le_sum (a := j)
            · intro l hl
              exact Set.indicator_nonneg (fun _ _ => hW l hl) t
            · exact hj
      have hps : ‖P t‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hRbound t) 2
      have hms : ‖M t‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMbound t ht) 2
      calc
        _ = ‖P t‖ ^ 2 * ‖M t‖ ^ 2 * ‖N t‖ ^ 2 := by
          simp only [norm_mul, mul_pow]
        _ ≤ R ^ 2 * m ^ 2 * E t := mul_le_mul
          (mul_le_mul hps hms (sq_nonneg _) (sq_nonneg _)) hNE (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hmono := integral_mono_ae hf hupper
    (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
  have hEint : (∫ t in Set.Icc (-T) T, E t) ≤ ∑ j ∈ J, W j := by
    rw [← hEsum]
    exact setIntegral_le_integral hEi (ae_of_all _ hEn)
  rw [integral_add (hmn.const_mul _) (hEi.integrableOn.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  rw [← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact hmono.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hEint
      (mul_nonneg (sq_nonneg R) (sq_nonneg m))))

lemma pd7d_finite_sum_energy_bound {α : Type*} (J : Finset α) (F : α → ℝ → ℂ)
    (T : ℝ) (hT : 0 ≤ T) (hF : ∀ j ∈ J, Continuous (F j)) :
    (∫ t in (-T)..T, ‖∑ j ∈ J, F j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (∫ t in (-T)..T, ‖F j t‖ ^ 2) := by
  have hsum : Continuous (fun t => ∑ j ∈ J, F j t) := continuous_finsetSum J hF
  have hsq : ∀ t, ‖∑ j ∈ J, F j t‖ ^ 2 ≤ (J.card : ℝ) * ∑ j ∈ J, ‖F j t‖ ^ 2 := by
    intro t
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun j => ‖F j t‖)
    have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le J (fun j => F j t)) 2
    exact hnorm.trans (by simpa using hcs)
  have hJint : ∀ j ∈ J, IntervalIntegrable (fun t => ‖F j t‖ ^ 2) volume (-T) T :=
    fun j hj => ((hF j hj).norm.pow 2).intervalIntegrable _ _
  have hsumInt : IntervalIntegrable (fun t => ∑ j ∈ J, ‖F j t‖ ^ 2) volume (-T) T :=
    (continuous_finsetSum J (fun j hj => (hF j hj).norm.pow 2)).intervalIntegrable _ _
  calc
    _ ≤ ∫ t in (-T)..T, (J.card : ℝ) * ∑ j ∈ J, ‖F j t‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) ((hsum.norm.pow 2).intervalIntegrable _ _)
        (hsumInt.const_mul _) (fun t _ => hsq t)
    _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hJint]

end ArtinPrimitiveRoots.TypeII.PD
