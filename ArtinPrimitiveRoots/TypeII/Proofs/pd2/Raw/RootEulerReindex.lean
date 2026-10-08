import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTProgression
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootSeriesTail

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootEulerFactor (u S : ℕ) : ℝ :=
  ∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ))

lemma pd2a_sum_real_indicator (I : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    (∑ n ∈ I, if P n then c else 0) = c * ((I.filter P).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

lemma pd2a_rootEuler_reindex (S : ℕ) (a : ZMod S) (A B : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ u ∈ pd2a_natClosedInterval A B, if (u : ZMod S) = a then pd2a_rootEulerFactor u S else 0) =
      ∑ d ∈ Finset.range (⌊B⌋₊ + 1), if Nat.Coprime d S then
        (ArithmeticFunction.moebius d : ℝ) / d *
          (((pd2a_natClosedInterval A B).filter (fun u => d ∣ u ∧ (u : ZMod S) = a)).card : ℝ)
      else 0 := by
  have hB : 0 ≤ B := by linarith
  have hExpand : ∀ u ∈ pd2a_natClosedInterval A B,
      pd2a_rootEulerFactor u S = ∑ d ∈ Finset.range (⌊B⌋₊ + 1),
        if Nat.Coprime d S ∧ d ∣ u then (ArithmeticFunction.moebius d : ℝ) / d else 0 := by
    intro u hu
    obtain ⟨hulo, huhi⟩ := (pd2a_natClosedInterval_mem A B hB u).mp hu
    have hup : 0 < u := by
      have huR : 0 < (u : ℝ) := by linarith
      exact_mod_cast huR
    have huN : u ≤ ⌊B⌋₊ := (Nat.le_floor_iff hB).mpr huhi
    have hDiv : u.divisors = (Finset.range (⌊B⌋₊ + 1)).filter (fun d => d ∣ u) := by
      ext d
      constructor
      · intro hd
        have hdata := Nat.mem_divisors.mp hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((Nat.le_of_dvd hup hdata.1).trans huN)), hdata.1⟩
      · intro hd
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hup.ne'⟩
    rw [pd2a_rootEulerFactor, pd2a_root_euler_divisor_expansion u S hup, hDiv, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d S <;> by_cases hdu : d ∣ u <;>
      simp only [Nat.Coprime] at hc ⊢ <;> simp [hc, hdu]
  have hsum : (∑ u ∈ pd2a_natClosedInterval A B, if (u : ZMod S) = a then pd2a_rootEulerFactor u S else 0) =
      ∑ u ∈ pd2a_natClosedInterval A B, ∑ d ∈ Finset.range (⌊B⌋₊ + 1),
        if Nat.Coprime d S then (if d ∣ u ∧ (u : ZMod S) = a then (ArithmeticFunction.moebius d : ℝ) / d else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hur : (u : ZMod S) = a
    · rw [if_pos hur, hExpand u hu]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hc : Nat.Coprime d S <;> by_cases hdu : d ∣ u <;>
        simp only [Nat.Coprime] at hc ⊢ <;> simp [hc, hdu, hur]
    · rw [if_neg hur]
      simp only [hur, and_false, ite_false, ite_self, Finset.sum_const_zero]
  rw [hsum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d S
  · simp only [Nat.Coprime] at hc ⊢
    simp only [hc, ite_true]
    exact pd2a_sum_real_indicator _ _ _
  · simp only [Nat.Coprime] at hc ⊢
    simp [hc]

end ArtinPrimitiveRoots.TypeII.PD
