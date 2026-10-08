import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory Function
set_option autoImplicit false

noncomputable def pd7dFrequencyWindow (S : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ioc (((n + 1 : ℕ) : ℝ) * S) (((n + 2 : ℕ) : ℝ) * S)

lemma pd7d_frequency_windows_union (S : ℝ) (hS : 0 < S) :
    (⋃ n : ℕ, pd7dFrequencyWindow S n) = Set.Ioi S := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    have hnlo := hn.1
    have hncast : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hh := mul_le_mul_of_nonneg_right hncast hS.le
    apply Set.mem_Ioi.mpr
    simpa only [one_mul] using lt_of_le_of_lt hh hnlo
  · intro ht
    have htpos : S < t := Set.mem_Ioi.mp ht
    obtain ⟨N, hN⟩ := exists_nat_gt (t / S)
    let a := fun n : ℕ => ((n + 1 : ℕ) : ℝ) * S
    have hbound : t ≤ a N := by
      have hh := (div_lt_iff₀ hS).mp hN
      dsimp [a]
      push_cast
      nlinarith
    have hstart : a 0 = S := by simp [a]
    have htI : t ∈ Set.Ioc (a 0) (a N) := ⟨by rw [hstart]; exact htpos, hbound⟩
    have hcover := Ioc_subset_biUnion_Ioc N a htI
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hcover
    obtain ⟨_, htn⟩ := Set.mem_iUnion.mp hn
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact htn

lemma pd7d_frequency_windows_disjoint (S : ℝ) (hS : 0 < S) :
    Pairwise (Disjoint on pd7dFrequencyWindow S) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hidx : ((i + 2 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i + 2 ≤ j + 1)
    have hh := mul_le_mul_of_nonneg_right hidx hS.le
    exact not_lt_of_ge (hti.2.trans hh) htj.1
  · have hidx : ((j + 2 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j + 2 ≤ i + 1)
    have hh := mul_le_mul_of_nonneg_right hidx hS.le
    exact not_lt_of_ge (htj.2.trans hh) hti.1

lemma pd7d_integral_frequency_windows (S : ℝ) (hS : 0 < S) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioi S)) :
    (∫ t in Set.Ioi S, f t) = ∑' n : ℕ, ∫ t in pd7dFrequencyWindow S n, f t := by
  rw [← pd7d_frequency_windows_union S hS] at hf ⊢
  exact integral_iUnion (fun _ => measurableSet_Ioc) (pd7d_frequency_windows_disjoint S hS) hf

end ArtinPrimitiveRoots.TypeII.PD
