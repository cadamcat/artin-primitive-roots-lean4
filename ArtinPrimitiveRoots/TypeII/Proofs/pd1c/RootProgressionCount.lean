import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootRounding

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd1c_natClosedInterval (A B : ℝ) : Finset ℕ := Finset.Icc ⌈A⌉₊ ⌊B⌋₊

lemma pd1c_natClosedInterval_mem (A B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    n ∈ pd1c_natClosedInterval A B ↔ A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B := by
  simp only [pd1c_natClosedInterval, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hB]

lemma pd1c_natClosedInterval_card (A B : ℝ) :
    (pd1c_natClosedInterval A B).card = pd1c_intervalLength A B := by
  simp only [pd1c_natClosedInterval, Nat.card_Icc, pd1c_intervalLength]

lemma pd1c_progression_interval_error (Q r : ℕ) (hQ : 0 < Q) (hr : r < Q)
    (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    |(((pd1c_natClosedInterval A B).filter (fun n => n % Q = r)).card : ℝ) - (B - A) / Q| ≤ 2 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hrR : (r : ℝ) < Q := by exact_mod_cast hr
  by_cases hBr : B < (r : ℝ)
  · have hEmpty : (pd1c_natClosedInterval A B).filter (fun n => n % Q = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      have hHi := ((pd1c_natClosedInterval_mem A B hB n).mp hmem.1).2
      have hrn : r ≤ n := by rw [← hmem.2]; exact Nat.mod_le n Q
      have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
      linarith
    rw [hEmpty, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (div_nonneg (sub_nonneg.mpr hAB) hQR.le)]
    have hwidth : B - A ≤ (Q : ℝ) := by linarith
    have hdiv := (div_le_one hQR).mpr hwidth
    linarith
  · have hBr : (r : ℝ) ≤ B := le_of_not_gt hBr
    let L := (A - (r : ℝ)) / Q
    let H := (B - (r : ℝ)) / Q
    let L₀ := max 0 L
    have hH : 0 ≤ H := div_nonneg (sub_nonneg.mpr hBr) hQR.le
    have hLH : L ≤ H := div_le_div_of_nonneg_right (by linarith) hQR.le
    have hL₀ : 0 ≤ L₀ := le_max_left _ _
    have hL₀H : L₀ ≤ H := max_le hH hLH
    have hLlow : -1 < L := by
      dsimp [L]
      apply (lt_div_iff₀ hQR).mpr
      linarith
    have hGap : 0 ≤ L₀ - L ∧ L₀ - L ≤ 1 := by
      dsimp [L₀]
      constructor
      · exact sub_nonneg.mpr (le_max_right _ _)
      · rcases le_total 0 L with hL | hL
        · rw [max_eq_right hL]
          norm_num
        · rw [max_eq_left hL]
          linarith
    have hImage : (pd1c_natClosedInterval A B).filter (fun n => n % Q = r) =
        (pd1c_natClosedInterval L₀ H).image (fun k => Q * k + r) := by
      ext n
      constructor
      · intro hn
        have hmem := Finset.mem_filter.mp hn
        obtain ⟨hLo, hHi⟩ := (pd1c_natClosedInterval_mem A B hB n).mp hmem.1
        have hnEq : Q * (n / Q) + r = n := by
          have h := Nat.mod_add_div n Q
          rw [hmem.2] at h
          omega
        have hnEqR : (Q : ℝ) * (n / Q : ℕ) + r = n := by exact_mod_cast hnEq
        have hkLo : L ≤ ((n / Q : ℕ) : ℝ) := by
          apply (div_le_iff₀ hQR).mpr
          nlinarith
        have hkHi : ((n / Q : ℕ) : ℝ) ≤ H := by
          apply (le_div_iff₀ hQR).mpr
          nlinarith
        exact Finset.mem_image.mpr ⟨n / Q, (pd1c_natClosedInterval_mem L₀ H hH _).mpr
          ⟨max_le (Nat.cast_nonneg _) hkLo, hkHi⟩, hnEq⟩
      · intro hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        obtain ⟨hLo, hHi⟩ := (pd1c_natClosedInterval_mem L₀ H hH k).mp hk
        have hLk : L ≤ (k : ℝ) := (le_max_right 0 L).trans hLo
        have hLo' : A ≤ ((Q * k + r : ℕ) : ℝ) := by
          have h := (div_le_iff₀ hQR).mp hLk
          push_cast
          nlinarith
        have hHi' : ((Q * k + r : ℕ) : ℝ) ≤ B := by
          have h := (le_div_iff₀ hQR).mp hHi
          push_cast
          nlinarith
        exact Finset.mem_filter.mpr ⟨(pd1c_natClosedInterval_mem A B hB _).mpr ⟨hLo', hHi'⟩,
          by simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr]⟩
    have hinj : Function.Injective (fun k : ℕ => Q * k + r) := fun a b hab =>
      Nat.mul_left_cancel hQ (Nat.add_right_cancel hab)
    rw [hImage, Finset.card_image_of_injective _ hinj, pd1c_natClosedInterval_card]
    have hround := pd1c_intervalLength_error L₀ H hL₀ hL₀H
    have hwidth : (B - A) / (Q : ℝ) = H - L := by dsimp [H, L]; ring
    rw [hwidth, abs_le]
    rw [abs_le] at hround
    constructor <;> linarith [hGap.1, hGap.2]

end ArtinPrimitiveRoots.TypeII.PD
