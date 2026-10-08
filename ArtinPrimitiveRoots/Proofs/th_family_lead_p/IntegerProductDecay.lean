import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DirectionalFourierBound
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

/-- Integer-coordinate directional decay controls the product inverse-square weight,
including the zero tuple and the empty product. -/
theorem theta_integer_product_decay
    (n : ℕ) (k : Fin n → ℤ) (z C0 CN : ℝ)
    (hz : 0 ≤ z) (hC0 : 0 ≤ C0) (hCN : 0 ≤ CN)
    (hzero : z ≤ C0)
    (hdir : ∀ i, |(k i : ℝ)| ^ (2 * n) * z ≤ CN) :
    z ≤ (C0 + (2 : ℝ) ^ (2 * n) * CN) *
      ∏ i, ((1 + |(k i : ℝ)|) ^ 2)⁻¹ := by
  by_cases hk : k = 0
  · have hzsum : z ≤ C0 + (2 : ℝ) ^ (2 * n) * CN :=
      hzero.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hCN))
    simpa [hk] using hzsum
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    simpa only [funext_iff, not_forall, Pi.zero_apply] using hk
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => |(k i : ℝ)|) ⟨i, Finset.mem_univ i⟩
  let r : ℝ := |(k j : ℝ)|
  have hiabs : (1 : ℤ) ≤ |k i| := Int.add_one_le_iff.mpr (abs_pos.mpr hi)
  have hiabsR : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast hiabs
  have hr : 1 ≤ r := hiabsR.trans (hmax i (Finset.mem_univ i))
  let Q : ℝ := ∏ i, (1 + |(k i : ℝ)|) ^ 2
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact Finset.prod_pos fun i _ => pow_pos (by positivity) 2
  have hQbound : Q ≤ (2 : ℝ) ^ (2 * n) * r ^ (2 * n) := by
    calc
      Q ≤ ∏ _i : Fin n, (1 + r) ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => sq_nonneg (1 + |(k i : ℝ)|))
          (fun i _ => pow_le_pow_left₀ (by positivity)
            (add_le_add (le_refl (1 : ℝ)) (hmax i (Finset.mem_univ i))) 2)
      _ = ((1 + r) ^ 2) ^ n := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (1 + r) ^ (2 * n) := by rw [pow_mul]
      _ ≤ (2 * r) ^ (2 * n) :=
        pow_le_pow_left₀ (by positivity) (by linarith [hr]) (2 * n)
      _ = (2 : ℝ) ^ (2 * n) * r ^ (2 * n) := mul_pow 2 r (2 * n)
  have hzQ : z * Q ≤ (2 : ℝ) ^ (2 * n) * CN := by
    calc
      z * Q ≤ z * ((2 : ℝ) ^ (2 * n) * r ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left hQbound hz
      _ = (2 : ℝ) ^ (2 * n) * (r ^ (2 * n) * z) := by ring
      _ ≤ (2 : ℝ) ^ (2 * n) * CN :=
        mul_le_mul_of_nonneg_left (hdir j) (by positivity)
  have hzQ' : z * Q ≤ C0 + (2 : ℝ) ^ (2 * n) * CN :=
    hzQ.trans (le_add_of_nonneg_left hC0)
  have hdiv : z ≤ (C0 + (2 : ℝ) ^ (2 * n) * CN) / Q :=
    (le_div_iff₀ hQpos).mpr hzQ'
  simpa only [div_eq_mul_inv, Q, Finset.prod_inv_distrib] using hdiv

end ArtinPrimitiveRoots.Proofs.majorant_sol
