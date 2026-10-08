import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelComposition

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

lemma pd7d_product_jet_bound (f g : E → A) (u : E) (C D : ℝ)
    (n k : ℕ) (hk : k ≤ n) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfirst : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f u‖ ≤ C)
    (hsecond : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g u‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) u‖ ≤ (2 : ℝ) ^ n * C * D := by
  have hh := norm_iteratedFDeriv_mul_le hf hg u
    (by simp : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hsumChoose : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f u‖ * ‖iteratedFDeriv ℝ (k - i) g u‖ := hh
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hk
      have hkin : k - i ≤ n := (Nat.sub_le k i).trans hk
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfirst i hin) (by positivity)) (hsecond (k - i) hkin)
        (norm_nonneg _) (mul_nonneg (by positivity) hC)
    _ = (2 : ℝ) ^ k * C * D := by
      simp only [← Finset.sum_mul]
      rw [hsumChoose]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hk) hC) hD

end ArtinPrimitiveRoots.TypeII.PD
