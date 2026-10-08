import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootFixedCount

namespace ArtinPrimitiveRoots.TypeII.PD
set_option maxHeartbeats 1000000

lemma pd1c_root_rounded_product_error (u V S E Nc Nv d₂ d₃ : ℝ)
    (hu : 1 ≤ u) (hV : 1 ≤ V) (hS : 1 ≤ S) (hE₀ : 0 ≤ E) (hE₁ : E ≤ 1)
    (hNc₀ : 0 ≤ Nc) (hNv₀ : 0 ≤ Nv) (hNv₁ : Nv ≤ 16 * V)
    (hd₃₀ : 0 ≤ d₃) (hd₃₁ : d₃ ≤ 1)
    (hc : |Nc - u * d₃| ≤ 2) (hv : |Nv - V * d₂| ≤ 1) :
    |(u * E) * Nc * Nv / (u * S) ^ 2 - V * d₂ * d₃ * E / S ^ 2| ≤ 32 * V / u + 1 := by
  have hup : 0 < u := by linarith
  have hSp : 0 < S := by linarith
  have hS2 : 1 ≤ S ^ 2 := by nlinarith
  have hpref₀ : 0 ≤ E / S ^ 2 := by positivity
  have hpref₁ : E / S ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hSp)).mpr (hE₁.trans hS2)
  have hcu : |Nc / u - d₃| ≤ 2 / u := by
    have heq : Nc / u - d₃ = (Nc - u * d₃) / u := by field_simp
    rw [heq, abs_div, abs_of_pos hup]
    exact div_le_div_of_nonneg_right hc hup.le
  have hinner : |(Nc / u) * Nv - V * d₂ * d₃| ≤ 32 * V / u + 1 := by
    have heq : (Nc / u) * Nv - V * d₂ * d₃ = (Nc / u - d₃) * Nv + d₃ * (Nv - V * d₂) := by ring
    rw [heq]
    calc
      _ ≤ |(Nc / u - d₃) * Nv| + |d₃ * (Nv - V * d₂)| := abs_add_le _ _
      _ = |Nc / u - d₃| * Nv + d₃ * |Nv - V * d₂| := by rw [abs_mul, abs_of_nonneg hNv₀, abs_mul, abs_of_nonneg hd₃₀]
      _ ≤ (2 / u) * (16 * V) + 1 * 1 := add_le_add
        (mul_le_mul hcu hNv₁ hNv₀ (by positivity)) (mul_le_mul hd₃₁ hv (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have heq : (u * E) * Nc * Nv / (u * S) ^ 2 - V * d₂ * d₃ * E / S ^ 2 =
      (E / S ^ 2) * ((Nc / u) * Nv - V * d₂ * d₃) := by field_simp
  rw [heq, abs_mul, abs_of_nonneg hpref₀]
  calc
    _ ≤ 1 * (32 * V / u + 1) := mul_le_mul hpref₁ hinner (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma pd1c_rootEulerFactor_bounds (u S : ℕ) : 0 ≤ pd1c_rootEulerFactor u S ∧ pd1c_rootEulerFactor u S ≤ 1 := by
  have hFactor : ∀ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), 0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
    have hpos := pd1c_prime_euler_factor_pos p hpp
    have hInv : 0 ≤ 1 / (p : ℝ) := by positivity
    exact ⟨hpos.le, by linarith⟩
  constructor
  · exact Finset.prod_nonneg (fun p hp => (hFactor p hp).1)
  · calc
      _ ≤ ∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun p hp => (hFactor p hp).1) (fun p hp => (hFactor p hp).2)
      _ = 1 := by simp

end ArtinPrimitiveRoots.TypeII.PD
