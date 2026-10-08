import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootFrequencyArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootKSum (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] (H K : ZMod m) : ℂ :=
  ∑ c : (ZMod m)ˣ, ZMod.stdAddChar (H * (c : ZMod m) + K * ((c⁻¹ : (ZMod m)ˣ) : ZMod m))

lemma pd2a_rootGraph_fourier_bound_of_kloosterman
    (ε CK : ℝ) (hε : 0 < ε) (hCK : 0 < CK)
    (hK : ∀ m : ℕ, ∀ hi : NeZero m, ∀ Ft : Fintype (ZMod m)ˣ, ∀ H K : ZMod m,
      ‖@pd2a_rootKSum m hi Ft H K‖ ≤ CK * (m : ℝ) ^ (3 / 4 + ε) *
        (Nat.gcd (Nat.gcd H.val K.val) m : ℝ) ^ (1 / 4 : ℝ))
    (u S : ℕ) (hu : 0 < u) (hS : 0 < S) [NeZero (u * S)]
    [NeZero (u * pd2a_rootShared u S)] [NeZero (pd2a_rootShared u S)]
    [NeZero (pd2a_rootUnshared u S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) (h k : ZMod (u * S)) :
    ‖pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k‖ ≤
      CK * (u : ℝ) ^ (3 / 4 + ε) * (S : ℝ) ^ (1 + ε) * (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ) ∧
    ‖pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k‖ ≤
      CK * (u : ℝ) ^ (3 / 4 + ε) * (S : ℝ) ^ (1 + ε) * (Nat.gcd k.val u : ℝ) ^ (1 / 4 : ℝ) := by
  let D := pd2a_rootShared u S
  let M := u * D
  have hD : 0 < D := pd2a_rootShared_pos u S
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hur : 0 < (u : ℝ) := by exact_mod_cast hu
  have hSr : 0 < (S : ℝ) := by exact_mod_cast hS
  have hDleS : (D : ℝ) ≤ S := by exact_mod_cast Nat.le_of_dvd hS (pd2a_rootShared_dvd_modulus u S hSq)
  obtain ⟨α, phase, hphase, hα, hSpec⟩ := pd2a_rootGraph_fourier_decomposition u S hu hS hSq g₀ hdet hu₀ h k
  let Γ := pd2a_rootGamma u S
  let Hj := fun j : ZMod D => (Γ : ZMod M) * (h.val : ZMod M) + (u : ZMod M) * (j.val : ZMod M)
  let Kj : ZMod M := (Γ : ZMod M) * (k.val : ZMod M) * (α : ZMod M)
  have hGH : ∀ j : ZMod D, Nat.gcd (Hj j).val u = Nat.gcd h.val u := fun j =>
    pd2a_shifted_unit_frequency_gcd u D Γ h.val j.val
  have hGK : Nat.gcd Kj.val u = Nat.gcd k.val u := pd2a_product_unit_frequency_gcd u D Γ α k.val
  have hGLeft : ∀ j : ZMod D, Nat.gcd (Nat.gcd (Hj j).val Kj.val) M ≤ D * Nat.gcd h.val u := by
    intro j
    simpa only [hGH j] using pd2a_gcd_pair_product_bound_left u D (Hj j).val Kj.val hu hD
  have hGRight : ∀ j : ZMod D, Nat.gcd (Nat.gcd (Hj j).val Kj.val) M ≤ D * Nat.gcd k.val u := by
    intro j
    simpa only [hGK] using pd2a_gcd_pair_product_bound_right u D (Hj j).val Kj.val hu hD
  have hSpec' : pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k =
      phase * (D : ℂ)⁻¹ * ∑ j : ZMod D, ZMod.stdAddChar (-j * ((g₀ 0 1).val : ZMod D)) * pd2a_rootKSum M (Hj j) Kj := by
    dsimp [pd2a_rootKSum, Hj, Kj, Γ, M, D]
    convert hSpec using 1 <;> congr!
  have hGeneric : ∀ P : ℕ,
      (∀ j : ZMod D, Nat.gcd (Nat.gcd (Hj j).val Kj.val) M ≤ D * P) →
      ‖pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k‖ ≤
        CK * (u : ℝ) ^ (3 / 4 + ε) * (S : ℝ) ^ (1 + ε) * (P : ℝ) ^ (1 / 4 : ℝ) := by
    intro P hG
    let B := CK * (u : ℝ) ^ (3 / 4 + ε) * (S : ℝ) ^ (1 + ε) * (P : ℝ) ^ (1 / 4 : ℝ)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hDPow : (D : ℝ) ^ (3 / 4 + ε) * (D : ℝ) ^ (1 / 4 : ℝ) = (D : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_add hDr]
      congr 1
      ring
    have hEach : ∀ j : ZMod D, ‖pd2a_rootKSum M (Hj j) Kj‖ ≤ B := by
      intro j
      have hBound := hK M inferInstance inferInstance (Hj j) Kj
      have hGpow : (Nat.gcd (Nat.gcd (Hj j).val Kj.val) M : ℝ) ^ (1 / 4 : ℝ) ≤
          ((D : ℝ) * P) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast hG j) (by norm_num)
      calc
        _ ≤ CK * (M : ℝ) ^ (3 / 4 + ε) * (Nat.gcd (Nat.gcd (Hj j).val Kj.val) M : ℝ) ^ (1 / 4 : ℝ) := hBound
        _ ≤ CK * (M : ℝ) ^ (3 / 4 + ε) * ((D : ℝ) * P) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hGpow (by positivity)
        _ = CK * (u : ℝ) ^ (3 / 4 + ε) * (D : ℝ) ^ (1 + ε) * (P : ℝ) ^ (1 / 4 : ℝ) := by
          dsimp [M]
          rw [Nat.cast_mul, Real.mul_rpow hur.le hDr.le, Real.mul_rpow hDr.le (Nat.cast_nonneg P)]
          calc
            _ = CK * (u : ℝ) ^ (3 / 4 + ε) * ((D : ℝ) ^ (3 / 4 + ε) * (D : ℝ) ^ (1 / 4 : ℝ)) * (P : ℝ) ^ (1 / 4 : ℝ) := by ring
            _ = _ := by rw [hDPow]
        _ ≤ B := by
          dsimp [B]
          gcongr
    rw [hSpec', norm_mul, norm_mul, hphase, one_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (D : ℝ)⁻¹ * ∑ j : ZMod D, ‖ZMod.stdAddChar (-j * ((g₀ 0 1).val : ZMod D)) * pd2a_rootKSum M (Hj j) Kj‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (D : ℝ)⁻¹ * ∑ j : ZMod D, ‖pd2a_rootKSum M (Hj j) Kj‖ := by simp only [norm_mul, pd2a_root_character_norm, one_mul]
      _ ≤ (D : ℝ)⁻¹ * ∑ j : ZMod D, B := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => hEach j)) (by positivity)
      _ = B := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ hDr.ne', one_mul]
  exact ⟨hGeneric _ hGLeft, hGeneric _ hGRight⟩

end ArtinPrimitiveRoots.TypeII.PD
