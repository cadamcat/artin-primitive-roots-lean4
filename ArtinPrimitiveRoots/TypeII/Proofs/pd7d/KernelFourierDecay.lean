import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelDerivativeMass
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FourierWeightAlgebra

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma pd7d_scaled_kernel_transform_decay (κ ψ : ℝ → ℝ) (R A₀ : ℝ) (hR : 0 ≤ R) (hA₀ : 0 ≤ A₀)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R) (j : ℕ) :
    ∃ CF : ℝ, 0 < CF ∧ ∀ L X lam : ℝ, 1 ≤ L → 1 ≤ X →
      |lam| ≤ 2 * Real.rpow L A₀ → ∀ v : PDPlane,
        let H := Real.rpow L (A₀ + 1)
        ‖pd7dFourier2 (pd7dScaledKernel κ ψ X lam) v‖ ≤
          CF * Real.rpow (1 + |v 0| / H) (-(j : ℝ)) * Real.rpow (1 + |v 1| / H) (-(j : ℝ)) := by
  obtain ⟨C₀, hC₀, hmass₀⟩ := pd7d_kernel_dominated_derivative_mass κ ψ R hR hκ hψ hκsupp hψsupp 0
  obtain ⟨Cj, hCj, hmassj⟩ := pd7d_kernel_dominated_derivative_mass κ ψ R hR hκ hψ hκsupp hψsupp j
  obtain ⟨C₂j, hC₂j, hmass₂j⟩ := pd7d_kernel_dominated_derivative_mass κ ψ R hR hκ hψ hκsupp hψsupp (2 * j)
  let aπ : ℝ := (1 / (2 * Real.pi)) ^ 2
  let D₀ := aπ * C₀
  let D₁ := aπ * Cj * (3 : ℝ) ^ j
  let D₂ := aπ * C₂j * (3 : ℝ) ^ (2 * j)
  let D := max D₀ (max D₁ D₂) + 1
  let CF := (4 : ℝ) ^ j * D
  have haπ : 0 < aπ := by dsimp [aπ]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  have hD₂ : 0 ≤ D₂ := by dsimp [D₂]; positivity
  have hD : 0 < D := by
    have hh := le_max_left D₀ (max D₁ D₂)
    dsimp [D]
    linarith
  have hD0le : D₀ ≤ D := (le_max_left _ _).trans (by dsimp [D]; linarith)
  have hD1le : D₁ ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [D]; linarith))
  have hD2le : D₂ ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [D]; linarith))
  refine ⟨CF, by dsimp [CF]; positivity, ?_⟩
  intro L X lam hL hX hlam v
  dsimp only
  let H := Real.rpow L (A₀ + 1)
  let B := 1 + |lam|
  have hLp : 0 < L := by linarith
  have hH : 0 < H := Real.rpow_pos_of_pos hLp _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpowA : 1 ≤ Real.rpow L A₀ := Real.one_le_rpow hL hA₀
  have hHrel : H = Real.rpow L A₀ * L := by
    calc
      _ = Real.rpow L A₀ * Real.rpow L 1 := Real.rpow_add hLp A₀ 1
      _ = _ := congrArg (fun z : ℝ => Real.rpow L A₀ * z) (Real.rpow_one L)
  have hpowH : Real.rpow L A₀ ≤ H := by
    rw [hHrel]
    nlinarith
  have hBH : B ≤ 3 * H := by dsimp [B]; linarith
  let hc := pd7d_scaled_kernel_hasCompactSupport κ ψ X lam R hX hR hκsupp hψsupp
  let hs := pd7d_scaled_kernel_contDiff κ ψ X lam hκ hψ
  let F : SchwartzMap PDPlane ℂ := hc.toSchwartzMap hs
  have hF : (F : PDPlane → ℂ) = pd7dScaledKernel κ ψ X lam := rfl
  let s := ‖pd7dFourier2 (F : PDPlane → ℂ) v‖
  have hs0 : 0 ≤ s := norm_nonneg _
  have hbaseMass : (∫ u : PDPlane, ‖F u‖) ≤ C₀ := by
    have hh := hmass₀ X lam hX (F : PDPlane → ℂ) F.integrable (fun u => by
      rw [norm_iteratedFDeriv_zero]
      exact le_rfl)
    simpa only [pow_zero, mul_one] using hh
  have hcoordMass (i : Fin 2) : (∫ u : PDPlane, ‖pd7dPartial i j F u‖) ≤ Cj * B ^ j := by
    exact hmassj X lam hX (pd7dPartial i j F : PDPlane → ℂ) (pd7dPartial i j F).integrable
      (fun u => by have hh := pd7dPartial_norm F i j u; rw [hF] at hh; exact hh)
  have hmixedMass : (∫ u : PDPlane, ‖pd7dPartial 0 j (pd7dPartial 1 j F) u‖) ≤ C₂j * B ^ (2 * j) := by
    exact hmass₂j X lam hX (pd7dPartial 0 j (pd7dPartial 1 j F) : PDPlane → ℂ)
      (pd7dPartial 0 j (pd7dPartial 1 j F)).integrable
      (fun u => by have hh := pd7dPartial_mixed_norm F j u; rw [hF] at hh; exact hh)
  have hbase : s ≤ D := by
    calc
      _ ≤ aπ * (∫ u : PDPlane, ‖F u‖) := pd7dFourier2_norm_le _ _
      _ ≤ aπ * C₀ := mul_le_mul_of_nonneg_left hbaseMass haπ.le
      _ ≤ D := hD0le
  have hcoord (i : Fin 2) : |v i| ^ j * s ≤ D * H ^ j := by
    have hweight := pd7dFourier2_partial_weight_bound F i j v
    have hBpow : B ^ j ≤ (3 * H) ^ j := pow_le_pow_left₀ hB hBH j
    calc
      _ ≤ aπ * (∫ u : PDPlane, ‖pd7dPartial i j F u‖) := hweight
      _ ≤ aπ * (Cj * B ^ j) := mul_le_mul_of_nonneg_left (hcoordMass i) haπ.le
      _ ≤ aπ * (Cj * (3 * H) ^ j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBpow hCj.le) haπ.le
      _ = D₁ * H ^ j := by dsimp [D₁]; rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD1le (pow_nonneg hH.le j)
  have hmixed : |v 0| ^ j * |v 1| ^ j * s ≤ D * H ^ (2 * j) := by
    have hweight := pd7dFourier2_mixed_weight_bound F j v
    have hBpow : B ^ (2 * j) ≤ (3 * H) ^ (2 * j) := pow_le_pow_left₀ hB hBH _
    calc
      _ ≤ aπ * (∫ u : PDPlane, ‖pd7dPartial 0 j (pd7dPartial 1 j F) u‖) := hweight
      _ ≤ aπ * (C₂j * B ^ (2 * j)) := mul_le_mul_of_nonneg_left hmixedMass haπ.le
      _ ≤ aπ * (C₂j * (3 * H) ^ (2 * j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBpow hC₂j.le) haπ.le
      _ = D₂ * H ^ (2 * j) := by dsimp [D₂]; rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD2le (pow_nonneg hH.le _)
  have hnorm₀ := pd7d_normalize_weight |v 0| s D H j hH (hcoord 0)
  have hnorm₁ := pd7d_normalize_weight |v 1| s D H j hH (hcoord 1)
  have hnorm₂ := pd7d_normalize_mixed_weight |v 0| |v 1| s D H j hH hmixed
  have hfinal := pd7d_four_weight_decay (|v 0| / H) (|v 1| / H) s D j
    (div_nonneg (abs_nonneg _) hH.le) (div_nonneg (abs_nonneg _) hH.le) hs0 hD.le
    hbase hnorm₀ hnorm₁ hnorm₂
  exact hfinal

end ArtinPrimitiveRoots.TypeII.PD
