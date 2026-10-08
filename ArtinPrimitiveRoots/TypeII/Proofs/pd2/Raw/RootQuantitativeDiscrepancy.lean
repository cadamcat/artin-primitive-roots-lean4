import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootDiscrepancyScalar

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_root_quantitative_discrepancy
    (CK CT : ℝ) (hCK : 0 < CK) (hCT : 0 < CT)
    (hK : ∀ m : ℕ, ∀ hi : NeZero m, ∀ Ft : Fintype (ZMod m)ˣ, ∀ H K : ZMod m,
      ‖@pd2a_rootKSum m hi Ft H K‖ ≤ CK * (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) *
        (Nat.gcd (Nat.gcd H.val K.val) m : ℝ) ^ (1 / 4 : ℝ))
    (hτ : ∀ u : ℕ, 1 ≤ u → (u.divisors.card : ℝ) ≤ CT * (u : ℝ) ^ (1 / 100 : ℝ))
    (u S : ℕ) (hu : 0 < u) (hS : 0 < S) [NeZero (u * S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) (ac Nc av Nv : ℕ) (hNc : Nc ≤ u * S) :
    ‖(∑ z ∈ pd2a_rootGraph u S g₀, pd2a_rootIntervalDensity (u * S) ac Nc z.1 *
      pd2a_rootIntervalDensity (u * S) av Nv z.2) -
      ((pd2a_rootGraph u S g₀).card : ℂ) * (Nc : ℂ) * (Nv : ℂ) / ((u * S : ℕ) : ℂ) ^ 2‖ ≤
      (40804 * CK * CT) * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * ((Nv : ℝ) / u + 5) := by
  let D := pd2a_rootShared u S
  have hD : 0 < D := pd2a_rootShared_pos u S
  letI : NeZero D := ⟨hD.ne'⟩
  letI : NeZero (u * D) := ⟨(mul_pos hu hD).ne'⟩
  letI : NeZero (pd2a_rootUnshared u S) := ⟨(pd2a_rootUnshared_pos u S).ne'⟩
  let B := CK * (u : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * (S : ℝ) ^ (1 + 1 / 100 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : ∀ h k : ZMod (u * S), ‖pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k‖ ≤
      B * (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ) := by
    intro h k
    exact (pd2a_rootGraph_fourier_bound_of_kloosterman (1 / 100) CK (by norm_num) hCK hK
      u S hu hS hSq g₀ hdet hu₀ h k).1
  have hR : ∀ h k : ZMod (u * S), ‖pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k‖ ≤
      B * (Nat.gcd k.val u : ℝ) ^ (1 / 4 : ℝ) := by
    intro h k
    exact (pd2a_rootGraph_fourier_bound_of_kloosterman (1 / 100) CK (by norm_num) hCK hK
      u S hu hS hSq g₀ hdet hu₀ h k).2
  have hdisc := pd2a_density_fourier_discrepancy (u * S) u ac Nc av Nv (mul_pos hu hS) hu
    (dvd_mul_right u S) hNc (pd2a_rootGraph u S g₀) B hB hL hR
  have hLog : 0 ≤ 1 + Real.log ((u * S : ℕ) : ℝ) := by
    have hOne : (1 : ℝ) ≤ ((u * S : ℕ) : ℝ) := by exact_mod_cast mul_pos hu hS
    linarith [Real.log_nonneg hOne]
  calc
    _ ≤ 4 * B * (u.divisors.card : ℝ) * (1 + Real.log ((u * S : ℕ) : ℝ)) *
        ((Nv : ℝ) / ((u * S : ℕ) : ℝ) + 5 * (1 + Real.log ((u * S : ℕ) : ℝ))) := hdisc
    _ ≤ 4 * B * (CT * (u : ℝ) ^ (1 / 100 : ℝ)) * (1 + Real.log ((u * S : ℕ) : ℝ)) *
        ((Nv : ℝ) / ((u * S : ℕ) : ℝ) + 5 * (1 + Real.log ((u * S : ℕ) : ℝ))) := by
      gcongr
      exact hτ u hu
    _ ≤ _ := by
      dsimp [B]
      simp only [Nat.cast_mul]
      exact pd2a_root_discrepancy_scalar CK CT u S Nv hCK.le hCT.le (by exact_mod_cast hu)
        (by exact_mod_cast hS) (Nat.cast_nonneg Nv)

end ArtinPrimitiveRoots.TypeII.PD
