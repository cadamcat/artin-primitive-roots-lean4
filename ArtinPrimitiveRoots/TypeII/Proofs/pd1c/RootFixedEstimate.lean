import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootRoundingProduct
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCountingInputs

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_fixedRootCount_estimate (inputs : pd1c_RootCountingInputs)
    (u : ℕ) (V : ℝ) (S : ℕ) (hu : 0 < u) (hV : 1 ≤ V) (hS : 0 < S) [NeZero (u * S)]
    (hSq : Squarefree S) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
    (hdet : Matrix.det g₀ = 1) (hu₀ : (u : ZMod S) = g₀ 0 0)
    (l₂ r₂ l₃ r₃ : ℝ) (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 16)
    (hl₃ : 0 ≤ l₃) (hlr₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    |pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ -
      V * (r₂ - l₂) * (r₃ - l₃) * pd1c_rootEulerFactor u S / (S : ℝ) ^ 2| ≤
      (16 * (40804 * inputs.CK * inputs.CT) + 32) * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * (V / u + 5) := by
  let ac := pd1c_rootCStart u l₃
  let Nc := pd1c_rootCLength u l₃ r₃
  let av := pd1c_intervalStart (l₂ * V)
  let Nv := pd1c_intervalLength (l₂ * V) (r₂ * V)
  let E := pd1c_rootEulerFactor u S
  let D := 40804 * inputs.CK * inputs.CT
  let G := pd1c_rootGraph u S g₀
  let Main := (G.card : ℝ) * (Nc : ℝ) * (Nv : ℝ) / ((u * S : ℕ) : ℝ) ^ 2
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hVp : 0 < V := by linarith
  have hR2 : 0 ≤ r₂ := by linarith
  have hA : 0 ≤ l₂ * V := by positivity
  have hAB : l₂ * V ≤ r₂ * V := mul_le_mul_of_nonneg_right hlr₂ hVp.le
  obtain ⟨hNcNat, hNcErr⟩ := pd1c_rootCLength_bounds u hu l₃ r₃ hl₃ hlr₃ hr₃
  have hNcM : Nc ≤ u * S := hNcNat.trans (by simpa using Nat.mul_le_mul_left u hS)
  have hNvErr : |(Nv : ℝ) - V * (r₂ - l₂)| ≤ 1 := by
    have h := pd1c_intervalLength_error (l₂ * V) (r₂ * V) hA hAB
    convert h using 1 <;> dsimp [Nv] <;> ring
  have hNvMax : (Nv : ℝ) ≤ 16 * V := by
    have hupper := (abs_le.mp hNvErr).2
    have hwidth : r₂ - l₂ ≤ 15 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hwidth hVp.le]
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by norm_num) inputs.CK_pos.le) inputs.CT_pos.le
  have hDisc := pd1c_root_quantitative_discrepancy inputs.CK inputs.CT inputs.CK_pos inputs.CT_pos
    inputs.kloosterman inputs.divisors u S hu hS hSq g₀ hdet hu₀ ac Nc av Nv hNcM
  have hDensity := pd1c_fixedRootCount_density u V S hu hS g₀ hu₀ l₂ r₂ l₃ r₃ hVp (by linarith) hlr₂ hl₃ hlr₃ hr₃
  have hDiff : ((pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ - Main : ℝ) : ℂ) =
      (∑ z ∈ G, pd1c_rootIntervalDensity (u * S) ac Nc z.1 * pd1c_rootIntervalDensity (u * S) av Nv z.2) -
        (G.card : ℂ) * (Nc : ℂ) * (Nv : ℂ) / ((u * S : ℕ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_sub, hDensity]
    dsimp [Main, G, ac, Nc, av, Nv]
    push_cast
    rfl
  have hDiscR : |pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ - Main| ≤
      D * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * ((Nv : ℝ) / u + 5) := by
    rw [← hDiff, Complex.norm_real, Real.norm_eq_abs] at hDisc
    exact hDisc
  have hMass : (G.card : ℝ) = (u : ℝ) * E := pd1c_rootGraph_mass u S hu hS hSq g₀ hdet hu₀
  have hRound : |Main - V * (r₂ - l₂) * (r₃ - l₃) * E / (S : ℝ) ^ 2| ≤ 32 * V / u + 1 := by
    dsimp [Main]
    rw [hMass, Nat.cast_mul]
    exact pd1c_root_rounded_product_error u V S E Nc Nv (r₂ - l₂) (r₃ - l₃)
      huR hV hSR (pd1c_rootEulerFactor_bounds u S).1 (pd1c_rootEulerFactor_bounds u S).2
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hNvMax (by linarith) (by linarith)
      hNcErr hNvErr
  have hScale : 1 ≤ (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) := by
    have hU := Real.one_le_rpow huR (by norm_num : (0 : ℝ) ≤ 99 / 100)
    have hS := Real.one_le_rpow hSR (by norm_num : (0 : ℝ) ≤ 2)
    have h := mul_le_mul hU hS (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa only [one_mul] using h
  have hMean : 0 ≤ V / (u : ℝ) + 5 := by positivity
  calc
    _ ≤ |pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ - Main| +
        |Main - V * (r₂ - l₂) * (r₃ - l₃) * E / (S : ℝ) ^ 2| := abs_sub_le _ _ _
    _ ≤ D * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * ((Nv : ℝ) / u + 5) + (32 * V / u + 1) :=
      add_le_add hDiscR hRound
    _ ≤ (16 * D + 32) * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * (V / u + 5) := by
      have hRatio : (Nv : ℝ) / u ≤ 16 * (V / u) := by
        have h := div_le_div_of_nonneg_right hNvMax (show (0 : ℝ) ≤ u by positivity)
        exact h.trans_eq (by ring)
      have hFirst : D * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * ((Nv : ℝ) / u + 5) ≤
          16 * D * ((u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ)) * (V / u + 5) := by
        have hc : 0 ≤ D * ((u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show (Nv : ℝ) / u + 5 ≤ 16 * (V / u + 5) by linarith) hc]
      have hSecond : 32 * V / u + 1 ≤ 32 * ((u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ)) * (V / u + 5) := by
        calc
          32 * V / u + 1 ≤ 32 * (V / u + 5) := by
            have heq : 32 * V / u = 32 * (V / u) := by ring
            rw [heq]
            linarith
          _ ≤ 32 * (((u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ)) * (V / u + 5)) :=
            mul_le_mul_of_nonneg_left (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hScale hMean) (by norm_num)
          _ = _ := by ring
      nlinarith only [hFirst, hSecond]

end ArtinPrimitiveRoots.TypeII.PD
