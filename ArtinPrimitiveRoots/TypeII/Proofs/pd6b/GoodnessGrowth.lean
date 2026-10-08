import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.ErrorDecay

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- Polynomial endpoint bounds absorb the model, boundary and residue remainders. -/
theorem goodness_majorant_decay (A C a rhoCoeff B R Cr cg ε γ CN CQ CZ : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hrhoCoeff : 0 < rhoCoeff) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hCr : 0 < Cr) (hcg : 0 < cg) (hε : 0 < ε) (hγ : 0 < γ)
    (hCN : 0 ≤ CN) (hCQ : 0 ≤ CQ) (hCZ : 0 ≤ CZ) :
    ∃ CA L₀ : ℝ, 0 < CA ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ U V Y σ Q Z D : ℝ, 0 < U → 0 < V → 1 ≤ Y → 0 ≤ σ → 0 ≤ Q → 0 ≤ Z →
      σ ≤ Real.exp (CN * Real.rpow L (21 / 100 : ℝ)) →
      Q ≤ Real.exp (CQ * Real.rpow L (21 / 100 : ℝ)) →
      Z ≤ 25 * Real.exp (CZ * Real.rpow L (21 / 100 : ℝ)) →
      (let H := 32 * B * Real.rpow L a / Y
       D ≤ U * V * rhoCoeff *
          (27 * ((17 + H * (17 * (2 * R * Y + 1))) * (15 * Real.exp (-cg * Real.rpow L (1 / 10 : ℝ)))) +
            3 * Real.exp (Real.rpow L (9 / 10 : ℝ) - ε * L) * Z * (1 + H)) +
          (475 * Cr * U * V * Real.exp (-γ * L)) * σ * Q * Z * (1 + H)) →
      2 * Real.rpow L (4 * C) * D ≤ CA * U * V * Real.rpow L (-A) := by
  let CM := 27 * (17 * (1 + 32 * B * (2 * R + 1))) * 15
  let CB := 3 * 25 * (1 + 32 * B)
  let CE := 475 * Cr * 25 * (1 + 32 * B)
  let CT := CN + CQ + CZ
  let γ₀ := min ε γ
  have hCT : 0 ≤ CT := by dsimp [CT]; positivity
  have hγ₀ : 0 < γ₀ := lt_min hε hγ
  have hCM : 0 < CM := by dsimp [CM]; positivity
  have hCB : 0 < CB := by dsimp [CB]; positivity
  have hCE : 0 < CE := by dsimp [CE]; positivity
  obtain ⟨Lm, hLm, modelDecay⟩ := modelError_logPowerDecay A (a + 4 * C) cg (1 / 10 : ℝ) hcg (by norm_num)
  obtain ⟨Le, hLe, errorDecay⟩ := gridError_logPowerDecay A (a + 4 * C) CT γ₀ hCT hγ₀
  let CA := 2 * (rhoCoeff * CM + rhoCoeff * CB + CE)
  refine ⟨CA, max Lm Le, by dsimp [CA]; positivity, hLm.trans (le_max_left _ _), ?_⟩
  intro L hL U V Y σ Q Z D hU hV hY hσ hQ hZ hσBound hQBound hZBound hD
  have hLone : 1 ≤ L := (hLm.trans (le_max_left _ _)).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  let P := Real.rpow L a
  let q := Real.rpow L (21 / 100 : ℝ)
  let v := Real.rpow L (9 / 10 : ℝ)
  let H := 32 * B * P / Y
  let g := Real.exp (-cg * Real.rpow L (1 / 10 : ℝ))
  let e := Real.exp (CT * q + v - γ₀ * L)
  have hPone : 1 ≤ P := Real.one_le_rpow hLone ha
  have hP : 0 ≤ P := Real.rpow_nonneg hLpos.le a
  have hq : 0 ≤ q := Real.rpow_nonneg hLpos.le _
  have hv : 0 ≤ v := Real.rpow_nonneg hLpos.le _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHbound : H ≤ 32 * B * P := by
    dsimp [H]
    apply (div_le_iff₀ hYpos).mpr
    have hn : 0 ≤ 32 * B * P := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hY hn
  have hOneH : 1 + H ≤ (1 + 32 * B) * P := by nlinarith
  have hInvY : Y⁻¹ ≤ 1 := (inv_le_one₀ hYpos).mpr hY
  have hHRY : H * (2 * R * Y + 1) ≤ (32 * B * P) * (2 * R + 1) := by
    calc
      _ = (32 * B * P) * (2 * R + Y⁻¹) := by dsimp [H]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hInvY) (by positivity)
  have hModelFactor : 17 + H * (17 * (2 * R * Y + 1)) ≤
      (17 * (1 + 32 * B * (2 * R + 1))) * P := by nlinarith
  have hModel : 27 * ((17 + H * (17 * (2 * R * Y + 1))) * (15 * g)) ≤ CM * P * g := by
    have ht := mul_le_mul_of_nonneg_right hModelFactor (by positivity : 0 ≤ 15 * g)
    have ht' := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 27)
    dsimp [CM]
    nlinarith
  have hBoundaryExp : Real.exp (CZ * q + v - ε * L) ≤ e := by
    apply Real.exp_le_exp.mpr
    have hcoeff : CZ ≤ CT := by dsimp [CT]; linarith
    have hc := mul_le_mul_of_nonneg_right hcoeff hq
    have hg := mul_le_mul_of_nonneg_right (min_le_left ε γ) hLpos.le
    dsimp [e, γ₀]
    linarith
  have hBoundary : 3 * Real.exp (v - ε * L) * Z * (1 + H) ≤ CB * P * e := by
    calc
      _ ≤ 3 * Real.exp (v - ε * L) * (25 * Real.exp (CZ * q)) * ((1 + 32 * B) * P) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hZBound (by positivity)) hOneH (by positivity) (by positivity)
      _ = CB * P * Real.exp (CZ * q + v - ε * L) := by
        dsimp [CB]
        rw [show CZ * q + v - ε * L = (v - ε * L) + CZ * q by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBoundaryExp (by positivity)
  have hResidueExp : Real.exp (CT * q - γ * L) ≤ e := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right (min_le_right ε γ) hLpos.le
    dsimp [e, γ₀]
    linarith
  have hResidue : (475 * Cr * U * V * Real.exp (-γ * L)) * σ * Q * Z * (1 + H) ≤
      U * V * (CE * P * e) := by
    have hσQ := mul_le_mul hσBound hQBound hQ (Real.exp_pos _).le
    have hσQZ := mul_le_mul hσQ hZBound hZ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    calc
      _ ≤ (475 * Cr * U * V * Real.exp (-γ * L)) *
          (Real.exp (CN * q) * Real.exp (CQ * q) * (25 * Real.exp (CZ * q))) * ((1 + 32 * B) * P) := by
        have ht := mul_le_mul_of_nonneg_left hσQZ (by positivity : 0 ≤ 475 * Cr * U * V * Real.exp (-γ * L))
        have ht' := mul_le_mul ht hOneH (by positivity) (by positivity)
        simpa only [mul_assoc] using ht'
      _ = U * V * (CE * P * Real.exp (CT * q - γ * L)) := by
        dsimp [CE, CT]
        rw [show (CN + CQ + CZ) * q - γ * L = -γ * L + CN * q + CQ * q + CZ * q by ring]
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hResidueExp (by positivity : 0 ≤ CE * P)) (mul_nonneg hU.le hV.le)
  have hTotal : D ≤ U * V * (rhoCoeff * CM * P * g + rhoCoeff * CB * P * e + CE * P * e) := by
    have ht := mul_le_mul_of_nonneg_left (add_le_add hModel hBoundary) (by positivity : 0 ≤ U * V * rhoCoeff)
    have ht' := add_le_add ht hResidue
    exact hD.trans (by convert ht' using 1 <;> ring)
  have hPcombine : Real.rpow L (4 * C) * P = Real.rpow L (a + 4 * C) := by
    calc
      _ = Real.rpow L (4 * C + a) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1 <;> ring
  have hm := modelDecay L ((le_max_left _ _).trans hL)
  have he := errorDecay L ((le_max_right _ _).trans hL)
  have hfinal : Real.rpow L (4 * C) * (rhoCoeff * CM * P * g + rhoCoeff * CB * P * e + CE * P * e) ≤
      (rhoCoeff * CM + rhoCoeff * CB + CE) * Real.rpow L (-A) := by
    calc
      _ = rhoCoeff * CM * (Real.rpow L (a + 4 * C) * g) +
          rhoCoeff * CB * (Real.rpow L (a + 4 * C) * e) + CE * (Real.rpow L (a + 4 * C) * e) := by
        rw [← hPcombine]; ring
      _ ≤ rhoCoeff * CM * Real.rpow L (-A) + rhoCoeff * CB * Real.rpow L (-A) + CE * Real.rpow L (-A) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hm (by positivity)) (mul_le_mul_of_nonneg_left he (by positivity)))
          (mul_le_mul_of_nonneg_left he hCE.le)
      _ = _ := by ring
  calc
    _ ≤ 2 * Real.rpow L (4 * C) * (U * V * (rhoCoeff * CM * P * g + rhoCoeff * CB * P * e + CE * P * e)) :=
      mul_le_mul_of_nonneg_left hTotal (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
    _ = (2 * U * V) * (Real.rpow L (4 * C) * (rhoCoeff * CM * P * g + rhoCoeff * CB * P * e + CE * P * e)) := by ring
    _ ≤ (2 * U * V) * ((rhoCoeff * CM + rhoCoeff * CB + CE) * Real.rpow L (-A)) :=
      mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = _ := by dsimp [CA]; ring

end ArtinPrimitiveRoots.TypeII.PD
