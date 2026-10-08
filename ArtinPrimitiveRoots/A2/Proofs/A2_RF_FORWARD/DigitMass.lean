import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.MaskTau

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem maskAlpha_mass {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (P : FinPlace F) (hP : P ∉ S.Sf) (p : Fˣ)
    (hp : S.IsGen (p : F) P.asIdeal) (j : Fin 6) :
    let mass := ∑ᶠ x : 𝓞 F ⧸ P.asIdeal, ‖maskAlpha D A P p j x‖
    (j ≠ 0 → mass ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (1 / 2 : ℝ)) ∧
      (j = 0 → mass < 2) := by
  classical
  letI := bridgeResidueFintype P
  let q : ℝ := Ideal.absNorm P.asIdeal
  have hcard : Fintype.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hq : 0 < q := by
    dsimp [q]
    rw [← hcard]
    exact_mod_cast Fintype.card_pos
  have hqone : 1 ≤ q := by
    dsimp [q]
    rw [← hcard]
    have h : 1 ≤ Fintype.card (𝓞 F ⧸ P.asIdeal) := Fintype.card_pos
    exact_mod_cast h
  dsimp only
  rw [finsum_eq_sum_of_fintype]
  constructor
  · intro hj
    have hnorm (x : 𝓞 F ⧸ P.asIdeal) :
        ‖maskAlpha D A P p j x‖ ≤ (Real.sqrt q)⁻¹ := by
      by_cases hx : x = 0
      · simp [maskAlpha, hj, hx, inv_nonneg.mpr (Real.sqrt_nonneg q)]
      · have hrep : residue P (algebraMap (𝓞 F) F x.out) = x := by
          simpa using (a2_bridge_SYMBOL D S).residue_algebraMap P x.out
        have hres : residue P (algebraMap (𝓞 F) F x.out) ≠ 0 := by
          rw [hrep]
          exact hx
        have hchi := (a2_bridge_SYMBOL D S).chi_norm P _ hres
        simp only [maskAlpha, dif_neg hj, if_neg hx, norm_mul, norm_inv, norm_zpow,
          maskTau_norm D S A P hP p hp j hj, hchi, one_zpow, mul_one]
        exact le_rfl
    calc
      (∑ x : 𝓞 F ⧸ P.asIdeal, ‖maskAlpha D A P p j x‖) ≤
          ∑ _x : 𝓞 F ⧸ P.asIdeal, (Real.sqrt q)⁻¹ :=
        Finset.sum_le_sum (fun x _ => hnorm x)
      _ = q * (Real.sqrt q)⁻¹ := by simp [hcard, q]
      _ = Real.sqrt q := by
        nth_rw 1 [← Real.sq_sqrt hq.le]
        rw [pow_two, mul_assoc,
          mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hq)), mul_one]
      _ = (Ideal.absNorm P.asIdeal : ℝ) ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow _
  · intro hj
    subst j
    have hi : q⁻¹ ≤ 1 := (inv_le_one₀ hq).mpr hqone
    have hnormzero :
        ‖(1 : ℂ) - (Ideal.absNorm P.asIdeal : ℂ)⁻¹‖ = 1 - q⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_one,
        ← Complex.ofReal_sub]
      exact Complex.norm_of_nonneg (sub_nonneg.mpr hi)
    have hnorm (x : 𝓞 F ⧸ P.asIdeal) :
        ‖maskAlpha D A P p 0 x‖ =
          q⁻¹ + if x = 0 then 1 - 2 * q⁻¹ else 0 := by
      by_cases hx : x = 0
      · simp only [maskAlpha, dite_true, if_pos hx, hnormzero]
        ring
      · simp [maskAlpha, hx, q, norm_inv, Complex.norm_natCast]
    simp_rw [hnorm]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hcard]
    change q * q⁻¹ + (1 - 2 * q⁻¹) < 2
    rw [mul_inv_cancel₀ (ne_of_gt hq)]
    have : 0 < q⁻¹ := inv_pos.mpr hq
    linarith

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
