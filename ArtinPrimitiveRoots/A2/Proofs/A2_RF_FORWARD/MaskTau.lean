import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.FiniteMass

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem maskTau_norm {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (P : FinPlace F) (hP : P ∉ S.Sf) (p : Fˣ)
    (hp : S.IsGen (p : F) P.asIdeal) (j : Fin 6) (hj : j ≠ 0) :
    ‖maskTau D A P p j‖ = Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField P
  -- Match the parent ring used by the finite-field Gauss norm theorem.
  letI : CommRing (𝓞 F ⧸ P.asIdeal) :=
    (ArtinPrimitiveRoots.A2.bridgeResidueField P).toCommRing
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype P
  obtain ⟨_, ⟨χ, hχord, hχval⟩, ⟨ψ, hψprim, hψval⟩⟩ :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR D S A P hP p hp
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (x : 𝓞 F ⧸ P.asIdeal) :
      ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F x.out) = x :=
    by simpa using SB.residue_algebraMap P x.out
  have hphase (t x : 𝓞 F ⧸ P.asIdeal) :
      maskPhase A P p t x = ψ (t * x) := (hψval t x).symm
  have hcharPower (e : ℤ) (x : 𝓞 F ⧸ P.asIdeal) :
      (χ ^ e) x = ArtinPrimitiveRoots.A1.chiPow D P
        (algebraMap (𝓞 F) F x.out) e := by
    by_cases hx : x = 0
    · subst x
      have hz : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) = 0 := by
        rw [hres]
      have hzero : (χ ^ e) (0 : 𝓞 F ⧸ P.asIdeal) = 0 :=
        MulChar.map_nonunit (χ ^ e) (by simp)
      rw [hzero, SB.chiPow_zero P _ e hz]
    · let u : (𝓞 F ⧸ P.asIdeal)ˣ := Units.mk0 x hx
      have hχu : χ (u : 𝓞 F ⧸ P.asIdeal) = ArtinPrimitiveRoots.A1.chiPow D P
          (algebraMap (𝓞 F) F x.out) 1 := by
        change χ x = _
        exact hχval x
      have hresne : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres]
        exact hx
      have hEval : (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = (χ u) ^ e := by
        calc
          (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = χ (u ^ e : (𝓞 F ⧸ P.asIdeal)ˣ) :=
            MulChar.zpow_apply_coe χ e u
          _ = (χ u) ^ e := by
            change ((χ.toUnitHom (u ^ e) : ℂˣ) : ℂ) =
              ((χ.toUnitHom u : ℂˣ) : ℂ) ^ e
            rw [map_zpow, Units.val_zpow_eq_zpow_val]
      have hEvalX : (χ ^ e) x = (χ x) ^ e := by
        change (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = (χ u) ^ e
        exact hEval
      calc
        (χ ^ e) x = (χ x) ^ e := hEvalX
        _ = (ArtinPrimitiveRoots.A1.chiPow D P
            (algebraMap (𝓞 F) F x.out) 1) ^ e := by rw [hχval x]
        _ = ArtinPrimitiveRoots.A1.chiPow D P
            (algebraMap (𝓞 F) F x.out) e := by
          rw [SB.chiPow_nonzero P _ 1 hresne, SB.chiPow_nonzero P _ e hresne]
          simp
  have htau (j : Fin 6) :
      maskTau D A P p j = gaussSum (χ ^ (-(j.1 : ℤ))) ψ := by
    unfold maskTau
    rw [ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum P
      (fun x : 𝓞 F ⧸ P.asIdeal => if x = 0 then 0 else
        ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) *
          maskPhase A P p 1 x)]
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · subst x
      have hχzero : ((χ ^ (j.1 : ℤ))⁻¹) (0 : 𝓞 F ⧸ P.asIdeal) = 0 :=
        MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ P.asIdeal))
      simp only [ite_true, zpow_neg]
      change (0 : ℂ) = ((χ ^ (j.1 : ℤ))⁻¹) (0 : 𝓞 F ⧸ P.asIdeal) * ψ 0
      rw [hχzero, zero_mul]
    · have hresne : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres]
        exact hx
      have hcoeff : ArtinPrimitiveRoots.A1.chi D P
          (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) =
          (χ ^ (-(j.1 : ℤ))) x := by
        calc
          _ = ArtinPrimitiveRoots.A1.chiPow D P
              (algebraMap (𝓞 F) F x.out) (-(j.1 : ℤ)) :=
                (SB.chiPow_nonzero P _ _ hresne).symm
          _ = (χ ^ (-(j.1 : ℤ))) x := (hcharPower _ x).symm
      simp only [if_neg hx]
      rw [hcoeff, hphase]
      simp <;> rfl
  have hcharNotOne (j : Fin 6) (hj : j ≠ 0) :
      χ ^ (-(j.1 : ℤ)) ≠ (1 : MulChar (𝓞 F ⧸ P.asIdeal) ℂ) := by
    intro h
    have hd : (orderOf χ : ℤ) ∣ -(j.1 : ℤ) :=
      (orderOf_dvd_iff_zpow_eq_one).2 h
    rw [hχord] at hd
    have hd' : (6 : ℤ) ∣ (j.1 : ℤ) := by
      simpa using (dvd_neg.mp hd)
    have hdNat : 6 ∣ j.1 := Int.natCast_dvd_natCast.mp hd'
    have hjval : j.1 ≠ 0 := by
      intro hv
      apply hj
      exact Fin.ext hv
    have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjval
    have hjle : 6 ≤ j.1 := Nat.le_of_dvd hjpos hdNat
    omega
  have hcard : Fintype.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [htau]
  simpa only [hcard, gaussSum] using gaussSum_norm
    (χ ^ (-(j.1 : ℤ))) ψ (hcharNotOne j hj) hψprim

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
