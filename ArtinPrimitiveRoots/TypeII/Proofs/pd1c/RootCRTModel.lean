import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCRTPredicate
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootEulerArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd1c_rootCRTEquiv (u S : ℕ) (hSq : Squarefree S) :
    ZMod (u * S) ≃+* ZMod (u * pd1c_rootShared u S) × ZMod (pd1c_rootUnshared u S) :=
  (RingEquiv.cast (R := ZMod) (show u * S = (u * pd1c_rootShared u S) * pd1c_rootUnshared u S by
    rw [mul_assoc, pd1c_rootShared_mul_unshared u S hSq])).trans
      (ZMod.chineseRemainder (pd1c_rootCRT_coprime u S))

noncomputable def pd1c_rootCRTResidueEquiv (u S : ℕ) (hSq : Squarefree S) :
    ZMod S ≃+* ZMod (pd1c_rootShared u S) × ZMod (pd1c_rootUnshared u S) :=
  (RingEquiv.cast (R := ZMod) (pd1c_rootShared_mul_unshared u S hSq).symm).trans
    (ZMod.chineseRemainder (pd1c_rootParts_coprime u S))

lemma pd1c_rootCRT_commute (u S : ℕ) (hSq : Squarefree S) [NeZero (u * S)]
    (z : ZMod (u * S)) :
    pd1c_rootCRTResidueEquiv u S hSq (ZMod.castHom (dvd_mul_left S u) (ZMod S) z) =
      (ZMod.castHom (dvd_mul_left (pd1c_rootShared u S) u) (ZMod (pd1c_rootShared u S))
        (pd1c_rootCRTEquiv u S hSq z).1, (pd1c_rootCRTEquiv u S hSq z).2) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  conv_rhs => rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast]
  rfl

lemma pd1c_rootGraph_mass (u S : ℕ) (hu : 0 < u) (hS : 0 < S)
    [NeZero (u * S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) :
    ((pd1c_rootGraph u S g₀).card : ℝ) = (u : ℝ) *
      ∏ p ∈ u.primeFactors.filter (fun p => ¬p ∣ S), (1 - 1 / (p : ℝ)) := by
  letI : NeZero S := ⟨hS.ne'⟩
  let D := pd1c_rootShared u S
  let E := pd1c_rootUnshared u S
  let M := u * D
  have hD : 0 < D := pd1c_rootShared_pos u S
  have hM : 0 < M := mul_pos hu hD
  letI : NeZero D := ⟨hD.ne'⟩
  letI : NeZero M := ⟨hM.ne'⟩
  let e := pd1c_rootCRTEquiv u S hSq
  let eT := pd1c_rootCRTResidueEquiv u S hSq
  let f : ZMod M →+* ZMod D := ZMod.castHom (dvd_mul_left D u) (ZMod D)
  let r : ZMod (u * S) →+* ZMod S := ZMod.castHom (dvd_mul_left S u) (ZMod S)
  let α : ZMod (u * S) := (u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1
  have hαUnit : IsUnit ((e α).1) := by
    have huA := pd1c_root_inverse_rhs_unit u S hu ((g₀ 1 1).val : ℤ)
    simpa only [α, map_sub, map_mul, map_natCast, map_one, Prod.fst_sub, Prod.fst_mul, Prod.fst_natCast,
      Prod.fst_one, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] using huA
  obtain ⟨αA, hαA⟩ := hαUnit
  have hcUnit : IsUnit (eT (g₀ 0 1)).1 := by
    have hc := pd1c_root_shared_entry_unit u S hS hSq g₀ hdet hu₀
    have heq : (eT (g₀ 0 1)).1 = (((g₀ 0 1).val : ℕ) : ZMod D) := by
      calc
        _ = (eT (((g₀ 0 1).val : ℕ) : ZMod S)).1 :=
          congrArg (fun y : ZMod S => (eT y).1) (ZMod.natCast_zmod_val (g₀ 0 1)).symm
        _ = _ := by rw [map_natCast]; rfl
    rw [heq]
    exact hc
  obtain ⟨cU, hcU⟩ := hcUnit
  have hαr : r α = g₀ 0 1 * g₀ 1 0 := by
    have hdet' : g₀ 0 0 * g₀ 1 1 - g₀ 0 1 * g₀ 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hdet
    change r ((u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1) = _
    rw [map_sub, map_mul, map_natCast, map_natCast, map_one, ZMod.natCast_zmod_val, hu₀]
    linear_combination hdet'
  have hpred : ∀ z : ZMod (u * S) × ZMod (u * S), z ∈ pd1c_rootGraph u S g₀ ↔
      (e z.1).1 * (e z.2).1 = (αA : ZMod M) ∧
        (e z.1).2 = (eT (g₀ 0 1)).2 ∧ (e z.2).2 = (eT (g₀ 1 0)).2 ∧ f (e z.1).1 = (eT (g₀ 0 1)).1 := by
    intro z
    have hpre := pd1c_crt_inverse_predicate e eT f r (pd1c_rootCRT_commute u S hSq) α αA hαA.symm
      (g₀ 0 1) (g₀ 1 0) hαr ⟨cU, hcU⟩ z
    have hrCast : ∀ z : ZMod (u * S), r z = (z.val : ZMod S) := by
      intro z
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [map_natCast]
    simpa only [pd1c_rootGraph, Finset.mem_filter, Finset.mem_univ, true_and, hrCast, α] using hpre
  let G := {z : ZMod (u * S) × ZMod (u * S) // z ∈ pd1c_rootGraph u S g₀}
  let H := {c : (ZMod M)ˣ // f (c : ZMod M) = (eT (g₀ 0 1)).1}
  let eqPred : G ≃ {z : ZMod (u * S) × ZMod (u * S) //
      (e z.1).1 * (e z.2).1 = (αA : ZMod M) ∧ (e z.1).2 = (eT (g₀ 0 1)).2 ∧
        (e z.2).2 = (eT (g₀ 1 0)).2 ∧ f (e z.1).1 = (eT (g₀ 0 1)).1} :=
    Equiv.subtypeEquivRight hpred
  let eqGraph : H ≃ G := (pd1c_crtInverseGraphEquiv e f αA (eT (g₀ 0 1)).1
    (eT (g₀ 0 1)).2 (eT (g₀ 1 0)).2).trans eqPred.symm
  have hCard : (pd1c_rootGraph u S g₀).card = Nat.card H := by
    calc
      _ = Fintype.card G := by simp [G, Fintype.card_coe]
      _ = Nat.card G := Nat.card_eq_fintype_card.symm
      _ = Nat.card H := (Nat.card_congr eqGraph).symm
  have hH : Nat.card H = Nat.card {c : (ZMod M)ˣ // ZMod.unitsMap (dvd_mul_left D u) c = cU} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro c
    have hcval : ((ZMod.unitsMap (dvd_mul_left D u) c : (ZMod D)ˣ) : ZMod D) = f (c : ZMod M) := rfl
    rw [← hcU, ← hcval, Units.val_inj]
  rw [hCard, hH, pd1c_root_unitFiber_real M D hM hD]
  exact pd1c_root_euler_totient_ratio u S hu hS

end ArtinPrimitiveRoots.TypeII.PD
