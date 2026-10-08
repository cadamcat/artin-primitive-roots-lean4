import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCountingInputs
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Residue.RootDivisorBound

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

private abbrev pd2a_ReducedResidues (m : ℕ) :=
  {y : ℕ // y ∈ (Finset.range m).filter (fun y => Nat.Coprime y m)}

private noncomputable def pd2a_reducedResiduesEquivUnits (m : ℕ) (hm : 0 < m) :
    pd2a_ReducedResidues m ≃ (ZMod m)ˣ := by
  letI : NeZero m := ⟨by omega⟩
  refine
    { toFun := fun y => ZMod.unitOfCoprime y.val (Finset.mem_filter.mp y.property).2
      invFun := fun u => ⟨(u.val).val,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt u.val),
          ZMod.val_coe_unit_coprime u⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    have hylt : y.val < m := Finset.mem_range.mp (Finset.mem_filter.mp y.property).1
    simp [ZMod.unitOfCoprime, ZMod.val_natCast_of_lt hylt]
  · intro u
    apply Units.ext
    simp [ZMod.unitOfCoprime, ZMod.natCast_zmod_val]

private lemma pd2a_additiveCharacter_nat_div_eq_stdAddChar
    {m t : ℕ} [NeZero m] :
    ArtinPrimitiveRoots.TypeII.additiveCharacter ((t : ℝ) / (m : ℝ)) =
      ZMod.stdAddChar (t : ZMod m) := by
  have hcast : (t : ZMod m) = ((t : ℤ) : ZMod m) := by norm_cast
  rw [hcast, ZMod.stdAddChar_coe]
  unfold ArtinPrimitiveRoots.TypeII.additiveCharacter
  congr 1
  push_cast
  ring

lemma pd2a_kloostermanSum_eq_unit_sum
    (m h k : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] :
    kloostermanSum m h k =
      ∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar ((h : ZMod m) * (u : ZMod m) +
          (k : ZMod m) * (u⁻¹ : ZMod m)) := by
  classical
  have hm : 0 < m := NeZero.pos m
  let S : Finset ℕ := (Finset.range m).filter (fun y => Nat.Coprime y m)
  let e := pd2a_reducedResiduesEquivUnits m hm
  let f (y : pd2a_ReducedResidues m) :=
    ArtinPrimitiveRoots.TypeII.additiveCharacter
      (((h * y.val + k * ((y.val : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ))
  let g (u : (ZMod m)ˣ) :=
    ZMod.stdAddChar ((h : ZMod m) * (u : ZMod m) + (k : ZMod m) * (u⁻¹ : ZMod m))
  have hsum : (∑ y ∈ S,
      ArtinPrimitiveRoots.TypeII.additiveCharacter
        (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ))) =
      ∑ y : pd2a_ReducedResidues m, f y := by
    simpa [pd2a_ReducedResidues, S, f] using
      (Finset.sum_attach S (fun y =>
        ArtinPrimitiveRoots.TypeII.additiveCharacter
          (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ)))).symm
  calc
    kloostermanSum m h k = ∑ y ∈ S,
        ArtinPrimitiveRoots.TypeII.additiveCharacter
          (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ)) := by
      simp [kloostermanSum, S]
    _ = ∑ y : pd2a_ReducedResidues m, f y := hsum
    _ = ∑ u : (ZMod m)ˣ, g u := by
      apply Fintype.sum_equiv e f g
      intro y
      dsimp [f, g]
      rw [pd2a_additiveCharacter_nat_div_eq_stdAddChar (m := m)
        (t := h * y.val + k * ((y.val : ZMod m)⁻¹).val)]
      congr 1
      simp [e, pd2a_reducedResiduesEquivUnits, ZMod.unitOfCoprime,
        ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

lemma pd2a_unit_kloosterman_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ CK : ℝ, 0 < CK ∧
      ∀ m : ℕ, ∀ hi : NeZero m, ∀ Ft : Fintype (ZMod m)ˣ, ∀ H K : ZMod m,
        ‖@pd2a_rootKSum m hi Ft H K‖ ≤ CK * (m : ℝ) ^ (3/4+ε) *
          (Nat.gcd (Nat.gcd H.val K.val) m : ℝ) ^ (1/4:ℝ) := by
  obtain ⟨CK,hCK,hK⟩ := weak_kloosterman ε hε
  refine ⟨CK,hCK,?_⟩
  intro m hi Ft H K
  letI : NeZero m := hi
  letI : Fintype (ZMod m)ˣ := Ft
  have he : kloostermanSum m H.val K.val = pd2a_rootKSum m H K := by
    rw [pd2a_kloostermanSum_eq_unit_sum]
    simp only [ZMod.natCast_zmod_val,pd2a_rootKSum,ZMod.inv_coe_unit]
  rw [←he]
  exact hK m H.val K.val (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))

lemma pd2a_counting_inputs_exists : Nonempty pd2a_RootCountingInputs := by
  obtain ⟨CK,hCK,hK⟩ := pd2a_unit_kloosterman_bound (1/100) (by norm_num)
  obtain ⟨CT,hCT,hT⟩ := pd2r_divisor_card_rpow_bound (1/100) (by norm_num)
  exact ⟨⟨CK,CT,hCK,hCT,hK,hT⟩⟩

end ArtinPrimitiveRoots.TypeII.PD
