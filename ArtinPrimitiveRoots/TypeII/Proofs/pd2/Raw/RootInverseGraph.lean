import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootGraph
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootIntervals

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_inverseGraphEquiv (R : Type*) [CommRing R] (α : Rˣ) :
    Rˣ ≃ {z : R × R // z.1 * z.2 = (α : R)} where
  toFun c := ⟨((c : R), (α : R) * ((c⁻¹ : Rˣ) : R)), by simp [mul_left_comm, mul_assoc]⟩
  invFun z := Units.mkOfMulEqOne z.1.1 (z.1.2 * ((α⁻¹ : Rˣ) : R)) (by rw [← mul_assoc, z.2]; simp)
  left_inv c := by apply Units.ext; rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (α : R) * (z.1.2 * ((α⁻¹ : Rˣ) : R)) = z.1.2
      calc
        (α : R) * (z.1.2 * ((α⁻¹ : Rˣ) : R)) = z.1.2 * ((α : R) * ((α⁻¹ : Rˣ) : R)) := by ring
        _ = z.1.2 := by simp

noncomputable def pd2a_inverseGraph (m : ℕ) [NeZero m] (α : (ZMod m)ˣ) :
    Finset (ZMod m × ZMod m) := Finset.univ.filter (fun z => z.1 * z.2 = (α : ZMod m))

lemma pd2a_inverseGraph_card (m : ℕ) [NeZero m] (α : (ZMod m)ˣ) :
    (pd2a_inverseGraph m α).card = Nat.totient m := by
  have hc := Fintype.card_congr (pd2a_inverseGraphEquiv (ZMod m) α)
  have hcard : Fintype.card {z : ZMod m × ZMod m // z.1 * z.2 = (α : ZMod m)} =
      (pd2a_inverseGraph m α).card := by simp [pd2a_inverseGraph, Fintype.card_subtype]
  rw [hcard, ZMod.card_units_eq_totient] at hc
  exact hc.symm

lemma pd2a_inverseGraph_transform (m : ℕ) [NeZero m] (α : (ZMod m)ˣ) (h k : ZMod m) :
    pd2a_rootGraphTransform m (pd2a_inverseGraph m α) h k =
      ∑ c : (ZMod m)ˣ, ZMod.stdAddChar (h * (c : ZMod m) +
        (k * (α : ZMod m)) * ((c⁻¹ : (ZMod m)ˣ) : ZMod m)) := by
  have heq : (∑ c : (ZMod m)ˣ, ZMod.stdAddChar (h * (c : ZMod m) +
      k * ((α : ZMod m) * ((c⁻¹ : (ZMod m)ˣ) : ZMod m)))) =
      ∑ z : {z : ZMod m × ZMod m // z.1 * z.2 = (α : ZMod m)}, ZMod.stdAddChar (h * z.1.1 + k * z.1.2) :=
    (pd2a_inverseGraphEquiv (ZMod m) α).sum_comp (fun z => ZMod.stdAddChar (h * z.1.1 + k * z.1.2))
  unfold pd2a_rootGraphTransform
  rw [Finset.sum_subtype (p := fun z : ZMod m × ZMod m => z.1 * z.2 = (α : ZMod m)) (pd2a_inverseGraph m α) (fun z => by simp [pd2a_inverseGraph]), ← heq]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  ring

lemma pd2a_root_character_lift (u S : ℕ) (hu : 0 < u) (hS : 0 < S) [NeZero S] [NeZero (u * S)]
    (j : ZMod S) (c : ZMod (u * S)) :
    ZMod.stdAddChar ((u : ZMod (u * S)) * (j.val : ZMod (u * S)) * c) =
      ZMod.stdAddChar (j * (c.val : ZMod S)) := by
  letI : NeZero S := ⟨hS.ne'⟩
  letI : NeZero (u * S) := ⟨(mul_pos hu hS).ne'⟩
  have hleft := pd2a_root_character_nat_fraction (u * S) (u * j.val * c.val)
  have hright := pd2a_root_character_nat_fraction S (j.val * c.val)
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val] at hleft hright
  rw [← hleft, ← hright]
  congr 1
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  field_simp

end ArtinPrimitiveRoots.TypeII.PD
