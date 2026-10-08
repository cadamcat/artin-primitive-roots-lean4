import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootProgressionCount

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_crt_progression_error (d S : ℕ) (hd : 0 < d) (hS : 0 < S) (hcop : d.Coprime S)
    (a : ZMod S) (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    |(((pd1c_natClosedInterval A B).filter (fun n => d ∣ n ∧ (n : ZMod S) = a)).card : ℝ) -
      (B - A) / ((d * S : ℕ) : ℝ)| ≤ 2 := by
  letI : NeZero d := ⟨hd.ne'⟩
  letI : NeZero S := ⟨hS.ne'⟩
  letI : NeZero (d * S) := ⟨(mul_pos hd hS).ne'⟩
  let z : ZMod (d * S) := (ZMod.chineseRemainder hcop).symm (0, a)
  have hZ : ZMod.chineseRemainder hcop z = (0, a) := (ZMod.chineseRemainder hcop).apply_symm_apply _
  have hPred : ∀ n : ℕ, (d ∣ n ∧ (n : ZMod S) = a) ↔ n % (d * S) = z.val := by
    intro n
    have hCast : ((n : ZMod (d * S)) = z) ↔ (d ∣ n ∧ (n : ZMod S) = a) := by
      rw [← (ZMod.chineseRemainder hcop).injective.eq_iff, hZ, map_natCast]
      change (((n : ZMod d), (n : ZMod S)) = (0, a)) ↔ _
      rw [Prod.mk.injEq, ZMod.natCast_eq_zero_iff]
    have hMod : ((n : ZMod (d * S)) = z) ↔ n % (d * S) = z.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (ZMod.val_lt z)]
    exact hCast.symm.trans hMod
  have hFinset : (pd1c_natClosedInterval A B).filter (fun n => d ∣ n ∧ (n : ZMod S) = a) =
      (pd1c_natClosedInterval A B).filter (fun n => n % (d * S) = z.val) := by
    ext n
    simp only [Finset.mem_filter, hPred]
  rw [hFinset]
  exact pd1c_progression_interval_error (d * S) z.val (mul_pos hd hS) (ZMod.val_lt z) A B hA hAB

end ArtinPrimitiveRoots.TypeII.PD
