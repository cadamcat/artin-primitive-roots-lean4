import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCRTModel
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootRestrictedFourier

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_character_divisor_lift (m n t : ℕ) (hm : 0 < m) (hn : 0 < n)
    [NeZero m] [NeZero n] [NeZero (m * n)] :
    ZMod.stdAddChar ((n : ZMod (m * n)) * (t : ZMod (m * n))) =
      ZMod.stdAddChar (t : ZMod m) := by
  have hL := pd1c_root_character_nat_fraction (m * n) (n * t)
  have hR := pd1c_root_character_nat_fraction m t
  simp only [Nat.cast_mul] at hL
  rw [← hL, ← hR]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma pd1c_root_character_CRT (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)] (z : ZMod (m * n)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((((ZMod.unitOfCoprime n hcop.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) * (z.val : ZMod m)) *
        ZMod.stdAddChar ((((ZMod.unitOfCoprime m hcop)⁻¹ : (ZMod n)ˣ) : ZMod n) * (z.val : ZMod n)) := by
  let γ : ZMod m := (((ZMod.unitOfCoprime n hcop.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)
  let ν : ZMod n := (((ZMod.unitOfCoprime m hcop)⁻¹ : (ZMod n)ˣ) : ZMod n)
  have hγ : (n : ZMod m) * γ = 1 := by
    change ((ZMod.unitOfCoprime n hcop.symm : (ZMod m)ˣ) : ZMod m) *
      (((ZMod.unitOfCoprime n hcop.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) = 1
    simp
  have hν : (m : ZMod n) * ν = 1 := by
    change ((ZMod.unitOfCoprime m hcop : (ZMod n)ˣ) : ZMod n) *
      (((ZMod.unitOfCoprime m hcop)⁻¹ : (ZMod n)ˣ) : ZMod n) = 1
    simp
  let q : ZMod (m * n) := (n : ZMod (m * n)) * (γ.val : ZMod (m * n)) +
    (m : ZMod (m * n)) * (ν.val : ZMod (m * n))
  have hq : q = 1 := by
    apply (ZMod.chineseRemainder hcop).injective
    simp only [q, map_add, map_mul, map_natCast, map_one, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_mul, Prod.snd_mul, Prod.fst_natCast, Prod.snd_natCast, Prod.fst_one, Prod.snd_one]
    simp only [ZMod.natCast_self, mul_zero, zero_mul, zero_add, add_zero, ZMod.natCast_zmod_val,
      hγ, hν, and_self]
  have hz : z = (n : ZMod (m * n)) * ((γ.val * z.val : ℕ) : ZMod (m * n)) +
      (m : ZMod (m * n)) * ((ν.val * z.val : ℕ) : ZMod (m * n)) := by
    calc
      z = q * z := by rw [hq, one_mul]
      _ = _ := by dsimp [q]; rw [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val]; ring
  conv_lhs => rw [hz]
  rw [AddChar.map_add_eq_mul, pd1c_character_divisor_lift m n (γ.val * z.val) hm hn]
  have hN : ZMod.stdAddChar ((m : ZMod (m * n)) * ((ν.val * z.val : ℕ) : ZMod (m * n))) =
      ZMod.stdAddChar ((ν.val * z.val : ℕ) : ZMod n) := by
    have hL := pd1c_root_character_nat_fraction (m * n) (m * (ν.val * z.val))
    have hR := pd1c_root_character_nat_fraction n (ν.val * z.val)
    simp only [Nat.cast_mul] at hL hR ⊢
    rw [← hL, ← hR]
    congr 1
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [hN]
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  rfl

lemma pd1c_character_cast (m n : ℕ) (heq : m = n) [NeZero m] [NeZero n] (z : ZMod m) :
    ZMod.stdAddChar (RingEquiv.cast (R := ZMod) heq z) = ZMod.stdAddChar z := by
  subst n
  rfl

lemma pd1c_crt_first_val (m n : ℕ) (hcop : m.Coprime n) [NeZero (m * n)] (z : ZMod (m * n)) :
    (ZMod.chineseRemainder hcop z).1 = (z.val : ZMod m) := by
  calc
    _ = (ZMod.chineseRemainder hcop (z.val : ZMod (m * n))).1 :=
      congrArg (fun t : ZMod (m * n) => (ZMod.chineseRemainder hcop t).1) (ZMod.natCast_zmod_val z).symm
    _ = _ := by rw [map_natCast]; rfl

lemma pd1c_crt_second_val (m n : ℕ) (hcop : m.Coprime n) [NeZero (m * n)] (z : ZMod (m * n)) :
    (ZMod.chineseRemainder hcop z).2 = (z.val : ZMod n) := by
  calc
    _ = (ZMod.chineseRemainder hcop (z.val : ZMod (m * n))).2 :=
      congrArg (fun t : ZMod (m * n) => (ZMod.chineseRemainder hcop t).2) (ZMod.natCast_zmod_val z).symm
    _ = _ := by rw [map_natCast]; rfl

lemma pd1c_character_CRT_coordinates (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h k c v : ZMod (m * n)) :
    ZMod.stdAddChar (h * c + k * v) =
      ZMod.stdAddChar ((((ZMod.unitOfCoprime n hcop.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) *
        ((ZMod.chineseRemainder hcop h).1 * (ZMod.chineseRemainder hcop c).1 +
          (ZMod.chineseRemainder hcop k).1 * (ZMod.chineseRemainder hcop v).1)) *
      ZMod.stdAddChar ((((ZMod.unitOfCoprime m hcop)⁻¹ : (ZMod n)ˣ) : ZMod n) *
        ((ZMod.chineseRemainder hcop h).2 * (ZMod.chineseRemainder hcop c).2 +
          (ZMod.chineseRemainder hcop k).2 * (ZMod.chineseRemainder hcop v).2)) := by
  rw [pd1c_root_character_CRT m n hm hn hcop (h * c + k * v)]
  rw [← pd1c_crt_first_val m n hcop, ← pd1c_crt_second_val m n hcop]
  simp only [map_add, map_mul, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul]

end ArtinPrimitiveRoots.TypeII.PD
