import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def integerTube (T : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ)) ×ˢ (Finset.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ))

theorem mem_integerTube (T : ℝ) (z : ℤ × ℤ) (hz₁ : |(z.1 : ℝ)| ≤ T) (hz₂ : |(z.2 : ℝ)| ≤ T) :
    z ∈ integerTube T := by
  have hc := Nat.le_ceil T
  have hbounds (v : ℤ) (hv : |(v : ℝ)| ≤ T) : -(⌈T⌉₊ : ℤ) ≤ v ∧ v ≤ (⌈T⌉₊ : ℤ) := by
    have hl : -(⌈T⌉₊ : ℝ) ≤ (v : ℝ) := (neg_le_neg hc).trans (abs_le.mp hv).1
    have hr : (v : ℝ) ≤ (⌈T⌉₊ : ℝ) := (abs_le.mp hv).2.trans hc
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hbounds z.1 hz₁), Finset.mem_Icc.mpr (hbounds z.2 hz₂)⟩

theorem integerTube_card_le (T : ℝ) (hT : 1 ≤ T) : ((integerTube T).card : ℝ) ≤ 25 * T ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ)
  have hcZ := Int.card_Icc_of_le (a := -(⌈T⌉₊ : ℤ)) (b := (⌈T⌉₊ : ℤ)) (by omega)
  have hcR : (I.card : ℝ) = 2 * (⌈T⌉₊ : ℝ) + 1 := by
    have h : ((I.card : ℕ) : ℤ) = 2 * (⌈T⌉₊ : ℤ) + 1 := by dsimp [I]; omega
    exact_mod_cast h
  have hceil := (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ T)).le
  have hAxis : (I.card : ℝ) ≤ 5 * T := by rw [hcR]; linarith
  have hmul := mul_le_mul hAxis hAxis (Nat.cast_nonneg (α := ℝ) I.card) (by linarith : 0 ≤ 5 * T)
  change ((I ×ˢ I).card : ℝ) ≤ _
  rw [Finset.card_product]
  push_cast
  nlinarith

end
end ArtinPrimitiveRoots.TypeII.PD
