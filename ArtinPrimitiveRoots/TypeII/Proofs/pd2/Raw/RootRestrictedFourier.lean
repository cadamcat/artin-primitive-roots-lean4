import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootUnitFiber

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_root_character_indicator (m : ℕ) [NeZero m] (r c : ZMod m) :
    (if r = c then (1 : ℂ) else 0) = (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.stdAddChar (j * (r - c)) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have heq : (∑ j : ZMod m, ZMod.stdAddChar (j * (r - c))) = if r = c then (m : ℂ) else 0 := by
    simp_rw [mul_comm _ (r - c)]
    rw [pd2a_root_character_orthogonality]
    by_cases hrc : r = c <;> simp [hrc, sub_eq_zero]
  rw [heq]
  by_cases hrc : r = c <;> simp [hrc, hm]

lemma pd2a_restricted_inverse_fourier (u D : ℕ) (hu : 0 < u) (hD : 0 < D)
    [NeZero D] [NeZero (u * D)] (α : (ZMod (u * D))ˣ)
    (c₀ : ZMod D) (h k : ZMod (u * D)) :
    (∑ c : (ZMod (u * D))ˣ,
      if (((c : ZMod (u * D)).val : ℕ) : ZMod D) = c₀ then
        ZMod.stdAddChar (h * (c : ZMod (u * D)) + k * (α : ZMod (u * D)) * ((c⁻¹ : (ZMod (u * D))ˣ) : ZMod (u * D))) else 0) =
    (D : ℂ)⁻¹ * ∑ j : ZMod D, ZMod.stdAddChar (-j * c₀) *
      ∑ c : (ZMod (u * D))ˣ,
        ZMod.stdAddChar ((h + (u : ZMod (u * D)) * (j.val : ZMod (u * D))) * (c : ZMod (u * D)) +
          k * (α : ZMod (u * D)) * ((c⁻¹ : (ZMod (u * D))ˣ) : ZMod (u * D))) := by
  let r := fun c : (ZMod (u * D))ˣ => (((c : ZMod (u * D)).val : ℕ) : ZMod D)
  let a := fun c : (ZMod (u * D))ˣ => h * (c : ZMod (u * D)) + k * (α : ZMod (u * D)) * ((c⁻¹ : (ZMod (u * D))ˣ) : ZMod (u * D))
  have hpoint : ∀ c : (ZMod (u * D))ˣ,
      (if r c = c₀ then ZMod.stdAddChar (a c) else 0) =
      (D : ℂ)⁻¹ * ∑ j : ZMod D,
        ZMod.stdAddChar (-j * c₀) * ZMod.stdAddChar ((h + (u : ZMod (u * D)) * (j.val : ZMod (u * D))) * (c : ZMod (u * D)) +
          k * (α : ZMod (u * D)) * ((c⁻¹ : (ZMod (u * D))ˣ) : ZMod (u * D))) := by
    intro c
    calc
      _ = (if r c = c₀ then (1 : ℂ) else 0) * ZMod.stdAddChar (a c) := by by_cases hr : r c = c₀ <;> simp [hr]
      _ = ((D : ℂ)⁻¹ * ∑ j : ZMod D, ZMod.stdAddChar (j * (r c - c₀))) * ZMod.stdAddChar (a c) := by rw [pd2a_root_character_indicator]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hDarg : j * (r c - c₀) = -j * c₀ + j * r c := by ring
        rw [hDarg, AddChar.map_add_eq_mul]
        have hlift := pd2a_root_character_lift u D hu hD j (c : ZMod (u * D))
        change ZMod.stdAddChar ((u : ZMod (u * D)) * (j.val : ZMod (u * D)) * (c : ZMod (u * D))) = ZMod.stdAddChar (j * r c) at hlift
        rw [← hlift]
        have hMArg : (h + (u : ZMod (u * D)) * (j.val : ZMod (u * D))) * (c : ZMod (u * D)) +
          k * (α : ZMod (u * D)) * ((c⁻¹ : (ZMod (u * D))ˣ) : ZMod (u * D)) =
          (u : ZMod (u * D)) * (j.val : ZMod (u * D)) * (c : ZMod (u * D)) + a c := by dsimp [a]; ring
        rw [hMArg]
        conv_rhs => rw [AddChar.map_add_eq_mul]
        ring
  change (∑ c : (ZMod (u * D))ˣ, if r c = c₀ then ZMod.stdAddChar (a c) else 0) = _
  simp_rw [hpoint]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]

end ArtinPrimitiveRoots.TypeII.PD
