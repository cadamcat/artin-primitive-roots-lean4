import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootInverseGraph

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_root_unitFiber_mass (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hdiv : d ∣ m)
    (c₀ : (ZMod d)ˣ) :
    (Nat.card {c : (ZMod m)ˣ // ZMod.unitsMap hdiv c = c₀}) * Nat.totient d = Nat.totient m := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero d := ⟨hd.ne'⟩
  let f := ZMod.unitsMap hdiv
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hdiv
  have hker : Nat.card {c : (ZMod m)ˣ // f c = c₀} = Nat.card f.ker := by
    have heq := MonoidHom.fiberEquivKerOfSurjective hsurj c₀
    exact Nat.card_congr heq
  have hi : f.ker.index = Nat.totient d := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj]
    calc
      Nat.card (⊤ : Subgroup (ZMod d)ˣ) = Nat.card (ZMod d)ˣ := Nat.card_congr (Equiv.Set.univ _)
      _ = Nat.totient d := by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hc := f.ker.card_mul_index
  have hmcard : Nat.card (ZMod m)ˣ = Nat.totient m := by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hi, hmcard] at hc
  rw [hker]
  exact hc

lemma pd1c_root_unitFiber_real (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hdiv : d ∣ m)
    (c₀ : (ZMod d)ˣ) :
    (Nat.card {c : (ZMod m)ˣ // ZMod.unitsMap hdiv c = c₀} : ℝ) =
      (Nat.totient m : ℝ) / Nat.totient d := by
  have hφ : 0 < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  apply (eq_div_iff hφ.ne').mpr
  exact_mod_cast pd1c_root_unitFiber_mass m d hm hd hdiv c₀

noncomputable def pd1c_crtInverseGraphEquiv
    {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    (e : R ≃+* A × B) (f : A →+* D) (α : Aˣ) (c₀ : D) (cB vB : B) :
    {c : Aˣ // f (c : A) = c₀} ≃
      {z : R × R // (e z.1).1 * (e z.2).1 = (α : A) ∧
        (e z.1).2 = cB ∧ (e z.2).2 = vB ∧ f (e z.1).1 = c₀} where
  toFun c := ⟨(e.symm ((c.1 : A), cB), e.symm ((α : A) * ((c.1⁻¹ : Aˣ) : A), vB)), by
    simp only [e.apply_symm_apply]
    exact ⟨by simp [mul_left_comm, mul_assoc], trivial, trivial, c.2⟩⟩
  invFun z := ⟨(pd1c_inverseGraphEquiv A α).symm ⟨((e z.1.1).1, (e z.1.2).1), z.2.1⟩, z.2.2.2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Units.ext
    change (e (e.symm ((c.1 : A), cB))).1 = (c.1 : A)
    rw [e.apply_symm_apply]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply e.injective
      simp only [e.apply_symm_apply]
      apply Prod.ext
      · rfl
      · exact z.2.2.1.symm
    · apply e.injective
      simp only [e.apply_symm_apply]
      apply Prod.ext
      · change (α : A) * ((e z.1.2).1 * ((α⁻¹ : Aˣ) : A)) = (e z.1.2).1
        calc
          (α : A) * ((e z.1.2).1 * ((α⁻¹ : Aˣ) : A)) = (e z.1.2).1 * ((α : A) * ((α⁻¹ : Aˣ) : A)) := by ring
          _ = (e z.1.2).1 := by simp
      · exact z.2.2.2.1.symm

end ArtinPrimitiveRoots.TypeII.PD
