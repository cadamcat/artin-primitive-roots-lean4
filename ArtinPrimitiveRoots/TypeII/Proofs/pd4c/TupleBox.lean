import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.IntegerBox
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TupleCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Finite position/prime-tuple states embed in the coordinate rectangle with integer product labels. -/
theorem position_prime_tuple_box_embedding {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (T : Finset ((ℤ × ℤ) × (Fin K → ℕ)))
    (hT : ∀ u ∈ T, IsMarkedPrimeTuple x K a u.2)
    (Φ : (ℤ × ℤ) → (ℤ × ℤ))
    (hΦ : Set.InjOn Φ ((T.image Prod.fst) : Set (ℤ × ℤ)))
    (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hbox : ∀ u ∈ T, |((Φ u.1).1 : ℝ)| ≤ A ∧ |((Φ u.1).2 : ℝ)| ≤ B) :
    let M := (2*⌊A⌋+1).toNat
    let N := (2*⌊B⌋+1).toNat
    let E : ((ℤ × ℤ) × (Fin K → ℕ)) → ((ℕ × ℕ) × ℤ) := fun u =>
      (((((Φ u.1).1+⌊A⌋).toNat), (((Φ u.1).2+⌊B⌋).toNat)), (tupleProduct u.2 : ℤ))
    let U : Finset ℤ := T.image (fun u => (tupleProduct u.2 : ℤ))
    (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧
      Set.InjOn E (T : Set ((ℤ × ℤ) × (Fin K → ℕ))) ∧
      (∀ u ∈ T, E u ∈ ((Finset.range M).product (Finset.range N)).product U) ∧
      ∀ u ∈ T, ((E u).1.1 : ℤ)-⌊A⌋ = (Φ u.1).1 ∧
        ((E u).1.2 : ℤ)-⌊B⌋ = (Φ u.1).2 := by
  let M := (2*⌊A⌋+1).toNat
  let N := (2*⌊B⌋+1).toNat
  let Ep : (ℤ × ℤ) → (ℕ × ℕ) := fun v =>
    ((v.1+⌊A⌋).toNat, (v.2+⌊B⌋).toNat)
  let E : ((ℤ × ℤ) × (Fin K → ℕ)) → ((ℕ × ℕ) × ℤ) := fun u =>
    (Ep (Φ u.1), (tupleProduct u.2 : ℤ))
  let U : Finset ℤ := T.image (fun u => (tupleProduct u.2 : ℤ))
  let P : Finset (ℤ × ℤ) := T.image (fun u => Φ u.1)
  change (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧
    Set.InjOn E (T : Set ((ℤ × ℤ) × (Fin K → ℕ))) ∧
    (∀ u ∈ T, E u ∈ ((Finset.range M).product (Finset.range N)).product U) ∧
    ∀ u ∈ T, ((E u).1.1 : ℤ)-⌊A⌋ = (Φ u.1).1 ∧
      ((E u).1.2 : ℤ)-⌊B⌋ = (Φ u.1).2
  have hPbox (v : ℤ × ℤ) (hv : v ∈ P) : |(v.1 : ℝ)| ≤ A ∧ |(v.2 : ℝ)| ≤ B := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact hbox u hu
  have hc := centered_integer_box_embedding A B hA hB P hPbox
  change (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧ Set.InjOn Ep (P : Set (ℤ × ℤ)) ∧
    ∀ v ∈ P, Ep v ∈ (Finset.range M).product (Finset.range N) ∧
      ((Ep v).1 : ℤ)-⌊A⌋ = v.1 ∧ ((Ep v).2 : ℤ)-⌊B⌋ = v.2 at hc
  have hmem (u : (ℤ × ℤ) × (Fin K → ℕ)) (hu : u ∈ T) : Φ u.1 ∈ P :=
    Finset.mem_image.mpr ⟨u, hu, rfl⟩
  refine ⟨hc.1, hc.2.1, ?_, ?_, ?_⟩
  · intro u hu v hv huv
    have hEpos : Ep (Φ u.1) = Ep (Φ v.1) := congrArg Prod.fst huv
    have hPhieq := hc.2.2.1 (hmem u hu) (hmem v hv) hEpos
    have hposeq : u.1 = v.1 := hΦ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hPhieq
    have hlabel := congrArg Prod.snd huv
    change (tupleProduct u.2 : ℤ) = (tupleProduct v.2 : ℤ) at hlabel
    have hproduct : tupleProduct u.2 = tupleProduct v.2 := by exact_mod_cast hlabel
    exact Prod.ext hposeq (markedTupleProduct_injective hbands (hT u hu) (hT v hv) hproduct)
  · intro u hu
    exact Finset.mem_product.mpr ⟨(hc.2.2.2 (Φ u.1) (hmem u hu)).1,
      Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · intro u hu
    exact (hc.2.2.2 (Φ u.1) (hmem u hu)).2

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
