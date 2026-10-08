import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTCharacters

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_crtGraph_sum
    {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Fintype R] [Fintype A] [Fintype B] [Fintype D]
    (e : R ≃+* A × B) (f : A →+* D) (α : Aˣ) (c₀ : D) (cB vB : B)
    (G : Finset (R × R))
    (hG : ∀ z : R × R, z ∈ G ↔ (e z.1).1 * (e z.2).1 = (α : A) ∧
      (e z.1).2 = cB ∧ (e z.2).2 = vB ∧ f (e z.1).1 = c₀)
    (W : R × R → ℂ) (phase : ℂ) (H K : A) (χ : A → ℂ)
    (hW : ∀ z ∈ G, W z = phase * χ (H * (e z.1).1 + K * (e z.2).1)) :
    (∑ z ∈ G, W z) = phase * ∑ c : Aˣ,
      if f (c : A) = c₀ then χ (H * (c : A) + K * (α : A) * ((c⁻¹ : Aˣ) : A)) else 0 := by
  let P := fun z : R × R => (e z.1).1 * (e z.2).1 = (α : A) ∧
    (e z.1).2 = cB ∧ (e z.2).2 = vB ∧ f (e z.1).1 = c₀
  let eqPred : {z : R × R // z ∈ G} ≃ {z : R × R // P z} := Equiv.subtypeEquivRight hG
  let eqGraph := (pd2a_crtInverseGraphEquiv e f α c₀ cB vB).trans eqPred.symm
  have hCFst : ∀ c : {c : Aˣ // f (c : A) = c₀}, (e (eqGraph c).1.1).1 = (c.1 : A) := by
    intro c
    change (e (e.symm ((c.1 : A), cB))).1 = (c.1 : A)
    rw [e.apply_symm_apply]
  have hVSnd : ∀ c : {c : Aˣ // f (c : A) = c₀}, (e (eqGraph c).1.2).1 = (α : A) * ((c.1⁻¹ : Aˣ) : A) := by
    intro c
    change (e (e.symm ((α : A) * ((c.1⁻¹ : Aˣ) : A), vB))).1 = _
    rw [e.apply_symm_apply]
  have hsum : (∑ z ∈ G, W z) = ∑ c : {c : Aˣ // f (c : A) = c₀}, W (eqGraph c).1 := by
    rw [Finset.sum_subtype G (fun z => Iff.rfl)]
    exact (eqGraph.sum_comp (fun z => W z.1)).symm
  rw [hsum]
  have hfilter : (∑ c : Aˣ, if f (c : A) = c₀ then χ (H * (c : A) + K * (α : A) * ((c⁻¹ : Aˣ) : A)) else 0) =
      ∑ c : {c : Aˣ // f (c : A) = c₀}, χ (H * (c.1 : A) + K * (α : A) * ((c.1⁻¹ : Aˣ) : A)) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun c => by simp) _
  rw [hfilter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hW (eqGraph c).1 (eqGraph c).2, hCFst, hVSnd]
  have hArg : H * (c.1 : A) + K * ((α : A) * ((c.1⁻¹ : Aˣ) : A)) =
      H * (c.1 : A) + K * (α : A) * ((c.1⁻¹ : Aˣ) : A) := by ring
  rw [hArg]

end ArtinPrimitiveRoots.TypeII.PD
