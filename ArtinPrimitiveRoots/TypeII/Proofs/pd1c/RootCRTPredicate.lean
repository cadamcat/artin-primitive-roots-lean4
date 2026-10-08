import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootUnitFiber

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_crt_inverse_predicate
    {R A B D T : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D] [CommRing T]
    (e : R ≃+* A × B) (eT : T ≃+* D × B) (f : A →+* D) (r : R →+* T)
    (hcomm : ∀ z : R, eT (r z) = (f (e z).1, (e z).2))
    (α : R) (αA : Aˣ) (hα : (e α).1 = (αA : A))
    (c₀ v₀ : T) (hαr : r α = c₀ * v₀) (hcUnit : IsUnit (eT c₀).1)
    (z : R × R) :
    (r z.1 = c₀ ∧ r z.2 = v₀ ∧ z.1 * z.2 = α) ↔
      (e z.1).1 * (e z.2).1 = (αA : A) ∧
        (e z.1).2 = (eT c₀).2 ∧ (e z.2).2 = (eT v₀).2 ∧ f (e z.1).1 = (eT c₀).1 := by
  have hαD : f (αA : A) = (eT c₀).1 * (eT v₀).1 := by
    have hd := congrArg Prod.fst (hcomm α)
    rw [hαr, map_mul] at hd
    simpa only [Prod.fst_mul, hα] using hd.symm
  have hαB : (e α).2 = (eT c₀).2 * (eT v₀).2 := by
    have hd := congrArg Prod.snd (hcomm α)
    rw [hαr, map_mul] at hd
    exact hd.symm
  constructor
  · rintro ⟨hc, hv, hcv⟩
    have hce := hcomm z.1
    have hve := hcomm z.2
    rw [hc] at hce
    rw [hv] at hve
    have hcD : f (e z.1).1 = (eT c₀).1 := congrArg Prod.fst hce.symm
    have hcB : (e z.1).2 = (eT c₀).2 := congrArg Prod.snd hce.symm
    have hvB : (e z.2).2 = (eT v₀).2 := congrArg Prod.snd hve.symm
    have hm := congrArg (fun t : R => (e t).1) hcv
    simp only [map_mul, Prod.fst_mul] at hm
    exact ⟨hm.trans hα, hcB, hvB, hcD⟩
  · rintro ⟨hA, hcB, hvB, hcD⟩
    have hcvD : (eT c₀).1 * f (e z.2).1 = (eT c₀).1 * (eT v₀).1 := by
      have h := congrArg f hA
      rw [map_mul, hcD, hαD] at h
      exact h
    obtain ⟨cU, hcU⟩ := hcUnit
    have hvD : f (e z.2).1 = (eT v₀).1 := by
      have hcvU : (cU : D) * f (e z.2).1 = (cU : D) * (eT v₀).1 := by simpa only [hcU] using hcvD
      have h := congrArg (fun t : D => ((cU⁻¹ : Dˣ) : D) * t) hcvU
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using h
    have hc : r z.1 = c₀ := by
      apply eT.injective
      rw [hcomm]
      apply Prod.ext <;> assumption
    have hv : r z.2 = v₀ := by
      apply eT.injective
      rw [hcomm]
      apply Prod.ext <;> assumption
    have hcv : z.1 * z.2 = α := by
      apply e.injective
      rw [map_mul]
      apply Prod.ext
      · exact hA.trans hα.symm
      · change (e z.1).2 * (e z.2).2 = (e α).2
        rw [hcB, hvB, hαB]
    exact ⟨hc, hv, hcv⟩

end ArtinPrimitiveRoots.TypeII.PD
