import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical Pointwise
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Replace a bounded null-measurable fundamental domain by a bounded measurable one a.e.
Guide: sol-thin-thglobal/PROOFS.md:846–848. Uses IsAddFundamentalDomain.nullMeasurableSet.
Feeds torusCoeff_analytic and all three frozen residue Fourier declarations. -/
theorem adapted_domain_measurable_representative
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) :
    ∃ Q : Set (InfinitePlace F → ℂ), MeasurableSet Q ∧ Bornology.IsBounded Q ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Q volume ∧
      Q =ᵐ[volume] Pd := by
  classical
  let Q := toMeasurable volume Pd ∩ closure Pd
  have hEq : Q =ᵐ[volume] Pd := by
    filter_upwards [hPd.nullMeasurableSet.toMeasurable_ae_eq] with x hx
    apply propext
    change (x ∈ toMeasurable volume Pd ∩ closure Pd) ↔ x ∈ Pd
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h, _⟩
      exact hx.mp h
    · intro h
      exact ⟨hx.mpr h, subset_closure h⟩
  have hmeas : MeasurableSet Q := by
    dsimp [Q]
    exact (measurableSet_toMeasurable _ _).inter isClosed_closure.measurableSet
  have hbounded : Bornology.IsBounded Q := by
    apply Bornology.IsBounded.subset hb.closure
    intro x hx
    exact hx.2
  refine ⟨Q, hmeas, hbounded, ?_, hEq⟩
  refine {
    nullMeasurableSet := hmeas.nullMeasurableSet
    ae_covers := hPd.ae_covers.mono fun x hx => ?_
    aedisjoint := ?_ }
  · obtain ⟨g, hg⟩ := hx
    refine ⟨g, ?_⟩
    change (g : InfinitePlace F → ℂ) +ᵥ x ∈ toMeasurable volume Pd ∩ closure Pd
    exact ⟨subset_toMeasurable _ _ hg, subset_closure hg⟩
  · intro g₁ g₂ hne
    have htrans (g : (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map
        infEmbA.toAddMonoidHom) :
        ((g : InfinitePlace F → ℂ) +ᵥ Q) =ᵐ[volume]
          (g : InfinitePlace F → ℂ) +ᵥ Pd := by
      exact (quasiMeasurePreserving_add_left volume (-(g : InfinitePlace F → ℂ))).vadd_ae_eq_of_ae_eq
        (g : InfinitePlace F → ℂ) hEq
    change AEDisjoint volume ((g₁ : InfinitePlace F → ℂ) +ᵥ Q)
      ((g₂ : InfinitePlace F → ℂ) +ᵥ Q)
    exact (hPd.aedisjoint hne).congr (htrans g₁) (htrans g₂)

end ArtinPrimitiveRoots.A1.Theta
