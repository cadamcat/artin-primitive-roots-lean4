import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RestrictedProduct

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem compact_chart_uniform_tame_support (P : CoverPackage D S H A)
    (hRP : HasRestrictedProductTopology P) (C : Set P.RP)
    (hC : @IsCompact P.RP P.rpTopology C) :
    ∃ T : Finset (FinPlace F),
      ∀ x ∈ C, ∀ v, v ∉ S.Sf → v ∉ T →
        P.compF v x ∈ referenceSubset P (.inl v) := by
  letI : TopologicalSpace P.RP := P.rpTopology
  rcases hRP with ⟨e, heF, -⟩
  let exc : P.RP → Finset (FinPlace F) := fun x => (P.comp_restricted x).toFinset
  have hRef (v : FinPlace F) (hv : v ∉ S.Sf) :
      referenceSubset P (.inl v) = ((P.tame v hv).Kmax : Set (P.loc v).L) := by
    simp [referenceSubset, LocalComponent, localComponentTopology, hv]
  have hAopen : ∀ p, IsOpen (referenceSubset P p) := by
    intro p
    cases p with
    | inl v =>
      by_cases hv : v ∈ S.Sf
      · simp [referenceSubset, hv]
      · simpa [referenceSubset, LocalComponent, localComponentTopology, hv] using
          (P.tame v hv).open_
    | inr w => simp [referenceSubset]
  let pred (x : P.RP) (p : Place F) : Prop :=
    match p with
    | .inl v => v ∉ S.Sf ∧ v ∉ exc x
    | .inr _ => False
  let U (x : P.RP) : Set (CanonicalRP P) :=
    {y | ∀ p, pred x p → y p ∈ referenceSubset P p}
  have hUopen (x : P.RP) : IsOpen (U x) := by
    change IsOpen {y : CanonicalRP P | ∀ p, pred x p → y.1 p ∈ referenceSubset P p}
    exact RestrictedProduct.isOpen_forall_imp_mem hAopen
  have hxe (x : P.RP) : e x ∈ U x := by
    intro p hp
    cases p with
    | inl v =>
      rcases hp with ⟨hv, hvE⟩
      have hvE' : v ∉ (P.comp_restricted x).toFinset := by simpa [exc] using hvE
      have hK : P.compF v x ∈ (P.tame v hv).Kmax := by
        by_contra hn
        have hsupp : v ∈ (P.comp_restricted x).toFinset :=
          (P.comp_restricted x).mem_toFinset.mpr ⟨hv, hn⟩
        exact hvE' hsupp
      change e x (.inl v) ∈ referenceSubset P (.inl v)
      rw [heF]
      rw [hRef v hv]
      exact hK
    | inr w => exact False.elim hp
  have hC' : IsCompact (e '' C) := hC.image e.continuous
  let V : C → Set (CanonicalRP P) := fun x => U x.1
  have hVopen (x : C) : IsOpen (V x) := hUopen x.1
  have hVcover : e '' C ⊆ ⋃ x : C, V x := by
    rintro y ⟨x, hxC, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨x, hxC⟩, hxe x⟩
  obtain ⟨t, ht⟩ := hC'.elim_finite_subcover V hVopen hVcover
  let T : Finset (FinPlace F) := t.biUnion fun x => exc x.1
  refine ⟨T, ?_⟩
  intro x hxC v hv hvT
  have hximage : e x ∈ e '' C := ⟨x, hxC, rfl⟩
  rcases Set.mem_iUnion₂.1 (ht hximage) with ⟨z, hzt, hzU⟩
  have hvE : v ∉ exc z.1 := by
    intro hvE
    exact hvT (Finset.mem_biUnion.mpr ⟨z, hzt, hvE⟩)
  have hz := (Set.mem_setOf_eq.mp hzU) (.inl v) ⟨hv, hvE⟩
  have hz' := hz
  rw [hRef v hv] at hz'
  rw [← heF x v]
  rw [hRef v hv]
  exact hz'

end ArtinPrimitiveRoots.A1.Theta
