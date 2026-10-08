import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem localCover_weaklyLocallyCompact (P : CoverPackage D S H A) (v : FinPlace F) :
    WeaklyLocallyCompactSpace (P.loc v).L := by
  let L := (P.loc v).L
  letI : TopologicalSpace L := (P.loc v).top
  letI : Group L := (P.loc v).grp
  letI : IsTopologicalGroup L := (P.loc v).tg
  refine ⟨fun x => ?_⟩
  let K : Set L := (P.loc v).Kc (P.loc v).m0
  have hK : IsCompact K := (P.loc v).Kc_compact _ le_rfl
  have hKo : IsOpen K := (P.loc v).Kc_open _ le_rfl
  let e : L ≃ₜ L := Homeomorph.mulLeft x
  refine ⟨e '' K, hK.image e.continuous, ?_⟩
  have hx : x ∈ e '' K := by
    refine ⟨1, ?_, ?_⟩
    · exact (P.loc v).Kc _ |>.one_mem
    · simp [e]
  exact (e.isOpenMap _ hKo).mem_nhds hx

theorem canonicalRP_weaklyLocallyCompact (P : CoverPackage D S H A) :
    WeaklyLocallyCompactSpace (CanonicalRP P) := by
  letI : ∀ p : Place F, WeaklyLocallyCompactSpace (LocalComponent P p) := by
    intro p
    cases p with
    | inl v => exact localCover_weaklyLocallyCompact P v
    | inr w =>
      change WeaklyLocallyCompactSpace (PGL2 ℂ)
      unfold PGL2
      haveI : FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℂ) := by infer_instance
      haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
        LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
      haveI : LocallyCompactSpace (GL (Fin 2) ℂ) := by infer_instance
      exact inferInstance
  have hAopen : ∀ p, IsOpen (referenceSubset P p) := by
    intro p
    cases p with
    | inl v =>
      by_cases hv : v ∈ S.Sf
      · simp [referenceSubset, hv]
      · simpa [referenceSubset, LocalComponent, localComponentTopology, hv] using
          (P.tame v hv).open_
    | inr w => simp [referenceSubset]
  have hAcompact : ∀ᶠ p in cofinite, IsCompact (referenceSubset P p) := by
    apply Filter.eventually_cofinite.mpr
    have hS : (Set.image (fun v : FinPlace F => (Sum.inl v : Place F))
        (S.Sf : Set (FinPlace F))).Finite :=
      S.Sf.finite_toSet.image fun v => (Sum.inl v : Place F)
    have hInf : (Set.image (fun w : InfinitePlace F => (Sum.inr w : Place F))
        (Set.univ : Set (InfinitePlace F))).Finite :=
      (Set.toFinite _).image fun w => (Sum.inr w : Place F)
    refine (hS.union hInf).subset ?_
    intro p hp
    cases p with
    | inl v =>
      by_cases hv : v ∈ S.Sf
      · exact Or.inl ⟨v, hv, rfl⟩
      · have hc : IsCompact (referenceSubset P (Sum.inl v)) := by
          simpa [referenceSubset, LocalComponent, localComponentTopology, hv] using
            (P.tame v hv).compact
        exact (hp hc).elim
    | inr w => exact Or.inr ⟨w, Set.mem_univ _, rfl⟩
  exact RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
    (R := LocalComponent P) (A := referenceSubset P) hAopen hAcompact

theorem coverPackage_rp_weaklyLocallyCompact (P : CoverPackage D S H A)
    (hRP : HasRestrictedProductTopology P) :
    @WeaklyLocallyCompactSpace P.RP P.rpTopology := by
  letI : TopologicalSpace P.RP := P.rpTopology
  rcases hRP with ⟨e, -, -⟩
  letI : WeaklyLocallyCompactSpace (CanonicalRP P) := canonicalRP_weaklyLocallyCompact P
  refine ⟨fun x => ?_⟩
  let y : CanonicalRP P := e x
  obtain ⟨C, hC, hyC⟩ := exists_compact_mem_nhds y
  have hyI : y ∈ interior C := mem_interior_iff_mem_nhds.2 hyC
  refine ⟨e.symm '' C, hC.image e.symm.continuous, ?_⟩
  have hx : x ∈ e.symm '' interior C := ⟨y, hyI, by simp [y]⟩
  have hO : IsOpen (e.symm '' interior C) := e.symm.isOpenMap _ isOpen_interior
  exact Filter.mem_of_superset (hO.mem_nhds hx) (Set.image_mono interior_subset)

theorem compact_quotient_lift_charts (P : CoverPackage D S H A)
    (hRP : HasRestrictedProductTopology P) (K : Set P.tc.G)
    (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ (t : Finset P.tc.G) (C : P.tc.G → Set P.RP),
      (∀ c ∈ t, @IsCompact P.RP P.rpTopology (C c)) ∧
      ∀ g ∈ K, ∃ c ∈ t, ∃ x ∈ C c, P.q x = g := by
  letI : TopologicalSpace P.RP := P.rpTopology
  letI : TopologicalSpace P.tc.G := P.tc.topology
  letI : @IsTopologicalGroup P.RP P.rpTopology P.rpGrp := P.rpTopGroup
  haveI : WeaklyLocallyCompactSpace P.RP := coverPackage_rp_weaklyLocallyCompact P hRP
  have hq : IsQuotientMap P.q := P.q_quotient
  have hqopen : IsOpenMap P.q :=
    (MonoidHom.isOpenQuotientMap_iff_isQuotientMap.mpr hq).isOpenMap
  let lift : P.tc.G → P.RP := fun g => Classical.choose (P.q_surj g)
  have hlift (g : P.tc.G) : P.q (lift g) = g := Classical.choose_spec (P.q_surj g)
  let C : P.tc.G → Set P.RP := fun g =>
    Classical.choose (exists_compact_mem_nhds (lift g))
  have hC (g : P.tc.G) : IsCompact (C g) :=
    (Classical.choose_spec (exists_compact_mem_nhds (lift g))).1
  have hCn (g : P.tc.G) : C g ∈ 𝓝 (lift g) :=
    (Classical.choose_spec (exists_compact_mem_nhds (lift g))).2
  let U : P.tc.G → Set P.tc.G := fun g => P.q '' interior (C g)
  have hUopen (g : P.tc.G) : IsOpen (U g) := hqopen _ isOpen_interior
  have hgU (g : P.tc.G) : g ∈ U g := by
    refine ⟨lift g, mem_interior_iff_mem_nhds.2 (hCn g), hlift g⟩
  have hcover : K ⊆ ⋃ g, U g := by
    intro g hg
    exact Set.mem_iUnion.2 ⟨g, hgU g⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  refine ⟨t, C, fun c hc => hC c, ?_⟩
  intro g hg
  rcases Set.mem_iUnion₂.1 (ht hg) with ⟨c, hct, hgc⟩
  rcases hgc with ⟨x, hx, hqx⟩
  exact ⟨c, hct, x, interior_subset hx, hqx⟩

end ArtinPrimitiveRoots.A1.Theta
