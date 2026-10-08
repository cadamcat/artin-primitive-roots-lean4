import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactPGLMatrixLifts
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.TailSupport

set_option autoImplicit false
open NumberField Matrix Filter Topology
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def thetaFiniteLevelRPSet (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ) : Set P.RP :=
  {r | (∀ v ∈ T0, P.compF v r ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v r ∈ (P.tame v (fun h => hv (hsub h))).Kmax}

private theorem thetaFiniteLevelRPSet_one (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ) :
    (1 : P.RP) ∈ thetaFiniteLevelRPSet P T0 hsub m := by
  constructor
  · intro v hv
    simpa only [map_one] using ((P.loc v).Kc (m v)).one_mem
  · intro v hv
    simpa only [map_one] using (P.tame v (fun h => hv (hsub h))).Kmax.one_mem

private theorem thetaFiniteLevelRPSet_isOpen (P : CoverPackage D S H A)
    (hRP : HasRestrictedProductTopology P)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) :
    @IsOpen P.RP P.rpTopology (thetaFiniteLevelRPSet P T0 hsub m) := by
  letI : TopologicalSpace P.RP := P.rpTopology
  obtain ⟨e, heF, -⟩ := hRP
  have hAopen : ∀ p, IsOpen (referenceSubset P p) := by
    intro p
    cases p with
    | inl v =>
      by_cases hv : v ∈ S.Sf
      · simp [referenceSubset, hv]
      · simpa [referenceSubset, LocalComponent, localComponentTopology, hv] using
          (P.tame v hv).open_
    | inr w => simp [referenceSubset]
  have hRef (v : FinPlace F) (hv : v ∉ S.Sf) :
      referenceSubset P (.inl v) = ((P.tame v hv).Kmax : Set (P.loc v).L) := by
    simp [referenceSubset, LocalComponent, localComponentTopology, hv]
  let pred : Place F → Prop := fun p => match p with
    | .inl v => v ∉ T0
    | .inr _ => False
  let UT : Set (CanonicalRP P) :=
    {x | ∀ p, pred p → x p ∈ referenceSubset P p}
  have hUT : IsOpen UT := by
    change IsOpen {x : CanonicalRP P | ∀ p, pred p → x.1 p ∈ referenceSubset P p}
    exact RestrictedProduct.isOpen_forall_imp_mem hAopen
  have hTailEq : {r : P.RP | ∀ v (hv : v ∉ T0),
      P.compF v r ∈ (P.tame v (fun h => hv (hsub h))).Kmax} = e ⁻¹' UT := by
    ext r
    constructor
    · intro hr p hp
      cases p with
      | inl v =>
        have hv : v ∉ T0 := hp
        have hvS : v ∉ S.Sf := fun h => hv (hsub h)
        change e r (.inl v) ∈ referenceSubset P (.inl v)
        rw [heF, hRef v hvS]
        exact hr v hv
      | inr w => exact False.elim hp
    · intro hr v hv
      have h := hr (.inl v) hv
      have hvS : v ∉ S.Sf := fun h => hv (hsub h)
      rw [heF, hRef v hvS] at h
      exact h
  have hFopen : IsOpen {r : P.RP | ∀ v ∈ T0, P.compF v r ∈ (P.loc v).Kc (m v)} := by
    have h := isOpen_biInter_finset (s := T0)
      (f := fun v => {r : P.RP | P.compF v r ∈ (P.loc v).Kc (m v)})
      (fun v hv => ((P.loc v).Kc_open (m v) (hm v hv)).preimage (P.compF_cont v))
    convert h using 1
    ext r
    simp
  change IsOpen ({r : P.RP | ∀ v ∈ T0, P.compF v r ∈ (P.loc v).Kc (m v)} ∩
    {r | ∀ v (hv : v ∉ T0), P.compF v r ∈ (P.tame v (fun h => hv (hsub h))).Kmax})
  rw [hTailEq]
  exact hFopen.inter (hUT.preimage e.continuous)

/-- A finite set of anchors and one compact invertible matrix set cover every compact adelic set
by pure archimedean variation and the prescribed finite level. -/
theorem theta_compact_finite_level_matrix_charts (P : CoverPackage D S H A)
    (hRP : HasRestrictedProductTopology P)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v)
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ (J : Finset P.tc.G)
      (CM : Set (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ)),
      IsCompact CM ∧ CM ⊆ thetaMatrixRegion ∧
      ∀ g ∈ K, ∃ j ∈ J, ∃ M : InfinitePlace F → GL (Fin 2) ℂ,
        (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) ∈ CM ∧
        ∃ k ∈ levelSet P T0 hsub m,
          g = P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * j * k := by
  letI : TopologicalSpace P.RP := P.rpTopology
  letI : TopologicalSpace P.tc.G := P.tc.topology
  letI : @IsTopologicalGroup P.RP P.rpTopology P.rpGrp := P.rpTopGroup
  obtain ⟨s, C, hC, hCover⟩ := compact_quotient_lift_charts P hRP K hK
  let CR : Set P.RP := ⋃ a ∈ s, C a
  have hCR : IsCompact CR := s.isCompact_biUnion (fun a ha => hC a ha)
  have hLift : ∀ g ∈ K, ∃ r ∈ CR, P.q r = g := by
    intro g hg
    obtain ⟨a, ha, r, hr, hqr⟩ := hCover g hg
    exact ⟨r, Set.mem_iUnion₂.2 ⟨a, ha, hr⟩, hqr⟩
  let U := thetaFiniteLevelRPSet P T0 hsub m
  have hU : IsOpen U := thetaFiniteLevelRPSet_isOpen P hRP T0 hsub m hm
  have hUone : (1 : P.RP) ∈ U := thetaFiniteLevelRPSet_one P T0 hsub m
  let V : P.RP → Set P.RP := fun a => {r | a⁻¹ * r ∈ U}
  have hV (a : P.RP) : IsOpen (V a) :=
    hU.preimage (continuous_const.mul continuous_id)
  have hVCover : CR ⊆ ⋃ a, V a := by
    intro r hr
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    change r⁻¹ * r ∈ U
    simpa only [inv_mul_cancel] using hUone
  obtain ⟨t, ht⟩ := hCR.elim_finite_subcover V hV hVCover
  obtain ⟨e, -, heC⟩ := hRP
  have hCompC (w : InfinitePlace F) : Continuous (P.compC w) := by
    have heval : @Continuous P.RP (LocalComponent P (.inr w))
        P.rpTopology (localComponentTopology P (.inr w)) (fun r => e r (.inr w)) :=
      (RestrictedProduct.continuous_eval (R := LocalComponent P)
        (A := referenceSubset P) (.inr w)).comp e.continuous
    have heval' : @Continuous P.RP (LocalComponent P (.inr w))
        P.rpTopology (localComponentTopology P (.inr w)) (P.compC w) :=
      heval.congr (fun r => heC r w)
    change @Continuous P.RP (PGL2 ℂ) P.rpTopology _ (P.compC w)
    change @Continuous P.RP (PGL2 ℂ) P.rpTopology inferInstance (P.compC w) at heval'
    exact heval'
  let rel : P.RP → P.RP → (InfinitePlace F → PGL2 ℂ) :=
    fun a r w => P.compC w r * (P.compC w a)⁻¹
  have hRel (a : P.RP) : Continuous (rel a) :=
    continuous_pi fun w => (hCompC w).mul continuous_const
  let CP : Set (InfinitePlace F → PGL2 ℂ) := ⋃ a ∈ t, rel a '' CR
  have hCP : IsCompact CP := t.isCompact_biUnion (fun a ha => hCR.image (hRel a))
  obtain ⟨CM, hCM, hCMreg, hMatrices⟩ := theta_compact_pgl_matrix_lifts CP hCP
  refine ⟨t.image P.q, CM, hCM, hCMreg, ?_⟩
  intro g hg
  obtain ⟨r, hr, hqr⟩ := hLift g hg
  obtain ⟨a, ha, hcoset⟩ := Set.mem_iUnion₂.1 (ht hr)
  let c := rel a r
  have hcCP : c ∈ CP := Set.mem_iUnion₂.2 ⟨a, ha, Set.mem_image_of_mem _ hr⟩
  obtain ⟨M, hMC, hMQ⟩ := hMatrices c hcCP
  have hTuple : (fun w => (QuotientGroup.mk (M w) : PGL2 ℂ)) = c := funext hMQ
  let kr : P.RP := a⁻¹ * (thetaArchRP P c)⁻¹ * r
  have hkrC : ∀ w, P.compC w kr = 1 := by
    intro w
    simp only [kr, map_mul, map_inv, thetaArchRP_compC]
    dsimp [c, rel]
    group
  have hkrF (v : FinPlace F) : P.compF v kr = P.compF v (a⁻¹ * r) := by
    simp only [kr, map_mul, map_inv, thetaArchRP_compF, inv_one, mul_one]
  have hkrLevel : P.q kr ∈ levelSet P T0 hsub m := by
    refine ⟨kr, rfl, hkrC, ?_, ?_⟩
    · intro v hv
      rw [hkrF]
      exact hcoset.1 v hv
    · intro v hv
      rw [hkrF]
      exact hcoset.2 v hv
  have hrshape : r = thetaArchRP P c * a * kr := by
    dsimp [kr]
    group
  refine ⟨P.q a, Finset.mem_image.2 ⟨a, ha, rfl⟩, M, hMC, P.q kr, hkrLevel, ?_⟩
  rw [hTuple, ← hqr]
  simpa only [map_mul] using congrArg P.q hrshape

end ArtinPrimitiveRoots.Proofs.majorant_sol
