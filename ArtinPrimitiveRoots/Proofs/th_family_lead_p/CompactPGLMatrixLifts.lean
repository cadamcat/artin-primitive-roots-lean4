import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ArchMatrixResidue
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RestrictedProduct

set_option autoImplicit false
open NumberField Matrix Filter Topology
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

private theorem compact_lift_of_open_surjection {X Y : Type}
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Function.Surjective f) (ho : IsOpenMap f)
    (K : Set Y) (hK : IsCompact K) :
    ∃ C : Set X, IsCompact C ∧ ∀ y ∈ K, ∃ x ∈ C, f x = y := by
  let lift : Y → X := fun y => Classical.choose (hf y)
  have hlift (y : Y) : f (lift y) = y := Classical.choose_spec (hf y)
  let C : Y → Set X := fun y =>
    Classical.choose (exists_compact_mem_nhds (lift y))
  have hC (y : Y) : IsCompact (C y) :=
    (Classical.choose_spec (exists_compact_mem_nhds (lift y))).1
  have hCn (y : Y) : C y ∈ 𝓝 (lift y) :=
    (Classical.choose_spec (exists_compact_mem_nhds (lift y))).2
  let U : Y → Set Y := fun y => f '' interior (C y)
  have hU (y : Y) : IsOpen (U y) := ho _ isOpen_interior
  have hyU (y : Y) : y ∈ U y :=
    ⟨lift y, mem_interior_iff_mem_nhds.2 (hCn y), hlift y⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU
    (fun y hy => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  refine ⟨⋃ y ∈ t, C y, t.isCompact_biUnion (fun y hy => hC y), ?_⟩
  intro y hy
  rcases Set.mem_iUnion₂.1 (ht hy) with ⟨z, hzt, x, hx, hfx⟩
  exact ⟨x, Set.mem_iUnion₂.2 ⟨z, hzt, interior_subset hx⟩, hfx⟩

/-- Compact PGL tuples have compact matrix lifts contained in the invertible locus. -/
theorem theta_compact_pgl_matrix_lifts
    (K : Set (InfinitePlace F → PGL2 ℂ)) (hK : IsCompact K) :
    ∃ CM : Set (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ),
      IsCompact CM ∧ CM ⊆ thetaMatrixRegion ∧
      ∀ c ∈ K, ∃ M : InfinitePlace F → GL (Fin 2) ℂ,
        (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) ∈ CM ∧
        ∀ w, (QuotientGroup.mk (M w) : PGL2 ℂ) = c w := by
  haveI : FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℂ) := by infer_instance
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  haveI : LocallyCompactSpace (GL (Fin 2) ℂ) := by infer_instance
  have hlifts : ∀ w : InfinitePlace F,
      ∃ C : Set (GL (Fin 2) ℂ), IsCompact C ∧
        ∀ c ∈ (fun z : InfinitePlace F → PGL2 ℂ => z w) '' K,
          ∃ m ∈ C, (QuotientGroup.mk m : PGL2 ℂ) = c := by
    intro w
    exact compact_lift_of_open_surjection
      (fun m : GL (Fin 2) ℂ => (QuotientGroup.mk m : PGL2 ℂ))
      Quotient.mk_surjective QuotientGroup.isOpenMap_coe
      _ (hK.image (continuous_apply w))
  choose C hC hcover using hlifts
  let CM : Set (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) :=
    (fun m : InfinitePlace F → GL (Fin 2) ℂ =>
      fun w => (m w : Matrix (Fin 2) (Fin 2) ℂ)) '' Set.pi Set.univ C
  have hcoe : Continuous (fun m : InfinitePlace F → GL (Fin 2) ℂ =>
      fun w => (m w : Matrix (Fin 2) (Fin 2) ℂ)) := by
    exact continuous_pi fun w => Units.continuous_val.comp (continuous_apply w)
  refine ⟨CM, (isCompact_univ_pi hC).image hcoe, ?_, ?_⟩
  · rintro M ⟨m, hm, rfl⟩ w
    exact (m w).det_ne_zero
  · intro c hc
    have hex : ∀ w, ∃ m ∈ C w, (QuotientGroup.mk m : PGL2 ℂ) = c w :=
      fun w => hcover w (c w) (Set.mem_image_of_mem _ hc)
    choose m hm hq using hex
    refine ⟨m, ?_, hq⟩
    exact ⟨m, fun w hw => hm w, rfl⟩

end ArtinPrimitiveRoots.Proofs.majorant_sol
