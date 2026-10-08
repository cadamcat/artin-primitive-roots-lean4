import ArtinPrimitiveRoots.Theta.Res

set_option autoImplicit false
open NumberField MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem specPosSet_isOpen : IsOpen (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  unfold ArtinPrimitiveRoots.A1.Spec.posSet
  have h := isOpen_set_pi (i := Set.univ)
    (s := fun _ : InfinitePlace F => {z : ℂ × ℝ | 0 < z.2}) (Set.toFinite _)
    (by intro w hw; exact isOpen_Ioi.preimage continuous_snd)
  simpa [Set.pi] using h

/-- Every fixed coordinate derivative of a P-SPEC residue is bounded on a compact coordinate
set in the positive-height region. -/
theorem spec_residue_iteratedFDeriv_bound
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))}
    (σ : Matrix.SpecialLinearGroup (Fin 2) F)
    (d : ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F Γ σ (1 / 6 : ℝ))
    (n : ℕ) (K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F))
    (hK : IsCompact K) (hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n
        (fun p => d.res (ArtinPrimitiveRoots.A1.Spec.ptX F p)) p‖ ≤ C := by
  let f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
    fun p => d.res (ArtinPrimitiveRoots.A1.Spec.ptX F p)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n f)
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    ContinuousOn.continuousOn_iteratedFDeriv d.res_smooth specPosSet_isOpen (by simp)
  have himage : IsCompact (iteratedFDeriv ℝ n f '' K) :=
    hK.image_of_continuousOn (hcont.mono hKpos)
  obtain ⟨C, hC⟩ := himage.isBounded.subset_closedBall (0 : _)
  refine ⟨C, fun p hp => ?_⟩
  have hmem := hC (Set.mem_image_of_mem _ hp)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hmem

/-- The finite reconstructed residue sum also has bounded coordinate derivatives on compact
positive-height sets. -/
theorem spec_componentTheta_iteratedFDeriv_bound
    [IsTotallyComplex F] {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) (j : C.J)
    (n : ℕ) (K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F))
    (hK : IsCompact K) (hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    ∃ Cb : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n
        (fun p => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F p)) p‖ ≤ Cb := by
  let f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
    fun p => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F p)
  have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
    dsimp [f, ContinuedEisComponents.componentTheta]
    apply ContDiffOn.sum
    intro i hi
    simpa [smul_eq_mul] using
      (C.d j i).res_smooth.const_smul (C.c j i (1 / 6))
  have hcont : ContinuousOn (iteratedFDeriv ℝ n f)
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    ContinuousOn.continuousOn_iteratedFDeriv hsmooth specPosSet_isOpen (by simp)
  have himage : IsCompact (iteratedFDeriv ℝ n f '' K) :=
    hK.image_of_continuousOn (hcont.mono hKpos)
  obtain ⟨Cbound, hCbound⟩ := himage.isBounded.subset_closedBall (0 : _)
  refine ⟨Cbound, fun p hp => ?_⟩
  have hmem := hCbound (Set.mem_image_of_mem _ hp)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hmem

end ArtinPrimitiveRoots.A1.Theta
