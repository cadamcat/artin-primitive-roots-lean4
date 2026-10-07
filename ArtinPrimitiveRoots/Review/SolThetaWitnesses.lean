import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.Theta.Assemble

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Review.SolThetaWitnesses

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A tame basis itself rules out the zero-dimensional carrier required by GlobalDatum. -/
theorem tame_basis_carrier_nontrivial {D : FieldData F} {H : HilbertData F}
    {v : FinPlace F} (T : TorusRep D H v) (B : TameTorusBasis T) : Nontrivial T.V := by
  have he : B.e 0 ≠ 0 := B.linIndep.ne_zero 0
  exact ⟨⟨(0 : T.V), B.e 0, Ne.symm he⟩⟩

/-- The `Re(s) > 1/2` input is inhabited at `s = 1`. -/
theorem whittaker_half_plane_witness : (1 / 2 : ℝ) < (1 : ℂ).re := by
  norm_num

/-- The new complex-kernel measurability input and every old moment bound are compatible. -/
theorem zero_kernel_measurability_and_moments :
    AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)) (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      ∀ β : ℝ, IntegrableOn
        (fun T => ‖(0 : ℂ)‖ * T ^ β / T) (Set.Ioi (0 : ℝ)) := by
  constructor
  · exact aestronglyMeasurable_const
  · intro β
    simp

/-- The unit representative satisfies the precise normalization needed at the unit ideal. -/
theorem one_generates_unit_ideal (S : SData F CE condη) : S.IsGen (1 : F) ⊤ := by
  refine ⟨?_, one_ne_zero, ?_⟩
  · refine ⟨by simp, ?_⟩
    intro v hv hle
    exact v.isMaximal.ne_top (top_le_iff.mp hle)
  · intro v hv
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.coeIdeal_top]

/-- Constant-one representatives witness that the added B0 premise is consistent. -/
theorem unit_generator_premise_witness (S : SData F CE condη) :
    ∃ cgen : S.SqfExtIdeal → F,
      ∀ I : S.SqfExtIdeal, I.1 = ⊤ → S.IsGen (cgen I) ⊤ := by
  refine ⟨fun _ => 1, ?_⟩
  intro I hI
  change S.IsGen (1 : F) ⊤
  exact one_generates_unit_ideal S

/-!
The full wild-place nontrivial `TorusRep` witness requires the local finite-quotient
Heisenberg construction in P-TORUS-IND; the review-only zero representation is not
a witness for the refined producer. A full `AnalyticFamily`/`ContinuedEis` witness
with `Fam.T0 = S.Sf` likewise requires the global construction in P-EIS. Their
existence theorem bodies remain the theory-level obligations in the source files.
-/

theorem zero_sheetHypC (δ : ℝ) : SheetHypC δ (fun _ : ℂ => (0 : ℂ)) := by
  constructor
  · exact contDiff_const.contDiffOn
  · intro j A hA
    refine ⟨0, ?_⟩
    intro y hy
    simp [normDeriv]

example (δ : ℝ) : SheetHypC δ (fun _ : ℂ => (0 : ℂ)) := zero_sheetHypC δ

theorem zero_joint_smooth_on_finite_product (ι : Type) [Fintype ι] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : (ι → ℂ) × (ι → ℂ) => (0 : ℂ)) := by
  exact contDiff_const

theorem zero_cutoff_smooth_compact :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (0 : ℂ)) ∧
      HasCompactSupport (fun _ : ℝ => (0 : ℂ)) := by
  constructor
  · exact contDiff_const
  · exact HasCompactSupport.intro' isCompact_empty isClosed_empty (by simp)

theorem trivial_character_unramified (v : FinPlace F) :
    (1 : HeckeChar F).UnramifiedAt v := by
  intro u hu huinv
  simp [HeckeChar.UnramifiedAt, HeckeChar.loc]

theorem level_bound_witness (T0 : Finset (FinPlace F)) (m0 : FinPlace F → ℕ) :
    ∃ m : FinPlace F → ℕ, ∀ v ∈ T0, m0 v ≤ m v := by
  refine ⟨m0, ?_⟩
  intro v hv
  exact le_rfl

theorem top_specialLinear_finiteIndex :
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))).FiniteIndex := by
  infer_instance

theorem cover_topology_equality {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F} (C : ThetaCover D S H A) :
    ∃ t : TopologicalSpace C.G, t = C.topology := ⟨C.topology, rfl⟩

example : CompleteSpace ℂ := inferInstance

#print axioms zero_sheetHypC
#print axioms zero_joint_smooth_on_finite_product
#print axioms zero_cutoff_smooth_compact
#print axioms tame_basis_carrier_nontrivial
#print axioms whittaker_half_plane_witness
#print axioms zero_kernel_measurability_and_moments
#print axioms one_generates_unit_ideal
#print axioms unit_generator_premise_witness
#print axioms trivial_character_unramified
#print axioms level_bound_witness
#print axioms top_specialLinear_finiteIndex
#print axioms cover_topology_equality

end ArtinPrimitiveRoots.Review.SolThetaWitnesses
