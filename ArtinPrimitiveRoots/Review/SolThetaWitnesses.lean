import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.Theta.Assemble

set_option autoImplicit false

open NumberField IsDedekindDomain
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Review.SolThetaWitnesses

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

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
#print axioms trivial_character_unramified
#print axioms level_bound_witness
#print axioms top_specialLinear_finiteIndex
#print axioms cover_topology_equality

end ArtinPrimitiveRoots.Review.SolThetaWitnesses
