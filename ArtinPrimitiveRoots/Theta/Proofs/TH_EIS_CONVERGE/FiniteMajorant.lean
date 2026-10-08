import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- A finite-place section has bounded norm on every compact set: its open
right stabilizer makes it locally constant. -/
theorem section_norm_bound_on_compact
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) (T : TorusRep D H v) {s : ℂ}
    (f : L.L → T.V) (hf : IsSection L T s f)
    (K : Set L.L) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖f g‖ ≤ C := by
  obtain ⟨m, hm, hright⟩ := hf.2.2
  have hloc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).2
    intro g
    refine ⟨(fun h : L.L => g⁻¹ * h) ⁻¹' (L.Kc m : Set L.L),
      (L.Kc_open m hm).preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp
    · intro h hh
      simpa only [mul_inv_cancel_left] using hright g (g⁻¹ * h) hh
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hloc.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  exact fun g hg => (hC g hg).trans (le_max_left _ _)

end ArtinPrimitiveRoots.A1.Theta
