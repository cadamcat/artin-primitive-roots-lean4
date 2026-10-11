import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Two triangular transitions represent the same seed coset.
Uses the frozen `cuspStab`/right-coset definitions;
feeds the first conjunct of `E4_eis_siegel`. -/
theorem triangular_transition_unique (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (q q' : CuspCosets F Γ σ)
    (hq : siegelTransition Γ σ σ' q ∈ borelSL F)
    (hq' : siegelTransition Γ σ σ' q' ∈ borelSL F) : q = q' := by
  let b : SL(2,F) := siegelTransition Γ σ σ' q
  let b' : SL(2,F) := siegelTransition Γ σ σ' q'
  have hbtri : b' * b⁻¹ ∈ borelSL F := by
    exact (borelSL F).mul_mem (by simpa [b'] using hq')
      ((borelSL F).inv_mem (by simpa [b] using hq))
  let δ : Γ := q'.out * q.out⁻¹
  have hδcoerce : (δ : SL(2,𝓞 F)) =
      ((q'.out : Γ) : SL(2,𝓞 F)) * ((q.out : Γ) : SL(2,𝓞 F))⁻¹ := rfl
  have hδmap : toSLF F (δ : SL(2,𝓞 F)) =
      toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) *
        (toSLF F ((q.out : Γ) : SL(2,𝓞 F)))⁻¹ := by
    rw [hδcoerce, map_mul, map_inv]
  have hBAeq : b' * b⁻¹ = σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ := by
    dsimp [b, b', siegelTransition]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hδmap]
    group
  have hstab : δ ∈ cuspStab F Γ σ := by
    have htri : σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
      rw [← hBAeq]
      exact hbtri
    simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact htri
  calc
    q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out :=
      (Quotient.out_eq q).symm
    _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q'.out :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr hstab)
    _ = q' := Quotient.out_eq q'

end ArtinPrimitiveRoots.A1.Spec
