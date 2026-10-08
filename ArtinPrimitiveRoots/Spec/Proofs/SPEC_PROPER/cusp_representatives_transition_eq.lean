import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A triangular transition between distinct entries of the cusp representative system
forces equality of their indices.
Guide: sol-thin-spec/PROOFS.md:205. Uses d.reps_bijective and the right-coset
relations underlying R3_cusps_finite; feeds siegel_high_height_overlap_finite. -/
theorem cusp_representatives_transition_eq
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ)
    (i j : d.ι) (γ : Γ)
    (htri : (d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i ∈ borelSL F) :
    i = j := by
  classical
  let c₁ : CuspCosets F Γ (d.σ i) :=
    Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) (1 : Γ)
  let c₂ : CuspCosets F Γ (d.σ j) :=
    Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ j))) γ
  have hc₁ : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) c₁.out =
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) (1 : Γ) := by
    simpa [c₁] using (Quotient.out_eq' c₁)
  have hc₂ : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ j))) c₂.out =
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ j))) γ := by
    simpa [c₂] using (Quotient.out_eq' c₂)
  have eval_eq (k : d.ι) (c : CuspCosets F Γ (d.σ k)) (δ : Γ)
      (hc : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ k))) c.out =
        Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ k))) δ) :
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ k)⁻¹ * toSLF F (c.out : SL(2,𝓞 F))) =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ k)⁻¹ * toSLF F (δ : SL(2,𝓞 F))) := by
    have hstab : δ * c.out⁻¹ ∈ cuspStab F Γ (d.σ k) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hc)
    have hB : ((d.σ k)⁻¹ * toSLF F (δ : SL(2,𝓞 F))) *
        ((d.σ k)⁻¹ * toSLF F (c.out : SL(2,𝓞 F)))⁻¹ ∈ borelSL F := by
      have hconj := hstab
      simpa [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hconj
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr hB
  let v₁ : SL(2,F) := (d.σ i)⁻¹ * toSLF F (1 : SL(2,𝓞 F))
  let v₂ : SL(2,F) := (d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F))
  have htriQuot : Quotient.mk (QuotientGroup.rightRel (borelSL F)) v₁ =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) v₂ := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa [v₁, v₂, map_one, mul_assoc] using htri
  let p : Σ k, CuspCosets F Γ (d.σ k) := ⟨i, c₁⟩
  let q : Σ k, CuspCosets F Γ (d.σ k) := ⟨j, c₂⟩
  have hmaps :
      (fun p : (Σ k, CuspCosets F Γ (d.σ k)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))) p =
      (fun p : (Σ k, CuspCosets F Γ (d.σ k)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))) q := by
    calc
      _ = Quotient.mk (QuotientGroup.rightRel (borelSL F)) v₁ := by
        simpa [p, v₁] using eval_eq i c₁ 1 hc₁
      _ = Quotient.mk (QuotientGroup.rightRel (borelSL F)) v₂ := htriQuot
      _ = _ := by
        simpa [q, v₂] using (eval_eq j c₂ γ hc₂).symm
  have hpq := d.reps_bijective.injective hmaps
  exact congrArg (fun p : Σ k, CuspCosets F Γ (d.σ k) => p.1) hpq
end ArtinPrimitiveRoots.A1.Spec
