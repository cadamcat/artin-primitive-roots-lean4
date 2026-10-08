import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The triangular term has the absolute FIELD norm as its leading coefficient,
even when its diagonal entry is not integral. Guide: `sol-thin-spec/PROOFS.md:350`.
Uses `G2_x_action`; feeds the third conjunct of `E4_eis_siegel`. -/
theorem triangular_transition_term (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (q : CuspCosets F Γ σ)
    (hq : siegelTransition Γ σ σ' q ∈ borelSL F) (s : ℂ) (z : X F) :
    eisTerm F Γ σ s (σ' • z) q =
      ((absFieldNorm F ((siegelTransition Γ σ σ' q) 0 0) : ℝ) : ℂ) ^ (1 + 2 * s) *
        ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s) := by
  let b : SL(2,F) := siegelTransition Γ σ σ' q
  let c : ℝ := absFieldNorm F (b 0 0)
  have hsmul :
      σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • z)) = b • z := by
    change σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • (σ' • z)) = _
    calc
      σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • (σ' • z)) =
          (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • (σ' • z) :=
        smul_smul σ⁻¹ (toSLF F ((q.out : Γ) : SL(2,𝓞 F))) (σ' • z)
      _ = ((σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) * σ') • z :=
        smul_smul (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) σ' z
      _ = b • z := by simpa [b, siegelTransition, mul_assoc]
  have hb10 : b 1 0 = 0 := by
    change b ∈ borelSL F at hq
    exact hq
  have hdet : b 0 0 * b 1 1 = 1 := by
    have hd := b.property
    rw [Matrix.det_fin_two, hb10] at hd
    simpa using hd
  have hb00 : b 0 0 ≠ 0 := by
    intro hzero
    rw [hzero] at hdet
    simp at hdet
  have hc : 0 < c := by
    exact absFieldNorm_pos_of_ne_zero hb00
  have hNpos : 0 < normHeight F z := by
    unfold normHeight
    apply Finset.prod_pos
    intro w hw
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hheight : normHeight F (b • z) = c * normHeight F z := by
    exact (G2_x_action (F := F)).2.1 b (by simpa [b] using hq) z
  calc
    eisTerm F Γ σ s (σ' • z) q =
        ((normHeight F (σ⁻¹ •
          (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • z))) : ℝ) : ℂ) ^ (1 + 2 * s) := by
            rfl
    _ = ((normHeight F (b • z) : ℝ) : ℂ) ^ (1 + 2 * s) := by rw [hsmul]
    _ = ((c * normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s) := by rw [hheight]
    _ = ((c : ℝ) : ℂ) ^ (1 + 2 * s) *
        ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s) := by
          simpa [Complex.ofReal_mul] using
            (Complex.mul_cpow_ofReal_nonneg hc.le hNpos.le (1 + 2 * s))
    _ = ((absFieldNorm F ((siegelTransition Γ σ σ' q) 0 0) : ℝ) : ℂ) ^
          (1 + 2 * s) * ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s) := by
            rfl

end ArtinPrimitiveRoots.A1.Spec
