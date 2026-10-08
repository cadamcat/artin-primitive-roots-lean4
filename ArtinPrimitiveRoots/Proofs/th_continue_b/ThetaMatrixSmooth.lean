import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaBasics

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open scoped ContDiff MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem continuedEis_jointMatrix_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : GL (Fin 2) ℂ) (B : SL(2, ℂ))
    (x y : E → ℂ) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) :
    ∀ i j, ContDiff ℝ ∞ (fun q =>
      ((continuedEis_conjugateRoot γ (x q) * B *
        ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
          (@Multiplicative.ofAdd ℂ (y q)) : SL(2, ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) i j) := by
  let gM : Matrix (Fin 2) (Fin 2) ℂ := γ
  let giM : Matrix (Fin 2) (Fin 2) ℂ := (γ⁻¹ : GL (Fin 2) ℂ)
  let nM (q : E) : Matrix (Fin 2) (Fin 2) ℂ := !![1, x q; 0, 1]
  have hnM : ∀ i j, ContDiff ℝ ∞ (fun q => nM q i j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact contDiff_const
    · exact hx
    · exact contDiff_const
    · exact contDiff_const
  have h1 := continuedEis_matrixMul_contDiff (fun _ : E => giM) nM
    (fun _ _ => contDiff_const) hnM
  have h2 := continuedEis_matrixMul_contDiff (fun q => giM * nM q)
    (fun _ => gM) h1 (fun _ _ => contDiff_const)
  let dM (q : E) : Matrix (Fin 2) (Fin 2) ℂ := continuedEis_conjugateRoot γ (x q)
  have hdM : ∀ i j, ContDiff ℝ ∞ (fun q => dM q i j) := by
    intro i j
    change ContDiff ℝ ∞ (fun q => (giM * nM q * gM) i j)
    exact h2 i j
  let uM (q : E) : Matrix (Fin 2) (Fin 2) ℂ := !![1, y q; 0, 1]
  have huM : ∀ i j, ContDiff ℝ ∞ (fun q => uM q i j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact contDiff_const
    · exact hy
    · exact contDiff_const
    · exact contDiff_const
  have h3 := continuedEis_matrixMul_contDiff dM
    (fun _ => (B : Matrix (Fin 2) (Fin 2) ℂ)) hdM (fun _ _ => contDiff_const)
  have h4 := continuedEis_matrixMul_contDiff
    (fun q => dM q * (B : Matrix (Fin 2) (Fin 2) ℂ)) uM h3 huM
  intro i j
  simpa only [Matrix.SpecialLinearGroup.coe_mul, continuedEis_upperHom_matrix]
    using h4 i j

end ArtinPrimitiveRoots.A1.Theta
