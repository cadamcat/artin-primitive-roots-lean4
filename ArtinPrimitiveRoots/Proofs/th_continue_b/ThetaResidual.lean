import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaMatrixSmooth

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField
open scoped MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem continuedEis_slPointResidual
    (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
    (M : SL(2, ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y)
    (hM : M • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt x y) :
    ∃ k : GL (Fin 2) ℂ,
      (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy))⁻¹ *
        Matrix.SpecialLinearGroup.toPGL M = (QuotientGroup.mk k : PGL2 ℂ) := by
  let t : SL(2, ℂ) := (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)⁻¹ * M
  have hfix : t • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
    change ((ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)⁻¹ * M) •
      ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) = _
    rw [mul_smul, hM, ← continuedEis_ptMat_smul_base x y hy]
    exact inv_smul_smul _ _
  refine ⟨(t : GL (Fin 2) ℂ), continuedEis_slFixBase_unitary F t hfix, ?_⟩
  have hmul := (Matrix.SpecialLinearGroup.toPGL).map_mul
    (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)⁻¹ M
  have hinv := congrArg (fun a => a * Matrix.SpecialLinearGroup.toPGL M)
    ((Matrix.SpecialLinearGroup.toPGL).map_inv
      (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy))
  have hquot (s : SL(2, ℂ)) : Matrix.SpecialLinearGroup.toPGL s =
      (QuotientGroup.mk (s : GL (Fin 2) ℂ) : PGL2 ℂ) := rfl
  exact (hmul.trans hinv).symm.trans (hquot t)

end ArtinPrimitiveRoots.A1.Theta
