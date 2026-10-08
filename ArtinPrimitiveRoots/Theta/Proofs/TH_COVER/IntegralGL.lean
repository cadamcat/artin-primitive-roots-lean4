import ArtinPrimitiveRoots.A1.Field

/-! Lifting integral GL₂ matrices from a finite completion to its valuation ring. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Integral entries and integral inverse determinant give a GL₂ unit over the valuation ring. -/
theorem integralGL2_lift (v : FinPlace F)
    (g : GL (Fin 2) (v.adicCompletion F))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F)
    (hd : (g⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈
      v.adicCompletionIntegers F) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers F),
      Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k = g := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let j : O →+* K := O.subtype
  let ιM : Matrix (Fin 2) (Fin 2) O →+* Matrix (Fin 2) (Fin 2) K := RingHom.mapMatrix j
  have hdEq : (g⁻¹ : GL (Fin 2) K).val.det = (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ := by
    change ((Matrix.GeneralLinearGroup.det (g⁻¹) : Kˣ) : K) =
      ((Matrix.GeneralLinearGroup.det g : Kˣ) : K)⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hdi : (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ ∈ O := by
    rw [← hdEq]
    exact hd
  have hi : ∀ i j, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O := by
    have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ •
          !![(g : Matrix (Fin 2) (Fin 2) K) 1 1, -(g : Matrix (Fin 2) (Fin 2) K) 0 1;
            -(g : Matrix (Fin 2) (Fin 2) K) 1 0, (g : Matrix (Fin 2) (Fin 2) K) 0 0] := by
      rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv,
        Matrix.adjugate_fin_two]
    intro i j
    rw [hinv]
    fin_cases i <;> fin_cases j
    · simpa [Matrix.smul_apply, smul_eq_mul] using O.toSubring.mul_mem hdi (hg 1 1)
    · simpa [Matrix.smul_apply, smul_eq_mul] using O.toSubring.mul_mem hdi (O.toSubring.neg_mem (hg 0 1))
    · simpa [Matrix.smul_apply, smul_eq_mul] using O.toSubring.mul_mem hdi (O.toSubring.neg_mem (hg 1 0))
    · simpa [Matrix.smul_apply, smul_eq_mul] using O.toSubring.mul_mem hdi (hg 0 0)
  let A : Matrix (Fin 2) (Fin 2) O := fun i j =>
    ⟨(g : Matrix (Fin 2) (Fin 2) K) i j, hg i j⟩
  let B : Matrix (Fin 2) (Fin 2) O := fun i j =>
    ⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j, hi i j⟩
  have hA : ιM A = (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hB : ιM B = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
  have hMinj : Function.Injective ιM := Matrix.map_injective Subtype.val_injective
  let k : GL (Fin 2) O := {
    val := A
    inv := B
    val_inv := by
      apply hMinj
      rw [map_mul, map_one, hA, hB]
      exact g.mul_inv
    inv_val := by
      apply hMinj
      rw [map_mul, map_one, hA, hB]
      exact g.inv_mul
  }
  refine ⟨k, ?_⟩
  apply Units.ext
  change ιM A = (g : Matrix (Fin 2) (Fin 2) K)
  exact hA

end ArtinPrimitiveRoots.Proofs.th_cover_sol
