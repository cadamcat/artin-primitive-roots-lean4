import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelMellin

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

noncomputable def pd7dPlaneEquivProd : PDPlane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow (α := ℝ))

lemma pd7dPlaneEquivProd_symm (q : ℝ × ℝ) :
    pd7dPlaneEquivProd.symm q = pd7dPlanePoint q.1 q.2 := by
  ext i
  fin_cases i <;> rfl

lemma pd7dPlaneEquivProd_measurePreserving : MeasurePreserving pd7dPlaneEquivProd :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

lemma pd7dPlaneEquivProd_symm_measurePreserving : MeasurePreserving pd7dPlaneEquivProd.symm :=
  pd7dPlaneEquivProd_measurePreserving.symm

lemma pd7d_plane_integral_eq_product (f : PDPlane → ℂ) :
    (∫ v : PDPlane, f v) = ∫ q : ℝ × ℝ, f (pd7dPlanePoint q.1 q.2) := by
  have hh := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) pd7dPlaneEquivProd.symm f
  rw [pd7dPlaneEquivProd_symm_measurePreserving.map_eq] at hh
  simpa only [pd7dPlaneEquivProd_symm] using hh

lemma pd7d_plane_integrable_product (f : PDPlane → ℂ) (hf : Integrable f) :
    Integrable (fun q : ℝ × ℝ => f (pd7dPlanePoint q.1 q.2)) := by
  have hh := pd7dPlaneEquivProd_symm_measurePreserving.integrable_comp_of_integrable hf
  have hfun : f ∘ (pd7dPlaneEquivProd.symm : ℝ × ℝ → PDPlane) =
      (fun q : ℝ × ℝ => f (pd7dPlanePoint q.1 q.2)) := by
    funext q
    rw [Function.comp_apply, pd7dPlaneEquivProd_symm]
  rw [hfun] at hh
  exact hh

lemma pd7d_plane_integral_eq_iterated (f : PDPlane → ℂ) (hf : Integrable f) :
    (∫ v : PDPlane, f v) = ∫ a : ℝ, ∫ b : ℝ, f (pd7dPlanePoint a b) := by
  rw [pd7d_plane_integral_eq_product]
  exact integral_prod (fun q : ℝ × ℝ => f (pd7dPlanePoint q.1 q.2)) (pd7d_plane_integrable_product f hf)

end ArtinPrimitiveRoots.TypeII.PD

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_plane_real_integral_eq_product (f : PDPlane → ℝ) :
    (∫ v : PDPlane, f v) = ∫ q : ℝ × ℝ, f (pd7dPlanePoint q.1 q.2) := by
  have hh := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) pd7dPlaneEquivProd.symm f
  rw [pd7dPlaneEquivProd_symm_measurePreserving.map_eq] at hh
  simpa only [pd7dPlaneEquivProd_symm] using hh

lemma pd7d_plane_real_integrable_product (f : PDPlane → ℝ) (hf : Integrable f) :
    Integrable (fun q : ℝ × ℝ => f (pd7dPlanePoint q.1 q.2)) := by
  have hh := pd7dPlaneEquivProd_symm_measurePreserving.integrable_comp_of_integrable hf
  have hfun : f ∘ (pd7dPlaneEquivProd.symm : ℝ × ℝ → PDPlane) =
      (fun q : ℝ × ℝ => f (pd7dPlanePoint q.1 q.2)) := by
    funext q
    rw [Function.comp_apply, pd7dPlaneEquivProd_symm]
  rw [hfun] at hh
  exact hh
end ArtinPrimitiveRoots.TypeII.PD
