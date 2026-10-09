import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.DegreeComparison

set_option autoImplicit false
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open scoped BigOperators
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Native completion degrees above a rational place sum to the number-field degree. -/
theorem native_degree_sum (w : FinPlace ℚ)
    [Fintype {v : FinPlace F // finitePlaceBelow (K := ℚ) v = w}] :
    (∑ v : {v : FinPlace F // finitePlaceBelow (K := ℚ) v = w},
      nativeCompletionDegree v.1) = Module.finrank ℚ F := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv ℚ w
  have hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w
  letI := completionTensorDecomposition_extensionFintype (K := ℚ) (L := F) vK hvK
  letI : ∀ a : AbsoluteValueExtension vK F, Algebra vK.Completion a.1.Completion :=
    fun a ↦ AbsoluteValue.completionAlgebra vK a.1 a.2
  let e := finitePlaceExtensionEquivAbove (K := ℚ) (L := F) w
  have hsum := e.sum_comp (fun v => nativeCompletionDegree v.1)
  have hlocal (a : AbsoluteValueExtension vK F) :
      nativeCompletionDegree (e a).1 = Module.finrank vK.Completion a.1.Completion :=
    (nativeCompletionInvariants_eq_absoluteInvariants w a).2
  have hdegree : Module.finrank ℚ F =
      ∑ a : AbsoluteValueExtension vK F, Module.finrank vK.Completion a.1.Completion :=
    completionDegreeNormTrace_degree (K := ℚ) (L := F) vK hvK
  calc
    (∑ v : {v : FinPlace F // finitePlaceBelow (K := ℚ) v = w},
        nativeCompletionDegree v.1) =
        ∑ a : AbsoluteValueExtension vK F, nativeCompletionDegree (e a).1 := hsum.symm
    _ = ∑ a : AbsoluteValueExtension vK F, Module.finrank vK.Completion a.1.Completion := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hlocal a
    _ = Module.finrank ℚ F := hdegree.symm

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
