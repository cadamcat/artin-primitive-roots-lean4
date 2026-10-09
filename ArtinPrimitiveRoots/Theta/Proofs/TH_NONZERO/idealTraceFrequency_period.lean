import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_fourier_character
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- The trace-dual frequency character is trivial on the embedded ideal. -/
theorem idealTraceFrequency_period [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (n : Module.Free.ChooseBasisIndex ℤ I → ℤ) {z : F} (hz : z ∈ (I : Set F)) :
    psiInf (idealTraceFrequency F I n) (infEmbA z) = 1 := by
  have hspan : infEmbA z ∈ Submodule.span ℤ (Set.range (idealArchBasis F I)) :=
    (mem_span_idealArchBasis F I).mpr ⟨z, hz, rfl⟩
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan
  have hcoord : (idealArchBasis F I).equivFun.symm (fun i => (m i : ℝ)) = infEmbA z := by
    rw [Basis.equivFun_symm_apply]
    simpa only [Int.cast_smul_eq_zsmul] using hm
  rw [← hcoord, idealTraceFrequency_fourier_character F I n]
  have hzero : (fun i => ((m i : ℝ) : UnitAddCircle)) =
      (0 : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I)) := by
    funext i
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m i, by simp [zsmul_eq_mul]⟩
  rw [hzero]
  simp [UnitAddTorus.mFourier, fourier_eval_zero]

end ArtinPrimitiveRoots.A1.Theta
