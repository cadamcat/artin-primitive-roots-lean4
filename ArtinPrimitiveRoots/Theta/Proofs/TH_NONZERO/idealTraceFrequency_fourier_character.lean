import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_coordinate_sum
import ArtinPrimitiveRoots.Theta.Eis
import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- The theta character of a trace-dual frequency, in real ideal-basis
coordinates, is the corresponding standard torus Fourier character. -/
theorem idealTraceFrequency_fourier_character [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (n : Module.Free.ChooseBasisIndex ℤ I → ℤ)
    (x : Module.Free.ChooseBasisIndex ℤ I → ℝ) :
    psiInf (idealTraceFrequency F I n) ((idealArchBasis F I).equivFun.symm x) =
      UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) := by
  let ν := idealTraceFrequency F I n
  let y := (idealArchBasis F I).equivFun.symm x
  have hcoord : (2 : ℂ) * ∑ w : InfinitePlace F,
      (((w.embedding ν * y w).re : ℝ) : ℂ) =
      -(∑ i, (n i : ℂ) * (x i : ℂ)) := by
    exact_mod_cast idealTraceFrequency_coordinate_sum F I n x
  change psiInf ν y = _
  simp only [psiInf, psiC, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F,
        -(4 * Real.pi * Complex.I * (((w.embedding ν * y w).re : ℝ) : ℂ)) =
      -(2 * Real.pi * Complex.I *
        (2 * ∑ w : InfinitePlace F, (((w.embedding ν * y w).re : ℝ) : ℂ))) := by
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          ring
    _ = ∑ i, 2 * Real.pi * Complex.I * (n i : ℂ) * (x i : ℂ) := by
      rw [hcoord]
      simp [Finset.mul_sum, mul_assoc]

end ArtinPrimitiveRoots.A1.Theta
