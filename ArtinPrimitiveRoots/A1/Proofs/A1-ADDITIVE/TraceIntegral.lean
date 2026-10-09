import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».CompletionTrace
import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue

set_option autoImplicit false

open AlgebraicNumberTheory.Valuations

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem traceAtCompletion_integral (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) (hvK0 : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) (x : w.1.Completion) (hx : ‖x‖ ≤ 1) :
    ‖traceAtCompletion vK w x‖ ≤ 1 := by
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK0 w
  have hxint : IsIntegral (absoluteValueCompletionIntegers vK hvK) x :=
    isIntegral_over_baseCompletionIntegers_of_mem vK hvK hvK0 w hx
  have htrace : IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (Algebra.trace vK.Completion w.1.Completion x) :=
    Algebra.isIntegral_trace hxint
  obtain ⟨a, ha⟩ := (IsIntegrallyClosedIn.isIntegral_iff).mp htrace
  change ‖Algebra.trace vK.Completion w.1.Completion x‖ ≤ 1
  rw [← ha]
  exact a.property

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
