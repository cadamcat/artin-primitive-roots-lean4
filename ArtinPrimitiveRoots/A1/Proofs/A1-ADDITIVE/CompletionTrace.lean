import ValuedFieldTheory.Valuation.Completion.DegreeNormTrace

set_option autoImplicit false

open AlgebraicNumberTheory.Valuations

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

noncomputable def traceAtCompletion (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) : w.1.Completion → vK.Completion := by
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact fun x => Algebra.trace vK.Completion w.1.Completion x

theorem completion_trace_compatible (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) [Fintype (AbsoluteValueExtension vK L)] (x : L) :
    algebraMap K vK.Completion (Algebra.trace K L x) =
      ∑ w : AbsoluteValueExtension vK L,
        traceAtCompletion vK w (algebraMap L w.1.Completion x) := by
  classical
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w => completionModuleFinite vK hvK w
  have htrace := ValuationTheory.Completion.baseChange_pi_trace_eq_sum
    (fun w : AbsoluteValueExtension vK L => w.1.Completion)
    (completionTensorDecomposition_left (K := K) (L := L) vK hvK) x
  rw [htrace]
  apply Finset.sum_congr rfl
  intro w _
  rw [completionTensorDecomposition_left_tmul_apply, map_one, one_mul]
  change Algebra.trace vK.Completion w.1.Completion (AbsoluteValue.toCompletion w.1 x) =
    Algebra.trace vK.Completion w.1.Completion (algebraMap L w.1.Completion x)
  rw [AbsoluteValue.toCompletion_eq_algebraMap]

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
