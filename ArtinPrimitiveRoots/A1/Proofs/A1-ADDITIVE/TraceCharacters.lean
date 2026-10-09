import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TraceIntegral
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalCharacter

set_option autoImplicit false

open AlgebraicNumberTheory.Valuations
open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem localTraceChar_family (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) (hvK0 : vK.IsNontrivial)
    [Fintype (AbsoluteValueExtension vK L)] (θ : AddChar vK.Completion ℂ)
    (hθ : ∀ x : vK.Completion, ‖x‖ ≤ 1 → θ x = 1) :
    ∃ ψ : (w : AbsoluteValueExtension vK L) → AddChar w.1.Completion ℂ,
      (∀ (w : AbsoluteValueExtension vK L) (x : w.1.Completion),
        ψ w x = θ (traceAtCompletion vK w x)) ∧
      (∀ (w : AbsoluteValueExtension vK L) (x : w.1.Completion),
        ‖x‖ ≤ 1 → ψ w x = 1) ∧
      (∀ z : L, (∏ w : AbsoluteValueExtension vK L,
          ψ w (algebraMap L w.1.Completion z)) =
        θ (algebraMap K vK.Completion (Algebra.trace K L z))) := by
  classical
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let ψ : (w : AbsoluteValueExtension vK L) → AddChar w.1.Completion ℂ :=
    fun w => θ.compAddMonoidHom
      (Algebra.trace vK.Completion w.1.Completion).toAddMonoidHom
  have hprod (s : Finset (AbsoluteValueExtension vK L))
      (g : AbsoluteValueExtension vK L → vK.Completion) :
      θ (∑ w ∈ s, g w) = ∏ w ∈ s, θ (g w) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih =>
      rw [Finset.sum_insert hw, Finset.prod_insert hw, θ.map_add_eq_mul, ih]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro w x
    rfl
  · intro w x hx
    change θ (traceAtCompletion vK w x) = 1
    exact hθ _ (traceAtCompletion_integral vK hvK hvK0 w x hx)
  · intro z
    change (∏ w : AbsoluteValueExtension vK L,
        θ (traceAtCompletion vK w (algebraMap L w.1.Completion z))) =
      θ (algebraMap K vK.Completion (Algebra.trace K L z))
    rw [completion_trace_compatible vK hvK0 z]
    exact (hprod Finset.univ _).symm

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
