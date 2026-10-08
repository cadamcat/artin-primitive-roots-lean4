import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol

theorem gaussSum_norm {k : Type} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card k : ℝ) := by
    have hh := congrArg Complex.re h
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using hh
  rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
