import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs

/-!
# A1-FOURIER part `a1_fourier_e_basic` (IMPL)

Basic properties of the global character `S.e A` on `F_S`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Basic properties of `e = ∏_{v∈S} ψ_v` on `F_S`: continuity (each `A.ψ v` is trivial on the
open subgroup `O_v` by `AddCharData.integral`, hence locally constant; `psiC` is continuous),
unit norm, additivity, and nontriviality (e.g. `z = (0, Pi.single w₀ (1/8))` gives
`psiC (1/8) = exp(-πi/2) = -i`; `InfinitePlace F` is nonempty).

Guide: lane `a1-poisson-opus` STATEMENTS.md (abstract route); compare the private
`globalAddChar_continuous` in `A2/Proofs/A2_WEIGHTS/Exist.lean:314` (copy, do not import).
Used by: `a1_fourier_orthogonality`, `a1_fourier_uniqueness`, `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_e_basic (S : SData F CE condη) (A : AddCharData F) :
    Continuous (S.e A) ∧ (∀ x : S.FS, ‖S.e A x‖ = 1) ∧
      (∀ x y : S.FS, S.e A (x + y) = S.e A x * S.e A y) ∧ ∃ z : S.FS, S.e A z ≠ 1 := by
  sorry

end ArtinPrimitiveRoots.A1
