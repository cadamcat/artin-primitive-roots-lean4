import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.Core
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# A1-FOURIER: shared definitions

Shared objects for the abstract Poisson-summation route on `F_S / R`.

* `SData.IsFSTensorSum S g`: `g` is a finite sum of tensors
  `x ↦ (∏_{v ∈ S_f} φ_v (x_v)) * Φ (x_∞)` with locally constant, compactly supported
  `φ_v` and an archimedean Schwartz function `Φ` on `InfinitePlace F → ℂ`.
  Every Bruhat–Schwartz function is of this form, and the class is stable under the
  self-dual Fourier transform.
* `a1LocalFourier v A μ φ`: the local Fourier transform `x ↦ ∫ y, ψ_v(-(x y)) φ(y) dμ`
  at a finite place.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- `g : F_S → ℂ` is a finite sum of pure tensors whose finite components are locally constant
compactly supported functions and whose archimedean component is a Schwartz function on
`InfinitePlace F → ℂ`. -/
def SData.IsFSTensorSum (S : SData F CE condη) (g : S.FS → ℂ) : Prop :=
  ∃ (n : ℕ) (φ : Fin n → ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (Φ : Fin n → SchwartzMap (InfinitePlace F → ℂ) ℂ),
    (∀ i v, Continuous (φ i v) ∧ HasCompactSupport (φ i v) ∧ IsLocallyConstant (φ i v)) ∧
    ∀ x : S.FS, g x = ∑ i, (∏ v : S.Sf, φ i v (x.1 v)) * Φ i x.2

/-- The local Fourier transform at a finite place for the character `A.ψ v` and a measure `μ`,
in the normalization of `SLattice.lean`'s private `covol_local_fourier`. -/
def a1LocalFourier (v : FinPlace F) (A : AddCharData F) (μ : Measure (v.adicCompletion F))
    (φ : v.adicCompletion F → ℂ) (x : v.adicCompletion F) : ℂ :=
  ∫ y, A.ψ v (-(x * y)) * φ y ∂μ

end ArtinPrimitiveRoots.A1
