import ArtinPrimitiveRoots.Hecke.Dedekind
import Mathlib.FieldTheory.SplittingField.Construction
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# §7 fields and analytic notation

Notation from `B-reduction-sieve.md`, N7–N10, and `07-splitting.tex:19-24, 112-130`.
-/

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

/-- `E_q = ℚ(μ_q)`. -/
noncomputable abbrev cyclotomicField (q : ℕ) [NeZero q] := CyclotomicField q ℚ

/-- `F_q = ℚ(μ_{12q})`. -/
noncomputable abbrev heckeBaseField (q : ℕ) [NeZero (12 * q)] := CyclotomicField (12 * q) ℚ

/-- The Kummer polynomial over `ℚ(μ_q)`. -/
def kummerPolynomial (a : ℤ) (q : ℕ) [NeZero q] : Polynomial (CyclotomicField q ℚ) :=
  Polynomial.X ^ q - Polynomial.C (a : CyclotomicField q ℚ)

/-- `K_q = ℚ(μ_q, a^(1/q))`, represented as the splitting field over `ℚ(μ_q)`. -/
noncomputable abbrev kummerField (a : ℤ) (q : ℕ) [NeZero q] :=
  (kummerPolynomial a q).SplittingField

instance kummerField.numberField (a : ℤ) (q : ℕ) [NeZero q] :
    NumberField (kummerField a q) :=
  NumberField.of_module_finite (cyclotomicField q) (kummerField a q)

/-- The splitting field of `T^q-a` over `F_q`, representing `K̃_q = K_q F_q`. -/
noncomputable abbrev compositumField (a : ℤ) (q : ℕ) [NeZero (12 * q)] :=
  (Polynomial.X ^ q - Polynomial.C (a : heckeBaseField q)).SplittingField

instance compositumField.numberField (a : ℤ) (q : ℕ) [NeZero (12 * q)] :
    NumberField (compositumField a q) :=
  NumberField.of_module_finite (heckeBaseField q) (compositumField a q)

/-- The four fields and Kummer polynomial from N7: `E_q`, `K_q`, `F_q`, and `K̃_q`.
`K_q` and `K̃_q` are represented as splitting fields over `E_q` and `F_q`, respectively; these
are the same composita as the splitting-field-over-`ℚ` definitions in the blueprint. -/
structure KummerFields (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)] where
  polynomial : Polynomial (cyclotomicField q)
  E : Type
  K : Type
  F : Type
  Ktilde : Type

/-- **Definition `def:kummer-fields`**, N7, `01a-reduction.tex:41-48` and
`07-splitting.tex:19-24`. The body records the Kummer and cyclotomic fields used throughout §7. -/
noncomputable def kummerFields (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)] :
    KummerFields a q :=
  ⟨kummerPolynomial a q, cyclotomicField q, kummerField a q, heckeBaseField q,
    compositumField a q⟩

/-- An abelian extension together with the algebra structure needed by the class-field interface.
The §7 compositum node supplies these records for both `K_q ⊂ K̃_q` and `F_q ⊂ K̃_q`. -/
class AbelianExtensionData (K L : Type*) [Field K] [Field L] where
  algebra : Algebra K L
  abelian : @IsAbelianGalois K L ‹Field K› ‹Field L› algebra

instance {K L : Type*} [Field K] [Field L] [D : AbelianExtensionData K L] : Algebra K L :=
  D.algebra

instance {K L : Type*} [Field K] [Field L] [D : AbelianExtensionData K L] :
    IsAbelianGalois K L := D.abelian

/-- The absolute degree `n_q = [K_q:ℚ]`. -/
noncomputable def kummerDegree (a : ℤ) (q : ℕ) [NeZero q] : ℕ :=
  Module.finrank ℚ (kummerField a q)

/-- The absolute discriminant `D_q = |d_{K_q}|`. -/
noncomputable def absoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

/-- **Definition `def:split-completely`**, `01a-reduction.tex:56,69-75`. A rational prime splits
completely when the number of prime ideals above it is the absolute degree. -/
def splitsCompletely (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

/-- The Mellin transform `Φ(s) = ∫₀^∞ f(t)t^(s-1)dt`, using Mathlib's integral on `Ioi 0`. -/
def mellinTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (f t : ℂ)) s

/-- A vertical line integral, parametrized by `s = σ + it`; the `ds = i dt` factor is cancelled. -/
def verticalLineIntegral (F : ℂ → ℂ) (σ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, F (σ + t * Complex.I)

/-- The chosen entire `ξ_K(s)=s(s-1)Λ_K(s)` supplied by Hecke D1. -/
noncomputable def dedekindXi (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.choose (ArtinPrimitiveRoots.Hecke.dedekind_completed K)

/-- `ζ_K^♮`, defined from Hecke D1's `ξ_K` by removing `s(s-1)` and the gamma/discriminant
prefactor (blueprint N10). -/
noncomputable def dedekindZetaSharp (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  fun s => dedekindXi K s /
    (s * (s - 1) * ArtinPrimitiveRoots.Hecke.dedekindPrefactor K s)

/-- The nontrivial zeros of the meromorphic continuation `ζ_K^♮`. -/
def nontrivialZeros (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ dedekindZetaSharp K ρ = 0}

/-- The analytic multiplicity of a nontrivial zero of `ζ_K^♮`. -/
noncomputable def zeroMultiplicity (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (dedekindZetaSharp K) ρ

/-- The smoothed prime-ideal sum `Θ_{K,f}(x)` from `07-splitting.tex:116-129`. -/
noncomputable def primeIdealTheta (K : Type*) [Field K] [NumberField K]
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 K), ∑' j : ℕ,
    if 0 < j then
      Real.log (Ideal.absNorm v.asIdeal : ℝ) *
        f (((Ideal.absNorm v.asIdeal) ^ j : ℕ) / x)
    else 0

/-- The logarithmic derivative of the meromorphic Dedekind zeta continuation. -/
noncomputable def dedekindZetaLogDerivative (K : Type*) [Field K] [NumberField K]
    (s : ℂ) : ℂ :=
  -(deriv (dedekindZetaSharp K) s) / dedekindZetaSharp K s

end ArtinPrimitiveRoots.Splitting

end
