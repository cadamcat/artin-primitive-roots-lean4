import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».Defs
import ArtinPrimitiveRoots.Hecke.Dedekind

/-!
# A2-QS-POISSON: definitions (weights, transform, residue functionals)

Guide: `runs/lanes/sol-thin-found/PROOFS.md:329-378` (P0-P2).

* `IsQSWeight h`: smooth on `ℝ`, zero beyond some point, constant on `[0, δ]` (found:331).
* `IsCapWeight W` (`W = Wcap`) and `IsDyadWeight W` (`Wdyad`), found:331-332.
* `qsGammaRatio K u = G_K(u)/G_K(1-u)` with `G_K = Hecke.dedekindPrefactor K`
  (`|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`, the completed-zeta prefactor, so the discriminant is
  inside the transform).
* `qsTransform K h`: the transform `T` of found:333, `Mellin(T h)(u) = G_K(u)/G_K(1-u)·Mellin(h)(1-u)`,
  defined by Mellin inversion on the line `Re u = 1/2` (the integrand is holomorphic on `Re u > 0`
  for the weights used; moving the line is a proof obligation of the parts, not of this def).
* `qsZetaCont K s`: the continuation of `ζ_K` off `{0,1}` from AINTLIB's entire completed zeta.
* `qsResidueOne K = ρ_K` (Mathlib's `dedekindZeta_residue`), `qsResidueZero K f = R_K(f)`
  (found:367-369): `Res_{s=0}(Mellin(f)(s)·ζ_K(s))`, taken as the limit of `s·Mellin f(s)·ζ_K(s)`
  along real `s → 0⁺` (valid because the pole is at most simple for the weights of P2; along
  `s > 0` the Mellin integral converges, so no junk value enters).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- QS test weight (found:331): smooth on `ℝ`, vanishing for `x ≥ B`, constant on `[0, δ]`. -/
def IsQSWeight (h : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ (∃ B : ℝ, ∀ x : ℝ, B ≤ x → h x = 0) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc (0 : ℝ) δ, h x = h 0

/-- `Wcap` (found:331): smooth, nonnegative, constant near zero, zero on `[5/2, ∞)`,
`≥ 1` on `[0, 1]`. -/
def IsCapWeight (W : ℝ → ℝ) : Prop :=
  IsQSWeight (fun x => (W x : ℂ)) ∧ (∀ x : ℝ, 0 ≤ W x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ W x) ∧ (∀ x : ℝ, 5 / 2 ≤ x → W x = 0)

/-- `Wdyad` (found:331-332): smooth, nonnegative, zero outside `(1/2, 5/2)`, `≥ 1` on `[1, 2]`. -/
def IsDyadWeight (W : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ (∀ x : ℝ, 0 ≤ W x) ∧
    (∀ x ∈ Set.Icc (1 : ℝ) 2, 1 ≤ W x) ∧ (∀ x : ℝ, x ∉ Set.Ioo (1 / 2 : ℝ) (5 / 2) → W x = 0)

/-- `G_K(u)/G_K(1-u)`, `G_K = Hecke.dedekindPrefactor K` (discriminant included). -/
def qsGammaRatio (K : Type) [Field K] [NumberField K] (u : ℂ) : ℂ :=
  Hecke.dedekindPrefactor K u / Hecke.dedekindPrefactor K (1 - u)

/-- The transform `T h` (found:333): inverse Mellin transform on `Re u = 1/2` of
`G_K(u)/G_K(1-u) · Mellin(h)(1-u)`. -/
def qsTransform (K : Type) [Field K] [NumberField K] (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  mellinInv (1 / 2) (fun u : ℂ => qsGammaRatio K u * mellin h (1 - u)) y

/-- `ζ_K(s)` for `s ∉ {0, 1}` (and off the prefactor poles), from AINTLIB's entire
`ξ_K(s) = s(s-1)·G_K(s)·ζ_K(s)`. -/
def qsZetaCont (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  DedekindResidue.completedDedekindZetaEntire K s / (s * (s - 1) * Hecke.dedekindPrefactor K s)

/-- `ρ_K = Res_{s=1} ζ_K(s)` (Mathlib, `NumberField.dedekindZeta_residue`). -/
def qsResidueOne (K : Type) [Field K] [NumberField K] : ℝ :=
  NumberField.dedekindZeta_residue K

/-- `R_K(f) = Res_{s=0}(Mellin(f)(s)·ζ_K(s))` (found:367-369), as the limit of
`s·Mellin(f)(s)·ζ_K(s)` along real `s → 0⁺`. -/
def qsResidueZero (K : Type) [Field K] [NumberField K] (f : ℝ → ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun t : ℝ => (t : ℂ) * mellin f (t : ℂ) * qsZetaCont K (t : ℂ))

/-- The square-variable weights of P2 (found:363-366): `f(y) = h(y²)` or `f(y) = (T h)(y²)`
with `h` a QS weight. -/
def IsQSSquareWeight (K : Type) [Field K] [NumberField K] (f : ℝ → ℂ) : Prop :=
  ∃ h : ℝ → ℂ, IsQSWeight h ∧
    (f = (fun y : ℝ => h (y ^ 2)) ∨ f = (fun y : ℝ => qsTransform K h (y ^ 2)))

end ArtinPrimitiveRoots.A2
