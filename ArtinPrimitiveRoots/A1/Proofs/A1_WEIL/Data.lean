import ArtinPrimitiveRoots.A1.AddChar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Stabilized quadratic Gaussian integrals for the A1 Weil-index route. -/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance completionMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The truncation ball of radius `|π|⁻ᴺ`, written with the multiplicative valuation. -/
def localBall (v : FinPlace F) (N : ℕ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp (N : ℤ)}

/-- Each Gaussian is integrated on a finite-radius ball. -/
def quadraticIntegral (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (a : (v.adicCompletion F)ˣ) (N : ℕ) : ℂ :=
  ∫ x in localBall v N, A.ψ v ((a : v.adicCompletion F) * x ^ 2) ∂μ

/-- A Haar measure and actual stabilization cutoffs; no local index identities are assumed. -/
structure LocalGaussianData (A : AddCharData F) where
  measure : (v : FinPlace F) → Measure (v.adicCompletion F)
  isHaar : ∀ v, Measure.IsAddHaarMeasure (measure v)
  cutoff : (v : FinPlace F) → (v.adicCompletion F)ˣ → ℕ
  stable : ∀ v a N, cutoff v a ≤ N →
    quadraticIntegral A v (measure v) a N =
      quadraticIntegral A v (measure v) a (cutoff v a)
  integral_ne_zero : ∀ v a,
    quadraticIntegral A v (measure v) a (cutoff v a) ≠ 0
  normalized_ne_zero : ∀ (v : FinPlace F) (a : (v.adicCompletion F)ˣ),
    ((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      quadraticIntegral A v (measure v) a (cutoff v a) /
        quadraticIntegral A v (measure v) 1 (cutoff v 1) ≠ 0

/-- The normalized ratio is independent of a rescaling of the chosen Haar measure. -/
def LocalGaussianData.index {A : AddCharData F} (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : ℂˣ :=
  Units.mk0
    (((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      quadraticIntegral A v (W.measure v) a (W.cutoff v a) /
        quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1))
    (W.normalized_ne_zero v a)

/-- Read a sextic root of unity through the frozen complex embedding. -/
def complexRoot (D : FieldData F) : rootsOfUnity 6 F →* ℂˣ :=
  (Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 F).subtype

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
