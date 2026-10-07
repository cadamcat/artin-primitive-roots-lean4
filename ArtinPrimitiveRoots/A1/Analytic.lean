import ArtinPrimitiveRoots.A1.Coefficients

/-!
# A1 interface, §7: analytic notation for T5–T6

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 7. Analytic notation for T5–T6 -/

/-- `K_ν(x) = ∫_0^∞ exp(-x cosh t) cosh(ν t) dt` (`x > 0`); Mathlib has no Bessel `K`. -/
def besselK (ν x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)

/-- Angular character `ω_m(y) = (y/|y|)^m` on `ℂ^×`. -/
def omegaAng (m : ℤ) (y : ℂ) : ℂ := (y / (‖y‖ : ℂ)) ^ m

/-- Norm derivative at a complex place: `𝒟^j f(y) = (d/dt)^j f(e^{t/2} y)|_{t=0}` (03:255–261). -/
def normDeriv (j : ℕ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => f ((Real.exp (t / 2) : ℂ) * y)) 0

/-- Hypothesis (a) of lem:sheet-profile at a finite place (03:515–517).
Corrected per rev-theta to require local constancy near every nonzero point. -/
def SheetHypFin (v : FinPlace F) (δ : ℝ) (f : v.adicCompletion F → ℂ) : Prop :=
  (∀ x : v.adicCompletion F, x ≠ 0 →
    ∃ U : Set (v.adicCompletion F), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x) ∧
  (∃ C : ℝ, ∀ y : v.adicCompletion F, C < absFin v y → f y = 0) ∧
  (∃ C : ℝ, ∀ y : v.adicCompletion F, y ≠ 0 → absFin v y ≤ 1 → ‖f y‖ ≤ C * absFin v y ^ δ)

/-- Hypothesis (b) of lem:sheet-profile at a complex place (03:518–523); `‖y‖_v = |y|²`.
Corrected per rev-a2 to express C-infinity smoothness using the coercion of `⊤ : ℕ∞`; C9 of
`sol-gate-theta` keeps this form because it is equivalent to `SmoothSheetHypC`. -/
def SheetHypC (δ : ℝ) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {y | y ≠ 0} ∧
  ∀ (j : ℕ) (A : ℝ), 0 < A → ∃ C : ℝ, ∀ y : ℂ, y ≠ 0 →
    ‖normDeriv j f y‖ ≤ C * min (Complex.normSq y ^ δ) (Complex.normSq y ^ (-A))


end ArtinPrimitiveRoots.A1
