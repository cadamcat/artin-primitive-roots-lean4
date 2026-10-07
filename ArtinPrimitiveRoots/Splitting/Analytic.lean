import ArtinPrimitiveRoots.Splitting.ZeroFree

/-!
# §7 smoothed prime-ideal estimate

Blueprint nodes `spl:mellin-integral`, `spl:left-line`, `spl:explicit-formula`, `spl:zero-sum`,
and `spl:smooth-estimate`; source `07-splitting.tex:112-225`.
-/

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs
open Classical
open Complex

/-- A smooth compactly supported test function on the positive half-line. -/
def IsSmoothPositiveTestFunction (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
    Function.support f ⊆ Set.Ioi 0

/-- **`spl:mellin-integral`**, `07-splitting.tex:130-145`. The Mellin transform is entire and
rapidly decreasing on every vertical strip; Mellin inversion and the Dedekind Euler logarithmic
derivative give the prime-ideal identity on `Re s = 2`. -/
theorem spl_mellin_integral (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f) :
    Differentiable ℂ (mellinTransform f) ∧
      (∀ (A : ℕ) (a b : ℝ), a ≤ b →
        ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
          ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ))) ∧
      (∀ (K : Type*) [Field K] [NumberField K] (x : ℝ), 0 < x →
        (primeIdealTheta K f x : ℂ) =
          verticalLineIntegral
            (fun s : ℂ => dedekindZetaLogDerivative K s *
              Complex.cpow (x : ℂ) s * mellinTransform f s) 2) := by
  sorry

/-- **`spl:left-line`**, `07-splitting.tex:147-170`. The functional equation and D3's Euler
bound at `1-s`, with the digamma strip estimate for the gamma factors, give an absolute constant
uniform in the number field. -/
theorem spl_left_line :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|)) := by
  sorry

/-- **`spl:explicit-formula`**, `07-splitting.tex:172-210`. The contour shift crosses the pole at
`1`, the nontrivial zeros with analytic multiplicity, and the trivial zero at `0`; the remaining
fixed-line integral is `O_f(x^(-1/2)(log D+n))`. -/
theorem spl_explicit_formula (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (x : ℝ), 2 ≤ x →
      ∃ R : ℂ,
      Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
      else 0) ∧
      (primeIdealTheta K f x : ℂ) =
        (x : ℂ) * mellinTransform f 1 -
          (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
            (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
          else 0) -
          ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0 + R ∧
      ‖R‖ ≤ C * Real.rpow x (-1 / 2 : ℝ) *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) := by
  sorry

/-- **`spl:zero-sum`**, `07-splitting.tex:212-224`. Zero counting in unit-height intervals and
rapid Mellin decay make the zero sum absolutely convergent and bound it by
`x^(1-δ)(log D+n)`. -/
theorem spl_zero_sum (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type*) [Field K] [NumberField K]
      (hzero : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 →
        meromorphicOrderAt (dedekindZetaSharp K) s ≤ 0)
      (x : ℝ) (hx : 2 ≤ x),
      Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℝ) *
          ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖ else 0) ∧
      (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℝ) *
          ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖ else 0) ≤
        C * Real.rpow x (1 - δ) *
          (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) ∧
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℝ) *
        ‖mellinTransform f 0‖ ≤ C * Module.finrank ℚ K := by
  sorry

/-- **`spl:smooth-estimate`**, `07-splitting.tex:112-225`. For each fixed smooth nonnegative
test function and `0 < δ < 1/2`, one constant works for every number field and every `x ≥ 2`:
`Θ_{K,f}(x) ≤ C (x + x^(1-δ)(log D+n))`. -/
theorem spl_smooth_estimate (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f)
    (hfnn : ∀ t : ℝ, 0 ≤ f t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K]
      (hzero : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 →
        meromorphicOrderAt (dedekindZetaSharp K) s ≤ 0)
      (x : ℝ) (hx : 2 ≤ x),
        primeIdealTheta K f x ≤
          C * (x + Real.rpow x (1 - δ) *
            (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K)) := by
  sorry

end ArtinPrimitiveRoots.Splitting

end
