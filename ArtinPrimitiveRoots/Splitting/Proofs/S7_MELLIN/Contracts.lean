import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.ZeroSum
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Boundary
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroEndpoint
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HadamardTail
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroWindows
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Heights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».XiHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GammaHorizontal
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrefactorDeriv
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpLogDeriv
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».FinitePatch
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpPrincipalParts

set_option autoImplicit false

universe u

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting
open Classical

-- The smooth-test hypothesis is expanded here to keep this helper file below Analytic.lean.
theorem mellin_entire (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) :
    Differentiable ℂ (mellinTransform f) := by
  sorry

theorem mellin_decay (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) :
    ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)) := by
  sorry

theorem euler_log_norm_summable (K : Type u) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) × ℕ =>
      Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
        Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * σ)) := by
  sorry

theorem mellin_prime_identity (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 0 < x) :
    (primeIdealTheta K f x : ℂ) = verticalLineIntegral
      (fun s : ℂ => dedekindZetaLogDerivative K s *
        Complex.cpow (x : ℂ) s * mellinTransform f s) 2 := by
  sorry

theorem euler_right_line_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + t * Complex.I)‖ ≤
        B * Module.finrank ℚ K := by
  sorry

theorem reflected_line_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-t) * Complex.I)‖ +
          Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |t|) := by
  sorry

theorem zero_family_summable (f : ℝ → ℝ)
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 2 ≤ x) :
    Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
      else 0) := by
  exact zero_family_summable_of_decay f hdecay K x hx

theorem contour_shift (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (hleft : ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 2 ≤ x) :
    verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
      Complex.cpow (x : ℂ) s * mellinTransform f s) 2 =
      (x : ℂ) * mellinTransform f 1 -
        (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
          (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
          else 0) -
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
          mellinTransform f 0 +
        verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
          Complex.cpow (x : ℂ) s * mellinTransform f s) (-1 / 2) := by
  sorry

theorem left_integral_bound (f : ℝ → ℝ)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (hleft : ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (x : ℝ), 2 ≤ x →
      ‖verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
        Complex.cpow (x : ℂ) s * mellinTransform f s) (-1 / 2)‖ ≤
      C * Real.rpow x (-1 / 2 : ℝ) *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
