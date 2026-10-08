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
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectanglePatch
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PoleIntegrals
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectangleResidues
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WeightedRectangle
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HorizontalLimits
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GoodContours
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WindowSums
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WeightDecay
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».LineIntegrability
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».BoundaryGrowth
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

universe u

open scoped NumberField BigOperators Interval Topology
open NumberField IsDedekindDomain Filter MeasureTheory intervalIntegral

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
  let W : ℂ → ℂ := fun s => Complex.cpow (x : ℂ) s * mellinTransform f s
  let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s * W s
  let F : ℂ → ℂ := fun ρ => if ρ ∈ nontrivialZeros K then
    (zeroMultiplicity K ρ : ℂ) * W ρ else 0
  let N : ℂ := ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ)
  obtain ⟨hW, hdW⟩ := cpow_weight_entire_decay (mellinTransform f) hentire hdecay x hx
  change Differentiable ℂ W at hW
  obtain ⟨C, hC, hbound⟩ := hdW 6 (-1 / 2) 2 (by norm_num)
  have hWdecay : ∀ s : ℂ, (-1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖W s‖ ≤ C * Real.rpow (1 + |s.im|) (-6 : ℝ) := by
    simpa only [Nat.cast_ofNat] using hbound
  have hint (σ : ℝ) (hσ : σ = (-1 / 2 : ℝ) ∨ σ = 2) :
      Integrable (fun t : ℝ => H ((σ : ℂ) + t * Complex.I)) := by
    obtain ⟨hL, B, hB, hLB⟩ := sharp_boundary_line_growth K σ hσ
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcontW : Continuous (fun t : ℝ => W ((σ : ℂ) + t * Complex.I)) :=
      hW.continuous.comp hline
    change Integrable (fun t : ℝ =>
      dedekindZetaLogDerivative K ((σ : ℂ) + t * Complex.I) * W ((σ : ℂ) + t * Complex.I))
    apply integrable_product_of_growth_decay _ _ hL.aestronglyMeasurable
      hcontW.aestronglyMeasurable B C hB.le hC.le hLB
    intro t
    have hσstrip : σ ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
      rcases hσ with h | h <;> norm_num [h]
    simpa using hWdecay ((σ : ℂ) + t * Complex.I)
      (by simpa using hσstrip.1) (by simpa using hσstrip.2)
  obtain ⟨a, b, ha, hb, hsigns, havoid, hbottom, htop⟩ :=
    good_contour_sequences K W C hC.le hWdecay
  let Z : ℕ → Finset ℂ := fun n => (zero_strip_finite K (a n) (b n)).toFinset
  have hZ (n : ℕ) (ρ : ℂ) :
      ρ ∈ Z n ↔ ρ ∈ nontrivialZeros K ∧ a n ≤ ρ.im ∧ ρ.im ≤ b n := by
    simp only [Z, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hF : Summable F := by
    simpa only [F, W, mul_assoc] using zero_family_summable f hdecay K x hx
  have hcover (ρ : ℂ) (hne : F ρ ≠ 0) : ∀ᶠ n in atTop, ρ ∈ Z n := by
    have hρ : ρ ∈ nontrivialZeros K := by
      by_contra hnot
      exact hne (by simp only [F, if_neg hnot])
    filter_upwards [ha.eventually (eventually_le_atBot ρ.im),
      hb.eventually (eventually_ge_atTop ρ.im)] with n hnlow hnup
    exact (hZ n ρ).mpr ⟨hρ, hnlow, hnup⟩
  have hsumF := finset_sum_tendsto_of_eventually_mem F hF Z hcover
  have hsumEq (n : ℕ) : (∑ ρ ∈ Z n, F ρ) =
      ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [F, if_pos ((hZ n ρ).mp hρ).1]
  have hsum : Tendsto (fun n : ℕ => ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ)
      atTop (𝓝 (∑' ρ : ℂ, F ρ)) := by
    simpa only [hsumEq] using hsumF
  have hright := MeasureTheory.intervalIntegral_tendsto_integral
    (hint 2 (Or.inr rfl)) ha hb
  have hleftlim := MeasureTheory.intervalIntegral_tendsto_integral
    (hint (-1 / 2) (Or.inl rfl)) ha hb
  have hrect (n : ℕ) := sharp_weighted_rectangle_identity K W hW (a n) (b n)
    (hsigns n).1 (hsigns n).2 (fun ρ hρ => (havoid n ρ hρ).1)
    (fun ρ hρ => (havoid n ρ hρ).2) (Z n) (hZ n)
  have hboundary : Tendsto (fun n : ℕ =>
      (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (a n : ℂ) * Complex.I)) -
        (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (b n : ℂ) * Complex.I)) +
        Complex.I * (∫ t : ℝ in a n..b n, H ((2 : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ in a n..b n, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)))
      atTop (𝓝 (Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)))) := by
    simpa only [H, Complex.ofReal_ofNat, sub_self, zero_add] using
      ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
        (hleftlim.const_mul Complex.I)
  have hresidue : Tendsto (fun n : ℕ => 2 * (Real.pi : ℂ) * Complex.I *
      (W 1 - N * W 0 - ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ))
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I *
        (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hsum)
  have hlimit : Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := by
    exact tendsto_nhds_unique (hboundary.congr' (Filter.Eventually.of_forall hrect)) hresidue
  have hcancel : (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
      (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      2 * (Real.pi : ℂ) * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      _ = Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
          Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by ring
      _ = 2 * (Real.pi : ℂ) * Complex.I * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := hlimit
      _ = _ := by ring
  have hshift : verticalLineIntegral H 2 = W 1 - (∑' ρ : ℂ, F ρ) - N * W 0 +
      verticalLineIntegral H (-1 / 2) := by
    unfold verticalLineIntegral
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hcoef : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
    have he : (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) =
        (2 * (Real.pi : ℂ)) * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) +
          (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by
      linear_combination hcancel
    rw [he, mul_add, ← mul_assoc, inv_mul_cancel₀ hcoef, one_mul]
    ring
  have hW1 : W 1 = (x : ℂ) * mellinTransform f 1 := by
    dsimp [W]
    congr 1
    exact Complex.cpow_one (x : ℂ)
  have hW0 : W 0 = mellinTransform f 0 := by
    calc
      W 0 = (1 : ℂ) * mellinTransform f 0 :=
        congrArg (fun z : ℂ => z * mellinTransform f 0) (Complex.cpow_zero (x : ℂ))
      _ = _ := one_mul _
  rw [hW1, hW0] at hshift
  simpa only [H, W, F, N, mul_assoc] using hshift

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
