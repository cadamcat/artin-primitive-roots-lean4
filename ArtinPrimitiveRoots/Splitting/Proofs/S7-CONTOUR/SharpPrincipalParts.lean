import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroEndpoint
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary

set_option autoImplicit false

open scoped NumberField Topology
open Filter NumberField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- The weighted sharp-zeta logarithmic derivative has the expected endpoint and zero coefficients. -/
theorem sharp_weighted_principal_parts (K : Type*) [Field K] [NumberField K]
    (W : ℂ → ℂ) (hW : Differentiable ℂ W) :
    (∃ R : ℂ → ℂ, AnalyticAt ℂ R 1 ∧
      ∀ᶠ z in 𝓝[≠] (1 : ℂ),
        dedekindZetaLogDerivative K z * W z = W 1 / (z - 1) + R z) ∧
    (∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        dedekindZetaLogDerivative K z * W z =
          (-((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            W 0) / z + R z) ∧
    (∀ ρ : ℂ, ρ ∈ nontrivialZeros K →
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R ρ ∧
        ∀ᶠ z in 𝓝[≠] ρ,
          dedekindZetaLogDerivative K z * W z =
            (-(zeroMultiplicity K ρ : ℂ) * W ρ) / (z - ρ) + R z) := by
  have hmerom (z : ℂ) : MeromorphicAt (dedekindZetaSharp K) z :=
    (sharp_continuation K).2.2.1 z (Set.mem_univ z)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨R, hR, hlocal⟩ := weighted_logderiv_principal (dedekindZetaSharp K)
      W 1 (-1) (hmerom 1) (sharp_pole_one K) (hW.analyticAt 1)
    refine ⟨R, hR, ?_⟩
    filter_upwards [hlocal] with z hz
    simpa only [dedekindZetaLogDerivative, Int.cast_neg, Int.cast_one, neg_neg, one_mul]
      using hz
  · let n : ℕ := InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1
    obtain ⟨R, hR, hlocal⟩ := weighted_logderiv_principal (dedekindZetaSharp K)
      W 0 (n : ℤ) (hmerom 0) (sharp_order_zero K) (hW.analyticAt 0)
    refine ⟨R, hR, ?_⟩
    filter_upwards [hlocal] with z hz
    simpa only [dedekindZetaLogDerivative, Int.cast_natCast, sub_zero] using hz
  · intro ρ hρ
    have hρ₁ : ρ ≠ 1 := by
      intro heq
      have hlt := hρ.2.1
      simp only [heq, Complex.one_re, lt_self_iff_false] at hlt
    have hAn : AnalyticAt ℂ (dedekindZetaSharp K) ρ :=
      dedekindZetaSharp_analyticAt_core K hρ.1 hρ₁
    have hpos : 0 < zeroMultiplicity K ρ := (xi_zero_dictionary K).2.2 ρ hρ
    have hfinite : analyticOrderAt (dedekindZetaSharp K) ρ ≠ ⊤ := by
      intro htop
      have hzero : zeroMultiplicity K ρ = 0 := by
        simp only [zeroMultiplicity, analyticOrderNatAt, htop, ENat.toNat_top]
      exact (Nat.ne_of_gt hpos) hzero
    have horder : meromorphicOrderAt (dedekindZetaSharp K) ρ =
        ((zeroMultiplicity K ρ : ℤ) : WithTop ℤ) := by
      rw [hAn.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfinite]
      simp only [ENat.map_natCast, zeroMultiplicity]
    obtain ⟨R, hR, hlocal⟩ := weighted_logderiv_principal (dedekindZetaSharp K)
      W ρ (zeroMultiplicity K ρ : ℤ) (hmerom ρ) horder (hW.analyticAt ρ)
    refine ⟨R, hR, ?_⟩
    filter_upwards [hlocal] with z hz
    simpa only [dedekindZetaLogDerivative, Int.cast_natCast] using hz

open ArtinPrimitiveRoots.Hecke

/-- To the right of -1, only the two endpoints and xi zeros can obstruct sharp-zeta regularity. -/
theorem sharp_regular_of_re_gt_neg_one (K : Type*) [Field K] [NumberField K]
    (s : ℂ) (hs : -1 < s.re) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hxi : dedekindXi K s ≠ 0) :
    AnalyticAt ℂ (dedekindZetaSharp K) s ∧
      dedekindZetaSharp K s ≠ 0 ∧
      AnalyticAt ℂ (dedekindZetaLogDerivative K) s := by
  have hpole (z : ℂ) (hz : -1 < z.re) (hz₀ : z ≠ 0) (m : ℕ) :
      z ≠ -(m : ℂ) := by
    intro heq
    by_cases hm : m = 0
    · exact hz₀ (by simpa only [hm, Nat.cast_zero, neg_zero] using heq)
    · have hmreal : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
      have hzre : z.re = -(m : ℝ) := by
        simpa using congrArg Complex.re heq
      linarith
  have hhalf : -1 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith only [hs]
  have hhalf₀ : s / 2 ≠ 0 := div_ne_zero hs₀ two_ne_zero
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (hpole s hs hs₀)
  have hGhalf : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero (hpole (s / 2) hhalf hhalf₀)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi₂ : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hR : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)) hGhalf
  have hC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi₂))) hG
  have hD : (absoluteDiscriminant K : ℂ) ≠ 0 := by
    unfold absoluteDiscriminant
    exact_mod_cast abs_ne_zero.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hPref : dedekindPrefactor K s ≠ 0 := by
    change (absoluteDiscriminant K : ℂ) ^ (s / 2) *
      (Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) ≠ 0
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hD))
      (mul_ne_zero (pow_ne_zero _ hR) (pow_ne_zero _ hC))
  have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁)
  have hSharp : dedekindZetaSharp K s ≠ 0 := by
    unfold dedekindZetaSharp
    exact div_ne_zero hxi (mul_ne_zero hden hPref)
  obtain ⟨hinv, heq, _, _⟩ := sharp_continuation K
  have hxiDiff : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (dedekind_completed K)).1
  have hAn : AnalyticAt ℂ (dedekindZetaSharp K) s := by
    have hfun : dedekindZetaSharp K = fun z : ℂ =>
        dedekindXi K z * invPrefactor K z / (z * (z - 1)) := funext heq
    rw [hfun]
    exact ((hxiDiff.analyticAt s).mul (hinv.analyticAt s)).div
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) hden
  refine ⟨hAn, hSharp, ?_⟩
  change AnalyticAt ℂ (fun z : ℂ => -(deriv (dedekindZetaSharp K) z) /
    dedekindZetaSharp K z) s
  exact hAn.deriv.neg.div hAn hSharp

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
