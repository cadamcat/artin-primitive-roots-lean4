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

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
