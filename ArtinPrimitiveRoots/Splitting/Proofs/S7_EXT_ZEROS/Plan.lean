import ArtinPrimitiveRoots.Splitting.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Jensen
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Growth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaRatio
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Strip
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneRatio
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiBoundary

set_option autoImplicit false
open scoped NumberField BigOperators
open Classical ArtinPrimitiveRoots.Splitting

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Removing the nonvanishing prefactor preserves orders in the critical strip. -/
theorem sharp_xi_order (K : Type*) [Field K] [NumberField K] {z : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderNatAt (dedekindZetaSharp K) z = analyticOrderNatAt (dedekindXi K) z := by
  sorry

/-- Uniform translated Jensen estimate for the entire completed function. -/
theorem xi_window_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (T : ℝ),
      Summable (fun z : ℂ => if z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 then
        (analyticOrderNatAt (dedekindXi K) z : ℝ) else 0) ∧
      (∑' z : ℂ, if z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 then
        (analyticOrderNatAt (dedekindXi K) z : ℝ) else 0) ≤ C *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K * Real.log (2 + |T|)) := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
