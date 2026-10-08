import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs
import ArtinPrimitiveRoots.Proofs.s7_euler_b.SharpZeta

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- Sharp zeta is analytic on the positive half-plane away from the pole at one.
Guide: ../sol-thin-s7/PROOFS.md:507–515. Uses `dedekind_completed` and positive
real-part gamma regularity; feeds pointwise quotient factorization. -/
theorem dedekindZetaSharp_analyticAt (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaSharp T) s := by
  exact dedekindZetaSharp_analyticAt_core T hs hs1

end ArtinPrimitiveRoots.Splitting
end
