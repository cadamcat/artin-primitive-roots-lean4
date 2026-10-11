import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs
import ArtinPrimitiveRoots.Proofs.s7_euler_b.SharpZeta

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The canonical sharp zeta agrees with the Dirichlet series on `Re s > 1`.
Uses `dedekind_completed` and nonzero
gamma factors; feeds continuation and quotient construction. -/
theorem dedekindZetaSharp_eq (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaSharp T s = NumberField.dedekindZeta T s := by
  exact dedekindZetaSharp_eq_core T hs

end ArtinPrimitiveRoots.Splitting
end
