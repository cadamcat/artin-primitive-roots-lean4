import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs
import ArtinPrimitiveRoots.Proofs.s7_euler_b.SharpZeta

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The canonical sharp zeta is meromorphic, including its arbitrary pole values.
Guide: ../sol-thin-s7/PROOFS.md:444–454. Uses `dedekind_completed` and the
meromorphic gamma prefactor; feeds continuation and zero-free descent. -/
theorem dedekindZetaSharp_meromorphic (T : Type*) [Field T] [NumberField T] :
    Meromorphic (dedekindZetaSharp T) := by
  exact dedekindZetaSharp_meromorphic_core T

end ArtinPrimitiveRoots.Splitting
end
