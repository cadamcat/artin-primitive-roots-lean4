import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField
open NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Splitting

/-- The native splitting-field algebra over the cyclotomic base is abelian.
Guide: ../sol-thin-s7/PROOFS.md:366–397; arithmetic prerequisite for the
specialization of the general Euler core. Uses the Kummer splitting-field lemmas
and the fact that the base contains the qth roots of unity. Feeds
`sp_upstairs_factor`, whose frozen Artin target uses this native algebra.
The arbitrary algebra stored in `AbelianExtensionData` is not definitionally
equal to the native splitting-field algebra. -/
theorem compositum_native_abelian (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)]
    (hq : q.Prime) : IsAbelianGalois (heckeBaseField q) (compositumField a q) := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
