import /- Reciprocity is prebuilt on the Mac. -/ ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».LocalUnits
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».FractionalIdeals

set_option autoImplicit false
open scoped NumberField
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

lemma transport_reciprocity_data {K L M N : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    [IsAbelianGalois M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L))
    (D : ClassFieldTheory.FiniteAbelianReciprocityData M N) :
    Nonempty (ClassFieldTheory.FiniteAbelianReciprocityData K L) := by
  sorry

lemma reciprocity_data {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    Nonempty (ClassFieldTheory.FiniteAbelianReciprocityData K L) := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
