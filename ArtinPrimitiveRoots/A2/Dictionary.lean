import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.A1.Characters

/-!
# Dictionary between ray-class and idelic Hecke characters
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

/-! `A1.HeckeChar` is idelic, while the analytic package uses ray-class characters.  This is the
only direction needed to feed a fixed ray-class character into A1's coefficient family. -/

/-- **dict:ray-class-to-idelic** (06:4-10, with the ray-class package of `Hecke/Defs.lean`).
Every ray-class character has a finite-order idelic representative with the same ideal values on
ideals prime to its modulus. -/
theorem rayClass_idelic_dictionary {K : Type} [Field K] [NumberField K]
    (m : RayClassModulus K) (η : RayClassGroup m →* ℂˣ) :
    ∃ χ : ArtinPrimitiveRoots.A1.HeckeChar K,
      IsOfFinOrder χ ∧
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace K,
        v ∉ m.finitePart.support → χ.UnramifiedAt v) ∧
      ∀ (I : Ideal (𝓞 K)) (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I),
        χ.idealValue I =
          ((η (ArtinPrimitiveRoots.Hecke.rayClass m I hI) : ℂˣ) : ℂ) := by
  sorry

end ArtinPrimitiveRoots.A2
