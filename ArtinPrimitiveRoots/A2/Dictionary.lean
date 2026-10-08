import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Dictionary
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
ideals prime to its modulus. Corrected per rev-a2 to include the conductor divisibility condition.
-/
theorem rayClass_idelic_dictionary {K : Type} [Field K] [NumberField K]
    (m : RayClassModulus K) (η : RayClassGroup m →* ℂˣ) :
    ∃ χ : ArtinPrimitiveRoots.A1.HeckeChar K,
      IsOfFinOrder χ ∧
      χ.ConductorDvd (ArtinPrimitiveRoots.Dictionary.modulusIdeal m) ∧
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace K,
        v ∉ m.finitePart.support → χ.UnramifiedAt v) ∧
      ∀ (I : Ideal (𝓞 K)) (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I),
        χ.idealValue I =
          ((η (ArtinPrimitiveRoots.Hecke.rayClass m I hI) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨χ, hfin, hcond, hprime⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_heckeChar_of_rayClass m η
  refine ⟨χ, hfin, hcond, ?_, ?_⟩
  · intro v hv
    exact (hprime v hv).1
  · intro I hI
    have hval :=
      ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue η χ hprime I hI
    simpa [ArtinPrimitiveRoots.Hecke.charValue, hI] using hval

end ArtinPrimitiveRoots.A2
