import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Local units have trivial index at odd unramified-character exterior places.
Guide: PROOFS.md:473–477. Uses: A.unramified; S.over6; S.different_mem; actual shell cancellation. -/
theorem exterior_local_index_unit (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (hv : v ∉ S.Sf) (a : Fˣ)
    (ha : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0) :
    W.index v (toLoc v a) = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
