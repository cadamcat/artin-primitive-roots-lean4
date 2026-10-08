import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits

/-! Residue/valuation and sextic-root compatibility shared with A1-HILBERT. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem residue_ne_zero_iff_ord_zero (P : FinPlace F) (x : F) :
    residue P x ≠ 0 ↔
      FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) = 0 ∧ x ≠ 0 := by
  sorry

theorem chiAlg_spec (D : FieldData F) (P : FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (x : F) (hx : residue P x ≠ 0) :
    Ideal.Quotient.mk P.asIdeal ((chiAlg P x : (𝓞 F)ˣ) : 𝓞 F) =
      residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
  sorry

theorem residue_zero_finite (a : Fˣ) :
    {P : FinPlace F | residue P (a : F) = 0}.Finite := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
