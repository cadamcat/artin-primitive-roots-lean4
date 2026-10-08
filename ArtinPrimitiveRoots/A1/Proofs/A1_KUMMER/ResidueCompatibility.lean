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
  rw [A2.qs_nq0_residue_ne_zero_iff_valuation_one P x]
  constructor
  · intro hv
    have hx : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hv]; exact one_ne_zero)
    refine ⟨?_, hx⟩
    rw [A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation P x hx,
      hv, WithZero.log_one, neg_zero]
  · rintro ⟨hcount, hx⟩
    have hc := A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation P x hx
    rw [hcount] at hc
    have hlog : WithZero.log (P.valuation F x) = 0 := neg_eq_zero.mp hc.symm
    calc
      P.valuation F x = WithZero.exp (WithZero.log (P.valuation F x)) :=
        (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)).symm
      _ = 1 := by rw [hlog, WithZero.exp_zero]

theorem chiAlg_spec (D : FieldData F) (P : FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (x : F) (hx : residue P x ≠ 0) :
    Ideal.Quotient.mk P.asIdeal ((chiAlg P x : (𝓞 F)ˣ) : 𝓞 F) =
      residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
  sorry

theorem residue_zero_finite (a : Fˣ) :
    {P : FinPlace F | residue P (a : F) = 0}.Finite := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
