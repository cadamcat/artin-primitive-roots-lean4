import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Local

/-! Positive tame orientation at the frozen global uniformizer. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem frobenius_residue_root (D : FieldData F) (H : HilbertData F)
    (a : Fˣ) (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
    (ha : residue P (a : F) ≠ 0) :
    ((kummerLocal D H P (toLoc P a) (toLoc P (uniformizerUnit P)) : ℂˣ) : ℂ) =
      chi D P (a : F) := by
  have hv : P.valuation F (uniformizerUnit P : F) = WithZero.exp (-1) :=
    (HeightOneSpectrum.valuation_exists_uniformizer F P).choose_spec
  have hcount : FractionalIdeal.count F P
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (uniformizerUnit P : F)) = 1 := by
    rw [A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation P _
      (uniformizerUnit P).ne_zero, hv, WithZero.log_exp]
    rfl
  have htame := H.tame P h6 a (uniformizerUnit P) ha
  rw [hcount, zpow_one] at htame
  change D.σ0 ((H.hilb P (toLoc P a) (toLoc P (uniformizerUnit P)) : Fˣ) : F) = _
  rw [htame, chi, ite_eq_right ha]

theorem kummer_prime_values (D : FieldData F) (H : HilbertData F) (a : Fˣ)
    (κ : KummerChar F)
    (hloc : ∀ P : FinPlace F, localComponent κ P = kummerLocal D H P (toLoc P a))
    (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (ha : residue P (a : F) ≠ 0) :
    unramifiedAt κ P ∧ primeValue κ P = chi D P (a : F) := by
  have hnr : unramifiedAt κ P := by
    intro x hx hxinv
    rw [hloc P]
    exact kummer_local_unit_trivial D H P h6 a ha x ⟨hx, hxinv⟩
  refine ⟨hnr, ?_⟩
  rw [primeValue, ite_eq_left hnr, hloc P]
  exact frobenius_residue_root D H a P h6 ha

end ArtinPrimitiveRoots.A1.KummerProofs
