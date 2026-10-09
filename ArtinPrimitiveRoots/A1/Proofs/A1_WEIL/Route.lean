import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.SignCharacter


set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem quadratic_sign_character_route (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (H : HilbertData F) (Bd : BData S H) :
    ∃ θB : Bd.B →* ℂˣ, ∀ v : FinPlace F, v ∉ S.Sf →
      ∀ p : Fˣ, ∀ (hpgen : S.IsGen (p : F) v.asIdeal),
        ∀ (hpAllowed : Bd.Allowed p),
        gamma D S A 3 v.asIdeal (p : F) =
          ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ) := by
  exact quadratic_sign_character_data D S A H Bd

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
