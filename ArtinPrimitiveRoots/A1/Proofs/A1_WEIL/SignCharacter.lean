import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Assembly
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianExists
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianHilbert
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.WeilProduct
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianPrime

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The exact quadratic sign-character endpoint below Characters.lean, without an import cycle.
Guide: PROOFS.md:487–489. Uses the proved descent and the frozen local/global parts. -/
theorem quadratic_sign_character_data (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (H : HilbertData F) (Bd : BData S H) :
    ∃ θB : Bd.B →* ℂˣ, ∀ v : FinPlace F, v ∉ S.Sf →
      ∀ p : Fˣ, ∀ (hpgen : S.IsGen (p : F) v.asIdeal),
        ∀ (hpAllowed : Bd.Allowed p),
        gamma D S A 3 v.asIdeal (p : F) =
          ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ) := by
  let W := (local_gaussian_data D A).some
  exact quadratic_sign_character_of_indices D S A H Bd W.index
    (local_index_one A W) (local_index_square D A W) (local_index_hilbert_defect D A H W)
    (fun a => (weil_product D A W a).2) (exterior_local_index_unit D S A W)
    (exterior_prime_index_gamma D S A W)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
