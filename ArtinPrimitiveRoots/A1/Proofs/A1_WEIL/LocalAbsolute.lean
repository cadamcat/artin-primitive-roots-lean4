import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Basic positivity and multiplication for the frozen normalized finite absolute value.
Guide: PROOFS.md:464–469. Uses: absFin; Ideal.absNorm_pos; WithZeroMulInt.toNNReal. -/
theorem local_absolute_value (v : FinPlace F) :
    absFin v 1 = 1 ∧
    (∀ a : (v.adicCompletion F)ˣ, 0 < absFin v (a : v.adicCompletion F)) ∧
    (∀ a b : (v.adicCompletion F)ˣ,
      absFin v ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        absFin v (a : v.adicCompletion F) * absFin v (b : v.adicCompletion F)) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
