import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ContinuousCharacters
import ArtinPrimitiveRoots.Hecke.Dict.WeakApproximation

/-! Prime-value uniqueness through approximation and local normalization. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.A1.KummerProofs
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_kummer_sol

variable {F : Type} [Field F] [NumberField F]

theorem char_eq_of_local_eq_away (κ κ' : KummerChar F) (T : Finset (FinPlace F))
    (h : ∀ P : FinPlace F, P ∉ T → localComponent κ P = localComponent κ' P) :
    κ = κ' := by
  sorry

theorem local_eq_of_prime_values (κ κ' : KummerChar F) (P : FinPlace F)
    (hκ : unramifiedAt κ P) (hκ' : unramifiedAt κ' P)
    (hv : primeValue κ P = primeValue κ' P) : localComponent κ P = localComponent κ' P := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_kummer_sol
