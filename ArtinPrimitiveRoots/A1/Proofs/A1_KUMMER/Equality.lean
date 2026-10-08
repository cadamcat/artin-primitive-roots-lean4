import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Idelic
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.PrimeValues
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Detection
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.UniquenessInterfaces

/-! Finite-order uniqueness outside a finite set of primes. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem finite_order_good_prime_unique (κ κ' : KummerChar F)
    (hκ : IsOfFinOrder κ) (hκ' : IsOfFinOrder κ') (T : Finset (FinPlace F))
    (h : ∀ P : FinPlace F, P ∉ T → unramifiedAt κ P ∧ unramifiedAt κ' P ∧
      primeValue κ P = primeValue κ' P) : κ = κ' := by
  apply ArtinPrimitiveRoots.Proofs.a1_kummer_sol.char_eq_of_local_eq_away κ κ' T
  intro P hP
  obtain ⟨hu, hu', hv⟩ := h P hP
  exact ArtinPrimitiveRoots.Proofs.a1_kummer_sol.local_eq_of_prime_values κ κ' P hu hu' hv

end ArtinPrimitiveRoots.A1.KummerProofs
