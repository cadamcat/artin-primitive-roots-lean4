import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.FiniteField

/-! Cubic power residue symbols under finite-field norms. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

theorem cubic_power_residue_norm {k K : Type*} [Field k] [Field K]
    [Algebra k K] [Finite K] (h3 : 3 ∣ Nat.card k - 1) (x : K) :
    algebraMap k K (Algebra.norm k x ^ ((Nat.card k - 1) / 3)) =
      x ^ ((Nat.card K - 1) / 3) := by
  have hdiv : Nat.card k - 1 ∣ Nat.card K - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := K)]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hexp : ((Nat.card K - 1) / (Nat.card k - 1)) *
      ((Nat.card k - 1) / 3) = (Nat.card K - 1) / 3 := by
    rw [← Nat.mul_div_assoc _ h3, Nat.div_mul_cancel hdiv]
  rw [map_pow, FiniteField.algebraMap_norm_eq_pow, ← pow_mul, hexp]

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
