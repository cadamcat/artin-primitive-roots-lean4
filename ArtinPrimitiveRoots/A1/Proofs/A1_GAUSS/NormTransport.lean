import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.FiniteField
import ArtinPrimitiveRoots.Arith.DavenportHasse

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

theorem cubic_character_norm_transport {k K : Type*} [Field k] [Field K]
    [Algebra k K] [Finite K] (h3 : 3 ∣ Nat.card k - 1)
    (α : MulChar k ℂ) (β : MulChar K ℂ) (readRoot : K → ℂ)
    (hα : ∀ u : kˣ, α (u : k) =
      readRoot (algebraMap k K ((u : k) ^ ((Nat.card k - 1) / 3))))
    (hβ : ∀ u : Kˣ, β (u : K) =
      readRoot ((u : K) ^ ((Nat.card K - 1) / 3))) :
    β = ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α := by
  apply MulChar.ext
  intro u
  have hαnorm : α (Algebra.norm k (u : K)) =
      readRoot (algebraMap k K
        (Algebra.norm k (u : K) ^ ((Nat.card k - 1) / 3))) := by
    simpa only [Units.coe_map] using hα (Units.map (Algebra.norm k) u)
  rw [hβ u, ArtinPrimitiveRoots.Arith.normLift_apply, hαnorm,
    cubic_power_residue_norm h3 (u : K)]

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
