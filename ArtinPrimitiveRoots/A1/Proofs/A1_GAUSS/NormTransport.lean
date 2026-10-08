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

theorem normalized_cubic_jacobi_norm_lift {k K : Type*}
    [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (α : MulChar k ℂ) (hα : α ≠ 1) (hα3 : α ^ 3 = 1) :
    let J : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * jacobiSum α α
    ((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
      jacobiSum (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α)
        (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α) =
      -((-J) ^ Module.finrank k K) := by
  let n := Module.finrank k K
  let c : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)
  let J₀ := jacobiSum α α
  have hαα : α * α ≠ 1 := by
    intro h
    apply hα
    calc
      α = (α * α) * α := by rw [h, one_mul]
      _ = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hα3
  have hn : 1 ≤ n := Module.finrank_pos
  have hcard : Fintype.card K = Fintype.card k ^ n := Module.card_eq_pow_finrank
  have hpos : 0 < (Fintype.card k : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  have hscale : (Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) =
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    rw [hcard, Nat.cast_pow]
    calc
      ((Fintype.card k : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) =
          (Fintype.card k : ℝ) ^ ((n : ℝ) * (-(1 / 2 : ℝ))) :=
        (Real.rpow_natCast_mul (le_of_lt hpos) n (-(1 / 2 : ℝ))).symm
      _ = (Fintype.card k : ℝ) ^ ((-(1 / 2 : ℝ)) * (n : ℝ)) := by
        congr 1
        ring
      _ = ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ n :=
        Real.rpow_mul_natCast (le_of_lt hpos) (-(1 / 2 : ℝ)) n
  have hc : (((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c ^ n := by
    dsimp [c]
    exact_mod_cast hscale
  have hsign : (-1 : ℂ) ^ (n - 1) = -((-1 : ℂ) ^ n) := by
    have hexp : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hexp, pow_succ]
    ring
  change (((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      jacobiSum (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α)
        (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α) =
      -((-(c * J₀)) ^ n)
  rw [ArtinPrimitiveRoots.Arith.jacobiSum_lift α α hα hα hαα hn, hc]
  change c ^ n * ((-1 : ℂ) ^ (n - 1) * J₀ ^ n) = -((-(c * J₀)) ^ n)
  rw [hsign, neg_pow (c * J₀) n, mul_pow]
  ring

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
