import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.SquareClearing

/-!
# Integral quadratic-symbol representatives

Cubing the sextic residue symbol gives the quadratic symbol at primes
away from six. The integral cube is a sign; its reduction determines
which sign by the finite-field quadratic-character formula.
-/

set_option autoImplicit false

open scoped NumberField Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Away from six, the cubed sextic residue symbol is the quadratic symbol. -/
theorem qs_nq0_chi_cube_quad_symbol
    (D : FieldData K) (v : FinPlace K)
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (c : 𝓞 K) :
    chi D v (c : K) ^ 3 = (qsQuadSymbolAt v c : ℂ) := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hres : residue v (c : K) = Ideal.Quotient.mk v.asIdeal c :=
    qs_nq0_residue_algebraMap v c
  by_cases hx : residue v (c : K) = 0
  · have hc : Ideal.Quotient.mk v.asIdeal c = 0 := hres.symm.trans hx
    simp [chi, hx, qsQuadSymbolAt, hc]
  have hc : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
    simpa only [hres] using hx
  have hchar : ringChar (𝓞 K ⧸ v.asIdeal) ≠ 2 := by
    intro hchar
    have htwo : (2 : 𝓞 K ⧸ v.asIdeal) = 0 :=
      (ringChar.spec (𝓞 K ⧸ v.asIdeal) 2).mpr (by rw [hchar])
    have hmem : (2 : 𝓞 K) ∈ v.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using htwo)
    apply h6
    have hsix : (6 : 𝓞 K) = 3 * 2 := by norm_num
    rw [hsix]
    exact Ideal.mul_mem_left _ _ hmem
  have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hdiv : Fintype.card (𝓞 K ⧸ v.asIdeal) / 2 =
      (Ideal.absNorm v.asIdeal - 1) / 2 := by
    have hodd := FiniteField.odd_card_of_char_ne_two hchar
    omega
  have hquad := quadraticChar_eq_pow_of_char_ne_two hchar hc
  rw [hdiv] at hquad
  let z : 𝓞 K := (((chiAlg v (c : K) : (𝓞 K)ˣ) : 𝓞 K) ^ 3)
  have hzsq : z ^ 2 = 1 := by
    have hsix := congrArg Units.val
      ((mem_rootsOfUnity 6 (chiAlg v (c : K) : (𝓞 K)ˣ)).1
        (chiAlg v (c : K)).property)
    simpa only [z, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_one] using hsix
  have hred : Ideal.Quotient.mk v.asIdeal z =
      Ideal.Quotient.mk v.asIdeal c ^ ((Ideal.absNorm v.asIdeal - 1) / 2) := by
    simpa only [z, hres] using qs_nq0_chiAlg_cube_reduction D v h6 (c : K) hx
  have hcube : chi D v (c : K) ^ 3 = D.σ0 (algebraMap (𝓞 K) K z) := by
    rw [chi, if_neg hx, ← map_pow, ← map_pow]
  change chi D v (c : K) ^ 3 =
    (quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal c) : ℂ)
  rcases sq_eq_one_iff.mp hzsq with hz | hz
  · have hp : Ideal.Quotient.mk v.asIdeal c ^
        ((Ideal.absNorm v.asIdeal - 1) / 2) = 1 := by
      rw [← hred, hz, map_one]
    rw [hp, if_pos rfl] at hquad
    rw [hcube, hz, map_one, map_one, hquad, Int.cast_one]
  · have hp : Ideal.Quotient.mk v.asIdeal c ^
        ((Ideal.absNorm v.asIdeal - 1) / 2) ≠ 1 := by
      rw [← hred, hz, map_neg, map_one]
      exact Ring.neg_one_ne_one_of_char_ne_two hchar
    rw [if_neg hp] at hquad
    rw [hcube, hz, map_neg, map_one, map_neg, map_one, hquad,
      Int.cast_neg, Int.cast_one]

end ArtinPrimitiveRoots.A2
