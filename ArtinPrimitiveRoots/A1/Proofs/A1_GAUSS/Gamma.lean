import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueAdditive
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.NormTransport

/-! Transport of the frozen prime-ideal Gauss sums to the residue field. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem gamma_prime_eq_normalizedGauss (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (P : FinPlace F) (c : F)
    (χ : MulChar (𝓞 F ⧸ P.asIdeal) ℂ)
    (hχ : ∀ x : 𝓞 F, χ (Ideal.Quotient.mk P.asIdeal x) =
      chi D P (algebraMap (𝓞 F) F x))
    (ψ : AddChar (𝓞 F ⧸ P.asIdeal) ℂ)
    (hψ : ∀ x : 𝓞 F, ψ (Ideal.Quotient.mk P.asIdeal x) =
      S.e A (S.diag (algebraMap (𝓞 F) F x / c))) (j : ℕ) (hj : 0 < j) :
    letI : P.asIdeal.IsMaximal := P.isMaximal
    letI : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    letI : Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _
    gamma D S A (j : ℤ) P.asIdeal c = normalizedGauss (χ ^ j) ψ := by
  classical
  let : P.asIdeal.IsMaximal := P.isMaximal
  let : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let : Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _
  have hfac : UniqueFactorizationMonoid.normalizedFactors P.asIdeal = {P.asIdeal} := by
    simpa only [normalize_eq] using
      UniqueFactorizationMonoid.normalizedFactors_irreducible P.irreducible
  have hprime (x : F) (n : ℤ) :
      chiIdealPow D P.asIdeal x n = chiPow D P x n := by
    rw [chiIdealPow, hfac, Multiset.map_singleton, Multiset.prod_singleton]
    rw [dif_pos ⟨P.isPrime, P.ne_bot⟩]
  have hcard : Fintype.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  change gamma D S A (j : ℤ) P.asIdeal c = normalizedGauss (χ ^ j) ψ
  unfold gamma normalizedGauss gaussSum
  rw [hcard, finsum_eq_sum_of_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprime, ← hψ x.out, Ideal.Quotient.mk_out]
  congr 1
  have hχx : χ x = chi D P (algebraMap (𝓞 F) F x.out) := by
    simpa only [Ideal.Quotient.mk_out] using hχ x.out
  have hr : residue P (algebraMap (𝓞 F) F x.out) = x :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_algebraMap P x.out).trans
      (Ideal.Quotient.mk_out x)
  rw [chiPow, hr, ← hχx, χ.pow_apply' hj.ne' x]
  by_cases hx0 : x = 0
  · rw [hx0, ite_eq_left rfl, χ.map_zero, zero_pow hj.ne']
  · simp [hx0]

theorem gamma_duplication (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (c : F) (hc : S.IsGen c v.asIdeal) :
    gamma D S A 1 v.asIdeal c * gamma D S A 2 v.asIdeal c =
      ((starRingEnd ℂ) (chi D v 4) * gamma D S A 3 v.asIdeal c) *
        gamma D S A 2 v.asIdeal c ^ 3 := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  obtain ⟨χ, hχ, hχ6⟩ := residue_character_exists D v h6
  obtain ⟨ψ, hψ, hψprim⟩ := residue_additive_character_exists D S A v hc.1 c hc
  have hχne : χ ≠ 1 := by
    simpa only [pow_one] using
      residue_character_pow_ne_one D v h6 χ hχ 1 (by decide) (by decide)
  have hχ2 : χ ^ 2 ≠ 1 :=
    residue_character_pow_ne_one D v h6 χ hχ 2 (by decide) (by decide)
  have hquad : χ ^ 3 = quadraticComplex (k := 𝓞 F ⧸ v.asIdeal) :=
    residue_character_cube_eq_quadraticComplex D v h6 χ hχ hχ6
  have hneg : χ (-1) = 1 := residue_character_neg_one D v h6 χ hχ
  have hodd : ringChar (𝓞 F ⧸ v.asIdeal) ≠ 2 := by
    intro h
    have hneg' : (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := neg_one_eq_one_iff.mpr h
    apply h6
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_ofNat]
    linear_combination -3 * hneg'
  have htwo : (2 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
    intro h
    apply hodd
    apply neg_one_eq_one_iff.mp
    linear_combination -h
  have hfour : (4 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
    rw [show (4 : 𝓞 F ⧸ v.asIdeal) = (2 : 𝓞 F ⧸ v.asIdeal) ^ 2 by ring]
    exact pow_ne_zero _ htwo
  have hroot : χ (4 : 𝓞 F ⧸ v.asIdeal) ^ 6 = 1 := by
    rw [← χ.pow_apply' (by decide : (6 : ℕ) ≠ 0) (4 : 𝓞 F ⧸ v.asIdeal),
      hχ6, MulChar.one_apply (isUnit_iff_ne_zero.mpr hfour)]
  have hχ4 : χ (4 : 𝓞 F ⧸ v.asIdeal) = chi D v (4 : F) := by
    simpa only [map_ofNat] using hχ (4 : 𝓞 F)
  have hinv : (χ (4 : 𝓞 F ⧸ v.asIdeal))⁻¹ = (starRingEnd ℂ) (chi D v 4) := by
    calc
      (χ (4 : 𝓞 F ⧸ v.asIdeal))⁻¹ = (starRingEnd ℂ) (χ 4) :=
        Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hroot (by decide))
      _ = (starRingEnd ℂ) (chi D v 4) := by rw [hχ4]
  have hgamma (n : ℕ) (hn : 0 < n) :
      gamma D S A (n : ℤ) v.asIdeal c = normalizedGauss (χ ^ n) ψ :=
    gamma_prime_eq_normalizedGauss D S A v c χ hχ ψ hψ n hn
  have hg1 := hgamma 1 (by decide)
  have hg2 := hgamma 2 (by decide)
  have hg3 := hgamma 3 (by decide)
  simp only [Nat.cast_one, Nat.cast_ofNat, pow_one] at hg1 hg2 hg3
  rw [hg1, hg2, hg3]
  simpa only [hinv] using
    normalized_sextic_duplication χ ψ hχne hχ2 hχ6 hquad hneg hodd hψprim

theorem gamma_three_sign (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (c : F) (hc : S.IsGen c v.asIdeal) :
    gamma D S A 3 v.asIdeal c = 1 ∨ gamma D S A 3 v.asIdeal c = -1 := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  obtain ⟨χ, hχ, hχ6⟩ := residue_character_exists D v h6
  obtain ⟨ψ, hψ, hψprim⟩ := residue_additive_character_exists D S A v hc.1 c hc
  have hχ3 : χ ^ 3 ≠ 1 :=
    residue_character_pow_ne_one D v h6 χ hχ 3 (by decide) (by decide)
  have hχ32 : (χ ^ 3) ^ 2 = 1 := by
    simpa only [← pow_mul] using hχ6
  have hquad : (χ ^ 3).IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ32
  have hneg : (χ ^ 3) (-1) = 1 := by
    rw [χ.pow_apply' (by decide : (3 : ℕ) ≠ 0),
      residue_character_neg_one D v h6 χ hχ, one_pow]
  have hsq := normalized_quadratic_gauss_sq (χ ^ 3) ψ hχ3 hquad hneg hψprim
  have hgamma := gamma_prime_eq_normalizedGauss D S A v c χ hχ ψ hψ 3 (by decide)
  simp only [Nat.cast_ofNat] at hgamma
  rw [← hgamma] at hsq
  exact sq_eq_one_iff.mp hsq

theorem gamma_two_cube_eq_jacobiSum (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (c : F) (hc : S.IsGen c v.asIdeal)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχ : ∀ x : 𝓞 F, χ (Ideal.Quotient.mk v.asIdeal x) =
      chi D v (algebraMap (𝓞 F) F x)) (hχ6 : χ ^ 6 = 1) :
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    gamma D S A 2 v.asIdeal c ^ 3 =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        jacobiSum (χ ^ 2) (χ ^ 2) := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  obtain ⟨ψ, hψ, hψprim⟩ := residue_additive_character_exists D S A v hc.1 c hc
  have hχ2 : χ ^ 2 ≠ 1 :=
    residue_character_pow_ne_one D v h6 χ hχ 2 (by decide) (by decide)
  have hχ23 : (χ ^ 2) ^ 3 = 1 := by
    simpa only [← pow_mul] using hχ6
  have hneg : (χ ^ 2) (-1) = 1 := by
    rw [χ.pow_apply' (by decide : (2 : ℕ) ≠ 0),
      residue_character_neg_one D v h6 χ hχ, one_pow]
  have hcube := normalized_cubic_gauss_cube (χ ^ 2) ψ hχ2 hχ23 hneg hψprim
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hgamma := gamma_prime_eq_normalizedGauss D S A v c χ hχ ψ hψ 2 (by decide)
  simp only [Nat.cast_ofNat] at hgamma
  rw [← hgamma, hcard] at hcube
  exact hcube

theorem gamma_two_cube_of_norm_lift (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (c : F) (hc : S.IsGen c v.asIdeal)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχ : ∀ x : 𝓞 F, χ (Ideal.Quotient.mk v.asIdeal x) =
      chi D v (algebraMap (𝓞 F) F x)) (hχ6 : χ ^ 6 = 1)
    {k : Type*} [Field k] [Fintype k] :
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    ∀ (alg : Algebra k (𝓞 F ⧸ v.asIdeal)),
    letI : Algebra k (𝓞 F ⧸ v.asIdeal) := alg
    ∀ (α : MulChar k ℂ), α ≠ 1 → α ^ 3 = 1 →
      χ ^ 2 = ArtinPrimitiveRoots.Arith.normLift (k := k)
        (K := 𝓞 F ⧸ v.asIdeal) α →
      ∀ (z : ℂ),
        ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * jacobiSum α α = -z →
        gamma D S A 2 v.asIdeal c ^ 3 =
          -(z ^ Module.finrank k (𝓞 F ⧸ v.asIdeal)) := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  intro alg
  letI : Algebra k (𝓞 F ⧸ v.asIdeal) := alg
  intro α hα hα3 hlift z hJ
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hgamma := gamma_two_cube_eq_jacobiSum D S A v hv c hc χ hχ hχ6
  rw [← hcard, hlift] at hgamma
  have hnorm := normalized_cubic_jacobi_norm_lift
    (k := k) (K := 𝓞 F ⧸ v.asIdeal) α hα hα3
  dsimp only at hnorm
  rw [hJ, neg_neg] at hnorm
  exact hgamma.trans hnorm

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
