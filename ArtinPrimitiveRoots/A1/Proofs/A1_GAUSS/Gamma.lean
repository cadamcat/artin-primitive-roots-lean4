import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueAdditive

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

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
