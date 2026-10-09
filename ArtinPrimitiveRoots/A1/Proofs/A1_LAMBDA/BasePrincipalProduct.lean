import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseFiniteCharacters

/-! The principal finite product of the Eisenstein primary factors.
Ideal factorization identifies the product on nonzero primary integers.
This supplies the algebraic principal correction; its ramified continuity
and completion extension are separate steps. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued
noncomputable section

attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open ArtinPrimitiveRoots.A1

variable {K : Type} [Field K] [NumberField K]

/-- A nonzero integer as a field unit. -/
def integerFieldUnit (n : 𝓞 K) (hn : n ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K n)
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hn)

/-- Local order of an integral principal element is its ideal multiplicity. -/
theorem localOrder_integerFieldUnit (v : HeightOneSpectrum (𝓞 K))
    (n : 𝓞 K) (hn : n ≠ 0) :
    (FiniteIdeleGroup.localOrder v (toLoc v (integerFieldUnit n hn))).toAdd =
      ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {n} : Ideal (𝓞 K))).factors : ℤ) := by
  rw [FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (Valued.v
    (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K n))) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    v.valuation_of_algebraMap, v.intValuation_if_neg hn, WithZero.log_exp, neg_neg]

/-- The ordinary principal idele recovers the frozen local unit embedding. -/
theorem principal_finiteComponent_toLoc (t : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (_root_.IdeleGroup.principalIdele K t).2 v = toLoc v t := by
  apply Units.ext
  rfl

/-- The finite primary family has finite multiplicative support on principals. -/
theorem baseFiniteCharacter_principal_support (σ : E →+* ℂ) (t : Eˣ) :
    Function.HasFiniteMulSupport
      (fun v : FinPlace E => baseFiniteCharacter σ v (toLoc v t)) := by
  apply (FiniteIdeleGroup.finite_nonLocalUnits
    (_root_.IdeleGroup.principalIdele E t).2).subset
  intro v hv hu
  apply hv
  have hunit : localUnit v (toLoc v t) := by
    rw [principal_finiteComponent_toLoc] at hu
    exact hu
  exact baseFiniteCharacter_localUnit σ v _ hunit

/-- The principal finite product, as a field-unit homomorphism. -/
def exteriorFieldProduct (σ : E →+* ℂ) : Eˣ →* ℂˣ where
  toFun t := ∏ᶠ v : FinPlace E, baseFiniteCharacter σ v (toLoc v t)
  map_one' := by simp
  map_mul' t s := by
    simp only [map_mul]
    exact finprod_mul_distrib (baseFiniteCharacter_principal_support σ t)
      (baseFiniteCharacter_principal_support σ s)

theorem exteriorFieldProduct_unitary (σ : E →+* ℂ) (t : Eˣ) :
    ‖(exteriorFieldProduct σ t : ℂ)‖ = 1 := by
  change ‖(((∏ᶠ v : FinPlace E, baseFiniteCharacter σ v (toLoc v t)) : ℂˣ) : ℂ)‖ = 1
  rw [finprod_eq_prod _ (baseFiniteCharacter_principal_support σ t)]
  apply Finset.prod_induction _ (fun u : ℂˣ => ‖(u : ℂ)‖ = 1)
  · intro x y hx hy
    rw [Units.val_mul, norm_mul, hx, hy, one_mul]
  · simp
  · intro v _
    exact baseFiniteCharacter_unitary σ v _

/-- Nonzero integers remain nonzero under the chosen complex embedding. -/
theorem integerComplex_ne_zero (σ : E →+* ℂ) (n : OE) (hn : n ≠ 0) :
    integerComplex σ n ≠ 0 := by
  have hfield : algebraMap OE E n ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective OE E)).mpr hn
  simpa only [integerComplex, RingHom.comp_apply, map_zero] using σ.injective.ne hfield

/-- On a primary integer, each local factor is the ideal character's factor. -/
theorem baseFiniteCharacter_primary_factor (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (n : OE) (hn : n ≠ 0) (hprimary : lambda ^ 2 ∣ n - 1) (v : FinPlace E) :
    (baseFiniteCharacter σ v (toLoc v (integerFieldUnit n hn)) : ℂ) =
      φ (v.maxPowDividing (Ideal.span {n})) := by
  let I : Ideal OE := Ideal.span {n}
  let k := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have hI : I ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  rw [baseFiniteCharacter, valuationCharacter_apply, localOrder_integerFieldUnit,
    Units.val_zpow_eq_zpow_val, zpow_natCast]
  change (basePrimeWeight σ v : ℂ) ^ k = φ (v.asIdeal ^ k)
  rw [map_pow]
  by_cases hk : k = 0
  · simp [hk]
  · have hdvd : v.asIdeal ∣ I :=
      (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hk
    have hnmem : n ∈ v.asIdeal := by
      simpa only [I, Ideal.dvd_span_singleton] using hdvd
    let : v.asIdeal.IsMaximal := v.isMaximal
    have hv : lambda ∉ v.asIdeal :=
      OAI.ActualEisensteinCubic.primary_maximal_divisor_good n hprimary v.asIdeal hnmem
    rw [basePrimeWeight_exterior σ v hv, hφ]
    rfl

/-- The principal finite product equals the angular value on primary integers. -/
theorem exteriorFieldProduct_primary (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (n : OE) (hn : n ≠ 0) (hprimary : lambda ^ 2 ∣ n - 1) :
    exteriorFieldProduct σ (integerFieldUnit n hn) =
      normalizedComplexUnit (integerComplex σ n) (integerComplex_ne_zero σ n hn) := by
  apply Units.ext
  change (Units.coeHom ℂ)
    (∏ᶠ v : FinPlace E, baseFiniteCharacter σ v (toLoc v (integerFieldUnit n hn))) = _
  rw [(Units.coeHom ℂ).map_finprod
    (baseFiniteCharacter_principal_support σ (integerFieldUnit n hn))]
  have hI : (Ideal.span {n} : Ideal OE) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  calc
    (∏ᶠ v : FinPlace E, (baseFiniteCharacter σ v (toLoc v (integerFieldUnit n hn)) : ℂ)) =
        ∏ᶠ v : FinPlace E, φ (v.maxPowDividing (Ideal.span {n})) :=
      finprod_congr (baseFiniteCharacter_primary_factor σ φ hφ n hn hprimary)
    _ = φ (Ideal.span {n}) := by
      exact (φ.toMonoidHom.map_finprod (Ideal.hasFiniteMulSupport hI)).symm.trans
        (congrArg φ (Ideal.finprod_heightOneSpectrum_factorization hI))
    _ = (normalizedComplexUnit (integerComplex σ n)
        (integerComplex_ne_zero σ n hn) : ℂ) := by
      have hgen : primary (Ideal.span {n}) = n :=
        OAI.CompletedGauss.primaryGenerator_span n hn hprimary
      rw [hφ, hgen]
      rfl

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
