import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseFieldCorrection
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryExists

/-! The ramified prime and the near-one kernel of the principal correction. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued
noncomputable section

attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open ArtinPrimitiveRoots.A1

theorem lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ E).zeta_sub_one_prime'

/-- The unique finite place above the Eisenstein ramified element. -/
def lambdaPlace : FinPlace E where
  asIdeal := Ideal.span {lambda}
  isPrime := Ideal.isPrime_span_singleton_of_prime lambda_prime
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero

theorem lambdaPlace_unique (v : FinPlace E) :
    lambda ∈ v.asIdeal ↔ v = lambdaPlace := by
  constructor
  · intro hv
    apply HeightOneSpectrum.ext
    exact (lambdaPlace.isMaximal.eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hv)).symm
  · rintro rfl
    exact Ideal.subset_span (Set.mem_singleton lambda)

/-- A local integral fraction close to one has a primary numerator and denominator.
The same global unit normalizes both integers, so their ratio is unchanged. -/
theorem primary_fraction_near_one (t : Eˣ)
    (hsmall : lambdaPlace.valuation E ((t : E) - 1) ≤ WithZero.exp (-2 : ℤ)) :
    ∃ (n d : OE) (hn : n ≠ 0) (hd : d ≠ 0),
      lambda ^ 2 ∣ n - 1 ∧ lambda ^ 2 ∣ d - 1 ∧
      t = integerFieldUnit n hn / integerFieldUnit d hd := by
  have hexp : WithZero.exp (-2 : ℤ) ≤ (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have ht : lambdaPlace.valuation E (t : E) ≤ 1 := by
    have h := (lambdaPlace.valuation E).map_add ((t : E) - 1) 1
    simpa only [sub_add_cancel, map_one, max_le_iff] using
      h.trans (max_le (hsmall.trans hexp) (by simp))
  obtain ⟨n, d, hnd⟩ := lambdaPlace.exists_primeCompl_mul_eq_of_integer (t : E) ht
  have hdnot : (d : OE) ∉ lambdaPlace.asIdeal := d.property
  have hd : (d : OE) ≠ 0 := fun h => hdnot (h ▸ Ideal.zero_mem _)
  have hdE : algebraMap OE E (d : OE) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective OE E)).mpr hd
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, map_zero] at hnd
    exact mul_ne_zero t.ne_zero hdE hnd
  have hdiff : lambda ^ 2 ∣ n - (d : OE) := by
    have hvd : lambdaPlace.valuation E (algebraMap OE E (d : OE)) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (lambdaPlace.intValuation_eq_one_iff_mem_primeCompl d).mpr d.property
    have heq : algebraMap OE E (n - (d : OE)) =
        ((t : E) - 1) * algebraMap OE E (d : OE) := by
      rw [map_sub, sub_mul, one_mul, hnd]
    have hval : lambdaPlace.intValuation (n - (d : OE)) ≤ WithZero.exp (-2 : ℤ) := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
      change lambdaPlace.valuation E (algebraMap OE E (n - (d : OE))) ≤ _
      rw [heq, map_mul, hvd, mul_one]
      exact hsmall
    have hmem := (lambdaPlace.intValuation_le_pow_iff_mem (n - (d : OE)) 2).mp hval
    simpa only [lambdaPlace, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hmem
  have hcop : (Ideal.span {(d : OE)} : Ideal OE) ⊔ Ideal.span {lambda} = ⊤ := by
    apply IsCoprime.sup_eq
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    apply IsCoprime.symm
    apply lambda_prime.irreducible.coprime_iff_not_dvd.mpr
    exact fun h => hdnot (Ideal.mem_span_singleton.mpr h)
  obtain ⟨p, hp, hpprimary⟩ := primary_generator_exists (Ideal.span {(d : OE)})
    (Ideal.span_singleton_eq_bot.not.mpr hd) hcop
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hp
  have hpne : p ≠ 0 := by
    rw [← hu]
    exact mul_ne_zero hd u.ne_zero
  have hnu : n * (u : OE) ≠ 0 := mul_ne_zero hn u.ne_zero
  refine ⟨n * u, p, hnu, hpne, ?_, hpprimary, ?_⟩
  · have h := dvd_add (dvd_mul_of_dvd_left hdiff (u : OE)) hpprimary
    convert h using 1
    rw [← hu]
    ring
  · apply Units.ext
    change (t : E) = algebraMap OE E (n * (u : OE)) / algebraMap OE E p
    apply (eq_div_iff ((map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective OE E)).mpr hpne)).mpr
    rw [← hu, map_mul, map_mul, ← mul_assoc, hnd]

/-- The ramified correction is trivial on the second principal-unit neighborhood. -/
theorem baseFieldCorrection_near_one (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (t : Eˣ)
    (hsmall : lambdaPlace.valuation E ((t : E) - 1) ≤ WithZero.exp (-2 : ℤ)) :
    baseFieldCorrection σ a t = 1 := by
  obtain ⟨n, d, hn, hd, hnp, hdp, ht⟩ := primary_fraction_near_one t hsmall
  rw [ht]
  exact baseFieldCorrection_primary_div σ φ hφ a ha n d hn hd hnp hdp

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
