import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.FiniteNormTransport
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryPrimeSpec

/-! The unramified factors of the Eisenstein primary character.
The finite family has weight one at ramified places; the base construction
must supply the ramified correction enforcing the principal relation.
Continuity follows from the open subgroup of local integral units, as in
the conductor construction in Characters, without importing that file. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued
noncomputable section

attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open ArtinPrimitiveRoots.A1

/-- The nonzero complex angular coordinate as a unit. -/
def normalizedComplexUnit (z : ℂ) (hz : z ≠ 0) : ℂˣ :=
  Units.mk0 (z / ‖z‖) (div_ne_zero hz (by
    exact_mod_cast norm_ne_zero_iff.mpr hz))

theorem normalizedComplexUnit_norm (z : ℂ) (hz : z ≠ 0) :
    ‖(normalizedComplexUnit z hz : ℂ)‖ = 1 := by
  change ‖z / (‖z‖ : ℂ)‖ = 1
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- Nonvanishing of the complex primary prime generator. -/
theorem primary_prime_complex_ne_zero (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) : integerComplex σ (primary v.asIdeal) ≠ 0 := by
  have hp : algebraMap OE E (primary v.asIdeal) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap OE E)
      (FaithfulSMul.algebraMap_injective OE E)).mpr (primary_prime_spec v hv).1
  simpa only [integerComplex, RingHom.comp_apply, map_zero] using σ.injective.ne hp

/-- The primary angular weight at exterior primes and weight one elsewhere. -/
def basePrimeWeight (σ : E →+* ℂ) (v : FinPlace E) : ℂˣ :=
  if hv : lambda ∉ v.asIdeal then
    normalizedComplexUnit (integerComplex σ (primary v.asIdeal))
      (primary_prime_complex_ne_zero σ v hv)
  else 1

theorem basePrimeWeight_norm (σ : E →+* ℂ) (v : FinPlace E) :
    ‖(basePrimeWeight σ v : ℂ)‖ = 1 := by
  unfold basePrimeWeight
  split
  · exact normalizedComplexUnit_norm _ _
  · simp

theorem basePrimeWeight_exterior (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    (basePrimeWeight σ v : ℂ) = eisensteinPrimeValue σ v := by
  simp only [basePrimeWeight, dite_eq_left hv, normalizedComplexUnit,
    Units.val_mk0, eisensteinPrimeValue]

variable {K : Type} [Field K] [NumberField K]

/-- A complex weight raised to local order, bundled continuously. -/
def valuationCharacter (v : HeightOneSpectrum (𝓞 K)) (c : ℂˣ) :
    ContinuousMonoidHom (v.adicCompletion K)ˣ ℂˣ where
  toMonoidHom := (zpowersHom ℂˣ c).comp (FiniteIdeleGroup.localOrder v)
  continuous_toFun := by
    let f := (zpowersHom ℂˣ c).comp (FiniteIdeleGroup.localOrder v)
    have hunit (u : (v.adicCompletion K)ˣ) (hu : localUnit v u) : f u = 1 := by
      have hv := (FiniteIdeleGroup.localOrder_eq_zero_iff v u).mpr hu
      change c ^ (FiniteIdeleGroup.localOrder v u).toAdd = 1
      rw [hv, zpow_zero]
    have hopen : IsOpen {u : (v.adicCompletion K)ˣ | localUnit v u} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        Units.continuous_val |>.inter
          ((Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
            Units.continuous_coe_inv)
    have hU : {u : (v.adicCompletion K)ˣ | localUnit v u} ∈ 𝓝 1 :=
      hopen.mem_nhds (by constructor <;> simp)
    have heq : f =ᶠ[𝓝 1] fun _ => (1 : ℂˣ) := by
      filter_upwards [hU] with u hu
      exact hunit u hu
    exact continuous_of_tendsto_nhds_one f
      ((Filter.tendsto_congr' heq).mpr tendsto_const_nhds)

theorem valuationCharacter_apply (v : HeightOneSpectrum (𝓞 K)) (c : ℂˣ)
    (u : (v.adicCompletion K)ˣ) :
    valuationCharacter v c u = c ^ (FiniteIdeleGroup.localOrder v u).toAdd := rfl

theorem valuationCharacter_localUnit (v : HeightOneSpectrum (𝓞 K)) (c : ℂˣ)
    (u : (v.adicCompletion K)ˣ) (hu : localUnit v u) :
    valuationCharacter v c u = 1 := by
  rw [valuationCharacter_apply, (FiniteIdeleGroup.localOrder_eq_zero_iff v u).mpr hu,
    zpow_zero]

theorem valuationCharacter_unitary (v : HeightOneSpectrum (𝓞 K)) (c : ℂˣ)
    (hc : ‖(c : ℂ)‖ = 1) (u : (v.adicCompletion K)ˣ) :
    ‖(valuationCharacter v c u : ℂ)‖ = 1 := by
  rw [valuationCharacter_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hc, one_zpow]

theorem valuationCharacter_uniformizer (v : HeightOneSpectrum (𝓞 K)) (c : ℂˣ) :
    valuationCharacter v c (toLoc v (KummerProofs.uniformizerUnit v)) = c := by
  rw [valuationCharacter_apply]
  have horder : (FiniteIdeleGroup.localOrder v
      (toLoc v (KummerProofs.uniformizerUnit v))).toAdd = 1 := by
    rw [FiniteIdeleGroup.localOrder_apply, uniformizer_valuation, WithZero.log_exp]
    norm_num
  rw [horder, zpow_one]

/-- The exterior primary local family, before its ramified correction. -/
def baseFiniteCharacter (σ : E →+* ℂ) (v : FinPlace E) :
    ContinuousMonoidHom (v.adicCompletion E)ˣ ℂˣ :=
  valuationCharacter v (basePrimeWeight σ v)

theorem baseFiniteCharacter_localUnit (σ : E →+* ℂ) (v : FinPlace E)
    (u : (v.adicCompletion E)ˣ) (hu : localUnit v u) :
    baseFiniteCharacter σ v u = 1 :=
  valuationCharacter_localUnit v (basePrimeWeight σ v) u hu

theorem baseFiniteCharacter_unitary (σ : E →+* ℂ) (v : FinPlace E)
    (u : (v.adicCompletion E)ˣ) :
    ‖(baseFiniteCharacter σ v u : ℂ)‖ = 1 :=
  valuationCharacter_unitary v (basePrimeWeight σ v) (basePrimeWeight_norm σ v) u

theorem baseFiniteCharacter_prime_formula (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    (baseFiniteCharacter σ v (toLoc v (KummerProofs.uniformizerUnit v)) : ℂ) =
      eisensteinPrimeValue σ v := by
  rw [baseFiniteCharacter, valuationCharacter_uniformizer]
  exact basePrimeWeight_exterior σ v hv

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
