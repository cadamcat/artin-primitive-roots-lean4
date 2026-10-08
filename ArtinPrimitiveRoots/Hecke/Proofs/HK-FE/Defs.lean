import ArtinPrimitiveRoots.Hecke.Continuation
import ArtinPrimitiveRoots.Hecke.Dictionary
import OAI.NumberTheory.DirichletL.FiniteFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! Exact arithmetic and theta objects for the primitive Hecke functional equation.
The Gaussian and full-unit box are the ones used by H1. The zero-point weight is retained
for the unit modulus; nontrivial character orthogonality removes it after summing classes. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain ClassFieldTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem DedekindResidue MeasureTheory
open scoped NumberField nonZeroDivisors Real Classical NNReal

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

/-- Primitivity in the exact ray quotient, including its infinite part. -/
def HKPrimitive {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) : Prop :=
  ∀ n : RayClassModulus K, FactorsThrough ψ n → n = m

/-- The conductor residue ring; it need not be a field. -/
abbrev HKResidueRing (m : RayClassModulus K) := (𝓞 K) ⧸ modulusIdeal m

instance hkResidueRingFinite (m : RayClassModulus K) : Finite (HKResidueRing m) := by
  letI : NeZero (modulusIdeal m) := ⟨modulusIdeal_ne_bot m⟩
  infer_instance

instance hkResidueRingFintype (m : RayClassModulus K) : Fintype (HKResidueRing m) :=
  Fintype.ofFinite _

/-- A residue character with its principal-ideal identification and ideal primitivity. -/
structure HKResidueCharacter {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) where
  character : MulChar (HKResidueRing m) ℂ
  principal_value : ∀ a : 𝓞 K, IsCoprimeTo m (Ideal.span {a}) →
    character (Ideal.Quotient.mk (modulusIdeal m) a) = charValue ψ (Ideal.span {a})
  primitive : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals character

/-- The different, as an invertible fractional ideal. -/
def hkDifferentUnit (K : Type*) [Field K] [NumberField K] :
    NumberFieldFractionalIdealGroup K :=
  idealUnit (differentIdeal ℤ (𝓞 K)) differentIdeal_ne_bot

/-- The conductor, as an invertible fractional ideal. -/
def hkModulusUnit (m : RayClassModulus K) : NumberFieldFractionalIdealGroup K :=
  idealUnit (modulusIdeal m) (modulusIdeal_ne_bot m)

/-- Different-normalized trace data. The ideal equality and coprimality encode exact local
orders of the trace generator; the trace formula fixes the Fourier convention. -/
structure HKTraceDatum (m : RayClassModulus K) where
  a : Kˣ
  B : Ideal (𝓞 K)
  coprime : IsCoprimeTo m B
  ideal_eq : idealUnit B coprime.1 =
    toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K
  additive : AddChar (HKResidueRing m) ℂ
  trace_value : ∀ x : 𝓞 K,
    additive (Ideal.Quotient.mk (modulusIdeal m) x) =
      Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ)
  primitive : additive.IsPrimitive

/-- The finite Gauss sum with exactly `N m` residue terms. -/
def hkGaussSum {m : RayClassModulus K} {ψ : RayClassGroup m →* ℂˣ}
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) : ℂ :=
  gaussSum χ.character T.additive

/-- The root number with the positive trace character and negative Fourier phase. -/
def hkRootNumber {m : RayClassModulus K} {ψ : RayClassGroup m →* ℂˣ}
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) : ℂ :=
  charValue ψ T.B * hkGaussSum χ T / (Real.sqrt (modulusNorm m : ℝ) : ℂ)

/-- Contract a fractional ideal to the ring of integers. For the quotients below,
integrality follows from membership of the numerator in the denominator ideal. -/
def hkIntegralPart (I : FractionalIdeal (𝓞 K)⁰ K) : Ideal (𝓞 K) :=
  (I : Submodule (𝓞 K) K).comap (Algebra.linearMap (𝓞 K) K)

/-- Zero extension of a ray character to fractional ideal units. -/
def hkFractionalCharValue {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) : ℂ :=
  if h : I ∈ rayClassPrimeToIdeals m then
    (ψ (QuotientGroup.mk (⟨I, h⟩ : rayClassPrimeToIdeals m)) : ℂ) else 0

/-- Ideal weight of a theta point. At zero the full theta keeps the unramified constant. -/
def hkPointWeight {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (x : K) : ℂ :=
  if x = 0 then
    if m.finitePart = 0 then hkFractionalCharValue ψ I⁻¹ else 0
  else charValue ψ (hkIntegralPart
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)))

/-- Weighted Gaussian theta on a fractional ideal, with H1's archimedean Gaussian. -/
def hkWeightedTheta {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (c : InfinitePlace K → ℝ) : ℂ :=
  ∑' x : {x : K // x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)},
    hkPointWeight ψ I x.1 *
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K, c w * (w x.1) ^ 2) : ℂ)

/-- Full-unit box average, using the same torsion multiplicity as H1. -/
def hkWeightedG {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (t : ℝ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    ∫ v in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      hkWeightedTheta ψ I (heckeWeights K t v)

/-- Norm normalization that makes the full-unit average depend only on the ordinary class. -/
def hkNormalizedG {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (t : ℝ) : ℂ :=
  hkWeightedG ψ I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t)

/-- Finite ordinary-class sum of the normalized weighted theta. -/
def hkWeightedH {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (t : ℝ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), hkNormalizedG ψ (classRep K C) t

/-- The conductor-scaled theta with the Deligne complex-Gamma normalization. -/
def hkWeightedPhi {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (t : ℝ) : ℂ :=
  ((2 : ℂ) ^ nrComplexPlaces K /
    ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))) * hkWeightedH ψ (t / modulusNorm m)

/-- The conductor-and-different dual fractional ideal. -/
def hkDualIdeal (m : RayClassModulus K) (I : NumberFieldFractionalIdealGroup K) :
    NumberFieldFractionalIdealGroup K :=
  (hkModulusUnit m * hkDifferentUnit K * I)⁻¹

/-- Actual dual ordinary class, determined by the fractional-ideal definition. -/
def hkDualClass (m : RayClassModulus K) (C : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K) :=
  (ClassGroup.mk K (hkModulusUnit m * hkDifferentUnit K))⁻¹ * C⁻¹

/-- Canonical H1 representatives; no new ray-unit fundamental domain is introduced. -/
def hkRayRepresentatives [IsTotallyComplex K] (m : RayClassModulus K) :
    IntegralRayRepresentatives m :=
  Classical.choice (exists_integralRayRepresentatives m)

/-- The entire uncompleted H1 function, retaining H1's exact Mellin normalization. -/
def hkEntireL [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (s : ℂ) : ℂ :=
  rayMellinNormalization K s * (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2)

/-- Conductor scaling of the H1 entire completed transform. -/
def hkCompleted [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (s : ℂ) : ℂ :=
  ((2 : ℂ) ^ nrComplexPlaces K /
    ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))) *
    (modulusNorm m : ℂ) ^ (s / 2) *
      (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2)

/-- Completed Gamma product, used only away from its poles. -/
def hkCompletedValue (L : ℂ → ℂ) (m : RayClassModulus K) (s : ℂ) : ℂ :=
  ((((discr K).natAbs : ℝ) * (modulusNorm m : ℝ) : ℝ) : ℂ) ^ (s / 2) *
    Complex.Gammaℂ s ^ nrComplexPlaces K * L s

end ArtinPrimitiveRoots.Hecke
