import ArtinPrimitiveRoots.Splitting.Defs
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.Frobenius
import Mathlib.Analysis.MellinInversion
import TauCeti.NumberTheory.NumberField.Discriminant.Relative

/-!
# External inputs for §7

The Hecke/Dedekind continuation, Hecke-character continuation, and changes of modulus are
provided by `ArtinPrimitiveRoots.Hecke` (D1, D2, H1 and `LSeriesRay_change_modulus`); this file
does not declare replacement `ext:dedekind-fe`, `ext:hecke-L-holomorphic`, or Euler-factor nodes.
Source rows are recorded on each remaining external interface below.
-/

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Ext.SplittingInputs

open Classical Polynomial
open Complex
open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke ClassFieldTheory

/-- **`ext:kummer-irreducible`**, `07-splitting.tex:43-49`. Mathlib
`X_pow_sub_C_irreducible_of_prime` (`Mathlib/FieldTheory/KummerPolynomial.lean:99`): if `p` is
prime and `a` has no `p`th root in a field, `X^p-C(a)` is irreducible. -/
theorem ext_kummer_irreducible {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {a : K}
    (ha : ∀ b : K, b ^ p ≠ a) : Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
  sorry

/-- **`ext:kummer-galois`**, `07-splitting.tex:44-51`. Mathlib
`autEquivRootsOfUnity` (`Mathlib/FieldTheory/KummerExtension.lean:398`) identifies the Galois
group of a Kummer splitting field with the `n`th roots of unity when the base contains `μ_n`. -/
theorem ext_kummer_galois {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {a : K}
    (hζ : (primitiveRoots n K).Nonempty)
    (H : Irreducible (Polynomial.X ^ n - Polynomial.C a))
    [IsSplittingField K L (Polynomial.X ^ n - Polynomial.C a)] :
    Nonempty (Gal(L/K) ≃* rootsOfUnity n K) := by
  sorry

/-- **`ext:frobenius`**, `01a-reduction.tex:83-96`. Mathlib `arithFrobAt` and
`IsArithFrobAt` (`Mathlib/RingTheory/Frobenius.lean:260-270`) give an arithmetic Frobenius at
every prime with finite residue field. -/
theorem ext_frobenius {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S] [IsGaloisGroup G R S]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] :
    IsArithFrobAt R (arithFrobAt R G Q) Q := by
  sorry

/-- The arithmetic Frobenius congruence at a prime of the integral closure. -/
def IsArithmeticFrobeniusAt {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
    (σ : L ≃ₐ[K] L) : Prop :=
  ∀ x : 𝓞 L, ∃ y : 𝓞 L, (y : L) = σ (x : L) ∧
    y - x ^ Ideal.absNorm p ∈ P

/-- A prime outside the modulus is unramified in the extension. -/
def IsUnramifiedOutsideModulus {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    (m : RayClassModulus K) : Prop :=
  ∀ (p : Ideal (𝓞 K)), p.IsPrime → IsCoprimeTo m p →
    (p.ramificationIdxIn (𝓞 L)) = 1

/-- The ray-class Artin map has arithmetic-Frobenius normalization at every prime outside its
modulus. This is the form of ClassFieldTheory's `FiniteAbelianReciprocityData.artin_frobenius` used
in §7. -/
def FrobeniusNormalizedArtinMap {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Algebra (𝓞 K) (𝓞 L)] (m : RayClassModulus K)
    (Art : RayClassGroup m →* (L ≃ₐ[K] L)) : Prop :=
  IsUnramifiedOutsideModulus (K := K) (L := L) m ∧
  ∀ (p : Ideal (𝓞 K)), p.IsPrime → (hcop : IsCoprimeTo m p) →
    ∀ (P : Ideal (𝓞 L)), P.IsPrime → P.LiesOver p →
      ∃ σ : L ≃ₐ[K] L, Art (rayClass m p hcop) = σ ∧
        IsArithmeticFrobeniusAt p P σ

/-- **`ext:cft-artin`**, `07-splitting.tex:78-91`. ClassFieldTheory
`finiteAbelianGlobalReciprocity` (`Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/
FiniteAbelianGlobalReciprocity.lean:31-37`) supplies a modulus, a surjective Artin map, and
arithmetic-Frobenius normalization. The ray-class types here are the verbatim local copy in
`Hecke/RayClassCopy.lean`; ClassFieldTheory itself is deliberately not imported. -/
theorem ext_cft_artin {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)] [IsAbelianGalois K L] :
    ∃ (m : RayClassModulus K) (Art : RayClassGroup m →* (L ≃ₐ[K] L)),
      Function.Surjective Art ∧ FrobeniusNormalizedArtinMap m Art := by
  sorry

/-- **`ext:split-criterion`**, `07-splitting.tex:231-233`. TauCeti
`NumberField.ncard_primesOver_eq_finrank_iff` (`TauCeti/NumberField/SplitsCompletely/Basic.lean:82`)
characterizes complete splitting in a Galois number field by `e=f=1`. -/
theorem ext_split_criterion (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [Fact p.Prime] :
    splitsCompletely K p ↔
      (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
        (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  sorry

/-- The norm conclusion for primes above a completely split rational prime. TauCeti
`Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank` (`SplitsCompletely/Basic.lean:161`). -/
theorem ext_split_prime_norm (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K))
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hsplit : splitsCompletely K p) : Ideal.absNorm P = p := by
  sorry

/-- **`ext:cyclotomic-disc`**, `07-splitting.tex:58-61`. Mathlib
`IsCyclotomicExtension.Rat.discr_prime` (`Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean:651`)
gives the prime cyclotomic discriminant. -/
theorem ext_cyclotomic_disc {q : ℕ} [NeZero q] (hq : q.Prime) :
    absoluteDiscriminant (CyclotomicField q ℚ) = (q : ℝ) ^ (q - 2) := by
  sorry

/-- **`ext:disc-tower`**, `07-splitting.tex:63-68`. TauCeti
`TauCeti.NumberField.relDiscr_tower` (`NumberField/Discriminant/Relative.lean:43-46`) gives
transitivity of the relative discriminant in a tower. -/
theorem ext_disc_tower {K L M : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    TauCeti.relDiscr (𝓞 K) (𝓞 M) =
      TauCeti.relDiscr (𝓞 K) (𝓞 L) ^ Module.finrank L M *
        Ideal.relNorm (𝓞 K) (TauCeti.relDiscr (𝓞 L) (𝓞 M)) := by
  sorry

/-- **`ext:fundamental-identity`**, `07-splitting.tex:164-170`. Mathlib
`Ideal.sum_ramification_inertia` (`Mathlib/NumberTheory/RamificationInertia/Basic.lean:614`) is
the identity `Σ_{P|p} e_P f_P = [L:K]`. -/
theorem ext_fundamental_identity {R S K L : Type*} [CommRing R] [CommRing S]
    [Field K] [Field L] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
      Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P = Module.finrank K L := by
  sorry

/-- **`ext:dedekind-euler-logderiv`**, `07-splitting.tex:132-145`. TauCeti
`dedekindZeta_eulerProduct_hasProd` (`ArithmeticDirichletSeries/EulerProduct/Analytic.lean:498`)
and the logarithmic derivative of that product give the prime-ideal series on `Re s > 1`. -/
theorem ext_dedekind_euler_logderiv (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    (∀ v : HeightOneSpectrum (𝓞 K), Summable (fun j : ℕ =>
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j + 1 : ℕ) : ℂ) * s))) ∧
    Summable (fun v : HeightOneSpectrum (𝓞 K) => ∑' j : ℕ,
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j + 1 : ℕ) : ℂ) * s)) ∧
    dedekindZetaLogDerivative K s =
      ∑' v : HeightOneSpectrum (𝓞 K), ∑' j : ℕ,
        (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j + 1 : ℕ) : ℂ) * s) := by
  sorry

/-- **`ext:mellin-inversion`**, `07-splitting.tex:130-145`. Mathlib
`mellinInv_mellin_eq` (`Mathlib/Analysis/MellinInversion.lean:92`) is the inversion theorem for a
Mellin-convergent function with an integrable inverse transform. -/
theorem ext_mellin_inversion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    (hf : MellinConvergent f σ) (hFf : VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) : mellinInv σ (mellin f) x = f x := by
  sorry

/-- **`ext:digamma-strip`**, `07-splitting.tex:164-170`. The PNT+ source declaration
`Complex.exists_norm_digamma_le_log`
(`Mathlib/Analysis/SpecialFunctions/Gamma/DigammaSeries.lean:726`) provides logarithmic growth on
closed vertical strips in the right half-plane; this source module is not in the shared prebuilt
set. The recurrence
`Complex.Gamma_add_one` handles the fixed negative-real lines in §7. -/
theorem ext_digamma_strip {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤ C * Real.log (|z.im| + 2) := by
  sorry

/-- **`ext:hadamard-order-one`**, `07-splitting.tex:194-199`. The PNT+ source declaration
`Complex.Hadamard.hadamard_factorization_of_order`
(`Mathlib/Analysis/Complex/HadamardFactorization/Order.lean:176`) supplies the canonical product;
its module is not in the shared prebuilt set. The logarithmic-derivative form below is the part
consumed to choose contour heights. Corrected 2026-10-07 (review lane `rev-7`): growth with `‖s‖ + 1` (the old
bound forced `‖G 0‖ ≤ 1`) and an explicit `Summable` conclusion. -/
theorem ext_hadamard_order_one (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ B : ℂ, ∀ s : ℂ, G s ≠ 0 →
      Summable (fun ρ : ℂ => if G ρ = 0 then
        (analyticOrderNatAt G ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹) else 0) ∧
      deriv G s / G s = B + ∑' ρ : ℂ,
        if G ρ = 0 then
          (analyticOrderNatAt G ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹)
        else 0 := by
  sorry

/-- The multiplicity-weighted number of nontrivial zeros of `ζ_K^♮` in a unit-height window. -/
noncomputable def dedekindZeroWindowCount (K : Type*) [Field K] [NumberField K]
    (T : ℝ) : ℝ :=
  ∑' ρ : ℂ, if ρ ∈ nontrivialZeros K ∧ T ≤ ρ.im ∧ ρ.im < T + 1 then
    (analyticOrderNatAt (dedekindZetaSharp K) ρ : ℝ) else 0

/-- **`ext:dedekind-zero-count`**, `07-splitting.tex:182-192`. The unit-window bound follows
from Jensen's `AnalyticOnNhd.sum_divisor_le` (`Mathlib/Analysis/Complex/JensenFormula.lean:389`),
the D1 functional equation, and D3's uniform bounds on `Re s > 1`; zeros are counted with their
analytic multiplicity. -/
theorem ext_dedekind_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (T : ℝ),
      Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K ∧ T ≤ ρ.im ∧ ρ.im < T + 1 then
        (zeroMultiplicity K ρ : ℝ) else 0) ∧
      dedekindZeroWindowCount K T ≤ C *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K * Real.log (2 + |T|)) := by
  sorry

/-- Auxiliary smooth bump for **`sp:count-from-theta`**, `07-splitting.tex:227-230`. The PNT+ source
`smooth_urysohn_support_Ioo` (`PrimeNumberTheoremAnd/SmoothExistence.lean`) yields a nonnegative
smooth compactly supported function that is at least one on `[1,2]`; this auxiliary input is used
by `sp:count-from-theta`. -/
theorem smooth_bump_exists :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioo 0 3 ∧ (∀ t ∈ Set.Icc 1 2, 1 ≤ f t) ∧
      ∀ t, 0 ≤ f t := by
  sorry

end ArtinPrimitiveRoots.Ext.SplittingInputs

end
