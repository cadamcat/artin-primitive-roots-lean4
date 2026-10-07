import Mathlib

/-!
# Ray class groups (copy of the `ClassFieldTheory` package's public definitions)

Verbatim copy of the ideal-theoretic ray class group of the `ClassFieldTheory` package
(`Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/*.lean`, by N. Yamaguchi,
Apache-2.0), kept with identical names so that this module can be replaced by
`import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup` once that package is
built. Design: `research/design/A2-HeckeAPI.lean` and `A2-DESIGN.md` (Opus A2 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

/-! ## §0 Copy of `ClassFieldTheory.Definitions` (ray class groups) -/

namespace ClassFieldTheory

universe u

/-- (copy of `RayClassModulus.lean:31`) A real infinite place of a number field. -/
abbrev RayClassRealPlace (K : Type u) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsReal}

/-- (copy of `RayClassModulus.lean:37`) A ray modulus: finite prime exponents together with the
real places at which positivity is imposed. -/
structure RayClassModulus (K : Type u) [Field K] [NumberField K] where
  /-- The finite prime-power part. -/
  finitePart : HeightOneSpectrum (𝓞 K) →₀ ℕ
  /-- The selected real places. -/
  infinitePart : Finset (RayClassRealPlace K)

/-- (copy of `RayClassModulus.lean`) Modulus divisibility. -/
instance {K : Type u} [Field K] [NumberField K] : LE (RayClassModulus K) where
  le m n := m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart

/-- (copy of `RayLocalHigherUnitGroup.lean`) Reduction of a local integral unit modulo the
`n`-th power of the maximal ideal. -/
def rayLocalHigherUnitMap {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- (copy of `RayLocalHigherUnitGroup.lean`) The `n`-th higher-unit subgroup at a finite place. -/
def rayLocalHigherUnitGroup {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map (v.adicCompletionIntegers K).units.subtype (rayLocalHigherUnitMap v n).ker

/-- (copy of `IsRayCongruent.lean`) The diagonal embedding of field units into a finite
completion. -/
def finitePlaceUnitEmbedding {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom

/-- (copy of `IsRayCongruent.lean`) `x ≡ 1 mod^× 𝔪` and positivity at the selected real places. -/
def IsRayCongruent {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) (x : Kˣ) : Prop :=
  (∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v (m.finitePart v)) ∧
    (∀ v, v ∈ m.infinitePart → 0 < v.1.embedding_of_isReal v.2 (x : K))

/-- (copy of `NumberFieldFractionalIdealGroup.lean`) Nonzero fractional ideals. -/
abbrev NumberFieldFractionalIdealGroup (K : Type u) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

/-- (copy of `RayClassPrimeToIdeals.lean`) Fractional ideals prime to the finite part. -/
def rayClassPrimeToIdeals {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : Subgroup (NumberFieldFractionalIdealGroup K) where
  carrier := {I | ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0}
  one_mem' v _ := FractionalIdeal.count_one K v
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J),
      hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K v, hI v hv, neg_zero]

/-- (copy of `RayPrincipalIdealSubgroup.lean`) Ray-principal ideals. -/
def rayPrincipalIdealSubgroup {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : Subgroup (NumberFieldFractionalIdealGroup K) :=
  Subgroup.closure {I | ∃ x : Kˣ, IsRayCongruent m x ∧ toPrincipalIdeal (𝓞 K) K x = I}

/-- (copy of `RayPrincipalIdealSubgroup.lean`) Ray-principal ideals inside the prime-to group. -/
def rayPrincipalIdealSubgroupInPrimeTo {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : Subgroup (rayClassPrimeToIdeals m) :=
  Subgroup.comap (rayClassPrimeToIdeals m).subtype (rayPrincipalIdealSubgroup m)

/-- (copy of `RayClassGroup.lean:22`) The ideal-theoretic ray class group `J^𝔪 / P^𝔪`. -/
abbrev RayClassGroup {K : Type u} [Field K] [NumberField K] (m : RayClassModulus K) :=
  rayClassPrimeToIdeals m ⧸ rayPrincipalIdealSubgroupInPrimeTo m

/-- Stand-in for `ClassFieldTheory.rayClassGroup_finite`
(`Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassGroupFinite.lean:26`,
sorry-free in the package).  In this draft only: `sorry`. -/
instance rayClassGroup_finite {K : Type u} [Field K] [NumberField K] (m : RayClassModulus K) :
    Finite (RayClassGroup m) := sorry

end ClassFieldTheory
