import ArtinPrimitiveRoots.A1.Field

/-!
# Arithmetic preparation for the canonical narrow family

The Euler cutoff in `SData.nonempty` can absorb any prescribed finite set of
places. This gives an enlargement with a PID ring of S-integers without
requiring a separate localization argument.
-/

/-
# NQ0 proof plan

The plan is to prove the following helpers in dependency order. The signatures use this common context:

```lean
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory ArtinPrimitiveRoots.A1
namespace ArtinPrimitiveRoots.A2
variable {K : Type} [Field K] [NumberField K]
variable {CE : ℕ} {condη : Ideal (𝓞 K)}
```

1. `Foundation.lean`: absorb the supplied set in A1's Euler cutoff; obtain a
   PID S-integer ring and all the fixed bad primes.

```lean
theorem qs_nq0_sdata_enlargement (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (CE : ℕ) (Sd : SData K CE (⊤ : Ideal (𝓞 K))), S ⊆ Sd.Sf
```

2. `Generators.lean`: fix the field embedding and allowed generators using
   the frozen A1 producers.

```lean
theorem qs_nq0_field_data (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12) :
    Nonempty (FieldData K)

theorem qs_nq0_allowed_generators (Sd : SData K CE condη)
    (H : HilbertData K) (Bd : BData Sd H) :
    ∃ a : Ideal (𝓞 K) → Kˣ, ∀ I, Sd.IsExterior I →
      Sd.IsGen (a I : K) I ∧ Bd.Allowed (a I)
```

3. `LocalCharacter.lean`: realize the cubed Hilbert character as an actual
   continuous idelic Hecke character. This supplies the local information
   that `A1.kummer_exists` alone does not expose.

```lean
theorem qs_nq0_quadratic_local_realization (D : FieldData K)
    (H : HilbertData K) (a : Ideal (𝓞 K) → Kˣ) :
    ∃ χ : Ideal (𝓞 K) → HeckeChar K,
      (∀ I, χ I ^ 2 = 1) ∧
      (∀ I (w : InfinitePlace K) (u : w.Completionˣ), (χ I).locInf w u = 1) ∧
      (∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
        (((χ I).loc v u : ℂˣ) : ℂ) =
          D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3)
```

4. `Conductors.lean`: bound the fixed local square conductor at S; use the
   isotropic complement for reciprocity and the equal-ray-class quotient.
   Exterior conductor exponents must be exactly 0 or 1.

```lean
theorem qs_nq0_conductor_family (D : FieldData K) (Sd : SData K CE condη)
    (H : HilbertData K) (Bd : BData Sd H) (a : Ideal (𝓞 K) → Kˣ)
    (ha : ∀ I, Sd.IsExterior I → Sd.IsGen (a I : K) I ∧ Bd.Allowed (a I))
    (χ : Ideal (𝓞 K) → HeckeChar K)
    (hχ : ∀ I, χ I ^ 2 = 1)
    (h∞ : ∀ I (w : InfinitePlace K) (u : w.Completionˣ), (χ I).locInf w u = 1)
    (hloc : ∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
      (((χ I).loc v u : ℂˣ) : ℂ) =
        D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3) :
    ∃ (m : RayClassModulus K) (qS : Ideal (𝓞 K)) (F : QSFamily m qS),
      qS ≠ ⊥ ∧ m.finitePart.support = Sd.Sf ∧
      (∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf) ∧
      (∀ g h, F.rayFactor g h = 1) ∧
      (∀ I, Sd.IsExterior I → F.character I = χ I)
```

5. `Admissibility.lean`: prime-factor algebra transports the S-support
   conditions to every finite squarefree exterior support. Then assemble
   the frozen `qs_canonical_family_NQ0` after the integral-symbol helper.

```lean
theorem qs_nq0_support_admissible (Sd : SData K CE condη)
    (m : RayClassModulus K) (hm : m.finitePart.support = Sd.Sf)
    (qS : Ideal (𝓞 K)) (hqS : qS ≠ ⊥)
    (hsupport : ∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf)
    (T : Finset (FinPlace K)) (hT : Disjoint T Sd.Sf) :
    Sd.IsExterior (qsIdealOf T) ∧ QSAdm m qS (qsIdealOf T)
```

6. `IntegralSymbols.lean`: clear S-supported denominators by an even power,
   prove the masked quadratic-symbol dictionary also at overlapping primes,
   and multiply over the finite support.

```lean
theorem qs_nq0_integral_symbol_representatives (D : FieldData K)
    (Sd : SData K CE condη) (H : HilbertData K)
    (a : Ideal (𝓞 K) → Kˣ)
    (ha : ∀ I, Sd.IsExterior I → Sd.IsGen (a I : K) I)
    (χ : Ideal (𝓞 K) → HeckeChar K)
    (hloc : ∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
      (((χ I).loc v u : ℂˣ) : ℂ) =
        D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3) :
    ∃ gen₀ : Finset (FinPlace K) → 𝓞 K,
      (∀ T, Disjoint T Sd.Sf → qsIsExteriorGenerator Sd.Sf T (gen₀ T)) ∧
      (∀ T D', Disjoint T Sd.Sf → Disjoint D' Sd.Sf →
        (χ (qsIdealOf T)).idealValue (qsIdealOf D') =
          (qsQuadSymbol D' (gen₀ T) : ℂ))
```

-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

set_option maxHeartbeats 1000000 in
/-- Enlarge any finite set of places to A1 data, using the trivial target conductor. -/
theorem qs_nq0_sdata_enlargement (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (CE : ℕ) (Sd : ArtinPrimitiveRoots.A1.SData K CE (⊤ : Ideal (𝓞 K))),
      S ⊆ Sd.Sf := by
  classical
  let CE : ℕ := S.sup (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal)
  have hη : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  obtain ⟨Sd⟩ := ArtinPrimitiveRoots.A1.SData.nonempty (F := K) CE ⊤ hη
  refine ⟨CE, Sd, ?_⟩
  intro v hv
  apply Sd.euler_mem v
  exact Finset.le_sup (f := fun w : HeightOneSpectrum (𝓞 K) => Ideal.absNorm w.asIdeal) hv

end ArtinPrimitiveRoots.A2
