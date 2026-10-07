import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.A1.Characters

/-!
# Hecke package: dictionary between ray-class characters and A1's idelic characters

Frozen interface (owned by the Hecke package). Design: `research/design/A2-Dictionary.lean`, `A2-ALIGN.md` §2
(Opus A2 sub-agent, 2026-10-07); `ConductorDvd'` of the draft is A1's corrected `HeckeChar.ConductorDvd`.

Statements against the two frozen interfaces, imported directly from the built repo modules
`ArtinPrimitiveRoots.Hecke.Defs` and `ArtinPrimitiveRoots.A1.Characters` (both Mathlib-only).
Design and consumers: `A2-ALIGN.md` §2.  Proof sources (not compiled here): TauCeti
`HeckeCharacter.ofRayClassCharacter` (NumberField/Global/HeckeCharacter/Basic.lean:97),
`isFiniteOrder_iff_exists_rayClassCharacter` (HeckeCharacter/FiniteOrder.lean:80),
`RayClassCharacter.conductor`, `primitiveCharacter` (RayClass/Character/Conductor.lean:72,99),
`rayClassQuotient_mk_of_mem` (Ideles/Ray/ClassQuotient.lean:212); ClassFieldTheory
`rayClassGroup_hom_ext_finitePrime` (Theorems/ConductorsAndRayClassFields/
RayClassGroupHomExtFinitePrime.lean); plus an isomorphism between ClassFieldTheory's and TauCeti's
ideal-theoretic ray class groups (new).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Hecke ClassFieldTheory

variable {F : Type} [Field F] [NumberField F]

/-! ## §0 Moduli as ideals; small package lemmas -/

/-- The ideal `∏_v 𝔭_v^{e_v}` of the finite part of a ray modulus. -/
def modulusIdeal (m : RayClassModulus F) : Ideal (𝓞 F) :=
  m.finitePart.prod (fun v e => v.asIdeal ^ e)

/-- `N𝔪 = N(modulusIdeal 𝔪)`. Consumer: A2 `zf:convexity` (with `kummer_conductor`). -/
theorem modulusNorm_eq_absNorm (m : RayClassModulus F) :
    modulusNorm m = Ideal.absNorm (modulusIdeal m) := sorry

/-- A character factors through its own modulus. -/
theorem factorsThrough_self {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    FactorsThrough η m := by
  refine ⟨⟨le_refl _, Finset.Subset.refl _⟩, ?_⟩
  intro x hx h
  have hmem : (⟨toPrincipalIdeal (𝓞 F) F x, h⟩ : rayClassPrimeToIdeals m) ∈
      rayPrincipalIdealSubgroupInPrimeTo m :=
    Subgroup.subset_closure ⟨x, hx, rfl⟩
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]

/-- `conductorNorm η ≤ N𝔪`.  Consumer: A2 `zf:convexity` (H3 applied with the modulus bound of
`kummer_conductor`), `zf:row-conductor-family`. -/
theorem conductorNorm_le_modulusNorm {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    conductorNorm η ≤ modulusNorm m :=
  Nat.sInf_le ⟨m, factorsThrough_self η, rfl⟩

/-! ## §1 Ray class → idelic -/

/-- **DICT-1.** A ray-class character gives a finite-order idelic character with the same values at
the primes prime to `𝔪`, unramified there, and with conductor dividing `modulusIdeal 𝔪`.
Its local components at `S` (A1's `SData.LS`, `vartheta`) are the `S`-adic component of `η`.
Consumers: `HeckeBoundary.a2_zero_free_every_continuation` (proof: builds A1's `condη`, `SData`,
`ϑ = Λ⁻¹G⁻¹χ`, `Bm`); A1 `vartheta_S`; A2 `def:rf-S-character`, `prop:euler-product`,
`po:H-product`. -/
theorem exists_heckeChar_of_rayClass (m : RayClassModulus F) (η : RayClassGroup m →* ℂˣ) :
    ∃ χ : HeckeChar F, IsOfFinOrder χ ∧ χ.ConductorDvd (modulusIdeal m) ∧
      ∀ v : FinPlace F, v ∉ m.finitePart.support →
        χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal := sorry

/-- Ideal values agree on ideals prime to `𝔪` (multiplicativity on both sides).
Consumer: A1 `Bm` / A2 `lem:reflection-theta-representation` (`ϑ(𝔄)` with `ϑ` built from `χ`). -/
theorem idealValue_eq_charValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal)
    (I : Ideal (𝓞 F)) (hI : IsCoprimeTo m I) : χ.idealValue I = charValue η I := sorry

open Classical in
/-- The partial L-series as an Euler product in A1's prime values (from
`Hecke.LSeriesRay_eulerProduct`).  Consumer: every place where the paper writes `L^S(·, χ)`
(A2 `prop:euler-product`, `zf:principal-row`, `prop:zero-density`). -/
theorem LSeriesRay_hasProd_primeValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : FinPlace F => if v ∈ m.finitePart.support then (1 : ℂ) else
      (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s) := sorry

/-! ## §2 Idelic → ray class -/

open Classical in
/-- **DICT-2.** A finite-order idelic character with conductor dividing `𝔫 ≠ 0` is a character
of `Cl_𝔪(F)` for the modulus `𝔪` with finite part `𝔫` and all real places (for totally complex `F`
there are none), with the same prime values off `𝔫`.
Consumers: A2 `zf:row-conductor-family`, `zf:convexity`, `zf:small-rows`,
`zf:intermediate-rows` (numerator `L^S(w, χ_•(u))` from A1 `kummer_exists`), `prop:zero-density`
(`ω_u = η κ_u⁻¹`). -/
theorem exists_rayClass_of_heckeChar (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hc : χ.ConductorDvd n) :
    ∃ (m : RayClassModulus F) (ψ : RayClassGroup m →* ℂˣ),
      modulusIdeal m = n ∧ m.infinitePart = Finset.univ ∧
      ∀ v : FinPlace F, v ∉ m.finitePart.support → charValue ψ v.asIdeal = χ.primeValue v :=
  sorry

/-! ## §3 Uniqueness and primitive characters -/

/-- **DICT-3.** Idelic characters agreeing (and unramified) at all primes outside a finite set are
equal (weak approximation and continuity).  Consumer: A2 `zf:row-conductor-family` (the `ω_u` are
pairwise distinct, transported from A1 `kummer_eq_iff`), `lem:conductor-sieve`. -/
theorem heckeChar_eq_of_primeValue (χ χ' : HeckeChar F) (T : Finset (FinPlace F))
    (h : ∀ v : FinPlace F, v ∉ T →
      χ.UnramifiedAt v ∧ χ'.UnramifiedAt v ∧ χ.primeValue v = χ'.primeValue v) :
    χ = χ' := sorry

/-- **DICT-4.** Ray-class characters agreeing at all primes outside a finite set `T` are equal
(every ray class contains an ideal prime to `T`).  Consumer: A2 `lem:conductor-sieve`
(distinctness of the family on the ray-class side), `zf:row-conductor-family`. -/
theorem rayClassChar_eq_of_charValue {m : RayClassModulus F} (η η' : RayClassGroup m →* ℂˣ)
    (T : Finset (FinPlace F))
    (h : ∀ v : FinPlace F, v ∉ T → charValue η v.asIdeal = charValue η' v.asIdeal) :
    η = η' := sorry

/-- **DICT-P.** Every ray-class character is induced by a primitive one, at a modulus of norm
`conductorNorm η`.  Consumers: A2 `prop:zero-density` (the detector runs on the primitive
`L_F(s, ω_u)`), `lem:conductor-sieve` (family of distinct primitive characters with
`N𝔣 ≤ C₀U`; primitivity gives a primitive residue character and `|τ| = √N𝔮`). -/
theorem exists_primitive {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    ∃ (f : RayClassModulus F) (η' : RayClassGroup f →* ℂˣ),
      f ≤ m ∧ modulusNorm f = conductorNorm η ∧
      (∀ v : FinPlace F, v ∉ m.finitePart.support →
        charValue η v.asIdeal = charValue η' v.asIdeal) ∧
      ∀ n : RayClassModulus F, FactorsThrough η' n → n = f := sorry

end ArtinPrimitiveRoots.Dictionary
