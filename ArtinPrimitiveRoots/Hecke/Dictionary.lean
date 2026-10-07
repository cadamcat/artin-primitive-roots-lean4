import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.Dict.LocalCongruence
import ArtinPrimitiveRoots.Hecke.Dict.ConductorSupport
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

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
    modulusNorm m = Ideal.absNorm (modulusIdeal m) := by
  classical
  simp [modulusNorm, modulusIdeal, Finsupp.prod, map_prod, map_pow]

private theorem modulusIdeal_antitone {n m : RayClassModulus F} (h : n ≤ m) :
    modulusIdeal m ≤ modulusIdeal n := by
  classical
  let d := m.finitePart - n.finitePart
  have hd : n.finitePart + d = m.finitePart := by
    ext v
    exact Nat.add_sub_of_le (h.1 v)
  unfold modulusIdeal
  rw [← hd, Finsupp.prod_add_index' (h_zero := by intro v; simp)
    (h_add := by intro v a b; simp [pow_add])]
  exact Ideal.mul_le_left

private theorem modulusNorm_mono {n m : RayClassModulus F} (h : n ≤ m) :
    modulusNorm n ≤ modulusNorm m := by
  have hdiv : modulusNorm n ∣ modulusNorm m := by
    rw [modulusNorm_eq_absNorm, modulusNorm_eq_absNorm]
    exact Ideal.absNorm_dvd_absNorm_of_le (modulusIdeal_antitone h)
  have hmpos : 0 < modulusNorm m := by
    rw [modulusNorm]
    simp only [Finsupp.prod]
    apply Finset.prod_pos
    intro v hv
    exact pow_pos (Nat.zero_lt_of_lt
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)) _
  exact Nat.le_of_dvd hmpos hdiv

private def rayModulusWeight (m : RayClassModulus F) : ℕ :=
  m.finitePart.sum (fun _ e => e) + m.infinitePart.card

private theorem rayModulusWeight_strict_mono {n m : RayClassModulus F} (h : n ≤ m)
    (hne : n ≠ m) : rayModulusWeight n < rayModulusWeight m := by
  classical
  have hcard : n.infinitePart.card ≤ m.infinitePart.card := Finset.card_le_card h.2
  by_cases hfin : n.finitePart = m.finitePart
  · have hinf : n.infinitePart ≠ m.infinitePart := by
      intro hinf
      apply hne
      cases n
      cases m
      simp_all
    have hnot : ¬m.infinitePart ⊆ n.infinitePart := by
      intro hmn
      exact hinf (Finset.Subset.antisymm h.2 hmn)
    have hcard' : n.infinitePart.card < m.infinitePart.card :=
      Finset.card_lt_card ⟨h.2, hnot⟩
    have hsumEq : n.finitePart.sum (fun _ e => e) = m.finitePart.sum (fun _ e => e) :=
      congrArg (fun d : HeightOneSpectrum (𝓞 F) →₀ ℕ => d.sum (fun _ e => e)) hfin
    unfold rayModulusWeight
    omega
  · let d := m.finitePart - n.finitePart
    have hd : n.finitePart + d = m.finitePart := by
      ext v
      exact Nat.add_sub_of_le (h.1 v)
    have hd0 : d ≠ 0 := by
      intro hz
      apply hfin
      calc
        n.finitePart = n.finitePart + d := by simp [hz]
        _ = m.finitePart := hd
    have hdsum : 0 < d.sum (fun _ e => e) := by
      apply Finsupp.sum_pos _ hd0
      intro v hv
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
    have hsum' : n.finitePart.sum (fun _ e => e) + d.sum (fun _ e => e) =
        m.finitePart.sum (fun _ e => e) := by
      rw [← hd, Finsupp.sum_add_index' (h_zero := by intro v; rfl)
        (h_add := by intro v a b; rfl)]
    unfold rayModulusWeight
    omega

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

private theorem normalizedFactor_not_mem_support {m : RayClassModulus F}
    {I : Ideal (𝓞 F)} (hI : IsCoprimeTo m I) {P : Ideal (𝓞 F)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    ∃ v : FinPlace F, v.asIdeal = P ∧ v ∉ m.finitePart.support := by
  rcases hI with ⟨hI0, hcop⟩
  have hP' := (Ideal.mem_normalizedFactors_iff hI0).1 hP
  have hP0 : P ≠ ⊥ := by
    intro hzero
    apply hI0
    exact le_antisymm (hzero ▸ hP'.2) bot_le
  let v : FinPlace F := ⟨P, hP'.1, hP0⟩
  refine ⟨v, rfl, ?_⟩
  intro hv
  have hcountI : FractionalIdeal.count F v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    simpa [idealUnit] using hcop v hv
  rw [FractionalIdeal.count_coe F v hI0,
    Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot] at hcountI
  have hcountZero : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
    exact_mod_cast hcountI
  have hcountpos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I) :=
    Multiset.count_pos.mpr hP
  have hcountpos' : 0 < Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) := by
    simpa [v] using hcountpos
  omega

private theorem charValue_eq_zero_of_mem_support {m : RayClassModulus F}
    (η : RayClassGroup m →* ℂˣ) {v : FinPlace F}
    (hv : v ∈ m.finitePart.support) : charValue η v.asIdeal = 0 := by
  classical
  have hnot : ¬ IsCoprimeTo m v.asIdeal := by
    rintro ⟨hI0, hcop⟩
    have hcount : FractionalIdeal.count F v
        (idealUnit v.asIdeal hI0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 :=
      hcop v hv
    have hcount' : FractionalIdeal.count F v
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 :=
      FractionalIdeal.count_self F v
    have : (0 : ℤ) = 1 := by simpa [idealUnit] using hcount.symm.trans hcount'
    omega
  simp [charValue, hnot]

/-- Ideal values agree on ideals prime to `𝔪` (multiplicativity on both sides).
Consumer: A1 `Bm` / A2 `lem:reflection-theta-representation` (`ϑ(𝔄)` with `ϑ` built from `χ`). -/
theorem idealValue_eq_charValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal)
    (I : Ideal (𝓞 F)) (hI : IsCoprimeTo m I) : χ.idealValue I = charValue η I := by
  classical
  rcases hI with ⟨hI0, hcop⟩
  let fs := UniqueFactorizationMonoid.normalizedFactors I
  have hfactor (P : Ideal (𝓞 F)) (hP : P ∈ fs) :
      (if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1) =
        charValue η P := by
    have hP' := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    obtain ⟨v, hvP, hv⟩ := normalizedFactor_not_mem_support ⟨hI0, hcop⟩ hP
    have hP0 : P ≠ ⊥ := by rw [← hvP]; exact v.ne_bot
    have hval := (hχ v hv).2
    have hpair : P.IsPrime ∧ P ≠ ⊥ := ⟨hP'.1, hP0⟩
    rw [dif_pos hpair]
    have hv' : (⟨P, hpair.1, hpair.2⟩ : FinPlace F) = v :=
      HeightOneSpectrum.ext hvP.symm
    rw [hv']
    simpa [hvP] using hval
  have hcharTop : charValue η (⊤ : Ideal (𝓞 F)) = 1 := by
    classical
    have htop : IsCoprimeTo m (⊤ : Ideal (𝓞 F)) := by
      refine ⟨by simp, ?_⟩
      intro v hv
      simpa [idealUnit] using FractionalIdeal.count_one F v
    have hunitTop : idealUnit (⊤ : Ideal (𝓞 F)) htop.1 = 1 := by
      apply Units.ext
      simp [idealUnit]
    have hclassTop : rayClass m ⊤ htop = 1 := by
      have hsub : (⟨idealUnit ⊤ htop.1, htop.2⟩ : rayClassPrimeToIdeals m) = 1 := by
        apply Subtype.ext
        exact hunitTop
      simp [rayClass, hsub]
    simp [charValue, htop, hclassTop]
  have hprodChar (s : Multiset (Ideal (𝓞 F))) :
      (s.map (charValue η)).prod = charValue η s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp [hcharTop]
    | cons P s ih => simp [Hecke.charValue_mul, ih]
  calc
    χ.idealValue I = (fs.map fun P =>
        if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1).prod := rfl
    _ = (fs.map (charValue η)).prod := by
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun P hP => hfactor P hP)
    _ = charValue η fs.prod := hprodChar fs
    _ = charValue η I := by rw [Ideal.prod_normalizedFactors_eq_self hI0]

open Classical in
/-- The partial L-series as an Euler product in A1's prime values (from
`Hecke.LSeriesRay_eulerProduct`).  Consumer: every place where the paper writes `L^S(·, χ)`
(A2 `prop:euler-product`, `zf:principal-row`, `prop:zero-density`). -/
theorem LSeriesRay_hasProd_primeValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : FinPlace F => if v ∈ m.finitePart.support then (1 : ℂ) else
      (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s) := by
  have heuler := Hecke.LSeriesRay_eulerProduct η hs
  apply heuler.congr_fun
  intro v
  by_cases hv : v ∈ m.finitePart.support
  · simp [hv, charValue_eq_zero_of_mem_support η hv]
  · simp [hv, (hχ v hv).2]

private theorem heckeLoc_eq_of_primeValue (χ χ' : HeckeChar F) (v : FinPlace F)
    (hχ : χ.UnramifiedAt v) (hχ' : χ'.UnramifiedAt v)
    (hprime : χ.primeValue v = χ'.primeValue v) (u : (v.adicCompletion F)ˣ) :
    χ.loc v u = χ'.loc v u := by
  classical
  let π : (v.adicCompletion F)ˣ :=
    toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  have hπ : χ.loc v π = χ'.loc v π := by
    apply Units.ext
    simpa [HeckeChar.primeValue, hχ, hχ', π] using hprime
  have hunif : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (π : v.adicCompletion F) =
          Valued.v (algebraMap F (v.adicCompletion F) (unif v)) := by
            simp [π, toLoc]
      _ = v.valuation F (unif v) := v.valuedAdicCompletion_eq_valuation' (unif v)
      _ = WithZero.exp (-1 : ℤ) := hunif
  have hval : Valued.v (u : v.adicCompletion F) ≠ 0 := by simpa using u.ne_zero
  let k : ℤ := -WithZero.log (Valued.v (u : v.adicCompletion F))
  have hpow : Valued.v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (u : v.adicCompletion F) := by
    calc
      Valued.v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          Valued.v (π : v.adicCompletion F) ^ k := by simp
      _ = WithZero.exp (-k) := by
        rw [hπval]
        simpa [k] using (WithZero.exp_zsmul k (-1 : ℤ)).symm
      _ = Valued.v (u : v.adicCompletion F) := by
        simp [k, WithZero.exp_log hval]
  let u₀ : (v.adicCompletion F)ˣ := u * (π ^ k)⁻¹
  have hu₀val : Valued.v (u₀ : v.adicCompletion F) = 1 := by
    dsimp [u₀]
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hpow]
    exact mul_inv_cancel₀ hval
  have hu₀int : (u₀ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu₀val.le
  have hu₀invint : ((u₀⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      Units.val_inv_eq_inv_val, map_inv₀, hu₀val]
    simp
  have hχ₀ := hχ u₀ hu₀int hu₀invint
  have hχ'₀ := hχ' u₀ hu₀int hu₀invint
  have hπpow : χ.loc v (π ^ k) = χ'.loc v (π ^ k) := by
    simpa only [map_zpow] using congrArg (fun z : ℂˣ => z ^ k) hπ
  have hdecomp : u₀ * π ^ k = u := by
    dsimp [u₀]
    group
  calc
    χ.loc v u = χ.loc v (u₀ * π ^ k) := congrArg (χ.loc v) hdecomp.symm
    _ = χ.loc v u₀ * χ.loc v (π ^ k) := map_mul _ _ _
    _ = 1 * χ'.loc v (π ^ k) := by rw [hχ₀, hπpow]
    _ = χ'.loc v u₀ * χ'.loc v (π ^ k) := by rw [hχ'₀]
    _ = χ'.loc v (u₀ * π ^ k) := (map_mul _ _ _).symm
    _ = χ'.loc v u := congrArg (χ'.loc v) hdecomp

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

private theorem exists_rayCongruent_generator_with_prime_valuation
    {m : RayClassModulus F} (T : Finset (FinPlace F)) (v : FinPlace F)
    (hvT : v ∈ T) (hvM : v ∉ m.finitePart.support) :
    ∃ (a : 𝓞 F) (ha0 : a ≠ 0) (x : Fˣ),
    x = Units.mk0 (algebraMap (𝓞 F) F a)
        (fun hmap => ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap))) ∧
        IsRayCongruent m x ∧
        (∀ q ∈ m.finitePart.support, a ∉ q.asIdeal) ∧
        Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {a})) = 1 ∧
        ∀ w ∈ T, w ≠ v → Multiset.count w.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 0 := by
  classical
  let U := T ∪ m.finitePart.support
  let e (q : FinPlace F) : ℕ :=
    if q = v then 2 else if q ∈ m.finitePart.support then m.finitePart q else 1
  have hvU : v ∈ U := Finset.mem_union_left _ hvT
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    simpa using Ideal.pow_succ_lt_pow v.ne_bot 1
  obtain ⟨r, hrV, hrV2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨x₀, hx₀⟩ := exists_forall_sub_mem_ideal
      (s := U) (fun q : FinPlace F => q.asIdeal) e
      (by intro q hq; exact q.prime)
      (by
        intro q hq q' hq' hne hideal
        exact hne (HeightOneSpectrum.ext hideal))
      (fun q => if q.1 = v then r else 1)
  have hx₀q (q : FinPlace F) (hq : q ∈ U) :
      x₀ - (if q = v then r else 1) ∈ q.asIdeal ^ e q := by
    simpa using hx₀ q hq
  have hx₀v : x₀ - r ∈ v.asIdeal ^ 2 := by
    simpa [e] using hx₀q v hvU
  let z (q : FinPlace F) : 𝓞 F :=
    Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot
      (pow_ne_zero (e q) q.ne_bot))
  have hz (q : FinPlace F) : z q ∈ q.asIdeal ^ e q ∧ z q ≠ 0 :=
    Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
      (pow_ne_zero (e q) q.ne_bot))
  let y : 𝓞 F := ∏ q ∈ U, z q
  have hy0 : y ≠ 0 := by
    dsimp [y]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (hz q).2
  have hyq (q : FinPlace F) (hq : q ∈ U) : y ∈ q.asIdeal ^ e q := by
    dsimp [y]
    rw [← Finset.mul_prod_erase U z hq]
    simpa [mul_comm] using
      (Ideal.mul_mem_left (q.asIdeal ^ e q) (∏ q' ∈ U.erase q, z q') (hz q).1)
  have hyq2 (q : FinPlace F) (hq : q ∈ U) : y ^ 2 ∈ q.asIdeal ^ e q := by
    rw [pow_two]
    exact Ideal.mul_mem_left (q.asIdeal ^ e q) y (hyq q hq)
  let ratio (w : ClassFieldTheory.RayClassRealPlace F) : ℝ :=
    -(w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F x₀)) /
      w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2))
  let B : ℝ := ∑ w ∈ m.infinitePart, max 0 (ratio w)
  obtain ⟨N, hN⟩ := exists_nat_gt B
  let a : 𝓞 F := x₀ + (N : 𝓞 F) * y ^ 2
  have haCongr (q : FinPlace F) (hq : q ∈ U) :
      a - (if q = v then r else 1) ∈ q.asIdeal ^ e q := by
    have h1 := hx₀q q hq
    have h2 : (N : 𝓞 F) * y ^ 2 ∈ q.asIdeal ^ e q :=
      Ideal.mul_mem_left (q.asIdeal ^ e q) (N : 𝓞 F) (hyq2 q hq)
    have hEq : a - (if q = v then r else 1) =
        (x₀ - (if q = v then r else 1)) + (N : 𝓞 F) * y ^ 2 := by
      dsimp [a]
      ring
    rw [hEq]
    exact Ideal.add_mem _ h1 h2
  have haUnit (q : FinPlace F) (hq : q ∈ U) (hqv : q ≠ v) : a ∉ q.asIdeal := by
    have he : 0 < e q := by
      dsimp [e]
      split_ifs with hqeq hqM
      · exact False.elim (hqv hqeq)
      · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqM)
      · omega
    have hsub' : a - 1 ∈ q.asIdeal ^ e q := by
      simpa only [if_neg hqv] using haCongr q hq
    have hsub : a - 1 ∈ q.asIdeal :=
      Ideal.pow_le_self (I := q.asIdeal) (Nat.ne_zero_of_lt he) hsub'
    intro haq
    have hone : (1 : 𝓞 F) ∈ q.asIdeal := by
      have hmem := Ideal.sub_mem (I := q.asIdeal) haq hsub
      simpa [sub_sub_cancel] using hmem
    exact q.isPrime.one_notMem hone
  have haNotV2 : a ∉ v.asIdeal ^ 2 := by
    intro hav2
    have hdiff : a - r ∈ v.asIdeal ^ 2 := by
      simpa [e] using haCongr v hvU
    have : r ∈ v.asIdeal ^ 2 := by
      have hdiff := Ideal.sub_mem (v.asIdeal ^ 2) hav2 hdiff
      simpa [sub_sub_cancel] using hdiff
    exact hrV2 this
  have haV : a ∈ v.asIdeal := by
    have hdiff : a - r ∈ v.asIdeal ^ 2 := by
      simpa [e] using haCongr v hvU
    have hdiff' : a - r ∈ v.asIdeal :=
      Ideal.pow_le_self (I := v.asIdeal) (by decide) hdiff
    have hmem := Ideal.add_mem v.asIdeal hdiff' hrV
    have hEq : a = (a - r) + r := by ring
    rw [hEq]
    exact hmem
  have ha0 : a ≠ 0 := by
    intro hz
    apply haNotV2
    simpa [hz] using (Ideal.zero_mem (v.asIdeal ^ 2))
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F a)
    (fun hmap => ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap)))
  have hpositive (w : ClassFieldTheory.RayClassRealPlace F) (hw : w ∈ m.infinitePart) :
      0 < w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F a) := by
    have hyF0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro hmap
      exact hy0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap))
    have hyEmb0 : w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F y) ≠ 0 :=
      (map_ne_zero (w.1.embedding_of_isReal w.2)
        (a := algebraMap (𝓞 F) F y)).2 hyF0
    have hd : 0 < w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2)) := by
      simpa [map_pow] using sq_pos_of_ne_zero hyEmb0
    have hratio : ratio w < N := by
      have hle : ratio w ≤ B := by
        dsimp [B]
        exact (le_max_right 0 (ratio w)).trans
          (Finset.single_le_sum (fun w' _ => le_max_left 0 (ratio w')) hw)
      exact hle.trans_lt hN
    have hmul := (div_lt_iff₀ hd).mp hratio
    dsimp [a]
    have hEval : w.1.embedding_of_isReal w.2
        (algebraMap (𝓞 F) F (x₀ + (N : 𝓞 F) * y ^ 2)) =
        w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F x₀) +
          (N : ℝ) * w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2)) := by
      simp [map_add, map_mul]
    rw [hEval]
    linarith
  have hRay : IsRayCongruent m x := by
    constructor
    · intro q hq
      have hqU : q ∈ U := Finset.mem_union_right _ hq
      have hqv : q ≠ v := by
        intro heq
        exact hvM (heq ▸ hq)
      have heq : e q = m.finitePart q := by
        dsimp [e]
        rw [if_neg hqv, if_pos hq]
      have hqcong : a - 1 ∈ q.asIdeal ^ (m.finitePart q) := by
        have htmp := haCongr q hqU
        rw [heq] at htmp
        simpa only [if_neg hqv] using htmp
      exact localUnit_mem_rayLocalHigherUnitGroup_of_congruent
        q (m.finitePart q) a x rfl (haUnit q hqU hqv) hqcong
    · intro w hw
      exact hpositive w hw
  have hnotMod : ∀ q ∈ m.finitePart.support, a ∉ q.asIdeal := by
    intro q hq
    have hqU : q ∈ U := Finset.mem_union_right _ hq
    have hqv : q ≠ v := by
      intro heq
      exact hvM (heq ▸ hq)
    exact haUnit q hqU hqv
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    intro hbot
    apply ha0
    exact Ideal.span_singleton_eq_bot.mp hbot
  have hcountV : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 1 := by
    apply Ideal.count_normalizedFactors_eq (n := 1)
    · simpa using (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haV))
    · intro hle
      exact haNotV2 (hle (Ideal.subset_span (by simp)))
  have hcountOther (q : FinPlace F) (hq : q ∈ T) (hqv : q ≠ v) :
      Multiset.count q.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    have hfac := (Ideal.mem_normalizedFactors_iff hspan0).1 hmem
    have haq : a ∈ q.asIdeal := hfac.2 (Ideal.subset_span (by simp))
    exact haUnit q (Finset.mem_union_left _ hq) hqv haq
  exact ⟨a, ha0, x, ⟨rfl, ⟨hRay, ⟨hnotMod, ⟨hcountV, hcountOther⟩⟩⟩⟩⟩

private def primeToRayIdeal (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) : rayClassPrimeToIdeals m :=
  ⟨idealUnit v.asIdeal v.ne_bot, by
    intro w hw
    have hne : w ≠ v := by
      intro hEq
      exact hv (hEq ▸ hw)
    change FractionalIdeal.count F w
      (idealUnit v.asIdeal v.ne_bot : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
    simpa [idealUnit] using
      (FractionalIdeal.count_maximal_coprime F w hne.symm)⟩

private def rayIdealExponent {m : RayClassModulus F}
    (I : rayClassPrimeToIdeals m) (v : FinPlace F) : ℤ :=
  FractionalIdeal.count F v
    ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)

open Classical in
private theorem rayIdealFactorization {m : RayClassModulus F}
    (I : rayClassPrimeToIdeals m) :
    I = ∏ᶠ v : FinPlace F,
      (if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1) ^
        rayIdealExponent I v := by
  classical
  let p (v : FinPlace F) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1
  have hexpFinite : ∀ᶠ v : FinPlace F in Filter.cofinite, rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hfinite : Function.HasFiniteMulSupport
      (fun v : FinPlace F => p v ^ rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : FinPlace F in Filter.cofinite,
        p v ^ rayIdealExponent I v = 1 := by
      filter_upwards [hexpFinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  let coeHom : rayClassPrimeToIdeals m →* FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    (Units.coeHom (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).comp
      (rayClassPrimeToIdeals m).subtype
  have hmap : coeHom (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) =
      ∏ᶠ v : FinPlace F, coeHom (p v) ^ rayIdealExponent I v := by
    simpa only [map_zpow] using MonoidHom.map_finprod coeHom hfinite
  have hterm (v : FinPlace F) :
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ rayIdealExponent I v =
        coeHom (p v) ^ rayIdealExponent I v := by
    by_cases hv : v ∉ m.finitePart.support
    · have hv0 : m.finitePart v = 0 := by
        by_contra hne
        exact hv (Finsupp.mem_support_iff.mpr hne)
      simp [p, hv0, coeHom, primeToRayIdeal, idealUnit]
    · have hv' : v ∈ m.finitePart.support := by simpa using hv
      have hz : rayIdealExponent I v = 0 := I.property v hv'
      simp [p, hv, coeHom, hz]
  apply Subtype.ext
  apply Units.ext
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization'
    (R := 𝓞 F) (K := F) (Units.ne_zero (I : NumberFieldFractionalIdealGroup F))
  calc
    ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ v : FinPlace F,
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
            rayIdealExponent I v := hfac.symm
    _ = ∏ᶠ v : FinPlace F, coeHom (p v) ^ rayIdealExponent I v := by
      apply finprod_congr
      exact hterm
    _ = coeHom (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) := hmap.symm
    _ = (((∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v : rayClassPrimeToIdeals m) :
        NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := rfl

private theorem rayIdealHom_ext {m : RayClassModulus F}
    (f g : rayClassPrimeToIdeals m →* ℂˣ)
    (hprime : ∀ v : FinPlace F, ∀ hv : v ∉ m.finitePart.support,
      f (primeToRayIdeal m v hv) = g (primeToRayIdeal m v hv)) : f = g := by
  classical
  apply MonoidHom.ext
  intro I
  let p (v : FinPlace F) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1
  have hfinite : ∀ᶠ v : FinPlace F in Filter.cofinite, rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hfinite' : Function.HasFiniteMulSupport
      (fun v : FinPlace F => p v ^ rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : FinPlace F in Filter.cofinite,
        p v ^ rayIdealExponent I v = 1 := by
      filter_upwards [hfinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  calc
    f I = f (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) :=
      congrArg f (rayIdealFactorization I)
    _ = ∏ᶠ v : FinPlace F, f (p v) ^ rayIdealExponent I v := by
      simpa only [map_zpow] using MonoidHom.map_finprod f hfinite'
    _ = ∏ᶠ v : FinPlace F, g (p v) ^ rayIdealExponent I v := by
      apply finprod_congr
      intro v
      by_cases hv : v ∉ m.finitePart.support
      · have hp : p v = primeToRayIdeal m v hv := by
          simpa only [p, dite_eq_left hv]
        rw [hp, hprime v hv]
      · have hv' : v ∈ m.finitePart.support := by simpa using hv
        have hz : rayIdealExponent I v = 0 := I.property v hv'
        have hp : p v = 1 := by
          simpa only [p, dite_eq_right hv]
        rw [hp, hz]
        simp
    _ = g (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) := by
      symm
      simpa only [map_zpow] using MonoidHom.map_finprod g hfinite'
    _ = g I := congrArg g (rayIdealFactorization I).symm

/-- **DICT-4.** Ray-class characters agreeing at all primes outside a finite set `T` are equal
(every ray class contains an ideal prime to `T`).  Consumer: A2 `lem:conductor-sieve`
(distinctness of the family on the ray-class side), `zf:row-conductor-family`. -/
theorem rayClassChar_eq_of_charValue {m : RayClassModulus F} (η η' : RayClassGroup m →* ℂˣ)
    (T : Finset (FinPlace F))
    (h : ∀ v : FinPlace F, v ∉ T → charValue η v.asIdeal = charValue η' v.asIdeal) :
    η = η' := by
  classical
  let qmap : rayClassPrimeToIdeals m →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  let f : rayClassPrimeToIdeals m →* ℂˣ := η.comp qmap
  let g : rayClassPrimeToIdeals m →* ℂˣ := η'.comp qmap
  let ρ : rayClassPrimeToIdeals m →* ℂˣ := f * g⁻¹
  have hDirect (v : FinPlace F) (hvM : v ∉ m.finitePart.support)
      (hvT : v ∉ T) : ρ (primeToRayIdeal m v hvM) = 1 := by
    let hcop : IsCoprimeTo m v.asIdeal := by
      refine ⟨v.ne_bot, ?_⟩
      intro w hw
      exact (primeToRayIdeal m v hvM).property w hw
    have hclass : rayClass m v.asIdeal hcop = QuotientGroup.mk
        (primeToRayIdeal m v hvM) := by
      rfl
    have hchar : charValue η v.asIdeal = ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hchar' : charValue η' v.asIdeal = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hvalue : η (rayClass m v.asIdeal hcop) = η' (rayClass m v.asIdeal hcop) := by
      apply Units.ext
      calc
        ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) = charValue η v.asIdeal := hchar.symm
        _ = charValue η' v.asIdeal := h v hvT
        _ = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := hchar'
    have hfg : f (primeToRayIdeal m v hvM) = g (primeToRayIdeal m v hvM) := by
      change η (QuotientGroup.mk (primeToRayIdeal m v hvM)) =
        η' (QuotientGroup.mk (primeToRayIdeal m v hvM))
      rw [← hclass]
      exact hvalue
    simp [ρ, hfg]
  have hAtExcluded (v : FinPlace F) (hvM : v ∉ m.finitePart.support)
      (hvT : v ∈ T) : ρ (primeToRayIdeal m v hvM) = 1 := by
    obtain ⟨a, ha0, x, hx, hRay, hnotMod, hcountV, hcountOther⟩ :=
      exists_rayCongruent_generator_with_prime_valuation T v hvT hvM
    let I : Ideal (𝓞 F) := Ideal.span {a}
    have hI0 : I ≠ ⊥ := by
      intro hbot
      apply ha0
      exact Ideal.span_singleton_eq_bot.mp (by simpa [I] using hbot)
    have hIcop : IsCoprimeTo m I := by
      refine ⟨hI0, ?_⟩
      intro q hqM
      have hcountNat : Multiset.count q.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmem
        have hfac := (Ideal.mem_normalizedFactors_iff hI0).1 (by simpa [I] using hmem)
        exact hnotMod q hqM (hfac.2 (Ideal.subset_span (by simp)))
      have hcount : FractionalIdeal.count F q
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        rw [FractionalIdeal.count_coe F q hI0,
          Ideal.count_associates_factors_eq hI0 q.isPrime q.ne_bot]
        exact_mod_cast hcountNat
      change FractionalIdeal.count F q
        (idealUnit I hI0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
      simpa [idealUnit] using hcount
    let P : rayClassPrimeToIdeals m := ⟨idealUnit I hI0, hIcop.2⟩
    have hprincipalEq : toPrincipalIdeal (𝓞 F) F x = idealUnit I hI0 := by
      apply Units.ext
      rw [coe_toPrincipalIdeal, hx]
      simp only [Units.val_mk0]
      dsimp [idealUnit, I]
      exact (FractionalIdeal.coeIdeal_span_singleton
        (R := 𝓞 F) (S := nonZeroDivisors (𝓞 F)) (P := F) a).symm
    have htoMem : toPrincipalIdeal (𝓞 F) F x ∈ rayClassPrimeToIdeals m := by
      rw [hprincipalEq]
      exact P.property
    let P' : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 F) F x, htoMem⟩
    have hP' : P' ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
      Subgroup.subset_closure ⟨x, hRay, rfl⟩
    have hP'P : P' = P := by
      apply Subtype.ext
      exact hprincipalEq
    have hP : P ∈ rayPrincipalIdealSubgroupInPrimeTo m := by
      simpa [hP'P] using hP'
    have hρP : ρ P = 1 := by
      have hclassOne : qmap P = 1 := (QuotientGroup.eq_one_iff _).mpr hP
      simp [ρ, f, g, hclassOne]
    have hexp (q : FinPlace F) : rayIdealExponent P q =
        (Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
      unfold rayIdealExponent
      have hcoe : ((P : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        simp [P, idealUnit]
      rw [hcoe, FractionalIdeal.count_coe F q hI0,
        Ideal.count_associates_factors_eq hI0 q.isPrime q.ne_bot]
    have hexpV : rayIdealExponent P v = 1 := by
      rw [hexp]
      exact_mod_cast hcountV
    have hexpOther (q : FinPlace F) (hq : q ∈ T) (hqv : q ≠ v) :
        rayIdealExponent P q = 0 := by
      rw [hexp]
      exact_mod_cast hcountOther q hq hqv
    let pfun (q : FinPlace F) : rayClassPrimeToIdeals m :=
      if hq : q ∉ m.finitePart.support then primeToRayIdeal m q hq else 1
    have hfinite : ∀ᶠ q : FinPlace F in Filter.cofinite, rayIdealExponent P q = 0 := by
      simpa [rayIdealExponent] using
        (FractionalIdeal.finite_factors
          ((P : NumberFieldFractionalIdealGroup F) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    have hmulSupport : Function.HasFiniteMulSupport
        (fun q : FinPlace F => pfun q ^ rayIdealExponent P q) := by
      have hEv : ∀ᶠ q : FinPlace F in Filter.cofinite,
          pfun q ^ rayIdealExponent P q = 1 := by
        filter_upwards [hfinite] with q hq
        simp [hq]
      exact Filter.eventually_cofinite.mp hEv
    have hρfactor : ρ P = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := by
      calc
        ρ P = ρ (∏ᶠ q : FinPlace F, pfun q ^ rayIdealExponent P q) :=
          congrArg ρ (rayIdealFactorization P)
        _ = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := by
          simpa only [map_zpow] using MonoidHom.map_finprod ρ hmulSupport
    have hterm (q : FinPlace F) (hqv : q ≠ v) :
        ρ (pfun q) ^ rayIdealExponent P q = 1 := by
      by_cases hqM : q ∈ m.finitePart.support
      · have hfalse : ¬ q ∉ m.finitePart.support := by simpa using hqM
        simp only [pfun, dite_eq_right hfalse]
        simp
      · by_cases hqT : q ∈ T
        · have hzero := hexpOther q hqT hqv
          simp only [pfun, dite_eq_left hqM]
          simp [hzero]
        · have hprimeq := hDirect q hqM hqT
          simp only [pfun, dite_eq_left hqM]
          simp [hprimeq]
    have hρv : ρ (primeToRayIdeal m v hvM) = 1 := by
      have hpfunV : pfun v = primeToRayIdeal m v hvM := by
        dsimp [pfun]
        rw [dite_eq_left hvM]
      have hprod : (∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q) =
          ρ (pfun v) ^ rayIdealExponent P v :=
        finprod_eq_single _ v (fun q hqv => hterm q hqv)
      have hone : (1 : ℂˣ) = ρ (pfun v) := by
        calc
          1 = ρ P := hρP.symm
          _ = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := hρfactor
          _ = ρ (pfun v) ^ rayIdealExponent P v := hprod
          _ = ρ (pfun v) := by rw [hexpV]; simp
      simpa [hpfunV] using hone.symm
    exact hρv
  have hprime : ∀ v : FinPlace F, ∀ hv : v ∉ m.finitePart.support,
      f (primeToRayIdeal m v hv) = g (primeToRayIdeal m v hv) := by
    intro v hv
    have hrho : ρ (primeToRayIdeal m v hv) = 1 := by
      by_cases hvT : v ∈ T
      · exact hAtExcluded v hv hvT
      · exact hDirect v hv hvT
    have hdiv : f (primeToRayIdeal m v hv) *
        (g (primeToRayIdeal m v hv))⁻¹ = 1 := by
      simpa [ρ] using hrho
    calc
      f (primeToRayIdeal m v hv) =
          f (primeToRayIdeal m v hv) * (g (primeToRayIdeal m v hv))⁻¹ *
            g (primeToRayIdeal m v hv) := by simp [mul_assoc]
      _ = 1 * g (primeToRayIdeal m v hv) := by rw [hdiv]
      _ = g (primeToRayIdeal m v hv) := by simp
  have hfg : f = g := rayIdealHom_ext f g hprime
  apply MonoidHom.ext
  intro c
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) c
  exact DFunLike.congr_fun hfg I

/-- **DICT-P.** Every ray-class character is induced by a primitive one, at a modulus of norm
`conductorNorm η`.  Consumers: A2 `prop:zero-density` (the detector runs on the primitive
`L_F(s, ω_u)`), `lem:conductor-sieve` (family of distinct primitive characters with
`N𝔣 ≤ C₀U`; primitivity gives a primitive residue character and `|τ| = √N𝔮`). -/
theorem exists_primitive {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    ∃ (f : RayClassModulus F) (η' : RayClassGroup f →* ℂˣ),
      f ≤ m ∧ modulusNorm f = conductorNorm η ∧
      (∀ v : FinPlace F, v ∉ m.finitePart.support →
        charValue η v.asIdeal = charValue η' v.asIdeal) ∧
      ∀ n : RayClassModulus F, FactorsThrough η' n → n = f := by
  classical
  let normSet : Set ℕ :=
    {N | ∃ n : RayClassModulus F, FactorsThrough η n ∧ modulusNorm n = N}
  have hnormSet : normSet.Nonempty := by
    exact ⟨modulusNorm m, m, factorsThrough_self η, rfl⟩
  have hnormMem : conductorNorm η ∈ normSet := by
    simpa [conductorNorm, normSet] using Nat.sInf_mem hnormSet
  obtain ⟨f₀, hf₀, hf₀norm⟩ := hnormMem
  let weightSet : Set ℕ :=
    {w | ∃ n : RayClassModulus F, FactorsThrough η n ∧
      modulusNorm n = conductorNorm η ∧ rayModulusWeight n = w}
  have hweightSet : weightSet.Nonempty := by
    exact ⟨rayModulusWeight f₀, f₀, hf₀, hf₀norm, rfl⟩
  have hweightMem := Nat.sInf_mem hweightSet
  obtain ⟨f, hf, hfnorm, hfweight⟩ := hweightMem
  obtain ⟨η', hηeq⟩ := exists_rayClassChar_of_factorsThrough hf.1 η hf
  have hcop (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo m q.asIdeal := by
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal m q hq).property w hw
  have hcopF (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo f q.asIdeal := by
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal f q hqF).property w hw
  have hprimeClass (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      η (rayClass m q.asIdeal (hcop q hq)) =
        η' (rayClass f q.asIdeal (hcopF q hq)) := by
    let Pm := primeToRayIdeal m q hq
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    let Pf := primeToRayIdeal f q hqF
    have hclassM : rayClass m q.asIdeal (hcop q hq) = QuotientGroup.mk Pm := rfl
    have hclassF : rayClass f q.asIdeal (hcopF q hq) = QuotientGroup.mk Pf := rfl
    have hmap : rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
      rw [rayClassMap_apply_mk]
      congr 1
    have hηprime := DFunLike.congr_fun hηeq (QuotientGroup.mk Pm)
    simpa [MonoidHom.comp_apply, hclassM, hclassF, hmap] using hηprime
  refine ⟨f, η', hf.1, hfnorm, ?_, ?_⟩
  · intro q hq
    have hvalue := hprimeClass q hq
    simp only [charValue, dif_pos (hcop q hq), dif_pos (hcopF q hq)]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hvalue
  · intro n hn
    have hηFactorsN : FactorsThrough η n := by
      refine ⟨⟨le_trans hn.1.1 hf.1.1, Finset.Subset.trans hn.1.2 hf.1.2⟩, ?_⟩
      intro x hx hI
      have hIF : toPrincipalIdeal (𝓞 F) F x ∈ rayClassPrimeToIdeals f := by
        intro q hq
        exact hI q (Finsupp.support_mono hf.1.1 hq)
      let Pm : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 F) F x, hI⟩
      let Pf : rayClassPrimeToIdeals f := ⟨toPrincipalIdeal (𝓞 F) F x, hIF⟩
      have hmap : rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
        rw [rayClassMap_apply_mk]
        congr 1
      have hηprime := DFunLike.congr_fun hηeq (QuotientGroup.mk Pm)
      have hηvalue : η (QuotientGroup.mk Pm) = η' (QuotientGroup.mk Pf) := by
        calc
          η (QuotientGroup.mk Pm) =
              η' (rayClassMap hf.1 (QuotientGroup.mk Pm)) := by
            simpa [MonoidHom.comp_apply] using hηprime
          _ = η' (QuotientGroup.mk Pf) := congrArg η' hmap
      change η (QuotientGroup.mk Pm) = 1
      rw [hηvalue]
      exact hn.2 x hx hIF
    have hnormLower : conductorNorm η ≤ modulusNorm n :=
      Nat.sInf_le ⟨n, hηFactorsN, rfl⟩
    have hnormUpper : modulusNorm n ≤ modulusNorm f := modulusNorm_mono hn.1
    have hnormEq : modulusNorm n = conductorNorm η := by
      rw [hfnorm] at hnormUpper
      exact le_antisymm hnormUpper hnormLower
    have hnWeight : rayModulusWeight n ∈ weightSet :=
      ⟨n, hηFactorsN, hnormEq, rfl⟩
    have hweightLower : rayModulusWeight f ≤ rayModulusWeight n := by
      rw [hfweight]
      exact Nat.sInf_le hnWeight
    by_contra hne
    have hweightStrict := rayModulusWeight_strict_mono hn.1 hne
    omega

end ArtinPrimitiveRoots.Dictionary
