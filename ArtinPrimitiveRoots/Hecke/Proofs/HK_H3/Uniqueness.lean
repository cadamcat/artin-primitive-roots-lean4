import ArtinPrimitiveRoots.Hecke.Proofs.HK_H3.Descent
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs

/-! Support-free uniqueness and nontriviality of the primitive inducer,
at `K : Type*`.

The frozen `rayClassChar_eq_of_charValue` / `primitive_inducer_ne_one` are at
`F : Type` (`Type 0`). Here only everywhere-agreement uniqueness is needed
(the inducer agrees with `η` off `supp m` and both vanish on it), so the
finite-set CRT step of DICT-4 is unnecessary: `hk_rayIdealHom_ext` kills every
prime-to ideal directly. -/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory ArtinPrimitiveRoots.Hecke

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.hk_misc_muse

open ArtinPrimitiveRoots.Dictionary

variable {K : Type*} [Field K] [NumberField K]

def hk_rayIdealExponent {m : RayClassModulus K}
    (I : rayClassPrimeToIdeals m) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v
    ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)

open Classical in
theorem hk_rayIdealFactorization {m : RayClassModulus K}
    (I : rayClassPrimeToIdeals m) :
    I = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (if hv : v ∉ m.finitePart.support then hk_primeToRayIdeal m v hv else 1) ^
        hk_rayIdealExponent I v := by
  classical
  let p (v : HeightOneSpectrum (𝓞 K)) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then hk_primeToRayIdeal m v hv else 1
  have hexpFinite : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      hk_rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hfinite : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => p v ^ hk_rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        p v ^ hk_rayIdealExponent I v = 1 := by
      filter_upwards [hexpFinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  let coeHom : rayClassPrimeToIdeals m →* FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    (Units.coeHom (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)).comp
      (rayClassPrimeToIdeals m).subtype
  have hmap : coeHom (∏ᶠ v : HeightOneSpectrum (𝓞 K), p v ^ hk_rayIdealExponent I v) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), coeHom (p v) ^ hk_rayIdealExponent I v := by
    simpa only [map_zpow] using MonoidHom.map_finprod coeHom hfinite
  have hterm (v : HeightOneSpectrum (𝓞 K)) :
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ hk_rayIdealExponent I v =
        coeHom (p v) ^ hk_rayIdealExponent I v := by
    by_cases hv : v ∉ m.finitePart.support
    · have hv0 : m.finitePart v = 0 := by
        by_contra hne
        exact hv (Finsupp.mem_support_iff.mpr hne)
      simp [p, hv0, coeHom, hk_primeToRayIdeal, idealUnit]
    · have hv' : v ∈ m.finitePart.support := by simpa using hv
      have hz : hk_rayIdealExponent I v = 0 := I.property v hv'
      simp [p, hv, coeHom, hz]
  apply Subtype.ext
  apply Units.ext
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization'
    (R := 𝓞 K) (K := K) (Units.ne_zero (I : NumberFieldFractionalIdealGroup K))
  calc
    ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^
            hk_rayIdealExponent I v := hfac.symm
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), coeHom (p v) ^ hk_rayIdealExponent I v := by
      apply finprod_congr
      exact hterm
    _ = coeHom (∏ᶠ v : HeightOneSpectrum (𝓞 K), p v ^ hk_rayIdealExponent I v) := hmap.symm
    _ = (((∏ᶠ v : HeightOneSpectrum (𝓞 K), p v ^ hk_rayIdealExponent I v :
        rayClassPrimeToIdeals m) :
        NumberFieldFractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := rfl

theorem hk_rayIdealHom_ext {m : RayClassModulus K}
    (f g : rayClassPrimeToIdeals m →* ℂˣ)
    (hprime : ∀ v : HeightOneSpectrum (𝓞 K), ∀ hv : v ∉ m.finitePart.support,
      f (hk_primeToRayIdeal m v hv) = g (hk_primeToRayIdeal m v hv)) : f = g := by
  classical
  apply MonoidHom.ext
  intro I
  let p (v : HeightOneSpectrum (𝓞 K)) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then hk_primeToRayIdeal m v hv else 1
  have hfinite : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      hk_rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hfinite' : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => p v ^ hk_rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        p v ^ hk_rayIdealExponent I v = 1 := by
      filter_upwards [hfinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  calc
    f I = f (∏ᶠ v : HeightOneSpectrum (𝓞 K), p v ^ hk_rayIdealExponent I v) :=
      congrArg f (hk_rayIdealFactorization I)
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), f (p v) ^ hk_rayIdealExponent I v := by
      simpa only [map_zpow] using MonoidHom.map_finprod f hfinite'
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), g (p v) ^ hk_rayIdealExponent I v := by
      apply finprod_congr
      intro v
      by_cases hv : v ∉ m.finitePart.support
      · have hp : p v = hk_primeToRayIdeal m v hv := by
          simpa only [p, dite_eq_left hv]
        rw [hp, hprime v hv]
      · have hv' : v ∈ m.finitePart.support := by simpa using hv
        have hz : hk_rayIdealExponent I v = 0 := I.property v hv'
        have hp : p v = 1 := by
          simpa only [p, dite_eq_right hv]
        rw [hp, hz]
        simp
    _ = g (∏ᶠ v : HeightOneSpectrum (𝓞 K), p v ^ hk_rayIdealExponent I v) := by
      symm
      simpa only [map_zpow] using MonoidHom.map_finprod g hfinite'
    _ = g I := congrArg g (hk_rayIdealFactorization I).symm

/-- Character values vanish at the primes of the modulus support. -/
theorem hk_charValue_zero_of_mem_support {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {P : HeightOneSpectrum (𝓞 K)}
    (hP : P ∈ m.finitePart.support) : charValue η P.asIdeal = 0 := by
  have hnot : ¬ IsCoprimeTo m P.asIdeal := by
    rintro ⟨hI, hunit⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count K v
        (idealUnit P.asIdeal hI : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 at hunit
    have hzero := hunit P hP
    have hcount : FractionalIdeal.count K P
        (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1 :=
      FractionalIdeal.count_self K P
    have hzero' : FractionalIdeal.count K P
        (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
      simpa [idealUnit] using hzero
    rw [hcount] at hzero'
    norm_num at hzero'
  unfold charValue
  simp [hnot]

/-- Ray-class characters agreeing on all prime-ideal character values are equal. -/
theorem hk_rayClassChar_eq_of_all_charValue {m : RayClassModulus K}
    (η η' : RayClassGroup m →* ℂˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      charValue η v.asIdeal = charValue η' v.asIdeal) : η = η' := by
  classical
  let qmap : rayClassPrimeToIdeals m →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  let f : rayClassPrimeToIdeals m →* ℂˣ := η.comp qmap
  let g : rayClassPrimeToIdeals m →* ℂˣ := η'.comp qmap
  have hprime : ∀ v : HeightOneSpectrum (𝓞 K), ∀ hv : v ∉ m.finitePart.support,
      f (hk_primeToRayIdeal m v hv) = g (hk_primeToRayIdeal m v hv) := by
    intro v hv
    let hcop : IsCoprimeTo m v.asIdeal := by
      refine ⟨v.ne_bot, ?_⟩
      intro w hw
      exact (hk_primeToRayIdeal m v hv).property w hw
    have hclass : rayClass m v.asIdeal hcop = QuotientGroup.mk
        (hk_primeToRayIdeal m v hv) := by
      rfl
    have hchar : charValue η v.asIdeal = ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hchar' : charValue η' v.asIdeal = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hvalue : η (rayClass m v.asIdeal hcop) = η' (rayClass m v.asIdeal hcop) := by
      apply Units.ext
      calc
        ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) = charValue η v.asIdeal := hchar.symm
        _ = charValue η' v.asIdeal := h v
        _ = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := hchar'
    change η (QuotientGroup.mk (hk_primeToRayIdeal m v hv)) =
      η' (QuotientGroup.mk (hk_primeToRayIdeal m v hv))
    rw [← hclass]
    exact hvalue
  have hfg : f = g := hk_rayIdealHom_ext f g hprime
  apply MonoidHom.ext
  intro c
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) c
  exact DFunLike.congr_fun hfg I

/-- A primitive inducer of a nontrivial character is nontrivial. -/
theorem hk_primitive_inducer_ne_one {m f : RayClassModulus K}
    (hfm : f ≤ m) (η : RayClassGroup m →* ℂˣ) (ψ : RayClassGroup f →* ℂˣ)
    (hη : η ≠ 1)
    (hprime : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      charValue η v.asIdeal = charValue ψ v.asIdeal) : ψ ≠ 1 := by
  intro hψ
  have hcopM (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m.finitePart.support) :
      IsCoprimeTo m v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    exact (hk_primeToRayIdeal m v hv).property w hw
  have hcopF (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m.finitePart.support) :
      IsCoprimeTo f v.asIdeal := by
    have hvF : v ∉ f.finitePart.support := by
      intro hvF
      exact hv (Finsupp.support_mono hfm.1 hvF)
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    exact (hk_primeToRayIdeal f v hvF).property w hw
  have hall : ∀ v : HeightOneSpectrum (𝓞 K),
      charValue η v.asIdeal = charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal := by
    intro v
    by_cases hv : v ∉ m.finitePart.support
    · have hval := hprime v hv
      rw [hψ] at hval
      simpa [charValue, hcopM v hv, hcopF v hv] using hval
    · have hv' : v ∈ m.finitePart.support := by
        by_contra hcon
        exact hv hcon
      rw [hk_charValue_zero_of_mem_support η hv',
        hk_charValue_zero_of_mem_support 1 hv']
  have hηone : η = (1 : RayClassGroup m →* ℂˣ) :=
    hk_rayClassChar_eq_of_all_charValue η 1 hall
  exact hη hηone

/-- Descent of a nontrivial ray-class character to its nontrivial primitive
inducer, at `K : Type*`. -/
theorem hk_descent_to_primitive {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1) :
    ∃ (f : RayClassModulus K) (ψ : RayClassGroup f →* ℂˣ),
      f ≤ m ∧ modulusNorm f = conductorNorm η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        charValue η v.asIdeal = charValue ψ v.asIdeal) ∧
      HKPrimitive ψ ∧ ψ ≠ 1 := by
  obtain ⟨f, ψ, hfm, hfnorm, hagree, hprim⟩ := hk_exists_primitive η
  exact ⟨f, ψ, hfm, hfnorm, hagree, hprim,
    hk_primitive_inducer_ne_one hfm η ψ hη hagree⟩

end ArtinPrimitiveRoots.Proofs.hk_misc_muse
