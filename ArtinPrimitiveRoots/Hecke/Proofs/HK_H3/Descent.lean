import ArtinPrimitiveRoots.Hecke.Dictionary

/-! Universe-polymorphic (§9) primitive-descent port for `K : Type*`.

The frozen `Dictionary.exists_primitive` is at `F : Type` (`Type 0`), so it
cannot be applied to the `K : Type*` of the frozen H3 statement. This file
ports its proof chain with `K : Type*`: the transition map, the modulus
monotonicity/weight minimum, and the primitive-existence conclusion.
Proofs follow `Hecke/Dictionary.lean` and `Hecke/Dict/ConductorSupport.lean`
line by line. -/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory ArtinPrimitiveRoots.Hecke

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.hk_misc_muse

open ArtinPrimitiveRoots.Dictionary

variable {K : Type*} [Field K] [NumberField K]

/-- The finite-part ideal, as a lane-local copy at `K : Type*`. -/
def hk_modulusIdeal (m : RayClassModulus K) : Ideal (𝓞 K) :=
  m.finitePart.prod (fun v e => v.asIdeal ^ e)

private theorem hk_modulusIdeal_antitone {n m : RayClassModulus K} (h : n ≤ m) :
    hk_modulusIdeal m ≤ hk_modulusIdeal n := by
  classical
  let d := m.finitePart - n.finitePart
  have hd : n.finitePart + d = m.finitePart := by
    ext v
    exact Nat.add_sub_of_le (h.1 v)
  unfold hk_modulusIdeal
  rw [← hd, Finsupp.prod_add_index' (h_zero := by intro v; simp)
    (h_add := by intro v a b; simp [pow_add])]
  exact Ideal.mul_le_left

private theorem hk_modulusNorm_mono {n m : RayClassModulus K} (h : n ≤ m) :
    ArtinPrimitiveRoots.Hecke.modulusNorm n ≤
      ArtinPrimitiveRoots.Hecke.modulusNorm m := by
  have hdiv : ArtinPrimitiveRoots.Hecke.modulusNorm n ∣
      ArtinPrimitiveRoots.Hecke.modulusNorm m := by
    have h1 : ArtinPrimitiveRoots.Hecke.modulusNorm n =
        Ideal.absNorm (hk_modulusIdeal n) := by
      simp [ArtinPrimitiveRoots.Hecke.modulusNorm, hk_modulusIdeal,
        Finsupp.prod, map_prod, map_pow]
    have h2 : ArtinPrimitiveRoots.Hecke.modulusNorm m =
        Ideal.absNorm (hk_modulusIdeal m) := by
      simp [ArtinPrimitiveRoots.Hecke.modulusNorm, hk_modulusIdeal,
        Finsupp.prod, map_prod, map_pow]
    rw [h1, h2]
    exact Ideal.absNorm_dvd_absNorm_of_le (hk_modulusIdeal_antitone h)
  have hmpos : 0 < ArtinPrimitiveRoots.Hecke.modulusNorm m :=
    ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  exact Nat.le_of_dvd hmpos hdiv

/-- A character factors through its own modulus. -/
theorem hk_factorsThrough_self {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) : FactorsThrough η m := by
  refine ⟨⟨le_refl _, Finset.Subset.refl _⟩, ?_⟩
  intro x hx h
  have hmem : (⟨toPrincipalIdeal (𝓞 K) K x, h⟩ : rayClassPrimeToIdeals m) ∈
      rayPrincipalIdealSubgroupInPrimeTo m :=
    Subgroup.subset_closure ⟨x, hx, rfl⟩
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]

private def hk_rayModulusWeight (m : RayClassModulus K) : ℕ :=
  m.finitePart.sum (fun _ e => e) + m.infinitePart.card

private theorem hk_rayModulusWeight_strict_mono {n m : RayClassModulus K}
    (h : n ≤ m) (hne : n ≠ m) :
    hk_rayModulusWeight n < hk_rayModulusWeight m := by
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
      congrArg (fun d : HeightOneSpectrum (𝓞 K) →₀ ℕ => d.sum (fun _ e => e)) hfin
    unfold hk_rayModulusWeight
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
    unfold hk_rayModulusWeight
    omega

private def hk_rayCongruentUnits (m : RayClassModulus K) : Subgroup (Kˣ) where
  carrier := {x | IsRayCongruent m x}
  one_mem' := by
    constructor
    · intro v hv
      exact (rayLocalHigherUnitGroup v (m.finitePart v)).one_mem
    · intro w hw
      simp
  mul_mem' {x y} hx hy := by
    constructor
    · intro v hv
      simpa [IsRayCongruent, finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx.1 v hv) (hy.1 v hv)
    · intro w hw
      simpa [IsRayCongruent] using mul_pos (hx.2 w hw) (hy.2 w hw)
  inv_mem' {x} hx := by
    constructor
    · intro v hv
      simpa [IsRayCongruent, finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).inv_mem (hx.1 v hv)
    · intro w hw
      simpa [IsRayCongruent] using inv_pos.mpr (hx.2 w hw)

private def hk_rayPrincipalIdealHom (m : RayClassModulus K) :
    hk_rayCongruentUnits m →* NumberFieldFractionalIdealGroup K :=
  (toPrincipalIdeal (𝓞 K) K).comp (hk_rayCongruentUnits m).subtype

private theorem hk_rayPrincipalIdealSubgroup_eq_range (m : RayClassModulus K) :
    rayPrincipalIdealSubgroup m = (hk_rayPrincipalIdealHom m).range := by
  have hset :
      {I : NumberFieldFractionalIdealGroup K |
        ∃ x : Kˣ, IsRayCongruent m x ∧ toPrincipalIdeal (𝓞 K) K x = I} =
        Set.range (hk_rayPrincipalIdealHom m) := by
    ext I
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hrange : Set.range (hk_rayPrincipalIdealHom m) =
      ((hk_rayPrincipalIdealHom m).range : Set _) := by
    ext I
    simp [MonoidHom.mem_range]
  calc
    rayPrincipalIdealSubgroup m =
        Subgroup.closure (Set.range (hk_rayPrincipalIdealHom m)) := by
      rw [rayPrincipalIdealSubgroup, hset]
    _ = (hk_rayPrincipalIdealHom m).range := by
      rw [hrange, Subgroup.closure_eq]

private theorem hk_rayLocalHigherUnitGroup_antitone
    (v : HeightOneSpectrum (𝓞 K)) {n e : ℕ}
    (hne : n ≤ e) : rayLocalHigherUnitGroup v e ≤ rayLocalHigherUnitGroup v n := by
  intro u hu
  rcases Subgroup.mem_map.mp hu with ⟨y, hy, huy⟩
  apply Subgroup.mem_map.mpr
  refine ⟨y, ?_, huy⟩
  have hker : rayLocalHigherUnitMap v e y = 1 := by
    simpa only [MonoidHom.mem_ker] using hy
  let z : v.adicCompletionIntegers K :=
    ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y :
      (v.adicCompletionIntegers K).toSubmonoidˣ).1
  have hval : Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ e)
        z = 1 := by
    have hker' : Units.map
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ e)).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) = 1 := by
      simpa [rayLocalHigherUnitMap] using hker
    have hval' := congrArg Units.val hker'
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ e) z = 1 at hval'
    exact hval'
  have hsubE :
      z - (1 : v.adicCompletionIntegers K) ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ e := by
    rw [← Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact hval
  have hsub :
      z - (1 : v.adicCompletionIntegers K) ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n :=
    (Ideal.pow_le_pow_right hne) hsubE
  have hmem :
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
          z = 1 := by
    rw [Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact hsub
  have hkerN : rayLocalHigherUnitMap v n y = 1 := by
    change Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)).toMonoidHom
      ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) = 1
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      z = 1
    exact hmem
  exact hkerN

private theorem hk_rayCongruent_mono {n m : RayClassModulus K} (h : n ≤ m)
    {x : Kˣ} (hx : IsRayCongruent m x) : IsRayCongruent n x := by
  constructor
  · intro v hv
    have hv' : v ∈ m.finitePart.support :=
      Finsupp.support_mono h.1 hv
    have he : n.finitePart v ≤ m.finitePart v := h.1 v
    exact hk_rayLocalHigherUnitGroup_antitone v he (hx.1 v hv')
  · intro v hv
    exact hx.2 v (h.2 hv)

private theorem hk_rayPrincipalIdealSubgroup_mono {n m : RayClassModulus K}
    (h : n ≤ m) :
    rayPrincipalIdealSubgroup m ≤ rayPrincipalIdealSubgroup n := by
  unfold rayPrincipalIdealSubgroup
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, rfl⟩
  exact ⟨x, hk_rayCongruent_mono h hx, rfl⟩

private theorem hk_rayClassPrimeToIdeals_mono {n m : RayClassModulus K}
    (h : n ≤ m) :
    rayClassPrimeToIdeals m ≤ rayClassPrimeToIdeals n := by
  intro I hI v hv
  exact hI v (Finsupp.support_mono h.1 hv)

/-- The transition homomorphism from the ray class group of a modulus to that
of a divisor. -/
noncomputable def hk_rayClassMap {n m : RayClassModulus K} (h : n ≤ m) :
    RayClassGroup m →* RayClassGroup n :=
  QuotientGroup.map (rayPrincipalIdealSubgroupInPrimeTo m)
    (rayPrincipalIdealSubgroupInPrimeTo n)
    (Subgroup.inclusion (hk_rayClassPrimeToIdeals_mono h)) (by
      intro I hI
      apply Subgroup.mem_comap.mpr
      exact hk_rayPrincipalIdealSubgroup_mono h (Subgroup.mem_comap.mp hI))

@[simp]
theorem hk_rayClassMap_apply_mk {n m : RayClassModulus K} (h : n ≤ m)
    (I : rayClassPrimeToIdeals m) :
    hk_rayClassMap h (QuotientGroup.mk I) =
      QuotientGroup.mk (Subgroup.inclusion (hk_rayClassPrimeToIdeals_mono h) I) := rfl

private theorem hk_rayClassMap_ker_le {n m : RayClassModulus K}
    (h : n ≤ m) (η : RayClassGroup m →* ℂˣ) (hη : FactorsThrough η n) :
    (hk_rayClassMap h).ker ≤ η.ker := by
  intro c hc
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) c
  have hq : hk_rayClassMap h (QuotientGroup.mk I) = 1 := MonoidHom.mem_ker.mp hc
  have hprincipal :
      Subgroup.inclusion (hk_rayClassPrimeToIdeals_mono h) I ∈
        rayPrincipalIdealSubgroupInPrimeTo n :=
    (QuotientGroup.eq_one_iff _).mp hq
  have hprincipal' :
      ((rayClassPrimeToIdeals n).subtype
        (Subgroup.inclusion (hk_rayClassPrimeToIdeals_mono h) I)) ∈
          rayPrincipalIdealSubgroup n :=
    Subgroup.mem_comap.mp hprincipal
  rw [hk_rayPrincipalIdealSubgroup_eq_range n] at hprincipal'
  obtain ⟨u, hI⟩ := MonoidHom.mem_range.mp hprincipal'
  let x : Kˣ := u
  have hu : IsRayCongruent n x := u.property
  have hIeq : toPrincipalIdeal (𝓞 K) K x =
      (rayClassPrimeToIdeals m).subtype I := by
    simpa [hk_rayPrincipalIdealHom, x] using hI
  have hIprime : toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals m := by
    rw [hIeq]
    exact I.property
  have hkill := hη.2 x hu hIprime
  have hclass :
      (QuotientGroup.mk I : RayClassGroup m) =
        QuotientGroup.mk ⟨toPrincipalIdeal (𝓞 K) K x, hIprime⟩ := by
    congr 1
    exact Subtype.ext hIeq.symm
  change η (QuotientGroup.mk I) = 1
  rw [hclass]
  exact hkill

/-- A character that factors through a divisor modulus extends from the
transition-map image to the whole smaller ray class group. -/
theorem hk_exists_rayClassChar_of_factorsThrough {n m : RayClassModulus K}
    (h : n ≤ m) (η : RayClassGroup m →* ℂˣ) (hη : FactorsThrough η n) :
    ∃ ψ : RayClassGroup n →* ℂˣ, η = ψ.comp (hk_rayClassMap h) := by
  classical
  let q := hk_rayClassMap h
  let qR := q.rangeRestrict
  have hker : qR.ker ≤ η.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk_rayClassMap_ker_le h η hη
  let ηR : q.range →* ℂˣ :=
    qR.liftOfSurjective q.rangeRestrict_surjective ⟨η, hker⟩
  have hηR : ηR.comp qR = η := by
    ext x
    simp [ηR, qR, MonoidHom.liftOfSurjective]
  have hexp : Monoid.exponent (RayClassGroup n) ≠ 0 :=
    Monoid.exponent_ne_zero_of_finite (G := RayClassGroup n)
  letI : NeZero ((Monoid.exponent (RayClassGroup n) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast hexp⟩
  have hrestrictSurj :
      Function.Surjective (MonoidHom.domRestrictHom q.range ℂˣ) :=
    MonoidHom.domRestrict_surjective (G := RayClassGroup n) (M := ℂ) (H := q.range)
  obtain ⟨ψ, hψ⟩ := hrestrictSurj ηR
  have hψval (y : q.range) : ψ y.1 = ηR y := by
    have := congrArg (fun g : q.range →* ℂˣ => g y) hψ
    simpa using this
  refine ⟨ψ, ?_⟩
  apply MonoidHom.ext
  intro x
  calc
    η x = ηR (qR x) := (DFunLike.congr_fun hηR x).symm
    _ = ψ (qR x) := (hψval (qR x)).symm

/-- The prime-to ideal of a finite place outside the modulus support. -/
def hk_primeToRayIdeal (m : RayClassModulus K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) : rayClassPrimeToIdeals m :=
  ⟨idealUnit v.asIdeal v.ne_bot, by
    intro w hw
    have hne : w ≠ v := by
      intro hEq
      exact hv (hEq ▸ hw)
    change FractionalIdeal.count K w
      (idealUnit v.asIdeal v.ne_bot : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
    simpa [idealUnit] using
      (FractionalIdeal.count_maximal_coprime K w hne.symm)⟩

/-- Universe-polymorphic primitive descent: every ray-class character is
induced by a primitive one at a modulus of norm `conductorNorm η`. -/
theorem hk_exists_primitive {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) :
    ∃ (f : RayClassModulus K) (η' : RayClassGroup f →* ℂˣ),
      f ≤ m ∧ modulusNorm f = conductorNorm η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        charValue η v.asIdeal = charValue η' v.asIdeal) ∧
      ∀ n : RayClassModulus K, FactorsThrough η' n → n = f := by
  classical
  let normSet : Set ℕ :=
    {N | ∃ n : RayClassModulus K, FactorsThrough η n ∧ modulusNorm n = N}
  have hnormSet : normSet.Nonempty := by
    exact ⟨modulusNorm m, m, hk_factorsThrough_self η, rfl⟩
  have hnormMem : conductorNorm η ∈ normSet := by
    simpa [conductorNorm, normSet] using Nat.sInf_mem hnormSet
  obtain ⟨f₀, hf₀, hf₀norm⟩ := hnormMem
  let weightSet : Set ℕ :=
    {w | ∃ n : RayClassModulus K, FactorsThrough η n ∧
      modulusNorm n = conductorNorm η ∧ hk_rayModulusWeight n = w}
  have hweightSet : weightSet.Nonempty := by
    exact ⟨hk_rayModulusWeight f₀, f₀, hf₀, hf₀norm, rfl⟩
  have hweightMem := Nat.sInf_mem hweightSet
  obtain ⟨f, hf, hfnorm, hfweight⟩ := hweightMem
  obtain ⟨η', hηeq⟩ := hk_exists_rayClassChar_of_factorsThrough hf.1 η hf
  have hcop (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo m q.asIdeal := by
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (hk_primeToRayIdeal m q hq).property w hw
  have hcopF (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo f q.asIdeal := by
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (hk_primeToRayIdeal f q hqF).property w hw
  have hprimeClass (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ m.finitePart.support) :
      η (rayClass m q.asIdeal (hcop q hq)) =
        η' (rayClass f q.asIdeal (hcopF q hq)) := by
    let Pm := hk_primeToRayIdeal m q hq
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    let Pf := hk_primeToRayIdeal f q hqF
    have hclassM : rayClass m q.asIdeal (hcop q hq) = QuotientGroup.mk Pm := rfl
    have hclassF : rayClass f q.asIdeal (hcopF q hq) = QuotientGroup.mk Pf := rfl
    have hmap : hk_rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
      rw [hk_rayClassMap_apply_mk]
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
      have hIF : toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals f := by
        intro q hq
        exact hI q (Finsupp.support_mono hf.1.1 hq)
      let Pm : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K x, hI⟩
      let Pf : rayClassPrimeToIdeals f := ⟨toPrincipalIdeal (𝓞 K) K x, hIF⟩
      have hmap : hk_rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
        rw [hk_rayClassMap_apply_mk]
        congr 1
      have hηprime := DFunLike.congr_fun hηeq (QuotientGroup.mk Pm)
      have hηvalue : η (QuotientGroup.mk Pm) = η' (QuotientGroup.mk Pf) := by
        calc
          η (QuotientGroup.mk Pm) =
              η' (hk_rayClassMap hf.1 (QuotientGroup.mk Pm)) := by
            simpa [MonoidHom.comp_apply] using hηprime
          _ = η' (QuotientGroup.mk Pf) := congrArg η' hmap
      change η (QuotientGroup.mk Pm) = 1
      rw [hηvalue]
      exact hn.2 x hx hIF
    have hnormLower : conductorNorm η ≤ modulusNorm n :=
      Nat.sInf_le ⟨n, hηFactorsN, rfl⟩
    have hnormUpper : modulusNorm n ≤ modulusNorm f := hk_modulusNorm_mono hn.1
    have hnormEq : modulusNorm n = conductorNorm η := by
      rw [hfnorm] at hnormUpper
      exact le_antisymm hnormUpper hnormLower
    have hnWeight : hk_rayModulusWeight n ∈ weightSet :=
      ⟨n, hηFactorsN, hnormEq, rfl⟩
    have hweightLower : hk_rayModulusWeight f ≤ hk_rayModulusWeight n := by
      rw [hfweight]
      exact Nat.sInf_le hnWeight
    by_contra hne
    have hweightStrict := hk_rayModulusWeight_strict_mono hn.1 hne
    omega

end ArtinPrimitiveRoots.Proofs.hk_misc_muse
