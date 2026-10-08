import Mathlib

/-!
# A1 interface, §0–1: field data, the finite set S, S-integers

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1

/-! ## 0. Field data (def:ar-field; resolves D1) -/

/-- A1's field: a number field with a primitive 12th root of unity, and one fixed complex
embedding `σ0` through which every root-of-unity–valued symbol is read (A1 defect D1).
Cyclotomicity is not assumed (A1-DESIGN §1, Q4). -/
structure FieldData (F : Type) [Field F] [NumberField F] where
  ζ12 : F
  hζ12 : IsPrimitiveRoot ζ12 12
  σ0 : F →+* ℂ

/-- Part B's fields `ℚ(μ_n)`, `12 ∣ n`, contain a primitive 12th root of unity. -/
theorem cyclotomic_has_primitive_twelfth_root (n : ℕ) [NeZero n] (h : 12 ∣ n) :
    ∃ ζ : CyclotomicField n ℚ, IsPrimitiveRoot ζ 12 := by
  have : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using hk)
  refine ⟨IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ k, ?_⟩
  have h2 := hζ.pow_of_dvd hk0 (by rw [hk]; exact dvd_mul_left k 12)
  have h3 : n / k = 12 := by
    rw [hk]; exact Nat.mul_div_cancel 12 (Nat.pos_of_ne_zero hk0)
  rwa [h3] at h2

/-- The instance of `FieldData` used by Part B (`F_q = ℚ(μ_{12q})`), for any choice of `σ0`. -/
def cyclotomicFieldData (n : ℕ) [NeZero n] (h : 12 ∣ n) (σ0 : CyclotomicField n ℚ →+* ℂ) :
    FieldData (CyclotomicField n ℚ) where
  ζ12 := (cyclotomic_has_primitive_twelfth_root n h).choose
  hζ12 := (cyclotomic_has_primitive_twelfth_root n h).choose_spec
  σ0 := σ0

variable {F : Type} [Field F] [NumberField F]

/-- `μ12 ⊂ F` forces `F` totally complex. Package P-ARITH-BASE. -/
theorem FieldData.isTotallyComplex (D : FieldData F) : IsTotallyComplex F := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  let ι : F →+* ℝ := hreal.embedding
  have hprim : IsPrimitiveRoot (ι D.ζ12) 12 :=
    IsPrimitiveRoot.map_of_injective (f := ι) D.hζ12 (RingHom.injective ι)
  have hsq : ((ι D.ζ12) ^ 6) ^ 2 = 1 := by
    calc
      ((ι D.ζ12) ^ 6) ^ 2 = (ι D.ζ12) ^ (6 * 2) := by rw [pow_mul]
      _ = (ι D.ζ12) ^ 12 := by norm_num
      _ = 1 := hprim.pow_eq_one
  have hnonneg : 0 ≤ (ι D.ζ12) ^ 6 := by positivity
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hprim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h
  · have : (ι D.ζ12) ^ 6 = -1 := h
    linarith

/-- Number of complex places, `r = [F:ℚ]/2`. -/
def numComplex (F : Type) [Field F] [NumberField F] : ℕ := Fintype.card (InfinitePlace F)

/-! ## 1. Places, the finite set `S`, S-integers (def:ar-S, def:ar-notation) -/

/-- Finite places of `F`. -/
abbrev FinPlace (F : Type) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)

/-- The finite set `S` (its finite part `Sf`; all complex places are in `S` implicitly).
Choice order (A1-DESIGN §2.1): `CE` (A2's absolute Euler cutoff, `po:H-local-bounds`) and the
conductor `condη` of the target character are fixed first; then `S`; everything else after.
Item (v) of def:ar-S (theta-exceptional places) is empty in route C beyond the places over 3. -/
structure SData (F : Type) [Field F] [NumberField F] (CE : ℕ) (condη : Ideal (𝓞 F)) where
  Sf : Finset (FinPlace F)
  over6 : ∀ v : FinPlace F, (6 : 𝓞 F) ∈ v.asIdeal → v ∈ Sf
  cond_mem : ∀ v : FinPlace F, condη ≤ v.asIdeal → v ∈ Sf
  different_mem : ∀ v : FinPlace F, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ Sf
  euler_mem : ∀ v : FinPlace F, Ideal.absNorm v.asIdeal ≤ CE → v ∈ Sf
  pid : IsPrincipalIdealRing ((Sf : Set (FinPlace F)).integer F)

private lemma mem_sInteger_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) (x : K) :
    x ∈ S.integer K ↔ ∀ v ∉ S, v.valuation K x ≤ 1 := Iff.rfl

private def denominatorIdeal {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    [Algebra R K] (x : K) : Ideal R where
  carrier := {r | ∃ s : R, algebraMap R K r * x = algebraMap R K s}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, ?_⟩
    rw [map_add, add_mul, hs, ht, map_add]
  smul_mem' := by
    rintro a r ⟨s, hs⟩
    refine ⟨a * s, ?_⟩
    change algebraMap R K (a * r) * x = algebraMap R K (a * s)
    rw [map_mul, map_mul, mul_assoc, hs]

private lemma mem_denominatorIdeal {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    [Algebra R K] (x : K) (r : R) :
    r ∈ denominatorIdeal x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := Iff.rfl

private lemma denominatorIdeal_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : K) :
    denominatorIdeal (R := R) (K := K) x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have hden : algebraMap R K (b : R) * x = algebraMap R K a := by
    rw [← hab, IsFractionRing.mk'_eq_div]
    have hb : algebraMap R K (b : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    field_simp [hb]
  have hb : (b : R) ∈ denominatorIdeal (R := R) (K := K) x := by
    exact ⟨a, hden⟩
  intro h
  have : (b : R) ∈ (⊥ : Ideal R) := h ▸ hb
  have hbzero : (b : R) = 0 := by simpa using this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp b.property) hbzero

private lemma denominatorIdeal_not_le {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (x : K) (hx : v.valuation K x ≤ 1) :
    ¬ denominatorIdeal (R := R) (K := K) x ≤ v.asIdeal := by
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  intro hle
  have hd : (d : R) ∈ denominatorIdeal (R := R) (K := K) x := by
    rw [mem_denominatorIdeal]
    exact ⟨n, by rw [mul_comm]; exact hnd⟩
  exact d.property (hle hd)

private lemma integer_map_asIdeal_eq_top {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) {v : HeightOneSpectrum R} (hv : v ∈ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal = ⊤ := by
  let A := S.integer K
  let f := algebraMap R A
  have h1F : (1 : K) ∈
      (v.asIdeal : FractionalIdeal R⁰ K) * (v.asIdeal : FractionalIdeal R⁰ K)⁻¹ := by
    rw [FractionalIdeal.coe_ideal_mul_inv _ v.ne_bot]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  have h1 := h1F
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at h1
  have H : ∀ x ∈ (v.asIdeal : FractionalIdeal R⁰ K) *
      (v.asIdeal : FractionalIdeal R⁰ K)⁻¹,
      ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ Ideal.map f v.asIdeal := by
    intro x hx
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hx
    refine Submodule.mul_induction_on hx (fun a ha y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp
        ((FractionalIdeal.mem_coe (I := (v.asIdeal : FractionalIdeal R⁰ K))).mpr ha)
      have hyA : y ∈ A := by
        rw [mem_sInteger_iff]
        intro w hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw hv
        have hnot : ¬v.asIdeal ≤ w.asIdeal := by
          intro hle
          have heq : v.asIdeal = w.asIdeal :=
            v.isMaximal.eq_of_le w.isPrime.ne_top hle
          exact hwv (HeightOneSpectrum.ext heq.symm)
        obtain ⟨b, hb, hbw⟩ := Set.not_subset_iff_exists_mem_notMem.mp hnot
        have hprod : y * algebraMap R K b ∈ (1 : FractionalIdeal R⁰ K) :=
          (FractionalIdeal.mem_inv_iff
            (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).mp hy _
              (FractionalIdeal.mem_coeIdeal_of_mem R⁰ (by
                -- `b` is the ideal element outside `w`.
                simpa using hb))
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
        have hval : w.valuation K (y * algebraMap R K b) ≤ 1 := by
          rw [hr.symm]
          exact w.valuation_le_one r
        rw [map_mul, w.valuation_eq_one_iff_notMem.mpr hbw, mul_one] at hval
        exact hval
      have haA : algebraMap R K a ∈ A := A.algebraMap_mem a
      refine ⟨mul_mem haA hyA, ?_⟩
      have he : (⟨algebraMap R K a * y, mul_mem haA hyA⟩ : A) = f a * ⟨y, hyA⟩ := by
        apply Subtype.ext
        simp [f, A]
      rw [he]
      exact Ideal.mul_mem_right _ _ <| Ideal.mem_map_of_mem f ha'
    · obtain ⟨hx, hx'⟩ := hx
      obtain ⟨hy, hy'⟩ := hy
      exact ⟨add_mem hx hy, add_mem hx' hy'⟩
  refine (Ideal.eq_top_iff_one _).mpr ?_
  obtain ⟨h1A, h1I⟩ := H 1 h1F
  have h1A' : (⟨1, h1A⟩ : A) = 1 := Subtype.ext (by simp)
  exact h1A' ▸ h1I

private lemma integer_map_denominatorIdeal_eq_top {R : Type*} [CommRing R]
    [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) {x : K} (hx : x ∈ S.integer K) :
    Ideal.map (algebraMap R (S.integer K)) (denominatorIdeal (R := R) (K := K) x) = ⊤ := by
  let f := algebraMap R (S.integer K)
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hdenle : denominatorIdeal (R := R) (K := K) x ≤ M.comap f :=
    (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
  have hPne : M.comap f ≠ ⊥ := fun h0 =>
    denominatorIdeal_ne_bot (R := R) (K := K) x <| bot_unique <| h0 ▸ hdenle
  have hprime : (M.comap f).IsPrime := hM.isPrime.comap f
  let v : HeightOneSpectrum R := ⟨M.comap f, hprime, hPne⟩
  have hvS : v ∈ S := by
    by_contra hvS
    exact denominatorIdeal_not_le (R := R) (K := K) v x
      ((mem_sInteger_iff (R := R) (K := K) S x).mp hx v hvS) hdenle
  have htop := integer_map_asIdeal_eq_top (R := R) (K := K) S hvS
  have htopM : (⊤ : Ideal (S.integer K)) ≤ M := by
    rw [← htop]
    simpa [v] using (Ideal.map_comap_le (f := f) (K := M))
  exact hM.ne_top (top_le_iff.mp htopM)

private theorem integer_map_comap_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) (I : Ideal (S.integer K)) :
    Ideal.map (algebraMap R (S.integer K)) (I.comap (algebraMap R (S.integer K))) = I := by
  refine le_antisymm Ideal.map_comap_le ?_
  let f := algebraMap R (S.integer K)
  let J' := Ideal.map f (I.comap f)
  intro x hx
  have hkey (d : R) (hd : d ∈ denominatorIdeal (R := R) (K := K) (x : K)) :
      f d * x ∈ J' := by
    obtain ⟨s, hs⟩ := (mem_denominatorIdeal (x : K) d).mp hd
    have he : f d * x = f s := by
      apply Subtype.ext
      exact hs
    have hsI : f s ∈ I := by
      rw [← he]
      exact I.mul_mem_left _ hx
    rw [he]
    exact Ideal.mem_map_of_mem f (Ideal.mem_comap.mpr hsI)
  have hsub : Ideal.map f (denominatorIdeal (R := R) (K := K) (x : K)) ≤ J'.colon {x} :=
    Ideal.map_le_iff_le_comap.mpr fun d hd => by
      simpa only [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul] using hkey d hd
  have htop : Ideal.map f (denominatorIdeal (R := R) (K := K) (x : K)) = ⊤ :=
    integer_map_denominatorIdeal_eq_top S x.property
  have hx' : (1 : S.integer K) * x ∈ J' :=
    Submodule.mem_colon_singleton.mp (hsub (htop.ge Submodule.mem_top))
  simpa [J'] using hx'

private def primeClass {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

private theorem classGroup_mk0_mem_closure_of_prime_support
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) (G : Finset (HeightOneSpectrum R))
    (hSupport : ∀ v, v.asIdeal ∣ I → v ∈ G) (H : Subgroup (ClassGroup R))
    (hPrime : ∀ v ∈ G, primeClass v ∈ H) :
    ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ ∈ H := by
  classical
  let f (v : HeightOneSpectrum R) : (Ideal R)⁰ :=
    ⟨v.maxPowDividing I, mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero _ v.ne_bot)⟩
  have hf : Function.HasFiniteMulSupport f := by
    change (Function.mulSupport f).Finite
    have heq : Function.mulSupport f =
        Function.mulSupport (fun v : HeightOneSpectrum R => v.maxPowDividing I) := by
      ext v
      simp [f]
    rw [heq]
    exact Ideal.hasFiniteMulSupport hI
  have hfac : ((∏ᶠ v : HeightOneSpectrum R, f v : (Ideal R)⁰) : Ideal R) = I := by
    calc
      ((∏ᶠ v : HeightOneSpectrum R, f v : (Ideal R)⁰) : Ideal R) =
          ∏ᶠ v : HeightOneSpectrum R, (f v : Ideal R) := by
        exact (SubmonoidClass.subtype (nonZeroDivisors (Ideal R))).map_finprod hf
      _ = ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I := rfl
      _ = I := Ideal.finprod_heightOneSpectrum_factorization hI
  have hmulSupport : Function.mulSupport f ⊆ G := by
    intro v hv
    apply hSupport v
    by_contra hdiv
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra hc
      have hdiv' := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc
      exact hdiv hdiv'
    apply hv
    apply Subtype.ext
    dsimp [f]
    simpa [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
  have hclassfac : ClassGroup.mk0
      (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal R)⁰) =
      ∏ᶠ v : HeightOneSpectrum R, ClassGroup.mk0 (f v) := by
    calc
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ =
          ClassGroup.mk0 (∏ᶠ v : HeightOneSpectrum R, f v) :=
        congrArg ClassGroup.mk0 (Subtype.ext hfac).symm
      _ = ∏ᶠ v : HeightOneSpectrum R, ClassGroup.mk0 (f v) :=
        ClassGroup.mk0.map_finprod hf
  have hclassSupport : Function.mulSupport (fun v => ClassGroup.mk0 (f v)) ⊆ G := by
    intro v hv
    apply hmulSupport
    intro hfv
    apply hv
    simp [hfv]
  rw [hclassfac, finprod_eq_prod_of_mulSupport_subset _ hclassSupport]
  apply H.prod_mem
  intro v hvG
  by_cases hdiv : v.asIdeal ∣ I
  · let pv : (Ideal R)⁰ :=
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    let n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
    have hpow : f v = pv ^ n := by
      apply Subtype.ext
      change v.maxPowDividing I = v.asIdeal ^ n
      simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, n]
    rw [hpow, ClassGroup.mk0.map_pow]
    exact H.pow_mem (by simpa [pv, primeClass] using hPrime v hvG) n
  · have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra hc
      have hdiv' := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc
      exact hdiv hdiv'
    have hmax : f v = 1 := by
      apply Subtype.ext
      dsimp [f]
      simpa [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
    simp [hmax]

private theorem classGroup_generated_by_finite_prime_support
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Fintype (ClassGroup R)] :
    ∃ G : Finset (HeightOneSpectrum R),
      Subgroup.closure (primeClass '' (G : Set (HeightOneSpectrum R))) = ⊤ := by
  classical
  let rep : ClassGroup R → (Ideal R)⁰ := fun c => Classical.choose (ClassGroup.mk0_surjective c)
  have hrep (c : ClassGroup R) : ClassGroup.mk0 (rep c) = c := by
    dsimp [rep]
    exact Classical.choose_spec (ClassGroup.mk0_surjective c)
  have hrepNe (c : ClassGroup R) : (rep c : Ideal R) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp (rep c).property
  let G : Finset (HeightOneSpectrum R) :=
    Finset.univ.biUnion fun c => (Ideal.finite_factors (hrepNe c)).toFinset
  refine ⟨G, ?_⟩
  apply (Subgroup.eq_top_iff' _).2
  intro c
  rw [← hrep c]
  apply classGroup_mk0_mem_closure_of_prime_support (hrepNe c) G ?_
    (Subgroup.closure (primeClass '' (G : Set (HeightOneSpectrum R)))) ?_
  · intro v hdiv
    simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨c, (Ideal.finite_factors (hrepNe c)).mem_toFinset.mpr hdiv⟩
  · intro v hv
    exact Subgroup.subset_closure ⟨v, hv, rfl⟩

private theorem sInteger_isPrincipal_of_primeClasses_generate
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R))
    (hS : Subgroup.closure (primeClass '' S) = ⊤) :
    IsPrincipalIdealRing (S.integer K) := by
  classical
  let A := S.integer K
  let f := algebraMap R A
  letI : Module.IsTorsionFree R A := by infer_instance
  let e := ClassGroup.extendedHom R A
  have hprime (v : HeightOneSpectrum R) (hv : v ∈ S) :
      e (primeClass v) = 1 := by
    let pv : (Ideal R)⁰ :=
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    have hu : Units.map (FractionalIdeal.extendedHom (FractionRing A) A).toMonoidHom
        (FractionalIdeal.mk0 (FractionRing R) pv) = 1 := by
      apply Units.ext
      change FractionalIdeal.extendedHom (FractionRing A) A
        (pv.1 : FractionalIdeal R⁰ (FractionRing R)) = 1
      rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
      rw [integer_map_asIdeal_eq_top (R := R) (K := K) S hv]
      simp
    rw [primeClass, ← ClassGroup.mk_mk0 (K := FractionRing R) pv,
      ClassGroup.extendedHom_mk]
    rw [hu]
    simp
  have hker : Subgroup.closure (primeClass '' S) ≤ e.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprime v hv)
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · simpa [hI] using (bot_isPrincipal : (⊥ : Ideal A).IsPrincipal)
  let J := I.comap f
  have hJ : J ≠ ⊥ := by
    intro hJ
    have hmap := integer_map_comap_eq (R := R) (K := K) S I
    change Ideal.map f J = I at hmap
    rw [hJ, Ideal.map_bot] at hmap
    exact hI hmap.symm
  let J₀ : (Ideal R)⁰ := ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
  have hclass : e (ClassGroup.mk0 J₀) = 1 := by
    apply MonoidHom.mem_ker.mp (hker ?_)
    rw [hS]
    simp
  have htarget : ClassGroup.mk (FractionRing A)
      (Units.map (FractionalIdeal.extendedHom (FractionRing A) A).toMonoidHom
        (FractionalIdeal.mk0 (FractionRing R) J₀)) = 1 := by
    rw [← ClassGroup.mk_mk0 (K := FractionRing R) J₀,
      ClassGroup.extendedHom_mk] at hclass
    exact hclass
  have hfrac :
      (((Ideal.map f J : Ideal A) : FractionalIdeal A⁰ (FractionRing A)) :
        Submodule A (FractionRing A)).IsPrincipal := by
    have hm := (ClassGroup.mk_eq_one_iff (K := FractionRing A)).mp htarget
    simpa [FractionalIdeal.extendedHom_coeIdeal_eq_map] using hm
  have hmapprincipal : (Ideal.map f J).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal (R := A) (K := FractionRing A)
      (I := Ideal.map f J)).mp (by simpa using hfrac)
  have hmap : Ideal.map f J = I := integer_map_comap_eq (R := R) (K := K) S I
  simpa [hmap] using hmapprincipal

private lemma finite_places_absNorm_le (CE : ℕ) :
    {v : FinPlace F | Ideal.absNorm v.asIdeal ≤ CE}.Finite := by
  apply Set.Finite.of_injOn (f := fun v : FinPlace F => v.asIdeal)
    (s := {v : FinPlace F | Ideal.absNorm v.asIdeal ≤ CE})
    (t := {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ CE}) ?_ ?_
    (Ideal.finite_setOfPred_absNorm_le CE)
  · intro v hv
    exact hv
  · intro v hv w hw h
    exact HeightOneSpectrum.ext h

/-- Existence of `S` (add class-group generators). Package P-ARITH-BASE. -/
theorem SData.nonempty (CE : ℕ) (condη : Ideal (𝓞 F)) (hη : condη ≠ ⊥) :
    Nonempty (SData F CE condη) := by
  classical
  let I6 : Ideal (𝓞 F) := Ideal.span {(6 : 𝓞 F)}
  have h6 : I6 ≠ ⊥ := by
    have h6ne : (6 : 𝓞 F) ≠ 0 := by
      exact_mod_cast (by norm_num : (6 : ℤ) ≠ 0)
    simpa [I6, Ideal.span_singleton_eq_bot] using h6ne
  have hdiff : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨G, hG⟩ := classGroup_generated_by_finite_prime_support (R := 𝓞 F)
  have hEuler := finite_places_absNorm_le (F := F) CE
  let T6 := (Ideal.finite_factors h6).toFinset
  let Tη := (Ideal.finite_factors hη).toFinset
  let Tdiff := (Ideal.finite_factors hdiff).toFinset
  let Teuler := hEuler.toFinset
  let Sf := T6 ∪ Tη ∪ Tdiff ∪ Teuler ∪ G
  have hGS : (G : Set (FinPlace F)) ⊆ (Sf : Set (FinPlace F)) := by
    intro v hv
    change v ∈ (((T6 ∪ Tη) ∪ Tdiff) ∪ Teuler) ∪ G
    exact Finset.mem_union.mpr (Or.inr hv)
  have hSf : Subgroup.closure (primeClass '' (Sf : Set (FinPlace F))) = ⊤ := by
    apply le_antisymm le_top
    rw [← hG]
    exact Subgroup.closure_mono (Set.image_mono hGS)
  have hpid : IsPrincipalIdealRing ((Sf : Set (FinPlace F)).integer F) :=
    sInteger_isPrincipal_of_primeClasses_generate (R := 𝓞 F) (K := F) Sf hSf
  refine ⟨⟨Sf, ?_, ?_, ?_, ?_, hpid⟩⟩
  · intro v hv
    have hle : I6 ≤ v.asIdeal := by
      change Ideal.span {(6 : 𝓞 F)} ≤ v.asIdeal
      apply Ideal.span_le.mpr
      intro x hx
      have hx6 : x = 6 := Set.mem_singleton_iff.mp hx
      simpa [hx6] using hv
    have hdiv : v.asIdeal ∣ I6 := Ideal.dvd_iff_le.mpr hle
    have hT6 : v ∈ T6 := by
      change v ∈ (Ideal.finite_factors h6).toFinset
      exact (Ideal.finite_factors h6).mem_toFinset.mpr hdiv
    change v ∈ (((T6 ∪ Tη) ∪ Tdiff) ∪ Teuler) ∪ G
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hT6)))
  · intro v hv
    have hdiv : v.asIdeal ∣ condη := Ideal.dvd_iff_le.mpr hv
    have hTη : v ∈ Tη := by
      change v ∈ (Ideal.finite_factors hη).toFinset
      exact (Ideal.finite_factors hη).mem_toFinset.mpr hdiv
    change v ∈ (((T6 ∪ Tη) ∪ Tdiff) ∪ Teuler) ∪ G
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hTη)))
  · intro v hv
    have hdiv : v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := Ideal.dvd_iff_le.mpr hv
    have hTdiff : v ∈ Tdiff := by
      change v ∈ (Ideal.finite_factors hdiff).toFinset
      exact (Ideal.finite_factors hdiff).mem_toFinset.mpr hdiv
    change v ∈ (((T6 ∪ Tη) ∪ Tdiff) ∪ Teuler) ∪ G
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hTdiff))
  · intro v hv
    have hTeuler : v ∈ Teuler := by
      change v ∈ hEuler.toFinset
      exact hEuler.mem_toFinset.mpr hv
    change v ∈ (((T6 ∪ Tη) ∪ Tdiff) ∪ Teuler) ∪ G
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr hTeuler)

variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- `R = O_S`. -/
abbrev SData.R (S : SData F CE condη) : Subalgebra (𝓞 F) F :=
  ((S.Sf : Set (FinPlace F))).integer F

/-- `U_S = R^×`, as a subgroup of `Fˣ`. -/
abbrev SData.US (S : SData F CE condη) : Subgroup Fˣ :=
  ((S.Sf : Set (FinPlace F))).unit F

/-- Exterior ideal: a nonzero `O_F`-ideal prime to `S_f` (≅ a nonzero ideal of `R`). -/
def SData.IsExterior (S : SData F CE condη) (I : Ideal (𝓞 F)) : Prop :=
  I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal

/-- `c ∈ F^×` generates the exterior ideal `I` in `R`: equal valuations at all `v ∉ S`.
Corrected per rev-theta to require that `I` is exterior. -/
def SData.IsGen (S : SData F CE condη) (c : F) (I : Ideal (𝓞 F)) : Prop :=
  S.IsExterior I ∧ c ≠ 0 ∧ ∀ v : FinPlace F, v ∉ S.Sf →
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) =
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)

/-- `F_S = Π_{v∈S_f} F_v × Π_{w complex} ℂ` (complex places through `w.embedding`). -/
abbrev SData.FS (S : SData F CE condη) : Type :=
  (∀ v : S.Sf, v.1.adicCompletion F) × (InfinitePlace F → ℂ)

/-- Diagonal embedding `F → F_S`. -/
def SData.diag (S : SData F CE condη) : F →+* S.FS :=
  RingHom.prod (RingHom.pi fun v : S.Sf => algebraMap F (v.1.adicCompletion F))
    (RingHom.pi fun w : InfinitePlace F => w.embedding)

/-- Diagonal embedding on units. -/
def SData.diagU (S : SData F CE condη) : Fˣ →* S.FSˣ :=
  Units.map S.diag.toMonoidHom

/-- Normalized absolute value at a finite place: `‖x‖_v = (Nv)^{-v(x)}`. -/
def absFin (v : FinPlace F) (x : v.adicCompletion F) : ℝ :=
  if h : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 then
    (WithZeroMulInt.toNNReal h (Valued.v x) : ℝ) else 0

/-- `‖y‖_S = Π_{v∈S} ‖y_v‖_v` (complex: square of the modulus, def:ar-abs). -/
def SData.absS (S : SData F CE condη) (y : S.FS) : ℝ :=
  (∏ v : S.Sf, absFin v.1 (y.1 v)) * ∏ w : InfinitePlace F, Complex.normSq (y.2 w)

/-- Norm section `ℓ_T`: finite components 1, component `T^{1/(2r)}` at each complex place.
Corrected per rev-theta to require fixed field data and `T > 0`. -/
def SData.ell (D : FieldData F) (S : SData F CE condη) (T : ℝ) (hT : 0 < T) : S.FS :=
  (fun _ => 1, fun _ => ((T ^ ((1 : ℝ) / (2 * numComplex F)) : ℝ) : ℂ))

/-- `𝒱 = F_S^×/F_S^{×6}`. -/
abbrev SData.V (S : SData F CE condη) : Type :=
  S.FSˣ ⧸ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range

/-- Component of an `F_S`-unit at a finite place of `S`. -/
def SData.compU (S : SData F CE condη) (v : S.Sf) : S.FSˣ →* (v.1.adicCompletion F)ˣ :=
  Units.map ((Pi.evalMonoidHom (fun v : S.Sf => v.1.adicCompletion F) v).comp
    (MonoidHom.fst _ _))

/-- Component of an `F_S`-unit at a complex place. -/
def SData.compC (S : SData F CE condη) (w : InfinitePlace F) : S.FSˣ →* ℂˣ :=
  Units.map ((Pi.evalMonoidHom (fun _ : InfinitePlace F => ℂ) w).comp (MonoidHom.snd _ _))

/-- The unit of `F_S` equal to `z` at the complex place `w` and 1 elsewhere (rotations, T7). -/
def SData.atComplex (S : SData F CE condη) (w : InfinitePlace F) (z : ℂˣ) : S.FSˣ where
  val := (fun _ => 1, Function.update (fun _ => 1) w (z : ℂ))
  inv := (fun _ => 1, Function.update (fun _ => 1) w ((z⁻¹ : ℂˣ) : ℂ))
  val_inv := by
    ext v
    · simp
    · by_cases h : v = w
      · subst h; simp
      · simp [Function.update_of_ne h]
  inv_val := by
    ext v
    · simp
    · by_cases h : v = w
      · subst h; simp
      · simp [Function.update_of_ne h]


end ArtinPrimitiveRoots.A1
