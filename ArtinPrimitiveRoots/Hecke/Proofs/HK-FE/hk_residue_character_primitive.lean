import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_residue_character_lift
import Mathlib.Algebra.BigOperators.Finprod


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

open IsDedekindDomain Function

private noncomputable def hk_residue_ideal_exponent (I : Ideal (𝓞 K))
    (hI : I ≠ ⊥) : HeightOneSpectrum (𝓞 K) →₀ ℕ := by
  classical
  refine Finsupp.onFinset (Ideal.finite_factors hI).toFinset
    (fun v => factorization I v.asIdeal) ?_
  intro v hv
  have hpos : 0 < factorization I v.asIdeal := Nat.pos_of_ne_zero hv
  have hcount : 0 < Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) := by
    simpa only [factorization_eq_count] using hpos
  have hfac : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.count_pos.mp hcount
  have hle : I ≤ v.asIdeal := (Ideal.mem_normalizedFactors_iff hI).mp hfac |>.2
  have hdvd : v.asIdeal ∣ I := Ideal.dvd_iff_le.mpr hle
  exact (Ideal.finite_factors hI).mem_toFinset.mpr hdvd

private theorem hk_residue_ideal_exponent_apply (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    hk_residue_ideal_exponent I hI v = factorization I v.asIdeal := by
  classical
  simp [hk_residue_ideal_exponent, Finsupp.onFinset_apply]

private noncomputable def hk_residue_modulus_of_ideal (I : Ideal (𝓞 K))
    (hI : I ≠ ⊥) : RayClassModulus K :=
  ⟨hk_residue_ideal_exponent I hI, ∅⟩

set_option maxHeartbeats 1000000 in
private theorem hk_modulusIdeal_of_ideal (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    modulusIdeal (hk_residue_modulus_of_ideal I hI) = I := by
  classical
  let e := hk_residue_ideal_exponent I hI
  let f : HeightOneSpectrum (𝓞 K) → Ideal (𝓞 K) :=
    fun v => v.asIdeal ^ multiplicity v.asIdeal I
  have he (v : HeightOneSpectrum (𝓞 K)) : e v = multiplicity v.asIdeal I := by
    dsimp [e]
    rw [hk_residue_ideal_exponent_apply]
    exact IsDedekindDomain.HeightOneSpectrum.factorization_eq_multiplicity hI v
  have hfin₀ : HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) :=
    Ideal.hasFiniteMulSupport hI
  have hfin : HasFiniteMulSupport f := by
    have hfun : f = fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I := by
      funext v
      dsimp [f]
      exact (IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI v).symm
    rw [hfun]
    exact hfin₀
  have hsupport : mulSupport f ⊆ e.support := by
    intro v hv
    change v ∈ e.support
    rw [Finsupp.mem_support_iff]
    have hmult : multiplicity v.asIdeal I ≠ 0 := by
      intro hz
      apply hv
      simp [f, hz]
    change e v ≠ 0
    rw [he]
    exact hmult
  have hprod : (∏ᶠ v : HeightOneSpectrum (𝓞 K), f v) =
      ∏ v ∈ e.support, f v := finprod_eq_prod_of_mulSupport_subset f hsupport
  calc
    modulusIdeal (hk_residue_modulus_of_ideal I hI) =
        ∏ v ∈ e.support, v.asIdeal ^ e v := rfl
    _ = ∏ v ∈ e.support, f v := by
      apply Finset.prod_congr rfl
      intro v hv
      simp only [f, he]
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v := hprod.symm
    _ = I := Ideal.finprod_heightOneSpectrum_pow_multiplicity hI

private theorem hk_modulusIdeal_count (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (modulusIdeal m : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (m.finitePart v : ℤ) := by
  classical
  have hcoe : (modulusIdeal m : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ w ∈ m.finitePart.support,
        (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ m.finitePart w := by
    change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
        (m.finitePart.prod (fun w e => w.asIdeal ^ e)) = _
    rw [Finsupp.prod, map_prod]
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod]
  · have hterm (w : HeightOneSpectrum (𝓞 K)) :
        FractionalIdeal.count K v
            ((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ m.finitePart w) =
          if w = v then (m.finitePart w : ℤ) else 0 := by
      rw [FractionalIdeal.count_pow]
      by_cases hwv : w = v
      · subst w
        rw [FractionalIdeal.count_self]
        simp
      · rw [FractionalIdeal.count_maximal_coprime K v hwv]
        simp [hwv]
    simp_rw [hterm]
    simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff]
    by_cases hv : m.finitePart v = 0 <;> simp [hv]
  · intro w hw
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

private def hk_residue_denominator_exponent (I : NumberFieldFractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  (NumberFieldFractionalIdealGroup.countVector I).mapRange
    (fun n => max 0 (-n)) (by simp)

private theorem hk_residue_denominator_exponent_nonneg
    (I : NumberFieldFractionalIdealGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ hk_residue_denominator_exponent I v := by
  simp only [hk_residue_denominator_exponent, Finsupp.mapRange_apply]
  exact le_max_left 0 _

private noncomputable irreducible_def hk_residue_denominator_ideal
    (I : NumberFieldFractionalIdealGroup K) : Ideal (𝓞 K) :=
  (hk_residue_denominator_exponent I).support.prod fun v =>
    v.asIdeal ^ Int.toNat (hk_residue_denominator_exponent I v)

private theorem hk_residue_denominator_ideal_coe (I : NumberFieldFractionalIdealGroup K) :
    (hk_residue_denominator_ideal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.factorization
        (Multiplicative.ofAdd (hk_residue_denominator_exponent I)) :
          NumberFieldFractionalIdealGroup K) := by
  classical
  rw [NumberFieldFractionalIdealGroup.factorization_val]
  rw [hk_residue_denominator_ideal]
  let d := hk_residue_denominator_exponent I
  change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
      (∏ v ∈ d.support, v.asIdeal ^ Int.toNat (d v)) =
    ∏ v ∈ d.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ d v
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro v hv
  have hnat : (Int.toNat (d v) : ℤ) = d v :=
    Int.toNat_of_nonneg (hk_residue_denominator_exponent_nonneg I v)
  rw [← hnat, zpow_natCast]
  rfl

private theorem hk_residue_denominator_ideal_ne_bot (I : NumberFieldFractionalIdealGroup K) :
    hk_residue_denominator_ideal I ≠ ⊥ := by
  intro h
  have hcoe :
      (hk_residue_denominator_ideal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
    rw [h]
    simp
  rw [hk_residue_denominator_ideal_coe] at hcoe
  exact Units.ne_zero
    (NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd (hk_residue_denominator_exponent I))) hcoe

private theorem hk_residue_denominator_ideal_count (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (hk_residue_denominator_ideal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        hk_residue_denominator_exponent I v := by
  rw [hk_residue_denominator_ideal_coe]
  simpa using NumberFieldFractionalIdealGroup.count_factorization
    (Multiplicative.ofAdd (hk_residue_denominator_exponent I)) v

private theorem hk_residue_denominator_ideal_coprime [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    IsCoprimeTo m (hk_residue_denominator_ideal (A : NumberFieldFractionalIdealGroup K)) := by
  let I : NumberFieldFractionalIdealGroup K := A
  let D := hk_residue_denominator_ideal I
  have hD : D ≠ ⊥ := hk_residue_denominator_ideal_ne_bot I
  refine ⟨hD, ?_⟩
  change ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      ((idealUnit D hD : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  intro v hv
  have hA : FractionalIdeal.count K v
      ((A : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := A.2 v hv
  have hcountI : NumberFieldFractionalIdealGroup.countVector I v = 0 := by
    simpa [I] using hA
  have hzero : hk_residue_denominator_exponent I v = 0 := by
    simp [hk_residue_denominator_exponent, hcountI]
  simpa [D, idealUnit, hk_residue_denominator_ideal_count, hzero]

private def hk_integralIdealOfExponent (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, 0 ≤ e v) : Ideal (𝓞 K) :=
  e.support.prod fun v => v.asIdeal ^ Int.toNat (e v)

private theorem hk_coe_integralIdealOfExponent (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, 0 ≤ e v) :
    (hk_integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) :
        NumberFieldFractionalIdealGroup K) := by
  classical
  rw [NumberFieldFractionalIdealGroup.factorization_val]
  change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
      (∏ v ∈ e.support, v.asIdeal ^ Int.toNat (e v)) =
    ∏ v ∈ e.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ e v
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro v hv
  have hnat : (Int.toNat (e v) : ℤ) = e v := Int.toNat_of_nonneg (he v)
  rw [← hnat, zpow_natCast]
  rfl

private theorem hk_factorization_countVector (I : NumberFieldFractionalIdealGroup K) :
    NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd (NumberFieldFractionalIdealGroup.countVector I)) = I := by
  apply NumberFieldFractionalIdealGroup.ext_count
  intro v
  rw [NumberFieldFractionalIdealGroup.count_factorization]
  exact NumberFieldFractionalIdealGroup.countVector_apply I v

private theorem hk_fractional_le_one_of_count_nonneg (I : NumberFieldFractionalIdealGroup K)
    (hI : ∀ v, 0 ≤ FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 := by
  let e := NumberFieldFractionalIdealGroup.countVector I
  have he : ∀ v, 0 ≤ e v := by
    intro v
    simpa [e] using hI v
  have hcoe :
      (hk_integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    calc
      (hk_integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) :
            NumberFieldFractionalIdealGroup K) := hk_coe_integralIdealOfExponent e he
      _ = (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        congrArg Units.val (by simpa [e] using hk_factorization_countVector I)
  rw [← hcoe]
  exact FractionalIdeal.coeIdeal_le_one

private theorem hk_denominator_count_le_integralPrincipal_count
    (I : NumberFieldFractionalIdealGroup K) (a : 𝓞 K) (ha : a ≠ 0)
    (haD : a ∈ hk_residue_denominator_ideal I) (v : HeightOneSpectrum (𝓞 K)) :
    hk_residue_denominator_exponent I v ≤
      FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K
          (Units.mk0 (algebraMap (𝓞 K) K a)
            ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp ha
  have hspanLe : (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      (hk_residue_denominator_ideal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    apply (FractionalIdeal.coeIdeal_le_coeIdeal K).2
    exact (Ideal.span_singleton_le_iff_mem
      (hk_residue_denominator_ideal I)).mpr haD
  have hmono := FractionalIdeal.count_mono K v
    (FractionalIdeal.coeIdeal_ne_zero.mpr hspan0) hspanLe
  have hmono' : hk_residue_denominator_exponent I v ≤
      FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K
          (Units.mk0 (algebraMap (𝓞 K) K a)
            ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    calc
      hk_residue_denominator_exponent I v =
          FractionalIdeal.count K v
            (hk_residue_denominator_ideal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        (hk_residue_denominator_ideal_count I v).symm
      _ ≤ FractionalIdeal.count K v
          (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := hmono
      _ = FractionalIdeal.count K v
          (toPrincipalIdeal (𝓞 K) K
            (Units.mk0 (algebraMap (𝓞 K) K a)
              ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
          rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
          rfl
  exact hmono'

private theorem hk_exists_crt_nonzero_element (D M : Ideal (𝓞 K))
    (hDM : D ⊔ M = ⊤) (hM : M ≠ ⊤) :
    ∃ d : 𝓞 K, d ∈ D ∧ d ≠ 0 ∧ d - 1 ∈ M := by
  obtain ⟨d, hd, e, he, hde⟩ := (Ideal.isCoprime_iff_sup_eq.mpr hDM).exists
  have hdz : d ≠ 0 := by
    intro h0
    have hmem : d + e ∈ M := by simpa [h0] using he
    have hone : (1 : 𝓞 K) ∈ M := by simpa [hde] using hmem
    exact hM (Ideal.eq_top_of_isUnit_mem M hone isUnit_one)
  have hmod : d - 1 ∈ M := by
    have hneg : d - 1 = -e := by
      calc
        d - 1 = d - (d + e) := by rw [← hde]
        _ = -e := by ring
    rw [hneg]
    exact M.neg_mem he
  exact ⟨d, hd, hdz, hmod⟩

private theorem hk_exists_residue_denominator [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d ∈ hk_residue_denominator_ideal
      (A : NumberFieldFractionalIdealGroup K) ∧ d - 1 ∈ modulusIdeal m := by
  classical
  let D := hk_residue_denominator_ideal (A : NumberFieldFractionalIdealGroup K)
  have hD : D ≠ ⊥ := hk_residue_denominator_ideal_ne_bot _
  by_cases hM : modulusIdeal m = ⊤
  · obtain ⟨d, hd, hdz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact ⟨d, hdz, hd, by simp [hM]⟩
  · have hDM : D ⊔ modulusIdeal m = ⊤ := by
      exact ((isCoprimeTo_iff_sup m D).mp
        (hk_residue_denominator_ideal_coprime m A)).2
    obtain ⟨d, hd, hdz, hmod⟩ := hk_exists_crt_nonzero_element D (modulusIdeal m) hDM hM
    exact ⟨d, hdz, hd, hmod⟩

private theorem hk_principal_mul_fractional_le_one
    (I : NumberFieldFractionalIdealGroup K) (a : 𝓞 K) (ha : a ≠ 0)
    (haD : a ∈ hk_residue_denominator_ideal I) :
    (toPrincipalIdeal (𝓞 K) K
      (Units.mk0 (algebraMap (𝓞 K) K a)
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) * I :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 := by
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K
    (Units.mk0 (algebraMap (𝓞 K) K a)
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha))
  have hden : ∀ v : HeightOneSpectrum (𝓞 K),
      hk_residue_denominator_exponent I v ≤ FractionalIdeal.count K v
        (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro v
    exact hk_denominator_count_le_integralPrincipal_count I a ha haD v
  have hnonneg : ∀ v : HeightOneSpectrum (𝓞 K),
      0 ≤ FractionalIdeal.count K v
        (P * I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro v
    have hbase : 0 ≤ hk_residue_denominator_exponent I v +
        NumberFieldFractionalIdealGroup.countVector I v := by
      simp only [hk_residue_denominator_exponent, Finsupp.mapRange_apply]
      omega
    have hIcount : FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          NumberFieldFractionalIdealGroup.countVector I v :=
      (NumberFieldFractionalIdealGroup.countVector_apply I v).symm
    have hmul := FractionalIdeal.count_mul K v (Units.ne_zero P) (Units.ne_zero I)
    calc
      0 ≤ hk_residue_denominator_exponent I v +
          NumberFieldFractionalIdealGroup.countVector I v := hbase
      _ ≤ FractionalIdeal.count K v
            (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
          FractionalIdeal.count K v
            (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
          rw [← hIcount]
          simpa [add_comm] using
            add_le_add_left (hden v) (NumberFieldFractionalIdealGroup.countVector I v)
      _ = FractionalIdeal.count K v
          (P * I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := hmul.symm
  exact hk_fractional_le_one_of_count_nonneg (P * I) hnonneg

private theorem hk_exists_integral_multiple_of_denominator
    (x : Kˣ) (d : 𝓞 K) (hd : d ≠ 0)
    (hden : d ∈ hk_residue_denominator_ideal
      (toPrincipalIdeal (𝓞 K) K x)) :
    ∃ a : 𝓞 K, ∃ ha : a ≠ 0,
      Units.mk0 (algebraMap (𝓞 K) K a)
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha) =
          Units.mk0 (algebraMap (𝓞 K) K d)
            ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd) * x := by
  let dK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K d)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd)
  let yK : Kˣ := dK * x
  have hprincipal : toPrincipalIdeal (𝓞 K) K yK =
      toPrincipalIdeal (𝓞 K) K dK * toPrincipalIdeal (𝓞 K) K x := by
    simp [yK, map_mul]
  have hle : (toPrincipalIdeal (𝓞 K) K yK :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 := by
    rw [hprincipal]
    exact hk_principal_mul_fractional_le_one
      (toPrincipalIdeal (𝓞 K) K x) d hd hden
  have hyMem : (yK : K) ∈
      (toPrincipalIdeal (𝓞 K) K yK : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hyOne : (yK : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := hle hyMem
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 K))).mp hyOne
  have ha0 : a ≠ 0 := by
    intro hz
    have hy0 : (yK : K) = 0 := by simpa [hz] using ha.symm
    exact Units.ne_zero yK hy0
  let aK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha0)
  have hval : (aK : K) = (yK : K) := ha
  refine ⟨a, ha0, ?_⟩
  apply Units.ext
  exact hval

private theorem hk_isCoprimeTo_of_one_modulus {m : RayClassModulus K} (a : 𝓞 K)
    (ha0 : a ≠ 0) (hmod : a - 1 ∈ modulusIdeal m) :
    IsCoprimeTo m (Ideal.span {a}) := by
  have hcomax : Ideal.span {a} ⊔ modulusIdeal m = ⊤ := by
    apply (Ideal.span {a} ⊔ modulusIdeal m).eq_top_iff_one.mpr
    have ha : a ∈ Ideal.span {a} := Ideal.subset_span (by simp)
    have hsum : a - (a - 1) ∈ Ideal.span {a} ⊔ modulusIdeal m :=
      Submodule.sub_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hmod)
    simpa [sub_sub_cancel] using hsum
  exact (isCoprimeTo_iff_sup m (Ideal.span {a})).mpr
    ⟨by simpa using ha0, hcomax⟩

/-- Exact ray primitivity forces ideal primitivity of the residue character.
Uses hk_residue_character_lift, the smaller finite-modulus
construction and the fractional-principal congruence bridge from HK-DICT-RAY. -/
theorem hk_residue_character_primitive [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hp : HKPrimitive ψ)
    (χ₀ : MulChar (HKResidueRing m) ℂ)
    (hχ₀ : ∀ a : 𝓞 K, IsCoprimeTo m (Ideal.span {a}) →
      χ₀ (Ideal.Quotient.mk (modulusIdeal m) a) = charValue ψ (Ideal.span {a})) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ₀ := by
  classical
  intro J hJ
  by_contra hbad
  have hNo : ∀ u : (HKResidueRing m)ˣ, (u : HKResidueRing m) - 1 ∈ J →
      χ₀ (u : HKResidueRing m) = 1 := by
    intro u hu
    by_contra hne
    exact hbad ⟨u, hu, hne⟩
  let M := modulusIdeal m
  let L := Ideal.comap (Ideal.Quotient.mk M) J
  have hM0 : M ≠ ⊥ := modulusIdeal_ne_bot m
  have hML : M ≤ L := by
    intro a ha
    rw [Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha ▸ J.zero_mem
  have hL0 : L ≠ ⊥ := by
    intro hbot
    have hle : M ≤ (⊥ : Ideal (𝓞 K)) := by simpa [L, hbot] using hML
    exact hM0 (bot_unique hle)
  have hLneM : L ≠ M := by
    intro hLM
    have hJbot : J = ⊥ := by
      apply le_antisymm
      · intro z hz
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        have haL : a ∈ L := Ideal.mem_comap.mpr hz
        have haM : a ∈ M := by simpa [L, hLM] using haL
        have hz0 : Ideal.Quotient.mk M a = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr haM
        simpa using hz0
      · exact bot_le
    exact hJ hJbot
  let n := hk_residue_modulus_of_ideal L hL0
  have hnIdeal : modulusIdeal n = L := hk_modulusIdeal_of_ideal L hL0
  have hfinite : n.finitePart ≤ m.finitePart := by
    intro v
    have hcount : factorization L v.asIdeal ≤ factorization M v.asIdeal := by
      rw [factorization_eq_count, factorization_eq_count]
      exact Ideal.count_le_of_ideal_ge hML hM0 v.asIdeal
    have hNexp : n.finitePart v = factorization L v.asIdeal := by
      exact hk_residue_ideal_exponent_apply L hL0 v
    have hMexp : factorization M v.asIdeal = m.finitePart v := by
      have h := hk_modulusIdeal_count m v
      rw [FractionalIdeal.count_coe K v hM0,
        Ideal.count_associates_factors_eq hM0 v.isPrime v.ne_bot] at h
      rw [← factorization_eq_count] at h
      exact_mod_cast h
    rw [hNexp, ← hMexp]
    exact hcount
  have hnm : n ≤ m := ⟨hfinite, Finset.empty_subset _⟩
  have hnNe : n ≠ m := by
    intro h
    apply hLneM
    calc
      L = modulusIdeal n := hnIdeal.symm
      _ = modulusIdeal m := congrArg modulusIdeal h
      _ = M := rfl
  have hFactors : FactorsThrough ψ n := by
    refine ⟨hnm, ?_⟩
    intro x hx hPx
    let Px : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K x, hPx⟩
    obtain ⟨d, hd0, hdD, hdM⟩ := hk_exists_residue_denominator m Px
    let dK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K d)
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd0)
    obtain ⟨a, ha0, haK⟩ := hk_exists_integral_multiple_of_denominator x d hd0
      (by simpa [Px] using hdD)
    have hdN : d - 1 ∈ modulusIdeal n := by
      rw [hnIdeal]
      exact hML hdM
    have hdRay : IsRayCongruent n dK := by
      simpa [dK] using (integral_rayCongruent_iff n d hd0).mpr hdN
    let aK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha0)
    have haK' : aK = dK * x := by simpa [aK, dK] using haK
    have haRay : IsRayCongruent n aK := by
      rw [haK']
      exact ClassFieldTheory.IsRayCongruent.mul hdRay hx
    have haN : a - 1 ∈ modulusIdeal n :=
      (integral_rayCongruent_iff n a ha0).mp (by simpa [aK] using haRay)
    have haL : a - 1 ∈ L := by rw [← hnIdeal]; exact haN
    have hcopD : IsCoprimeTo m (Ideal.span {d}) :=
      hk_isCoprimeTo_of_one_modulus d hd0 hdM
    have hDprime : toPrincipalIdeal (𝓞 K) K dK ∈ rayClassPrimeToIdeals m := by
      rw [← hk_idealUnit_span d hd0]
      exact hcopD.2
    have hYprime : toPrincipalIdeal (𝓞 K) K (dK * x) ∈ rayClassPrimeToIdeals m := by
      rw [map_mul]
      exact (rayClassPrimeToIdeals m).mul_mem hDprime hPx
    have hA0 : Ideal.span {a} ≠ ⊥ := by simpa using ha0
    have hAto : idealUnit (Ideal.span {a}) hA0 =
        toPrincipalIdeal (𝓞 K) K (dK * x) := by
      calc
        idealUnit (Ideal.span {a}) hA0 = toPrincipalIdeal (𝓞 K) K aK :=
          hk_idealUnit_span a ha0
        _ = toPrincipalIdeal (𝓞 K) K (dK * x) := by rw [haK']
    have hcopA : IsCoprimeTo m (Ideal.span {a}) := by
      refine ⟨hA0, ?_⟩
      change idealUnit (Ideal.span {a}) hA0 ∈ rayClassPrimeToIdeals m
      rw [hAto]
      exact hYprime
    let Py : rayClassPrimeToIdeals m := ⟨idealUnit (Ideal.span {a}) hA0, hcopA.2⟩
    let Pd : rayClassPrimeToIdeals m :=
      ⟨idealUnit (Ideal.span {d}) hcopD.1, hcopD.2⟩
    have hPy : Py = Pd * Px := by
      apply Subtype.ext
      change idealUnit (Ideal.span {a}) hA0 =
        idealUnit (Ideal.span {d}) hcopD.1 * toPrincipalIdeal (𝓞 K) K x
      rw [hAto, hk_idealUnit_span d hd0]
      exact map_mul (toPrincipalIdeal (𝓞 K) K) dK x
    have hclass : rayClass m (Ideal.span {a}) hcopA =
        rayClass m (Ideal.span {d}) hcopD * QuotientGroup.mk Px := by
      change QuotientGroup.mk Py = QuotientGroup.mk Pd * QuotientGroup.mk Px
      calc
        QuotientGroup.mk Py = QuotientGroup.mk (Pd * Px) := by rw [hPy]
        _ = QuotientGroup.mk Pd * QuotientGroup.mk Px := by
          rw [← QuotientGroup.mk_mul]
    have hunitA : IsUnit (Ideal.Quotient.mk M a) := hk_isUnit_mk_of_coprime a hcopA
    let uA := hunitA.unit
    have hshift : (uA : HKResidueRing m) - 1 ∈ J := by
      have hmem : Ideal.Quotient.mk M (a - 1) ∈ J := Ideal.mem_comap.mp haL
      rw [hunitA.unit_spec]
      simpa only [map_sub, map_one] using hmem
    have hchiA : χ₀ (Ideal.Quotient.mk M a) = 1 := by
      rw [← hunitA.unit_spec]
      exact hNo uA hshift
    have hcharA : charValue ψ (Ideal.span {a}) = 1 := by
      calc
        charValue ψ (Ideal.span {a}) = χ₀ (Ideal.Quotient.mk M a) :=
          (hχ₀ a hcopA).symm
        _ = 1 := hchiA
    have hpsiA : ψ (rayClass m (Ideal.span {a}) hcopA) = 1 := by
      apply Units.ext
      simpa [charValue, hcopA] using hcharA
    have hdmk : Ideal.Quotient.mk M d = 1 :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr hdM
    have hcharD : charValue ψ (Ideal.span {d}) = 1 := by
      calc
        charValue ψ (Ideal.span {d}) = χ₀ (Ideal.Quotient.mk M d) :=
          (hχ₀ d hcopD).symm
        _ = χ₀ 1 := by rw [hdmk]
        _ = 1 := by simp
    have hpsiD : ψ (rayClass m (Ideal.span {d}) hcopD) = 1 := by
      apply Units.ext
      simpa [charValue, hcopD] using hcharD
    have hpsiX : ψ (QuotientGroup.mk Px) = 1 := by
      have hh := congrArg ψ hclass
      rw [map_mul, hpsiA, hpsiD] at hh
      simpa using hh.symm
    simpa [Px] using hpsiX
  have hdescent := hp n hFactors
  exact hnNe hdescent

end ArtinPrimitiveRoots.Hecke
