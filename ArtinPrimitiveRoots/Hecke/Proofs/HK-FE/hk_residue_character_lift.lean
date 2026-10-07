import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

open IsDedekindDomain

private theorem hk_modulusIdeal_le_primePower (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
    modulusIdeal m ≤ v.asIdeal ^ m.finitePart v := by
  change (∏ w ∈ m.finitePart.support, w.asIdeal ^ m.finitePart w) ≤ _
  exact (Ideal.prod_le_inf (s := m.finitePart.support)
    (f := fun w => w.asIdeal ^ m.finitePart w)).trans (Finset.inf_le hv)

private theorem hk_idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem hk_isCoprimeTo_mul {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) : IsCoprimeTo m (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  rw [hk_idealUnit_mul I J hI.1 hJ.1 (mul_ne_zero hI.1 hJ.1)]
  exact (rayClassPrimeToIdeals m).mul_mem hI.2 hJ.2

private theorem hk_rayClass_mul {m : RayClassModulus K} (I J : Ideal (𝓞 K))
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m (I * J) (hk_isCoprimeTo_mul hI hJ) =
      rayClass m I hI * rayClass m J hJ := by
  change QuotientGroup.mk
      (⟨idealUnit (I * J) _, _⟩ : rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨idealUnit I hI.1, hI.2⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨idealUnit J hJ.1, hJ.2⟩ : rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hk_idealUnit_mul I J hI.1 hJ.1 (mul_ne_zero hI.1 hJ.1))

private theorem hk_rayClass_eq_of_ideals_eq {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hIJ : I = J) (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m I hI = rayClass m J hJ := by
  cases hIJ
  have hp : hI = hJ := Subsingleton.elim _ _
  subst hJ
  rfl

theorem hk_idealUnit_span (a : 𝓞 K) (ha : a ≠ 0) :
    idealUnit (Ideal.span {a}) (mt Ideal.span_singleton_eq_bot.mp ha) =
      toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) := by
  apply Units.ext
  change (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

private theorem hk_integralFieldUnit_mul (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Units.mk0 (algebraMap (𝓞 K) K (a * b))
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (mul_ne_zero ha hb)) =
      Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha) *
        Units.mk0 (algebraMap (𝓞 K) K b)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hb) := by
  apply Units.ext
  change algebraMap (𝓞 K) K (a * b) =
    algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K b
  exact map_mul (algebraMap (𝓞 K) K) a b

private theorem hk_no_support_of_coprime {m : RayClassModulus K} (a : 𝓞 K)
    (ha0 : a ≠ 0) (ha : IsCoprimeTo m (Ideal.span {a}))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) : a ∉ v.asIdeal := by
  intro hav
  let I : Ideal (𝓞 K) := Ideal.span {a}
  have hI0 : I ≠ ⊥ := by
    simpa [I] using ha0
  have hcount : FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
    have h := ha.2 v hv
    simpa [I, idealUnit] using h
  have hcountNat : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
    have h' := hcount
    rw [FractionalIdeal.count_coe K v hI0,
      Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot] at h'
    exact_mod_cast h'
  have hfac : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    (Ideal.mem_normalizedFactors_iff hI0).mpr
      ⟨v.isPrime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hav)⟩
  have hcount' : 0 < Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) := Multiset.count_pos.mpr hfac
  omega

set_option maxHeartbeats 1000000 in
private theorem hk_coprime_span_modulus_of_no_support (m : RayClassModulus K)
    (a : 𝓞 K) (hno : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ m.finitePart.support → a ∉ v.asIdeal) :
    Ideal.span {a} ⊔ modulusIdeal m = ⊤ := by
  classical
  have hspanv (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
      IsCoprime (Ideal.span {a}) v.asIdeal := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_cases htop : Ideal.span {a} ⊔ v.asIdeal = ⊤
    · exact htop
    · have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
      have heq : v.asIdeal = Ideal.span {a} ⊔ v.asIdeal :=
        hmax.eq_of_le htop le_sup_right
      have hle : Ideal.span {a} ≤ v.asIdeal := by
        rw [heq]
        exact le_sup_left
      have haV : a ∈ v.asIdeal := hle (Ideal.subset_span (by simp))
      exact False.elim ((hno v hv) haV)
  have hspanpow (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
      IsCoprime (Ideal.span {a}) (v.asIdeal ^ m.finitePart v) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    simpa only [pow_one] using
      (Ideal.pow_sup_pow_eq_top (m := 1) (n := m.finitePart v)
        (hspanv v hv).sup_eq)
  change Ideal.span {a} ⊔
      (∏ v ∈ m.finitePart.support, v.asIdeal ^ m.finitePart v) = ⊤
  exact Ideal.sup_prod_eq_top (I := Ideal.span {a}) fun v hv =>
    (hspanpow v hv).sup_eq

private theorem hk_isCoprimeTo_of_no_support {m : RayClassModulus K} (a : 𝓞 K)
    (ha0 : a ≠ 0) (hno : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ m.finitePart.support → a ∉ v.asIdeal) :
    IsCoprimeTo m (Ideal.span {a}) := by
  have hI0 : Ideal.span {a} ≠ ⊥ := by simpa using ha0
  refine ⟨hI0, ?_⟩
  change ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (idealUnit (Ideal.span {a}) hI0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  intro v hv
  have hcount : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    have hfac := (Ideal.mem_normalizedFactors_iff hI0).mp hmem
    exact hno v hv (hfac.2 (Ideal.subset_span (by simp)))
  have hcount' : FractionalIdeal.count K v
      (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
    rw [FractionalIdeal.count_coe K v hI0,
      Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
    exact_mod_cast hcount
  simpa [idealUnit] using hcount'

private theorem hk_isCoprimeTo_of_isUnit {m : RayClassModulus K} (a : 𝓞 K)
    (ha0 : a ≠ 0) (hu : IsUnit (Ideal.Quotient.mk (modulusIdeal m) a)) :
    IsCoprimeTo m (Ideal.span {a}) := by
  have hcomax : Ideal.span {a} ⊔ modulusIdeal m = ⊤ := by
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmod : a * b - 1 ∈ modulusIdeal m := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, hb, map_one, sub_self]
    apply (Ideal.span {a} ⊔ modulusIdeal m).eq_top_iff_one.mpr
    have hA : a * b ∈ Ideal.span {a} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_right a b)
    have hsum : a * b - (a * b - 1) ∈ Ideal.span {a} ⊔ modulusIdeal m :=
      Submodule.sub_mem _ (Submodule.mem_sup_left hA) (Submodule.mem_sup_right hmod)
    simpa [sub_sub_cancel] using hsum
  have hno : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ m.finitePart.support → a ∉ v.asIdeal := by
    intro v hv hav
    have he : 0 < m.finitePart v := Nat.pos_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hv)
    have hMle : modulusIdeal m ≤ v.asIdeal :=
      (hk_modulusIdeal_le_primePower m v hv).trans
        (Ideal.pow_le_self (I := v.asIdeal) (Nat.ne_of_gt he))
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := by
      rw [← hcomax]
      exact sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hav)) hMle
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  exact hk_isCoprimeTo_of_no_support a ha0 hno

theorem hk_isUnit_mk_of_coprime {m : RayClassModulus K} (a : 𝓞 K)
    (ha : IsCoprimeTo m (Ideal.span {a})) :
    IsUnit (Ideal.Quotient.mk (modulusIdeal m) a) := by
  have ha0 : a ≠ 0 := by
    intro hz
    apply ha.1
    simpa [hz]
  have hno := fun v hv => hk_no_support_of_coprime a ha0 ha v hv
  have hcomax := hk_coprime_span_modulus_of_no_support m a hno
  have hmem : (1 : 𝓞 K) ∈ Ideal.span {a} ⊔ modulusIdeal m := by
    rw [hcomax]
    trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk (modulusIdeal m) b, ?_⟩
  have heq := congrArg (Ideal.Quotient.mk (modulusIdeal m)) hxy
  simpa only [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] using heq

private noncomputable def hkResidueLift (m : RayClassModulus K)
    (u : (HKResidueRing m)ˣ) : 𝓞 K := by
  classical
  exact if htop : modulusIdeal m = ⊤ then 1
    else if hu : u = 1 then 1
    else Classical.choose (Ideal.Quotient.mk_surjective (u : HKResidueRing m))

private theorem hkResidueLift_spec (m : RayClassModulus K) (u : (HKResidueRing m)ˣ) :
    Ideal.Quotient.mk (modulusIdeal m) (hkResidueLift m u) = (u : HKResidueRing m) := by
  classical
  by_cases htop : modulusIdeal m = ⊤
  · have hs : Subsingleton (HKResidueRing m) :=
      (Ideal.Quotient.subsingleton_iff).2 htop
    exact hs.elim _ _
  · by_cases hu : u = 1
    · simp [hkResidueLift, htop, hu]
    · simpa [hkResidueLift, htop, hu] using
        (Classical.choose_spec (Ideal.Quotient.mk_surjective (u : HKResidueRing m)))

private theorem hkResidueLift_ne_zero (m : RayClassModulus K) (u : (HKResidueRing m)ˣ) :
    hkResidueLift m u ≠ 0 := by
  classical
  by_cases htop : modulusIdeal m = ⊤
  · simp [hkResidueLift, htop]
  · by_cases hu : u = 1
    · simp [hkResidueLift, htop, hu]
    · intro hz
      have hu0 : (u : HKResidueRing m) = 0 := by
        calc
          (u : HKResidueRing m) = Ideal.Quotient.mk (modulusIdeal m) (hkResidueLift m u) :=
            (hkResidueLift_spec m u).symm
          _ = 0 := by simp [hz]
      have h01 : (0 : HKResidueRing m) = 1 := by
        calc
          (0 : HKResidueRing m) = (u : HKResidueRing m) * (↑(u⁻¹) : HKResidueRing m) := by
            simp [hu0]
          _ = 1 := by simpa using congrArg Units.val (mul_inv_cancel u)
      exact htop (Ideal.Quotient.zero_eq_one_iff.mp h01)

private theorem hkResidueLift_coprime (m : RayClassModulus K)
    (u : (HKResidueRing m)ˣ) : IsCoprimeTo m (Ideal.span {hkResidueLift m u}) := by
  apply hk_isCoprimeTo_of_isUnit (hkResidueLift m u) (hkResidueLift_ne_zero m u)
  rw [hkResidueLift_spec]
  exact u.isUnit

private theorem hk_rayClass_span_eq_of_residue_eq [IsTotallyComplex K] {m : RayClassModulus K}
    (a b : 𝓞 K) (ha : IsCoprimeTo m (Ideal.span {a}))
    (hb : IsCoprimeTo m (Ideal.span {b}))
    (hres : Ideal.Quotient.mk (modulusIdeal m) a =
      Ideal.Quotient.mk (modulusIdeal m) b) :
    rayClass m (Ideal.span {a}) ha = rayClass m (Ideal.span {b}) hb := by
  classical
  let ua : (HKResidueRing m)ˣ :=
    (hk_isUnit_mk_of_coprime a ha).unit
  have hua : (ua : HKResidueRing m) = Ideal.Quotient.mk (modulusIdeal m) a :=
    (hk_isUnit_mk_of_coprime a ha).unit_spec
  let c := hkResidueLift m ua⁻¹
  have hc0 : c ≠ 0 := hkResidueLift_ne_zero m ua⁻¹
  have hmc : Ideal.Quotient.mk (modulusIdeal m) c =
      ((ua⁻¹ : (HKResidueRing m)ˣ) : HKResidueRing m) :=
    hkResidueLift_spec m ua⁻¹
  have hac : Ideal.Quotient.mk (modulusIdeal m) (a * c) = 1 := by
    calc
      Ideal.Quotient.mk (modulusIdeal m) (a * c) =
          (ua : HKResidueRing m) * ((ua⁻¹ : (HKResidueRing m)ˣ) : HKResidueRing m) := by
            rw [map_mul, ← hua, hmc]
      _ = 1 := by simpa using congrArg Units.val (mul_inv_cancel ua)
  have hbc : Ideal.Quotient.mk (modulusIdeal m) (b * c) = 1 := by
    calc
      Ideal.Quotient.mk (modulusIdeal m) (b * c) =
          (ua : HKResidueRing m) * ((ua⁻¹ : (HKResidueRing m)ˣ) : HKResidueRing m) := by
            rw [map_mul, ← hres, ← hua, hmc]
      _ = 1 := by simpa using congrArg Units.val (mul_inv_cancel ua)
  have hacM : a * c - 1 ∈ modulusIdeal m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hac, map_one, sub_self]
  have hbcM : b * c - 1 ∈ modulusIdeal m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hbc, map_one, sub_self]
  have ha0 : a ≠ 0 := by
    intro hz
    exact ha.1 (by simpa [hz])
  have hb0 : b ≠ 0 := by
    intro hz
    exact hb.1 (by simpa [hz])
  let xa : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha0)
  let xb : Kˣ := Units.mk0 (algebraMap (𝓞 K) K b)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hb0)
  let xc : Kˣ := Units.mk0 (algebraMap (𝓞 K) K c)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hc0)
  let xac : Kˣ := Units.mk0 (algebraMap (𝓞 K) K (a * c))
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (mul_ne_zero ha0 hc0))
  let xbc : Kˣ := Units.mk0 (algebraMap (𝓞 K) K (b * c))
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (mul_ne_zero hb0 hc0))
  have hxac : xac = xa * xc := hk_integralFieldUnit_mul a c ha0 hc0
  have hxbc : xbc = xb * xc := hk_integralFieldUnit_mul b c hb0 hc0
  have hxacRay : IsRayCongruent m xac :=
    (integral_rayCongruent_iff m (a * c) (mul_ne_zero ha0 hc0)).mpr hacM
  have hxbcRay : IsRayCongruent m xbc :=
    (integral_rayCongruent_iff m (b * c) (mul_ne_zero hb0 hc0)).mpr hbcM
  have hratio : xac * xbc⁻¹ = xa * xb⁻¹ := by
    rw [hxac, hxbc]
    group
  have hratioRay : IsRayCongruent m (xa * xb⁻¹) := by
    have h := ClassFieldTheory.IsRayCongruent.mul hxacRay
      (ClassFieldTheory.IsRayCongruent.inv hxbcRay)
    rw [hratio] at h
    exact h
  have hspanA : idealUnit (Ideal.span {a}) ha.1 = toPrincipalIdeal (𝓞 K) K xa :=
    hk_idealUnit_span a ha0
  have hspanB : idealUnit (Ideal.span {b}) hb.1 = toPrincipalIdeal (𝓞 K) K xb :=
    hk_idealUnit_span b hb0
  let P : rayClassPrimeToIdeals m :=
    ⟨idealUnit (Ideal.span {a}) ha.1 / idealUnit (Ideal.span {b}) hb.1,
      (rayClassPrimeToIdeals m).div_mem ha.2 hb.2⟩
  have hprincipal : toPrincipalIdeal (𝓞 K) K (xa * xb⁻¹) = (P : NumberFieldFractionalIdealGroup K) := by
    change toPrincipalIdeal (𝓞 K) K (xa * xb⁻¹) =
      idealUnit (Ideal.span {a}) ha.1 / idealUnit (Ideal.span {b}) hb.1
    rw [map_mul, map_inv, hspanA, hspanB, div_eq_mul_inv]
  have hPmem : P ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m P).mpr
      ⟨xa * xb⁻¹, hratioRay, hprincipal⟩
  have hquot : rayClass m (Ideal.span {a}) ha /
      rayClass m (Ideal.span {b}) hb = 1 := by
    change QuotientGroup.mk
      ((⟨idealUnit (Ideal.span {a}) ha.1, ha.2⟩ : rayClassPrimeToIdeals m) /
        ⟨idealUnit (Ideal.span {b}) hb.1, hb.2⟩) = 1
    change QuotientGroup.mk P = 1
    exact (QuotientGroup.eq_one_iff (N := rayPrincipalIdealSubgroupInPrimeTo m) P).mpr hPmem
  exact (div_eq_one.mp hquot)

private theorem hk_rayClass_span_mul {m : RayClassModulus K} (a b : 𝓞 K)
    (ha : IsCoprimeTo m (Ideal.span {a}))
    (hb : IsCoprimeTo m (Ideal.span {b}))
    (hab : IsCoprimeTo m (Ideal.span {a * b})) :
    rayClass m (Ideal.span {a * b}) hab =
      rayClass m (Ideal.span {a}) ha * rayClass m (Ideal.span {b}) hb := by
  have hspan : Ideal.span {a} * Ideal.span {b} = Ideal.span {a * b} :=
    Ideal.span_singleton_mul_span_singleton a b
  have hab' : IsCoprimeTo m (Ideal.span {a} * Ideal.span {b}) := hspan.symm ▸ hab
  have hprod := hk_isCoprimeTo_mul ha hb
  have hproof : hab' = hprod := Subsingleton.elim _ _
  have hclass := hk_rayClass_eq_of_ideals_eq hspan.symm hab hab'
  calc
    rayClass m (Ideal.span {a * b}) hab =
        rayClass m (Ideal.span {a} * Ideal.span {b}) hab' := hclass
    _ = rayClass m (Ideal.span {a} * Ideal.span {b}) hprod := by
      rw [hproof]
    _ = rayClass m (Ideal.span {a}) ha * rayClass m (Ideal.span {b}) hb :=
      hk_rayClass_mul (Ideal.span {a}) (Ideal.span {b}) ha hb

private noncomputable def hkResidueUnitsHom [IsTotallyComplex K] (m : RayClassModulus K)
    (ψ : RayClassGroup m →* ℂˣ) : (HKResidueRing m)ˣ →* ℂˣ where
  toFun u := ψ (rayClass m (Ideal.span {hkResidueLift m u}) (hkResidueLift_coprime m u))
  map_one' := by
    classical
    have htop : IsCoprimeTo m (⊤ : Ideal (𝓞 K)) := by
      refine ⟨by simp [Ideal.one_eq_top], ?_⟩
      intro v hv
      simpa [idealUnit] using (FractionalIdeal.count_one K v)
    have hspan : Ideal.span {(1 : 𝓞 K)} = (⊤ : Ideal (𝓞 K)) := by simp
    have hcopSpan : IsCoprimeTo m (Ideal.span {(1 : 𝓞 K)}) := hspan.symm ▸ htop
    have hclassTop : rayClass m (⊤ : Ideal (𝓞 K)) htop = 1 := by
      change QuotientGroup.mk
        (⟨idealUnit (⊤ : Ideal (𝓞 K)) htop.1, htop.2⟩ : rayClassPrimeToIdeals m) = 1
      have hrep : (⟨idealUnit (⊤ : Ideal (𝓞 K)) htop.1, htop.2⟩ :
          rayClassPrimeToIdeals m) = 1 := by
        apply Subtype.ext
        apply Units.ext
        change ((⊤ : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1
        exact FractionalIdeal.coeIdeal_eq_one.mpr (by simp)
      rw [hrep]
      simp
    have hclass : rayClass m (Ideal.span {(1 : 𝓞 K)}) hcopSpan = 1 := by
      calc
        rayClass m (Ideal.span {(1 : 𝓞 K)}) hcopSpan = rayClass m ⊤ htop := by
          exact hk_rayClass_eq_of_ideals_eq hspan hcopSpan htop
        _ = 1 := hclassTop
    have hlift : hkResidueLift m 1 = 1 := by
      simp [hkResidueLift]
    have hspanLift : Ideal.span {hkResidueLift m (1 : (HKResidueRing m)ˣ)} =
        Ideal.span {(1 : 𝓞 K)} := by rw [hlift]
    have hclassLift : rayClass m (Ideal.span {hkResidueLift m (1 : (HKResidueRing m)ˣ)})
        (hkResidueLift_coprime m 1) = rayClass m (Ideal.span {(1 : 𝓞 K)}) hcopSpan :=
      hk_rayClass_eq_of_ideals_eq hspanLift (hkResidueLift_coprime m 1) hcopSpan
    change ψ (rayClass m (Ideal.span {hkResidueLift m (1 : (HKResidueRing m)ˣ)})
      (hkResidueLift_coprime m 1)) = 1
    rw [hclassLift, hclass]
    exact map_one ψ
  map_mul' u v := by
    let a := hkResidueLift m u
    let b := hkResidueLift m v
    let c := hkResidueLift m (u * v)
    have hres : Ideal.Quotient.mk (modulusIdeal m) c =
        Ideal.Quotient.mk (modulusIdeal m) (a * b) := by
      calc
        Ideal.Quotient.mk (modulusIdeal m) c = (u * v : (HKResidueRing m)) :=
          hkResidueLift_spec m (u * v)
        _ = (u : HKResidueRing m) * (v : HKResidueRing m) := rfl
        _ = Ideal.Quotient.mk (modulusIdeal m) a *
            Ideal.Quotient.mk (modulusIdeal m) b := by
              rw [hkResidueLift_spec, hkResidueLift_spec]
        _ = Ideal.Quotient.mk (modulusIdeal m) (a * b) := (map_mul _ _ _).symm
    have hcopA := hkResidueLift_coprime m u
    have hcopB := hkResidueLift_coprime m v
    have hcopC := hkResidueLift_coprime m (u * v)
    have hcopAB : IsCoprimeTo m (Ideal.span {a * b}) := by
      apply hk_isCoprimeTo_of_isUnit (a * b)
        (mul_ne_zero (hkResidueLift_ne_zero m u) (hkResidueLift_ne_zero m v))
      rw [← hres, hkResidueLift_spec]
      exact (u * v).isUnit
    have hclass := hk_rayClass_span_eq_of_residue_eq c (a * b) hcopC hcopAB hres
    rw [hclass, hk_rayClass_span_mul a b hcopA hcopB hcopAB, map_mul]

private theorem hkResidueUnitsHom_principal_value [IsTotallyComplex K] (m : RayClassModulus K)
    (ψ : RayClassGroup m →* ℂˣ) (a : 𝓞 K)
    (ha : IsCoprimeTo m (Ideal.span {a})) :
    (hkResidueUnitsHom m ψ) ((hk_isUnit_mk_of_coprime a ha).unit :
        (HKResidueRing m)ˣ) = ψ (rayClass m (Ideal.span {a}) ha) := by
  let u := (hk_isUnit_mk_of_coprime a ha).unit
  have hu : (u : HKResidueRing m) = Ideal.Quotient.mk (modulusIdeal m) a :=
    (hk_isUnit_mk_of_coprime a ha).unit_spec
  have hclass : rayClass m (Ideal.span {hkResidueLift m u})
      (hkResidueLift_coprime m u) = rayClass m (Ideal.span {a}) ha :=
    hk_rayClass_span_eq_of_residue_eq (hkResidueLift m u) a
      (hkResidueLift_coprime m u) ha (by rw [hkResidueLift_spec, hu])
  change ψ (rayClass m (Ideal.span {hkResidueLift m u})
    (hkResidueLift_coprime m u)) = _
  exact congrArg ψ hclass


/-- Construct a residue character by prime-to integral lifts. Guide:
sol-thin-hk2/PROOFS.md:1209–1230. Uses H1's residue/congruence bridge and MulChar.ofUnitHom;
at the unit ideal choose the integral lift 1 explicitly. -/
theorem hk_residue_character_lift [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) :
    ∃ χ₀ : MulChar (HKResidueRing m) ℂ, ∀ a : 𝓞 K,
      IsCoprimeTo m (Ideal.span {a}) →
        χ₀ (Ideal.Quotient.mk (modulusIdeal m) a) = charValue ψ (Ideal.span {a}) := by
  refine ⟨MulChar.ofUnitHom (hkResidueUnitsHom m ψ), ?_⟩
  intro a ha
  have hunit : IsUnit (Ideal.Quotient.mk (modulusIdeal m) a) :=
    hk_isUnit_mk_of_coprime a ha
  let u := hunit.unit
  have hu : (u : HKResidueRing m) = Ideal.Quotient.mk (modulusIdeal m) a := hunit.unit_spec
  calc
    MulChar.ofUnitHom (hkResidueUnitsHom m ψ)
        (Ideal.Quotient.mk (modulusIdeal m) a) =
      MulChar.ofUnitHom (hkResidueUnitsHom m ψ) (u : HKResidueRing m) := by rw [← hu]
    _ = ((hkResidueUnitsHom m ψ) u : ℂ) := by rw [MulChar.ofUnitHom_coe]
    _ = (ψ (rayClass m (Ideal.span {a}) ha) : ℂ) := by
      rw [hkResidueUnitsHom_principal_value m ψ a ha]
    _ = charValue ψ (Ideal.span {a}) := by
      simp [charValue, ha]

end ArtinPrimitiveRoots.Hecke
