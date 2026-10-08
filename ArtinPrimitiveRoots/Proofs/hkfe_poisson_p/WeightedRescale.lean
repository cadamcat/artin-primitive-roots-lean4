import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_point_ideal_integral
import ArtinPrimitiveRoots.Hecke.Theta.RayTheta
import DedekindResidue.CompletedZeta.ClassTheta

set_option autoImplicit false

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  ClassFieldTheory DedekindResidue MeasureTheory ArtinPrimitiveRoots.Hecke.Theta
open NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Real Classical RealInnerProductSpace

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

private def hkPrincipalRayIdeal [IsTotallyComplex K]
    (m : RayClassModulus K) (hm : m.finitePart = 0) (y : Kˣ) :
    rayClassPrimeToIdeals m :=
  ⟨toPrincipalIdeal (𝓞 K) K y, by
    intro v hv
    have hfalse : False := by simpa [hm] using hv
    exact hfalse.elim⟩

private theorem hk_principal_raySubgroup_of_finitePart_zero [IsTotallyComplex K]
    {m : RayClassModulus K} (hm : m.finitePart = 0) (y : Kˣ) :
    hkPrincipalRayIdeal m hm y ∈ rayPrincipalIdealSubgroupInPrimeTo m := by
  have hyRay : IsRayCongruent m y := by
    constructor
    · intro v hv
      have hfalse : False := by simpa [hm] using hv
      exact hfalse.elim
    · intro v hv
      have hfalse : False := by
        rw [rayClassModulus_infinitePart_eq_empty (K := K) m] at hv
        simpa using hv
      exact hfalse.elim
  exact (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m (hkPrincipalRayIdeal m hm y)).2
    ⟨y, hyRay, rfl⟩

private theorem hk_fractionalCharValue_principal_mul [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (hm : m.finitePart = 0) (I : NumberFieldFractionalIdealGroup K) (y : Kˣ) :
    hkFractionalCharValue ψ ((toPrincipalIdeal (𝓞 K) K y * I)⁻¹) =
      hkFractionalCharValue ψ (I⁻¹) := by
  classical
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K y
  let A : rayClassPrimeToIdeals m := hkPrincipalRayIdeal m hm y
  have hAsub : A ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    hk_principal_raySubgroup_of_finitePart_zero hm y
  have hprime (J : NumberFieldFractionalIdealGroup K) :
      J ∈ rayClassPrimeToIdeals m := by
    intro v hv
    have hfalse : False := by simpa [hm] using hv
    exact hfalse.elim
  let B : rayClassPrimeToIdeals m := ⟨I⁻¹, hprime _⟩
  let C : rayClassPrimeToIdeals m := ⟨(P * I)⁻¹, hprime _⟩
  have hCA : C = B * A⁻¹ := by
    apply Subtype.ext
    change (P * I)⁻¹ = I⁻¹ * P⁻¹
    rw [mul_inv_rev]
  let q : rayClassPrimeToIdeals m →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  have hqA : q A = 1 :=
    (QuotientGroup.eq_one_iff (N := rayPrincipalIdealSubgroupInPrimeTo m) A).mpr hAsub
  have hqAinv : q A⁻¹ = 1 := by simp [map_inv, hqA]
  have hqCB : q C = q B := by
    calc
      q C = q B * q A⁻¹ := by rw [hCA, map_mul]
      _ = q B := by rw [hqAinv]; exact mul_one (q B)
  change hkFractionalCharValue ψ (C : NumberFieldFractionalIdealGroup K) =
    hkFractionalCharValue ψ (B : NumberFieldFractionalIdealGroup K)
  calc
    hkFractionalCharValue ψ (C : NumberFieldFractionalIdealGroup K) =
        (ψ (q C) : ℂ) := by simp [hkFractionalCharValue, q, C.property]
    _ = (ψ (q B) : ℂ) := congrArg (fun z : RayClassGroup m => (ψ z : ℂ)) hqCB
    _ = hkFractionalCharValue ψ (B : NumberFieldFractionalIdealGroup K) := by
        simp [hkFractionalCharValue, q, B.property]

private theorem hk_span_coprime_iff_unit_residue {m : RayClassModulus K}
    {x : 𝓞 K} (hx : x ≠ 0) :
    IsCoprimeTo m (Ideal.span {x}) ↔
      IsUnit (Ideal.Quotient.mk (modulusIdeal m) x) := by
  rw [isCoprimeTo_iff_sup]
  have hspan : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp hx
  constructor
  · rintro ⟨_, hsup⟩
    have hcop : IsCoprime (Ideal.span ({x} : Set (𝓞 K))) (modulusIdeal m) :=
      Ideal.isCoprime_iff_sup_eq.mpr hsup
    obtain ⟨a, ha, b, hb, hab⟩ := hcop.exists
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp ha
    have hmk1 : Ideal.Quotient.mk (modulusIdeal m) a = 1 := by
      have h := congrArg (Ideal.Quotient.mk (modulusIdeal m)) hab
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one] at h
      exact h
    have hmul :
        Ideal.Quotient.mk (modulusIdeal m) x *
          Ideal.Quotient.mk (modulusIdeal m) z = 1 := by
      calc
        Ideal.Quotient.mk (modulusIdeal m) x *
            Ideal.Quotient.mk (modulusIdeal m) z =
            Ideal.Quotient.mk (modulusIdeal m) (z * x) := by rw [map_mul, mul_comm]
        _ = 1 := by
          calc
            Ideal.Quotient.mk (modulusIdeal m) (z * x) =
                Ideal.Quotient.mk (modulusIdeal m) (x * z) := by rw [mul_comm]
            _ = Ideal.Quotient.mk (modulusIdeal m) a := by rw [hz]
            _ = 1 := hmk1
    exact (isUnit_iff_exists).2 ⟨Ideal.Quotient.mk (modulusIdeal m) z, hmul,
      by simpa [mul_comm] using hmul⟩
  · intro hunit
    obtain ⟨z, hxz, hzx⟩ := (isUnit_iff_exists.mp hunit)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hmk1 : Ideal.Quotient.mk (modulusIdeal m) (x * a) = 1 := by
      simpa [map_mul] using hxz
    have hmod : x * a - 1 ∈ modulusIdeal m :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := modulusIdeal m) _ _).mp hmk1
    have hneg : -(x * a - 1) = 1 - x * a := by ring
    have hmem : 1 - x * a ∈ modulusIdeal m := by
      have h := (modulusIdeal m).neg_mem hmod
      rw [hneg] at h
      exact h
    have hcop : IsCoprime (Ideal.span ({x} : Set (𝓞 K))) (modulusIdeal m) :=
      (Ideal.isCoprime_iff_exists).2
        ⟨x * a, Ideal.mem_span_singleton.mpr ⟨a, by ring⟩,
          1 - x * a, hmem, by ring⟩
    have hsup := Ideal.isCoprime_iff_sup_eq.mp hcop
    exact ⟨hspan, hsup⟩

private theorem hk_coprimeTo_principal_congruence [IsTotallyComplex K]
    {m : RayClassModulus K} (A B : Ideal (𝓞 K)) (hA0 : A ≠ ⊥) (hB0 : B ≠ ⊥)
    (q : Kˣ)
    (hAB : (A : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) *
        (B : FractionalIdeal (𝓞 K)⁰ K))
    (hcong : (q : K) - 1 ∈
      (((hkModulusUnit m * (idealUnit B hB0)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K))) :
    IsCoprimeTo m A ↔ IsCoprimeTo m B := by
  classical
  have hAiff := isCoprimeTo_iff_sup m A
  have hBiff := isCoprimeTo_iff_sup m B
  have hBcoe : (B : FractionalIdeal (𝓞 K)⁰ K) =
      (idealUnit B hB0 : FractionalIdeal (𝓞 K)⁰ K) := by
    simp [idealUnit]
  rw [hAiff, hBiff]
  constructor
  · rintro ⟨_, hAsup⟩
    have hAM : IsCoprime A (modulusIdeal m) :=
      Ideal.isCoprime_iff_sup_eq.mpr hAsup
    obtain ⟨a, ha, b, hb, hab⟩ := hAM.exists
    have haF : (algebraMap (𝓞 K) K a) ∈ (A : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) ha
    rw [hAB] at haF
    obtain ⟨x, hxF, hax⟩ := (FractionalIdeal.mem_singleton_mul).mp haF
    obtain ⟨x₀, hx₀, hxval⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hxF
    have hcrossF := FractionalIdeal.mul_mem_mul hcong
      (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hx₀)
    rw [hBcoe] at hcrossF
    have hcancel : hkModulusUnit m * (idealUnit B hB0)⁻¹ *
        idealUnit B hB0 = hkModulusUnit m := by group
    have hcross' : ((q : K) - 1) * (algebraMap (𝓞 K) K x₀) ∈
        (((hkModulusUnit m : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K)) := by
      have hcrossGroup : ((q : K) - 1) * (algebraMap (𝓞 K) K x₀) ∈
          (((hkModulusUnit m * (idealUnit B hB0)⁻¹ * idealUnit B hB0 :
            NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)) := by
        simpa only [← Units.val_mul] using hcrossF
      rw [hcancel] at hcrossGroup
      exact hcrossGroup
    obtain ⟨d, hd, hdval⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hcross'
    have hcomb : x₀ + (b + d) = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      calc
        algebraMap (𝓞 K) K (x₀ + (b + d)) =
            (algebraMap (𝓞 K) K x₀) +
              ((algebraMap (𝓞 K) K b) + (algebraMap (𝓞 K) K d)) := by simp
        _ = (q : K) * (algebraMap (𝓞 K) K x₀) +
              algebraMap (𝓞 K) K b := by rw [hdval]; ring
        _ = algebraMap (𝓞 K) K a + algebraMap (𝓞 K) K b := by
              rw [← hxval] at hax
              rw [← hax]
        _ = 1 := by exact_mod_cast hab
    have hBM : IsCoprime B (modulusIdeal m) :=
      (Ideal.isCoprime_iff_exists).mpr
        ⟨x₀, hx₀, b + d, Ideal.add_mem _ hb hd, hcomb⟩
    exact ⟨hB0, Ideal.isCoprime_iff_sup_eq.mp hBM⟩
  · rintro ⟨_, hBsup⟩
    have hBM : IsCoprime B (modulusIdeal m) :=
      Ideal.isCoprime_iff_sup_eq.mpr hBsup
    obtain ⟨b, hb, c, hc, hbc⟩ := hBM.exists
    have hbF : (algebraMap (𝓞 K) K b) ∈ (B : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hb
    have hqbf : (q : K) * algebraMap (𝓞 K) K b ∈
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) *
          (B : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_singleton_mul).mpr ⟨algebraMap (𝓞 K) K b, hbF, rfl⟩
    rw [← hAB] at hqbf
    obtain ⟨a, ha, haval⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hqbf
    have hcrossF := FractionalIdeal.mul_mem_mul hcong hbF
    rw [hBcoe] at hcrossF
    have hcross' : ((q : K) - 1) * algebraMap (𝓞 K) K b ∈
        (((hkModulusUnit m : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K)) := by
      have hcrossGroup : ((q : K) - 1) * algebraMap (𝓞 K) K b ∈
          (((hkModulusUnit m * (idealUnit B hB0)⁻¹ * idealUnit B hB0 :
            NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)) := by
        simpa only [← Units.val_mul] using hcrossF
      have hcancel' : hkModulusUnit m * (idealUnit B hB0)⁻¹ *
          idealUnit B hB0 = hkModulusUnit m := by group
      rw [hcancel'] at hcrossGroup
      exact hcrossGroup
    obtain ⟨d, hd, hdval⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hcross'
    have hcomb : a + (c - d) = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      calc
        algebraMap (𝓞 K) K (a + (c - d)) =
            algebraMap (𝓞 K) K a +
              (algebraMap (𝓞 K) K c - algebraMap (𝓞 K) K d) := by simp
        _ = (q : K) * algebraMap (𝓞 K) K b +
              (algebraMap (𝓞 K) K c - algebraMap (𝓞 K) K d) := by rw [haval]
        _ = algebraMap (𝓞 K) K b + algebraMap (𝓞 K) K c := by rw [hdval]; ring
        _ = 1 := by exact_mod_cast hbc
    have hAM : IsCoprime A (modulusIdeal m) :=
      (Ideal.isCoprime_iff_exists).mpr
        ⟨a, ha, c - d, Ideal.sub_mem _ hc hd, hcomb⟩
    exact ⟨hA0, Ideal.isCoprime_iff_sup_eq.mp hAM⟩

private theorem hk_idealUnit_span (x : 𝓞 K) (hx : x ≠ 0) :
    idealUnit (Ideal.span ({x} : Set (𝓞 K))) (mt Ideal.span_singleton_eq_bot.mp hx) =
      toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K x)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hx)) := by
  apply Units.ext
  rw [idealUnit, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton,
    coe_toPrincipalIdeal]
  rfl

private theorem hk_idealUnit_mul (A B : Ideal (𝓞 K)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hAB : A * B ≠ ⊥) :
    idealUnit (A * B) hAB = idealUnit A hA * idealUnit B hB := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem hk_pointWeight_ideal_residue_formula [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (x : 𝓞 K) (hxJ : x ∈ J) :
    hkPointWeight ψ (idealUnit J hJ.1) (algebraMap (𝓞 K) K x) =
      (charValue ψ J)⁻¹ * χ.character (Ideal.Quotient.mk (modulusIdeal m) x) := by
  classical
  let U : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let R := HKResidueRing m
  let r : R := Ideal.Quotient.mk (modulusIdeal m) x
  have hpointzero : hkPointWeight ψ U (algebraMap (𝓞 K) K (0 : 𝓞 K)) =
      if m.finitePart = 0 then hkFractionalCharValue ψ U⁻¹ else 0 := by
    simp [hkPointWeight]
  by_cases hx : x = 0
  · subst x
    by_cases hm : m.finitePart = 0
    · have htop : modulusIdeal m = ⊤ := (modulusIdeal_eq_top_iff m).2 hm
      letI : Subsingleton R := (Ideal.Quotient.subsingleton_iff).2 htop
      have hr0 : Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K) = 1 :=
        Subsingleton.elim _ _
      have hchi0 : χ.character (Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) = 1 := by
        rw [hr0]
        simp
      let pJ : rayClassPrimeToIdeals m := ⟨U, hJ.2⟩
      let q : rayClassPrimeToIdeals m →* RayClassGroup m :=
        QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
      have hclassJ : q pJ = rayClass m J hJ := rfl
      have hclassInv : q pJ⁻¹ = (rayClass m J hJ)⁻¹ := by
        rw [map_inv, hclassJ]
      have hzeroWeight : hkFractionalCharValue ψ (U⁻¹) = (charValue ψ J)⁻¹ := by
        have hJinv : U⁻¹ ∈ rayClassPrimeToIdeals m :=
          (rayClassPrimeToIdeals m).inv_mem hJ.2
        rw [hkFractionalCharValue, dif_pos hJinv]
        change (ψ (q pJ⁻¹) : ℂ) = _
        rw [hclassInv]
        simp [charValue, hJ]
      rw [hpointzero, if_pos hm, hzeroWeight, hchi0]
      simp
    · have htop : modulusIdeal m ≠ ⊤ := by
        intro htop
        exact hm ((modulusIdeal_eq_top_iff m).mp htop)
      letI : Nontrivial R := (Ideal.Quotient.nontrivial_iff).2 htop
      have hchi0 : χ.character (Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) = 0 := by
        simpa using χ.character.map_zero
      rw [hpointzero, if_neg hm, hchi0]
      simp
  · have hxK : algebraMap (𝓞 K) K x ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hx
    let xK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K x) hxK
    let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K xK
    let F : FractionalIdeal (𝓞 K)⁰ K :=
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) *
        ((U : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    let E : Ideal (𝓞 K) := hkIntegralPart F
    have hxmem : algebraMap (𝓞 K) K x ∈ (U : FractionalIdeal (𝓞 K)⁰ K) := by
      change algebraMap (𝓞 K) K x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)
      exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hxJ
    have hEcoe : (E : FractionalIdeal (𝓞 K)⁰ K) = F := by
      simpa [E, F] using hk_point_ideal_integral U hxmem
    have hspan0 :
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hxK
    have hUinv0 : ((U : FractionalIdeal (𝓞 K)⁰ K)⁻¹) ≠ 0 := by
      rw [← DedekindResidue.val_unit_inv]
      exact Units.ne_zero (U⁻¹)
    have hF0 : F ≠ 0 := mul_ne_zero hspan0 hUinv0
    have hE0 : E ≠ ⊥ := by
      intro hbot
      have hzero : (E : FractionalIdeal (𝓞 K)⁰ K) = 0 := by simp [hbot]
      rw [hEcoe] at hzero
      exact hF0 hzero
    have hEunit : idealUnit E hE0 = P * U⁻¹ := by
      apply Units.ext
      simpa [E, F, idealUnit, P, xK, coe_toPrincipalIdeal,
        DedekindResidue.val_unit_inv] using hEcoe
    have hS0 : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ :=
      mt Ideal.span_singleton_eq_bot.mp hx
    have hSunit : idealUnit (Ideal.span ({x} : Set (𝓞 K))) hS0 = P := by
      simpa [P, xK] using hk_idealUnit_span x hx
    have hSprime :
        idealUnit (Ideal.span ({x} : Set (𝓞 K))) hS0 ∈ rayClassPrimeToIdeals m ↔
          IsCoprimeTo m (Ideal.span ({x} : Set (𝓞 K))) := by
      constructor
      · intro hP
        exact ⟨hS0, hP⟩
      · rintro ⟨hS0', hP⟩
        have hEq : idealUnit (Ideal.span ({x} : Set (𝓞 K))) hS0 =
            idealUnit (Ideal.span ({x} : Set (𝓞 K))) hS0' := by
          apply Units.ext
          rfl
        rw [← hEq] at hP
        exact hP
    have hPprime_iff :
        P ∈ rayClassPrimeToIdeals m ↔ IsUnit r := by
      rw [← hSunit]
      exact hSprime.trans (hk_span_coprime_iff_unit_residue hx)
    have hEprime_iff : IsCoprimeTo m E ↔ P ∈ rayClassPrimeToIdeals m := by
      constructor
      · intro hEc
        have hEP : P = idealUnit E hEc.1 * U := by
          rw [hEunit]
          simp [mul_assoc]
        rw [hEP]
        exact (rayClassPrimeToIdeals m).mul_mem hEc.2 hJ.2
      · intro hP
        refine ⟨hE0, ?_⟩
        rw [hEunit]
        exact (rayClassPrimeToIdeals m).mul_mem hP
          ((rayClassPrimeToIdeals m).inv_mem hJ.2)
    by_cases hr : IsUnit r
    · have hEc : IsCoprimeTo m E := hEprime_iff.mpr (hPprime_iff.mpr hr)
      have hP : P ∈ rayClassPrimeToIdeals m := hPprime_iff.mpr hr
      have hSc : IsCoprimeTo m (Ideal.span ({x} : Set (𝓞 K))) := by
        refine ⟨hS0, ?_⟩
        rw [hSunit]
        exact hP
      let pE : rayClassPrimeToIdeals m := ⟨idealUnit E hEc.1, hEc.2⟩
      let pS : rayClassPrimeToIdeals m := ⟨P, hPprime_iff.mpr hr⟩
      let pJ : rayClassPrimeToIdeals m := ⟨U, hJ.2⟩
      let q : rayClassPrimeToIdeals m →* RayClassGroup m :=
        QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
      have hpE : pE = pS * pJ⁻¹ := by
        apply Subtype.ext
        exact hEunit
      have hclassS : q pS = rayClass m (Ideal.span ({x} : Set (𝓞 K))) hSc := by
        simp [rayClass, q, pS, hSunit]
      have hclassJ : q pJ = rayClass m J hJ := by rfl
      have hclassE : rayClass m E hEc =
          rayClass m (Ideal.span ({x} : Set (𝓞 K))) hSc *
            (rayClass m J hJ)⁻¹ := by
        calc
          rayClass m E hEc = q pE := by simp [rayClass, q, pE]
          _ = q pS * (q pJ)⁻¹ := by rw [hpE, map_mul, map_inv]
          _ = _ := by rw [hclassS, hclassJ]
      have hprincipal := χ.principal_value x hSc
      have hprincipalR : χ.character r = charValue ψ (Ideal.span ({x} : Set (𝓞 K))) := by
        simpa [r] using hprincipal
      have hcharS : charValue ψ (Ideal.span ({x} : Set (𝓞 K))) =
          (ψ (rayClass m (Ideal.span ({x} : Set (𝓞 K))) hSc) : ℂ) := by
        simp [charValue, hSc]
      have hcharJ : charValue ψ J = (ψ (rayClass m J hJ) : ℂ) := by
        simp [charValue, hJ]
      have hcharE : charValue ψ E =
          χ.character r * (charValue ψ J)⁻¹ := by
        calc
          charValue ψ E = (ψ (rayClass m E hEc) : ℂ) := by
            simp [charValue, hEc]
          _ = (ψ (rayClass m (Ideal.span ({x} : Set (𝓞 K))) hSc) : ℂ) *
              (ψ (rayClass m J hJ) : ℂ)⁻¹ := by
            rw [hclassE]
            simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
          _ = χ.character r * (charValue ψ J)⁻¹ := by
            have hχS : χ.character r =
                (ψ (rayClass m (Ideal.span ({x} : Set (𝓞 K))) hSc) : ℂ) :=
              hprincipalR.trans hcharS
            rw [← hχS, hcharJ]
      simp only [hkPointWeight, if_neg hxK]
      rw [hcharE]
      ring
    · have hEc : ¬ IsCoprimeTo m E := fun h => hr (hPprime_iff.mp (hEprime_iff.mp h))
      have hchi0 : χ.character r = 0 := χ.character.map_nonunit hr
      simp only [hkPointWeight, if_neg hxK]
      change charValue ψ E = (charValue ψ J)⁻¹ * χ.character r
      simp [charValue, hEc, hchi0]

private theorem hk_mulChar_norm_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (x : R) : ‖χ x‖ ≤ 1 := by
  classical
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hpow : (χ.toUnitHom u) ^ Nat.card Rˣ = 1 := by
      rw [← map_pow, pow_card_eq_one']
      simp
    have hpowC := congrArg (fun z : ℂˣ => (z : ℂ)) hpow
    have hpow' : (χ (u : R)) ^ Nat.card Rˣ = 1 := by
      simpa only [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one] using hpowC
    have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow' Nat.card_pos.ne'
    simpa using hnorm.le
  · simp [MulChar.map_nonunit χ hx]

private noncomputable def hkIntegralIdealPointLift [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J) :
    HKResidueRing m → J := fun r =>
      Classical.choose (integral_residue_surjective_of_sup_eq m J
        ((isCoprimeTo_iff_sup m J).mp hJ).2 r)

private theorem hkIntegralIdealPointLift_spec [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (r : HKResidueRing m) :
    Ideal.Quotient.mk (modulusIdeal m) (hkIntegralIdealPointLift m J hJ r).1 = r :=
  Classical.choose_spec (integral_residue_surjective_of_sup_eq m J
    ((isCoprimeTo_iff_sup m J).mp hJ).2 r)

private noncomputable def hkIntegralIdealPointToCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (x : J) : HKResidueRing m × (modulusIdeal m * J) := by
  classical
  let r : HKResidueRing m := Ideal.Quotient.mk (modulusIdeal m) x.1
  let d : 𝓞 K := x.1 - (hkIntegralIdealPointLift m J hJ r).1
  have hdJ : d ∈ J := by
    exact J.sub_mem x.2 (hkIntegralIdealPointLift m J hJ r).2
  have hdr : Ideal.Quotient.mk (modulusIdeal m) d = 0 := by
    dsimp [d, r]
    rw [map_sub, hkIntegralIdealPointLift_spec, sub_self]
  refine (r, ⟨d, ?_⟩)
  exact (integral_residue_kernel_of_sup_eq m J
    ((isCoprimeTo_iff_sup m J).mp hJ).2 ⟨d, hdJ⟩).mp hdr

private noncomputable def hkIntegralIdealPointFromCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (p : HKResidueRing m × (modulusIdeal m * J)) : J :=
  ⟨(hkIntegralIdealPointLift m J hJ p.1).1 + p.2.1,
    J.add_mem (hkIntegralIdealPointLift m J hJ p.1).2 (Ideal.mul_le_right p.2.2)⟩

private theorem hkIntegralIdealPointFromCoset_residue [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (p : HKResidueRing m × (modulusIdeal m * J)) :
    Ideal.Quotient.mk (modulusIdeal m) (hkIntegralIdealPointFromCoset m J hJ p).1 = p.1 := by
  change Ideal.Quotient.mk (modulusIdeal m)
      ((hkIntegralIdealPointLift m J hJ p.1).1 + p.2.1) = p.1
  rw [map_add, hkIntegralIdealPointLift_spec]
  have hzM : p.2.1 ∈ modulusIdeal m := Ideal.mul_le_left p.2.2
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzM, add_zero]

private noncomputable def hkIntegralIdealPointEquiv [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J) :
    J ≃ HKResidueRing m × (modulusIdeal m * J) where
  toFun := hkIntegralIdealPointToCoset m J hJ
  invFun := hkIntegralIdealPointFromCoset m J hJ
  left_inv x := by
    apply Subtype.ext
    dsimp [hkIntegralIdealPointToCoset, hkIntegralIdealPointFromCoset]
    ring
  right_inv p := by
    apply Prod.ext
    · exact hkIntegralIdealPointFromCoset_residue m J hJ p
    · apply Subtype.ext
      change (hkIntegralIdealPointFromCoset m J hJ p).1 -
          (hkIntegralIdealPointLift m J hJ
            (Ideal.Quotient.mk (modulusIdeal m)
              (hkIntegralIdealPointFromCoset m J hJ p).1)).1 = p.2.1
      rw [hkIntegralIdealPointFromCoset_residue]
      simp [hkIntegralIdealPointFromCoset]

private noncomputable def hkIntegralIdealPointsEquiv [IsTotallyComplex K]
    {m : RayClassModulus K} (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J) :
    J ≃ {x : K // x ∈ (idealUnit J hJ.1 : FractionalIdeal (𝓞 K)⁰ K)} where
  toFun x := ⟨algebraMap (𝓞 K) K x.1, by
    change algebraMap (𝓞 K) K x.1 ∈ (J : FractionalIdeal (𝓞 K)⁰ K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) x.2⟩
  invFun z := by
    have hmem : ∃ x : 𝓞 K, x ∈ J ∧ algebraMap (𝓞 K) K x = z.1 :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp (by
        simpa [idealUnit] using z.2)
    exact ⟨Classical.choose hmem, (Classical.choose_spec hmem).1⟩
  left_inv x := by
    apply Subtype.ext
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    have hmem : ∃ a : 𝓞 K, a ∈ J ∧
        algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K x.1 :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp
        (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) x.2)
    exact (Classical.choose_spec hmem).2
  right_inv z := by
    apply Subtype.ext
    have hmem : ∃ a : 𝓞 K, a ∈ J ∧ algebraMap (𝓞 K) K a = z.1 :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp (by
        simpa [idealUnit] using z.2)
    exact (Classical.choose_spec hmem).2

private theorem hk_summable_integralIdealGaussian [IsTotallyComplex K]
    {m : RayClassModulus K} (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (c : index K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ c i) :
    Summable (fun x : J => integralIdealGaussian c x.1) := by
  have hlat := DedekindResidue.summable_real_weightedGaussian
    (idealZLattice K (idealUnit J hJ.1)) ha hca
  let e := integralIdealCoordEquiv J hJ.1
  have hcomp : Summable (fun x : J =>
      Real.exp (-Real.pi * ∑ i : index K,
        c i * ((e x : EuclideanSpace ℝ (index K)) i) ^ 2)) :=
    (Equiv.summable_iff e).mpr hlat
  simpa [integralIdealGaussian, e, integralIdealCoordEquiv, integralIdealCoordMap] using hcomp

private theorem hkGaussianCM_eq (c : InfinitePlace K → ℝ) (x : K) :
    (Real.exp (-Real.pi * ∑ w : InfinitePlace K, c w * (w x) ^ 2) : ℂ) =
      weightedGaussianCM (placeWeights K c) (embeddingCoords K x) := by
  rw [Complex.ofReal_exp]
  unfold weightedGaussianCM
  simp only [ContinuousMap.coe_mk]
  congr 1
  have hsum := DedekindResidue.sum_placeWeights_embeddingCoords_sq K c x
  have hsumC :
      (∑ w : InfinitePlace K, (c w : ℂ) * (w x : ℂ) ^ 2) =
        ∑ i : index K,
          (placeWeights K c i : ℂ) * (embeddingCoords K x i : ℂ) ^ 2 := by
    exact_mod_cast hsum.symm
  push_cast
  rw [hsumC]

private theorem hk_finite_positive_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ a b : ℝ, 0 < a ∧ (∀ i, a ≤ f i) ∧ 0 < b ∧ (∀ i, f i ≤ b) := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let a := s.min' hs
  let b := s.max' hs
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    change 0 < s.min' hs
    rw [← hia]
    exact hf i
  · intro i
    exact Finset.min'_le s (f i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · obtain ⟨i, hi, hib⟩ := Finset.mem_image.mp (Finset.max'_mem s hs)
    change 0 < s.max' hs
    rw [← hib]
    exact hf i
  · intro i
    exact Finset.le_max' s (f i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private theorem hk_index_nonempty [IsTotallyComplex K] : Nonempty (index K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact ⟨Sum.inr (⟨w, IsTotallyComplex.isComplex w⟩, 0)⟩

private theorem hkGaussianCM_dual_eq [IsTotallyComplex K]
    (c : InfinitePlace K → ℝ) (y : K) :
    weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
        ((diagScale (dualityWeights K) (dualityWeights_ne_zero K))
          (embeddingCoords K y)) =
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        (4 / c w) * (w y) ^ 2) : ℂ) := by
  classical
  have hdualW (w : InfinitePlace K) : dualPlaceWeights K c w = 4 / c w := by
    have hnreal : ¬ IsReal w :=
      not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
    simp [dualPlaceWeights, hnreal, div_eq_mul_inv]
  have hsumR :
      ∑ i : index K, (placeWeights K c i)⁻¹ *
          (((diagScale (dualityWeights K) (dualityWeights_ne_zero K))
            (embeddingCoords K y)) i) ^ 2 =
        ∑ w : InfinitePlace K, (4 / c w) * (w y) ^ 2 := by
    calc
      ∑ i : index K, (placeWeights K c i)⁻¹ *
          (((diagScale (dualityWeights K) (dualityWeights_ne_zero K))
            (embeddingCoords K y)) i) ^ 2 =
        ∑ i : index K,
          ((placeWeights K c i)⁻¹ * (dualityWeights K i) ^ 2) *
            (embeddingCoords K y i) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [diagScale_apply]
              ring
      _ = ∑ i : index K, placeWeights K (dualPlaceWeights K c) i *
            (embeddingCoords K y i) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [DedekindResidue.placeWeights_dualPlaceWeights]
      _ = ∑ w : InfinitePlace K, dualPlaceWeights K c w * (w y) ^ 2 :=
        DedekindResidue.sum_placeWeights_embeddingCoords_sq K
          (dualPlaceWeights K c) y
      _ = ∑ w : InfinitePlace K, (4 / c w) * (w y) ^ 2 := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [hdualW]
  rw [Complex.ofReal_exp]
  unfold weightedGaussianCM
  simp only [ContinuousMap.coe_mk]
  congr 1
  have hsumC :
      (∑ i : index K, ((placeWeights K c i)⁻¹ : ℂ) *
          (((diagScale (dualityWeights K) (dualityWeights_ne_zero K))
            (embeddingCoords K y)) i : ℂ) ^ 2) =
        ∑ w : InfinitePlace K, ((4 / c w : ℝ) : ℂ) * (w y : ℂ) ^ 2 := by
    exact_mod_cast hsumR
  push_cast
  rw [hsumC]
  have hsumDiv :
      (∑ w : InfinitePlace K, ((4 / c w : ℝ) : ℂ) * (w y : ℂ) ^ 2) =
        ∑ w : InfinitePlace K, (4 : ℂ) / (c w : ℂ) * (w y : ℂ) ^ 2 := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    congr 1
    norm_cast
  rw [hsumDiv]

private theorem hk_weightedTheta_residueCosets [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i) :
    hkWeightedTheta ψ (idealUnit J hJ.1) c =
      (charValue ψ J)⁻¹ *
        ∑ r : HKResidueRing m, χ.character r *
          ∑' z : modulusIdeal m * J,
            (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
              c w * (w (algebraMap (𝓞 K) K
                ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) := by
  classical
  let U : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let ci := placeWeights K c
  let g := weightedGaussianCM ci
  let C0 : ℝ := ‖(charValue ψ J)⁻¹‖
  let f : J → ℂ := fun x =>
    hkPointWeight ψ U (algebraMap (𝓞 K) K x.1) *
      g (embeddingCoords K (algebraMap (𝓞 K) K x.1))
  have hgauss : Summable (fun x : J =>
      ‖g (embeddingCoords K (algebraMap (𝓞 K) K x.1))‖) := by
    simpa [g, ci, integralIdealGaussian, norm_weightedGaussianCM_apply] using
      hk_summable_integralIdealGaussian J hJ ci ha hca
  have hpointBound (x : J) :
      ‖hkPointWeight ψ U (algebraMap (𝓞 K) K x.1)‖ ≤ C0 := by
    rw [hk_pointWeight_ideal_residue_formula ψ χ J hJ x.1 x.2, norm_mul]
    calc
      ‖(charValue ψ J)⁻¹‖ *
          ‖χ.character (Ideal.Quotient.mk (modulusIdeal m) x.1)‖ ≤
          ‖(charValue ψ J)⁻¹‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (hk_mulChar_norm_le_one χ.character _) (norm_nonneg _)
      _ = C0 := by simp [C0]
  have hnorm : Summable (fun x : J => ‖f x‖) := by
    have hmajor : Summable (fun x : J =>
        C0 * ‖g (embeddingCoords K (algebraMap (𝓞 K) K x.1))‖) := hgauss.mul_left C0
    apply hmajor.of_norm_bounded
    intro x
    dsimp [f]
    rw [norm_mul]
    have hp : 0 ≤ ‖hkPointWeight ψ U (algebraMap (𝓞 K) K x.1)‖ := norm_nonneg _
    have hg : 0 ≤ ‖g (embeddingCoords K (algebraMap (𝓞 K) K x.1))‖ := norm_nonneg _
    simpa only [abs_of_nonneg (mul_nonneg hp hg)] using
      mul_le_mul_of_nonneg_right (hpointBound x) hg
  have hsum : Summable f := hnorm.of_norm
  let eK := hkIntegralIdealPointsEquiv J hJ
  let pointsK := {x : K // x ∈ (U : FractionalIdeal (𝓞 K)⁰ K)}
  let fK : pointsK → ℂ := fun x =>
    hkPointWeight ψ U x.1 *
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        c w * (w x.1) ^ 2) : ℂ)
  have hKJ : ∀ x : J, fK (eK x) = f x := by
    intro x
    dsimp [fK, f, g, ci, eK, hkIntegralIdealPointsEquiv]
    rw [hkGaussianCM_eq]
  have htheta : hkWeightedTheta ψ U c = ∑' x : J, f x := by
    unfold hkWeightedTheta
    calc
      ∑' x : pointsK, fK x = ∑' x : J, fK (eK x) :=
        (Equiv.tsum_eq eK fK).symm
      _ = ∑' x : J, f x := tsum_congr hKJ
  let eC := hkIntegralIdealPointEquiv m J hJ
  let fC : HKResidueRing m × (modulusIdeal m * J) → ℂ :=
    fun p => f (eC.symm p)
  have hcomp : Summable (fun x : J => fC (eC x)) := by
    apply hsum.congr
    intro x
    simp [fC]
  have hsumC : Summable fC := (Equiv.summable_iff eC).mp hcomp
  calc
    hkWeightedTheta ψ U c = ∑' x : J, f x := htheta
    _ = ∑' x : J, fC (eC x) := by
      apply tsum_congr
      intro x
      simp [fC]
    _ = ∑' p : HKResidueRing m × (modulusIdeal m * J), fC p := Equiv.tsum_eq eC fC
    _ = ∑' r : HKResidueRing m, ∑' z : modulusIdeal m * J, fC (r, z) := hsumC.tsum_prod
    _ = ∑ r : HKResidueRing m, ∑' z : modulusIdeal m * J,
          f (hkIntegralIdealPointFromCoset m J hJ (r, z)) := by
        simp only [fC, tsum_fintype]
        apply Finset.sum_congr rfl
        intro r _
        apply tsum_congr
        intro z
        simp [eC, hkIntegralIdealPointEquiv]
    _ = (charValue ψ J)⁻¹ *
          ∑ r : HKResidueRing m, χ.character r *
            ∑' z : modulusIdeal m * J,
              (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
                c w * (w (algebraMap (𝓞 K) K
                  ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [← tsum_mul_left]
        rw [← tsum_mul_left]
        apply tsum_congr
        intro z
        let x := hkIntegralIdealPointFromCoset m J hJ (r, z)
        have hxval : x.1 = (hkIntegralIdealPointLift m J hJ r).1 + z.1 := rfl
        have hxJ : x.1 ∈ J := x.2
        have hweight := hk_pointWeight_ideal_residue_formula ψ χ J hJ x.1 hxJ
        have hres := hkIntegralIdealPointFromCoset_residue m J hJ (r, z)
        have hgauss := hkGaussianCM_eq c
          (algebraMap (𝓞 K) K ((hkIntegralIdealPointLift m J hJ r).1 + z.1))
        dsimp [f, x, g, ci]
        rw [hweight, hres, hgauss]
        rw [hxval]
        ring

private theorem hkEmbeddingCoords_add (x y : K) :
    embeddingCoords K (x + y) = embeddingCoords K x + embeddingCoords K y := by
  simp [embeddingCoords]

private theorem hk_gaussianCoset_poisson [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (r : HKResidueRing m) (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
    {a B : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i)
    (hB : 0 < B) (hcB : ∀ i, placeWeights K c i ≤ B) :
    ∑' z : modulusIdeal m * J,
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          c w * (w (algebraMap (𝓞 K) K
            ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
      (ZLattice.covolume
        (idealZLattice K (idealUnit (modulusIdeal m * J) (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))) volume)⁻¹ •
        ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
            (idealZLattice K (idealUnit (modulusIdeal m * J)
              (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))),
          Real.fourierChar (⟪embeddingCoords K (algebraMap (𝓞 K) K
              (hkIntegralIdealPointLift m J hJ r).1),
              (w : EuclideanSpace ℝ (index K))⟫) •
          ((Real.sqrt (∏ i : index K, placeWeights K c i))⁻¹ •
              weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
                (w : EuclideanSpace ℝ (index K))) := by
  let MJ := modulusIdeal m * J
  have hMJ : MJ ≠ ⊥ := mul_ne_zero (modulusIdeal_ne_bot m) hJ.1
  let I' : NumberFieldFractionalIdealGroup K := idealUnit MJ hMJ
  let L := idealZLattice K I'
  let e := integralIdealCoordEquiv MJ hMJ
  let shift := embeddingCoords K (algebraMap (𝓞 K) K
    (hkIntegralIdealPointLift m J hJ r).1)
  let g := weightedGaussianCM (placeWeights K c)
  have hcCoord : ∀ i, 0 < placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hc w
  have hcoords (z : MJ) :
      embeddingCoords K (algebraMap (𝓞 K) K
        ((hkIntegralIdealPointLift m J hJ r).1 + z.1)) =
        shift + (e z : EuclideanSpace ℝ (index K)) := by
    rw [map_add, hkEmbeddingCoords_add]
    simp [shift, e, integralIdealCoordEquiv, integralIdealCoordMap]
  have hterm (z : MJ) :
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        c w * (w (algebraMap (𝓞 K) K
          ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
        g (shift + (e z : EuclideanSpace ℝ (index K))) := by
    rw [hkGaussianCM_eq, hcoords]
  change ∑' z : MJ, _ = _
  calc
    ∑' z : MJ,
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          c w * (w (algebraMap (𝓞 K) K
            ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
      ∑' z : MJ, g (shift + (e z : EuclideanSpace ℝ (index K))) := by
        apply tsum_congr
        exact hterm
    _ = ∑' v : L, g (shift + (v : EuclideanSpace ℝ (index K))) :=
      Equiv.tsum_eq e (fun v => g (shift + (v : EuclideanSpace ℝ (index K))))
    _ = (ZLattice.covolume L volume)⁻¹ •
        ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice L,
          Real.fourierChar (⟪shift, (w : EuclideanSpace ℝ (index K))⟫) •
            ((Real.sqrt (∏ i : index K, placeWeights K c i))⁻¹ •
              weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
                (w : EuclideanSpace ℝ (index K))) := by
      exact weightedGaussian_translate_transform L shift hcCoord ha hca hB hcB

private theorem hk_embeddingCoords_injective : Function.Injective (embeddingCoords K) := by
  intro x y hxy
  apply mixedEmbedding_injective K
  have h := congrArg
    (fun z => (NumberField.mixedEmbedding.euclidean.toMixed K)
      ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).repr.symm z)) hxy
  simpa [embeddingCoords] using h

private theorem hk_dualIdeal_integral_eq (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) :
    DedekindResidue.dualIdealUnit K
        (idealUnit (modulusIdeal m * J) hMJ) =
      hkDualIdeal m (idealUnit J hJ.1) := by
  have hprod : idealUnit (modulusIdeal m * J) hMJ =
      hkModulusUnit m * idealUnit J hJ.1 := by
    apply Units.ext
    simp [hkModulusUnit, idealUnit, FractionalIdeal.coeIdeal_mul]
  apply Units.ext
  change FractionalIdeal.dual ℤ ℚ
      (idealUnit (modulusIdeal m * J) hMJ : FractionalIdeal (𝓞 K)⁰ K) =
      (((hkModulusUnit m * hkDifferentUnit K * idealUnit J hJ.1)⁻¹ :
        NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)
  have hdualOne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  rw [FractionalIdeal.dual_eq_mul_inv, hdualOne, hprod]
  simp [hkDualIdeal, hkDifferentUnit, hkModulusUnit, idealUnit,
    FractionalIdeal.coeIdeal_mul, mul_comm, mul_left_comm]

private noncomputable def hk_dualVectorPreimage [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥)
    (w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
      (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ))) :
    {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K) ∧
      embeddingCoords K y =
        (diagScale (dualityWeights K) (dualityWeights_ne_zero K)).symm
          (w : EuclideanSpace ℝ (index K))} := by
  classical
  let I' : NumberFieldFractionalIdealGroup K := idealUnit (modulusIdeal m * J) hMJ
  let D' : NumberFieldFractionalIdealGroup K := DedekindResidue.dualIdealUnit K I'
  let T := diagScale (dualityWeights K) (dualityWeights_ne_zero K)
  have hdual := DedekindResidue.dualZLattice_idealZLattice K I'
  have hD' : D' = hkDualIdeal m (idealUnit J hJ.1) :=
    hk_dualIdeal_integral_eq m J hJ hMJ
  have hw : T.symm (w : EuclideanSpace ℝ (index K)) ∈ idealZLattice K D' := by
    have hw' : (w : EuclideanSpace ℝ (index K)) ∈
        ZLattice.comap ℝ (idealZLattice K D')
          (T.symm.toContinuousLinearEquiv.toLinearMap) := by
      rw [← hdual]
      exact w.2
    exact hw'
  have hmem : ∃ y, y ∈ (D' : FractionalIdeal (𝓞 K)⁰ K) ∧
      embeddingCoords K y = T.symm (w : EuclideanSpace ℝ (index K)) :=
    (mem_idealZLattice K D' _).mp hw
  refine ⟨Classical.choose hmem, ?_⟩
  constructor
  · simpa [D', hD'] using (Classical.choose_spec hmem).1
  · exact (Classical.choose_spec hmem).2

private noncomputable def hk_dualPointToVector [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)}) :
    ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
      (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) := by
  classical
  let T := diagScale (dualityWeights K) (dualityWeights_ne_zero K)
  let I' : NumberFieldFractionalIdealGroup K := idealUnit (modulusIdeal m * J) hMJ
  let D' : NumberFieldFractionalIdealGroup K := DedekindResidue.dualIdealUnit K I'
  have hdual := DedekindResidue.dualZLattice_idealZLattice K I'
  have hD' : D' = hkDualIdeal m (idealUnit J hJ.1) :=
    hk_dualIdeal_integral_eq m J hJ hMJ
  refine ⟨T (embeddingCoords K y.1), ?_⟩
  change T (embeddingCoords K y.1) ∈ DedekindResidue.dualZLattice
    (idealZLattice K I')
  rw [hdual]
  change T.symm (T (embeddingCoords K y.1)) ∈ idealZLattice K D'
  rw [T.symm_apply_apply]
  exact (mem_idealZLattice K D' _).mpr
    ⟨y.1, by simpa [D', hD'] using y.2, rfl⟩

private noncomputable def hk_dualPointEquiv [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) :
    ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
        (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) ≃
      {y : K // y ∈
        (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)} where
  toFun w :=
    ⟨(hk_dualVectorPreimage m J hJ hMJ w).1,
      (hk_dualVectorPreimage m J hJ hMJ w).2.1⟩
  invFun := hk_dualPointToVector m J hJ hMJ
  left_inv w := by
    apply Subtype.ext
    change (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
        (embeddingCoords K (hk_dualVectorPreimage m J hJ hMJ w).1) =
      (w : EuclideanSpace ℝ (index K))
    rw [(hk_dualVectorPreimage m J hJ hMJ w).2.2]
    exact (diagScale (dualityWeights K) (dualityWeights_ne_zero K)).apply_symm_apply _
  right_inv y := by
    apply Subtype.ext
    apply hk_embeddingCoords_injective
    change embeddingCoords K
        (hk_dualVectorPreimage m J hJ hMJ
          (hk_dualPointToVector m J hJ hMJ y)).1 = embeddingCoords K y.1
    rw [(hk_dualVectorPreimage m J hJ hMJ
      (hk_dualPointToVector m J hJ hMJ y)).2.2]
    simp [hk_dualPointToVector]

private theorem hk_dualIdeal_factor [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m) :
    hkDualIdeal m (idealUnit J hJ.1) =
      toPrincipalIdeal (𝓞 K) K T.a *
        (idealUnit (T.B * J) (mul_ne_zero T.coprime.1 hJ.1))⁻¹ := by
  let P := toPrincipalIdeal (𝓞 K) K T.a
  let C : Ideal (𝓞 K) := T.B * J
  have hC : C ≠ ⊥ := mul_ne_zero T.coprime.1 hJ.1
  have hCunit : idealUnit C hC =
      idealUnit T.B T.coprime.1 * idealUnit J hJ.1 := by
    apply Units.ext
    simp [C, idealUnit, FractionalIdeal.coeIdeal_mul]
  have hMD : hkModulusUnit m * hkDifferentUnit K =
      P⁻¹ * idealUnit T.B T.coprime.1 := by
    calc
      hkModulusUnit m * hkDifferentUnit K =
          P⁻¹ * (P * hkModulusUnit m * hkDifferentUnit K) := by group
      _ = P⁻¹ * idealUnit T.B T.coprime.1 := by rw [← T.ideal_eq]
  have hprod : hkModulusUnit m * hkDifferentUnit K * idealUnit J hJ.1 =
      P⁻¹ * (idealUnit T.B T.coprime.1 * idealUnit J hJ.1) := by
    calc
      hkModulusUnit m * hkDifferentUnit K * idealUnit J hJ.1 =
          (hkModulusUnit m * hkDifferentUnit K) * idealUnit J hJ.1 := by group
      _ = (P⁻¹ * idealUnit T.B T.coprime.1) * idealUnit J hJ.1 := by rw [hMD]
      _ = P⁻¹ * (idealUnit T.B T.coprime.1 * idealUnit J hJ.1) := by group
  calc
    hkDualIdeal m (idealUnit J hJ.1) =
        (hkModulusUnit m * hkDifferentUnit K * idealUnit J hJ.1)⁻¹ := rfl
    _ = (P⁻¹ * (idealUnit T.B T.coprime.1 * idealUnit J hJ.1))⁻¹ := by rw [← hprod]
    _ = P * (idealUnit T.B T.coprime.1 * idealUnit J hJ.1)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    _ = P * (idealUnit C hC)⁻¹ := by rw [hCunit]

private theorem hk_exists_nonzero_coprime_lift (m : RayClassModulus K)
    (A : Ideal (𝓞 K)) (hA : IsCoprimeTo m A) :
    ∃ d : 𝓞 K, d ∈ A ∧ d ≠ 0 ∧ d - 1 ∈ modulusIdeal m := by
  classical
  by_cases hMtop : modulusIdeal m = ⊤
  · obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA.1
    exact ⟨d, hd, hd0, by simp [hMtop]⟩
  · have hsup : modulusIdeal m ⊔ A = ⊤ := by
      simpa [sup_comm] using ((isCoprimeTo_iff_sup m A).mp hA).2
    have hcop : IsCoprime A (modulusIdeal m) :=
      Ideal.isCoprime_iff_sup_eq.mpr (by simpa [sup_comm] using hsup)
    obtain ⟨d, hd, e, he, hde⟩ := hcop.exists
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      have hone : (1 : 𝓞 K) ∈ modulusIdeal m := by
        have heq : e = 1 := by simpa using hde
        rw [← heq]
        exact he
      have htop : modulusIdeal m = ⊤ :=
        Ideal.eq_top_of_isUnit_mem (modulusIdeal m) hone isUnit_one
      exact hMtop htop
    have hmod : d - 1 ∈ modulusIdeal m := by
      have hEq : d - 1 = -e := by
        calc
          d - 1 = d - (d + e) := by rw [hde]
          _ = -e := by ring
      rw [hEq]
      exact (modulusIdeal m).neg_mem he
    exact ⟨d, hd, hd0, hmod⟩

private theorem hk_dualPoint_BJ_coprime [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m) : IsCoprimeTo m (T.B * J) := by
  let C : Ideal (𝓞 K) := T.B * J
  have hC : C ≠ ⊥ := mul_ne_zero T.coprime.1 hJ.1
  have hunit : idealUnit C hC = idealUnit T.B T.coprime.1 * idealUnit J hJ.1 := by
    apply Units.ext
    simp [C, idealUnit, FractionalIdeal.coeIdeal_mul]
  refine ⟨hC, ?_⟩
  rw [hunit]
  exact (rayClassPrimeToIdeals m).mul_mem T.coprime.2 hJ.2

private noncomputable def hk_dualPoint_denominator [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m) : 𝓞 K :=
  Classical.choose (hk_exists_nonzero_coprime_lift m (T.B * J)
    (hk_dualPoint_BJ_coprime m J hJ T))

private theorem hk_dualPoint_denominator_spec [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m) :
    hk_dualPoint_denominator m J hJ T ∈ T.B * J ∧
      hk_dualPoint_denominator m J hJ T ≠ 0 ∧
      hk_dualPoint_denominator m J hJ T - 1 ∈ modulusIdeal m :=
  Classical.choose_spec (hk_exists_nonzero_coprime_lift m (T.B * J)
    (hk_dualPoint_BJ_coprime m J hJ T))

private theorem hk_rayCongruent_of_modulus_fraction [IsTotallyComplex K]
    (m : RayClassModulus K) (C : Ideal (𝓞 K)) (hC : IsCoprimeTo m C)
    (q : Kˣ)
    (hq : (q : K) - 1 ∈
      ((hkModulusUnit m * (idealUnit C hC.1)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K)) :
    IsRayCongruent m q := by
  classical
  let M : NumberFieldFractionalIdealGroup K := hkModulusUnit m
  let CI : NumberFieldFractionalIdealGroup K := idealUnit C hC.1
  have hdlift := hk_exists_nonzero_coprime_lift m C hC
  let d : 𝓞 K := Classical.choose hdlift
  have hd : d ∈ C := (Classical.choose_spec hdlift).1
  have hd0 : d ≠ 0 := (Classical.choose_spec hdlift).2.1
  have hdmod : d - 1 ∈ modulusIdeal m := (Classical.choose_spec hdlift).2.2
  have hdCI : (d : K) ∈ (CI : FractionalIdeal (𝓞 K)⁰ K) := by
    change algebraMap (𝓞 K) K d ∈ (C : FractionalIdeal (𝓞 K)⁰ K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hd
  have hmul : (d : K) * ((q : K) - 1) ∈ ((CI * (M * CI⁻¹) :
      NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := CI),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul hdCI hq
  have hcancel : CI * (M * CI⁻¹) = M := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [congrArg Units.val hcancel] at hmul
  have hmulM : (d : K) * ((q : K) - 1) ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hmul
  have hmulMcoe : (d : K) * ((q : K) - 1) ∈
      (modulusIdeal m : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa [M, hkModulusUnit, idealUnit] using hmulM
  obtain ⟨v, hv, hvCast⟩ :=
    (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hmulMcoe
  let e : 𝓞 K := d + v
  have heCast : algebraMap (𝓞 K) K e = (d : K) * (q : K) := by
    dsimp [e]
    rw [map_add, hvCast]
    ring
  have heMinus : e - 1 ∈ modulusIdeal m := by
    have hEq : e - 1 = (d - 1) + v := by dsimp [e]; ring
    rw [hEq]
    exact (modulusIdeal m).add_mem hdmod hv
  have he0K : algebraMap (𝓞 K) K e ≠ 0 := by
    rw [heCast]
    exact mul_ne_zero
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd0) (Units.ne_zero q)
  have he0 : e ≠ 0 := fun h => he0K (by rw [h]; simp)
  let dUnit : Kˣ := Units.mk0 (algebraMap (𝓞 K) K d) (by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd0)
  let eUnit : Kˣ := Units.mk0 (algebraMap (𝓞 K) K e) (by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne he0)
  have hdRay : IsRayCongruent m dUnit :=
    (integral_rayCongruent_iff m d hd0).mpr hdmod
  have heRay : IsRayCongruent m eUnit :=
    (integral_rayCongruent_iff m e he0).mpr heMinus
  have hqEq : q = eUnit * dUnit⁻¹ := by
    apply Units.ext
    change (q : K) = _
    simp only [eUnit, dUnit, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [heCast]
    have hdKne : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd0
    field_simp [hdKne]
  rw [hqEq]
  exact (rayCongruentUnits m).mul_mem heRay ((rayCongruentUnits m).inv_mem hdRay)

private theorem hk_principal_rayPrimeTo_of_congruent [IsTotallyComplex K]
    (m : RayClassModulus K) (x : Kˣ) (hx : IsRayCongruent m x) :
    toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals m := by
  let m' := rayModulusToCFT m
  have hidele : IdeleGroup.principalIdele K x ∈
      RayClass.idelePrimeToModulusSubgroup m' :=
    (isRayCongruent_iff_principalIdele_mem m x).mp hx
  have hprime := RayClass.fractionalIdeal_mem_primeToModulusIdeals m'
    (IdeleGroup.principalIdele K x) hidele
  change ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (toPrincipalIdeal (𝓞 K) K x : FractionalIdeal (𝓞 K)⁰ K) = 0
  intro v hv
  have hv' : v ∈ m'.finitePart.support := by simpa [m'] using hv
  have hcount := hprime v hv'
  simpa [m', IdeleGroup.fractionalIdeal_principalIdele, coe_toPrincipalIdeal] using hcount

private noncomputable def hk_rayClassQuotientMap (m : RayClassModulus K) :
    rayClassPrimeToIdeals m →* RayClassGroup m :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)

private theorem hk_principal_rayClass_quotient_one [IsTotallyComplex K]
    (m : RayClassModulus K) (x : Kˣ)
    (hx : toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals m)
    (hRay : IsRayCongruent m x) :
    hk_rayClassQuotientMap m ⟨toPrincipalIdeal (𝓞 K) K x, hx⟩ = 1 := by
  let p : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K x, hx⟩
  have hp : p ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m p).2 ⟨x, hRay, rfl⟩
  exact (QuotientGroup.eq_one_iff
    (N := rayPrincipalIdealSubgroupInPrimeTo m) p).2 hp

private theorem hk_dualPoint_div_mem [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)}) :
    y.1 / (T.a : K) ∈
      ((idealUnit (T.B * J) (mul_ne_zero T.coprime.1 hJ.1))⁻¹ :
        FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K T.a
  let C : NumberFieldFractionalIdealGroup K :=
    idealUnit (T.B * J) (mul_ne_zero T.coprime.1 hJ.1)
  have hfactor := hk_dualIdeal_factor m J hJ T
  have hy : y.1 ∈ ((P * C⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hfactor]
    exact y.2
  have hPInv : P⁻¹ = toPrincipalIdeal (𝓞 K) K T.a⁻¹ := by simp [P]
  have hPInvVal : ((P⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) =
      (P : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
    DedekindResidue.val_unit_inv (K := K) (I := P)
  have haInvUnit : (T.a : K)⁻¹ ∈
      ((P⁻¹ : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hPInv, coe_toPrincipalIdeal]
    rw [← Units.val_inv_eq_inv_val]
    exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K))
      ((T.a⁻¹ : Kˣ) : K)
  have haInv : (T.a : K)⁻¹ ∈ (P : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← hPInvVal]
    exact haInvUnit
  have hmul : y.1 * (T.a : K)⁻¹ ∈
      (((P * C⁻¹) * P⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← Units.val_mul] using FractionalIdeal.mul_mem_mul hy haInvUnit
  have hcancel : (P * C⁻¹) * P⁻¹ = C⁻¹ := by
    calc
      (P * C⁻¹) * P⁻¹ = P * (C⁻¹ * P⁻¹) := by rw [mul_assoc]
      _ = P * (P⁻¹ * C⁻¹) := by rw [mul_comm C⁻¹ P⁻¹]
      _ = (P * P⁻¹) * C⁻¹ := by rw [← mul_assoc]
      _ = C⁻¹ := by simp
  have hcancelVal := congrArg Units.val hcancel
  rw [hcancelVal] at hmul
  change y.1 * (T.a : K)⁻¹ ∈ (C⁻¹ : FractionalIdeal (𝓞 K)⁰ K) at hmul
  simpa [div_eq_mul_inv] using hmul

private noncomputable def hk_dualPoint_frequencyLift [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)}) :
    {u : 𝓞 K // y.1 - (T.a : K) * (u : K) ∈
      (((hkDifferentUnit K * idealUnit J hJ.1)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) ∧
      algebraMap (𝓞 K) K u =
        (hk_dualPoint_denominator m J hJ T : K) * (y.1 / (T.a : K))} := by
  classical
  let Cideal : Ideal (𝓞 K) := T.B * J
  let hC : Cideal ≠ ⊥ := mul_ne_zero T.coprime.1 hJ.1
  let C : NumberFieldFractionalIdealGroup K := idealUnit Cideal hC
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K T.a
  let M : NumberFieldFractionalIdealGroup K := hkModulusUnit m
  let Junit : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let Dunit : NumberFieldFractionalIdealGroup K := hkDifferentUnit K
  have hCunit : idealUnit Cideal hC = idealUnit T.B T.coprime.1 * Junit := by
    apply Units.ext
    simp [Cideal, Junit, idealUnit, FractionalIdeal.coeIdeal_mul]
  have hCunit' : C = idealUnit T.B T.coprime.1 * Junit := hCunit
  have hCprime : IsCoprimeTo m Cideal := by
    simpa [Cideal] using hk_dualPoint_BJ_coprime m J hJ T
  let d : 𝓞 K := hk_dualPoint_denominator m J hJ T
  have hdlift := hk_dualPoint_denominator_spec m J hJ T
  have hd : d ∈ Cideal := by simpa [d, Cideal] using hdlift.1
  have hd0 : d ≠ 0 := by simpa [d] using hdlift.2.1
  have hdmod : d - 1 ∈ modulusIdeal m := by simpa [d] using hdlift.2.2
  let t : K := y.1 / (T.a : K)
  have ht : t ∈ (C⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
    exact hk_dualPoint_div_mem m J hJ T y
  have hdC : (d : K) ∈ (C : FractionalIdeal (𝓞 K)⁰ K) := by
    change algebraMap (𝓞 K) K d ∈ (Cideal : FractionalIdeal (𝓞 K)⁰ K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hd
  have hdt : (d : K) * t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := C),
      ← Units.val_mul, mul_inv_cancel, Units.val_one] using
      FractionalIdeal.mul_mem_mul hdC ht
  have hchoose : ∃ u : 𝓞 K, algebraMap (𝓞 K) K u = (d : K) * t :=
    (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 K))).mp hdt
  let u : 𝓞 K := Classical.choose hchoose
  have hu : algebraMap (𝓞 K) K u = (d : K) * t := Classical.choose_spec hchoose
  have h1d : (1 - d : 𝓞 K) ∈ modulusIdeal m := by
    have hEq : (1 - d : 𝓞 K) = -(d - 1) := by ring
    rw [hEq]
    exact (modulusIdeal m).neg_mem hdmod
  have hMmem : (1 - (d : K)) ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := by
    change algebraMap (𝓞 K) K (1 - d) ∈ (modulusIdeal m : FractionalIdeal (𝓞 K)⁰ K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) h1d
  have hdeltaM : t - (u : K) ∈ ((M * C⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    have hEq : t - (u : K) = (1 - (d : K)) * t := by
      change t - algebraMap (𝓞 K) K u = _
      rw [hu]
      ring
    rw [hEq]
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := C),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul hMmem ht
  have hfactor : P * (M * C⁻¹) = (Dunit * Junit)⁻¹ := by
    rw [hCunit']
    change P * (M * (idealUnit T.B T.coprime.1 * Junit)⁻¹) = _
    rw [T.ideal_eq]
    simp [P, M, Dunit, Junit, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have haP : (T.a : K) ∈ (P : FractionalIdeal (𝓞 K)⁰ K) := by
    change (T.a : K) ∈ ((P : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K)) (T.a : K)
  have hmul : (T.a : K) * (t - (u : K)) ∈
      (((P * (M * C⁻¹) : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K)) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := C),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul haP hdeltaM
  have hz : (T.a : K) * (t - (u : K)) ∈
      (((Dunit * Junit)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hfactor]
    exact hmul
  have hya : y.1 - (T.a : K) * (u : K) = (T.a : K) * (t - (u : K)) := by
    dsimp [t]
    field_simp [Units.ne_zero T.a]
  exact ⟨u, hya ▸ hz, hu⟩

private theorem hk_traceDual_one :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

private theorem hk_dualPoint_trace_integer [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})
    (x : 𝓞 K) (hx : x ∈ J) :
    Algebra.trace ℚ K
      ((y.1 - (T.a : K) * (hk_dualPoint_frequencyLift m J hJ T y).1) *
        algebraMap (𝓞 K) K x) ∈ Set.range (algebraMap ℤ ℚ) := by
  classical
  let Junit : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let Dunit : NumberFieldFractionalIdealGroup K := hkDifferentUnit K
  let z : K := y.1 - (T.a : K) * (hk_dualPoint_frequencyLift m J hJ T y).1
  have hz : z ∈ (((Dunit * Junit)⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) := (hk_dualPoint_frequencyLift m J hJ T y).2.1
  have hxJ : algebraMap (𝓞 K) K x ∈ (Junit : FractionalIdeal (𝓞 K)⁰ K) := by
    change algebraMap (𝓞 K) K x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hx
  have hzFrac : z ∈ ((Dunit * Junit : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← DedekindResidue.val_unit_inv (K := K) (I := Dunit * Junit)]
    exact hz
  have hmul : z * algebraMap (𝓞 K) K x ∈
      (((Dunit * Junit)⁻¹ * Junit : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := Dunit * Junit),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul hzFrac hxJ
  have hcancel : (Dunit * Junit)⁻¹ * Junit = Dunit⁻¹ := by
    simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  rw [congrArg Units.val hcancel] at hmul
  have hDdual : ((Dunit⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [DedekindResidue.val_unit_inv (K := K) (I := Dunit), hk_traceDual_one]
    simp [Dunit, hkDifferentUnit, idealUnit]
  have hdual : z * algebraMap (𝓞 K) K x ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hDdual]
    change z * algebraMap (𝓞 K) K x ∈
      ((Dunit⁻¹ : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)
    exact hmul
  have hone : (1 : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by simp
  have htraceForm :=
    (FractionalIdeal.mem_dual (show (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 by simp)).mp
      hdual (1 : K) hone
  rw [Algebra.traceForm_apply] at htraceForm
  simpa using htraceForm

private theorem hk_dualPoint_phase [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})
    (x : 𝓞 K) (hx : x ∈ J) :
    (Real.fourierChar
      (⟪embeddingCoords K (algebraMap (𝓞 K) K x),
        (hk_dualPointToVector m J hJ
          (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1) y :
            EuclideanSpace ℝ (index K))⟫) : ℂ) =
      T.additive
        (Ideal.Quotient.mk (modulusIdeal m) x *
          Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) := by
  classical
  let u : 𝓞 K := (hk_dualPoint_frequencyLift m J hJ T y).1
  have hInt := hk_dualPoint_trace_integer m J hJ T y x hx
  obtain ⟨n, hn⟩ := Set.mem_range.mp hInt
  have htraceSplit : Algebra.trace ℚ K (y.1 * (algebraMap (𝓞 K) K x)) =
      Algebra.trace ℚ K ((T.a : K) * ((algebraMap (𝓞 K) K x) * (u : K))) +
        algebraMap ℤ ℚ n := by
    calc
      Algebra.trace ℚ K (y.1 * (algebraMap (𝓞 K) K x)) =
          Algebra.trace ℚ K
            ((T.a : K) * ((algebraMap (𝓞 K) K x) * (u : K))) +
            Algebra.trace ℚ K
              ((y.1 - (T.a : K) * (u : K)) * (algebraMap (𝓞 K) K x)) := by
                rw [← map_add (Algebra.trace ℚ K)]
                congr 1
                ring_nf
      _ = _ := by rw [hn]
  have htraceReal :
      ((Algebra.trace ℚ K (y.1 * (algebraMap (𝓞 K) K x)) : ℚ) : ℝ) =
        ((Algebra.trace ℚ K
          ((T.a : K) * ((algebraMap (𝓞 K) K x) * (u : K))) : ℚ) : ℝ) + (n : ℝ) := by
    exact_mod_cast htraceSplit
  have hcharInt : Real.fourierChar (n : ℝ) = 1 := by
    rw [Real.fourierChar_apply']
    convert Circle.exp_int_mul_two_pi n using 1 <;> ring
  have hchar :
      Real.fourierChar ((Algebra.trace ℚ K (y.1 * (algebraMap (𝓞 K) K x)) : ℚ) : ℝ) =
        Real.fourierChar ((Algebra.trace ℚ K
          ((T.a : K) * ((algebraMap (𝓞 K) K x) * (u : K))) : ℚ) : ℝ) := by
    rw [htraceReal, AddChar.map_add_eq_mul, hcharInt, mul_one]
  have hinner :
      ⟪embeddingCoords K (algebraMap (𝓞 K) K x),
        (hk_dualPointToVector m J hJ
          (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1) y :
            EuclideanSpace ℝ (index K))⟫ =
        ((Algebra.trace ℚ K (y.1 * (algebraMap (𝓞 K) K x)) : ℚ) : ℝ) := by
    change ⟪embeddingCoords K (algebraMap (𝓞 K) K x),
        (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
          (embeddingCoords K y.1)⟫ = _
    rw [real_inner_comm]
    exact DedekindResidue.inner_diagScale_embeddingCoords K
      (algebraMap (𝓞 K) K x) y.1
  calc
    (Real.fourierChar
      (⟪embeddingCoords K (algebraMap (𝓞 K) K x),
        (hk_dualPointToVector m J hJ
          (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1) y :
            EuclideanSpace ℝ (index K))⟫) : ℂ) =
        (Real.fourierChar ((Algebra.trace ℚ K
          (y.1 * (algebraMap (𝓞 K) K x)) : ℚ) : ℝ) : ℂ) := by rw [hinner]
    _ = (Real.fourierChar ((Algebra.trace ℚ K
          ((T.a : K) * ((algebraMap (𝓞 K) K x) * (u : K))) : ℚ) : ℝ) : ℂ) :=
      congrArg (fun z : Circle => (z : ℂ)) hchar
    _ = T.additive (Ideal.Quotient.mk (modulusIdeal m) (x * u)) :=
      (T.trace_value (x * u)).symm
    _ = T.additive
        (Ideal.Quotient.mk (modulusIdeal m) x *
          Ideal.Quotient.mk (modulusIdeal m) u) := by rw [map_mul]

private theorem hk_finite_gauss_shift {m : RayClassModulus K}
    {ψ : RayClassGroup m →* ℂˣ}
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) (u : HKResidueRing m) :
    ∑ r : HKResidueRing m, χ.character r * T.additive (r * u) =
      χ.character⁻¹ u * hkGaussSum χ T := by
  classical
  have h := OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mulShift
    χ.character χ.primitive T.additive u
  simpa [gaussSum, AddChar.mulShift_apply, hkGaussSum, mul_comm] using h

private theorem hk_pointIdealUnit_of_mem
    (I : NumberFieldFractionalIdealGroup K) (x : K)
    (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) (hx0 : x ≠ 0) :
    ∃ hE : hkIntegralPart
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((I : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) ≠ ⊥,
      idealUnit (hkIntegralPart
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((I : FractionalIdeal (𝓞 K)⁰ K)⁻¹))) hE =
        toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) * I⁻¹ := by
  classical
  let F : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
      ((I : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
  let E : Ideal (𝓞 K) := hkIntegralPart F
  have hEcoe : (E : FractionalIdeal (𝓞 K)⁰ K) = F := by
    simpa [E, F] using hk_point_ideal_integral I hx
  have hspan0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0
  have hIinv0 : ((I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) ≠ 0 := by
    rw [← DedekindResidue.val_unit_inv (K := K) (I := I)]
    exact Units.ne_zero (I⁻¹)
  have hF0 : F ≠ 0 := mul_ne_zero hspan0 hIinv0
  have hE0 : E ≠ ⊥ := by
    intro hbot
    have hzero : (E : FractionalIdeal (𝓞 K)⁰ K) = 0 := by simp [hbot]
    rw [hEcoe] at hzero
    exact hF0 hzero
  have hEunit : idealUnit E hE0 =
      toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) * I⁻¹ := by
    apply Units.ext
    simpa [E, F, idealUnit, coe_toPrincipalIdeal,
      DedekindResidue.val_unit_inv] using hEcoe
  exact ⟨hE0, hEunit⟩

set_option maxHeartbeats 4000000 in
private theorem hk_dualPoint_frequencyLift_ne_zero [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (T : HKTraceDatum m)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})
    (hy0 : y.1 ≠ 0) :
    (hk_dualPoint_frequencyLift m J hJ T y).1 ≠ 0 := by
  let hfreq := hk_dualPoint_frequencyLift m J hJ T y
  have hd0 : (hk_dualPoint_denominator m J hJ T : K) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
      (hk_dualPoint_denominator_spec m J hJ T).2.1
  have hydiv : y.1 / (T.a : K) ≠ 0 := div_ne_zero hy0 (Units.ne_zero T.a)
  intro hu0
  have hval := hfreq.2.2
  rw [hu0] at hval
  have hprod : (hk_dualPoint_denominator m J hJ T : K) *
      (y.1 / (T.a : K)) = 0 := by simpa using hval.symm
  exact (mul_ne_zero hd0 hydiv) hprod

set_option maxHeartbeats 4000000 in
private theorem hk_dualPoint_weight_coeff_of_unit [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})
    (hy0 : y.1 ≠ 0)
    (hu : IsUnit (Ideal.Quotient.mk (modulusIdeal m)
      (hk_dualPoint_frequencyLift m J hJ T y).1)) :
    charValue ψ T.B *
        hkPointWeight (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1)) y.1 =
      (charValue ψ J)⁻¹ * χ.character⁻¹
        (Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T y).1) := by
  classical
  let u : 𝓞 K := (hk_dualPoint_frequencyLift m J hJ T y).1
  have hu0 : u ≠ 0 := by
    simpa [u] using hk_dualPoint_frequencyLift_ne_zero m J hJ T y hy0
  have hspanCoprime : IsCoprimeTo m (Ideal.span ({u} : Set (𝓞 K))) :=
    (hk_span_coprime_iff_unit_residue (x := u) hu0).2 hu
  let SU : Ideal (𝓞 K) := Ideal.span ({u} : Set (𝓞 K))
  let hspan0 : SU ≠ ⊥ := hspanCoprime.1
  let uUnit : Kˣ := Units.mk0 (algebraMap (𝓞 K) K u)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hu0)
  let Uunit : NumberFieldFractionalIdealGroup K := idealUnit SU hspan0
  have hspanUnit : Uunit = toPrincipalIdeal (𝓞 K) K uUnit := by
    apply Units.ext
    simp only [Uunit, SU, idealUnit, Units.val_mk0,
      FractionalIdeal.coeIdeal_span_singleton, coe_toPrincipalIdeal]
    congr 1
    all_goals simp [uUnit]
  have hUeq : Uunit = idealUnit SU hspanCoprime.1 := by
    apply Units.ext
    rfl
  have hUprime : Uunit ∈ rayClassPrimeToIdeals m := by
    rw [hUeq]
    exact hspanCoprime.2
  let BJ : Ideal (𝓞 K) := T.B * J
  let hBJ0 : BJ ≠ ⊥ := mul_ne_zero T.coprime.1 hJ.1
  let BJunit : NumberFieldFractionalIdealGroup K := idealUnit BJ hBJ0
  have hBJunit : BJunit = idealUnit T.B T.coprime.1 * idealUnit J hJ.1 := by
    apply Units.ext
    simp [BJunit, BJ, idealUnit, FractionalIdeal.coeIdeal_mul]
  have hBJcoprime : IsCoprimeTo m BJ := by
    simpa [BJ] using hk_dualPoint_BJ_coprime m J hJ T
  let Eideal : Ideal (𝓞 K) := BJ * SU
  let hE0 : Eideal ≠ ⊥ := mul_ne_zero hBJ0 hspan0
  let Eunit : NumberFieldFractionalIdealGroup K := idealUnit Eideal hE0
  have hEunitFactor : Eunit = BJunit * Uunit := by
    calc
      Eunit = idealUnit (BJ * SU) hE0 := by rfl
      _ = idealUnit BJ hBJ0 * idealUnit SU hspan0 :=
        hk_idealUnit_mul BJ SU hBJ0 hspan0 hE0
      _ = BJunit * Uunit := by rfl
  have hEprime : idealUnit Eideal hE0 ∈ rayClassPrimeToIdeals m := by
    have hEunitEq : idealUnit Eideal hE0 = BJunit * Uunit := by
      calc
        idealUnit Eideal hE0 = Eunit := rfl
        _ = BJunit * Uunit := hEunitFactor
    rw [hEunitEq]
    exact (rayClassPrimeToIdeals m).mul_mem hBJcoprime.2 hUprime
  have hEcoprime : IsCoprimeTo m Eideal := ⟨hE0, hEprime⟩
  let M : NumberFieldFractionalIdealGroup K := hkModulusUnit m
  let Dunit : NumberFieldFractionalIdealGroup K := hkDifferentUnit K
  let Junit : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K T.a
  let Idual : NumberFieldFractionalIdealGroup K := hkDualIdeal m Junit
  let yUnit : Kˣ := Units.mk0 y.1 hy0
  let qDen : Kˣ := T.a * uUnit
  let qUnit : Kˣ := Units.mk0 (y.1 / (qDen : K)) (div_ne_zero hy0 (Units.ne_zero qDen))
  have huUnitVal : (uUnit : K) = (u : K) := by
    change algebraMap (𝓞 K) K u = algebraMap (𝓞 K) K u
    rfl
  have hdenUnit : P * Uunit = toPrincipalIdeal (𝓞 K) K qDen := by
    calc
      P * Uunit = P * toPrincipalIdeal (𝓞 K) K uUnit := by rw [hspanUnit]
      _ = toPrincipalIdeal (𝓞 K) K (T.a * uUnit) := by
        symm
        exact map_mul (toPrincipalIdeal (𝓞 K) K) T.a uUnit
  have hyUnit : yUnit = qUnit * qDen := by
    apply Units.ext
    change y.1 = _
    dsimp [qUnit, qDen]
    field_simp [Units.ne_zero T.a, Units.ne_zero uUnit]
  have hyPrincipal : toPrincipalIdeal (𝓞 K) K yUnit =
      toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit) := by
    calc
      toPrincipalIdeal (𝓞 K) K yUnit =
          toPrincipalIdeal (𝓞 K) K (qUnit * qDen) := by rw [hyUnit]
      _ = toPrincipalIdeal (𝓞 K) K qUnit *
          toPrincipalIdeal (𝓞 K) K qDen := by rw [map_mul]
      _ = toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit) := by rw [← hdenUnit]
  have hdfactor : hkDualIdeal m Junit = P * BJunit⁻¹ := by
    simpa [P, BJunit] using hk_dualIdeal_factor m J hJ T
  have hAunit : toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ =
      toPrincipalIdeal (𝓞 K) K qUnit * Uunit * BJunit := by
    calc
      toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ =
          toPrincipalIdeal (𝓞 K) K yUnit * (P * BJunit⁻¹)⁻¹ := by
            change toPrincipalIdeal (𝓞 K) K yUnit * (hkDualIdeal m Junit)⁻¹ = _
            rw [hdfactor]
      _ = (toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit)) *
          (P * BJunit⁻¹)⁻¹ := by rw [hyPrincipal]
      _ = toPrincipalIdeal (𝓞 K) K qUnit * Uunit * BJunit := by
        simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  let hfreq := hk_dualPoint_frequencyLift m J hJ T y
  have hz : y.1 - (T.a : K) * (u : K) ∈
      (((Dunit * Junit)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    simpa [hfreq, u, Dunit, Junit] using hfreq.2.1
  have hdenInv : (qDen : K)⁻¹ ∈
      (((P * Uunit)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    have hInv : (P * Uunit)⁻¹ =
        toPrincipalIdeal (𝓞 K) K qDen⁻¹ := by rw [hdenUnit]; simp
    rw [hInv, coe_toPrincipalIdeal, ← Units.val_inv_eq_inv_val]
    exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K))
      ((qDen⁻¹ : Kˣ) : K)
  have hratioIdeal : (Dunit * Junit)⁻¹ * (P * Uunit)⁻¹ =
      M * Eunit⁻¹ := by
    rw [hEunitFactor, hBJunit, T.ideal_eq]
    simp [M, Dunit, Junit, P, Uunit, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have hcross :
      (y.1 - (T.a : K) * (u : K)) * (qDen : K)⁻¹ ∈
        (((Dunit * Junit)⁻¹ * (P * Uunit)⁻¹ : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := Dunit * Junit),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul hz hdenInv
  have hratio : (Dunit * Junit)⁻¹ * (P * Uunit)⁻¹ = M * Eunit⁻¹ := hratioIdeal
  rw [congrArg Units.val hratio] at hcross
  have hqmod : (qUnit : K) - 1 ∈ ((M * Eunit⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    have hEq : (qUnit : K) - 1 =
        (y.1 - (T.a : K) * (u : K)) * (qDen : K)⁻¹ := by
      dsimp [qUnit, qDen]
      rw [huUnitVal]
      have ha : (T.a : K) ≠ 0 := Units.ne_zero T.a
      have huK : (u : K) ≠ 0 :=
        (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hu0
      field_simp [ha, huK]
    rw [hEq]
    exact hcross
  have hqRay : IsRayCongruent m qUnit :=
    hk_rayCongruent_of_modulus_fraction m Eideal hEcoprime qUnit hqmod
  have hqPrime : toPrincipalIdeal (𝓞 K) K qUnit ∈ rayClassPrimeToIdeals m :=
    hk_principal_rayPrimeTo_of_congruent m qUnit hqRay
  have hAprime : (toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹) ∈
      rayClassPrimeToIdeals m := by
    rw [hAunit]
    exact (rayClassPrimeToIdeals m).mul_mem
      ((rayClassPrimeToIdeals m).mul_mem hqPrime hspanCoprime.2) hBJcoprime.2
  have hEpointData := hk_pointIdealUnit_of_mem Idual y.1 y.2 hy0
  let Epoint : Ideal (𝓞 K) := hkIntegralPart
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ y.1 *
      ((Idual : FractionalIdeal (𝓞 K)⁰ K)⁻¹))
  have hEpoint0 : Epoint ≠ ⊥ := Classical.choose hEpointData
  have hEpointUnit : idealUnit Epoint hEpoint0 =
      toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ :=
    Classical.choose_spec hEpointData
  have hEpointPrime : idealUnit Epoint hEpoint0 ∈ rayClassPrimeToIdeals m := by
    rw [hEpointUnit]
    exact hAprime
  have hEpointCop : IsCoprimeTo m Epoint := ⟨hEpoint0, hEpointPrime⟩
  have hpoint : hkPointWeight (ψ⁻¹) Idual y.1 = charValue (ψ⁻¹) Epoint := by
    simp [hkPointWeight, hy0, Epoint]
  let qMap : rayClassPrimeToIdeals m →* RayClassGroup m := hk_rayClassQuotientMap m
  let qP : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K qUnit, hqPrime⟩
  have hUeq : Uunit = idealUnit SU hspanCoprime.1 := by
    apply Units.ext
    rfl
  have hUprime : Uunit ∈ rayClassPrimeToIdeals m := by
    rw [hUeq]
    exact hspanCoprime.2
  let qU : rayClassPrimeToIdeals m := ⟨Uunit, hUprime⟩
  let qB : rayClassPrimeToIdeals m := ⟨idealUnit T.B T.coprime.1, T.coprime.2⟩
  let qJ : rayClassPrimeToIdeals m := ⟨idealUnit J hJ.1, hJ.2⟩
  let qA : rayClassPrimeToIdeals m :=
    ⟨toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹, hAprime⟩
  let qE : rayClassPrimeToIdeals m := ⟨idealUnit Epoint hEpoint0, hEpointPrime⟩
  have hqOne : qMap qP = 1 := hk_principal_rayClass_quotient_one m qUnit hqPrime hqRay
  have hqUClass : qMap qU = rayClass m (Ideal.span ({u} : Set (𝓞 K))) hspanCoprime := by
    have hspanP : qU =
        ⟨idealUnit (Ideal.span ({u} : Set (𝓞 K))) hspanCoprime.1, hspanCoprime.2⟩ := by
      apply Subtype.ext
      simpa [SU] using hUeq
    rw [hspanP]
    rfl
  have hqBClass : qMap qB = rayClass m T.B T.coprime := rfl
  have hqJClass : qMap qJ = rayClass m J hJ := rfl
  have hqAeq : qA = qP * qU * qB * qJ := by
    apply Subtype.ext
    dsimp [qA, qP, qU, qB, qJ]
    rw [hAunit, hBJunit]
    simp [mul_assoc]
  have hqEclass : qMap qE = qMap qA := by
    have hqE : qE = qA := by
      apply Subtype.ext
      exact hEpointUnit
    rw [hqE]
  have hχu : χ.character (Ideal.Quotient.mk (modulusIdeal m) u) =
      (ψ (qMap qU) : ℂ) := by
    calc
      χ.character (Ideal.Quotient.mk (modulusIdeal m) u) =
          charValue ψ (Ideal.span ({u} : Set (𝓞 K))) :=
            χ.principal_value u hspanCoprime
      _ = (ψ (qMap qU) : ℂ) := by
        rw [charValue, dif_pos hspanCoprime]
        exact congrArg (fun z : RayClassGroup m => (ψ z : ℂ)) hqUClass.symm
  have hBval : charValue ψ T.B = (ψ (qMap qB) : ℂ) := by
    rw [charValue, dif_pos T.coprime, ← hqBClass]
  have hJval : charValue ψ J = (ψ (qMap qJ) : ℂ) := by
    rw [charValue, dif_pos hJ, ← hqJClass]
  have hpointVal : hkPointWeight (ψ⁻¹) Idual y.1 =
      (ψ⁻¹ (qMap qE) : ℂ) := by
    rw [hpoint]
    rw [charValue, dif_pos hEpointCop]
    have hEclassRay : qMap qE = rayClass m Epoint hEpointCop := rfl
    rw [← hEclassRay]
  have hχuInv : χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m) u) =
      ((ψ (qMap qU) : ℂ)⁻¹) := by
    rw [MulChar.inv_apply_eq_inv, hχu]
    simp
  rw [hBval, hJval, hpointVal, hχuInv]
  have hqAclass : qMap qA = qMap qU * qMap qB * qMap qJ := by
    calc
      qMap qA = qMap qP * qMap qU * qMap qB * qMap qJ := by
        rw [hqAeq]
        simp only [map_mul]
      _ = qMap qU * qMap qB * qMap qJ := by
        rw [hqOne]
        change ((1 * qMap qU) * qMap qB) * qMap qJ =
          (qMap qU * qMap qB) * qMap qJ
        exact congrArg (fun z => (z * qMap qB) * qMap qJ) (one_mul (qMap qU))
  rw [hqEclass, hqAclass]
  have hchar : ψ (qMap qB) *
      ψ⁻¹ (qMap qU * qMap qB * qMap qJ) =
      ψ⁻¹ (qMap qJ) * ψ⁻¹ (qMap qU) := by
    simp only [MonoidHom.inv_apply, map_mul]
    calc
      ψ (qMap qB) *
          (((ψ (qMap qU))⁻¹ * (ψ (qMap qB))⁻¹) * (ψ (qMap qJ))⁻¹) =
          (ψ (qMap qB) * (ψ (qMap qB))⁻¹) *
            ((ψ (qMap qJ))⁻¹ * (ψ (qMap qU))⁻¹) := by ac_rfl
      _ = (ψ (qMap qJ))⁻¹ * (ψ (qMap qU))⁻¹ := by simp
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val, MonoidHom.inv_apply] using
    congrArg (fun z : ℂˣ => (z : ℂ)) hchar

private theorem hk_dualPoint_weight_zero_of_nonunit_lift [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (T : HKTraceDatum m) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})
    (hy0 : y.1 ≠ 0)
    (hu0 : (hk_dualPoint_frequencyLift m J hJ T y).1 ≠ 0)
    (huN : ¬ IsUnit (Ideal.Quotient.mk (modulusIdeal m)
      (hk_dualPoint_frequencyLift m J hJ T y).1)) :
    hkPointWeight (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1)) y.1 = 0 := by
  classical
  let u : 𝓞 K := (hk_dualPoint_frequencyLift m J hJ T y).1
  have hu0' : u ≠ 0 := by simpa [u] using hu0
  let SU : Ideal (𝓞 K) := Ideal.span ({u} : Set (𝓞 K))
  have hspan0 : SU ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hu0'
  let uUnit : Kˣ := Units.mk0 (algebraMap (𝓞 K) K u)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hu0')
  let Uunit : NumberFieldFractionalIdealGroup K := idealUnit SU hspan0
  have hspanUnit : Uunit = toPrincipalIdeal (𝓞 K) K uUnit := by
    simpa [Uunit, SU, uUnit] using hk_idealUnit_span u hu0'
  let BJ : Ideal (𝓞 K) := T.B * J
  have hBJ0 : BJ ≠ ⊥ := mul_ne_zero T.coprime.1 hJ.1
  let BJunit : NumberFieldFractionalIdealGroup K := idealUnit BJ hBJ0
  have hBJunit : BJunit = idealUnit T.B T.coprime.1 * idealUnit J hJ.1 := by
    apply Units.ext
    simp [BJunit, BJ, idealUnit, FractionalIdeal.coeIdeal_mul]
  have hBJcoprime : IsCoprimeTo m BJ := by
    simpa [BJ] using hk_dualPoint_BJ_coprime m J hJ T
  let Eideal : Ideal (𝓞 K) := BJ * SU
  have hE0 : Eideal ≠ ⊥ := mul_ne_zero hBJ0 hspan0
  let Eunit : NumberFieldFractionalIdealGroup K := idealUnit Eideal hE0
  have hEunitFactor : Eunit = BJunit * Uunit := by
    calc
      Eunit = idealUnit (BJ * SU) hE0 := rfl
      _ = idealUnit BJ hBJ0 * idealUnit SU hspan0 :=
        hk_idealUnit_mul BJ SU hBJ0 hspan0 hE0
      _ = BJunit * Uunit := by rfl
  let M : NumberFieldFractionalIdealGroup K := hkModulusUnit m
  let Dunit : NumberFieldFractionalIdealGroup K := hkDifferentUnit K
  let Junit : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K T.a
  let Idual : NumberFieldFractionalIdealGroup K := hkDualIdeal m Junit
  let yUnit : Kˣ := Units.mk0 y.1 hy0
  let qDen : Kˣ := T.a * uUnit
  let qUnit : Kˣ := Units.mk0 (y.1 / (qDen : K))
    (div_ne_zero hy0 (Units.ne_zero qDen))
  have huUnitVal : (uUnit : K) = (u : K) := by
    change algebraMap (𝓞 K) K u = algebraMap (𝓞 K) K u
    rfl
  have hdenUnit : P * Uunit = toPrincipalIdeal (𝓞 K) K qDen := by
    calc
      P * Uunit = P * toPrincipalIdeal (𝓞 K) K uUnit := by rw [hspanUnit]
      _ = toPrincipalIdeal (𝓞 K) K (T.a * uUnit) := by
        symm
        exact map_mul (toPrincipalIdeal (𝓞 K) K) T.a uUnit
  have hyUnit : yUnit = qUnit * qDen := by
    apply Units.ext
    change y.1 = _
    dsimp [qUnit, qDen]
    field_simp [Units.ne_zero T.a, Units.ne_zero uUnit]
  have hyPrincipal : toPrincipalIdeal (𝓞 K) K yUnit =
      toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit) := by
    calc
      toPrincipalIdeal (𝓞 K) K yUnit =
          toPrincipalIdeal (𝓞 K) K (qUnit * qDen) := by rw [hyUnit]
      _ = toPrincipalIdeal (𝓞 K) K qUnit *
          toPrincipalIdeal (𝓞 K) K qDen := by rw [map_mul]
      _ = toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit) := by rw [← hdenUnit]
  have hdfactor : hkDualIdeal m Junit = P * BJunit⁻¹ := by
    simpa [P, BJunit] using hk_dualIdeal_factor m J hJ T
  have hAunit : toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ =
      toPrincipalIdeal (𝓞 K) K qUnit * Uunit * BJunit := by
    calc
      toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ =
          toPrincipalIdeal (𝓞 K) K yUnit * (P * BJunit⁻¹)⁻¹ := by
            change toPrincipalIdeal (𝓞 K) K yUnit *
              (hkDualIdeal m Junit)⁻¹ = _
            rw [hdfactor]
      _ = (toPrincipalIdeal (𝓞 K) K qUnit * (P * Uunit)) *
          (P * BJunit⁻¹)⁻¹ := by rw [hyPrincipal]
      _ = toPrincipalIdeal (𝓞 K) K qUnit * Uunit * BJunit := by
        simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  let hfreq := hk_dualPoint_frequencyLift m J hJ T y
  have hz : y.1 - (T.a : K) * (u : K) ∈
      (((Dunit * Junit)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    simpa [hfreq, u, Dunit, Junit] using hfreq.2.1
  have hdenInv : (qDen : K)⁻¹ ∈
      (((P * Uunit)⁻¹ : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    have hInv : (P * Uunit)⁻¹ =
        toPrincipalIdeal (𝓞 K) K qDen⁻¹ := by rw [hdenUnit]; simp
    rw [hInv, coe_toPrincipalIdeal, ← Units.val_inv_eq_inv_val]
    exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K))
      ((qDen⁻¹ : Kˣ) : K)
  have hratioIdeal : (Dunit * Junit)⁻¹ * (P * Uunit)⁻¹ = M * Eunit⁻¹ := by
    rw [hEunitFactor, hBJunit, T.ideal_eq]
    simp [M, Dunit, Junit, P, Uunit, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have hcross :
      (y.1 - (T.a : K) * (u : K)) * (qDen : K)⁻¹ ∈
        (((Dunit * Junit)⁻¹ * (P * Uunit)⁻¹ : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [← DedekindResidue.val_unit_inv (K := K) (I := Dunit * Junit),
      ← Units.val_mul] using FractionalIdeal.mul_mem_mul hz hdenInv
  rw [congrArg Units.val hratioIdeal] at hcross
  have hqmod : (qUnit : K) - 1 ∈ ((M * Eunit⁻¹ : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    have hEq : (qUnit : K) - 1 =
        (y.1 - (T.a : K) * (u : K)) * (qDen : K)⁻¹ := by
      dsimp [qUnit, qDen]
      rw [huUnitVal]
      have ha : (T.a : K) ≠ 0 := Units.ne_zero T.a
      have huK : (u : K) ≠ 0 :=
        (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hu0'
      field_simp [ha, huK]
    rw [hEq]
    exact hcross
  have hEpointData := hk_pointIdealUnit_of_mem Idual y.1 y.2 hy0
  let Epoint : Ideal (𝓞 K) := hkIntegralPart
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ y.1 *
      ((Idual : FractionalIdeal (𝓞 K)⁰ K)⁻¹))
  have hEpoint0 : Epoint ≠ ⊥ := Classical.choose hEpointData
  have hEpointUnit : idealUnit Epoint hEpoint0 =
      toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ := Classical.choose_spec hEpointData
  have hEpointFrac : (Epoint : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (qUnit : K) *
        (Eideal : FractionalIdeal (𝓞 K)⁰ K) := by
    have hpointGroup : idealUnit Epoint hEpoint0 =
        toPrincipalIdeal (𝓞 K) K qUnit * Eunit := by
      calc
        idealUnit Epoint hEpoint0 = toPrincipalIdeal (𝓞 K) K yUnit * Idual⁻¹ :=
          hEpointUnit
        _ = toPrincipalIdeal (𝓞 K) K qUnit * Uunit * BJunit := hAunit
        _ = toPrincipalIdeal (𝓞 K) K qUnit * Eunit := by
          rw [hEunitFactor]
          ac_rfl
    have hval := congrArg
      (fun X : NumberFieldFractionalIdealGroup K =>
        (X : FractionalIdeal (𝓞 K)⁰ K)) hpointGroup
    simpa [Eunit, idealUnit, coe_toPrincipalIdeal] using hval
  have hpointCoprime : IsCoprimeTo m Epoint ↔ IsCoprimeTo m Eideal :=
    hk_coprimeTo_principal_congruence Epoint Eideal hEpoint0 hE0 qUnit
      hEpointFrac hqmod
  have hEcoprime : IsCoprimeTo m Eideal ↔ IsCoprimeTo m SU := by
    constructor
    · rintro ⟨_, hEprime⟩
      have hUeq : Uunit = BJunit⁻¹ * Eunit := by
        rw [hEunitFactor]
        group
      have hUprime : Uunit ∈ rayClassPrimeToIdeals m := by
        rw [hUeq]
        exact (rayClassPrimeToIdeals m).mul_mem
          ((rayClassPrimeToIdeals m).inv_mem hBJcoprime.2) hEprime
      exact ⟨hspan0, hUprime⟩
    · rintro ⟨_, hUprime⟩
      have hEprime : Eunit ∈ rayClassPrimeToIdeals m := by
        rw [hEunitFactor]
        exact (rayClassPrimeToIdeals m).mul_mem hBJcoprime.2 hUprime
      exact ⟨hE0, hEprime⟩
  have hnot : ¬ IsCoprimeTo m Epoint := by
    intro hEpointCop
    have hEidealCop := hpointCoprime.mp hEpointCop
    have hSUcop := hEcoprime.mp hEidealCop
    exact huN ((hk_span_coprime_iff_unit_residue hu0').mp hSUcop)
  have hpoint : hkPointWeight (ψ⁻¹) Idual y.1 = charValue (ψ⁻¹) Epoint := by
    simp [hkPointWeight, hy0, Epoint]
  rw [hpoint]
  simp [charValue, hnot]

private theorem hk_dualPoint_weight_coeff_at_zero [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J) :
    charValue ψ T.B *
        hkPointWeight (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1)) 0 =
      (charValue ψ J)⁻¹ * χ.character⁻¹
        (Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T
            (⟨0, by exact FractionalIdeal.zero_mem _⟩ : {y : K // y ∈
        (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)})).1) := by
  classical
  let y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)} :=
    ⟨0, FractionalIdeal.zero_mem _⟩
  let hfreq := hk_dualPoint_frequencyLift m J hJ T y
  have hu0 : hfreq.1 = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simpa [hfreq, y] using hfreq.2.2
  change charValue ψ T.B *
      hkPointWeight (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1)) 0 =
    (charValue ψ J)⁻¹ * χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m) hfreq.1)
  rw [hu0]
  by_cases hm : m.finitePart = 0
  · have htop : modulusIdeal m = ⊤ := (modulusIdeal_eq_top_iff m).2 hm
    letI : Subsingleton (HKResidueRing m) :=
      (Ideal.Quotient.subsingleton_iff).2 htop
    have hzeroone :
        Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K) = 1 := Subsingleton.elim _ _
    have hχ0 : χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) = 1 := by
      rw [hzeroone]
      simp
    let M : NumberFieldFractionalIdealGroup K := hkModulusUnit m
    let Dunit : NumberFieldFractionalIdealGroup K := hkDifferentUnit K
    let Junit : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
    let Bunit : NumberFieldFractionalIdealGroup K := idealUnit T.B T.coprime.1
    let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K T.a
    let Idual : NumberFieldFractionalIdealGroup K := hkDualIdeal m Junit
    have hMone : M = 1 := by
      apply Units.ext
      simp [M, hkModulusUnit, htop, idealUnit]
    have hMone' : hkModulusUnit m = 1 := by simpa [M] using hMone
    have hBrel : Bunit = P * Dunit := by
      calc
        Bunit = P * M * Dunit := T.ideal_eq
        _ = P * Dunit := by rw [hMone]; simp
    have hIinv : Idual⁻¹ = Dunit * Junit := by
      simp only [Idual, hkDualIdeal, inv_inv]
      rw [hMone']
      simp [Dunit, Junit]
    have hprime (X : NumberFieldFractionalIdealGroup K) :
        X ∈ rayClassPrimeToIdeals m := by
      intro v hv
      have hfalse : False := by simpa [hm] using hv
      exact hfalse.elim
    let qMap : rayClassPrimeToIdeals m →* RayClassGroup m :=
      hk_rayClassQuotientMap m
    let qP : rayClassPrimeToIdeals m := ⟨P, hprime P⟩
    let qB : rayClassPrimeToIdeals m := ⟨Bunit, T.coprime.2⟩
    let qD : rayClassPrimeToIdeals m := ⟨Dunit, hprime Dunit⟩
    let qJ : rayClassPrimeToIdeals m := ⟨Junit, hJ.2⟩
    let qI : rayClassPrimeToIdeals m := ⟨Idual⁻¹, hprime Idual⁻¹⟩
    have hqPeq : qP = hkPrincipalRayIdeal m hm T.a := by
      apply Subtype.ext
      rfl
    have hqPsub : qP ∈ rayPrincipalIdealSubgroupInPrimeTo m := by
      rw [hqPeq]
      exact hk_principal_raySubgroup_of_finitePart_zero hm T.a
    have hqPone : qMap qP = 1 :=
      (QuotientGroup.eq_one_iff
        (N := rayPrincipalIdealSubgroupInPrimeTo m) qP).2 hqPsub
    have hqB : qB = qP * qD := by
      apply Subtype.ext
      exact hBrel
    have hqI : qI = qD * qJ := by
      apply Subtype.ext
      exact hIinv
    have hfc (η : RayClassGroup m →* ℂˣ)
        (X : NumberFieldFractionalIdealGroup K) :
        hkFractionalCharValue η X =
          (η (qMap ⟨X, hprime X⟩) : ℂ) := by
      rw [hkFractionalCharValue, dif_pos (hprime X)]
      rfl
    have hcharB : charValue ψ T.B = (ψ (qMap qB) : ℂ) := by
      have hqBclass : qMap qB = rayClass m T.B T.coprime := rfl
      rw [charValue, dif_pos T.coprime, ← hqBclass]
    have hcharJ : charValue ψ J = (ψ (qMap qJ) : ℂ) := by
      have hqJclass : qMap qJ = rayClass m J hJ := rfl
      rw [charValue, dif_pos hJ, ← hqJclass]
    have hpoint0 : hkPointWeight (ψ⁻¹) Idual 0 =
        hkFractionalCharValue (ψ⁻¹) (Idual⁻¹) := by
      simp [hkPointWeight, hm]
    have hqBmap : qMap qB = qMap qD := by
      rw [hqB]
      rw [map_mul, hqPone]
      exact one_mul (qMap qD)
    have hqImap : qMap qI = qMap qD * qMap qJ := by
      rw [hqI]
      simp only [map_mul]
    have hcharCancel : ψ (qMap qD) * ψ⁻¹ (qMap qD * qMap qJ) =
        ψ⁻¹ (qMap qJ) := by
      simp only [MonoidHom.inv_apply, map_mul]
      simp [mul_assoc]
    rw [hcharB, hpoint0, hfc (ψ⁻¹) (Idual⁻¹), hqBmap, hqImap,
      hcharJ, hχ0]
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, MonoidHom.inv_apply, mul_one] using
      congrArg (fun z : ℂˣ => (z : ℂ)) hcharCancel
  · have htop : modulusIdeal m ≠ ⊤ := by
      intro htop
      exact hm ((modulusIdeal_eq_top_iff m).mp htop)
    letI : Nontrivial (HKResidueRing m) := (Ideal.Quotient.nontrivial_iff).2 htop
    have hpoint0 : hkPointWeight (ψ⁻¹)
        (hkDualIdeal m (idealUnit J hJ.1)) 0 = 0 := by
      simp [hkPointWeight, hm]
    have hχ0 : χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) = 0 := by
      have hz : χ.character (Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) = 0 := by
        simpa using χ.character.map_zero
      simpa [MulChar.inv_apply_eq_inv] using hz
    rw [hpoint0, hχ0]
    simp

private theorem hk_dualPoint_weight_coeff [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (y : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)}) :
    charValue ψ T.B *
        hkPointWeight (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1)) y.1 =
      (charValue ψ J)⁻¹ * χ.character⁻¹
        (Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T y).1) := by
  classical
  by_cases hy0 : y.1 = 0
  · let y0 : {y : K // y ∈
      (hkDualIdeal m (idealUnit J hJ.1) : FractionalIdeal (𝓞 K)⁰ K)} :=
        ⟨0, FractionalIdeal.zero_mem _⟩
    have hyEq : y = y0 := by
      apply Subtype.ext
      exact hy0
    rw [hyEq]
    exact hk_dualPoint_weight_coeff_at_zero ψ χ T J hJ
  · have hu0 := hk_dualPoint_frequencyLift_ne_zero m J hJ T y hy0
    by_cases hu : IsUnit (Ideal.Quotient.mk (modulusIdeal m)
        (hk_dualPoint_frequencyLift m J hJ T y).1)
    · exact hk_dualPoint_weight_coeff_of_unit ψ χ T J hJ y hy0 hu
    · have hweight := hk_dualPoint_weight_zero_of_nonunit_lift
        ψ T J hJ y hy0 hu0 hu
      have hχ : χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T y).1) = 0 := by
        rw [MulChar.inv_apply_eq_inv]
        simpa using χ.character.map_nonunit hu
      rw [hweight, hχ]
      simp

private theorem hk_pointWeight_principal_mul [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (y : Kˣ) {x : K}
    (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    hkPointWeight ψ (toPrincipalIdeal (𝓞 K) K y * I) (y * x) =
      hkPointWeight ψ I x := by
  classical
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K y
  by_cases hx0 : x = 0
  · subst x
    by_cases hm : m.finitePart = 0
    · simp only [hkPointWeight, mul_zero, if_pos rfl, hm]
      exact hk_fractionalCharValue_principal_mul ψ hm I y
    · simp [hkPointWeight, hm]
  · have hyx : (y : K) * x ≠ 0 := mul_ne_zero (Units.ne_zero y) hx0
    let xUnit : Kˣ := Units.mk0 x hx0
    have hgroup :
        toPrincipalIdeal (𝓞 K) K (y * xUnit) * (P * I)⁻¹ =
          toPrincipalIdeal (𝓞 K) K xUnit * I⁻¹ := by
      rw [map_mul]
      dsimp [P]
      rw [mul_inv_rev]
      simp [mul_assoc, mul_comm, mul_left_comm]
    have hInput :
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : K) * x) *
            (((P * I : NumberFieldFractionalIdealGroup K) :
              FractionalIdeal (𝓞 K)⁰ K)⁻¹) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
            ((I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) := by
      have h := congrArg (fun J : NumberFieldFractionalIdealGroup K =>
        (J : FractionalIdeal (𝓞 K)⁰ K)) hgroup
      simpa [P, xUnit, DedekindResidue.val_unit_inv] using h
    have hIntegral := congrArg hkIntegralPart hInput
    simp only [hkPointWeight, if_neg hx0, if_neg hyx]
    rw [hIntegral]

private noncomputable def hkPrincipalMulPoints
    (I : NumberFieldFractionalIdealGroup K) (y : Kˣ) :
    {x : K // x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)} ≃
      {z : K // z ∈ ((toPrincipalIdeal (𝓞 K) K y * I : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (𝓞 K)⁰ K)} where
  toFun x := ⟨(y : K) * x.1, by
    change (y : K) * x.1 ∈
      (toPrincipalIdeal (𝓞 K) K y * I : FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul]
    exact ⟨x.1, x.2, rfl⟩⟩
  invFun z := ⟨(y : K)⁻¹ * z.1, by
    have hz : z.1 ∈
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) := by
      simpa only [Units.val_mul, coe_toPrincipalIdeal] using z.2
    obtain ⟨x, hx, hxz⟩ := (FractionalIdeal.mem_singleton_mul).mp hz
    change (y : K)⁻¹ * z.1 ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [hxz]
    simpa [mul_assoc] using hx⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv z := by
    apply Subtype.ext
    simp [mul_assoc]

private theorem hkWeightedTheta_principal_mul [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (y : Kˣ)
    (c : InfinitePlace K → ℝ) :
    hkWeightedTheta ψ (toPrincipalIdeal (𝓞 K) K y * I) c =
      hkWeightedTheta ψ I (fun w => (w (y : K)) ^ 2 * c w) := by
  classical
  let e := hkPrincipalMulPoints I y
  rw [hkWeightedTheta, hkWeightedTheta]
  conv_lhs => rw [← Equiv.tsum_eq e]
  refine tsum_congr fun x => ?_
  have hval : (e x).1 = (y : K) * x.1 := rfl
  have hweight : hkPointWeight ψ (toPrincipalIdeal (𝓞 K) K y * I) (e x).1 =
      hkPointWeight ψ I x.1 := by
    rw [hval]
    exact hk_pointWeight_principal_mul ψ I y x.2
  have hgauss :
      Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        c w * (w (e x).1) ^ 2) =
      Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        ((w (y : K)) ^ 2 * c w) * (w x.1) ^ 2) := by
    congr 1
    rw [hval]
    simp_rw [map_mul, mul_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    ring
  change hkPointWeight ψ (toPrincipalIdeal (𝓞 K) K y * I) (e x).1 *
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K, c w * (w (e x).1) ^ 2) : ℂ) =
    hkPointWeight ψ I x.1 *
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        ((w (y : K)) ^ 2 * c w) * (w x.1) ^ 2) : ℂ)
  rw [hweight, hgauss]

private theorem hkWeightedTheta_unit_mul [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (u : (𝓞 K)ˣ)
    (c : InfinitePlace K → ℝ) :
    hkWeightedTheta ψ I
        (fun w => (w (algebraMap (𝓞 K) K (u : 𝓞 K))) ^ 2 * c w) =
      hkWeightedTheta ψ I c := by
  let y : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have hprincipal : toPrincipalIdeal (𝓞 K) K y = 1 :=
    rayPrincipalIdeal_of_integralUnit u
  have h := hkWeightedTheta_principal_mul ψ I y c
  rw [hprincipal, one_mul] at h
  exact h.symm

theorem hkWeightedTheta_heckeWeights_periodic [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (t : ℝ)
    (v : logSpace K) (u : (𝓞 K)ˣ) :
    hkWeightedTheta ψ I
        (heckeWeights K t (v + logEmbedding K (Additive.ofMul u))) =
      hkWeightedTheta ψ I (heckeWeights K t v) := by
  rw [heckeWeights_add_logEmbedding]
  exact hkWeightedTheta_unit_mul ψ I u (heckeWeights K t v)

private theorem setIntegral_fundamentalDomain_comp_add_complex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → ℂ)
    (hf : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x, f (↑l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain b, f (u + s) =
      ∫ u in ZSpan.fundamentalDomain b, f u := by
  let T : (ι → ℝ) ≃ₜ (ι → ℝ) := Homeomorph.addRight s
  let e : (ι → ℝ) ≃ (ι → ℝ) := T.toEquiv
  have hmp : MeasurePreserving T volume volume := measurePreserving_add_right volume s
  have hemb : MeasurableEmbedding T := T.measurableEmbedding
  have hmpInv : MeasurePreserving e.symm volume volume := by
    have hfun : (e.symm : (ι → ℝ) → (ι → ℝ)) = (fun x => x + (-s)) := by
      funext x
      simp [e, T, Homeomorph.addRight, sub_eq_add_neg, add_comm]
    rw [hfun]
    exact measurePreserving_add_right volume (-s)
  have hFD := ZSpan.isAddFundamentalDomain b volume
  have hFDshift : IsAddFundamentalDomain (Submodule.span ℤ (Set.range ⇑b))
      (T '' ZSpan.fundamentalDomain b) volume := by
    refine hFD.image_of_equiv e hmpInv.quasiMeasurePreserving
      (Equiv.refl (Submodule.span ℤ (Set.range ⇑b))) ?_
    intro g x
    change ((g : ι → ℝ) + x) + s = (g : ι → ℝ) + (x + s)
    abel
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)) (ι → ℝ) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup (ι → ℝ) volume)
  calc
    ∫ u in ZSpan.fundamentalDomain b, f (u + s) =
        ∫ u in T '' ZSpan.fundamentalDomain b, f u := by
      symm
      exact hmp.setIntegral_image_emb hemb f (ZSpan.fundamentalDomain b)
    _ = ∫ u in ZSpan.fundamentalDomain b, f u := by
      refine hFDshift.setIntegral_eq hFD ?_
      intro l x
      change f ((l : ι → ℝ) + x) = f x
      exact hf l x

theorem setIntegral_fundamentalDomain_comp_neg_add_complex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → ℂ)
    (hf : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x, f (↑l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain b, f (-u + s) =
      ∫ u in ZSpan.fundamentalDomain b, f u := by
  set τ : (ι → ℝ) → (ι → ℝ) := fun u => -u + s with hτ
  have hmp : MeasurePreserving τ volume volume :=
    (measurePreserving_add_right volume s).comp (Measure.measurePreserving_neg volume)
  have hemb : MeasurableEmbedding τ :=
    ((Homeomorph.neg (ι → ℝ)).trans (Homeomorph.addRight s)).measurableEmbedding
  have hFD := ZSpan.isAddFundamentalDomain b volume
  have hD' : IsAddFundamentalDomain (Submodule.span ℤ (Set.range ⇑b))
      (τ ⁻¹' ZSpan.fundamentalDomain b) volume := by
    refine hFD.preimage_of_equiv hmp.quasiMeasurePreserving
      (e := fun l => -l) neg_involutive.bijective (fun g x => ?_)
    show τ ((-g : Submodule.span ℤ (Set.range ⇑b)) +ᵥ x) = g +ᵥ τ x
    rw [Submodule.vadd_def, Submodule.vadd_def, vadd_eq_add, vadd_eq_add, hτ]
    push_cast
    abel
  have hset : ZSpan.fundamentalDomain b =
      τ ⁻¹' (τ ⁻¹' ZSpan.fundamentalDomain b) := by
    ext x
    have hττ : τ (τ x) = x := by
      rw [hτ]
      simp only [neg_add_rev, neg_neg]
      abel
    simp [Set.mem_preimage, hττ]
  conv_lhs => rw [hset]
  rw [hmp.setIntegral_preimage_emb hemb]
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)) (ι → ℝ) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup (ι → ℝ) volume)
  refine hD'.setIntegral_eq hFD (fun g x => ?_)
  rw [Submodule.vadd_def, vadd_eq_add]
  exact hf g x

theorem hkWeightedG_principal_mul [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (y : Kˣ) {t : ℝ} (ht : 0 ≤ t) :
    hkWeightedG ψ (toPrincipalIdeal (𝓞 K) K y * I) t =
      hkWeightedG ψ I (((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 * t) := by
  classical
  unfold hkWeightedG
  congr 1
  have hpt : ∀ v : logSpace K,
      hkWeightedTheta ψ (toPrincipalIdeal (𝓞 K) K y * I) (heckeWeights K t v) =
        hkWeightedTheta ψ I
          (heckeWeights K (((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 * t)
            (v + xShift K (y : K))) := by
    intro v
    rw [hkWeightedTheta_principal_mul]
    congr 1
    funext w
    exact DedekindResidue.sq_mul_heckeWeights K (Units.ne_zero y) ht v w
  simp only [hpt]
  refine setIntegral_fundamentalDomain_comp_add_complex
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
    (xShift K (y : K))
    (fun v => hkWeightedTheta ψ I
      (heckeWeights K (((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 * t) v))
    (fun l v => ?_)
  have hl : (l : logSpace K) ∈ unitLattice K :=
    (le_of_eq ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ)) l.2
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hl
  rw [add_comm, ← ha]
  exact hkWeightedTheta_heckeWeights_periodic ψ I
    (((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 * t) v (Additive.toMul a)

theorem exists_integral_primeTo_principal_mul [IsTotallyComplex K]
    (m : RayClassModulus K) (I : NumberFieldFractionalIdealGroup K) :
    ∃ y : Kˣ, ∃ J : Ideal (𝓞 K), ∃ hJ : IsCoprimeTo m J,
      idealUnit J hJ.1 = toPrincipalIdeal (𝓞 K) K y * I := by
  classical
  let IF : FractionalIdeal (𝓞 K)⁰ K := I
  let M : FractionalIdeal (𝓞 K)⁰ K := modulusIdeal m
  have hIne : IF ≠ 0 := Units.ne_zero I
  by_cases hMtop : modulusIdeal m = ⊤
  · let y : Kˣ := Units.mk0 (algebraMap (𝓞 K) K (IF.den : 𝓞 K))
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
        (nonZeroDivisors.coe_ne_zero IF.den))
    let J : Ideal (𝓞 K) := IF.num
    have hJcoe : (J : FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K y * I : NumberFieldFractionalIdealGroup K) := by
      have h := FractionalIdeal.den_mul_self_eq_num'
        (nonZeroDivisors (𝓞 K)) K IF
      change ((IF.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        ((toPrincipalIdeal (𝓞 K) K y * I : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K)
      rw [Units.val_mul, coe_toPrincipalIdeal]
      rw [show (y : K) = algebraMap (𝓞 K) K (IF.den : 𝓞 K) by rfl]
      exact h.symm
    have hJ : J ≠ ⊥ := by
      intro hbot
      have hzero : (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by simp [hbot]
      rw [hJcoe] at hzero
      exact Units.ne_zero (toPrincipalIdeal (𝓞 K) K y * I) hzero
    have hcop : IsCoprimeTo m J := by
      apply (isCoprimeTo_iff_sup m J).2
      refine ⟨hJ, ?_⟩
      simp [hMtop]
    have hunit : idealUnit J hJ = toPrincipalIdeal (𝓞 K) K y * I := by
      apply Units.ext
      simpa [idealUnit] using hJcoe
    exact ⟨y, J, hcop, hunit⟩
  · let α : K := (1 : FractionalIdeal (𝓞 K)⁰ K).divMod IF M
    have hMnotTop : modulusIdeal m ≠ ⊤ := by
      intro h
      exact hMtop h
    have hMle : M ≤ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      exact FractionalIdeal.coeIdeal_le_one
    have hMne : M ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (modulusIdeal_ne_bot m)
    have hdiv : M + FractionalIdeal.spanSingleton (𝓞 K)⁰ α * IF = 1 := by
      simpa [α, IF, M] using
        (FractionalIdeal.divMod_spec (a := M) (b := IF) (c := (1 : FractionalIdeal (𝓞 K)⁰ K))
          hMle hMne hIne)
    have hα : α ≠ 0 := by
      intro hzero
      have hMone : M = 1 := by simpa [hzero] using hdiv
      have hMtop : modulusIdeal m = ⊤ := by
        apply (FractionalIdeal.coeIdeal_inj' (S := nonZeroDivisors (𝓞 K)) (P := K) le_rfl).mp
        simpa [M, FractionalIdeal.coeIdeal_top] using hMone
      exact hMnotTop hMtop
    let y : Kˣ := Units.mk0 α hα
    let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K y
    have hPI : (P * I : NumberFieldFractionalIdealGroup K) =
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ α * IF : FractionalIdeal (𝓞 K)⁰ K) := by
      simp [P, y, IF, coe_toPrincipalIdeal, Units.val_mul]
    have hPle : (P * I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
      rw [← Units.val_mul, hPI]
      calc
        FractionalIdeal.spanSingleton (𝓞 K)⁰ α * IF ≤
            M + FractionalIdeal.spanSingleton (𝓞 K)⁰ α * IF := le_sup_right
        _ = 1 := hdiv
    obtain ⟨J, hJcoe⟩ := (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hPle
    have hJ : J ≠ ⊥ := by
      intro hbot
      have hzero : (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by simp [hbot]
      rw [hJcoe] at hzero
      exact Units.ne_zero (P * I) hzero
    have hsum :
        (modulusIdeal m : FractionalIdeal (𝓞 K)⁰ K) +
          (J : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      rw [hJcoe, ← Units.val_mul, hPI]
      exact hdiv
    have hJtop : modulusIdeal m ⊔ J = ⊤ := by
      apply (FractionalIdeal.coeIdeal_inj' (S := nonZeroDivisors (𝓞 K)) (P := K) le_rfl).mp
      simpa [FractionalIdeal.coeIdeal_sup, FractionalIdeal.coeIdeal_top] using hsum
    have hcop : IsCoprimeTo m J :=
      (isCoprimeTo_iff_sup m J).2 ⟨hJ, by simpa [sup_comm] using hJtop⟩
    have hunit : idealUnit J hJ = P * I := by
      apply Units.ext
      exact hJcoe
    exact ⟨y, J, hcop, by simpa [P] using hunit⟩

set_option maxHeartbeats 5000000 in
private theorem hk_weighted_gaussian_poisson_integral_covol [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    hkWeightedTheta ψ (idealUnit J hJ.1) c =
      (charValue ψ T.B * hkGaussSum χ T /
        (((ZLattice.covolume
          (idealZLattice K (idealUnit (modulusIdeal m * J)
            (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))) volume : ℝ) : ℂ) *
          (Real.sqrt (∏ i : index K, placeWeights K c i) : ℂ))) *
        hkWeightedTheta (ψ⁻¹) (hkDualIdeal m (idealUnit J hJ.1))
          (fun w => 4 / c w) := by
  classical
  letI : Nonempty (index K) := hk_index_nonempty
  let U : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let MJ : Ideal (𝓞 K) := modulusIdeal m * J
  have hMJ : MJ ≠ ⊥ := mul_ne_zero (modulusIdeal_ne_bot m) hJ.1
  let I' : NumberFieldFractionalIdealGroup K := idealUnit MJ hMJ
  let L := ArtinPrimitiveRoots.Hecke.Theta.dualZLattice (idealZLattice K I')
  let Y := {y : K // y ∈
    (hkDualIdeal m U : FractionalIdeal (𝓞 K)⁰ K)}
  let e : L ≃ Y := hk_dualPointEquiv m J hJ hMJ
  let ci : index K → ℝ := fun i => (placeWeights K c i)⁻¹
  let S : ℝ := (Real.sqrt (∏ i : index K, placeWeights K c i))⁻¹
  let C : ℝ := ZLattice.covolume (idealZLattice K I') volume
  have hcCoord : ∀ i : index K, 0 < placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hc w
  obtain ⟨a, b, ha, hca, hb, hcb⟩ :=
    hk_finite_positive_bounds (placeWeights K c) hcCoord
  have hinvCoord : ∀ i : index K, 0 < ci i := by
    intro i
    exact inv_pos.mpr (hcCoord i)
  obtain ⟨aInv, bInv, haInv, hcaInv, hbInv, hcbInv⟩ :=
    hk_finite_positive_bounds ci hinvCoord
  have hreal : Summable (fun w : L => Real.exp (-Real.pi * ∑ i : index K,
      ci i * ((w : EuclideanSpace ℝ (index K)) i) ^ 2)) :=
    DedekindResidue.summable_real_weightedGaussian L haInv hcaInv
  let gL : L → ℂ := fun w =>
    weightedGaussianCM ci (w : EuclideanSpace ℝ (index K))
  let phaseL : HKResidueRing m → L → ℂ := fun r w =>
    (Real.fourierChar (⟪embeddingCoords K
      (algebraMap (𝓞 K) K (hkIntegralIdealPointLift m J hJ r).1),
      (w : EuclideanSpace ℝ (index K))⟫) : ℂ)
  let phaseY : HKResidueRing m → Y → ℂ := fun r y =>
    (Real.fourierChar (⟪embeddingCoords K
      (algebraMap (𝓞 K) K (hkIntegralIdealPointLift m J hJ r).1),
      (hk_dualPointToVector m J hJ hMJ y :
        EuclideanSpace ℝ (index K))⟫) : ℂ)
  let gY : Y → ℂ := fun y =>
    weightedGaussianCM ci (hk_dualPointToVector m J hJ hMJ y :
      EuclideanSpace ℝ (index K))
  have hphaseY (r : HKResidueRing m) (y : Y) :
      phaseY r y = T.additive
        (r * Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T y).1) := by
    have h := hk_dualPoint_phase m J hJ T y
      (hkIntegralIdealPointLift m J hJ r).1
      (hkIntegralIdealPointLift m J hJ r).2
    rw [hkIntegralIdealPointLift_spec] at h
    exact h
  have hgaussY (y : Y) : gY y =
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        (4 / c w) * (w y.1) ^ 2) : ℂ) := by
    simpa [gY, ci, hk_dualPointToVector] using hkGaussianCM_dual_eq c y.1
  have hphaseL (r : HKResidueRing m) (w : L) :
      phaseL r w = T.additive
        (r * Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T (e w)).1) := by
    have hw : hk_dualPointToVector m J hJ hMJ (e w) = w := e.left_inv w
    have h := hphaseY r (e w)
    simpa [phaseL, phaseY, hw] using h
  have hphaseLEq (r : HKResidueRing m) (w : L) :
      phaseL r w = phaseY r (e w) := by
    exact (hphaseL r w).trans (hphaseY r (e w)).symm
  have hgaussL (w : L) : gL w = gY (e w) := by
    have hw : hk_dualPointToVector m J hJ hMJ (e w) = w := e.left_inv w
    simp [gL, gY, ci, hw]
  have htermSummable (r : HKResidueRing m) :
      Summable (fun w : L => phaseL r w * ((S : ℂ) * gL w)) := by
    apply Summable.of_norm
    have hmajor := hreal.mul_left |S|
    exact hmajor.congr (fun w => by
      simp [phaseL, S, gL, norm_weightedGaussianCM_apply, mul_assoc])
  have htermY_Summable (r : HKResidueRing m) :
      Summable (fun y : Y => phaseY r y * ((S : ℂ) * gY y)) := by
    apply (Equiv.summable_iff e).mp
    apply (htermSummable r).congr
    intro w
    change phaseL r w * ((S : ℂ) * gL w) =
      phaseY r (e w) * ((S : ℂ) * gY (e w))
    rw [hphaseLEq r w, hgaussL w]
  have hgaussPoisson (r : HKResidueRing m) :
      ∑' z : modulusIdeal m * J,
          (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            c w * (w (algebraMap (𝓞 K) K
              ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
        (C⁻¹ : ℂ) * ∑' y : Y, phaseY r y * ((S : ℂ) * gY y) := by
    have hpois := hk_gaussianCoset_poisson m J hJ r c hc ha hca hb hcb
    have hCinv : ((C⁻¹ : ℝ) : ℂ) = (C : ℂ)⁻¹ := by norm_cast
    rw [hpois, Complex.real_smul, hCinv]
    apply congrArg (fun z : ℂ => (C⁻¹ : ℂ) * z)
    calc
      ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
          (idealZLattice K (idealUnit (modulusIdeal m * J)
            (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))),
          Real.fourierChar (⟪embeddingCoords K
            (algebraMap (𝓞 K) K (hkIntegralIdealPointLift m J hJ r).1),
            (w : EuclideanSpace ℝ (index K))⟫) •
            ((Real.sqrt (∏ i : index K, placeWeights K c i))⁻¹ •
              weightedGaussianCM ci (w : EuclideanSpace ℝ (index K))) =
        ∑' w : L, phaseY r (e w) * ((S : ℂ) * gY (e w)) := by
          apply tsum_congr
          intro w
          simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul]
          change phaseL r w * ((S : ℂ) * gL w) =
            phaseY r (e w) * ((S : ℂ) * gY (e w))
          rw [hphaseLEq r w, hgaussL w]
          <;> ring
      _ = ∑' y : Y, phaseY r y * ((S : ℂ) * gY y) :=
        Equiv.tsum_eq e (fun y => phaseY r y * ((S : ℂ) * gY y))
  have hfinite (y : Y) :
      ∑ r : HKResidueRing m,
          χ.character r * phaseY r y * ((S : ℂ) * gY y) =
        (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
          (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
            ((S : ℂ) * gY y) := by
    calc
      ∑ r : HKResidueRing m,
          χ.character r * phaseY r y * ((S : ℂ) * gY y) =
        (∑ r : HKResidueRing m,
          χ.character r * phaseY r y) * ((S : ℂ) * gY y) := by
            rw [← Finset.sum_mul]
      _ = _ := by
        rw [show (∑ r : HKResidueRing m,
            χ.character r * phaseY r y) =
            ∑ r : HKResidueRing m,
              χ.character r * T.additive
                (r * Ideal.Quotient.mk (modulusIdeal m)
                  (hk_dualPoint_frequencyLift m J hJ T y).1) by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hphaseY]]
        rw [hk_finite_gauss_shift χ T
          (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1)]
  have hsumPoisson :
      ∑ r : HKResidueRing m, χ.character r *
          ∑' z : modulusIdeal m * J,
            (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
              c w * (w (algebraMap (𝓞 K) K
                ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
        (C⁻¹ : ℂ) * ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((S : ℂ) * gY y) := by
    calc
      ∑ r : HKResidueRing m, χ.character r *
          ∑' z : modulusIdeal m * J,
            (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
              c w * (w (algebraMap (𝓞 K) K
                ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) =
        ∑ r : HKResidueRing m, χ.character r *
          ((C⁻¹ : ℂ) * ∑' y : Y, phaseY r y * ((S : ℂ) * gY y)) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hgaussPoisson]
      _ = (C⁻¹ : ℂ) * ∑ r : HKResidueRing m,
          χ.character r * ∑' y : Y, phaseY r y * ((S : ℂ) * gY y) := by
            calc
              ∑ r : HKResidueRing m, χ.character r *
                  ((C⁻¹ : ℂ) * ∑' y : Y, phaseY r y * ((S : ℂ) * gY y)) =
                ∑ r : HKResidueRing m, (C⁻¹ : ℂ) *
                  (χ.character r * ∑' y : Y, phaseY r y * ((S : ℂ) * gY y)) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    calc
                      χ.character r * ((C⁻¹ : ℂ) *
                          ∑' y : Y, phaseY r y * ((S : ℂ) * gY y)) =
                        (χ.character r * (C⁻¹ : ℂ)) *
                          ∑' y : Y, phaseY r y * ((S : ℂ) * gY y) := by
                            exact (mul_assoc _ _ _).symm
                      _ = ((C⁻¹ : ℂ) * χ.character r) *
                            ∑' y : Y, phaseY r y * ((S : ℂ) * gY y) := by
                              exact congrArg (fun z : ℂ => z *
                                (∑' y : Y, phaseY r y * ((S : ℂ) * gY y)))
                                (mul_comm (χ.character r) (C⁻¹ : ℂ))
                      _ = (C⁻¹ : ℂ) *
                            (χ.character r * ∑' y : Y,
                              phaseY r y * ((S : ℂ) * gY y)) := by
                                exact mul_assoc _ _ _
              _ = _ := by rw [← Finset.mul_sum]
      _ = (C⁻¹ : ℂ) * ∑ r : HKResidueRing m, ∑' y : Y,
          χ.character r * phaseY r y * ((S : ℂ) * gY y) := by
            congr 1
            apply Finset.sum_congr rfl
            intro r hr
            calc
              χ.character r * ∑' y : Y,
                  phaseY r y * ((S : ℂ) * gY y) =
                ∑' y : Y, χ.character r *
                  (phaseY r y * ((S : ℂ) * gY y)) := by rw [← tsum_mul_left]
              _ = ∑' y : Y,
                  χ.character r * phaseY r y * ((S : ℂ) * gY y) := by
                    apply tsum_congr
                    intro y
                    ring
      _ = (C⁻¹ : ℂ) * ∑' y : Y,
          ∑ r : HKResidueRing m,
            χ.character r * phaseY r y * ((S : ℂ) * gY y) := by
            congr 1
            change Finset.univ.sum (fun r : HKResidueRing m =>
                ∑' y : Y, χ.character r * phaseY r y * ((S : ℂ) * gY y)) =
              ∑' y : Y, Finset.univ.sum (fun r : HKResidueRing m =>
                χ.character r * phaseY r y * ((S : ℂ) * gY y))
            simpa using (Summable.tsum_finsetSum (s := Finset.univ)
              (fun r hr => by
                simpa [mul_assoc] using
                  (htermY_Summable r).mul_left (χ.character r))).symm
      _ = (C⁻¹ : ℂ) * ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((S : ℂ) * gY y) := by
            congr 1
            apply tsum_congr
            exact hfinite
  have hweighted :
      (charValue ψ J)⁻¹ * ∑' y : Y,
          χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y =
        charValue ψ T.B * ∑' y : Y,
          hkPointWeight (ψ⁻¹) (hkDualIdeal m U) y.1 * gY y := by
    calc
      (charValue ψ J)⁻¹ * ∑' y : Y,
          χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y =
        ∑' y : Y,
          ((charValue ψ J)⁻¹ *
            χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
              (hk_dualPoint_frequencyLift m J hJ T y).1)) * gY y := by
                rw [← tsum_mul_left]
                apply tsum_congr
                intro y
                ring
      _ = ∑' y : Y,
          (charValue ψ T.B * hkPointWeight (ψ⁻¹) (hkDualIdeal m U) y.1) *
            gY y := by
              apply tsum_congr
              intro y
              rw [← hk_dualPoint_weight_coeff ψ χ T J hJ y]
      _ = charValue ψ T.B * ∑' y : Y,
          hkPointWeight (ψ⁻¹) (hkDualIdeal m U) y.1 * gY y := by
            simp_rw [mul_assoc]
            rw [tsum_mul_left]
  have hdualTheta : ∑' y : Y,
      hkPointWeight (ψ⁻¹) (hkDualIdeal m U) y.1 * gY y =
        hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c w) := by
    unfold hkWeightedTheta
    apply tsum_congr
    intro y
    rw [hgaussY]
  let V : ℝ := Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w)
  have hprod : (∏ i : index K, placeWeights K c i) =
      ∏ w : InfinitePlace K, c w ^ mult w :=
    DedekindResidue.prod_placeWeights K c
  have hS : (S : ℂ) = (V : ℂ)⁻¹ := by
    dsimp [S, V]
    rw [hprod]
    norm_cast
  have hCpos : 0 < C := by
    dsimp [C, I']
    exact ZLattice.covolume_pos
      (idealZLattice K (idealUnit MJ hMJ))
      (volume : Measure (EuclideanSpace ℝ (index K)))
  have hVpos : 0 < V := by
    apply Real.sqrt_pos.2
    rw [← hprod]
    exact Finset.prod_pos (fun i hi => hcCoord i)
  have hpull :
      ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((V : ℂ)⁻¹ * gY y) =
        (hkGaussSum χ T * (V : ℂ)⁻¹) *
          ∑' y : Y,
            χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
              (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y := by
    calc
      ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((V : ℂ)⁻¹ * gY y) =
        ∑' y : Y,
          (hkGaussSum χ T * (V : ℂ)⁻¹) *
            (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
              (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y) := by
                apply tsum_congr
                intro y
                ring
      _ = (hkGaussSum χ T * (V : ℂ)⁻¹) *
          ∑' y : Y,
            χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
              (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y :=
            tsum_mul_left
  have hscale :
      (charValue ψ J)⁻¹ * ((C⁻¹ : ℂ) * ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((S : ℂ) * gY y)) =
        (charValue ψ T.B * hkGaussSum χ T /
          ((C : ℂ) * (V : ℂ))) *
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c w) := by
    rw [hS, hpull]
    calc
      (charValue ψ J)⁻¹ * ((C⁻¹ : ℂ) *
          ((hkGaussSum χ T * (V : ℂ)⁻¹) *
            ∑' y : Y,
              χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
                (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y)) =
        ((C⁻¹ : ℂ) * hkGaussSum χ T * (V : ℂ)⁻¹) *
          ((charValue ψ J)⁻¹ * ∑' y : Y,
            χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
              (hk_dualPoint_frequencyLift m J hJ T y).1) * gY y) := by ring
      _ = ((C⁻¹ : ℂ) * hkGaussSum χ T * (V : ℂ)⁻¹) *
          (charValue ψ T.B * ∑' y : Y,
            hkPointWeight (ψ⁻¹) (hkDualIdeal m U) y.1 * gY y) := by
              rw [hweighted]
      _ = (charValue ψ T.B * hkGaussSum χ T /
          ((C : ℂ) * (V : ℂ))) *
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c w) := by
              rw [hdualTheta]
              have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
              have hVne : (V : ℂ) ≠ 0 := by exact_mod_cast hVpos.ne'
              field_simp [hCne, hVne]
              <;> ring
  calc
    hkWeightedTheta ψ U c = (charValue ψ J)⁻¹ *
        ∑ r : HKResidueRing m, χ.character r *
          ∑' z : modulusIdeal m * J,
            (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
              c w * (w (algebraMap (𝓞 K) K
                ((hkIntegralIdealPointLift m J hJ r).1 + z.1))) ^ 2) : ℂ) :=
      hk_weightedTheta_residueCosets ψ χ J hJ c hc ha hca
    _ = (charValue ψ J)⁻¹ * ((C⁻¹ : ℂ) * ∑' y : Y,
          (χ.character⁻¹ (Ideal.Quotient.mk (modulusIdeal m)
            (hk_dualPoint_frequencyLift m J hJ T y).1) * hkGaussSum χ T) *
              ((S : ℂ) * gY y)) := by rw [hsumPoisson]
    _ = _ := by simpa [C, V, I', MJ, hprod] using hscale

private theorem hk_prod_placeWeights_principal_rescale [IsTotallyComplex K]
    (c : InfinitePlace K → ℝ) (y : Kˣ) :
    ∏ w : InfinitePlace K,
        ((w (y⁻¹ : K)) ^ 2 * c w) ^ mult w =
      (|Algebra.norm ℚ (y : K)|⁻¹) ^ 2 *
        ∏ w : InfinitePlace K, c w ^ mult w := by
  classical
  have hnormInv : Algebra.norm ℚ (y⁻¹ : K) = (Algebra.norm ℚ (y : K))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    simp
  have hprodInv :
      ∏ w : InfinitePlace K, w (y⁻¹ : K) ^ mult w =
        |Algebra.norm ℚ (y : K)|⁻¹ := by
    rw [InfinitePlace.prod_eq_abs_norm, hnormInv, abs_inv]
  have hterm (w : InfinitePlace K) :
      ((w (y⁻¹ : K)) ^ 2 * c w) ^ mult w =
        ((w (y⁻¹ : K)) ^ mult w) ^ 2 * c w ^ mult w := by
    calc
      ((w (y⁻¹ : K)) ^ 2 * c w) ^ mult w =
          ((w (y⁻¹ : K)) ^ 2) ^ mult w * c w ^ mult w := by rw [mul_pow]
      _ = ((w (y⁻¹ : K)) ^ mult w) ^ 2 * c w ^ mult w := by
        congr 1
        calc
          ((w (y⁻¹ : K)) ^ 2) ^ mult w =
              (w (y⁻¹ : K)) ^ (2 * mult w) := by rw [pow_mul]
          _ = (w (y⁻¹ : K)) ^ (mult w * 2) := by rw [Nat.mul_comm]
          _ = ((w (y⁻¹ : K)) ^ mult w) ^ 2 := by rw [pow_mul]
  calc
    ∏ w : InfinitePlace K, ((w (y⁻¹ : K)) ^ 2 * c w) ^ mult w =
        ∏ w : InfinitePlace K,
          ((w (y⁻¹ : K)) ^ mult w) ^ 2 * c w ^ mult w := by
            apply Finset.prod_congr rfl
            intro w hw
            exact hterm w
    _ = (∏ w : InfinitePlace K, w (y⁻¹ : K) ^ mult w) ^ 2 *
          ∏ w : InfinitePlace K, c w ^ mult w := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow]
    _ = (|Algebra.norm ℚ (y : K)|⁻¹) ^ 2 *
          ∏ w : InfinitePlace K, c w ^ mult w := by rw [hprodInv]

private theorem hk_sqrt_prod_placeWeights_principal_rescale [IsTotallyComplex K]
    (c : InfinitePlace K → ℝ) (y : Kˣ) :
    Real.sqrt (∏ w : InfinitePlace K,
        ((w (y⁻¹ : K)) ^ 2 * c w) ^ mult w) =
      |Algebra.norm ℚ (y : K)|⁻¹ *
        Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) := by
  rw [hk_prod_placeWeights_principal_rescale]
  rw [Real.sqrt_mul (sq_nonneg _)]
  have hNinvNonneg :
      0 ≤ ((|Algebra.norm ℚ (y : K)|⁻¹ : ℚ) : ℝ) := by positivity
  rw [Real.sqrt_sq hNinvNonneg]

private theorem hk_idealNormR_idealUnit_integral (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) :
    idealNormR K (idealUnit A hA) = ((Ideal.absNorm A : ℕ) : ℝ) := by
  simp [DedekindResidue.idealNormR, idealUnit, FractionalIdeal.coeIdeal_absNorm]

theorem hk_weighted_gaussian_poisson_all [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (I : NumberFieldFractionalIdealGroup K)
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    hkWeightedTheta ψ I c =
      (charValue ψ T.B * hkGaussSum χ T /
        ((modulusNorm m : ℂ) *
          ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
            Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) *
          (Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) : ℂ))) *
        hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (fun w => 4 / c w) := by
  classical
  obtain ⟨y, J, hJ, hJunit⟩ := exists_integral_primeTo_principal_mul m I
  let U : NumberFieldFractionalIdealGroup K := idealUnit J hJ.1
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K y
  let yInv : Kˣ := y⁻¹
  let PInv : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K yInv
  have hU : U = P * I := by simpa [U, P] using hJunit
  have hPInv : PInv = P⁻¹ := by
    simp [PInv, P, yInv]
  have hIrep : PInv * U = I := by
    calc
      PInv * U = P⁻¹ * U := by rw [hPInv]
      _ = P⁻¹ * (P * I) := by rw [hU]
      _ = I := by group
  let c' : InfinitePlace K → ℝ := fun w =>
    (w (yInv : K)) ^ 2 * c w
  have hyInvPos (w : InfinitePlace K) : 0 < w (yInv : K) :=
    InfinitePlace.pos_iff.mpr (Units.ne_zero yInv)
  have hc' : ∀ w, 0 < c' w := by
    intro w
    exact mul_pos (sq_pos_of_pos (hyInvPos w)) (hc w)
  have hPrimal := hkWeightedTheta_principal_mul ψ U yInv c
  rw [hIrep] at hPrimal
  let N : ℝ := ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ)
  have hNpos : 0 < N := by
    dsimp [N]
    rw [← InfinitePlace.prod_eq_abs_norm]
    exact Finset.prod_pos (fun w hw =>
      pow_pos (InfinitePlace.pos_iff.mpr (Units.ne_zero y)) _)
  have hJnorm : idealNormR K U = N * idealNormR K I := by
    rw [hU]
    simpa [P, N] using DedekindResidue.idealNormR_principal_mul K I y
  let MJ : Ideal (𝓞 K) := modulusIdeal m * J
  have hMJ : MJ ≠ ⊥ := mul_ne_zero (modulusIdeal_ne_bot m) hJ.1
  let U' : NumberFieldFractionalIdealGroup K := idealUnit MJ hMJ
  let C' : ℝ := ZLattice.covolume (idealZLattice K U') volume
  have hNormMJ : idealNormR K U' =
      (modulusNorm m : ℝ) * idealNormR K U := by
    rw [hk_idealNormR_idealUnit_integral MJ hMJ,
      hk_idealNormR_idealUnit_integral J hJ.1]
    change (Ideal.absNorm (modulusIdeal m * J) : ℝ) = _
    rw [map_mul, modulusIdeal_absNorm]
    norm_cast
  have hdiscr : Real.sqrt |discr K| =
      Real.sqrt ((discr K).natAbs : ℝ) := by
    apply congrArg Real.sqrt
    exact (Int.cast_abs).symm.trans
      (Nat.cast_natAbs (α := ℝ) (discr K)).symm
  have hCvol : C' = (modulusNorm m : ℝ) *
      (idealNormR K U * (1 / 2 : ℝ) ^ nrComplexPlaces K *
        Real.sqrt ((discr K).natAbs : ℝ)) := by
    dsimp [C']
    rw [DedekindResidue.covolume_idealZLattice]
    change idealNormR K U' * (2⁻¹) ^ nrComplexPlaces K *
        Real.sqrt |discr K| = _
    rw [hNormMJ, hdiscr]
    rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
    ring
  have hRoot : Real.sqrt (∏ w : InfinitePlace K, c' w ^ mult w) =
      N⁻¹ * Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) := by
    simpa [c', yInv, N] using hk_sqrt_prod_placeWeights_principal_rescale c y
  have hDen : C' * Real.sqrt (∏ w : InfinitePlace K, c' w ^ mult w) =
      (modulusNorm m : ℝ) *
        (idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
          Real.sqrt ((discr K).natAbs : ℝ)) *
        Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) := by
    calc
      C' * Real.sqrt (∏ w : InfinitePlace K, c' w ^ mult w) =
          ((modulusNorm m : ℝ) *
            (idealNormR K U * (1 / 2 : ℝ) ^ nrComplexPlaces K *
              Real.sqrt ((discr K).natAbs : ℝ))) *
            (N⁻¹ * Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w)) := by
              rw [hCvol, hRoot]
      _ = (modulusNorm m : ℝ) *
            (idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
              Real.sqrt ((discr K).natAbs : ℝ)) *
            Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) := by
              rw [hJnorm]
              field_simp [hNpos.ne']
              <;> ring
  have hInt := hk_weighted_gaussian_poisson_integral_covol ψ χ T J hJ c' hc'
  have hInt' : hkWeightedTheta ψ U c' =
      (charValue ψ T.B * hkGaussSum χ T /
        (((ZLattice.covolume
          (idealZLattice K (idealUnit (modulusIdeal m * J)
            (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))) volume : ℝ) : ℂ) *
          (Real.sqrt (∏ w : InfinitePlace K, c' w ^ mult w) : ℂ))) *
        hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c' w) := by
    simpa only [DedekindResidue.prod_placeWeights] using hInt
  have hDenC :
      ((ZLattice.covolume
          (idealZLattice K (idealUnit (modulusIdeal m * J)
            (mul_ne_zero (modulusIdeal_ne_bot m) hJ.1))) volume : ℝ) : ℂ) *
        (Real.sqrt (∏ w : InfinitePlace K, c' w ^ mult w) : ℂ) =
      (modulusNorm m : ℂ) *
        ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
          Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) *
        (Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) : ℂ) := by
    exact_mod_cast hDen
  rw [hDenC] at hInt'
  have hPInvDual : hkDualIdeal m I = P * hkDualIdeal m U := by
    simp only [hkDualIdeal]
    rw [← hIrep, hPInv]
    simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have hyInvMap (w : InfinitePlace K) :
      w (yInv : K) = (w (y : K))⁻¹ := by simp [yInv]
  have hyPos (w : InfinitePlace K) : 0 < w (y : K) :=
    InfinitePlace.pos_iff.mpr (Units.ne_zero y)
  have hcDualPoint (w : InfinitePlace K) :
      4 / c' w = (w (y : K)) ^ 2 * (4 / c w) := by
    dsimp [c']
    rw [hyInvMap]
    field_simp [ne_of_gt (hc w), ne_of_gt (hyPos w)]
    <;> ring
  have hcDual : (fun w => 4 / c' w) =
      (fun w => (w (y : K)) ^ 2 * (4 / c w)) := by
    funext w
    exact hcDualPoint w
  have hdualRescale :
      hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c' w) =
        hkWeightedTheta (ψ⁻¹) (P * hkDualIdeal m U) (fun w => 4 / c w) := by
    have h := hkWeightedTheta_principal_mul (ψ⁻¹)
      (hkDualIdeal m U) y (fun w => 4 / c w)
    rw [← hcDual] at h
    exact h.symm
  calc
    hkWeightedTheta ψ I c = hkWeightedTheta ψ U c' := hPrimal
    _ = (charValue ψ T.B * hkGaussSum χ T /
          ((modulusNorm m : ℂ) *
            ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
              Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) *
            (Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) : ℂ))) *
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m U) (fun w => 4 / c' w) := hInt'
    _ = _ := by rw [hdualRescale, ← hPInvDual]

end ArtinPrimitiveRoots.Hecke

end
