import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_point_ideal_integral
import ArtinPrimitiveRoots.Hecke.Theta.RayMellinCone
import DedekindResidue.CompletedZeta.MellinAgreement

set_option autoImplicit false

open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open Classical
open scoped NumberField nonZeroDivisors Real

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

private theorem hkfe_rayClass_eq_implies_class_eq {m : RayClassModulus K}
    (P Q : Ideal (𝓞 K)) (hP : IsCoprimeTo m P) (hQ : IsCoprimeTo m Q)
    (h : rayClass m P hP = rayClass m Q hQ) :
    ClassGroup.mk K (idealUnit P hP.1) = ClassGroup.mk K (idealUnit Q hQ.1) := by
  let p : rayClassPrimeToIdeals m := ⟨idealUnit P hP.1, hP.2⟩
  let q : rayClassPrimeToIdeals m := ⟨idealUnit Q hQ.1, hQ.2⟩
  have hquot :
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) p =
        QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) q := by
    simpa [rayClass, p, q] using h
  have hmem : p / q ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (QuotientGroup.eq_iff_div_mem).mp hquot
  obtain ⟨a, -, ha⟩ := (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m (p / q)).mp hmem
  have hprincipal : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨(a : K), rfl⟩⟩
  have hclass :
      ClassGroup.mk K (p : NumberFieldFractionalIdealGroup K) /
        ClassGroup.mk K (q : NumberFieldFractionalIdealGroup K) = 1 := by
    calc
      ClassGroup.mk K (p : NumberFieldFractionalIdealGroup K) /
          ClassGroup.mk K (q : NumberFieldFractionalIdealGroup K) =
        ClassGroup.mk K ((p / q : rayClassPrimeToIdeals m) : NumberFieldFractionalIdealGroup K) := by
        calc
          _ = ClassGroup.mk K
              ((p : NumberFieldFractionalIdealGroup K) /
                (q : NumberFieldFractionalIdealGroup K)) :=
            (map_div (ClassGroup.mk K)
            (p : NumberFieldFractionalIdealGroup K)
            (q : NumberFieldFractionalIdealGroup K)).symm
          _ = _ := rfl
      _ = ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) := by rw [← ha]
      _ = 1 := hprincipal
  have hp : ClassGroup.mk K (p : NumberFieldFractionalIdealGroup K) =
      ClassGroup.mk K (idealUnit P hP.1) := rfl
  have hq : ClassGroup.mk K (q : NumberFieldFractionalIdealGroup K) =
      ClassGroup.mk K (idealUnit Q hQ.1) := rfl
  rw [← hp, ← hq]
  exact (div_eq_one.mp hclass)

private theorem hkFE_idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem hkFE_coprime_mul {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) : IsCoprimeTo m (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  rw [hkFE_idealUnit_mul I J hI.1 hJ.1]
  exact (rayClassPrimeToIdeals m).mul_mem hI.2 hJ.2

private theorem hkFE_rayClass_mul {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m (I * J) (hkFE_coprime_mul hI hJ) =
      rayClass m I hI * rayClass m J hJ := by
  change QuotientGroup.mk (⟨idealUnit (I * J) _, _⟩ : rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨idealUnit I _, _⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨idealUnit J _, _⟩ : rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hkFE_idealUnit_mul I J hI.1 hJ.1 (mul_ne_zero hI.1 hJ.1))

private theorem hkFE_rayClass_congr {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) (h : I = J) :
    rayClass m I hI = rayClass m J hJ := by
  subst J
  unfold rayClass
  congr 1

private theorem hkFE_idealUnit_span (x : 𝓞 K) (hx : x ≠ 0) :
    idealUnit (Ideal.span {x}) (mt Ideal.span_singleton_eq_bot.mp hx) =
      toPrincipalIdeal (𝓞 K) K (Units.mk0 (algebraMap (𝓞 K) K x)
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hx)) := by
  apply Units.ext
  change (Ideal.span {x} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

private noncomputable def hkFEIdealRayClassTerm {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (C : RayClassGroup m) (P : Ideal (𝓞 K)) : ℂ :=
  if h : IsCoprimeTo m P then
    if rayClass m P h = C then charValue ψ P else 0
  else 0

local instance hkFERayClassGroupFintype [IsTotallyComplex K]
    (m : RayClassModulus K) : Fintype (RayClassGroup m) := by
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  exact Fintype.ofFinite _

private theorem hkfe_charValue_eq_rayClass_sum [IsTotallyComplex K]
    {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (P : Ideal (𝓞 K)) :
    charValue ψ P = ∑ C : RayClassGroup m, hkFEIdealRayClassTerm ψ C P := by
  classical
  by_cases h : IsCoprimeTo m P
  · have hcv : charValue ψ P = (ψ (rayClass m P h) : ℂ) := by
      simp [charValue, h]
    rw [hcv]
    simp only [hkFEIdealRayClassTerm, dif_pos h, hcv]
    rw [Finset.sum_ite_eq Finset.univ (rayClass m P h)
      (fun _ => (ψ (rayClass m P h) : ℂ))]
    simp
  · simp [hkFEIdealRayClassTerm, h, charValue]

private theorem hkFE_charValue_norm_le_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (P : Ideal (𝓞 K)) :
    ‖charValue ψ P‖ ≤ ∑ C : RayClassGroup m, ‖(ψ C : ℂ)‖ := by
  classical
  by_cases hP : IsCoprimeTo m P
  · rw [charValue, dif_pos hP]
    exact Finset.single_le_sum
      (fun D hD => norm_nonneg (ψ D : ℂ)) (Finset.mem_univ (rayClass m P hP))
  · simp [charValue, hP]
    positivity

private theorem hkFE_rayClassTerm_norm_le_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (P : Ideal (𝓞 K)) :
    ‖hkFEIdealRayClassTerm ψ C P‖ ≤ ∑ D : RayClassGroup m, ‖(ψ D : ℂ)‖ := by
  classical
  by_cases hP : IsCoprimeTo m P
  · by_cases hC : rayClass m P hP = C
    · simp [hkFEIdealRayClassTerm, hP, hC]
      exact hkFE_charValue_norm_le_sum ψ P
    · simp [hkFEIdealRayClassTerm, hP, hC]
      positivity
  · simp [hkFEIdealRayClassTerm, hP]
    positivity

noncomputable def hkFEIdealRayClassPointWeight {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (C : RayClassGroup m)
    (A : FractionalIdeal (𝓞 K)⁰ K) : ℂ :=
  hkFEIdealRayClassTerm ψ C (hkIntegralPart A)

private theorem hkFEIdealRayClassPointWeight_eq_rayKernel [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hclass : rayClass m J hJ = C⁻¹) (x : J) (hx : x.1 ≠ 0) :
    hkFEIdealRayClassPointWeight ψ C
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x.1) *
        ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) =
      if rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1 then (ψ C : ℂ) else 0 := by
  classical
  let P : Ideal (𝓞 K) := Ideal.span {x.1}
  let A : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x.1) *
      ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K)
  have hxmem : (algebraMap (𝓞 K) K x.1) ∈
      (idealUnit J hJ.1 : FractionalIdeal (𝓞 K)⁰ K) := by
    change (algebraMap (𝓞 K) K x.1) ∈
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) x.2
  have hbridge := hk_point_ideal_integral (idealUnit J hJ.1) hxmem
  have hprodCo :
      ((hkIntegralPart A * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        (P : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_mul, hbridge]
    change A * (J : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.span {x.1} : FractionalIdeal (𝓞 K)⁰ K)
    have hJI :
        ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) *
          (J : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      have hJval : (J : FractionalIdeal (𝓞 K)⁰ K) =
          (idealUnit J hJ.1 : FractionalIdeal (𝓞 K)⁰ K) := rfl
      rw [hJval]
      exact congrArg (fun U : NumberFieldFractionalIdealGroup K =>
        (U : FractionalIdeal (𝓞 K)⁰ K)) (inv_mul_cancel (idealUnit J hJ.1))
    change (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x.1) *
      ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
        (J : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [mul_assoc, hJI, mul_one, FractionalIdeal.coeIdeal_span_singleton]
  have hprod : hkIntegralPart A * J = P :=
    FractionalIdeal.coeIdeal_injective hprodCo
  by_cases hker : rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1
  · obtain ⟨hP, hPclass⟩ :=
      (rayKernelWeight_eq_one_iff_rayClass_span m x.1 hx).mp hker
    have hdiv : J ∣ P := by
      exact Ideal.dvd_span_singleton.mpr x.2
    let J₀ : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ.1⟩
    let P₀ : (Ideal (𝓞 K))⁰ := ⟨P, mem_nonZeroDivisors_of_ne_zero hP.1⟩
    let e := rayPrincipalDvdEquiv m J₀ hJ
    let p : {Q : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (Q : Ideal (𝓞 K)) ∧
        ∃ hQ : IsCoprimeTo m (Q : Ideal (𝓞 K)), rayClass m (Q : Ideal (𝓞 K)) hQ = 1} :=
      ⟨P₀, hdiv, hP, hPclass⟩
    let b := e.symm p
    have hb : (∃ hb : IsCoprimeTo m (b.1 : Ideal (𝓞 K)),
        rayClass m (b.1 : Ideal (𝓞 K)) hb = (rayClass m J hJ)⁻¹) := b.2
    have hmul : (b.1 : Ideal (𝓞 K)) * J = P := by
      have hh := congrArg (fun q => (q.1 : Ideal (𝓞 K))) (e.apply_symm_apply p)
      change (b.1 : Ideal (𝓞 K)) * J = P at hh
      exact hh
    obtain ⟨hbCop, hbClass⟩ := hb
    have hbClassC : rayClass m (b.1 : Ideal (𝓞 K)) hbCop = C := by
      calc
        rayClass m (b.1 : Ideal (𝓞 K)) hbCop = (rayClass m J hJ)⁻¹ := hbClass
        _ = (C⁻¹)⁻¹ := by rw [hclass]
        _ = C := inv_inv C
    have hmulU : idealUnit (b.1 : Ideal (𝓞 K)) hbCop.1 * idealUnit J hJ.1 =
        idealUnit P hP.1 := by
      calc
        _ = idealUnit ((b.1 : Ideal (𝓞 K)) * J) (mul_ne_zero hbCop.1 hJ.1) :=
          (hkFE_idealUnit_mul (b.1 : Ideal (𝓞 K)) J hbCop.1 hJ.1
            (mul_ne_zero hbCop.1 hJ.1)).symm
        _ = idealUnit P hP.1 := by
          apply Units.ext
          exact congrArg (fun Q : Ideal (𝓞 K) =>
            (Q : FractionalIdeal (𝓞 K)⁰ K)) hmul
    let a : Kˣ := Units.mk0 (algebraMap (𝓞 K) K x.1)
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hx)
    have hspan := hkFE_idealUnit_span x.1 hx
    have hbUnit : idealUnit (b.1 : Ideal (𝓞 K)) hbCop.1 =
        toPrincipalIdeal (𝓞 K) K a * (idealUnit J hJ.1)⁻¹ := by
      calc
        _ = (idealUnit (b.1 : Ideal (𝓞 K)) hbCop.1 * idealUnit J hJ.1) *
            (idealUnit J hJ.1)⁻¹ := by group
        _ = _ := by rw [hmulU, ← hspan]
    have hbcoe : (b.1 : FractionalIdeal (𝓞 K)⁰ K) = A := by
      have h := congrArg (fun U : NumberFieldFractionalIdealGroup K =>
        (U : FractionalIdeal (𝓞 K)⁰ K)) hbUnit
      change (b.1 : FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
          ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) at h
      have hspanVal : (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x.1) := by
        have hh := congrArg (fun U : NumberFieldFractionalIdealGroup K =>
          (U : FractionalIdeal (𝓞 K)⁰ K)) hspan
        change (Ideal.span {x.1} : FractionalIdeal (𝓞 K)⁰ K) = _ at hh
        rw [FractionalIdeal.coeIdeal_span_singleton] at hh
        simpa [a] using hh.symm
      calc
        (b.1 : FractionalIdeal (𝓞 K)⁰ K) =
            (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
              ((idealUnit J hJ.1)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := h
        _ = A := by rw [hspanVal]
    have hcontract : hkIntegralPart A = (b.1 : Ideal (𝓞 K)) := by
      apply (FractionalIdeal.coeIdeal_injective (R := 𝓞 K) (K := K))
      have hcoeA : (hkIntegralPart A : FractionalIdeal (𝓞 K)⁰ K) = A := by
        simpa [A] using hbridge
      change (hkIntegralPart A : FractionalIdeal (𝓞 K)⁰ K) = _
      exact hcoeA.trans hbcoe.symm
    have hA : IsCoprimeTo m (hkIntegralPart A) := by simpa [hcontract] using hbCop
    have hAclass : rayClass m (hkIntegralPart A) hA = C := by
      simpa [hcontract] using hbClassC
    simp [hkFEIdealRayClassPointWeight, hkFEIdealRayClassTerm, A, hA, hAclass,
      charValue, hker]
  · have hterm : hkFEIdealRayClassPointWeight ψ C A = 0 := by
      by_cases hA : IsCoprimeTo m (hkIntegralPart A)
      · by_cases hAC : rayClass m (hkIntegralPart A) hA = C
        · have hPcop : IsCoprimeTo m P := by
            rw [← hprod]
            exact hkFE_coprime_mul hA hJ
          have hPclass : rayClass m P hPcop = 1 := by
            have hprodClass :
                rayClass m (hkIntegralPart A * J) (hkFE_coprime_mul hA hJ) = 1 := by
              rw [hkFE_rayClass_mul hA hJ, hAC, hclass]
              simp
            have htransport := hkFE_rayClass_congr hPcop
              (hkFE_coprime_mul hA hJ) hprod.symm
            exact htransport.trans hprodClass
          have hker' := (rayKernelWeight_eq_one_iff_rayClass_span m x.1 hx).mpr
            ⟨hPcop, hPclass⟩
          exact (hker hker').elim
        · simp [hkFEIdealRayClassPointWeight, hkFEIdealRayClassTerm, A, hA, hAC]
      · simp [hkFEIdealRayClassPointWeight, hkFEIdealRayClassTerm, A, hA]
    simpa [A, hker] using hterm

private theorem hkPointWeight_eq_rayClass_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) {x : K} (hx : x ≠ 0) :
    hkPointWeight ψ I x = ∑ C : RayClassGroup m,
      hkFEIdealRayClassPointWeight ψ C
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) := by
  simp only [hkPointWeight, if_neg hx]
  change charValue ψ (hkIntegralPart
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
      (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K))) =
    ∑ C : RayClassGroup m, hkFEIdealRayClassTerm ψ C (hkIntegralPart
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)))
  exact hkfe_charValue_eq_rayClass_sum ψ _

private abbrev hkPointSubtype (I : NumberFieldFractionalIdealGroup K) :=
  {x : K // x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}

private noncomputable def hkFEPointOPreimage (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (x : hkPointSubtype (idealUnit J hJ)) : J := by
  have hxcoe : x.1 ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    change x.1 ∈ (idealUnit J hJ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    exact x.2
  let hmem := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hxcoe
  exact ⟨Classical.choose hmem, (Classical.choose_spec hmem).1⟩

private theorem hkFEPointOPreimage_spec (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (x : hkPointSubtype (idealUnit J hJ)) :
    algebraMap (𝓞 K) K (hkFEPointOPreimage J hJ x).1 = x.1 := by
  have hxcoe : x.1 ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    change x.1 ∈ (idealUnit J hJ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    exact x.2
  let hmem := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hxcoe
  exact (Classical.choose_spec hmem).2

private noncomputable def hkFEIntegralPointEquiv (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    hkPointSubtype (idealUnit J hJ) ≃ J where
  toFun := hkFEPointOPreimage J hJ
  invFun x := ⟨algebraMap (𝓞 K) K x.1, FractionalIdeal.mem_coeIdeal_of_mem
    (nonZeroDivisors (𝓞 K)) x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact hkFEPointOPreimage_spec J hJ x
  right_inv x := by
    apply Subtype.ext
    apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    exact hkFEPointOPreimage_spec J hJ
      ⟨algebraMap (𝓞 K) K x.1, FractionalIdeal.mem_coeIdeal_of_mem
        (nonZeroDivisors (𝓞 K)) x.2⟩

private theorem hkFE_embeddingCoords_injective : Function.Injective (embeddingCoords K) := by
  intro x y hxy
  apply mixedEmbedding_injective K
  have h := congrArg (fun z => (euclidean.toMixed K)
    ((euclidean.stdOrthonormalBasis K).repr.symm z)) hxy
  simpa [embeddingCoords] using h

private noncomputable def hkFEPointLatticeEquiv (I : NumberFieldFractionalIdealGroup K) :
    hkPointSubtype I ≃ idealZLattice K I :=
  Equiv.ofBijective
    (fun x : hkPointSubtype I =>
      ⟨embeddingCoords K x.1,
        (mem_idealZLattice K I (embeddingCoords K x.1)).mpr ⟨x.1, x.2, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply hkFE_embeddingCoords_injective
      exact congrArg Subtype.val hxy,
     by
      intro v
      let hmem := (mem_idealZLattice K I v.1).mp v.2
      refine ⟨⟨Classical.choose hmem, (Classical.choose_spec hmem).1⟩, ?_⟩
      apply Subtype.ext
      exact (Classical.choose_spec hmem).2⟩

private theorem hkFE_gaussian_summable (I : NumberFieldFractionalIdealGroup K)
    {t : ℝ} (ht : 0 < t) (v : logSpace K) :
    Summable (fun x : hkPointSubtype I =>
      Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        heckeWeights K t v w * (w x.1) ^ 2)) := by
  let c := heckeWeights K t v
  have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  let a := Finset.univ.inf' hne c
  have ha : 0 < a := (Finset.lt_inf'_iff hne).mpr
    (fun w _ => heckeWeights_pos K ht v w)
  have hca : ∀ w : InfinitePlace K, a ≤ c w :=
    fun w => Finset.inf'_le _ (Finset.mem_univ w)
  have hplace : ∀ i : index K, a ≤ placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hca w
  have hlat := DedekindResidue.summable_real_weightedGaussian
    (idealZLattice K I) ha hplace
  have hcomp : Summable (fun x : hkPointSubtype I =>
      Real.exp (-Real.pi * ∑ i : index K,
        placeWeights K c i * ((hkFEPointLatticeEquiv I x :
          EuclideanSpace ℝ (index K)) i) ^ 2)) :=
    (Equiv.summable_iff (hkFEPointLatticeEquiv I)).mpr hlat
  apply hcomp.congr
  intro x
  have hcoords :
      (hkFEPointLatticeEquiv I x : EuclideanSpace ℝ (index K)) =
        embeddingCoords K x.1 := rfl
  rw [hcoords, ← DedekindResidue.sum_placeWeights_embeddingCoords_sq]

private theorem hkFEIdealRayClassPointWeight_norm_le [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (A : FractionalIdeal (𝓞 K)⁰ K) :
    ‖hkFEIdealRayClassPointWeight ψ C A‖ ≤
      ∑ D : RayClassGroup m, ‖(ψ D : ℂ)‖ := by
  exact hkFE_rayClassTerm_norm_le_sum ψ C (hkIntegralPart A)

private theorem hkFE_pointIdeal_class_eq [IsTotallyComplex K]
    {m : RayClassModulus K} (I : NumberFieldFractionalIdealGroup K)
    {x : K} (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) (hx0 : x ≠ 0)
    (hA : IsCoprimeTo m (hkIntegralPart
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K))))
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hclass : rayClass m (hkIntegralPart
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K))) hA =
      (rayClass m J hJ)⁻¹) :
    ClassGroup.mk K I = ClassGroup.mk K (idealUnit J hJ.1) := by
  classical
  let A : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)
  let P : Ideal (𝓞 K) := hkIntegralPart A
  have hbridge := hk_point_ideal_integral I hx
  have hprodCop : IsCoprimeTo m (P * J) := hkFE_coprime_mul hA hJ
  have hprodClass : rayClass m (P * J) hprodCop = 1 := by
    rw [hkFE_rayClass_mul hA hJ, hclass]
    simp
  have hprin : Submodule.IsPrincipal (P * J) :=
    isPrincipal_of_rayClass_eq_one m (P * J) hprodCop hprodClass
  have hprinFrac :
      (((P * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal (R := 𝓞 K) (K := K)
      (I := P * J)).mpr hprin
  have hmkProd :
      ClassGroup.mk K (idealUnit P hA.1) *
        ClassGroup.mk K (idealUnit J hJ.1) = 1 := by
    have hmk : ClassGroup.mk K (idealUnit (P * J) hprodCop.1) = 1 :=
      ClassGroup.mk_eq_one_iff.mpr hprinFrac
    calc
      _ = ClassGroup.mk K (idealUnit P hA.1 * idealUnit J hJ.1) := by
        exact (map_mul (ClassGroup.mk K) _ _).symm
      _ = ClassGroup.mk K (idealUnit (P * J) hprodCop.1) := by
        rw [← hkFE_idealUnit_mul P J hA.1 hJ.1 (mul_ne_zero hA.1 hJ.1)]
      _ = 1 := hmk
  let a : Kˣ := Units.mk0 x hx0
  have hPUnit : idealUnit P hA.1 = toPrincipalIdeal (𝓞 K) K a * I⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change (P : FractionalIdeal (𝓞 K)⁰ K) =
      (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
        ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
    have hbridge' : (P : FractionalIdeal (𝓞 K)⁰ K) = A := by simpa [A, P] using hbridge
    calc
      (P : FractionalIdeal (𝓞 K)⁰ K) = A := hbridge'
      _ = (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
          ((I : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
        dsimp [A]
        rw [coe_toPrincipalIdeal]
        simp [a]
  have hmkPrincipal : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨x, rfl⟩⟩
  have hmkA : ClassGroup.mk K (idealUnit P hA.1) =
      (ClassGroup.mk K I)⁻¹ := by
    calc
      _ = ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) *
          ClassGroup.mk K (I⁻¹) := by rw [hPUnit, map_mul]
      _ = (ClassGroup.mk K I)⁻¹ := by rw [hmkPrincipal, map_inv, one_mul]
  rw [hmkA] at hmkProd
  have hmul := congrArg (fun z : ClassGroup (𝓞 K) => ClassGroup.mk K I * z) hmkProd
  rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at hmul
  exact hmul.symm

private theorem hkFEIdealRayClassPointWeight_eq_zero_of_class_ne [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    {x : K} (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) (hx0 : x ≠ 0)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hclass : rayClass m J hJ = C⁻¹)
    (hne : ClassGroup.mk K I ≠ ClassGroup.mk K (idealUnit J hJ.1)) :
    hkFEIdealRayClassPointWeight ψ C
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) = 0 := by
  classical
  let A := FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)
  by_cases hA : IsCoprimeTo m (hkIntegralPart A)
  · by_cases hC : rayClass m (hkIntegralPart A) hA = C
    · have hclassA : rayClass m (hkIntegralPart A) hA = (rayClass m J hJ)⁻¹ := by
        calc
          rayClass m (hkIntegralPart A) hA = C := hC
          _ = (rayClass m J hJ)⁻¹ := by
            rw [hclass]
            exact (inv_inv C).symm
      exact (hne (hkFE_pointIdeal_class_eq I hx hx0 hA J hJ hclassA)).elim
    · simp [hkFEIdealRayClassPointWeight, hkFEIdealRayClassTerm, A, hA, hC]
  · simp [hkFEIdealRayClassPointWeight, hkFEIdealRayClassTerm, A, hA]

private noncomputable def hkScalePointEquiv (I : NumberFieldFractionalIdealGroup K)
    (a : Kˣ) : hkPointSubtype I ≃ hkPointSubtype (toPrincipalIdeal (𝓞 K) K a * I) where
  toFun x := ⟨(a : K) * x.1, by
    change (a : K) * x.1 ∈
      (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_singleton_mul.mpr ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨(a : K)⁻¹ * y.1, by
    have hy : y.1 ∈
        (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) := y.2
    rw [coe_toPrincipalIdeal] at hy
    obtain ⟨x, hx, hxy⟩ := FractionalIdeal.mem_singleton_mul.mp hy
    change (a : K)⁻¹ * y.1 ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [hxy]
    simpa using hx⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]

/-- A theta sum with a weight depending only on the point ideal; zero is omitted. -/
private noncomputable def hkIdealWeightTheta (w : FractionalIdeal (𝓞 K)⁰ K → ℂ)
    (I : NumberFieldFractionalIdealGroup K) (c : InfinitePlace K → ℝ) : ℂ :=
  ∑' x : hkPointSubtype I, if x.1 = 0 then 0 else
      w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
      (Real.exp (-Real.pi * ∑ v : InfinitePlace K, c v * (v x.1) ^ 2) : ℂ)

/-- A theta sum with a weight depending on the point ideal, omitting zero. -/
noncomputable def hkFEIdealWeightTheta (w : FractionalIdeal (𝓞 K)⁰ K → ℂ)
    (I : NumberFieldFractionalIdealGroup K) (c : InfinitePlace K → ℝ) : ℂ :=
  hkIdealWeightTheta w I c

private theorem hkFE_integralIdealGaussian_place (c : InfinitePlace K → ℝ) (x : 𝓞 K) :
    integralIdealGaussian (placeWeights K c) x =
      Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        c w * (w (algebraMap (𝓞 K) K x)) ^ 2) := by
  unfold integralIdealGaussian
  rw [← DedekindResidue.sum_placeWeights_embeddingCoords_sq]

private theorem hkFEIdealWeightTheta_rayThetaTail [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hclass : rayClass m J hJ = C⁻¹) {t : ℝ} (ht : 0 < t) (v : logSpace K) :
    hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) (idealUnit J hJ.1)
        (heckeWeights K t v) =
      (ψ C : ℂ) * (rayThetaTail m J hJ (heckeWeights K t v) : ℂ) := by
  classical
  let c := heckeWeights K t v
  let e := hkFEIntegralPointEquiv J hJ.1
  have hsource : hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C)
        (idealUnit J hJ.1) c =
      ∑' y : J, if y.1 = 0 then 0 else
        (if rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 then (ψ C : ℂ) else 0) *
          (integralIdealGaussian (placeWeights K c) y.1 : ℂ) := by
    unfold hkIdealWeightTheta
    conv_lhs => rw [← Equiv.tsum_eq e.symm]
    apply tsum_congr
    intro y
    have hyval : (e.symm y).1 = algebraMap (𝓞 K) K y.1 := rfl
    by_cases hy0 : y.1 = 0
    · have hx0 : (e.symm y).1 = 0 := by rw [hyval, hy0]; simp
      simp [hx0, hy0]
    · have hx0 : (e.symm y).1 ≠ 0 := by
        rw [hyval]
        intro hz
        exact hy0 ((FaithfulSMul.algebraMap_injective (𝓞 K) K) hz)
      simp only [if_neg hx0, if_neg hy0]
      have hw := hkFEIdealRayClassPointWeight_eq_rayKernel ψ C J hJ hclass y hy0
      rw [hyval]
      rw [hw, hkFE_integralIdealGaussian_place]
  let hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  let a := Finset.univ.inf' hne (heckeWeights K t v)
  have ha : 0 < a := (Finset.lt_inf'_iff hne).mpr
    (fun w _ => heckeWeights_pos K ht v w)
  have hca : ∀ w : InfinitePlace K, a ≤ heckeWeights K t v w :=
    fun w => Finset.inf'_le _ (Finset.mem_univ w)
  have hplace : ∀ i : index K, a ≤ placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hca w
  have hreal := summable_integralIdealGaussian m J hJ (placeWeights K c) ha hplace
  have hrealTail : Summable (fun y : rayKernelPoints m J =>
      if y.1.1 = 0 then 0 else integralIdealGaussian (placeWeights K c) y.1.1) := by
    apply hreal.of_nonneg_of_le
    · intro y
      by_cases hy : y.1.1 = 0
      · simp [hy]
      · simp [hy]
        unfold integralIdealGaussian
        positivity
    · intro y
      by_cases hy : y.1.1 = 0
      · simp [hy]
        unfold integralIdealGaussian
        positivity
      · simp [hy]
  have hcomplexTail : Summable (fun y : rayKernelPoints m J =>
      (if y.1.1 = 0 then 0 else integralIdealGaussian (placeWeights K c) y.1.1 : ℂ)) := by
    apply Summable.of_norm
    have hnorm : Summable (fun y : rayKernelPoints m J =>
        ‖(if y.1.1 = 0 then 0 else
          integralIdealGaussian (placeWeights K c) y.1.1 : ℂ)‖) := by
      refine hrealTail.congr fun y => ?_
      by_cases hy : y.1.1 = 0
      · simp [hy]
      · have hpos : 0 ≤ integralIdealGaussian (placeWeights K c) y.1.1 := by
          unfold integralIdealGaussian
          exact Real.exp_nonneg _
        simp [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    exact hnorm
  have hsub :
      (∑' y : J, if rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 then
        (if y.1 = 0 then 0 else
          (integralIdealGaussian (placeWeights K c) y.1 : ℂ)) else 0) =
      ∑' y : rayKernelPoints m J, if y.1.1 = 0 then 0 else
        (integralIdealGaussian (placeWeights K c) y.1.1 : ℂ) := by
    change (∑' y : J, if rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 then
        (if y.1 = 0 then 0 else
          (integralIdealGaussian (placeWeights K c) y.1 : ℂ)) else 0) =
      ∑' y : {y : J // rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1},
        if y.1.1 = 0 then 0 else
          (integralIdealGaussian (placeWeights K c) y.1.1 : ℂ)
    exact (tsum_subtype (α := ℂ) (β := J)
      {y : J | rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1}
      (fun y => if y.1 = 0 then 0 else
        (integralIdealGaussian (placeWeights K c) y.1 : ℂ))).symm
  have htailComplex : (rayThetaTail m J hJ c : ℂ) =
      ∑' y : rayKernelPoints m J,
        (if y.1.1 = 0 then 0 else
          (integralIdealGaussian (placeWeights K c) y.1.1 : ℂ)) := by
    unfold rayThetaTail
    rw [show ((∑' y : rayKernelPoints m J,
        (if y.1.1 = 0 then 0 else
          integralIdealGaussian (placeWeights K c) y.1.1 : ℝ) : ℝ) : ℂ) =
        Complex.ofRealCLM (∑' y : rayKernelPoints m J,
          (if y.1.1 = 0 then 0 else
            integralIdealGaussian (placeWeights K c) y.1.1 : ℝ)) from rfl]
    rw [ContinuousLinearMap.map_tsum Complex.ofRealCLM hrealTail]
    apply tsum_congr
    intro y
    by_cases hz : y.1.1 = 0 <;> simp [hz]
  calc
    hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) (idealUnit J hJ.1) c =
        ∑' y : J, if y.1 = 0 then 0 else
          (if rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 then (ψ C : ℂ) else 0) *
            (integralIdealGaussian (placeWeights K c) y.1 : ℂ) := hsource
    _ = (ψ C : ℂ) *
          ∑' y : J, if rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 then
            (if y.1 = 0 then 0 else
              (integralIdealGaussian (placeWeights K c) y.1 : ℂ)) else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro y
        by_cases hz : y.1 = 0 <;> by_cases hk :
          rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 <;> simp [hz, hk]
    _ = (ψ C : ℂ) *
          ∑' y : rayKernelPoints m J, if y.1.1 = 0 then 0 else
            (integralIdealGaussian (placeWeights K c) y.1.1 : ℂ) := by rw [hsub]
    _ = (ψ C : ℂ) * (rayThetaTail m J hJ c : ℂ) := by rw [htailComplex]

private theorem hkFEIdealWeightTheta_terms_summable [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    {t : ℝ} (ht : 0 < t) (v : logSpace K) :
    Summable (fun x : hkPointSubtype I => if x.1 = 0 then 0 else
      hkFEIdealRayClassPointWeight ψ C
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
          (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) := by
  classical
  let M : ℝ := ∑ D : RayClassGroup m, ‖(ψ D : ℂ)‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hgauss := hkFE_gaussian_summable I ht v
  have hmajor := hgauss.mul_left M
  apply hmajor.of_norm_bounded
  intro x
  by_cases hx : x.1 = 0
  · simp [hx]
    positivity
  · have hweight := hkFEIdealRayClassPointWeight_norm_le ψ C
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K))
    have hexp : 0 ≤ Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        heckeWeights K t v w * (w x.1) ^ 2) := Real.exp_nonneg _
    simp only [if_neg hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖hkFEIdealRayClassPointWeight ψ C
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K))‖ *
          Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2)
        ≤ M * Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) :=
          mul_le_mul_of_nonneg_right (by simpa [M] using hweight) hexp
      _ = _ := rfl

private theorem hkFEWeightedThetaTail_eq_rayClass_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) {t : ℝ} (ht : 0 < t) (v : logSpace K) :
    (∑' x : hkPointSubtype I, if x.1 = 0 then 0 else
      hkPointWeight ψ I x.1 *
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) =
      ∑ C : RayClassGroup m,
        hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
          (heckeWeights K t v) := by
  classical
  let f : RayClassGroup m → hkPointSubtype I → ℂ := fun C x =>
    if x.1 = 0 then 0 else
      hkFEIdealRayClassPointWeight ψ C
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
          (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          heckeWeights K t v w * (w x.1) ^ 2) : ℂ)
  have hpoint : ∀ x : hkPointSubtype I,
      (if x.1 = 0 then 0 else hkPointWeight ψ I x.1 *
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) =
        ∑ C : RayClassGroup m, f C x := by
    intro x
    by_cases hx : x.1 = 0
    · simp [f, hx]
    · simp only [if_neg hx, f]
      rw [hkPointWeight_eq_rayClass_sum ψ I hx, Finset.sum_mul]
  calc
    _ = ∑' x : hkPointSubtype I, ∑ C : RayClassGroup m, f C x := by
      apply tsum_congr
      exact hpoint
    _ = ∑ C : RayClassGroup m, ∑' x : hkPointSubtype I, f C x := by
      rw [Summable.tsum_finsetSum (fun C hC =>
        hkFEIdealWeightTheta_terms_summable ψ C I ht v)]
    _ = ∑ C : RayClassGroup m,
        hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
          (heckeWeights K t v) := by
      apply Finset.sum_congr rfl
      intro C hC
      rfl

private theorem hkFEFractionalCharValue_norm_le_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) :
    ‖hkFractionalCharValue ψ I‖ ≤ ∑ C : RayClassGroup m, ‖(ψ C : ℂ)‖ := by
  classical
  by_cases hI : I ∈ rayClassPrimeToIdeals m
  · simp only [hkFractionalCharValue, dif_pos hI]
    exact Finset.single_le_sum
      (fun D hD => norm_nonneg (ψ D : ℂ))
      (Finset.mem_univ (QuotientGroup.mk (⟨I, hI⟩ : rayClassPrimeToIdeals m)))
  · simp [hkFractionalCharValue, hI]
    positivity

private theorem hkFEPointWeight_norm_le_sum [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) (x : K) :
    ‖hkPointWeight ψ I x‖ ≤ ∑ C : RayClassGroup m, ‖(ψ C : ℂ)‖ := by
  classical
  by_cases hx : x = 0
  · simp only [hkPointWeight, if_pos hx]
    by_cases hm : m.finitePart = 0
    · simp only [if_pos hm]
      exact hkFEFractionalCharValue_norm_le_sum ψ I⁻¹
    · simp [hm]
      positivity
  · simp only [hkPointWeight, if_neg hx]
    exact hkFE_charValue_norm_le_sum ψ
      (hkIntegralPart (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)))

private theorem hkFEWeightedTheta_eq_zero_add_components [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) {t : ℝ} (ht : 0 < t) (v : logSpace K) :
    hkWeightedTheta ψ I (heckeWeights K t v) =
      (hkPointWeight ψ I 0 : ℂ) +
        ∑ C : RayClassGroup m,
          hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
            (heckeWeights K t v) := by
  classical
  let M : ℝ := ∑ C : RayClassGroup m, ‖(ψ C : ℂ)‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hgauss := hkFE_gaussian_summable I ht v
  have hmajor := hgauss.mul_left M
  have hfull : Summable (fun x : hkPointSubtype I =>
      hkPointWeight ψ I x.1 *
        (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
          heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) := by
    apply hmajor.of_norm_bounded
    intro x
    have hw := hkFEPointWeight_norm_le_sum ψ I x.1
    have hexp : 0 ≤ Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        heckeWeights K t v w * (w x.1) ^ 2) := Real.exp_nonneg _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖hkPointWeight ψ I x.1‖ *
          Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2)
        ≤ M * Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) :=
          mul_le_mul_of_nonneg_right (by simpa [M] using hw) hexp
      _ = _ := rfl
  let z : hkPointSubtype I := ⟨0, FractionalIdeal.zero_mem _⟩
  have hsplit := hfull.tsum_eq_add_tsum_ite z
  have hzero : hkPointWeight ψ I z.1 *
      (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        heckeWeights K t v w * (w z.1) ^ 2) : ℂ) =
      (hkPointWeight ψ I 0 : ℂ) := by simp [z]
  rw [hkWeightedTheta, hsplit, hzero]
  have htail :
      (∑' x : hkPointSubtype I,
        if x = z then 0 else hkPointWeight ψ I x.1 *
          (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) =
      ∑' x : hkPointSubtype I, if x.1 = 0 then 0 else
        hkPointWeight ψ I x.1 *
          (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) : ℂ) := by
    apply tsum_congr
    intro x
    by_cases hx : x.1 = 0
    · have hxz : x = z := by apply Subtype.ext; exact hx
      simp [hxz, z]
    · have hxz : x ≠ z := by
        intro heq
        exact hx (by simpa [z] using congrArg Subtype.val heq)
      simp [hx, hxz]
  rw [htail, hkFEWeightedThetaTail_eq_rayClass_sum ψ I ht v]

private theorem hkIdealWeightTheta_principal_mul
    (w : FractionalIdeal (𝓞 K)⁰ K → ℂ) (I : NumberFieldFractionalIdealGroup K)
    (a : Kˣ) (c : InfinitePlace K → ℝ) :
    hkIdealWeightTheta w (toPrincipalIdeal (𝓞 K) K a * I) c =
      hkIdealWeightTheta w I (fun v => (v (a : K)) ^ 2 * c v) := by
  rw [hkIdealWeightTheta, hkIdealWeightTheta]
  let e := hkScalePointEquiv I a
  conv_lhs => rw [← Equiv.tsum_eq e]
  refine tsum_congr fun x => ?_
  have heval : (e x).1 = (a : K) * x.1 := rfl
  change (if (e x).1 = 0 then 0 else
      w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (e x).1 *
        ((toPrincipalIdeal (𝓞 K) K a * I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
        (Real.exp (-Real.pi * ∑ v : InfinitePlace K, c v * (v (e x).1) ^ 2) : ℂ)) =
    (if x.1 = 0 then 0 else
      w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
        (Real.exp (-Real.pi * ∑ v : InfinitePlace K,
          ((v (a : K)) ^ 2 * c v) * (v x.1) ^ 2) : ℂ))
  by_cases hx : x.1 = 0
  · have hevalZero : (e x).1 = 0 := by rw [heval, hx, mul_zero]
    simp [hx, hevalZero]
  · have hne : (e x).1 ≠ 0 := by rw [heval]; exact mul_ne_zero (Units.ne_zero a) hx
    have hIdeal :
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K) * x.1) *
            ((toPrincipalIdeal (𝓞 K) K a * I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
      have hInv : (toPrincipalIdeal (𝓞 K) K a * I)⁻¹ =
          I⁻¹ * (toPrincipalIdeal (𝓞 K) K a)⁻¹ := by group
      have hInvVal :
          ((toPrincipalIdeal (𝓞 K) K a * I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) =
          (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) *
            ((toPrincipalIdeal (𝓞 K) K a)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
        have h := congrArg (fun U : NumberFieldFractionalIdealGroup K =>
          (U : FractionalIdeal (𝓞 K)⁰ K)) hInv
        simpa only [Units.val_inv_eq_inv_val, Units.val_mul] using h
      rw [hInvVal, coe_toPrincipalIdeal]
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
      calc
        _ = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) *
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))⁻¹) *
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
                (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) := by ac_rfl
        _ = _ := by
          rw [FractionalIdeal.spanSingleton_mul_inv K (Units.ne_zero a)]
          simp
    rw [if_neg hne, if_neg hx, heval, hIdeal]
    apply congrArg (fun z : ℂ =>
      w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
        (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) * z)
    apply congrArg (fun r : ℝ => (Real.exp r : ℂ))
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    simp only [map_mul, mul_pow]
    ring

theorem hkFEIdealWeightTheta_integrableOn_box [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hRay : rayClass m J hJ = C⁻¹) (hOrd : ClassGroup.mk K I =
      ClassGroup.mk K (idealUnit J hJ.1)) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun v : logSpace K =>
      hkFEIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
        (heckeWeights K ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * T) v))
      (ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)) := by
  classical
  obtain ⟨a, ha⟩ := (classGroup_mk_eq_mk_iff (K := K)).mp hOrd
  let nA : ℝ := ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ)
  let tI := (idealNormR K I)⁻¹ ^ 2 * heckeBeta K * T
  let tJ := (idealNormR K (idealUnit J hJ.1))⁻¹ ^ 2 * heckeBeta K * T
  have hIpos : 0 < idealNormR K I := idealNormR_pos K I
  have hApos : 0 < nA := by
    dsimp [nA]
    rw [Rat.cast_pos, abs_pos]
    exact Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a)
  have hnorm := idealNormR_principal_mul K I a
  have hnormJ : idealNormR K (idealUnit J hJ.1) =
      nA * idealNormR K I := by
    rw [← ha, hnorm]
  have hscale : nA ^ 2 * tJ = tI := by
    dsimp [tI, tJ]
    rw [hnormJ]
    field_simp [hApos.ne', hIpos.ne']
  have hJpos : 0 < idealNormR K (idealUnit J hJ.1) := idealNormR_pos K _
  have htJ : 0 < tJ := by
    dsimp [tJ]
    exact mul_pos (mul_pos (pow_pos (inv_pos.mpr hJpos) 2) (heckeBeta_pos K)) hT
  let w : FractionalIdeal (𝓞 K)⁰ K → ℂ := hkFEIdealRayClassPointWeight ψ C
  have hthetaShift : ∀ u : logSpace K,
      hkIdealWeightTheta w (idealUnit J hJ.1) (heckeWeights K tJ u) =
        hkIdealWeightTheta w I
          (heckeWeights K tI (u + xShift K (a : K))) := by
    intro u
    rw [← ha, hkIdealWeightTheta_principal_mul]
    congr 1
    funext z
    have hsq := DedekindResidue.sq_mul_heckeWeights K (Units.ne_zero a)
      (le_of_lt htJ) u z
    have hscale' : ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) ^ 2 * tJ = tI := by
      simpa [nA] using hscale
    rw [hscale'] at hsq
    simpa [tI, tJ] using hsq
  have hpointwise : ∀ u : logSpace K,
      hkIdealWeightTheta w I (heckeWeights K tI u) =
        (ψ C : ℂ) *
          (rayThetaTail m J hJ (heckeWeights K tJ (u - xShift K (a : K))) : ℂ) := by
    intro u
    have h := hthetaShift (u - xShift K (a : K))
    have hcancel : u - xShift K (a : K) + xShift K (a : K) = u := by abel
    rw [hcancel] at h
    calc
      _ = hkIdealWeightTheta w (idealUnit J hJ.1)
          (heckeWeights K tJ (u - xShift K (a : K))) := h.symm
      _ = _ := hkFEIdealWeightTheta_rayThetaTail ψ C J hJ hRay htJ _
  have htailCont : Continuous (fun u : logSpace K =>
      rayThetaTail m J hJ (heckeWeights K tJ u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hR := (continuousAt_rayTheta_heckeWeights m J hJ (p := (tJ, u)) htJ).comp
      ((continuous_const.prodMk continuous_id).continuousAt)
    have hfun : (fun v : logSpace K => rayThetaTail m J hJ (heckeWeights K tJ v)) =
        fun v => rayTheta m J hJ (heckeWeights K tJ v) -
          (if m.finitePart = 0 then 1 else 0) := by
      funext v
      exact rayThetaTail_eq_theta_sub_delta m J hJ htJ v
    rw [hfun]
    exact hR.sub continuousAt_const
  have htailComplex : Continuous (fun u : logSpace K =>
      (rayThetaTail m J hJ (heckeWeights K tJ u) : ℂ)) :=
    Complex.continuous_ofReal.comp htailCont
  have htranslated : Continuous (fun u : logSpace K =>
      (ψ C : ℂ) *
        (rayThetaTail m J hJ (heckeWeights K tJ (u - xShift K (a : K))) : ℂ)) :=
    continuous_const.mul (htailComplex.comp (continuous_id.sub continuous_const))
  have hcont : Continuous (fun u : logSpace K =>
      hkIdealWeightTheta w I (heckeWeights K tI u)) := by
    rw [show (fun u : logSpace K => hkIdealWeightTheta w I (heckeWeights K tI u)) =
      (fun u => (ψ C : ℂ) *
        (rayThetaTail m J hJ
          (heckeWeights K tJ (u - xShift K (a : K))) : ℂ)) from funext hpointwise]
    exact htranslated
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  have hcompact : IsCompact (closure B) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  change IntegrableOn (fun u : logSpace K =>
    hkIdealWeightTheta w I (heckeWeights K tI u)) B
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

theorem hkFEIdealWeightTheta_integrableOn_box_of_class_ne [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hRay : rayClass m J hJ = C⁻¹)
    (hne : ClassGroup.mk K I ≠ ClassGroup.mk K (idealUnit J hJ.1))
    (t : ℝ) :
    IntegrableOn (fun v : logSpace K =>
      hkFEIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
        (heckeWeights K t v))
      (ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)) := by
  classical
  let w : FractionalIdeal (𝓞 K)⁰ K → ℂ := hkFEIdealRayClassPointWeight ψ C
  have hzero : ∀ v : logSpace K, hkIdealWeightTheta w I (heckeWeights K t v) = 0 := by
    intro v
    unfold hkIdealWeightTheta
    have hterm : ∀ x : hkPointSubtype I,
        (if x.1 = 0 then 0 else
          w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
          (Real.exp (-Real.pi * ∑ u : InfinitePlace K,
            heckeWeights K t v u * (u x.1) ^ 2) : ℂ)) = 0 := by
      intro x
      by_cases hx : x.1 = 0
      · simp [hx]
      · simp only [if_neg hx]
        simpa [w] using congrArg (fun z : ℂ => z *
          (Real.exp (-Real.pi * ∑ u : InfinitePlace K,
            heckeWeights K t v u * (u x.1) ^ 2) : ℂ))
          (hkFEIdealRayClassPointWeight_eq_zero_of_class_ne ψ C I
            x.2 hx J hJ hRay hne)
    have hfun : (fun x : hkPointSubtype I =>
        if x.1 = 0 then 0 else
          w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
          (Real.exp (-Real.pi * ∑ u : InfinitePlace K,
            heckeWeights K t v u * (u x.1) ^ 2) : ℂ)) = fun _ => 0 := by
      funext x
      exact hterm x
    rw [hfun]
    simp
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  change IntegrableOn (fun v : logSpace K => hkFEIdealWeightTheta
    (hkFEIdealRayClassPointWeight ψ C) I (heckeWeights K t v)) B
  rw [show (fun v : logSpace K => hkFEIdealWeightTheta
      (hkFEIdealRayClassPointWeight ψ C) I (heckeWeights K t v)) =
    fun _ => 0 from funext (by intro v; simpa [hkFEIdealWeightTheta, w] using hzero v)]
  exact integrableOn_const (C := (0 : ℂ)) (ne_top_of_lt hBfin)


private theorem setIntegral_fundamentalDomain_comp_neg_add_complex
    {ι κ : Type*} [Fintype ι] [Fintype κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → E)
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
  have hset : ZSpan.fundamentalDomain b = τ ⁻¹' (τ ⁻¹' ZSpan.fundamentalDomain b) := by
    ext x
    have hττ : τ (τ x) = x := by
      rw [hτ]
      simp only [neg_add_rev, neg_neg]
      abel
    simp [Set.mem_preimage, hττ]
  conv_lhs => rw [hset]
  rw [hmp.setIntegral_preimage_emb hemb]
  have hv : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)) (ι → ℝ) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup (ι → ℝ) volume)
  refine hD'.setIntegral_eq hFD (f := f) (fun g x => ?_)
  rw [Submodule.vadd_def, vadd_eq_add]
  exact hf g x

private theorem setIntegral_fundamentalDomain_comp_add_complex
    {ι κ : Type*} [Fintype ι] [Fintype κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → E)
    (hf : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x, f (↑l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain b, f (u + s) =
      ∫ u in ZSpan.fundamentalDomain b, f u := by
  have hneg : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x : ι → ℝ,
      f (-(↑l + x)) = f (-x) := by
    intro l x
    have := hf (-l) (-x)
    rw [show ((↑(-l) : ι → ℝ) + -x) = -(↑l + x) by push_cast; abel] at this
    exact this
  have e1 : ∫ u in ZSpan.fundamentalDomain b, f (u + s) =
      ∫ u in ZSpan.fundamentalDomain b, (fun v => f (-v)) (-u + (-s)) := by
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b)
      (fun u _ => ?_)
    congr 1
    abel
  rw [e1, setIntegral_fundamentalDomain_comp_neg_add_complex b (-s)
    (fun v => f (-v)) hneg]
  have e2 : ∫ u in ZSpan.fundamentalDomain b, (fun v => f (-v)) u =
      ∫ u in ZSpan.fundamentalDomain b, f (-u + 0) := by
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b)
      (fun u _ => ?_)
    simp
  rw [e2, setIntegral_fundamentalDomain_comp_neg_add_complex b 0 f hf]

/-- The full-unit-box average of an ideal-weighted theta. -/
noncomputable def hkFEIdealWeightG (w : FractionalIdeal (𝓞 K)⁰ K → ℂ)
    (I : NumberFieldFractionalIdealGroup K) (t : ℝ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    ∫ v in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      hkFEIdealWeightTheta w I (heckeWeights K t v)

noncomputable def hkFEIdealRayGtail [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ v in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      rayThetaTail m J hJ (heckeWeights K t v)

theorem hkFEIdealWeightG_rayGtail [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hclass : rayClass m J hJ = C⁻¹) {t : ℝ} (ht : 0 < t) :
    hkFEIdealWeightG (hkFEIdealRayClassPointWeight ψ C) (idealUnit J hJ.1) t =
      (ψ C : ℂ) * (hkFEIdealRayGtail m J hJ t : ℂ) := by
  classical
  unfold hkFEIdealWeightG hkFEIdealRayGtail
  simp_rw [hkFEIdealWeightTheta, hkFEIdealWeightTheta_rayThetaTail ψ C J hJ hclass ht]
  rw [integral_const_mul, integral_complex_ofReal]
  have hT : ((torsionOrder K : ℂ)⁻¹) =
      (((torsionOrder K : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hT]
  push_cast
  ring

theorem hkFEIdealRayGtail_eq_rayF_sub_constant [IsTotallyComplex K]
    {m : RayClassModulus K} (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    {T : ℝ} (hT : 0 < T) :
    hkFEIdealRayGtail m J hJ
        ((idealNormR K (idealUnit J hJ.1))⁻¹ ^ 2 * heckeBeta K * T) =
      rayF m J hJ T - rayPrimalConstant m := by
  classical
  let t := (idealNormR K (idealUnit J hJ.1))⁻¹ ^ 2 * heckeBeta K * T
  have hN : 0 < idealNormR K (idealUnit J hJ.1) := idealNormR_pos K _
  have hβ := heckeBeta_pos K
  have ht : 0 < t := by
    dsimp [t]
    exact mul_pos (mul_pos (pow_pos (inv_pos.mpr hN) 2) hβ) hT
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  let d : ℝ := if m.finitePart = 0 then 1 else 0
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  have hcompact : IsCompact (closure B) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  have hcont : Continuous (fun u : logSpace K => rayTheta m J hJ (heckeWeights K t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (continuousAt_rayTheta_heckeWeights m J hJ (p := (t, u)) ht).comp
      ((continuous_const.prodMk continuous_id).continuousAt)
  have hint : IntegrableOn (fun u : logSpace K =>
      rayTheta m J hJ (heckeWeights K t u)) B :=
    (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have htailInt : IntegrableOn (fun u : logSpace K =>
      rayThetaTail m J hJ (heckeWeights K t u)) B := by
    have hi := hint.sub (integrableOn_const (C := d) (ne_top_of_lt hBfin))
    change IntegrableOn (fun u => rayTheta m J hJ (heckeWeights K t u) - d) B at hi
    simpa only [rayThetaTail_eq_theta_sub_delta m J hJ ht] using hi
  have hvol : volume.real B = unitBoxVol K := by
    rw [DedekindResidue.unitBoxVol]
    rfl
  have hId : rayG m J hJ t - rayPrimalConstant m =
      (torsionOrder K : ℝ)⁻¹ *
        ∫ u in B, rayThetaTail m J hJ (heckeWeights K t u) := by
    simp_rw [rayThetaTail_eq_theta_sub_delta m J hJ ht]
    rw [integral_sub hint (integrableOn_const (C := d) (ne_top_of_lt hBfin)),
      setIntegral_const, smul_eq_mul, hvol]
    dsimp [rayG, rayPrimalConstant, B, d]
    ring
  dsimp [hkFEIdealRayGtail, rayF, t]
  exact hId.symm

noncomputable def hkFEIdealWeightNormalizedG
    (w : FractionalIdeal (𝓞 K)⁰ K → ℂ)
    (I : NumberFieldFractionalIdealGroup K) (t : ℝ) : ℂ :=
  hkFEIdealWeightG w I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t)

private theorem hkFEIdealWeightTheta_heckeWeights_periodic
    (w : FractionalIdeal (𝓞 K)⁰ K → ℂ) (I : NumberFieldFractionalIdealGroup K)
    (t : ℝ) (v : logSpace K) (u : (𝓞 K)ˣ) :
    hkFEIdealWeightTheta w I (heckeWeights K t (v + logEmbedding K (Additive.ofMul u))) =
      hkFEIdealWeightTheta w I (heckeWeights K t v) := by
  rw [heckeWeights_add_logEmbedding]
  let a : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have ha : toPrincipalIdeal (𝓞 K) K a = 1 := by
    simpa [a] using rayPrincipalIdeal_of_integralUnit (K := K) u
  have hprincipal := hkIdealWeightTheta_principal_mul w I a (heckeWeights K t v)
  have hprincipal' := hprincipal.symm
  rw [ha, one_mul] at hprincipal'
  exact hprincipal'

private theorem hkFEIdealWeightG_principal_mul
    (w : FractionalIdeal (𝓞 K)⁰ K → ℂ) (I : NumberFieldFractionalIdealGroup K)
    (a : Kˣ) {t : ℝ} (ht : 0 ≤ t) :
    hkFEIdealWeightG w (toPrincipalIdeal (𝓞 K) K a * I) t =
      hkFEIdealWeightG w I (((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) ^ 2 * t) := by
  unfold hkFEIdealWeightG
  congr 1
  have hpt : ∀ u : logSpace K,
      hkFEIdealWeightTheta w (toPrincipalIdeal (𝓞 K) K a * I) (heckeWeights K t u) =
        hkFEIdealWeightTheta w I
          (heckeWeights K (((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) ^ 2 * t)
            (u + xShift K (a : K))) := by
    intro u
    change hkIdealWeightTheta w (toPrincipalIdeal (𝓞 K) K a * I)
        (heckeWeights K t u) = _
    rw [hkIdealWeightTheta_principal_mul]
    congr 1
    funext v
    exact DedekindResidue.sq_mul_heckeWeights K (Units.ne_zero a) ht u v
  simp_rw [hpt]
  refine setIntegral_fundamentalDomain_comp_add_complex
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
    (xShift K (a : K))
    (fun u => hkFEIdealWeightTheta w I
      (heckeWeights K (((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) ^ 2 * t) u))
    (fun l v => ?_)
  have hl : (l : logSpace K) ∈ unitLattice K :=
    (le_of_eq ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ)) l.2
  obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hl
  rw [add_comm, ← hu]
  exact hkFEIdealWeightTheta_heckeWeights_periodic w I _ v (Additive.toMul u)

theorem hkFEIdealWeightNormalizedG_eq_of_mk_eq
    (w : FractionalIdeal (𝓞 K)⁰ K → ℂ)
    (I J : NumberFieldFractionalIdealGroup K)
    (h : ClassGroup.mk K I = ClassGroup.mk K J) {t : ℝ} (ht : 0 < t) :
    hkFEIdealWeightNormalizedG w I t = hkFEIdealWeightNormalizedG w J t := by
  obtain ⟨a, ha⟩ := (classGroup_mk_eq_mk_iff (K := K)).mp h
  have hnorm := idealNormR_principal_mul K I a
  have hN : 0 < idealNormR K I := idealNormR_pos K I
  have hA : 0 < ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [Rat.cast_pos, abs_pos]
    exact Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a)
  have hβ := heckeBeta_pos K
  unfold hkFEIdealWeightNormalizedG
  rw [← ha, hkFEIdealWeightG_principal_mul w I a (by positivity)]
  congr 1
  rw [hnorm]
  have hsq :
      ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) ^ 2 *
        ((((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) * idealNormR K I)⁻¹ ^ 2 *
          heckeBeta K * t) = (idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t := by
    field_simp [hA.ne', hN.ne']
  exact hsq.symm

theorem hkFEIdealWeightNormalizedG_rayGtail [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hRay : rayClass m J hJ = C⁻¹)
    (hOrd : ClassGroup.mk K I = ClassGroup.mk K (idealUnit J hJ.1))
    {T : ℝ} (hT : 0 < T) :
    hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) I T =
      (ψ C : ℂ) *
        (hkFEIdealRayGtail m J hJ
          ((idealNormR K (idealUnit J hJ.1))⁻¹ ^ 2 * heckeBeta K * T) : ℂ) := by
  calc
    hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) I T =
        hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C)
          (idealUnit J hJ.1) T :=
      hkFEIdealWeightNormalizedG_eq_of_mk_eq
        (hkFEIdealRayClassPointWeight ψ C) I (idealUnit J hJ.1) hOrd hT
    _ = _ := by
      unfold hkFEIdealWeightNormalizedG
      have hN : 0 < idealNormR K (idealUnit J hJ.1) := idealNormR_pos K _
      have hJt : 0 <
          (idealNormR K (idealUnit J hJ.1))⁻¹ ^ 2 * heckeBeta K * T := by
        exact mul_pos (mul_pos (pow_pos (inv_pos.mpr hN) 2) (heckeBeta_pos K)) hT
      exact hkFEIdealWeightG_rayGtail ψ C J hJ hRay hJt

theorem hkFEIdealWeightNormalizedG_eq_zero_of_class_ne [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (C : RayClassGroup m) (I : NumberFieldFractionalIdealGroup K)
    (J : Ideal (𝓞 K)) (hJ : IsCoprimeTo m J)
    (hRay : rayClass m J hJ = C⁻¹)
    (hne : ClassGroup.mk K I ≠ ClassGroup.mk K (idealUnit J hJ.1))
    (T : ℝ) : hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) I T = 0 := by
  let w : FractionalIdeal (𝓞 K)⁰ K → ℂ := hkFEIdealRayClassPointWeight ψ C
  have hzero : ∀ t : ℝ, ∀ v : logSpace K,
      hkIdealWeightTheta w I (heckeWeights K t v) = 0 := by
    intro t v
    unfold hkIdealWeightTheta
    have hterm : ∀ x : hkPointSubtype I,
        (if x.1 = 0 then 0 else
          w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
          (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) = 0 := by
      intro x
      by_cases hx : x.1 = 0
      · simp [hx]
      · simp only [if_neg hx]
        simpa [w] using congrArg (fun z : ℂ => z *
          (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
            heckeWeights K t v w * (w x.1) ^ 2) : ℂ))
          (hkFEIdealRayClassPointWeight_eq_zero_of_class_ne ψ C I
            x.2 hx J hJ hRay hne)
    have hfun : (fun x : hkPointSubtype I =>
        if x.1 = 0 then 0 else
          w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x.1 *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) *
            (Real.exp (-Real.pi * ∑ w : InfinitePlace K,
              heckeWeights K t v w * (w x.1) ^ 2) : ℂ)) = fun _ => 0 := by
      funext x
      exact hterm x
    rw [hfun]
    simp
  have hzero' : ∀ t : ℝ, ∀ v : logSpace K,
      hkFEIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
        (heckeWeights K t v) = 0 := by
    intro t v
    simpa [hkFEIdealWeightTheta, w] using hzero t v
  unfold hkFEIdealWeightNormalizedG hkFEIdealWeightG
  simp_rw [hzero']
  simp

noncomputable def hkFEWeightedZeroAverage {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (I : NumberFieldFractionalIdealGroup K) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * (hkPointWeight ψ I 0 : ℂ) * (unitBoxVol K : ℂ)

theorem hkFEWeightedG_eq_zero_add_components [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (I : NumberFieldFractionalIdealGroup K) {t : ℝ} (ht : 0 < t)
    (hInt : ∀ C : RayClassGroup m, IntegrableOn
      (fun v : logSpace K => hkFEIdealWeightTheta
        (hkFEIdealRayClassPointWeight ψ C) I (heckeWeights K t v))
      (ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ))) :
    hkWeightedG ψ I t = hkFEWeightedZeroAverage ψ I +
      ∑ C : RayClassGroup m,
        hkFEIdealWeightG (hkFEIdealRayClassPointWeight ψ C) I t := by
  classical
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  have hB : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  have hInt' : ∀ C : RayClassGroup m, IntegrableOn
      (fun v : logSpace K => hkIdealWeightTheta
        (hkFEIdealRayClassPointWeight ψ C) I (heckeWeights K t v)) B := by
    intro C
    simpa [hkFEIdealWeightTheta] using hInt C
  have hvol : volume.real B = unitBoxVol K := by
    rw [DedekindResidue.unitBoxVol]
    rfl
  have hconstInt : Integrable (fun _ : logSpace K => (hkPointWeight ψ I 0 : ℂ))
      (volume.restrict B) :=
    integrableOn_const (C := (hkPointWeight ψ I 0 : ℂ)) (ne_top_of_lt hBfin)
  have hsumInt : Integrable (fun v : logSpace K =>
      ∑ C : RayClassGroup m,
        hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
          (heckeWeights K t v)) (volume.restrict B) :=
    integrable_finsetSum Finset.univ (fun C hC => hInt' C)
  have hconstIntegral :
      (∫ v in B, (hkPointWeight ψ I 0 : ℂ)) =
        (hkPointWeight ψ I 0 : ℂ) * (unitBoxVol K : ℂ) := by
    rw [setIntegral_const]
    change ((volume.real B : ℝ) : ℂ) * (hkPointWeight ψ I 0 : ℂ) = _
    rw [hvol]
    ring_nf
  have hsplitIntegral :
      (∫ v in B, hkWeightedTheta ψ I (heckeWeights K t v)) =
        (hkPointWeight ψ I 0 : ℂ) * (unitBoxVol K : ℂ) +
          ∑ C : RayClassGroup m,
            ∫ v in B, hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
              (heckeWeights K t v) := by
    calc
      _ = ∫ v in B, (hkPointWeight ψ I 0 : ℂ) +
          ∑ C : RayClassGroup m,
            hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
              (heckeWeights K t v) := by
            apply setIntegral_congr_fun hB
            intro v hv
            exact hkFEWeightedTheta_eq_zero_add_components ψ I ht v
      _ = (∫ v in B, (hkPointWeight ψ I 0 : ℂ)) +
          ∫ v in B, ∑ C : RayClassGroup m,
            hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
              (heckeWeights K t v) := by
            exact integral_add hconstInt hsumInt
      _ = _ := by
        rw [hconstIntegral]
        have hfin :
            (∫ v in B, ∑ C : RayClassGroup m,
              hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
                (heckeWeights K t v)) =
              ∑ C : RayClassGroup m,
                ∫ v in B, hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
                  (heckeWeights K t v) := by
          change (∫ v, ∑ C : RayClassGroup m,
              hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
                (heckeWeights K t v) ∂volume.restrict B) =
            ∑ C : RayClassGroup m,
              ∫ v, hkIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) I
                (heckeWeights K t v) ∂volume.restrict B
          rw [integral_finsetSum (μ := volume.restrict B) Finset.univ
            (fun C hC => hInt' C)]
        rw [hfin]
  unfold hkWeightedG hkFEIdealWeightG
  rw [hsplitIntegral, mul_add, Finset.mul_sum]
  dsimp [hkFEWeightedZeroAverage]
  simp [B]
  rw [← mul_assoc]
  rfl

private theorem hkFE_allRayPrime [IsTotallyComplex K] {m : RayClassModulus K}
    (hm : m.finitePart = 0) (I : NumberFieldFractionalIdealGroup K) :
    I ∈ rayClassPrimeToIdeals m := by
  change ∀ v ∈ m.finitePart.support, FractionalIdeal.count K v (I : _ ) = 0
  simp [hm]

private noncomputable def hkFEAllIdealRayHom [IsTotallyComplex K]
    (m : RayClassModulus K) (hm : m.finitePart = 0) :
    NumberFieldFractionalIdealGroup K →* RayClassGroup m := by
  let f : NumberFieldFractionalIdealGroup K →* rayClassPrimeToIdeals m :=
    MonoidHom.codRestrict (MonoidHom.id _) (rayClassPrimeToIdeals m) (hkFE_allRayPrime hm)
  exact (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)).comp f

private theorem hkFEClassPrincipal_le_allIdealRayKer [IsTotallyComplex K]
    {m : RayClassModulus K} (hm : m.finitePart = 0) :
    (ClassGroup.mk K).ker ≤ (hkFEAllIdealRayHom m hm).ker := by
  intro I hI
  have hmk : ClassGroup.mk K (1 : NumberFieldFractionalIdealGroup K) = ClassGroup.mk K I := by
    simpa using hI.symm
  obtain ⟨a, ha⟩ := (classGroup_mk_eq_mk_iff (K := K)).mp hmk
  have hIprin : toPrincipalIdeal (𝓞 K) K a = I := by simpa using ha
  have hcong : IsRayCongruent m a := by
    simp [ClassFieldTheory.IsRayCongruent, hm,
      rayClassModulus_infinitePart_eq_empty (K := K) m]
  let p : rayClassPrimeToIdeals m := ⟨I, hkFE_allRayPrime hm I⟩
  have hmem : p ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m p).mpr ⟨a, hcong, hIprin⟩
  change hkFEAllIdealRayHom m hm I = 1
  change (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m))
    (⟨I, hkFE_allRayPrime hm I⟩ : rayClassPrimeToIdeals m) = 1
  exact (QuotientGroup.eq_one_iff
    (N := rayPrincipalIdealSubgroupInPrimeTo m)
    (⟨I, hkFE_allRayPrime hm I⟩ : rayClassPrimeToIdeals m)).mpr hmem

private noncomputable def hkFEClassToRayHom [IsTotallyComplex K]
    (m : RayClassModulus K) (hm : m.finitePart = 0) :
    ClassGroup (𝓞 K) →* RayClassGroup m := by
  let f := hkFEAllIdealRayHom m hm
  let lift := QuotientGroup.lift (ClassGroup.mk K).ker f
    (hkFEClassPrincipal_le_allIdealRayKer hm)
  have hsurj : Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := by
    intro E
    exact ⟨classRep K E, mk_classRep K E⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective (ClassGroup.mk K) hsurj
  exact lift.comp e.symm.toMonoidHom

private theorem hkFEClassToRayHom_surjective [IsTotallyComplex K]
    (m : RayClassModulus K) (hm : m.finitePart = 0) :
    Function.Surjective (hkFEClassToRayHom m hm) := by
  classical
  intro q
  let N := rayPrincipalIdealSubgroupInPrimeTo m
  obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective N q
  let I : NumberFieldFractionalIdealGroup K := p
  refine ⟨ClassGroup.mk K I, ?_⟩
  let f := hkFEAllIdealRayHom m hm
  have hsurj : Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := by
    intro E
    exact ⟨classRep K E, mk_classRep K E⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective (ClassGroup.mk K) hsurj
  have he : e.symm (ClassGroup.mk K I) =
      QuotientGroup.mk' (ClassGroup.mk K).ker I := by
    apply e.injective
    simp [e, QuotientGroup.quotientKerEquivOfSurjective]
    exact hsurj.hasRightInverse.choose_spec _
  have hfI : f I = q := by
    change QuotientGroup.mk' N
      (⟨I, hkFE_allRayPrime hm I⟩ : rayClassPrimeToIdeals m) = q
    rw [show (⟨I, hkFE_allRayPrime hm I⟩ : rayClassPrimeToIdeals m) = p by
      apply Subtype.ext
      rfl]
    exact hp
  change (QuotientGroup.lift (ClassGroup.mk K).ker f
      (hkFEClassPrincipal_le_allIdealRayKer hm))
        (e.symm (ClassGroup.mk K I)) = q
  let lift := QuotientGroup.lift (ClassGroup.mk K).ker f
    (hkFEClassPrincipal_le_allIdealRayKer hm)
  change lift (e.symm (ClassGroup.mk K I)) = q
  calc
    lift (e.symm (ClassGroup.mk K I)) = lift (QuotientGroup.mk' (ClassGroup.mk K).ker I) :=
      congrArg lift he
    _ = f I := QuotientGroup.lift_mk' (N := (ClassGroup.mk K).ker) (φ := f)
      (hkFEClassPrincipal_le_allIdealRayKer hm) I
    _ = q := hfI

private theorem hkFEClassToRayHom_mk [IsTotallyComplex K]
    (m : RayClassModulus K) (hm : m.finitePart = 0)
    (I : NumberFieldFractionalIdealGroup K) :
    hkFEClassToRayHom m hm (ClassGroup.mk K I) = hkFEAllIdealRayHom m hm I := by
  classical
  let f := hkFEAllIdealRayHom m hm
  have hsurj : Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := by
    intro E
    exact ⟨classRep K E, mk_classRep K E⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective (ClassGroup.mk K) hsurj
  have he : e.symm (ClassGroup.mk K I) =
      QuotientGroup.mk' (ClassGroup.mk K).ker I := by
    apply e.injective
    simp [e, QuotientGroup.quotientKerEquivOfSurjective]
    exact hsurj.hasRightInverse.choose_spec _
  let lift := QuotientGroup.lift (ClassGroup.mk K).ker f
    (hkFEClassPrincipal_le_allIdealRayKer hm)
  change lift (e.symm (ClassGroup.mk K I)) = f I
  rw [he]
  exact QuotientGroup.lift_mk' (N := (ClassGroup.mk K).ker) (φ := f)
    (hkFEClassPrincipal_le_allIdealRayKer hm) I

theorem hkFEWeightedZeroAverage_sum_eq_zero_of_finitePart_zero [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1)
    (hm : m.finitePart = 0) :
    ∑ E : ClassGroup (𝓞 K), hkFEWeightedZeroAverage ψ (classRep K E) = 0 := by
  classical
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  letI : Fintype (RayClassGroup m) := Fintype.ofFinite _
  let χ := hkFEClassToRayHom m hm
  let ψinv : RayClassGroup m →* ℂˣ := ψ⁻¹
  have hψinv : ψinv ≠ 1 := by
    intro h
    apply hψ
    calc
      ψ = (ψ⁻¹)⁻¹ := (inv_inv ψ).symm
      _ = (1 : RayClassGroup m →* ℂˣ)⁻¹ := congrArg Inv.inv h
      _ = 1 := by ext C; simp
  have hsurj := hkFEClassToRayHom_surjective m hm
  have horth := sum_comp_char_eq_zero_of_surjective χ hsurj ψinv hψinv
  have hχClass (E : ClassGroup (𝓞 K)) :
      χ E = hkFEAllIdealRayHom m hm (classRep K E) := by
    calc
      χ E = χ (ClassGroup.mk K (classRep K E)) := by rw [mk_classRep]
      _ = hkFEAllIdealRayHom m hm (classRep K E) :=
        hkFEClassToRayHom_mk m hm (classRep K E)
  have hfractionalChar (E : ClassGroup (𝓞 K)) :
      hkFractionalCharValue ψ (classRep K E)⁻¹ =
        (ψ (hkFEAllIdealRayHom m hm (classRep K E)⁻¹) : ℂ) := by
    simp [hkFractionalCharValue, hkFEAllIdealRayHom, hkFE_allRayPrime, hm]
  have hmapInv (E : ClassGroup (𝓞 K)) :
      hkFEAllIdealRayHom m hm (classRep K E)⁻¹ = (χ E)⁻¹ := by
    rw [map_inv, ← hχClass]
  have hzeroChar (E : ClassGroup (𝓞 K)) :
      hkPointWeight ψ (classRep K E) 0 = (ψinv (χ E) : ℂ) := by
    rw [hkPointWeight, if_pos rfl, if_pos hm, hfractionalChar, hmapInv]
    simp [ψinv]
  calc
    ∑ E : ClassGroup (𝓞 K), hkFEWeightedZeroAverage ψ (classRep K E) =
        ∑ E : ClassGroup (𝓞 K),
          (((torsionOrder K : ℂ)⁻¹ * (unitBoxVol K : ℂ)) * (ψinv (χ E) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro E hE
            simp_rw [hkFEWeightedZeroAverage, hzeroChar]
            ring
    _ = 0 := by
      rw [← Finset.mul_sum, horth]
      simp


end ArtinPrimitiveRoots.Hecke

end
