import ArtinPrimitiveRoots.Hecke.Theta.RayFEPair

/-!
The ideal reindexing for ray-class Mellin agreement. Multiplication by an integral prime-to
representative identifies its inverse ray class with ray-principal ideals divisible by it.
This is the ray version of AINTLIB's `CompletedZeta/MellinAgreement.lean` principalDvdEquiv
(Chris Birkbeck, Apache-2.0).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField nonZeroDivisors ENNReal NNReal

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

private theorem rayMellin_idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem rayMellin_coprime_mul {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) : IsCoprimeTo m (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  rw [rayMellin_idealUnit_mul I J hI.1 hJ.1]
  exact (rayClassPrimeToIdeals m).mul_mem hI.2 hJ.2

private theorem rayMellin_rayClass_mul {m : RayClassModulus K} {I J : Ideal (𝓞 K)}
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m (I * J) (rayMellin_coprime_mul hI hJ) =
      rayClass m I hI * rayClass m J hJ := by
  change QuotientGroup.mk (⟨idealUnit (I * J) _, _⟩ : rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨idealUnit I _, _⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨idealUnit J _, _⟩ : rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (rayMellin_idealUnit_mul I J hI.1 hJ.1 (mul_ne_zero hI.1 hJ.1))

/-- An ideal in the inverse ray class is equivalent to a ray-principal multiple of J. -/
def rayPrincipalDvdEquiv (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hJ : IsCoprimeTo m (J : Ideal (𝓞 K))) :
    {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
      rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hJ)⁻¹} ≃
    {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
      ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1} := by
  classical
  refine Equiv.ofBijective (fun b => ⟨b.1 * J, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨hb, hclass⟩ := b.2
    refine ⟨⟨(b.1 : Ideal (𝓞 K)), ?_⟩, rayMellin_coprime_mul hb hJ, ?_⟩
    · change (b.1 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) =
        (J : Ideal (𝓞 K)) * (b.1 : Ideal (𝓞 K))
      exact mul_comm _ _
    · change rayClass m ((b.1 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) _ = 1
      rw [rayMellin_rayClass_mul hb hJ, hclass, inv_mul_cancel]
  · intro b c h
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val h)
  · rintro ⟨P, ⟨B, hB⟩, hP, hclassP⟩
    have hBne : B ≠ ⊥ := by
      intro h
      have hz : (P : Ideal (𝓞 K)) = ⊥ := by rw [hB, h, Ideal.mul_bot]
      exact hP.1 hz
    let b : (Ideal (𝓞 K))⁰ := ⟨B, mem_nonZeroDivisors_of_ne_zero hBne⟩
    have hprod : b * J = P := by
      apply Subtype.ext
      change B * (J : Ideal (𝓞 K)) = (P : Ideal (𝓞 K))
      rw [hB, mul_comm]
    have hunit : idealUnit B hBne * idealUnit (J : Ideal (𝓞 K)) hJ.1 =
        idealUnit (P : Ideal (𝓞 K)) hP.1 := by
      rw [← rayMellin_idealUnit_mul B (J : Ideal (𝓞 K)) hBne hJ.1
        (mul_ne_zero hBne hJ.1)]
      simpa using congrArg (fun x : (Ideal (𝓞 K))⁰ =>
        idealUnit (x : Ideal (𝓞 K)) (mem_nonZeroDivisors_iff_ne_zero.mp x.2)) hprod
    have hb : IsCoprimeTo m B := by
      refine ⟨hBne, ?_⟩
      have hmem := (rayClassPrimeToIdeals m).mul_mem hP.2
        ((rayClassPrimeToIdeals m).inv_mem hJ.2)
      have heq : idealUnit (P : Ideal (𝓞 K)) hP.1 *
          (idealUnit (J : Ideal (𝓞 K)) hJ.1)⁻¹ = idealUnit B hBne := by
        rw [← hunit, mul_inv_cancel_right]
      rwa [heq] at hmem
    refine ⟨⟨b, hb, ?_⟩, Subtype.ext hprod⟩
    apply (eq_inv_iff_mul_eq_one).mpr
    rw [← rayMellin_rayClass_mul hb hJ]
    have heq : (b : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) = (P : Ideal (𝓞 K)) :=
      congrArg (fun x : (Ideal (𝓞 K))⁰ => (x : Ideal (𝓞 K))) hprod
    have heq' : B * (J : Ideal (𝓞 K)) = (P : Ideal (𝓞 K)) := heq
    change rayClass m (B * (J : Ideal (𝓞 K))) _ = 1
    simpa only [heq'] using hclassP

private theorem rayMellin_idealUnit_span (a : 𝓞 K) (ha : a ≠ 0) :
    idealUnit (Ideal.span {a}) (mt Ideal.span_singleton_eq_bot.mp ha) =
      toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) := by
  apply Units.ext
  change (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

/-- The nonzero ray-kernel points generate precisely the prime-to principal ideals of ray class 1. -/
theorem rayKernelWeight_eq_one_iff_rayClass_span [IsTotallyComplex K]
    (m : RayClassModulus K) (a : 𝓞 K) (ha : a ≠ 0) :
    rayKernelWeight m (algebraMap (𝓞 K) K a) = 1 ↔
      ∃ hP : IsCoprimeTo m (Ideal.span {a}), rayClass m (Ideal.span {a}) hP = 1 := by
  classical
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha
  have hweight : rayKernelWeight m (algebraMap (𝓞 K) K a) = 1 ↔
      idealUnit (Ideal.span {a}) (mt Ideal.span_singleton_eq_bot.mp ha) ∈
        rayPrincipalIdealSubgroup m := by
    rw [rayMellin_idealUnit_span a ha]
    simp [rayKernelWeight, haK]
  constructor
  · intro h
    have hres : ∃ u : (𝓞 K)ˣ,
        Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
          Ideal.Quotient.mk (modulusIdeal m) a := by
      have hr := rayKernelWeight_integral_residue m a
      rw [h] at hr
      split_ifs at hr with hu
      · exact hu
      · norm_num at hr
    obtain ⟨u, hu⟩ := hres
    have hdiff : (u : 𝓞 K) - a ∈ modulusIdeal m :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := modulusIdeal m) _ _).mp hu
    have hsup : Ideal.span {a} ⊔ modulusIdeal m = ⊤ := by
      apply Ideal.eq_top_of_isUnit_mem _ _ u.isUnit
      have haMem : a ∈ Ideal.span {a} := Ideal.subset_span (Set.mem_singleton a)
      have huMem : ((u : 𝓞 K) - a) + a ∈ Ideal.span {a} ⊔ modulusIdeal m :=
        Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left haMem)
      simpa only [sub_add_cancel] using huMem
    have hP : IsCoprimeTo m (Ideal.span {a}) :=
      (isCoprimeTo_iff_sup m _).mpr ⟨mt Ideal.span_singleton_eq_bot.mp ha, hsup⟩
    refine ⟨hP, ?_⟩
    exact (QuotientGroup.eq_one_iff
      (N := rayPrincipalIdealSubgroupInPrimeTo m)
      (⟨idealUnit (Ideal.span {a}) hP.1, hP.2⟩ : rayClassPrimeToIdeals m)).mpr
      (hweight.mp h)
  · rintro ⟨hP, hclass⟩
    apply hweight.mpr
    exact (QuotientGroup.eq_one_iff
      (N := rayPrincipalIdealSubgroupInPrimeTo m)
      (⟨idealUnit (Ideal.span {a}) hP.1, hP.2⟩ : rayClassPrimeToIdeals m)).mp hclass

/-- The ray-principal class consists of principal ideals. -/
theorem isPrincipal_of_rayClass_eq_one (m : RayClassModulus K)
    (P : Ideal (𝓞 K)) (hP : IsCoprimeTo m P) (hclass : rayClass m P hP = 1) :
    Submodule.IsPrincipal P := by
  let p : rayClassPrimeToIdeals m := ⟨idealUnit P hP.1, hP.2⟩
  have hmem : p ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (QuotientGroup.eq_one_iff (N := rayPrincipalIdealSubgroupInPrimeTo m) p).mp hclass
  obtain ⟨x, _, hx⟩ := (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m p).mp hmem
  have hfrac : (toPrincipalIdeal (𝓞 K) K x : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
    congrArg (fun u : NumberFieldFractionalIdealGroup K =>
      (u : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) hx
  have hsub : ((P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).IsPrincipal := by
    rw [← hfrac, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨(x : K), rfl⟩⟩
  exact (IsFractionRing.coeSubmodule_isPrincipal (R := 𝓞 K) (K := K) (I := P)).mp hsub

/-- Norm weights under the ray-principal multiple reindexing. -/
theorem tsum_rayPrincipal_dvd_norm_rpow (m : RayClassModulus K)
    (J : (Ideal (𝓞 K))⁰) (hJ : IsCoprimeTo m (J : Ideal (𝓞 K))) (s : ℝ) :
    (∑' P : {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
      ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1},
      ENNReal.ofReal ((Ideal.absNorm (P.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))) =
    ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
      ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
        rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hJ)⁻¹},
        ENNReal.ofReal ((Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  classical
  rw [← Equiv.tsum_eq (rayPrincipalDvdEquiv m J hJ)
    (fun P => ENNReal.ofReal ((Ideal.absNorm (P.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  change ENNReal.ofReal
    ((Ideal.absNorm ((b.1 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) : ℝ) ^ (-s)) = _
  rw [map_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_comm]

/-- Squared norm weights, as used by the half-weight Gaussian Mellin transform. -/
theorem tsum_rayPrincipal_dvd_norm_sq_rpow (m : RayClassModulus K)
    (J : (Ideal (𝓞 K))⁰) (hJ : IsCoprimeTo m (J : Ideal (𝓞 K))) (σ : ℝ) :
    (∑' P : {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
      ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1},
      ENNReal.ofReal (((Ideal.absNorm (P.1 : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ))) =
    ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ)) *
      ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
        rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hJ)⁻¹},
        ENNReal.ofReal (((Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ)) := by
  have hpow : ∀ N : ℕ, ((N : ℝ) ^ 2) ^ (-σ) = (N : ℝ) ^ (-(2 * σ)) := by
    intro N
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hpow]
  exact tsum_rayPrincipal_dvd_norm_rpow m J hJ (2 * σ)

end ArtinPrimitiveRoots.Hecke

end
