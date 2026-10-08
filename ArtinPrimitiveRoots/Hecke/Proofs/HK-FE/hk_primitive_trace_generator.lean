import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

private theorem hk_exists_integral_primeTo_principal_mul
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

/-- CRT generator of the inverse conductor times codifferent, with exact conductor-prime
orders recorded by coprimality of B. Guide: sol-thin-hk2/PROOFS.md:1261–1281.
Uses CRT in an invertible ideal after clearing one denominator; neither M nor the different
is assumed principal. -/
theorem hk_primitive_trace_generator [IsTotallyComplex K] (m : RayClassModulus K) :
    ∃ (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B),
      idealUnit B hB.1 = toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K := by
  obtain ⟨a, B, hB, hB_eq⟩ :=
    hk_exists_integral_primeTo_principal_mul m (hkModulusUnit m * hkDifferentUnit K)
  refine ⟨a, B, hB, ?_⟩
  rw [hB_eq, mul_assoc]

end ArtinPrimitiveRoots.Hecke
