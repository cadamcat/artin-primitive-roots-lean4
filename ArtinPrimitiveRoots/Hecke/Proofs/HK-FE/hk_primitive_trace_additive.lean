import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_generator
import ArtinPrimitiveRoots.Hecke.Theta.RayArithmetic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.DedekindDomain.Different

set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

private lemma fourierChar_rat_eq_one_of_mem_range {q : ℚ} (hq : q ∈ (algebraMap ℤ ℚ).range) :
    (Real.fourierChar ((q : ℝ)) : ℂ) = 1 := by
  obtain ⟨n, rfl⟩ := hq
  have hqR : ((algebraMap ℤ ℚ n : ℚ) : ℝ) = (n : ℝ) := by simp
  rw [hqR, Real.fourierChar_apply']
  have h1 : Circle.exp (2 * Real.pi * (n : ℝ)) = 1 := Circle.exp_two_pi_mul_int n
  rw [h1]
  rfl

private lemma fourierChar_rat_mem_range_of_eq_one {q : ℚ}
    (hq : (Real.fourierChar ((q : ℝ)) : ℂ) = 1) :
    q ∈ (algebraMap ℤ ℚ).range := by
  have hcirc : (Real.fourierChar (q : ℝ) : Circle) = 1 := Subtype.ext hq
  rw [Real.fourierChar_apply', Circle.exp_eq_one] at hcirc
  obtain ⟨n, hn⟩ := hcirc
  have hpi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hmul : 2 * Real.pi * (q : ℝ) = 2 * Real.pi * (n : ℝ) := by
    calc
      2 * Real.pi * (q : ℝ) = (n : ℝ) * (2 * Real.pi) := hn
      _ = 2 * Real.pi * (n : ℝ) := mul_comm _ _
  have hq_eq_n : (q : ℝ) = (n : ℝ) := mul_left_cancel₀ hpi hmul
  have hqQ : q = (n : ℚ) := by exact_mod_cast hq_eq_n
  exact ⟨n, hqQ.symm ▸ rfl⟩

private lemma dual_one_eq_inv_different :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  have h := coeIdeal_differentIdeal (A := ℤ) (B := 𝓞 K) (K := ℚ) (L := K)
  rw [h, inv_inv]

private lemma mem_dual_one_iff (x : K) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ y : 𝓞 K, Algebra.trace ℚ K (x * (y : K)) ∈ (algebraMap ℤ ℚ).range := by
  rw [FractionalIdeal.mem_dual one_ne_zero]
  constructor
  · intro h y
    have hy : (algebraMap (𝓞 K) K y) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨y, rfl⟩
    have htr := h (algebraMap (𝓞 K) K y) hy
    rw [Algebra.traceForm_apply] at htr
    exact htr
  · intro h z hz
    obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
    rw [Algebra.traceForm_apply]
    exact h y

private lemma coe_idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((idealUnit I hI : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
      (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

private lemma coe_hkModulusUnit (m : RayClassModulus K) :
    ((hkModulusUnit m : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
      (modulusIdeal m : FractionalIdeal (𝓞 K)⁰ K) := rfl

private lemma coe_hkDifferentUnit :
    ((hkDifferentUnit K : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := rfl

private lemma coe_toPrincipalIdeal' (a : Kˣ) :
    ((toPrincipalIdeal (𝓞 K) K a : NumberFieldFractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
  exact coe_toPrincipalIdeal a

private lemma fractionalIdeal_eq (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K) :
    (B : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) *
        (modulusIdeal m : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := congrArg (fun u : NumberFieldFractionalIdealGroup K => (u : FractionalIdeal (𝓞 K)⁰ K)) hB_eq
  simp only [Units.val_mul, coe_idealUnit, coe_toPrincipalIdeal', coe_hkModulusUnit, coe_hkDifferentUnit] at h
  exact h

private lemma trace_mem_range_of_mem_modulus (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K)
    {x : 𝓞 K} (hx : x ∈ modulusIdeal m) :
    (Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) ∈ (algebraMap ℤ ℚ).range := by
  let F_B : FractionalIdeal (𝓞 K)⁰ K := B
  let F_a : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
  let F_m : FractionalIdeal (𝓞 K)⁰ K := modulusIdeal m
  let F_d : FractionalIdeal (𝓞 K)⁰ K := differentIdeal ℤ (𝓞 K)
  have heq : F_B = F_a * F_m * F_d := fractionalIdeal_eq m a B hB hB_eq
  have hd_ne : F_d ≠ 0 := by
    apply FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have h_mul_inv : F_B * F_d⁻¹ = F_a * F_m := by
    rw [heq, mul_assoc, mul_inv_cancel₀ hd_ne, mul_one]
  have h_le_inv : F_a * F_m ≤ F_d⁻¹ := by
    rw [← h_mul_inv]
    have hBle : F_B ≤ 1 := FractionalIdeal.coeIdeal_le_one
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hx1 : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := hBle hx
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx1
    have hy' : (algebraMap (𝓞 K) K c) * y = c • y := by simp [Algebra.smul_def]
    rw [hy']
    exact Submodule.smul_mem _ c hy
  have hx_mem_Fm : (x : K) ∈ F_m := by
    exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨x, hx, rfl⟩
  have ha_mem_Fa : (a : K) ∈ F_a := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (a : K)
  have hax_mem : (a : K) * (x : K) ∈ F_a * F_m := by
    change (a : K) * (x : K) ∈ ((F_a * F_m : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
    rw [FractionalIdeal.coe_mul]
    exact Submodule.mul_mem_mul ha_mem_Fa hx_mem_Fm
  have hax_in_dual : (a : K) * (x : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [dual_one_eq_inv_different]
    exact h_le_inv hax_mem
  rw [mem_dual_one_iff] at hax_in_dual
  have h1 : Algebra.trace ℚ K (((a : K) * (x : K)) * ((1 : 𝓞 K) : K)) ∈ (algebraMap ℤ ℚ).range :=
    hax_in_dual 1
  have hone : ((1 : 𝓞 K) : K) = 1 := rfl
  rw [hone, mul_one] at h1
  exact h1

private def trace_val (a : Kˣ) (x : 𝓞 K) : ℂ :=
  Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ)

private lemma trace_val_add (a : Kˣ) (x y : 𝓞 K) :
    trace_val a (x + y) = trace_val a x * trace_val a y := by
  dsimp [trace_val]
  have hlin : (a : K) * ((x + y : 𝓞 K) : K) = (a : K) * (x : K) + (a : K) * (y : K) := by
    simp [mul_add]
  rw [hlin, LinearMap.map_add, Rat.cast_add]
  have hcirc : (Real.fourierChar (((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ) +
      ((Algebra.trace ℚ K ((a : K) * (y : K)) : ℚ) : ℝ) ) : Circle) =
      (Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ)) *
      (Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (y : K)) : ℚ) : ℝ)) := by
    exact AddChar.map_add_eq_mul' Real.fourierChar _ _
  exact congrArg Subtype.val hcirc

private lemma trace_val_zero (a : Kˣ) : trace_val a 0 = 1 := by
  dsimp [trace_val]
  have hz : (a : K) * ((0 : 𝓞 K) : K) = 0 := by simp
  rw [hz, LinearMap.map_zero, Rat.cast_zero]
  have hcirc : (Real.fourierChar (0 : ℝ) : Circle) = 1 := AddChar.map_zero_eq_one' Real.fourierChar
  exact congrArg Subtype.val hcirc

private lemma trace_val_sub_mem (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K)
    {x y : 𝓞 K} (hxy : x - y ∈ modulusIdeal m) :
    trace_val a x = trace_val a y := by
  have hdecomp : x = (x - y) + y := by ring
  have hxy_val : trace_val a (x - y) = 1 := by
    have hrange := trace_mem_range_of_mem_modulus m a B hB hB_eq hxy
    exact fourierChar_rat_eq_one_of_mem_range hrange
  have hstep : trace_val a x = trace_val a (x - y) * trace_val a y := by
    conv_lhs => rw [hdecomp]
    exact trace_val_add a (x - y) y
  rw [hstep, hxy_val, one_mul]

private def traceChar (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K) :
    AddChar (HKResidueRing m) ℂ where
  toFun q := Quotient.liftOn' q (trace_val a)
    (fun x y h => trace_val_sub_mem m a B hB hB_eq ((Submodule.quotientRel_def (modulusIdeal m)).mp h))
  map_zero_eq_one' := by
    have hz : (0 : HKResidueRing m) = Ideal.Quotient.mk (modulusIdeal m) 0 := rfl
    change Quotient.liftOn' (0 : HKResidueRing m) (trace_val a) _ = 1
    rw [hz]
    exact trace_val_zero a
  map_add_eq_mul' q1 q2 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q1
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q2
    have hxy : Ideal.Quotient.mk (modulusIdeal m) x + Ideal.Quotient.mk (modulusIdeal m) y =
        Ideal.Quotient.mk (modulusIdeal m) (x + y) := (map_add (Ideal.Quotient.mk (modulusIdeal m)) x y).symm
    change Quotient.liftOn' (Ideal.Quotient.mk (modulusIdeal m) x + Ideal.Quotient.mk (modulusIdeal m) y) (trace_val a) _ =
      Quotient.liftOn' (Ideal.Quotient.mk (modulusIdeal m) x) (trace_val a) _ *
      Quotient.liftOn' (Ideal.Quotient.mk (modulusIdeal m) y) (trace_val a) _
    rw [hxy]
    exact trace_val_add a x y

private lemma traceChar_apply (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K)
    (x : 𝓞 K) :
    traceChar m a B hB hB_eq (Ideal.Quotient.mk (modulusIdeal m) x) =
      Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ) := rfl

private lemma traceChar_isPrimitive (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K) :
    (traceChar m a B hB hB_eq).IsPrimitive := by
  intro r hr_ne hr_shift
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hab_dual : (a : K) * (b : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [mem_dual_one_iff]
    intro x
    have hshift_apply := congrFun (congrArg DFunLike.coe hr_shift) (Ideal.Quotient.mk (modulusIdeal m) x)
    rw [AddChar.mulShift_apply, AddChar.one_apply] at hshift_apply
    have hprod_mk : (Ideal.Quotient.mk (modulusIdeal m) b) * (Ideal.Quotient.mk (modulusIdeal m) x) =
        Ideal.Quotient.mk (modulusIdeal m) (b * x) := by
      exact (map_mul (Ideal.Quotient.mk (modulusIdeal m)) b x).symm
    rw [hprod_mk, traceChar_apply] at hshift_apply
    have hlin : (a : K) * ((b * x : 𝓞 K) : K) = ((a : K) * (b : K)) * (x : K) := by
      simp [mul_assoc]
    have hshift_apply' : (Real.fourierChar ((Algebra.trace ℚ K (((a : K) * (b : K)) * (x : K)) : ℚ) : ℝ) : ℂ) = 1 := by
      rw [← hlin]
      exact hshift_apply
    exact fourierChar_rat_mem_range_of_eq_one hshift_apply'
  have hab_inv : (a : K) * (b : K) ∈ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← dual_one_eq_inv_different]
    exact hab_dual
  let F_B : FractionalIdeal (𝓞 K)⁰ K := B
  let F_a : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
  let F_m : FractionalIdeal (𝓞 K)⁰ K := modulusIdeal m
  let F_d : FractionalIdeal (𝓞 K)⁰ K := differentIdeal ℤ (𝓞 K)
  have heq : F_B = F_a * F_m * F_d := fractionalIdeal_eq m a B hB hB_eq
  have hd_ne : F_d ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have ha_ne : F_a ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]
    exact a.ne_zero
  have hb_mem : ∀ v ∈ B, b * v ∈ modulusIdeal m := by
    intro v hv
    have hv_mem : (v : K) ∈ F_B := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨v, hv, rfl⟩
    have hprod : ((a : K) * (b : K)) * (v : K) ∈ F_d⁻¹ * F_B := by
      change ((a : K) * (b : K)) * (v : K) ∈ ((F_d⁻¹ * F_B : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [FractionalIdeal.coe_mul]
      exact Submodule.mul_mem_mul hab_inv hv_mem
    have hFd_cancel : F_d⁻¹ * F_B = F_a * F_m := by
      rw [heq, mul_comm (F_a * F_m) F_d, ← mul_assoc, inv_mul_cancel₀ hd_ne, one_mul]
    rw [hFd_cancel] at hprod
    have hassoc : ((a : K) * (b : K)) * (v : K) = (a : K) * ((b * v : 𝓞 K) : K) := by
      have hbv : ((b * v : 𝓞 K) : K) = (b : K) * (v : K) := rfl
      rw [hbv, mul_assoc]
    rw [hassoc] at hprod
    have ha_inv_mem : (a⁻¹ : K) ∈ F_a⁻¹ := by
      rw [FractionalIdeal.spanSingleton_inv]
      exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (a⁻¹ : K)
    have hprod2 : (a⁻¹ : K) * ((a : K) * ((b * v : 𝓞 K) : K)) ∈ F_a⁻¹ * (F_a * F_m) := by
      change (a⁻¹ : K) * ((a : K) * ((b * v : 𝓞 K) : K)) ∈ ((F_a⁻¹ * (F_a * F_m) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [FractionalIdeal.coe_mul]
      exact Submodule.mul_mem_mul ha_inv_mem hprod
    have hFa_cancel : F_a⁻¹ * (F_a * F_m) = F_m := by
      rw [← mul_assoc, inv_mul_cancel₀ ha_ne, one_mul]
    rw [hFa_cancel] at hprod2
    have hcancel_a : (a⁻¹ : K) * ((a : K) * ((b * v : 𝓞 K) : K)) = ((b * v : 𝓞 K) : K) := by
      rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero a), one_mul]
    rw [hcancel_a] at hprod2
    obtain ⟨bv', hbv', heq_bv⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hprod2
    have hEq : bv' = b * v := FaithfulSMul.algebraMap_injective (𝓞 K) K heq_bv
    simpa [hEq] using hbv'
  have h_prod_le : Ideal.span {b} * B ≤ modulusIdeal m := by
    rw [Ideal.mul_le]
    intro u hu v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hbv := hb_mem v hv
    rw [smul_eq_mul, mul_assoc]
    exact Ideal.mul_mem_left (modulusIdeal m) c hbv
  have hB_sup : B ⊔ modulusIdeal m = ⊤ := (isCoprimeTo_iff_sup m B).mp hB |>.2
  have h_span_le : Ideal.span {b} ≤ modulusIdeal m := by
    have htop : Ideal.span {b} = Ideal.span {b} * ⊤ := by simp
    rw [htop, ← hB_sup, Ideal.mul_sup]
    exact sup_le h_prod_le Ideal.mul_le_right
  have hb_in_mod : b ∈ modulusIdeal m := by
    have hb_self : b ∈ Ideal.span {b} := Ideal.mem_span_singleton_self b
    exact h_span_le hb_self
  have hr_zero : Ideal.Quotient.mk (modulusIdeal m) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb_in_mod
  exact hr_ne hr_zero

/-- The exact-order trace generator descends to a primitive additive character.
Uses hk_primitive_trace_generator, mem_traceDual and the
Fourier-character integral kernel; the annihilator is precisely M. -/
theorem hk_primitive_trace_additive [IsTotallyComplex K] (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K) :
    ∃ β : AddChar (HKResidueRing m) ℂ,
      (∀ x : 𝓞 K, β (Ideal.Quotient.mk (modulusIdeal m) x) =
        Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ)) ∧
      β.IsPrimitive := by
  refine ⟨traceChar m a B hB hB_eq, ?_, traceChar_isPrimitive m a B hB hB_eq⟩
  intro x
  exact traceChar_apply m a B hB hB_eq x

end ArtinPrimitiveRoots.Hecke
