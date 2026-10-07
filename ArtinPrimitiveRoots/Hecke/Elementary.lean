import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Analytic
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.PrimeFibers
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Hecke L-function package: elementary statements (Re s > 1)

Frozen interface (§2 of the design, and (D3)). Design: `research/design/A2-HeckeAPI.lean` and `A2-DESIGN.md` (Opus A2 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open scoped NumberField ComplexOrder nonZeroDivisors
open NumberField IsDedekindDomain
open Filter Asymptotics
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory
open _root_.ArtinPrimitiveRoots.Hecke.EulerProduct

variable {K : Type*} [Field K] [NumberField K]

private theorem idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIJ : I * J ≠ ⊥) :
    idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem isCoprimeTo_mul_iff (m : RayClassModulus K) (I J : Ideal (𝓞 K)) :
    IsCoprimeTo m (I * J) ↔ IsCoprimeTo m I ∧ IsCoprimeTo m J := by
  classical
  by_cases hI : I = ⊥
  · subst I
    simp [IsCoprimeTo]
  by_cases hJ : J = ⊥
  · subst J
    simp [IsCoprimeTo]
  constructor
  · rintro ⟨hIJ0, hIJ⟩
    constructor
    · refine ⟨hI, ?_⟩
      intro v hv
      have hsum :
          FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
            FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        have hx := hIJ v hv
        have hval := congrArg (fun u : NumberFieldFractionalIdealGroup K =>
          (u : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
          (idealUnit_mul I J hI hJ hIJ0)
        rw [hval, Units.val_mul,
          FractionalIdeal.count_mul K v (Units.ne_zero (idealUnit I hI))
            (Units.ne_zero (idealUnit J hJ))] at hx
        simpa [idealUnit] using hx
      have hI' := FractionalIdeal.count_coe_nonneg K v I
      have hJ' := FractionalIdeal.count_coe_nonneg K v J
      have : FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        omega
      simpa [idealUnit] using this
    · refine ⟨hJ, ?_⟩
      intro v hv
      have hsum :
          FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
            FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        have hx := hIJ v hv
        have hval := congrArg (fun u : NumberFieldFractionalIdealGroup K =>
          (u : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
          (idealUnit_mul I J hI hJ hIJ0)
        rw [hval, Units.val_mul,
          FractionalIdeal.count_mul K v (Units.ne_zero (idealUnit I hI))
            (Units.ne_zero (idealUnit J hJ))] at hx
        simpa [idealUnit] using hx
      have hI' := FractionalIdeal.count_coe_nonneg K v I
      have hJ' := FractionalIdeal.count_coe_nonneg K v J
      have : FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        omega
      simpa [idealUnit] using this
  · rintro ⟨⟨_, hI'⟩, ⟨_, hJ'⟩⟩
    refine ⟨mul_ne_zero hI hJ, ?_⟩
    have hmul : idealUnit I hI * idealUnit J hJ ∈ rayClassPrimeToIdeals m :=
      (rayClassPrimeToIdeals m).mul_mem hI' hJ'
    simpa [idealUnit_mul I J hI hJ (mul_ne_zero hI hJ)] using hmul

private theorem rayClass_mul {m : RayClassModulus K} (I J : Ideal (𝓞 K))
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m (I * J) ((isCoprimeTo_mul_iff m I J).2 ⟨hI, hJ⟩) =
      rayClass m I hI * rayClass m J hJ := by
  rcases hI with ⟨hI0, hI'⟩
  rcases hJ with ⟨hJ0, hJ'⟩
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI0 hJ0
  have hIJ' : idealUnit (I * J) hIJ0 ∈ rayClassPrimeToIdeals m := by
    simpa [idealUnit_mul I J hI0 hJ0 hIJ0] using
      (rayClassPrimeToIdeals m).mul_mem hI' hJ'
  change QuotientGroup.mk (⟨idealUnit (I * J) hIJ0, hIJ'⟩ : rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨idealUnit I hI0, hI'⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨idealUnit J hJ0, hJ'⟩ : rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (idealUnit_mul I J hI0 hJ0 hIJ0)

private def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

private theorem idealCount_sum_eq (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} =
      ∑ k ∈ Finset.Icc 0 n, idealCount (K := K) k := by
  classical
  unfold idealCount
  rw [← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k)]
  simp [Set.coe_eq_subtype]

/-! ## §2 Elementary statements (Re s > 1)

The generic Euler-product and prime-fiber arguments are factored under `Elementary/EulerProduct/`.  Sizes in `A2-DESIGN.md` §2. -/

/-- `charValue` is completely multiplicative (zero extension included).
Consumers: A2 `def:zf-detector` (`L·D_U = Σ α_U η`), A2 `po:H-product`; B `sp:upstairs-factor`. -/
theorem charValue_mul {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (I J : Ideal (𝓞 K)) : charValue η (I * J) = charValue η I * charValue η J := by
  classical
  by_cases hprod : IsCoprimeTo m (I * J)
  · rcases (isCoprimeTo_mul_iff m I J).1 hprod with ⟨hI, hJ⟩
    simp [charValue, hprod, hI, hJ, rayClass_mul, map_mul]
  · have hpair : ¬ (IsCoprimeTo m I ∧ IsCoprimeTo m J) := by
      intro h
      exact hprod ((isCoprimeTo_mul_iff m I J).2 h)
    rcases not_and_or.mp hpair with hI | hJ
    · simp [charValue, hprod, hI]
    · simp [charValue, hprod, hJ]

/-- Characters of the finite group `Cl_𝔪` have unimodular values.
Consumers: every bound below; A2 `lem:conductor-sieve`. -/
theorem norm_charValue_le_one {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (I : Ideal (𝓞 K)) : ‖charValue η I‖ ≤ 1 := by
  classical
  by_cases h : IsCoprimeTo m I
  · simp only [charValue, dite_eq_left h]
    have hpow : (η (rayClass m I h)) ^ Nat.card (RayClassGroup m) = 1 := by
      rw [← map_pow, pow_card_eq_one']
      simp
    have hpow' := congrArg (fun z : ℂˣ => (z : ℂ)) hpow
    have hnorm := Complex.norm_eq_one_of_pow_eq_one (by simpa using hpow')
      (Nat.card_pos.ne' : Nat.card (RayClassGroup m) ≠ 0)
    simpa using hnorm.le
  · simp [charValue, h]

private theorem coeff_norm_le_idealCount {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (n : ℕ) :
    ‖coeff η n‖ ≤ (idealCount (K := K) n : ℝ) := by
  classical
  unfold coeff
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  let S := F.toFinset
  have hcard : S.card = idealCount (K := K) n := by
    dsimp [S, idealCount]
    exact (Nat.card_eq_card_finite_toFinset F).symm
  calc
    ‖∑ I ∈ S, charValue η I‖ ≤ ∑ I ∈ S, ‖charValue η I‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ S, (1 : ℝ) := Finset.sum_le_sum fun I hI ↦ norm_charValue_le_one η I
    _ = (idealCount (K := K) n : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard

/-- Absolute convergence for `Re s > 1`.  Consumers: all. -/
theorem LSeriesSummable_coeff {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (coeff η) s := by
  have hcountLim : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ)) atTop (𝓝 (dedekindZeta_residue K)) := by
    have h := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
    convert h using 1
    · funext n
      congr 1
      exact_mod_cast (Nat.card_congr
        (Equiv.subtypeEquivRight (fun _ ↦ by norm_cast)))
    · simp [dedekindZeta_residue]
  have hcountLim' : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 (dedekindZeta_residue K)) := by
    simpa only [Real.rpow_one] using hcountLim
  have hcount :
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1) hcountLim'
  have hpartial :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖coeff η k‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    apply (isBigO_of_le (l := atTop) ?_).trans hcount
    intro n
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k hk => norm_nonneg (coeff η k)),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      ∑ k ∈ Finset.Icc 1 n, ‖coeff η k‖ ≤
          ∑ k ∈ Finset.Icc 1 n, (idealCount (K := K) k : ℝ) :=
        Finset.sum_le_sum fun k hk => coeff_norm_le_idealCount η k
      _ ≤ ∑ k ∈ Finset.Icc 0 n, (idealCount (K := K) k : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
          (fun k _ _ ↦ by positivity)
      _ = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) := by
        exact_mod_cast (idealCount_sum_eq (K := K) n).symm
  exact LSeriesSummable_of_sum_norm_bigO hpartial zero_le_one hs

private theorem charValue_one_modulus (I : Ideal (𝓞 K)) :
    charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) I =
      if I = ⊥ then 0 else 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [charValue, IsCoprimeTo, hI]
  · have hcop : IsCoprimeTo (⟨0, ∅⟩ : RayClassModulus K) I := by
      change ∃ h' : I ≠ ⊥, idealUnit I h' ∈
        rayClassPrimeToIdeals (⟨0, ∅⟩ : RayClassModulus K)
      refine ⟨hI, ?_⟩
      change ∀ v, v ∈ (0 : HeightOneSpectrum (𝓞 K) →₀ ℕ).support → _
      intro v hv
      simp at hv
    simp only [charValue, dite_eq_left hcop]
    simp [hI]

private theorem coeff_one_modulus_eq_idealCount {n : ℕ} (hn : n ≠ 0) :
    coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  classical
  unfold coeff
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  calc
    ∑ I ∈ F.toFinset,
        charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) I =
      ∑ I ∈ F.toFinset, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [charValue_one_modulus]
        have hIn : Ideal.absNorm I = n := F.mem_toFinset.mp hI
        have hI0 : I ≠ ⊥ := by
          intro h
          subst I
          simp at hIn
          exact hn hIn.symm
        simp [hI0]
    _ = (F.toFinset.card : ℂ) := by simp
    _ = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset F).symm

private theorem idealCount_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealCount (K := K) n : ℂ)) s := by
  apply (LSeriesSummable_congr s
    (f := fun n ↦ (idealCount (K := K) n : ℂ))
    (g := coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ))
    (fun {n} hn ↦ (coeff_one_modulus_eq_idealCount (K := K) hn).symm)).mpr
  exact LSeriesSummable_coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) hs

private theorem idealCount_norm_tsum_eq_dedekindZeta_re {σ : ℝ} (hσ : 1 < σ) :
    (dedekindZeta K (σ : ℂ)).re =
      ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n‖ := by
  have hs := idealCount_LSeriesSummable (K := K) (s := (σ : ℂ)) (by simpa using hσ)
  have hnonneg (n : ℕ) :
      0 ≤ LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n := by
    exact LSeries.term_nonneg (by positivity) σ
  calc
    (dedekindZeta K (σ : ℂ)).re =
        (∑' n, LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n).re := rfl
    _ = ∑' n, (LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n).re :=
      Complex.re_tsum hs
    _ = ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n‖ := by
      apply tsum_congr
      intro n
      exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hnonneg n))

private theorem norm_LSeriesRay_upper {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeriesRay η s‖ ≤ (dedekindZeta K s.re).re := by
  have hη := (LSeriesSummable_coeff η hs).norm
  have hζ := (idealCount_LSeriesSummable (K := K) (s := s.re) hs).norm
  have hterm (n : ℕ) :
      ‖LSeries.term (coeff η) s n‖ ≤
        ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (s.re : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · simp only [Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (coeff_norm_le_idealCount η n) (by positivity)
  calc
    ‖LSeriesRay η s‖ = ‖∑' n, LSeries.term (coeff η) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (coeff η) s n‖ := norm_tsum_le_tsum_norm hη
    _ ≤ ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (s.re : ℂ) n‖ :=
      hη.tsum_le_tsum hterm hζ
    _ = (dedekindZeta K s.re).re :=
      (idealCount_norm_tsum_eq_dedekindZeta_re (K := K) hs).symm

private theorem charValue_one {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) :
    charValue η (1 : Ideal (𝓞 K)) = 1 := by
  classical
  have hcop : IsCoprimeTo m (1 : Ideal (𝓞 K)) := by
    refine ⟨by simp [Ideal.one_eq_top], ?_⟩
    change ∀ v, v ∈ m.finitePart.support → _
    intro v hv
    simpa [idealUnit] using (FractionalIdeal.count_one K v)
  have hrep :
      (⟨idealUnit (1 : Ideal (𝓞 K)) hcop.1, hcop.2⟩ : rayClassPrimeToIdeals m) = 1 := by
    apply Subtype.ext
    change idealUnit (1 : Ideal (𝓞 K)) hcop.1 = 1
    apply Units.ext
    change ((1 : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1
    exact FractionalIdeal.coeIdeal_eq_one.mpr rfl
  have hclass : rayClass m (1 : Ideal (𝓞 K)) hcop = 1 := by
    change QuotientGroup.mk
      (⟨idealUnit (1 : Ideal (𝓞 K)) hcop.1, hcop.2⟩ : rayClassPrimeToIdeals m) = 1
    rw [hrep]
    simp
  simp only [charValue, dif_pos hcop, hclass]
  simp

private theorem charValue_zero_of_mem_support {m : RayClassModulus K}
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

private def charIdealWeight {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) :
    IdealArithmeticFunction K := fun I ↦ charValue η I

private theorem charIdealWeight_isMultiplicative {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) : (charIdealWeight η).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · exact charValue_one η
  · intro I J hIJ
    change charValue η ((I : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) = _
    exact charValue_mul η _ _

private theorem normCoeff_charIdealWeight {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (n : ℕ) :
    normCoeff K (charIdealWeight η) n = coeff η n := by
  classical
  rw [normCoeff_eq_sum_normFiber]
  by_cases hn : n = 0
  · subst n
    rw [normFiber_zero]
    unfold coeff
    let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) 0
    simp only [Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro I hI
    have hnorm : Ideal.absNorm I = 0 := by
      simpa only [Set.mem_setOf_eq] using F.mem_toFinset.mp hI
    have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
    subst I
    simp [charValue, IsCoprimeTo]
  · let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
    change (∑ I ∈ normFiber K n, charValue η I) =
      ∑ I ∈ F.toFinset, charValue η I
    refine Finset.sum_bij (fun I _ ↦ (I : Ideal (𝓞 K)) ) ?_ ?_ ?_ ?_
    · intro I hI
      exact F.mem_toFinset.mpr ((mem_normFiber K).mp hI)
    · intro I hI J hJ hEq
      exact Subtype.ext hEq
    · intro J hJ
      have hnorm : Ideal.absNorm J = n := by
        simpa only [Set.mem_setOf_eq] using F.mem_toFinset.mp hJ
      have hJ0 : J ≠ ⊥ := by
        intro hJbot
        subst J
        simp at hnorm
        exact hn hnorm.symm
      let I : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩
      refine ⟨I, (mem_normFiber K).mpr hnorm, rfl⟩
    · intro I hI
      rfl

private theorem normFiber_card_le_idealCount (n : ℕ) :
    (normFiber K n).card ≤ idealCount (K := K) n := by
  classical
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  have hcard : (normFiber K n).card ≤ F.toFinset.card := by
    refine Finset.card_le_card_of_injOn (s := normFiber K n) (t := F.toFinset)
      (fun I ↦ (I : Ideal (𝓞 K))) ?_ ?_
    · intro I hI
      exact F.mem_toFinset.mpr ((mem_normFiber K).mp hI)
    · intro I hI J hJ hEq
      exact Subtype.ext hEq
  unfold idealCount
  exact hcard.trans_eq (Nat.card_eq_card_finite_toFinset F).symm

private theorem norm_idealTerm_charIdealWeight_fiber_le
    {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re)
    (n : ℕ) :
    ∑ I ∈ normFiber K n, ‖idealTerm (charIdealWeight η) s I‖ ≤
      ‖LSeries.term (fun k ↦ (idealCount (K := K) k : ℂ)) (s.re : ℂ) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [normFiber_zero]
  calc
    ∑ I ∈ normFiber K n, ‖idealTerm (charIdealWeight η) s I‖ ≤
        ∑ I ∈ normFiber K n, (1 : ℝ) / (n : ℝ) ^ s.re := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_idealTerm, (mem_normFiber K).mp hI]
      exact div_le_div_of_nonneg_right (norm_charValue_le_one η I) (by positivity)
    _ = (↑(normFiber K n).card : ℝ) / (n : ℝ) ^ s.re := by
      rw [← Finset.sum_div]
      simp
    _ ≤ (↑(idealCount (K := K) n) : ℝ) / (n : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right (by exact_mod_cast normFiber_card_le_idealCount (K := K) n)
        (by positivity)
    _ = ‖LSeries.term (fun k ↦ (idealCount (K := K) k : ℂ)) (s.re : ℂ) n‖ := by
      rw [LSeries.norm_term_eq]
      simp [hn, Complex.norm_natCast]

private theorem summable_idealTerm_charIdealWeight
    {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm (charIdealWeight η) s) := by
  have hζ := (idealCount_LSeriesSummable (K := K) (s := s.re) hs).norm
  have hnorm : Summable fun I : (Ideal (𝓞 K))⁰ ↦
      ‖idealTerm (charIdealWeight η) s I‖ := by
    apply (summable_partition (f := fun I : (Ideal (𝓞 K))⁰ ↦
      ‖idealTerm (charIdealWeight η) s I‖) (fun _ ↦ norm_nonneg _)
      (s := fun n ↦ (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n})
      (fun I ↦ ⟨Ideal.absNorm (I : Ideal (𝓞 K)), by simp,
        fun n hn ↦ by simpa using hn.symm⟩)).2
    constructor
    · intro n
      let fiber : Set ((Ideal (𝓞 K))⁰) :=
        (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 K))⁰ |
          Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by ext I; simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber K n).fintype
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le
        (f := fun n ↦ ‖LSeries.term (fun k ↦ (idealCount (K := K) k : ℂ))
          (s.re : ℂ) n‖)
        (g := fun n ↦ ∑' I :
          (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
          ‖idealTerm (charIdealWeight η) s I‖) ?_ ?_ hζ
      · intro n
        exact tsum_nonneg fun I ↦ norm_nonneg _
      · intro n
        let fiber : Set ((Ideal (𝓞 K))⁰) :=
          (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}
        have hEq : fiber = {I : (Ideal (𝓞 K))⁰ |
            Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by ext I; simp [fiber]
        letI : Fintype fiber := (hEq ▸ finite_normFiber K n).fintype
        rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n)
          (fun I ↦ ‖idealTerm (charIdealWeight η) s I‖)]
        exact norm_idealTerm_charIdealWeight_fiber_le η hs n
  exact Summable.of_norm hnorm

private theorem charValue_pow {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (P : Ideal (𝓞 K)) (e : ℕ) : charValue η (P ^ e) = charValue η P ^ e := by
  induction e with
  | zero => simpa only [pow_zero] using charValue_one η
  | succ e ih => rw [pow_succ, charValue_mul, ih, pow_succ]

private theorem idealTerm_charIdealWeight_primePow {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    idealTerm (charIdealWeight η) s (P.primeIdealPow e) =
      (charValue η P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, charIdealWeight, P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    charValue_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]

private theorem charIdealWeight_primeRatio_lt_one {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : Summable (idealTerm (charIdealWeight η) s)) (P : HeightOneSpectrum (𝓞 K)) :
    ‖charValue η P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  have hinj : Function.Injective P.primeIdealPow := by
    intro a b hab
    apply Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    simpa only [P.absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) hab
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective hinj).congr fun e ↦
    idealTerm_charIdealWeight_primePow η P e s

private theorem eulerFactor_charIdealWeight {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : Summable (idealTerm (charIdealWeight η) s)) (P : HeightOneSpectrum (𝓞 K)) :
    eulerFactor (charIdealWeight η) P s =
      (1 - charValue η P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [eulerFactor_eq_tsum]
  rw [tsum_congr fun e ↦ idealTerm_charIdealWeight_primePow η P e s]
  exact tsum_geometric_of_norm_lt_one (charIdealWeight_primeRatio_lt_one η hs P)

private theorem LSeries_charIdealWeight {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (s : ℂ) :
    LSeries (normCoeff K (charIdealWeight η)) s = LSeriesRay η s := by
  change LSeries (normCoeff K (charIdealWeight η)) s = LSeries (coeff η) s
  congr 1
  funext n
  exact normCoeff_charIdealWeight η n

private def charPrimeRatio {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  charValue η P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s

private def charPrimeEulerTerm {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  charValue η P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)

private theorem charPrimeRatio_summable {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable (charPrimeRatio η s) := by
  have hsI := summable_idealTerm_charIdealWeight η hs
  have hinj : Function.Injective (fun P : HeightOneSpectrum (𝓞 K) => P.primeIdealPow 1) := by
    intro P Q h
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    simpa only [P.coe_primeIdealPow, Q.coe_primeIdealPow, pow_one] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ => (I : Ideal (𝓞 K)) ) h
  exact (hsI.comp_injective hinj).congr fun P ↦ by
    change idealTerm (charIdealWeight η) s (P.primeIdealPow 1) = _
    rw [idealTerm_charIdealWeight_primePow η P 1 s]
    simp [charPrimeRatio]

private theorem charPrimeDenom_tprod_ne_zero {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    tprod (fun P : HeightOneSpectrum (𝓞 K) => 1 - charPrimeEulerTerm η s P) ≠ 0 := by
  have hsum := charPrimeRatio_summable η hs
  have hsum' : Summable (charPrimeEulerTerm η s) := by
    exact hsum.congr fun P ↦ by
      simp [charPrimeEulerTerm, charPrimeRatio, Complex.cpow_neg, div_eq_mul_inv]
  have hnorm := (summable_norm_iff).2 hsum'
  refine tprod_one_add_ne_zero_of_summable (f := fun P : HeightOneSpectrum (𝓞 K) =>
    -charPrimeEulerTerm η s P) ?_ (by simpa using hnorm)
  intro P
  have hlt := charIdealWeight_primeRatio_lt_one η
    (summable_idealTerm_charIdealWeight η hs) P
  have heq : charPrimeEulerTerm η s P = charPrimeRatio η s P := by
    simp [charPrimeEulerTerm, charPrimeRatio, Complex.cpow_neg, div_eq_mul_inv]
  have hlt' : ‖charPrimeEulerTerm η s P‖ < 1 := by rw [heq]; exact hlt
  intro hzero
  have hzero' : 1 - charPrimeEulerTerm η s P = 0 := by
    simpa [sub_eq_add_neg] using hzero
  have hq : charPrimeEulerTerm η s P = 1 := (sub_eq_zero.mp hzero').symm
  rw [hq] at hlt'
  norm_num at hlt'

/-- Euler product, as a convergent product over the finite primes.
Consumers: A2 `def:zf-detector`, `zf:reciprocal-bound`; B `sp:upstairs-factor`,
`sp:quotient-factor`. -/
theorem LSeriesRay_eulerProduct {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - charValue η v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s) := by
  have hsum := summable_idealTerm_charIdealWeight η hs
  have hprod := hasProd_eulerFactor (charIdealWeight η) (charIdealWeight_isMultiplicative η) hsum
  have hfun :
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - charValue η v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) =
      fun v ↦ eulerFactor (charIdealWeight η) v s := by
    funext v
    rw [eulerFactor_charIdealWeight η hsum v]
    congr 1
    simp [Complex.cpow_neg, div_eq_mul_inv]
  rw [hfun, ← LSeries_charIdealWeight η s]
  exact hprod

private theorem LSeriesRay_eq_inv_charPrimeDenom {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesRay η s =
      (tprod (fun P : HeightOneSpectrum (𝓞 K) => 1 - charPrimeEulerTerm η s P))⁻¹ := by
  have hEuler := LSeriesRay_eulerProduct η hs
  have hsum := charPrimeRatio_summable η hs
  have hsum' : Summable (charPrimeEulerTerm η s) := by
    exact hsum.congr fun P ↦ by
      simp [charPrimeEulerTerm, charPrimeRatio, Complex.cpow_neg, div_eq_mul_inv]
  have hnorm := (summable_norm_iff).2 hsum'
  have h0 := charPrimeDenom_tprod_ne_zero η hs
  have hEuler' : HasProd (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charPrimeEulerTerm η s P)⁻¹) (LSeriesRay η s) := by
    simpa [charPrimeEulerTerm] using hEuler
  have hmul := multipliable_one_sub_of_summable hnorm
  have hA : tprod (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charPrimeEulerTerm η s P)⁻¹) = LSeriesRay η s := hEuler'.tprod_eq
  have hB : tprod (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charPrimeEulerTerm η s P)⁻¹) =
      (tprod (fun P : HeightOneSpectrum (𝓞 K) => 1 - charPrimeEulerTerm η s P))⁻¹ :=
    hmul.tprod_inv₀ h0
  exact hA.symm.trans hB

private noncomputable def trivialPrimeFactor (σ : ℝ)
    (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (1 - ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹

private def rayPrimeFactor {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (1 - charPrimeEulerTerm η s P)⁻¹

private theorem hasProd_le_of_nonneg {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf : HasProd f a) (hg : HasProd g b) (h0 : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ g i) : a ≤ b := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro S
  exact Finset.prod_le_prod₀ (fun i _ ↦ h0 i) (fun i _ ↦ hfg i)

private theorem trivialPrimeFactor_hasProd {σ : ℝ} (hσ : 1 < σ) :
    HasProd (trivialPrimeFactor (K := K) σ)
      (dedekindZeta K (σ : ℂ)) := by
  let η₀ : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ := 1
  have hEuler := LSeriesRay_eulerProduct (K := K) η₀ (s := (σ : ℂ)) (by simpa using hσ)
  have hL : LSeriesRay η₀ (σ : ℂ) = dedekindZeta K (σ : ℂ) := by
    change LSeries (coeff η₀) (σ : ℂ) =
      LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) (σ : ℂ)
    apply LSeries_congr
    intro n hn
    exact coeff_one_modulus_eq_idealCount (K := K) hn
  rw [hL] at hEuler
  have hfun : trivialPrimeFactor (K := K) σ = fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - charValue η₀ P.asIdeal *
        ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ := by
    funext P
    simp [trivialPrimeFactor, η₀, charValue_one_modulus, P.ne_bot]
  rw [hfun]
  exact hEuler

private theorem charPrimeEulerTerm_norm_le_trivialFactor {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    1 + ‖charPrimeEulerTerm η s P‖ ≤ ‖trivialPrimeFactor (K := K) s.re P‖ := by
  let x : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)
  have hn : 0 < Ideal.absNorm P.asIdeal := by
    exact Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm P)
  have hbase : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hx0 : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hxlt : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg hbase (by linarith [hs])
  have hnorma : ‖charPrimeEulerTerm η s P‖ ≤ x := by
    dsimp [x, charPrimeEulerTerm]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    simp
    calc
      ‖charValue η P.asIdeal‖ * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (norm_charValue_le_one η P.asIdeal) (by positivity)
      _ = _ := one_mul _
  have hcomplexPow :
      ((((Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)) : ℝ) : ℂ) =
        ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s.re : ℂ)) := by
    simpa using Complex.ofReal_cpow (by positivity : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ)) (-s.re)
  have hfactor : trivialPrimeFactor (K := K) s.re P = ((1 - x)⁻¹ : ℝ) := by
    rw [trivialPrimeFactor, ← hcomplexPow]
    dsimp [x]
    norm_cast
  have hfactorC : trivialPrimeFactor (K := K) s.re P = (1 - (x : ℂ))⁻¹ := by
    rw [trivialPrimeFactor, ← hcomplexPow]
  have hlocalnorm : ‖trivialPrimeFactor (K := K) s.re P‖ = (1 - x)⁻¹ := by
    rw [hfactorC, norm_inv]
    have hsub : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
      push_cast
      rfl
    have hnormreal : ‖((1 - x : ℝ) : ℂ)‖ = 1 - x := by
      have h := @RCLike.norm_ofReal ℂ inferInstance (1 - x)
      rw [abs_of_nonneg (sub_nonneg.mpr hxlt.le)] at h
      exact h
    rw [hsub, hnormreal]
  have hratio : 1 + x ≤ (1 - x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1 - x)]
    nlinarith [sq_nonneg x]
  rw [hlocalnorm]
  linarith [hnorma, hratio]

private theorem dedekindZeta_real_positive {σ : ℝ} (hσ : 1 < σ) :
    0 < dedekindZeta K (σ : ℂ) := by
  let σ₀ : ℝ := (1 + σ) / 2
  have hσ₀ : 1 < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀σ : σ₀ < σ := by dsimp [σ₀]; linarith
  have hsum := idealCount_LSeriesSummable (K := K) (s := (σ₀ : ℂ)) (by simpa using hσ₀)
  have habs : LSeries.abscissaOfAbsConv (fun n ↦ (idealCount (K := K) n : ℂ)) < σ := by
    have hle := hsum.abscissaOfAbsConv_le
    have hσ₀σE : (σ₀ : EReal) < (σ : EReal) := by exact_mod_cast hσ₀σ
    exact hle.trans_lt hσ₀σE
  have hcoeff₀ : ∀ n, 0 ≤ (idealCount (K := K) n : ℂ) := fun _ ↦ by positivity
  have hcoeff₁ : 0 < (idealCount (K := K) 1 : ℂ) := by
    classical
    let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) 1
    letI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} := F
    letI : Nonempty {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} := ⟨⟨1, by simp⟩⟩
    change 0 < (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} : ℂ)
    exact_mod_cast Nat.card_pos
  simpa [dedekindZeta, idealCount] using
    (LSeries.positive hcoeff₀ hcoeff₁ habs)

/-- Size bounds on `Re s > 1`: `‖L‖ ≤ ζ_K(σ)` and `‖L⁻¹‖ ≤ ζ_K(σ)`, `σ = Re s`.
Consumers: A2 `zf:height-decay`, `zf:small-rows`, `zf:far-rows`, `zf:f-bounds`. -/
theorem norm_LSeriesRay_le {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LSeriesRay η s‖ ≤ (dedekindZeta K s.re).re ∧
      LSeriesRay η s ≠ 0 ∧ ‖(LSeriesRay η s)⁻¹‖ ≤ (dedekindZeta K s.re).re := by
  refine ⟨norm_LSeriesRay_upper η hs, ?_⟩
  constructor
  · rw [LSeriesRay_eq_inv_charPrimeDenom η hs]
    exact inv_ne_zero (charPrimeDenom_tprod_ne_zero η hs)
  · have hsum := charPrimeRatio_summable η hs
    have hsum' : Summable (charPrimeEulerTerm η s) := by
      exact hsum.congr fun P ↦ by
        simp [charPrimeEulerTerm, charPrimeRatio, Complex.cpow_neg, div_eq_mul_inv]
    have hnorm := (summable_norm_iff).2 hsum'
    have hden : Multipliable (fun P : HeightOneSpectrum (𝓞 K) =>
        1 - charPrimeEulerTerm η s P) := multipliable_one_sub_of_summable hnorm
    have hplus : Multipliable (fun P : HeightOneSpectrum (𝓞 K) =>
        1 + ‖charPrimeEulerTerm η s P‖) := Real.multipliable_one_add_of_summable hnorm
    have hζ := trivialPrimeFactor_hasProd (K := K) (σ := s.re) hs
    have hζmult := hζ.multipliable
    have htriangle (P : HeightOneSpectrum (𝓞 K)) :
        ‖1 - charPrimeEulerTerm η s P‖ ≤ 1 + ‖charPrimeEulerTerm η s P‖ := by
      simpa using norm_sub_le (1 : ℂ) (charPrimeEulerTerm η s P)
    have hlocal (P : HeightOneSpectrum (𝓞 K)) :
        1 + ‖charPrimeEulerTerm η s P‖ ≤ ‖trivialPrimeFactor (K := K) s.re P‖ :=
      charPrimeEulerTerm_norm_le_trivialFactor η hs P
    have hprod₁ :
        tprod (fun P : HeightOneSpectrum (𝓞 K) => ‖1 - charPrimeEulerTerm η s P‖) ≤
          tprod (fun P : HeightOneSpectrum (𝓞 K) => 1 + ‖charPrimeEulerTerm η s P‖) :=
      hasProd_le_of_nonneg hden.norm.hasProd hplus.hasProd
        (fun _ ↦ norm_nonneg _) htriangle
    have hprod₂ :
        tprod (fun P : HeightOneSpectrum (𝓞 K) => 1 + ‖charPrimeEulerTerm η s P‖) ≤
          tprod (fun P : HeightOneSpectrum (𝓞 K) => ‖trivialPrimeFactor (K := K) s.re P‖) :=
      hasProd_le_of_nonneg hplus.hasProd hζmult.norm.hasProd
        (fun _ ↦ by positivity) hlocal
    have hζnorm :
        tprod (fun P : HeightOneSpectrum (𝓞 K) => ‖trivialPrimeFactor (K := K) s.re P‖) =
          ‖dedekindZeta K (s.re : ℂ)‖ := by
      calc
        _ = ‖tprod (trivialPrimeFactor (K := K) s.re)‖ := hζmult.norm_tprod.symm
        _ = ‖dedekindZeta K (s.re : ℂ)‖ := congrArg norm hζ.tprod_eq
    have hζpos := dedekindZeta_real_positive (K := K) hs
    have hζpos' := Complex.pos_iff.mp hζpos
    have hζnorm_re : ‖dedekindZeta K (s.re : ℂ)‖ = (dedekindZeta K (s.re : ℂ)).re := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hζpos'.2.symm]
      norm_num
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hζpos'.1.le]
    calc
      ‖(LSeriesRay η s)⁻¹‖ =
          ‖tprod (fun P : HeightOneSpectrum (𝓞 K) =>
            1 - charPrimeEulerTerm η s P)‖ := by
              rw [LSeriesRay_eq_inv_charPrimeDenom η hs, inv_inv]
      _ = tprod (fun P : HeightOneSpectrum (𝓞 K) =>
          ‖1 - charPrimeEulerTerm η s P‖) := hden.norm_tprod
      _ ≤ tprod (fun P : HeightOneSpectrum (𝓞 K) =>
          1 + ‖charPrimeEulerTerm η s P‖) := hprod₁
      _ ≤ tprod (fun P : HeightOneSpectrum (𝓞 K) =>
          ‖trivialPrimeFactor (K := K) s.re P‖) := hprod₂
      _ = ‖dedekindZeta K (s.re : ℂ)‖ := hζnorm
      _ = (dedekindZeta K s.re).re := by simpa using hζnorm_re

/-- **Change of modulus.**  If `η` (mod `𝔪`) and `η'` (mod `𝔫`) agree on every prime coprime
to `𝔪`, the two L-series differ by the finitely many Euler factors at the primes of `𝔪`:
`L^{(𝔪)}(s,η) = L^{(𝔫)}(s,η') · ∏_{v ∈ supp 𝔪} (1 - η'(𝔭_v) N𝔭_v^{-s})`.
Consumers: B `thm:hecke-zero-free` note ("choice of modulus harmless"), `sp:upstairs-factor`;
A2 passage between `L^S` (paper) and `L^{(𝔪)}` in `zf:convexity`, `prop:zero-density`. -/
theorem LSeriesRay_change_modulus {m n : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (η' : RayClassGroup n →* ℂˣ)
    (hagree : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      charValue η v.asIdeal = charValue η' v.asIdeal)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesRay η s = LSeriesRay η' s * ∏ v ∈ m.finitePart.support,
      (1 - charValue η' v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
  classical
  let S := m.finitePart.support
  let corr : HeightOneSpectrum (𝓞 K) → ℂ := fun P ↦
    if P ∈ S then 1 - charPrimeEulerTerm η' s P else 1
  have hη : HasProd (rayPrimeFactor η s) (LSeriesRay η s) := by
    change HasProd (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charValue η P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s)
    exact LSeriesRay_eulerProduct η hs
  have hη' : HasProd (rayPrimeFactor η' s) (LSeriesRay η' s) := by
    change HasProd (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charValue η' P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η' s)
    exact LSeriesRay_eulerProduct η' hs
  have hcorrMult : Multipliable corr := by
    apply multipliable_of_hasFiniteMulSupport
    change (Function.mulSupport corr).Finite
    apply S.finite_toSet.subset
    intro P hmem
    by_contra hnot
    have hnotFin : P ∉ S := by simpa using hnot
    change corr P ≠ 1 at hmem
    apply hmem
    simp [corr, hnotFin]
  have hcorrTprod : tprod corr = ∏ P ∈ S, (1 - charPrimeEulerTerm η' s P) := by
    rw [tprod_eq_prod (s := S) (by intro P hP; simp [corr, hP])]
    apply Finset.prod_congr rfl
    intro P hP
    simp [corr, hP]
  have hcorr : HasProd corr (∏ P ∈ S, (1 - charPrimeEulerTerm η' s P)) := by
    rw [← hcorrTprod]
    exact hcorrMult.hasProd
  have hpoint (P : HeightOneSpectrum (𝓞 K)) :
      rayPrimeFactor η s P = rayPrimeFactor η' s P * corr P := by
    by_cases hP : P ∈ S
    · have hzero := charValue_zero_of_mem_support η (by simpa [S] using hP)
      have hlt := charIdealWeight_primeRatio_lt_one η'
        (summable_idealTerm_charIdealWeight η' hs) P
      have heq : charPrimeEulerTerm η' s P = charPrimeRatio η' s P := by
        simp [charPrimeEulerTerm, charPrimeRatio, Complex.cpow_neg, div_eq_mul_inv]
      have hlt' : ‖charPrimeEulerTerm η' s P‖ < 1 := by rw [heq]; exact hlt
      have hden : 1 - charPrimeEulerTerm η' s P ≠ 0 := by
        intro hz
        have hval : charPrimeEulerTerm η' s P = 1 := (sub_eq_zero.mp hz).symm
        rw [hval] at hlt'
        norm_num at hlt'
      have hcancel : (1 - charPrimeEulerTerm η' s P)⁻¹ *
          (1 - charPrimeEulerTerm η' s P) = 1 := inv_mul_cancel₀ hden
      simpa [rayPrimeFactor, charPrimeEulerTerm, corr, hP, hzero] using hcancel.symm
    · have hchar := hagree P (by simpa [S] using hP)
      simp [rayPrimeFactor, charPrimeEulerTerm, corr, hP, hchar]
  have hmul := hη'.mul hcorr
  calc
    LSeriesRay η s = tprod (rayPrimeFactor η s) := hη.tprod_eq.symm
    _ = tprod (fun P ↦ rayPrimeFactor η' s P * corr P) := by
      exact tprod_congr hpoint
    _ = LSeriesRay η' s * ∏ P ∈ S, (1 - charPrimeEulerTerm η' s P) := hmul.tprod_eq
    _ = LSeriesRay η' s * ∏ P ∈ m.finitePart.support,
        (1 - charValue η' P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      simp [S, charPrimeEulerTerm]

/-- Trivial modulus and trivial character give Mathlib's Dedekind zeta function.
Consumers: B `ext:dedekind-fe` (dictionary), A2 `zf:principal-row`. -/
theorem LSeriesRay_trivial_eq_dedekindZeta (s : ℂ) :
    LSeriesRay (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) s =
      dedekindZeta K s := by
  change LSeries (coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ)) s =
    LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s
  apply LSeries_congr
  intro n hn
  exact coeff_one_modulus_eq_idealCount (K := K) hn

private def dedekindPrimeFactor (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (1 - ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹

private theorem dedekindZeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (dedekindPrimeFactor (K := K) s) (dedekindZeta K s) := by
  let η₀ : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ := 1
  have hEuler := LSeriesRay_eulerProduct (K := K) η₀ hs
  rw [LSeriesRay_trivial_eq_dedekindZeta (K := K) s] at hEuler
  have hfun : dedekindPrimeFactor (K := K) s = fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - charValue η₀ P.asIdeal *
        ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext P
    simp [dedekindPrimeFactor, η₀, charValue_one_modulus, P.ne_bot]
  rw [hfun]
  exact hEuler

private theorem complex_norm_eq_re_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  have hp := Complex.pos_iff.mp hz
  rw [Complex.norm_eq_sqrt_sq_add_sq, hp.2.symm]
  have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hzero, add_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg hp.1.le]

private def riemannPrimeFactor (σ : ℝ) (p : Nat.Primes) : ℝ :=
  (1 - (p.val : ℝ) ^ (-σ))⁻¹

private def riemannPrimeLowerFactor (σ : ℝ) (p : Nat.Primes) : ℝ :=
  (1 + (p.val : ℝ) ^ (-σ))⁻¹

private theorem riemannPrimeFactor_hasProd {σ : ℝ} (hσ : 1 < σ) :
    HasProd (riemannPrimeFactor σ) (riemannZeta (σ : ℂ)).re := by
  have hEuler := riemannZeta_eulerProduct_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have hnorm := hEuler.norm
  have hfun : (fun p : Nat.Primes => ‖(1 - (p.val : ℂ) ^ (-(σ : ℂ)))⁻¹‖) =
      riemannPrimeFactor σ := by
    funext p
    let x : ℝ := (p.val : ℝ) ^ (-σ)
    have hpN : 0 < p.val := p.2.pos
    have hxlt : x < 1 := by
      dsimp [x]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
    have hpow : ((x : ℝ) : ℂ) = (p.val : ℂ) ^ (-(σ : ℂ)) := by
      simpa [x] using Complex.ofReal_cpow (by positivity : 0 ≤ (p.val : ℝ)) (-σ)
    have hfactor : (1 - (p.val : ℂ) ^ (-(σ : ℂ)))⁻¹ = (((1 - x)⁻¹ : ℝ) : ℂ) := by
      rw [← hpow]
      norm_cast
    have hnormfactor : ‖(((1 - x)⁻¹ : ℝ) : ℂ)‖ = (1 - x)⁻¹ := by
      have h := @RCLike.norm_ofReal ℂ inferInstance ((1 - x)⁻¹)
      rw [abs_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hxlt.le))] at h
      exact h
    rw [hfactor, hnormfactor]
    rfl
  rw [hfun] at hnorm
  rw [complex_norm_eq_re_of_pos (riemannZeta_pos_of_one_lt hσ)] at hnorm
  exact hnorm

private theorem primeIndex_absNorm_rpow_le (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ}
    (hσ : 1 < σ) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) ≤ ((primeIndex (K := K) P).val : ℝ) ^ (-σ) := by
  have hnat : (primeIndex (K := K) P).val ≤ Ideal.absNorm P.asIdeal := by
    rw [absNorm_eq_primeIndex_pow P]
    exact le_self_pow (primeIndex (K := K) P).2.one_le
      (Nat.ne_of_gt (P.asIdeal.inertiaDeg_pos ℤ))
  have hpPos : 0 < ((primeIndex (K := K) P).val : ℝ) := by
    exact_mod_cast (primeIndex (K := K) P).2.pos
  exact Real.rpow_le_rpow_of_nonpos hpPos (by exact_mod_cast hnat) (by linarith)

private theorem dedekindPrimeFactor_bounds {s : ℂ} (hs : 1 < s.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    (1 + (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re))⁻¹ ≤
        ‖dedekindPrimeFactor (K := K) s P‖ ∧
      ‖dedekindPrimeFactor (K := K) s P‖ ≤
        (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re))⁻¹ := by
  let r : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)
  let z : ℂ := ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)
  have hn : 0 < Ideal.absNorm P.asIdeal :=
    Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm P)
  have hbase : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hr0 : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg hbase (by linarith [hs])
  have hz : ‖z‖ = r := by
    dsimp [z, r]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hdenLower : 1 - r ≤ ‖1 - z‖ := by
    have htri : (1 : ℝ) ≤ ‖1 - z‖ + ‖z‖ := by
      calc
        1 = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 - z) + z‖ := by congr 1 <;> ring
        _ ≤ ‖1 - z‖ + ‖z‖ := norm_add_le _ _
    rw [hz] at htri
    linarith
  have hdenUpper : ‖1 - z‖ ≤ 1 + r := by
    simpa [hz] using norm_sub_le (1 : ℂ) z
  have hdenPos : 0 < ‖1 - z‖ := (sub_pos.mpr hrlt).trans_le hdenLower
  constructor
  · change (1 + r)⁻¹ ≤ ‖(1 - z)⁻¹‖
    calc
      (1 + r)⁻¹ ≤ ‖1 - z‖⁻¹ :=
        (inv_le_inv₀ (by linarith [hr0]) hdenPos).2 hdenUpper
      _ = ‖(1 - z)⁻¹‖ := (norm_inv _).symm
  · change ‖(1 - z)⁻¹‖ ≤ (1 - r)⁻¹
    calc
      ‖(1 - z)⁻¹‖ = ‖1 - z‖⁻¹ := norm_inv _
      _ ≤ (1 - r)⁻¹ :=
        (inv_le_inv₀ hdenPos (sub_pos.mpr hrlt)).2 hdenLower

private def rationalPrimeFiber (p : Nat.Primes) :=
  primeIndexFiber (K := K) p

private theorem finiteProd_lower_power {α : Type*} (S : Finset α) (q : ℝ) (f : α → ℝ)
    (d : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hcard : S.card ≤ d)
    (hpoint : ∀ a ∈ S, q ≤ f a) : q ^ d ≤ ∏ a ∈ S, f a := by
  calc
    q ^ d ≤ q ^ S.card := pow_le_pow_of_le_one hq0 hq1 hcard
    _ = ∏ a ∈ S, q := (Finset.prod_const q).symm
    _ ≤ ∏ a ∈ S, f a := Finset.prod_le_prod₀ (fun _ _ ↦ hq0) hpoint

private theorem finiteProd_upper_power {α : Type*} (S : Finset α) (q : ℝ) (f : α → ℝ)
    (d : ℕ) (hq1 : 1 ≤ q) (hcard : S.card ≤ d) (hnonneg : ∀ a ∈ S, 0 ≤ f a)
    (hpoint : ∀ a ∈ S, f a ≤ q) : ∏ a ∈ S, f a ≤ q ^ d := by
  calc
    ∏ a ∈ S, f a ≤ ∏ a ∈ S, q := Finset.prod_le_prod₀ hnonneg hpoint
    _ = q ^ S.card := Finset.prod_const q
    _ ≤ q ^ d := pow_le_pow_right₀ hq1 hcard

set_option maxHeartbeats 10000000 in
private theorem dedekindPrimeFactor_fiber_bounds {σ t : ℝ} (hσ : 1 < σ)
    (p : Nat.Primes) :
    (riemannPrimeLowerFactor σ p) ^ Module.finrank ℚ K ≤
        tprod (fun P : rationalPrimeFiber (K := K) p =>
          ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖) ∧
      tprod (fun P : rationalPrimeFiber (K := K) p =>
          ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖) ≤
        (riemannPrimeFactor σ p) ^ Module.finrank ℚ K := by
  classical
  letI : Fintype (rationalPrimeFiber (K := K) p) :=
    primeIndexFiberFintype (K := K) p
  have hcard : Fintype.card (rationalPrimeFiber (K := K) p) ≤ Module.finrank ℚ K := by
    exact card_primeIndexFiber_le_finrank (K := K) p
  have hpbase : 1 < (p.val : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : 0 < (p.val : ℝ) := by positivity
  let x : ℝ := (p.val : ℝ) ^ (-σ)
  have hx0 : 0 < x := by dsimp [x]; exact Real.rpow_pos_of_pos hp0 _
  have hxlt : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpbase (by linarith [hσ])
  have hqU : 1 ≤ riemannPrimeFactor σ p := by
    dsimp [riemannPrimeFactor]
    exact (one_le_inv₀ (sub_pos.mpr hxlt)).2 (by linarith)
  have hqL0 : 0 ≤ riemannPrimeLowerFactor σ p := by
    dsimp [riemannPrimeLowerFactor]
    positivity
  have hqL1 : riemannPrimeLowerFactor σ p ≤ 1 := by
    dsimp [riemannPrimeLowerFactor]
    exact (inv_le_one₀ (by positivity)).2 (by linarith)
  have hlocal (P : rationalPrimeFiber (K := K) p) :
      riemannPrimeLowerFactor σ p ≤
        ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ ∧
      ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ ≤
        riemannPrimeFactor σ p := by
    have hP : primeIndex (K := K) P.1 = p := by
      simpa [rationalPrimeFiber, primeIndexFiber] using P.2
    have hpower := primeIndex_absNorm_rpow_le (K := K) P.1 hσ
    rw [hP] at hpower
    have hb := dedekindPrimeFactor_bounds (K := K) (s := (σ + t * Complex.I))
      (by simpa using hσ) P.1
    have hsre : (σ + t * Complex.I).re = σ := by simp
    rw [hsre] at hb
    constructor
    · dsimp [riemannPrimeLowerFactor, x]
      calc
        (1 + ((p.val : ℝ) ^ (-σ)))⁻¹ ≤
            (1 + (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-σ))⁻¹ := by
              exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
        _ ≤ ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ := hb.1
    · dsimp [riemannPrimeFactor, x]
      calc
        ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ ≤
            (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-σ))⁻¹ := hb.2
        _ ≤ (1 - (p.val : ℝ) ^ (-σ))⁻¹ := by
          exact (inv_le_inv₀ (sub_pos.mpr (by
            exact Real.rpow_lt_one_of_one_lt_of_neg
              (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P.1)
              (by linarith [hσ]))) (sub_pos.mpr hxlt)).2 (by linarith)
  have hlocalLower : ∀ P : rationalPrimeFiber (K := K) p,
      riemannPrimeLowerFactor σ p ≤
        ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ := fun P => (hlocal P).1
  have hlocalUpper : ∀ P : rationalPrimeFiber (K := K) p,
      ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖ ≤
        riemannPrimeFactor σ p := fun P => (hlocal P).2
  have hcardFin :
      (Finset.univ : Finset (rationalPrimeFiber (K := K) p)).card ≤ Module.finrank ℚ K := by
    rw [Finset.card_univ]
    exact hcard
  have hprodLower :
      (riemannPrimeLowerFactor σ p) ^ Module.finrank ℚ K ≤
        tprod (fun P : rationalPrimeFiber (K := K) p =>
          ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖) := by
    rw [tprod_fintype]
    exact finiteProd_lower_power (Finset.univ : Finset (rationalPrimeFiber (K := K) p))
      (riemannPrimeLowerFactor σ p)
      (fun P => ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖)
      (Module.finrank ℚ K) hqL0 hqL1 hcardFin (fun P _ ↦ hlocalLower P)
  have hprodUpper :
      tprod (fun P : rationalPrimeFiber (K := K) p =>
          ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖) ≤
        (riemannPrimeFactor σ p) ^ Module.finrank ℚ K := by
    rw [tprod_fintype]
    exact finiteProd_upper_power (Finset.univ : Finset (rationalPrimeFiber (K := K) p))
      (riemannPrimeFactor σ p)
      (fun P => ‖dedekindPrimeFactor (K := K) (σ + t * Complex.I) P.1‖)
      (Module.finrank ℚ K) hqU hcardFin (fun _ _ ↦ by positivity)
      (fun P _ ↦ hlocalUpper P)
  constructor
  · exact hprodLower
  · exact hprodUpper


private noncomputable def primeIndexFiberFinset (p : Nat.Primes) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  letI : Fintype (rationalPrimeFiber (K := K) p) :=
    primeIndexFiberFintype (K := K) p
  exact Finset.univ.image fun P : rationalPrimeFiber (K := K) p => P.1

private theorem mem_primeIndexFiberFinset {p : Nat.Primes} {P : HeightOneSpectrum (𝓞 K)} :
    P ∈ primeIndexFiberFinset (K := K) p ↔ primeIndex (K := K) P = p := by
  classical
  letI : Fintype (rationalPrimeFiber (K := K) p) :=
    primeIndexFiberFintype (K := K) p
  unfold primeIndexFiberFinset
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨Q, hQ, hQP⟩
    have hQp : primeIndex (K := K) Q.1 = p := by
      simpa [rationalPrimeFiber, primeIndexFiber] using Q.2
    simpa [hQP] using hQp
  · intro hP
    have hQ : P ∈ rationalPrimeFiber (K := K) p := by
      simpa [rationalPrimeFiber, primeIndexFiber] using hP
    exact Finset.mem_image.mpr ⟨⟨P, hQ⟩, Finset.mem_univ _, rfl⟩

private noncomputable def primeIdealFinset (S : Finset Nat.Primes) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact S.biUnion (primeIndexFiberFinset (K := K))

private theorem primeIndexFiberFinset_pairwiseDisjoint (S : Finset Nat.Primes) :
    Set.PairwiseDisjoint (S : Set Nat.Primes) (primeIndexFiberFinset (K := K)) := by
  classical
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hpE := (mem_primeIndexFiberFinset (K := K)).mp hP
  have hqE := (mem_primeIndexFiberFinset (K := K)).mp hQ
  exact hpq (hpE.symm.trans hqE)

private theorem primeIdealFinset_tendsto :
    Tendsto (primeIdealFinset (K := K)) atTop atTop := by
  classical
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro S T hST
    unfold primeIdealFinset
    exact Finset.biUnion_subset_biUnion_of_subset_left
      (primeIndexFiberFinset (K := K)) hST
  · intro P
    refine ⟨{primeIndex (K := K) P}, ?_⟩
    unfold primeIdealFinset
    rw [Finset.mem_biUnion]
    exact ⟨primeIndex (K := K) P, Finset.mem_singleton_self _,
      (mem_primeIndexFiberFinset (K := K)).2 rfl⟩

private theorem primeIdealFinset_prod (S : Finset Nat.Primes)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    (∏ P ∈ primeIdealFinset (K := K) S, f P) =
      ∏ p ∈ S, ∏ P ∈ primeIndexFiberFinset (K := K) p, f P := by
  classical
  unfold primeIdealFinset
  exact Finset.prod_biUnion (f := f)
    (primeIndexFiberFinset_pairwiseDisjoint (K := K) S)

private theorem primeIndexFiber_prod_eq_tprod (p : Nat.Primes)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    (∏ P ∈ primeIndexFiberFinset (K := K) p, f P) =
      tprod (fun P : rationalPrimeFiber (K := K) p => f P.1) := by
  classical
  letI : Fintype (rationalPrimeFiber (K := K) p) :=
    primeIndexFiberFintype (K := K) p
  rw [tprod_fintype]
  unfold primeIndexFiberFinset
  exact Finset.prod_image (s := Finset.univ)
    (g := fun P : rationalPrimeFiber (K := K) p => P.1)
    (f := f) Subtype.val_injective.injOn

private theorem dedekindPrimeIdealPartial_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun S : Finset Nat.Primes =>
      ∏ P ∈ primeIdealFinset (K := K) S,
        ‖dedekindPrimeFactor (K := K) s P‖) atTop
      (𝓝 ‖dedekindZeta K s‖) := by
  have h := (dedekindZeta_eulerProduct (K := K) (s := s) hs).norm
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
    ∏ P ∈ T, ‖dedekindPrimeFactor (K := K) s P‖) atTop
      (𝓝 ‖dedekindZeta K s‖) at h
  exact h.comp (primeIdealFinset_tendsto (K := K))

set_option maxHeartbeats 10000000 in
private theorem dedekindZeta_norm_upper_bound {σ t : ℝ} (hσ : 1 < σ) :
    ‖dedekindZeta K ((σ : ℂ) + t * Complex.I)‖ ≤
      (riemannZeta σ).re ^ Module.finrank ℚ K := by
  classical
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hs : 1 < s.re := by simp [s, hσ]
  have hKnet := dedekindPrimeIdealPartial_tendsto (K := K) (s := s) hs
  have hζσ := riemannPrimeFactor_hasProd (σ := σ) hσ
  let d : ℕ := Module.finrank ℚ K
  have hζnet : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (riemannPrimeFactor σ p) ^ d) atTop
      (𝓝 ((riemannZeta (σ : ℂ)).re ^ d)) := by
    change HasProd (fun p : Nat.Primes => (riemannPrimeFactor σ p) ^ d)
      ((riemannZeta (σ : ℂ)).re ^ d)
    exact hζσ.pow d
  have hfiber (p : Nat.Primes) :
      ∏ P ∈ primeIndexFiberFinset (K := K) p,
        ‖dedekindPrimeFactor (K := K) s P‖ ≤ (riemannPrimeFactor σ p) ^ d := by
    calc
      ∏ P ∈ primeIndexFiberFinset (K := K) p,
          ‖dedekindPrimeFactor (K := K) s P‖ =
        tprod (fun P : rationalPrimeFiber (K := K) p =>
          ‖dedekindPrimeFactor (K := K) s P.1‖) :=
            primeIndexFiber_prod_eq_tprod (K := K) p _
      _ ≤ (riemannPrimeFactor σ p) ^ d := by
        simpa [d] using (dedekindPrimeFactor_fiber_bounds (K := K) hσ p).2
  have hpoint (S : Finset Nat.Primes) :
      (∏ P ∈ primeIdealFinset (K := K) S,
          ‖dedekindPrimeFactor (K := K) s P‖) ≤
        ∏ p ∈ S, (riemannPrimeFactor σ p) ^ d := by
    rw [primeIdealFinset_prod (K := K) S]
    apply Finset.prod_le_prod₀
    · intro p hp
      exact Finset.prod_nonneg fun P hP => norm_nonneg _
    · intro p hp
      exact hfiber p
  have h := le_of_tendsto_of_tendsto' hKnet hζnet hpoint
  simpa [s, d] using h

set_option maxHeartbeats 100000000 in
private theorem riemannPrimeLowerFactor_hasProd {σ : ℝ} (hσ : 1 < σ) (d : ℕ) :
    HasProd (fun p : Nat.Primes => (riemannPrimeLowerFactor σ p) ^ d)
      (((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ d) := by
  have hζσ := riemannPrimeFactor_hasProd (σ := σ) hσ
  have hζ2σ : HasProd (riemannPrimeFactor (2 * σ)) (riemannZeta (2 * σ)).re := by
    have hbase := riemannPrimeFactor_hasProd (σ := 2 * σ) (by linarith)
    have harg : ((2 * σ : ℝ) : ℂ) = (2 : ℂ) * (σ : ℂ) := by push_cast; ring
    rw [harg] at hbase
    exact hbase
  have hζ2Net : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, riemannPrimeFactor (2 * σ) p) atTop (𝓝 (riemannZeta (2 * σ)).re) := hζ2σ
  have hζσNet : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, riemannPrimeFactor σ p) atTop (𝓝 (riemannZeta σ).re) := hζσ
  have hRatioNet := hζ2Net.div hζσNet
    (ne_of_gt (riemannZeta_re_pos_of_one_lt hσ))
  have hRatioFamily :
      (fun p : Nat.Primes => riemannPrimeFactor (2 * σ) p / riemannPrimeFactor σ p) =
        riemannPrimeLowerFactor σ := by
    funext p
    let x : ℝ := (p.val : ℝ) ^ (-σ)
    have hpbase : 1 < (p.val : ℝ) := by exact_mod_cast p.2.one_lt
    have hx0 : 0 < x := by dsimp [x]; positivity
    have hxlt : x < 1 := by
      dsimp [x]
      exact Real.rpow_lt_one_of_one_lt_of_neg hpbase (by linarith [hσ])
    have hxpow : (p.val : ℝ) ^ (-(2 * σ)) = x ^ 2 := by
      rw [show -(2 * σ) = (-σ) * 2 by ring, Real.rpow_mul (by positivity), Real.rpow_two]
    dsimp [riemannPrimeFactor, riemannPrimeLowerFactor]
    rw [hxpow]
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith
    field_simp [ne_of_gt (sub_pos.mpr hxlt), ne_of_gt hx2,
      ne_of_gt (show 0 < 1 + x by linarith)]
    ring
  have hFinsetRatio (S : Finset Nat.Primes) :
      (∏ p ∈ S, riemannPrimeFactor (2 * σ) p) /
        (∏ p ∈ S, riemannPrimeFactor σ p) =
      ∏ p ∈ S, riemannPrimeLowerFactor σ p := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact congrFun hRatioFamily p
  have hRatioNetLower : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, riemannPrimeLowerFactor σ p) atTop
      (𝓝 ((riemannZeta (2 * σ)).re / (riemannZeta σ).re)) := by
    change Tendsto (fun S : Finset Nat.Primes =>
      (∏ p ∈ S, riemannPrimeFactor (2 * σ) p) /
        (∏ p ∈ S, riemannPrimeFactor σ p)) atTop
      (𝓝 ((riemannZeta (2 * σ)).re / (riemannZeta σ).re)) at hRatioNet
    exact (tendsto_congr (fun S => hFinsetRatio S)).mp hRatioNet
  have hPowNet : Tendsto (fun S : Finset Nat.Primes =>
      (∏ p ∈ S, riemannPrimeLowerFactor σ p) ^ d) atTop
        (𝓝 (((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ d)) := hRatioNetLower.pow d
  have hProdPow :
      (fun S : Finset Nat.Primes => ∏ p ∈ S, (riemannPrimeLowerFactor σ p) ^ d) =
        fun S => (∏ p ∈ S, riemannPrimeLowerFactor σ p) ^ d := by
    funext S
    rw [Finset.prod_pow]
  change Tendsto (fun S : Finset Nat.Primes =>
    ∏ p ∈ S, (riemannPrimeLowerFactor σ p) ^ d) atTop
      (𝓝 (((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ d))
  rw [hProdPow]
  exact hPowNet

set_option maxHeartbeats 10000000 in
private theorem dedekindPrimeIdealFinset_lower_bound {σ t : ℝ} (hσ : 1 < σ)
    (S : Finset Nat.Primes) :
    ∏ p ∈ S, (riemannPrimeLowerFactor σ p) ^ Module.finrank ℚ K ≤
      ∏ P ∈ primeIdealFinset (K := K) S,
        ‖dedekindPrimeFactor (K := K) ((σ : ℂ) + t * Complex.I) P‖ := by
  classical
  have hfiber (p : Nat.Primes) :
      (riemannPrimeLowerFactor σ p) ^ Module.finrank ℚ K ≤
        ∏ P ∈ primeIndexFiberFinset (K := K) p,
          ‖dedekindPrimeFactor (K := K) ((σ : ℂ) + t * Complex.I) P‖ := by
    calc
      (riemannPrimeLowerFactor σ p) ^ Module.finrank ℚ K ≤
          tprod (fun P : rationalPrimeFiber (K := K) p =>
            ‖dedekindPrimeFactor (K := K) ((σ : ℂ) + t * Complex.I) P.1‖) := by
        simpa using (dedekindPrimeFactor_fiber_bounds (K := K) hσ p).1
      _ = ∏ P ∈ primeIndexFiberFinset (K := K) p,
          ‖dedekindPrimeFactor (K := K) ((σ : ℂ) + t * Complex.I) P‖ :=
            (primeIndexFiber_prod_eq_tprod (K := K) p
              (fun P => ‖dedekindPrimeFactor (K := K) ((σ : ℂ) + t * Complex.I) P‖)).symm
  rw [primeIdealFinset_prod (K := K) S]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hq : 0 ≤ riemannPrimeLowerFactor σ p := by
      dsimp [riemannPrimeLowerFactor]
      positivity
    exact pow_nonneg hq _
  · intro p hp
    exact hfiber p

set_option maxHeartbeats 10000000 in
private theorem dedekindZeta_norm_lower_bound {σ t : ℝ} (hσ : 1 < σ) :
    ((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ Module.finrank ℚ K ≤
      ‖dedekindZeta K ((σ : ℂ) + t * Complex.I)‖ := by
  classical
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hs : 1 < s.re := by simp [s, hσ]
  have hKnet := dedekindPrimeIdealPartial_tendsto (K := K) (s := s) hs
  have hRiemannLower := riemannPrimeLowerFactor_hasProd (σ := σ) hσ
    (Module.finrank ℚ K)
  have hpoint := dedekindPrimeIdealFinset_lower_bound
    (K := K) (σ := σ) (t := t) hσ
  have h := le_of_tendsto_of_tendsto' hRiemannLower hKnet hpoint
  simpa [s] using h

set_option maxHeartbeats 10000000 in
/-- **(D3) Uniform Jensen inputs** (constants absolute; degree `n = [K:ℚ]`): for `σ > 1`,
`(ζ(2σ)/ζ(σ))^n ≤ ‖ζ_K(σ+it)‖ ≤ ζ(σ)^n`.  With (D1) and Stirling these are the only
field-dependent inputs of the unit-window zero count.
Consumers: B `ext:dedekind-zero-count`, `spl:left-line` (Euler bound at `Re = 3/2`). -/
theorem dedekindZeta_norm_bounds (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    ((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ Module.finrank ℚ K ≤
        ‖dedekindZeta K (σ + t * Complex.I)‖ ∧
      ‖dedekindZeta K (σ + t * Complex.I)‖ ≤ (riemannZeta σ).re ^ Module.finrank ℚ K := by
  exact ⟨dedekindZeta_norm_lower_bound (K := K) (σ := σ) (t := t) hσ,
    dedekindZeta_norm_upper_bound (K := K) (σ := σ) (t := t) hσ⟩


end ArtinPrimitiveRoots.Hecke
