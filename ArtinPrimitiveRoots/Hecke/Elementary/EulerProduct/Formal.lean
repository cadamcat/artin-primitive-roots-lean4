/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Adapted from `TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean`
(Apache-2.0). This file proves the finite ideal Euler products and the formal coefficient identity
used by the analytic argument.
-/
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Algebra
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/- The prime-power API is supplied by TauCeti's EulerProduct.Basic module. -/

namespace ArtinPrimitiveRoots.Hecke.EulerProduct

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K}

theorem coeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.mk fun j ↦ f (P.primeIdealPow j)) = f (P.primeIdealPow n) := by
  simp

/-- The canonical local power series at a height-one prime. -/
noncomputable def localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ f (P.primeIdealPow n)

@[simp]
theorem constantCoeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : (localPowerSeries f P).constantCoeff = f 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, localPowerSeries, PowerSeries.coeff_mk]
  congr 1

/-- The canonical local arithmetic factor, supported on powers of the prime ideal norm. -/
noncomputable def localArithmeticFactor (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P)

theorem localArithmeticFactor_apply_pow (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localArithmeticFactor f P (Ideal.absNorm P.asIdeal ^ n) = f (P.primeIdealPow n) := by
  rw [localArithmeticFactor,
    ArithmeticFunction.ofPowerSeries_apply_pow (NumberField.HeightOneSpectrum.one_lt_absNorm P)]
  rw [localPowerSeries, PowerSeries.coeff_mk]

theorem localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m) :
    localArithmeticFactor f P m = 0 := by
  rw [localArithmeticFactor,
    ArithmeticFunction.ofPowerSeries_apply (NumberField.HeightOneSpectrum.one_lt_absNorm P),
    Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]

theorem exists_pow_eq_of_localArithmeticFactor_apply_ne_zero (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : localArithmeticFactor f P m ≠ 0) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m := by
  by_contra hpow
  exact hm (localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hpow)

end IdealArithmeticFunction

namespace IdealArithmeticFunction

/-- Restrict an ideal function to nonzero ideals supported on a set of primes. -/
noncomputable def supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : IdealArithmeticFunction K :=
  Set.indicator {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ} f

variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}

@[simp]
theorem supportedPart_apply_of_isPrimeTo_compl
    (hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) : supportedPart f S A = f A :=
  Set.indicator_of_mem (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

@[simp]
theorem supportedPart_apply_of_not_isPrimeTo_compl
    (hA : ¬ Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) : supportedPart f S A = 0 :=
  Set.indicator_of_notMem (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

theorem isPrimeTo_compl_of_supportedPart_apply_ne_zero
    (hA : supportedPart f S A ≠ 0) : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ :=
  not_not.mp fun h ↦ hA (supportedPart_apply_of_not_isPrimeTo_compl h)

theorem supportedPart_one (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : supportedPart f S 1 = f 1 :=
  supportedPart_apply_of_isPrimeTo_compl (by simp [Ideal.one_eq_top])

theorem IsMultiplicative.supportedPart (hf : f.IsMultiplicative)
    (S : Set (HeightOneSpectrum (𝓞 K))) : (supportedPart f S).IsMultiplicative := by
  refine ⟨by rw [supportedPart_one, hf.map_one], fun {I J} hIJ ↦ ?_⟩
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ
  · by_cases hJ : Ideal.IsPrimeTo (J : Ideal (𝓞 K)) Sᶜ
    · rw [supportedPart_apply_of_isPrimeTo_compl (A := I * J)
          (by rw [Submonoid.coe_mul]; exact Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩),
        supportedPart_apply_of_isPrimeTo_compl hI, supportedPart_apply_of_isPrimeTo_compl hJ,
        hf.map_mul_of_isRelPrime hIJ]
    · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
          (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
        supportedPart_apply_of_not_isPrimeTo_compl hJ, mul_zero]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
      supportedPart_apply_of_not_isPrimeTo_compl hI, zero_mul]

@[simp]
theorem supportedPart_univ (f : IdealArithmeticFunction K) :
    supportedPart f Set.univ = f := by
  funext A
  refine supportedPart_apply_of_isPrimeTo_compl ?_
  rw [Set.compl_univ]
  exact Ideal.isPrimeTo_empty.mpr (by simpa using nonZeroDivisors.coe_ne_zero A)

noncomputable def delta : IdealArithmeticFunction K := fun A ↦ if A = 1 then 1 else 0

@[simp]
theorem delta_one : delta (1 : (Ideal (𝓞 K))⁰) = 1 := by simp [delta]

@[simp]
theorem delta_of_ne_one {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) : delta A = 0 := by
  simp [delta, hA]

theorem supportedPart_empty (hf : f 1 = 1) : supportedPart f ∅ = delta := by
  funext A
  have hiff : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (∅ : Set (HeightOneSpectrum (𝓞 K)))ᶜ ↔
      A = 1 := by
    rw [Set.compl_empty, Ideal.isPrimeTo_univ_iff, ← Ideal.one_eq_top]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rcases eq_or_ne A 1 with rfl | hA
  · rw [supportedPart_apply_of_isPrimeTo_compl (hiff.mpr rfl), delta_one, hf]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl (fun h ↦ hA (hiff.mp h)), delta_of_ne_one hA]

end IdealArithmeticFunction

theorem normCoeff_delta : normCoeff K (IdealArithmeticFunction.delta (K := K)) = 1 := by
  classical
  ext n
  by_cases hn : n = 1
  · subst n
    rw [normCoeff_apply_one, IdealArithmeticFunction.delta_one]
    simp
  · simp only [normCoeff_eq_sum_normFiber, ArithmeticFunction.one_apply, hn]
    apply Finset.sum_eq_zero
    intro I hI
    apply IdealArithmeticFunction.delta_of_ne_one
    intro hI_one
    subst I
    have hnorm := (mem_normFiber K).mp hI
    exact hn (by simpa using hnorm.symm)

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}

private theorem exists_eq_pow_of_supportedPart_singleton_apply_ne_zero
    {f : IdealArithmeticFunction K} {P : HeightOneSpectrum (𝓞 K)}
    {I : (Ideal (𝓞 K))⁰} (hI : supportedPart f {P} I ≠ 0) :
    ∃ m : ℕ, (I : Ideal (𝓞 K)) = P.asIdeal ^ m :=
  Ideal.isPrimeTo_compl_singleton_iff.mp (isPrimeTo_compl_of_supportedPart_apply_ne_zero hI)

private theorem supportedPart_mul_eq_zero_of_ne
    {f : IdealArithmeticFunction K} {P : HeightOneSpectrum (𝓞 K)}
    {S : Set (HeightOneSpectrum (𝓞 K))} (hPS : P ∈ Sᶜ)
    {A B C : (Ideal (𝓞 K))⁰} {n : ℕ}
    (hB : Ideal.IsPrimeTo (B : Ideal (𝓞 K)) Sᶜ)
    (hC : (C : Ideal (𝓞 K)) = P.asIdeal ^ n)
    (hA : (A : Ideal (𝓞 K)) = P.asIdeal ^ n * (B : Ideal (𝓞 K))) :
    ∀ p ∈ Ideal.divisorsAntidiagonal K A, p ≠ (B, C) →
      supportedPart f S p.1 * supportedPart f {P} p.2 = 0 := by
  intro p hp hne
  by_contra hp0
  have h1 := isPrimeTo_compl_of_supportedPart_apply_ne_zero (left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero
    (right_ne_zero_of_mul hp0)
  have hmul : (p.1 : Ideal (𝓞 K)) * (p.2 : Ideal (𝓞 K)) = (A : Ideal (𝓞 K)) := by
    exact congrArg Subtype.val ((Ideal.mem_divisorsAntidiagonal K).mp hp)
  have heq : P.asIdeal ^ m * (p.1 : Ideal (𝓞 K)) = P.asIdeal ^ n * (B : Ideal (𝓞 K)) := by
    rw [← h2, mul_comm, hmul, hA]
  obtain ⟨rfl, hval⟩ :=
    Ideal.eq_and_eq_of_pow_mul_eq_pow_mul P.ne_bot (h1.not_dvd hPS) (hB.not_dvd hPS) heq
  exact hne (Prod.ext (Subtype.ext hval) (Subtype.ext (h2.trans hC.symm)))

private theorem isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero
    {f : IdealArithmeticFunction K} {P : HeightOneSpectrum (𝓞 K)}
    {S : Set (HeightOneSpectrum (𝓞 K))} {A : (Ideal (𝓞 K))⁰}
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} (hp : p ∈ Ideal.divisorsAntidiagonal K A)
    (hp0 : supportedPart f S p.1 * supportedPart f {P} p.2 ≠ 0) :
    Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (insert P S)ᶜ := by
  have h1 := isPrimeTo_compl_of_supportedPart_apply_ne_zero (left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero
    (right_ne_zero_of_mul hp0)
  rw [← congrArg Subtype.val ((Ideal.mem_divisorsAntidiagonal K).mp hp), Submonoid.coe_mul]
  refine Ideal.isPrimeTo_mul_iff.mpr
    ⟨h1.mono (Set.compl_subset_compl.mpr (Set.subset_insert P S)), ?_⟩
  rw [h2]
  exact (Ideal.isPrimeTo_asIdeal_iff.mpr (by simp)).pow m

theorem supportedPart_insert (hf : f.IsMultiplicative) {P : HeightOneSpectrum (𝓞 K)}
    (hP : P ∉ S) : supportedPart f (insert P S) = convolution K (supportedPart f S)
      (supportedPart f {P}) := by
  have hPS : P ∈ Sᶜ := Set.mem_compl hP
  funext A
  rw [convolution_apply]
  by_cases hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (insert P S)ᶜ
  · obtain ⟨n, J, hJ, hAJ⟩ := hA.exists_eq_pow_mul (𝔭 := P)
    obtain ⟨B, rfl⟩ : ∃ B : (Ideal (𝓞 K))⁰, (B : Ideal (𝓞 K)) = J :=
      ⟨⟨J, mem_nonZeroDivisors_of_ne_zero (by simpa using hJ.ne_bot)⟩, rfl⟩
    have hCP : Ideal.IsPrimeTo ((P.primeIdealPow n : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        ({P} : Set (HeightOneSpectrum (𝓞 K)))ᶜ :=
      Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨n, P.coe_primeIdealPow n⟩
    have hBC : B * P.primeIdealPow n = A :=
      Subtype.ext (by rw [Submonoid.coe_mul, P.coe_primeIdealPow, mul_comm, ← hAJ])
    rw [Finset.sum_eq_single_of_mem (B, P.primeIdealPow n)
          ((Ideal.mem_divisorsAntidiagonal K).mpr hBC)
          (supportedPart_mul_eq_zero_of_ne hPS hJ (P.coe_primeIdealPow n) hAJ),
      supportedPart_apply_of_isPrimeTo_compl hA, supportedPart_apply_of_isPrimeTo_compl hJ,
      supportedPart_apply_of_isPrimeTo_compl hCP,
      ← hf.map_mul_of_isRelPrime ((hJ.mono (Set.singleton_subset_iff.mpr hPS)).isRelPrime hCP),
      hBC]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl hA]
    exact (Finset.sum_eq_zero fun p hp ↦ not_not.mp fun hp0 ↦
      hA (isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero hp hp0)).symm

theorem normCoeff_supportedPart_singleton (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    normCoeff K (supportedPart f {P}) = localArithmeticFactor f P := by
  have h2 : 2 ≤ Ideal.absNorm P.asIdeal := by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm P
    exact Nat.succ_le_iff.mpr h
  ext n
  rw [normCoeff_eq_sum_normFiber]
  by_cases hn : ∃ k : ℕ, Ideal.absNorm P.asIdeal ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    obtain ⟨C, hCval⟩ : ∃ C : (Ideal (𝓞 K))⁰, (C : Ideal (𝓞 K)) = P.asIdeal ^ k :=
      ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k P.ne_bot)⟩, rfl⟩
    have hCmem : C ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k) := by
      rw [mem_normFiber, hCval, map_pow]
    have hother : ∀ I ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k), I ≠ C →
        supportedPart f ({P} : Set (HeightOneSpectrum (𝓞 K))) I = 0 := by
      intro I hI hIC
      by_contra hI0
      obtain ⟨j, hj⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
      have hjk : Ideal.absNorm P.asIdeal ^ j = Ideal.absNorm P.asIdeal ^ k := by
        rw [← map_pow, ← hj]
        exact (mem_normFiber K).mp hI
      exact hIC (Subtype.ext (by rw [hj, hCval, Nat.pow_right_injective h2 hjk]))
    rw [Finset.sum_eq_single_of_mem C hCmem hother,
      supportedPart_apply_of_isPrimeTo_compl
        (by rw [hCval]; exact Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨k, rfl⟩),
      localArithmeticFactor_apply_pow]
    exact congrArg f (Subtype.ext hCval)
  · rw [localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hn]
    refine Finset.sum_eq_zero fun I hI ↦ ?_
    by_contra hI0
    obtain ⟨j, hj⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
    exact hn ⟨j, by rw [← map_pow, ← hj]; exact (mem_normFiber K).mp hI⟩

theorem normCoeff_supportedPart (hf : f.IsMultiplicative)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) =
      ∏ P ∈ S, localArithmeticFactor f P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, supportedPart_empty hf.map_one, normCoeff_delta, Finset.prod_empty]
  | insert P S hPS ih =>
      rw [Finset.coe_insert, supportedPart_insert hf (by simpa using hPS),
        normCoeff_convolution, ih, normCoeff_supportedPart_singleton,
        Finset.prod_insert hPS, mul_comm]

end IdealArithmeticFunction

end ArtinPrimitiveRoots.Hecke.EulerProduct
