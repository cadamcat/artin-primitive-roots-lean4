/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Adapted from `TauCeti/NumberTheory/ArithmeticDirichletSeries/{Regroup,EulerProduct/Analytic}.lean`
(Apache-2.0). It carries absolute convergence from ideal sums to norm fibres, and proves the
unrestricted analytic Euler product from the finite supported products.
-/
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Formal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

open scoped nonZeroDivisors NumberField ComplexOrder
open IsDedekindDomain

namespace ArtinPrimitiveRoots.Hecke.EulerProduct

variable {K : Type*} [Field K] [NumberField K]

/-- A term in a Dirichlet series indexed by nonzero integral ideals. -/
noncomputable def idealTerm (f : IdealArithmeticFunction K) (s : ℂ)
    (I : (Ideal (𝓞 K))⁰) : ℂ := f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s

theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s := rfl

@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]

theorem idealTerm_supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    idealTerm (IdealArithmeticFunction.supportedPart f S) s =
      Set.indicator {I : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}
        (idealTerm f s) := by
  funext I
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ
  · rw [Set.indicator_of_mem (s := {I : (Ideal (𝓞 K))⁰ |
        Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}) hI, idealTerm_def, idealTerm_def,
      IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hI]
  · rw [Set.indicator_of_notMem (s := {I : (Ideal (𝓞 K))⁰ |
        Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}) hI, idealTerm_def,
      IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl hI, zero_div]

theorem norm_idealTerm_supportedPart_le (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm (IdealArithmeticFunction.supportedPart f S) s I‖ ≤
      ‖idealTerm f s I‖ := by
  rw [idealTerm_supportedPart]
  exact norm_indicator_le_norm_self _ _

theorem summable_idealTerm_supportedPart {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : Summable (idealTerm f s)) (S : Set (HeightOneSpectrum (𝓞 K))) :
    Summable (idealTerm (IdealArithmeticFunction.supportedPart f S) s) := by
  rw [idealTerm_supportedPart]
  exact hs.indicator _

private theorem normCoeff_supportedPart_empty (f : IdealArithmeticFunction K)
    (hf : f 1 = 1) :
    ⇑(normCoeff K (IdealArithmeticFunction.supportedPart f ∅)) = LSeries.delta := by
  rw [IdealArithmeticFunction.supportedPart_empty hf, normCoeff_delta]
  exact ArithmeticFunction.one_eq_delta

/-- The `LSeries` of the norm coefficients is the ideal-indexed sum, whenever the latter
converges absolutely. -/
theorem LSeries_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm f s)) :
    LSeries (normCoeff K f) s = ∑' I, idealTerm f s I := by
  have hterm (n : ℕ) : LSeries.term (normCoeff K f) s n =
      ∑ I ∈ normFiber K n, idealTerm f s I := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normFiber_zero]
    · rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
      refine Finset.sum_congr rfl fun I hI ↦ ?_
      rw [idealTerm_def, (mem_normFiber K).mp hI]
  have hfiber (n : ℕ) :
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm f s I = LSeries.term (normCoeff K f) s n := by
    let fiber : Set ((Ideal (𝓞 K))⁰) :=
      (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}
    have hEq : fiber = {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by
      ext I
      simp [fiber]
    letI : Fintype fiber := (hEq ▸ finite_normFiber K n).fintype
    rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm f s), hterm]
  have hsum : HasSum (LSeries.term (normCoeff K f) s) (∑' I, idealTerm f s I) := by
    have h' := h.hasSum.tsum_fiberwise
      (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
    have hfun : (fun n : ℕ =>
        ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
          idealTerm f s I) = LSeries.term (normCoeff K f) s := funext hfiber
    rw [hfun] at h'
    exact h'
  change (∑' n, LSeries.term (normCoeff K f) s n) = _
  exact hsum.tsum_eq

theorem LSeriesSummable_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm f s)) : LSeriesSummable (normCoeff K f) s := by
  rw [LSeriesSummable]
  have hfiber (n : ℕ) :
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm f s I = LSeries.term (normCoeff K f) s n := by
    have hterm (n : ℕ) : LSeries.term (normCoeff K f) s n =
        ∑ I ∈ normFiber K n, idealTerm f s I := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [normFiber_zero]
      · rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
        refine Finset.sum_congr rfl fun I hI ↦ ?_
        rw [idealTerm_def, (mem_normFiber K).mp hI]
    let fiber : Set ((Ideal (𝓞 K))⁰) :=
      (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}
    have hEq : fiber = {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by
      ext I
      simp [fiber]
    letI : Fintype fiber := (hEq ▸ finite_normFiber K n).fintype
    rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm f s), hterm]
  have hsum := (h.hasSum.tsum_fiberwise
    (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))).summable
  have hfun : (fun n : ℕ =>
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm f s I) = LSeries.term (normCoeff K f) s := funext hfiber
  rw [hfun] at hsum
  exact hsum

theorem LSeriesSummable_localArithmeticFactor {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : Summable (idealTerm f s)) (P : HeightOneSpectrum (𝓞 K)) :
    LSeriesSummable (IdealArithmeticFunction.localArithmeticFactor f P) s := by
  rw [← IdealArithmeticFunction.normCoeff_supportedPart_singleton f P]
  exact LSeriesSummable_normCoeff (summable_idealTerm_supportedPart hs {P})

/-- The local Euler factor of the canonical arithmetic factor at a height-one prime. -/
noncomputable def eulerFactor (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (IdealArithmeticFunction.localArithmeticFactor f P) s

theorem LSeriesSummable_normCoeff_supportedPart (f : IdealArithmeticFunction K)
    (hf : f.IsMultiplicative) (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hS : ∀ P ∈ S, LSeriesSummable (IdealArithmeticFunction.localArithmeticFactor f P) s) :
    LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) ) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, normCoeff_supportedPart_empty f hf.map_one]
      refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
      simp only [Finset.mem_singleton] at hn
      simp [LSeries.term_delta, hn]
  | insert P S hPS ih =>
      have hSsum := ih (fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ))
      have hPsum : LSeriesSummable
          (normCoeff K (IdealArithmeticFunction.supportedPart f
            ({P} : Set (HeightOneSpectrum (𝓞 K))))) s := by
        rw [IdealArithmeticFunction.normCoeff_supportedPart_singleton f P]
        exact hS P (Finset.mem_insert_self P S)
      rw [Finset.coe_insert,
        IdealArithmeticFunction.supportedPart_insert (f := f) (S := (S : Set _)) hf
          (by simpa using hPS), normCoeff_convolution]
      refine ArithmeticFunction.LSeriesSummable_mul hSsum ?_
      rw [IdealArithmeticFunction.normCoeff_supportedPart_singleton f P]
      exact hS P (Finset.mem_insert_self P S)

theorem LSeries_normCoeff_supportedPart (f : IdealArithmeticFunction K)
    (hf : f.IsMultiplicative) (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hS : ∀ P ∈ S, LSeriesSummable (IdealArithmeticFunction.localArithmeticFactor f P) s) :
    LSeries
      (normCoeff K (IdealArithmeticFunction.supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))))
      s = ∏ P ∈ S, eulerFactor f P s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, normCoeff_supportedPart_empty f hf.map_one,
        LSeries_delta, Pi.one_apply, Finset.prod_empty]
  | insert P S hPS ih =>
      have hSsum := LSeriesSummable_normCoeff_supportedPart f hf S
        (fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ))
      have hPsum : LSeriesSummable
          (normCoeff K (IdealArithmeticFunction.supportedPart f
            ({P} : Set (HeightOneSpectrum (𝓞 K))))) s := by
        rw [IdealArithmeticFunction.normCoeff_supportedPart_singleton f P]
        exact hS P (Finset.mem_insert_self P S)
      rw [Finset.coe_insert,
        IdealArithmeticFunction.supportedPart_insert (f := f) (S := (S : Set _)) hf
          (by simpa using hPS), normCoeff_convolution,
        ArithmeticFunction.LSeries_mul' hSsum hPsum,
        ih (fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ)),
        IdealArithmeticFunction.normCoeff_supportedPart_singleton f P]
      change (∏ Q ∈ S, eulerFactor f Q s) * eulerFactor f P s =
        ∏ Q ∈ insert P S, eulerFactor f Q s
      rw [Finset.prod_insert hPS]
      exact mul_comm _ _

/-- The local Euler factor is the Dirichlet series over the powers of `P`. -/
theorem eulerFactor_eq_tsum (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    eulerFactor f P s = ∑' e : ℕ, idealTerm f s (P.primeIdealPow e) := by
  have hsupp : Function.support
      (fun n : ℕ ↦ (IdealArithmeticFunction.localArithmeticFactor f P n : ℂ) /
        (n : ℂ) ^ s) ⊆ Set.range fun e : ℕ ↦ Ideal.absNorm P.asIdeal ^ e := by
    intro n hn
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hn
    by_contra hpow
    exact hn.1 (IdealArithmeticFunction.localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq
      f P hpow)
  rw [eulerFactor, LSeries_def₀ (by simp),
    ← (Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)).tsum_eq hsupp]
  refine tsum_congr fun e ↦ ?_
  rw [IdealArithmeticFunction.localArithmeticFactor_apply_pow, idealTerm_def,
    IsDedekindDomain.HeightOneSpectrum.absNorm_primeIdealPow]

theorem hasProd_eulerFactor (f : IdealArithmeticFunction K) {s : ℂ}
    (hf : f.IsMultiplicative) (hs : Summable (idealTerm f s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦ eulerFactor f P s)
      (LSeries (normCoeff K f) s) := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ P ∈ S, eulerFactor f P s =
        ∑' I, idealTerm
          (IdealArithmeticFunction.supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) s I := by
    intro S
    rw [← LSeries_normCoeff_supportedPart f hf S
        (fun P hP ↦ LSeriesSummable_localArithmeticFactor hs P),
      LSeries_normCoeff (summable_idealTerm_supportedPart hs _)]
  rw [HasProd, SummationFilter.unconditional_filter, LSeries_normCoeff hs]
  simp only [key]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun I ↦ ‖idealTerm f s I‖) (summable_norm_iff.mpr hs)
    (fun I ↦ ?_) (Filter.Eventually.of_forall fun S I ↦ ?_)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_isPrimeTo_compl I] with S hS
    rw [idealTerm_def, idealTerm_def,
      IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hS]
  · exact norm_idealTerm_supportedPart_le f _ s I

end ArtinPrimitiveRoots.Hecke.EulerProduct
