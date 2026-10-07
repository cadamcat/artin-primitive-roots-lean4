/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Adapted from `TauCeti/NumberTheory/ArithmeticDirichletSeries/{Basic,NormCoeff,Convolution}.lean`
(Apache-2.0). Only the ideal arithmetic, norm-fibre, and convolution interfaces used by the
Euler-product proof are included here.
-/
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.IdealSupport
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

namespace ArtinPrimitiveRoots.Hecke.EulerProduct

variable (K : Type*) [Field K] [NumberField K]

/-- Complex-valued coefficients indexed by the nonzero integral ideals of `𝓞 K`. -/
abbrev IdealArithmeticFunction := (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

variable {K}

/-- Multiplicativity on relatively prime nonzero ideals. -/
structure IsMultiplicative (f : IdealArithmeticFunction K) : Prop where
  map_one : f 1 = 1
  map_mul_of_isRelPrime {I J : (Ideal (𝓞 K))⁰}
    (hIJ : IsRelPrime (I : Ideal (𝓞 K)) (J : Ideal (𝓞 K))) : f (I * J) = f I * f J

theorem IsMultiplicative.map_prod [DecompositionMonoid (Ideal (𝓞 K))]
    {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative) {ι : Type*}
    (g : ι → (Ideal (𝓞 K))⁰) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ IsRelPrime (g i : Ideal (𝓞 K)) (g j)) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf.map_one
  | insert i s hi ih =>
      have hrel : IsRelPrime (g i : Ideal (𝓞 K))
          ((∏ j ∈ s, g j : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
        rw [Submonoid.coe_finsetProd]
        exact IsRelPrime.prod_right fun j hj ↦
          hs (by simp) (by simp [hj]) (by rintro rfl; exact hi hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi, hf.map_mul_of_isRelPrime hrel,
        ih (hs.mono (by rw [Finset.coe_insert]; exact Set.subset_insert i s))]

theorem IsMultiplicative.map_prod_pow {f : IdealArithmeticFunction K}
    (hf : f.IsMultiplicative) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : HeightOneSpectrum (𝓞 K) → ℕ) (A : (Ideal (𝓞 K))⁰)
    (hA : (A : Ideal (𝓞 K)) = ∏ P ∈ S, P.asIdeal ^ e P) :
    f A = ∏ P ∈ S,
      f ⟨P.asIdeal ^ e P, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ P.ne_bot)⟩ := by
  have hAeq : A = ∏ P ∈ S,
      (⟨P.asIdeal ^ e P, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ P.ne_bot)⟩ :
        (Ideal (𝓞 K))⁰) := Subtype.ext (by rw [hA, Submonoid.coe_finsetProd])
  rw [hAeq]
  refine hf.map_prod _ S fun P _ Q _ hPQ ↦ ?_
  exact ((Ideal.isPrimeTo_asIdeal_iff.mpr (by simpa using hPQ)).pow (e P)).isRelPrime
    (Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨e Q, rfl⟩)

end IdealArithmeticFunction

/-- The finite fibre of nonzero ideals with absolute norm `n`. -/
theorem finite_normFiber (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}.Finite :=
  (Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn

/-- The finite set of nonzero ideals of absolute norm `n`. -/
noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

@[simp]
theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]

theorem coe_normFiber (n : ℕ) :
    (normFiber K n : Set ((Ideal (𝓞 K))⁰)) =
      (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n} := by
  ext I
  simp

@[simp]
theorem normFiber_zero : normFiber K 0 = ∅ := by
  ext I
  rw [mem_normFiber]
  constructor
  · intro hI
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property
      (Ideal.absNorm_eq_zero_iff.mp hI)).elim
  · simp

@[simp]
theorem normFiber_one : normFiber K 1 = {1} := by
  ext I
  simp [mem_normFiber, Ideal.absNorm_eq_one_iff, Subtype.ext_iff]

/-- Sum an ideal arithmetic function over the ideals of each absolute norm. -/
noncomputable def normCoeff (f : IdealArithmeticFunction K) : ArithmeticFunction ℂ where
  toFun n := ∑ I ∈ normFiber K n, f I
  map_zero' := by simp [normFiber_zero]

theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := rfl

@[simp]
theorem normCoeff_apply_one (f : IdealArithmeticFunction K) : normCoeff K f 1 = f 1 := by
  rw [normCoeff_eq_sum_normFiber, normFiber_one]
  simp

namespace Ideal

theorem finite_setOf_mul_eq (A : (Ideal (𝓞 K))⁰) :
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ | p.1 * p.2 = A}.Finite := by
  let hfin : Fintype {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ (nonZeroDivisors.coe_ne_zero A)
  have hdvd : {I : Ideal (𝓞 K) | I ∣ (A : Ideal (𝓞 K))}.Finite :=
    Set.Finite.ofFinset
      (Finset.univ.image (Subtype.val : {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} → _))
      (by simp)
  refine Set.Finite.of_finite_image (f := fun p ↦ ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
    (hdvd.subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.2 : Ideal (𝓞 K)), by simpa using congrArg Subtype.val hp.symm⟩
  · rintro p hp q hq hpq
    have h1 : p.1 = q.1 := Subtype.ext hpq
    have h2 : p.2 = q.2 := by
      refine mul_left_cancel (a := p.1) ?_
      rw [hp, ← hq, h1]
    exact Prod.ext h1 h2

noncomputable def divisorsAntidiagonal (A : (Ideal (𝓞 K))⁰) :
    Finset ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) := (finite_setOf_mul_eq K A).toFinset

@[simp]
theorem mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} :
    p ∈ divisorsAntidiagonal K A ↔ p.1 * p.2 = A := by
  simp [divisorsAntidiagonal]

end Ideal

namespace IdealArithmeticFunction

/-- Ideal Dirichlet convolution, indexed by the finite factorizations into nonzero ideals. -/
noncomputable def convolution (f g : IdealArithmeticFunction K) : IdealArithmeticFunction K :=
  fun A ↦ ∑ p ∈ Ideal.divisorsAntidiagonal K A, f p.1 * g p.2

@[simp]
theorem convolution_apply (f g : IdealArithmeticFunction K) (A : (Ideal (𝓞 K))⁰) :
    convolution K f g A = ∑ p ∈ Ideal.divisorsAntidiagonal K A, f p.1 * g p.2 := rfl

end IdealArithmeticFunction

theorem normCoeff_convolution (f g : IdealArithmeticFunction K) :
    normCoeff K (IdealArithmeticFunction.convolution K f g) =
      normCoeff K f * normCoeff K g := by
  ext n
  rcases n with _ | n
  · simp
  simp only [normCoeff_eq_sum_normFiber,
    IdealArithmeticFunction.convolution_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨A, p⟩ ↦
      ⟨(Ideal.absNorm (p.1 : Ideal (𝓞 K)), Ideal.absNorm (p.2 : Ideal (𝓞 K))),
        ⟨p.1, p.2⟩⟩)
    (fun ⟨_d, ⟨B, C⟩⟩ ↦ ⟨B * C, (B, C)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_sigma, mem_normFiber, Ideal.mem_divisorsAntidiagonal,
      Nat.mem_divisorsAntidiagonal] <;>
    aesop (add simp [map_mul])

end ArtinPrimitiveRoots.Hecke.EulerProduct
