import ArtinPrimitiveRoots.A2.ZeroFree.Missing
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Analytic
import ArtinPrimitiveRoots.Hecke.Dedekind.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
set_option maxHeartbeats 10000000

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical NumberField ComplexOrder nonZeroDivisors
open Filter Asymptotics

noncomputable section

namespace ArtinPrimitiveRoots.A2

open ArtinPrimitiveRoots A1 A2
open ArtinPrimitiveRoots.Hecke.EulerProduct

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def principalIdealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

private theorem principal_rpow_neg_two {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  have htwo : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_natCast x 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx, htwo]

private theorem principalNormFiber_card_le_idealCount (n : ℕ) :
    (normFiber F n).card ≤ principalIdealCount (F := F) n := by
  classical
  let T := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  have hcard : (normFiber F n).card ≤ T.toFinset.card := by
    refine Finset.card_le_card_of_injOn (s := normFiber F n) (t := T.toFinset)
      (fun I => (I : Ideal (𝓞 F))) ?_ ?_
    · intro I hI
      have hnorm : Ideal.absNorm (I : Ideal (𝓞 F)) = n :=
        (mem_normFiber F).mp hI
      exact T.mem_toFinset.mpr hnorm
    · intro I hI J hJ hEq
      exact Subtype.ext hEq
  unfold principalIdealCount
  exact hcard.trans_eq (Nat.card_eq_card_finite_toFinset T).symm

private theorem principalPrimeValue_norm_le_one (χ : HeckeChar F)
    (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (v : FinPlace F) :
    ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hv
  · have h := hχ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
      (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))))
    simpa [HeckeChar.loc] using le_of_eq h
  · simp

private theorem principalNorm_multiset_prod_le_one {α : Type*} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) <| ih fun x hx =>
      hf x (Multiset.mem_cons_of_mem hx)

private theorem principalIdealValue_norm_le_one (χ : HeckeChar F)
    (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (I : Ideal (𝓞 F)) :
    ‖χ.idealValue I‖ ≤ 1 := by
  unfold HeckeChar.idealValue
  apply principalNorm_multiset_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using principalPrimeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
  · simp [h]

private theorem principalIdealValue_mul (χ : HeckeChar F) (I J : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    χ.idealValue (I * J) = χ.idealValue I * χ.idealValue J := by
  classical
  simp only [HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add]

private theorem principalIdealValue_prime (χ : HeckeChar F) (v : FinPlace F) :
    χ.idealValue v.asIdeal = χ.primeValue v := by
  classical
  unfold HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible, normalize_eq]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥
  · simp [h]
  · exact (h ⟨v.isPrime, v.ne_bot⟩).elim

private theorem principalIdealValue_primePow (χ : HeckeChar F) (v : FinPlace F)
    (e : ℕ) : χ.idealValue (v.asIdeal ^ e) = χ.primeValue v ^ e := by
  induction e with
  | zero =>
    change χ.idealValue (1 : Ideal (𝓞 F)) = 1
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  | succ e ih =>
    rw [pow_succ, principalIdealValue_mul χ _ _ (pow_ne_zero _ v.ne_bot) v.ne_bot]
    rw [ih, principalIdealValue_prime, pow_succ]

private theorem principalCharacter_unitary (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  intro x
  have hxpow : (χ x : ℂˣ) ^ n = 1 := by
    have hx := congrArg (fun f : HeckeChar F => f x) hpow
    simpa using hx
  have hxpowC : (((χ x : ℂˣ) : ℂ) ^ n) = 1 := by
    simpa using congrArg (fun z : ℂˣ => (z : ℂ)) hxpow
  exact ((isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxpowC⟩).norm_eq_one)

private theorem principalIdealTerm_summable (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm (K := F)
      (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s) := by
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  have hχnorm := principalCharacter_unitary χ hχ
  have hfnorm : ∀ I : (Ideal (𝓞 F))⁰, ‖f I‖ ≤ 1 := fun I =>
    principalIdealValue_norm_le_one χ hχnorm I
  have hcount : LSeriesSummable (fun n =>
      ((principalIdealCount (F := F) n : ℕ) : ℂ)) (s.re : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F hs
  have hcountNorm := hcount.norm
  have hFiberBound (n : ℕ) :
      ∑ I ∈ normFiber F n, ‖idealTerm f s I‖ ≤
        ‖LSeries.term (fun k => (principalIdealCount (F := F) k : ℂ))
          (s.re : ℂ) n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normFiber_zero]
    calc
      ∑ I ∈ normFiber F n, ‖idealTerm f s I‖ ≤
          ∑ I ∈ normFiber F n, (1 : ℝ) / (n : ℝ) ^ s.re := by
            apply Finset.sum_le_sum
            intro I hI
            rw [norm_idealTerm, (mem_normFiber F).mp hI]
            exact div_le_div_of_nonneg_right (hfnorm I) (by positivity)
      _ = ((normFiber F n).card : ℝ) / (n : ℝ) ^ s.re := by
            rw [← Finset.sum_div]
            simp
      _ ≤ ((principalIdealCount (F := F) n : ℕ) : ℝ) / (n : ℝ) ^ s.re := by
            unfold principalIdealCount
            gcongr
            exact_mod_cast principalNormFiber_card_le_idealCount (F := F) n
      _ = ‖LSeries.term (fun k => (principalIdealCount (F := F) k : ℂ))
            (s.re : ℂ) n‖ := by
            rw [LSeries.norm_term_eq]
            simp [hn, principalIdealCount, Complex.norm_natCast]
  have hPartition : ∀ I : (Ideal (𝓞 F))⁰,
      ∃! n : ℕ, I ∈ ((fun I : (Ideal (𝓞 F))⁰ =>
        Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}) := by
    intro I
    refine ⟨Ideal.absNorm (I : Ideal (𝓞 F)), by simp, ?_⟩
    intro n hn
    simpa using hn.symm
  have hnorm : Summable (fun I : (Ideal (𝓞 F))⁰ => ‖idealTerm f s I‖) := by
    apply (summable_partition (f := fun I : (Ideal (𝓞 F))⁰ =>
      ‖idealTerm f s I‖) (fun _ => norm_nonneg _)
      (s := fun n => (fun I : (Ideal (𝓞 F))⁰ =>
        Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}) hPartition).2
    constructor
    · intro n
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ |
          Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by ext I; simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le
        (f := fun n => ‖LSeries.term
          (fun k => (principalIdealCount (F := F) k : ℂ)) (s.re : ℂ) n‖)
        (g := fun n => ∑' I : (fun I : (Ideal (𝓞 F))⁰ =>
          Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}, ‖idealTerm f s I‖)
        (fun n => tsum_nonneg fun I => norm_nonneg _)
        (fun n => ?_) hcountNorm
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ |
          Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by ext I; simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      rw [← coe_normFiber, Finset.tsum_subtype' (normFiber F n)
        (fun I => ‖idealTerm f s I‖)]
      exact hFiberBound n
  exact (summable_norm_iff.mp hnorm)

private theorem principalPrimeRatio_norm_lt_one (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) (P : FinPlace F) :
    ‖χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hχnorm := principalCharacter_unitary χ hχ
  have hN : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hNreal : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by exact_mod_cast hN
  have hnormPow : ‖((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
    have hNpos : 0 < Ideal.absNorm P.asIdeal := Nat.zero_lt_of_lt hN
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hNpos)]
    rfl
  rw [norm_mul, hnormPow]
  have hspos : 0 < s.re := lt_trans (by norm_num) hs
  calc
    ‖χ.primeValue P‖ * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) ≤
      1 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (principalPrimeValue_norm_le_one χ hχnorm P) (by positivity)
    _ < 1 := by
      calc
        1 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) =
            (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := one_mul _
        _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hNreal (neg_lt_zero.mpr hspos)

private theorem principalEulerFactor (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    {s : ℂ} (hs : 1 < s.re) (P : FinPlace F) :
    eulerFactor (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) P s =
      (1 - χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  rw [eulerFactor_eq_tsum]
  have hpowRatio (e : ℕ) :
      idealTerm (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s (P.primeIdealPow e) =
        (χ.primeValue P / ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ s) ^ e := by
    rw [idealTerm_def, P.absNorm_primeIdealPow, P.coe_primeIdealPow,
      principalIdealValue_primePow, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, div_pow]
  have hpow (e : ℕ) :
      idealTerm (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s (P.primeIdealPow e) =
        (χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) ^ e := by
    calc
      _ = (χ.primeValue P / ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ s) ^ e := hpowRatio e
      _ = (χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) ^ e := by
        congr 1
        rw [div_eq_mul_inv, Complex.cpow_neg]
  rw [tsum_congr hpow]
  exact tsum_geometric_of_norm_lt_one (principalPrimeRatio_norm_lt_one χ hχ hs P)

private theorem principalEuler_denominator_ne_zero (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    tprod (fun P : FinPlace F =>
      1 - χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  let α : FinPlace F → ℂ := fun P =>
    χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)
  have hsum := principalIdealTerm_summable χ hχ hs
  have hinj : Function.Injective (fun P : FinPlace F => P.primeIdealPow 1) := by
    intro P Q hPQ
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    simpa only [P.coe_primeIdealPow, Q.coe_primeIdealPow, pow_one] using
      congrArg (fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) hPQ
  have hsumAlpha : Summable α := by
    refine (hsum.comp_injective hinj).congr ?_
    intro P
    change idealTerm (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s
      (P.primeIdealPow 1) = α P
    rw [idealTerm_def, P.absNorm_primeIdealPow, P.coe_primeIdealPow,
      principalIdealValue_primePow]
    simp [α, div_eq_mul_inv, Complex.cpow_neg]
  have hnorm := (summable_norm_iff).2 hsumAlpha
  refine tprod_one_add_ne_zero_of_summable (f := fun P => -α P) ?_ (by simpa using hnorm)
  intro P hz
  have hsmall := principalPrimeRatio_norm_lt_one χ hχ hs P
  have hα : α P = 1 := by
    have hEq : 1 - α P = 0 := by simpa [sub_eq_add_neg] using hz
    exact (sub_eq_zero.mp hEq).symm
  change ‖α P‖ < 1 at hsmall
  rw [hα] at hsmall
  norm_num at hsmall

private theorem principal_hasProd (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : FinPlace F =>
      (1 - χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (heckeLSeries χ s) := by
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · change χ.idealValue (1 : Ideal (𝓞 F)) = 1
      unfold HeckeChar.idealValue
      rw [UniqueFactorizationMonoid.normalizedFactors_one]
      simp
    · intro I J hIJ
      change χ.idealValue ((I : Ideal (𝓞 F)) * (J : Ideal (𝓞 F)) : Ideal (𝓞 F)) = _
      exact principalIdealValue_mul χ _ _
        (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
        (mem_nonZeroDivisors_iff_ne_zero.mp J.property)
  have hsum := principalIdealTerm_summable χ hχ hs
  have hprod := hasProd_eulerFactor f hf hsum
  have hfun : (fun P : FinPlace F => eulerFactor f P s) =
      fun P => (1 - χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext P
    exact principalEulerFactor χ hχ hs P
  let e : (Ideal (𝓞 F))⁰ ≃ {I : Ideal (𝓞 F) // I ≠ ⊥} := {
    toFun := fun I : (Ideal (𝓞 F))⁰ =>
      (⟨(I : Ideal (𝓞 F)), mem_nonZeroDivisors_iff_ne_zero.mp I.property⟩ :
        {I : Ideal (𝓞 F) // I ≠ ⊥})
    invFun := fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2⟩ : (Ideal (𝓞 F))⁰)
    left_inv := fun I => Subtype.ext rfl
    right_inv := fun I => Subtype.ext rfl }
  have hseries : LSeries (normCoeff F f) s = heckeLSeries χ s := by
    rw [LSeries_normCoeff hsum]
    unfold heckeLSeries
    calc
      (∑' I : (Ideal (𝓞 F))⁰, idealTerm f s I) =
          ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, idealTerm f s (e.symm I) := by
            exact Equiv.tsum_eq e (fun I => idealTerm f s (e.symm I))
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
            apply tsum_congr
            intro I
            change χ.idealValue I.1 / ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ s =
              χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
            rw [div_eq_mul_inv, Complex.cpow_neg]
  rw [← hseries, ← hfun]
  exact hprod

private theorem principalHasProd_le_of_nonneg {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf : HasProd f a) (hg : HasProd g b) (h0 : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ g i) : a ≤ b := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro S
  exact Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => hfg i)

private theorem principalNorm_finsetProd_eq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∏ i ∈ s, f i‖ = ∏ i ∈ s, ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.prod_insert, hi, norm_mul, ih]

private theorem principalInverseBound (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖(heckeLSeries χ s)⁻¹‖ ≤ B := by
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  have hχnorm := principalCharacter_unitary χ hχ
  have hsum2 := principalIdealTerm_summable χ hχ (s := (2 : ℂ)) (by norm_num)
  have hnorm2 := (summable_norm_iff).2 hsum2
  let K : ℝ := ∑' I : (Ideal (𝓞 F))⁰, ‖idealTerm f (2 : ℂ) I‖
  have hK : 0 ≤ K := tsum_nonneg fun I => norm_nonneg _
  refine ⟨Real.exp K, Real.exp_pos _, ?_⟩
  intro s hs
  have hs1 : 1 < s.re := by linarith
  let α : FinPlace F → ℂ := fun P =>
    χ.primeValue P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)
  have hsum := principalIdealTerm_summable χ hχ hs1
  have hinj : Function.Injective (fun P : FinPlace F => P.primeIdealPow 1) := by
    intro P Q hPQ
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    simpa only [P.coe_primeIdealPow, Q.coe_primeIdealPow, pow_one] using
      congrArg (fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) hPQ
  have hcomp : Summable (fun P : FinPlace F =>
      ‖idealTerm f (2 : ℂ) (P.primeIdealPow 1)‖) := hnorm2.comp_injective hinj
  have hAlphaBound (P : FinPlace F) : ‖α P‖ ≤
      ‖idealTerm f (2 : ℂ) (P.primeIdealPow 1)‖ := by
    have hNP : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hPowS : ‖((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
      have hNpos : 0 < Ideal.absNorm P.asIdeal :=
        Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm P)
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hNpos)]
      rfl
    have hPow2 : (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) ≤
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNP.le (by linarith)
    have hval : f (P.primeIdealPow 1) = χ.primeValue P := by
      change χ.idealValue (P.asIdeal ^ 1) = χ.primeValue P
      simpa using principalIdealValue_primePow χ P 1
    calc
      ‖α P‖ = ‖χ.primeValue P‖ * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
        simp [α, norm_mul, hPowS]
      _ ≤ ‖χ.primeValue P‖ * (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hPow2 (norm_nonneg _)
      _ = ‖idealTerm f (2 : ℂ) (P.primeIdealPow 1)‖ := by
        rw [norm_idealTerm, P.absNorm_primeIdealPow, hval]
        simp only [pow_one, show (2 : ℂ).re = 2 by norm_num]
        rw [principal_rpow_neg_two (by positivity : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ)),
          div_eq_mul_inv]
        conv_lhs => rw [← Real.rpow_natCast]
        rfl
  have hAlphaNorm : Summable (fun P => ‖α P‖) :=
    hcomp.of_nonneg_of_le (fun P => norm_nonneg _) hAlphaBound
  have hAlphaTsum : (∑' P, ‖α P‖) ≤ K := by
    calc
      (∑' P, ‖α P‖) ≤ ∑' I : (Ideal (𝓞 F))⁰, ‖idealTerm f (2 : ℂ) I‖ :=
        hAlphaNorm.tsum_le_tsum_of_inj (fun P => P.primeIdealPow 1) hinj
          (fun I hI => norm_nonneg _) hAlphaBound hnorm2
      _ = K := rfl
  have hExp : HasProd (fun P => Real.exp (‖α P‖))
      (Real.exp (∑' P, ‖α P‖)) := hAlphaNorm.hasSum.rexp
  have hDenMult : Multipliable (fun P : FinPlace F => 1 - α P) :=
    multipliable_one_sub_of_summable (by simpa using hAlphaNorm)
  have hPlusMult : Multipliable (fun P : FinPlace F => 1 + ‖α P‖) :=
    Real.multipliable_one_add_of_summable hAlphaNorm
  have hDenLePlus : tprod (fun P : FinPlace F => ‖1 - α P‖) ≤
      tprod (fun P : FinPlace F => 1 + ‖α P‖) := by
    apply principalHasProd_le_of_nonneg hDenMult.norm.hasProd hPlusMult.hasProd
      (fun _ => norm_nonneg _)
    intro P
    simpa using norm_sub_le (1 : ℂ) (α P)
  have hPlusLeExp : tprod (fun P : FinPlace F => 1 + ‖α P‖) ≤
      Real.exp (∑' P, ‖α P‖) := by
    apply principalHasProd_le_of_nonneg hPlusMult.hasProd hExp
      (fun _ => by positivity)
    intro P
    simpa [add_comm] using Real.add_one_le_exp (‖α P‖)
  have hDenBound : tprod (fun P : FinPlace F => ‖1 - α P‖) ≤ Real.exp K := by
    calc
      _ ≤ Real.exp (∑' P, ‖α P‖) := hDenLePlus.trans hPlusLeExp
      _ ≤ Real.exp K := Real.exp_le_exp.mpr hAlphaTsum
  have hden0 : tprod (fun P : FinPlace F => 1 - α P) ≠ 0 :=
    principalEuler_denominator_ne_zero χ hχ hs1
  have hLval : heckeLSeries χ s =
      (tprod (fun P : FinPlace F => 1 - α P))⁻¹ := by
    have hE := principal_hasProd χ hχ hs1
    have hInv := hDenMult.tprod_inv₀ hden0
    calc
      heckeLSeries χ s = tprod (fun P : FinPlace F => (1 - α P)⁻¹) := hE.tprod_eq.symm
      _ = (tprod (fun P : FinPlace F => 1 - α P))⁻¹ := hInv
  rw [hLval, inv_inv]
  calc
    ‖tprod (fun P : FinPlace F => 1 - α P)‖ =
        tprod (fun P : FinPlace F => ‖1 - α P‖) := hDenMult.norm_tprod
    _ ≤ Real.exp K := hDenBound

private theorem principalLS_omittedFactor_nonzero (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) (v : FinPlace F) :
    1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  have hlt := principalPrimeRatio_norm_lt_one χ hχ hs v
  intro hz
  have heq : χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hz).symm
  rw [heq] at hlt
  norm_num at hlt

private theorem principalLS_omittedFactor_norm_inv_le_two (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 2 ≤ s.re) (v : FinPlace F) :
    ‖(1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ 2 := by
  have hχnorm := principalCharacter_unitary χ hχ
  have hN : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hPow : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
    have hNpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hNpos)]
    rfl
  have hsmall : ‖χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤
      (1 / 4 : ℝ) := by
    rw [norm_mul, hPow]
    have hpow2 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    have hpowle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) ≤ 1 / 4 := by
      have hNnat : 1 < Ideal.absNorm v.asIdeal :=
        NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hqn : 2 ≤ Ideal.absNorm v.asIdeal := by omega
      have hq : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hqn
      have hq2 : 4 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((Ideal.absNorm v.asIdeal : ℝ) - 2)]
      rw [principal_rpow_neg_two (by positivity : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ))]
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hq2
    calc
      ‖χ.primeValue v‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (principalPrimeValue_norm_le_one χ hχnorm v) (by positivity)
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) := by simpa using hpow2
      _ ≤ 1 / 4 := hpowle
  have hden : (3 / 4 : ℝ) ≤
      ‖1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ)
      (χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
    have hrev' : (1 : ℝ) - ‖χ.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤
      ‖1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
      simpa using hrev
    linarith
  have hineq : (‖1 - χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖)⁻¹ ≤ (3 / 4 : ℝ)⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le (by norm_num) hden) (by norm_num)).2 hden
  calc
    ‖(1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ =
        (‖1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖)⁻¹ := norm_inv _
    _ ≤ (3 / 4 : ℝ)⁻¹ := hineq
    _ ≤ 2 := by norm_num

theorem principalLS_right_half_plane_inputs
    {S : SData F CE condη} (η : HeckeChar F) (HA : HeckeAnalysis F)
    (hη : IsOfFinOrder η) :
    DifferentiableOn ℂ (HA.LS S η) {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → HA.LS S η s ≠ 0) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 2 ≤ s.re → ‖(HA.LS S η s)⁻¹‖ ≤ B := by
  have hcomplete : DifferentiableOn ℂ (HA.L η) {s : ℂ | 1 < s.re} := by
    by_cases hη1 : η = 1
    · subst η
      apply (HA.2.2.2.1).mono
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      intro hEq
      have hRe := congrArg Complex.re hEq
      norm_num at hRe
      linarith
    · obtain ⟨C, hC⟩ := HA.2.2.1 η hη hη1
      have hEq : C.value = HA.L η := hC
      rw [← hEq]
      exact C.differentiable.differentiableOn.mono fun s hs => Set.mem_univ s
  have hfactor : Differentiable ℂ (fun s : ℂ =>
      ∏ v ∈ S.Sf, (1 - η.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    refine Differentiable.fun_finsetProd ?_
    intro v hv
    have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt
        (Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))
    have hpow : Differentiable ℂ (fun s : ℂ =>
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro s
      exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (η.primeValue v)).mul hpow)
  have hLSdiff : DifferentiableOn ℂ (HA.LS S η) {s : ℂ | 1 < s.re} := by
    change DifferentiableOn ℂ (fun s => HA.L η s *
      ∏ v ∈ S.Sf, (1 - η.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) _
    exact hcomplete.mul hfactor.differentiableOn
  have hcompleteNonzero : ∀ s : ℂ, 1 < s.re → HA.L η s ≠ 0 := by
    intro s hs
    have hraw : HA.L η s = heckeLSeries η s := HA.2.1 η s hs
    rw [hraw]
    have hprod := principal_hasProd η hη hs
    have hden := principalEuler_denominator_ne_zero η hη hs
    let α : FinPlace F → ℂ := fun v => η.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)
    have hsum := principalIdealTerm_summable η hη hs
    have hinj : Function.Injective (fun v : FinPlace F => v.primeIdealPow 1) := by
      intro v w hvw
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      simpa only [v.coe_primeIdealPow, w.coe_primeIdealPow, pow_one] using
        congrArg (fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) hvw
    have hsumα : Summable α := by
      refine (hsum.comp_injective hinj).congr ?_
      intro v
      change idealTerm (fun I : (Ideal (𝓞 F))⁰ => η.idealValue I) s
        (v.primeIdealPow 1) = α v
      rw [idealTerm_def, v.absNorm_primeIdealPow, v.coe_primeIdealPow,
        principalIdealValue_primePow]
      simp [α, div_eq_mul_inv, Complex.cpow_neg]
    have hmult := multipliable_one_sub_of_summable
      ((summable_norm_iff).2 hsumα)
    have hInv := hmult.tprod_inv₀ hden
    intro hzero
    have hprodZero : tprod (fun v : FinPlace F => (1 - α v)⁻¹) = 0 :=
      hprod.tprod_eq.trans hzero
    rw [hInv] at hprodZero
    exact (inv_ne_zero hden) hprodZero
  have hLSnonzero : ∀ s : ℂ, 1 < s.re → HA.LS S η s ≠ 0 := by
    intro s hs
    change HA.L η s * ∏ v ∈ S.Sf, (1 - η.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ≠ 0
    apply mul_ne_zero (hcompleteNonzero s hs)
    exact Finset.prod_ne_zero_iff.mpr fun v hv =>
      principalLS_omittedFactor_nonzero η hη hs v
  obtain ⟨B₀, hB₀, hB₀bound⟩ := principalInverseBound η hη
  refine ⟨hLSdiff, hLSnonzero, ?_⟩
  let B : ℝ := B₀ * 2 ^ S.Sf.card
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro s hs
  have hs1 : 1 < s.re := by linarith
  have hcompleteInv : ‖(HA.L η s)⁻¹‖ ≤ B₀ := by
    have hraw : HA.L η s = heckeLSeries η s := HA.2.1 η s hs1
    rw [hraw]
    exact hB₀bound s hs
  have hlocalInv (v : FinPlace F) :
      ‖(1 - η.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ 2 :=
    principalLS_omittedFactor_norm_inv_le_two η hη hs v
  have hprodInv : ‖(∏ v ∈ S.Sf, (1 - η.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹‖ ≤ 2 ^ S.Sf.card := by
    rw [← Finset.prod_inv_distrib]
    calc
      ‖∏ v ∈ S.Sf, (1 - η.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤
          ∏ v ∈ S.Sf, ‖(1 - η.primeValue v *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
              exact le_of_eq (principalNorm_finsetProd_eq S.Sf (fun v =>
                (1 - η.primeValue v *
                  ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹))
      _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
            exact Finset.prod_le_prod₀
              (fun v hv => norm_nonneg _)
              (fun v hv => hlocalInv v)
      _ = 2 ^ S.Sf.card := by simp
  change ‖(HA.L η s * ∏ v ∈ S.Sf, (1 - η.primeValue v *
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹‖ ≤ B
  rw [mul_inv, norm_mul]
  calc
    ‖(HA.L η s)⁻¹‖ * ‖(∏ v ∈ S.Sf, (1 - η.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹‖ ≤
        B₀ * ‖(∏ v ∈ S.Sf, (1 - η.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹‖ :=
      mul_le_mul_of_nonneg_right hcompleteInv (norm_nonneg _)
    _ ≤ B₀ * 2 ^ S.Sf.card := mul_le_mul_of_nonneg_left hprodInv hB₀.le
    _ = B := rfl

end ArtinPrimitiveRoots.A2
