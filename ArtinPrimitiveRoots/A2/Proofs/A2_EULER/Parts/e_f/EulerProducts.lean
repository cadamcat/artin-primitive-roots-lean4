import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Analytic
import ArtinPrimitiveRoots.Hecke.Dedekind.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
set_option maxHeartbeats 10000000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical NumberField ComplexOrder nonZeroDivisors
open Filter Asymptotics
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_f
open ArtinPrimitiveRoots A1 A2 Hecke.EulerProduct
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def principalIdealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

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


theorem character_unitary (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (x : IdeleClassGroup (𝓞 F) F) : ‖((χ x : ℂˣ) : ℂ)‖ = 1 :=
  principalCharacter_unitary χ hχ x

theorem prime_ratio_small (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    {s : ℂ} (hs : 1 < s.re) (v : FinPlace F) :
    ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 :=
  principalPrimeRatio_norm_lt_one χ hχ hs v

theorem deleted_hasProd (S : SData F CE condη) (HA : HeckeAnalysis F)
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} =>
      (1 - χ.primeValue v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (HA.LS S χ s) := by
  classical
  let d : FinPlace F → ℂ := fun v =>
    1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)
  have hd (v : FinPlace F) : d v ≠ 0 := by
    intro hz
    have he : χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) = 1 :=
      (sub_eq_zero.mp hz).symm
    have h := prime_ratio_small χ hχ hs v
    rw [he] at h
    norm_num at h
  have hp := principal_hasProd χ hχ hs
  have hfin : HasProd (fun v => if v ∈ S.Sf then d v else 1) (∏ v ∈ S.Sf, d v) := by
    simpa using (hasProd_prod_of_ne_finset_one (s := S.Sf)
      (f := fun v => if v ∈ S.Sf then d v else 1) (by intro v hv; simp [hv]))
  have hm := hp.mul hfin
  have hfun : (fun v => (d v)⁻¹ * (if v ∈ S.Sf then d v else 1)) =
      (fun v => if v ∈ S.Sf then 1 else (d v)⁻¹) := by
    funext v
    by_cases hv : v ∈ S.Sf
    · simp [hv, hd v]
    · simp [hv]
  change HasProd (fun v => (d v)⁻¹ * (if v ∈ S.Sf then d v else 1)) _ at hm
  rw [hfun] at hm
  have hval : heckeLSeries χ s * (∏ v ∈ S.Sf, d v) = HA.LS S χ s := by
    rw [HeckeAnalysis.LS, HeckeAnalysis.L, HA.property.1 χ s hs]
  rw [hval] at hm
  apply (hasProd_subtype_iff_mulIndicator (s := {v : FinPlace F | v ∉ S.Sf})
    (f := fun v => (d v)⁻¹)).mpr
  exact hm.congr_fun (fun v => by
    by_cases hv : v ∈ S.Sf <;> simp [Set.mulIndicator_apply, hv])

theorem deleted_ne_zero (S : SData F CE condη) (HA : HeckeAnalysis F)
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    HA.LS S χ s ≠ 0 := by
  classical
  let d : FinPlace F → ℂ := fun v =>
    1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)
  have hd (v : FinPlace F) : d v ≠ 0 := by
    intro hz
    have h := prime_ratio_small χ hχ hs v
    rw [(sub_eq_zero.mp hz).symm] at h
    norm_num at h
  have hprod := principal_hasProd χ hχ hs
  have hdenprod : Multipliable d := by
    let α : FinPlace F → ℂ := fun P =>
      χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)
    have hsum := principalIdealTerm_summable χ hχ hs
    have hinj : Function.Injective (fun P : FinPlace F => P.primeIdealPow 1) := by
      intro P Q hPQ
      apply HeightOneSpectrum.asIdeal_injective
      simpa using congrArg (fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) hPQ
    have hα : Summable α := by
      refine (hsum.comp_injective hinj).congr ?_
      intro P
      change idealTerm (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s (P.primeIdealPow 1) = α P
      rw [idealTerm_def, P.absNorm_primeIdealPow, P.coe_primeIdealPow,
        principalIdealValue_primePow]
      simp [α, div_eq_mul_inv, Complex.cpow_neg]
    simpa [d, α, sub_eq_add_neg] using
      multipliable_one_add_of_summable (summable_norm_iff.mpr hα.neg)
  have hmul := hprod.mul hdenprod.hasProd
  have hOne : HasProd (fun _ : FinPlace F => (1 : ℂ)) 1 := hasProd_one
  have heq : heckeLSeries χ s * ∏' v, d v = 1 :=
    (hmul.congr_fun (fun v => by simp [d, hd v])).unique hOne
  have hraw : heckeLSeries χ s ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at heq
    exact zero_ne_one heq
  rw [HeckeAnalysis.LS, HeckeAnalysis.L, HA.property.1 χ s hs]
  exact mul_ne_zero hraw (Finset.prod_ne_zero_iff.mpr (fun v hv => hd v))

theorem twist_primeValue (χ κ : HeckeChar F) (v : FinPlace F)
    (hχ : χ.UnramifiedAt v) (hκfin : IsOfFinOrder κ) :
    (χ * κ⁻¹).primeValue v = χ.primeValue v * star (κ.primeValue v) := by
  classical
  have hloc (x : (v.adicCompletion F)ˣ) :
      (χ * κ⁻¹).loc v x = χ.loc v x * (κ.loc v x)⁻¹ := by
    rfl
  by_cases hκ : κ.UnramifiedAt v
  · have hp : (χ * κ⁻¹).UnramifiedAt v := by
      intro x hx hxi
      rw [hloc, hχ x hx hxi, hκ x hx hxi]
      simp
    let π := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
    have hn : ‖((κ.loc v π : ℂˣ) : ℂ)‖ = 1 :=
      e_f.character_unitary κ hκfin _
    simp only [HeckeChar.primeValue, if_pos hp, if_pos hχ, if_pos hκ]
    rw [hloc]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [Complex.inv_eq_conj hn]
    rfl
  · have hp : ¬ (χ * κ⁻¹).UnramifiedAt v := by
      intro hp
      apply hκ
      intro x hx hxi
      have he := hp x hx hxi
      rw [hloc, hχ x hx hxi, one_mul] at he
      exact inv_eq_one.mp he
    simp [HeckeChar.primeValue, hp, hκ]

theorem kummer_finiteOrder {D : FieldData F} {S : SData F CE condη}
    (η : HeckeChar F) (U : FrequencyData S D η) (u : U.U) (hη : IsOfFinOrder η) :
    IsOfFinOrder (U.kummer u) := by
  have hω : IsOfFinOrder (η * (U.kummer u)⁻¹) := by
    rw [← U.omega_induces_twist u]
    exact U.omega_finiteOrder u
  have heq : U.kummer u = η * (η * (U.kummer u)⁻¹)⁻¹ := by
    apply ContinuousMonoidHom.ext
    intro x
    change U.kummer u x = η x * (η x * (U.kummer u x)⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv, mul_left_comm (η x), mul_inv_cancel, mul_one]
  rw [heq]
  exact hη.mul hω.inv

theorem one_primeValue (v : FinPlace F) :
    (1 : HeckeChar F).primeValue v = 1 := by
  have h : (1 : HeckeChar F).UnramifiedAt v := by
    intro x hx hxi
    simp [HeckeChar.loc]
  simp [HeckeChar.primeValue, h, HeckeChar.loc]

end ArtinPrimitiveRoots.Proofs.e_f
