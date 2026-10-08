import DedekindResidue.CompletedZeta.Existence
import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Analytic

set_option autoImplicit false
set_option maxHeartbeats 10000000

open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2FreqP
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {S : ArtinPrimitiveRoots.A1.SData F CE condη}

private theorem complexUnit_norm_one_of_finiteOrder {z : ℂˣ}
    (hz : IsOfFinOrder z) : ‖(z : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hz)
  have hcomplex : (z : ℂ) ^ n = 1 := by
    have h := congrArg (fun y : ℂˣ => (y : ℂ)) hpow
    simpa using h
  exact Complex.norm_eq_one_of_pow_eq_one hcomplex (Nat.ne_of_gt hn)

theorem reciprocal_primeValue_norm_le_one (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hram
  · let y := Units.mk0 (unif v) (unif_ne_zero v)
    let g : IdeleClassGroup (𝓞 F) F :=
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (toLoc v y)
    have hfin : IsOfFinOrder (χ g) := by
      obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      have h := congrArg (fun f : HeckeChar F => f g) hpow
      simpa using h
    have heval : χ.loc v (toLoc v y) = χ g := rfl
    simpa [y, heval] using (complexUnit_norm_one_of_finiteOrder hfin).le
  · simp

theorem reciprocal_omittedEulerFactors_differentiable
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (χ : HeckeChar F) :
    Differentiable ℂ (fun s : ℂ => ∏ v ∈ S.Sf,
      (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
  refine Differentiable.fun_finsetProd ?_
  intro v hv
  have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNnat
  have hpow : Differentiable ℂ
      (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s
    exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
  exact (differentiable_const (1 : ℂ)).sub
    ((differentiable_const (χ.primeValue v)).mul hpow)

open scoped nonZeroDivisors in
open ArtinPrimitiveRoots.Hecke.EulerProduct in
private theorem finiteOrder_idealTerm_summable (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (s : ℂ) (hs : 1 < s.re) :
    Summable (idealTerm (K := F)
      (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s) := by
  classical
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  let count : ℕ → ℕ := fun n => Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have hprod (t : Multiset (Ideal (𝓞 F))) (g : Ideal (𝓞 F) → ℂ)
      (hg : ∀ I ∈ t, ‖g I‖ ≤ 1) : ‖(t.map g).prod‖ ≤ 1 := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons I t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hg I (by simp)) (norm_nonneg _) <|
        ih fun J hJ => hg J (Multiset.mem_cons_of_mem hJ)
  have hfnorm : ∀ I : (Ideal (𝓞 F))⁰, ‖f I‖ ≤ 1 := by
    intro I
    dsimp [f]
    unfold HeckeChar.idealValue
    apply hprod
    intro P hP
    split_ifs with h
    · exact reciprocal_primeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
    · simp
  have hcard (n : ℕ) : (normFiber F n).card ≤ count n := by
    let T := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
    have hle : (normFiber F n).card ≤ T.toFinset.card := by
      refine Finset.card_le_card_of_injOn (s := normFiber F n) (t := T.toFinset)
        (fun I => (I : Ideal (𝓞 F))) ?_ ?_
      · intro I hI
        have hnorm : Ideal.absNorm (I : Ideal (𝓞 F)) = n := (mem_normFiber F).mp hI
        exact T.mem_toFinset.mpr hnorm
      · intro I hI J hJ hEq
        exact Subtype.ext hEq
    exact hle.trans_eq (Nat.card_eq_card_finite_toFinset T).symm
  have hcount : LSeriesSummable (fun n => (count n : ℂ)) (s.re : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F hs
  have hcountNorm := hcount.norm
  have hfiber (n : ℕ) :
      ∑ I ∈ normFiber F n, ‖idealTerm f s I‖ ≤
        ‖LSeries.term (fun k => (count k : ℂ)) (s.re : ℂ) n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normFiber_zero]
    calc
      _ ≤ ∑ I ∈ normFiber F n, (1 : ℝ) / (n : ℝ) ^ s.re := by
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_idealTerm, (mem_normFiber F).mp hI]
        exact div_le_div_of_nonneg_right (hfnorm I) (by positivity)
      _ = ((normFiber F n).card : ℝ) / (n : ℝ) ^ s.re := by
        rw [← Finset.sum_div]
        simp
      _ ≤ (count n : ℝ) / (n : ℝ) ^ s.re := by
        gcongr
        exact_mod_cast hcard n
      _ = _ := by
        rw [LSeries.norm_term_eq]
        simp [hn, Complex.norm_natCast]
  have hpartition : ∀ I : (Ideal (𝓞 F))⁰,
      ∃! n : ℕ, I ∈ ((fun J : (Ideal (𝓞 F))⁰ =>
        Ideal.absNorm (J : Ideal (𝓞 F))) ⁻¹' {n}) := by
    intro I
    refine ⟨Ideal.absNorm (I : Ideal (𝓞 F)), by simp, ?_⟩
    intro n hn
    simpa using hn.symm
  have hnorm : Summable (fun I : (Ideal (𝓞 F))⁰ => ‖idealTerm f s I‖) := by
    apply (summable_partition (f := fun I : (Ideal (𝓞 F))⁰ => ‖idealTerm f s I‖)
      (fun _ => norm_nonneg _) (s := fun n =>
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n})
      hpartition).2
    constructor
    · intro n
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by
        ext I
        simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le
        (f := fun n => ‖LSeries.term (fun k => (count k : ℂ)) (s.re : ℂ) n‖)
        (g := fun n => ∑' I : (fun J : (Ideal (𝓞 F))⁰ =>
          Ideal.absNorm (J : Ideal (𝓞 F))) ⁻¹' {n}, ‖idealTerm f s I‖)
        (fun n => tsum_nonneg fun I => norm_nonneg _) (fun n => ?_) hcountNorm
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by
        ext I
        simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      rw [← coe_normFiber, Finset.tsum_subtype' (normFiber F n)
        (fun I => ‖idealTerm f s I‖)]
      exact hfiber n
  exact summable_norm_iff.mp hnorm
open scoped nonZeroDivisors in
open ArtinPrimitiveRoots.Hecke.EulerProduct in
theorem reciprocal_incompleteHeckeLSeries_eq_complete_factors
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (s : ℂ) (hs : 1 < s.re) :
    incompleteHeckeLSeries S χ s = heckeLSeries χ s *
      ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  have hmul (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
      χ.idealValue (I * J) = χ.idealValue I * χ.idealValue J := by
    simp only [HeckeChar.idealValue,
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
      Multiset.map_add, Multiset.prod_add]
  have hone : χ.idealValue (1 : Ideal (𝓞 F)) = 1 := by
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  have hprime (v : FinPlace F) : χ.idealValue v.asIdeal = χ.primeValue v := by
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible, normalize_eq]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    by_cases h : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥
    · simp [h]
    · exact (h ⟨v.isPrime, v.ne_bot⟩).elim
  have hpow (v : FinPlace F) (n : ℕ) :
      χ.idealValue (v.asIdeal ^ n) = χ.primeValue v ^ n := by
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ v.ne_bot) v.ne_bot, ih, hprime, pow_succ]
  have hf : f.IsMultiplicative := by
    refine ⟨hone, ?_⟩
    intro I J hIJ
    change χ.idealValue ((I : Ideal (𝓞 F)) * (J : Ideal (𝓞 F))) = _
    exact hmul _ _ (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      (mem_nonZeroDivisors_iff_ne_zero.mp J.property)
  have hsum : Summable (idealTerm f s) := finiteOrder_idealTerm_summable χ hχ s hs
  have hratio (P : FinPlace F) :
      ‖χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    have hN : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hNreal : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by exact_mod_cast hN
    have hnormPow : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hN)]
      rfl
    rw [norm_mul, hnormPow]
    calc
      _ ≤ 1 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (reciprocal_primeValue_norm_le_one χ hχ P) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hNreal (by linarith)
  have hfactor (P : FinPlace F) : eulerFactor f P s =
      (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ := by
    rw [eulerFactor_eq_tsum]
    have hpowRatio (n : ℕ) : idealTerm f s (P.primeIdealPow n) =
        (χ.primeValue P / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ n := by
      dsimp only [idealTerm, f]
      rw [P.absNorm_primeIdealPow, P.coe_primeIdealPow,
        hpow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.cpow_nat_mul, div_pow]
    have hterm (n : ℕ) : idealTerm f s (P.primeIdealPow n) =
        (χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ n := by
      rw [hpowRatio, div_eq_mul_inv, Complex.cpow_neg]
    rw [tsum_congr hterm]
    exact tsum_geometric_of_norm_lt_one (hratio P)
  let e : (Ideal (𝓞 F))⁰ ≃ {I : Ideal (𝓞 F) // I ≠ ⊥} := {
    toFun := fun I => ⟨(I : Ideal (𝓞 F)), mem_nonZeroDivisors_iff_ne_zero.mp I.property⟩
    invFun := fun I => ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2⟩
    left_inv := fun I => Subtype.ext rfl
    right_inv := fun I => Subtype.ext rfl }
  have hseries : LSeries (normCoeff F f) s = heckeLSeries χ s := by
    rw [LSeries_normCoeff hsum]
    unfold heckeLSeries
    calc
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, idealTerm f s (e.symm I) :=
        Equiv.tsum_eq e (fun I => idealTerm f s (e.symm I))
      _ = _ := by
        apply tsum_congr
        intro I
        change χ.idealValue I.1 / (Ideal.absNorm I.1 : ℂ) ^ s =
          χ.idealValue I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)
        rw [div_eq_mul_inv, Complex.cpow_neg]
  let g := IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
  have hgsum : Summable (idealTerm g s) := summable_idealTerm_supportedPart hsum _
  have hprimeTo (I : Ideal (𝓞 F)) :
      Ideal.IsPrimeTo I (S.Sf : Set (FinPlace F)) ↔
        I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal := by
    simp only [Ideal.isPrimeTo_iff, Finset.mem_coe, Ideal.dvd_iff_le]
  let ep : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F))
      (S.Sf : Set (FinPlace F))} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal} := {
    toFun := fun I => ⟨(I.1 : Ideal (𝓞 F)), (hprimeTo _).mp I.2⟩
    invFun := fun I => ⟨⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩,
      (hprimeTo _).mpr I.2⟩
    left_inv := fun I => Subtype.ext (Subtype.ext rfl)
    right_inv := fun I => Subtype.ext rfl }
  have hgseries : LSeries (normCoeff F g) s = incompleteHeckeLSeries S χ s := by
    rw [LSeries_normCoeff hgsum]
    change (∑' I : (Ideal (𝓞 F))⁰, idealTerm
      (IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ) s I) = _
    rw [idealTerm_supportedPart]
    simp only [compl_compl]
    rw [← tsum_subtype]
    unfold incompleteHeckeLSeries
    calc
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal},
          idealTerm f s (ep.symm I).1 :=
        Equiv.tsum_eq ep (fun I => idealTerm f s (ep.symm I).1)
      _ = _ := by
        apply tsum_congr
        intro I
        change χ.idealValue I.1 / (Ideal.absNorm I.1 : ℂ) ^ s =
          χ.idealValue I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)
        rw [div_eq_mul_inv, Complex.cpow_neg]
  have hmask (P : FinPlace F) : eulerFactor g P s =
      if P ∈ S.Sf then 1 else eulerFactor f P s := by
    by_cases hP : P ∈ S.Sf
    · rw [if_pos hP, eulerFactor_eq_tsum]
      have hterm (n : ℕ) : idealTerm g s (P.primeIdealPow n) =
          if n = 0 then 1 else 0 := by
        by_cases hn : n = 0
        · subst n
          have htop : χ.idealValue (⊤ : Ideal (𝓞 F)) = 1 := by
            simpa only [Ideal.one_eq_top] using hone
          simp [idealTerm_def, g, f, htop]
        · rw [if_neg hn, idealTerm_def]
          have hnot : ¬ Ideal.IsPrimeTo (P.asIdeal ^ n) (S.Sf : Set (FinPlace F)) := by
            rw [Ideal.isPrimeTo_pow_iff hn, Ideal.isPrimeTo_asIdeal_iff]
            simpa using hP
          have hnot' : ¬ Ideal.IsPrimeTo
              ((P.primeIdealPow n : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F))
              (S.Sf : Set (FinPlace F))ᶜᶜ := by
            simpa only [P.coe_primeIdealPow, compl_compl] using hnot
          change IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
            (P.primeIdealPow n) / _ = 0
          rw [IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl hnot',
            zero_div]
      rw [tsum_congr hterm]
      simp
    · rw [if_neg hP, eulerFactor_eq_tsum, eulerFactor_eq_tsum]
      apply tsum_congr
      intro n
      have hpt : Ideal.IsPrimeTo (P.asIdeal ^ n) (S.Sf : Set (FinPlace F)) :=
        (Ideal.isPrimeTo_asIdeal_iff.mpr hP).pow n
      rw [idealTerm_def, idealTerm_def]
      change IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
        (P.primeIdealPow n) / _ = _
      rw [IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
        (by simpa only [P.coe_primeIdealPow, compl_compl] using hpt)]
  have hfinite : HasProd ((S.Sf : Set (FinPlace F)).mulIndicator
      (fun P => eulerFactor f P s)) (∏ P ∈ S.Sf, eulerFactor f P s) :=
    hasProd_subtype_iff_mulIndicator.mp (S.Sf.hasProd (fun P => eulerFactor f P s))
  have hmasked := hasProd_eulerFactor g (hf.supportedPart _) hgsum
  have hfull := hasProd_eulerFactor f hf hsum
  have hproduct := hmasked.mul hfinite
  have hid : (fun P : FinPlace F => eulerFactor g P s *
      (S.Sf : Set (FinPlace F)).mulIndicator (fun P => eulerFactor f P s) P) =
      (fun P => eulerFactor f P s) := by
    funext P
    by_cases hP : P ∈ S.Sf
    · simp [hmask, hP, Set.mulIndicator_of_mem]
    · simp [hmask, hP, Set.mulIndicator_of_notMem]
  rw [hid] at hproduct
  have hrel := hfull.unique hproduct
  have hnonzero (P : FinPlace F) :
      1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have hh := hratio P
    rw [← heq] at hh
    norm_num at hh
  have hcancel : (∏ P ∈ S.Sf, eulerFactor f P s) *
      (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro P hP
    rw [hfactor]
    exact inv_mul_cancel₀ (hnonzero P)
  rw [← hgseries, ← hseries]
  calc
    _ = LSeries (normCoeff F g) s * 1 := (mul_one _).symm
    _ = LSeries (normCoeff F g) s * ((∏ P ∈ S.Sf, eulerFactor f P s) *
        (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)))) := by
      rw [hcancel]
    _ = (LSeries (normCoeff F g) s * (∏ P ∈ S.Sf, eulerFactor f P s)) *
        (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [← hrel]


end ArtinPrimitiveRoots.Proofs.A2FreqP
