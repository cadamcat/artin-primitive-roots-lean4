import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.TypeII.PP.Defs
import OAI.NumberTheory.PrimeGaps.CharacterErrors
import OAI.NumberTheory.PrimeGaps.Main

/-! Conductor reductions used in the rough-factor Siegel–Walfisz slot. -/

namespace ArtinPrimitiveRoots.TypeII.RoughProofs

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open MeasureTheory

theorem natLogTwo_le_realLog (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

theorem eventually_log_rpow_le_rpow (a b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ a ≤ x ^ b := by
  have hlittle := Real.isLittleO_log_rpow_rpow_atTop a hb
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x ^ a‖ ≤ 1 * ‖x ^ b‖ := hlittle.bound (by norm_num)
  filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hleft : 0 ≤ Real.log x ^ a := Real.rpow_nonneg hlog a
  have hright : 0 ≤ x ^ b := Real.rpow_nonneg (by linarith) b
  have habs : |Real.log x ^ a| ≤ |x ^ b| := by
    simpa only [Real.norm_eq_abs, one_mul] using hx
  rw [abs_of_nonneg hleft, abs_of_nonneg hright] at habs
  exact habs

theorem complex_partial_summation_error
    (c : ℕ → ℂ) (f f' : ℝ → ℂ) (δ : ℂ)
    {a b E M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf'cont : ContinuousOn f' (Set.Icc a b))
    (hfBound : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ M)
    (hf'Bound : ∀ t ∈ Set.Icc a b, ‖f' t‖ ≤ N)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - δ * (t : ℂ)‖ ≤ E) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) -
        δ * (∫ t in a..b, f t)‖ ≤ E * (2 * M + N * (b - a)) := by
  classical
  let S : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n
  let R : ℝ → ℂ := fun t => S t - δ * (t : ℂ)
  have hfcont : ContinuousOn f (Set.Icc a b) := by
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hf'Int : IntervalIntegrable f' volume a b :=
    hf'cont.intervalIntegrable_of_Icc hab
  have hderivCont : ContinuousOn (deriv f) (Set.Icc a b) :=
    hf'cont.congr (fun t ht => (hf t ht).deriv)
  have hderivEq (t : ℝ) (ht : t ∈ Set.Icc a b) : deriv f t = f' t :=
    (hf t ht).deriv
  have hIdCont : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Icc a b) :=
    Complex.continuous_ofReal.continuousOn
  have hIdInt : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a b :=
    intervalIntegrable_const
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (u := f) (u' := f') (v := fun t : ℝ => (t : ℂ)) (v' := fun _ => (1 : ℂ))
    (fun t ht => by
      have ht' : t ∈ Set.Icc a b := by rw [← Set.uIcc_of_le hab]; exact ht
      exact hf t ht')
    (fun t ht => by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasDerivAt (x := t)) hf'Int hIdInt
  have hprodCont : ContinuousOn (fun t : ℝ => f' t * (t : ℂ)) (Set.Icc a b) :=
    hf'cont.mul hIdCont
  have hprodInt : IntervalIntegrable (fun t : ℝ => f' t * (t : ℂ)) volume a b :=
    hprodCont.intervalIntegrable_of_Icc hab
  have hfInt : IntervalIntegrable f volume a b := hfcont.intervalIntegrable_of_Icc hab
  simp only [mul_one] at hparts
  rw [intervalIntegral.integral_add hprodInt hfInt] at hparts
  have hparts' : (∫ t in a..b, f t) =
      f b * (b : ℂ) - f a * (a : ℂ) - ∫ t in a..b, f' t * (t : ℂ) := by
    linear_combination hparts
  have hscale : (∫ t in a..b, f' t * (δ * (t : ℂ))) =
      δ * (∫ t in a..b, f' t * (t : ℂ)) := by
    rw [show (fun t : ℝ => f' t * (δ * (t : ℂ))) =
        fun t => δ * (f' t * (t : ℂ)) from by funext t; ring,
      intervalIntegral.integral_const_mul]
  have hmain :
      f b * (δ * (b : ℂ)) - f a * (δ * (a : ℂ)) -
          ∫ t in a..b, f' t * (δ * (t : ℂ)) =
        δ * (∫ t in a..b, f t) := by
    rw [hscale, hparts']
    ring
  have hSInt : IntervalIntegrable (fun t : ℝ => f' t * S t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc c ha hf'cont.integrableOn_Icc
  have hmainCont : ContinuousOn
      (fun t : ℝ => f' t * (δ * (t : ℂ))) (Set.Icc a b) :=
    hf'cont.mul (continuousOn_const.mul hIdCont)
  have hmainInt : IntervalIntegrable
      (fun t : ℝ => f' t * (δ * (t : ℂ))) volume a b :=
    hmainCont.intervalIntegrable_of_Icc hab
  have hIntSplit :
      (∫ t in a..b, f' t * S t) -
          ∫ t in a..b, f' t * (δ * (t : ℂ)) =
        ∫ t in a..b, f' t * R t := by
    rw [← intervalIntegral.integral_sub hSInt hmainInt]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [R, S]
    ring
  have hAbel := sum_mul_eq_sub_sub_integral_mul
    (c := c) ha hab (fun t ht => (hf t ht).differentiableAt) hderivCont.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  have hAbel' :
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
        f b * S b - f a * S a - ∫ t in a..b, f' t * S t := by
    calc
      _ = f b * S b - f a * S a - ∫ t in a..b, deriv f t * S t := hAbel
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc a b := by rw [← Set.uIcc_of_le hab]; exact ht
        change deriv f t * S t = f' t * S t
        rw [hderivEq t ht']
  have herrorEq :
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) -
          δ * (∫ t in a..b, f t) =
        f b * R b - f a * R a - ∫ t in a..b, f' t * R t := by
    rw [hAbel']
    have hSb : S b = R b + δ * (b : ℂ) := by dsimp [R]; ring
    have hSa : S a = R a + δ * (a : ℂ) := by dsimp [R]; ring
    have hInt : (∫ t in a..b, f' t * S t) =
        (∫ t in a..b, f' t * (δ * (t : ℂ))) +
          ∫ t in a..b, f' t * R t := by linear_combination hIntSplit
    rw [hSb, hSa, hInt]
    linear_combination hmain
  have hIntBound : ‖∫ t in a..b, f' t * R t‖ ≤ N * E * (b - a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t : ℝ => f' t * R t) (C := N * E)
      (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [norm_mul]
        exact mul_le_mul (hf'Bound t ht') (hprefix t ht')
          (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hEnd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖f t * R t‖ ≤ M * E := by
    rw [norm_mul]
    exact mul_le_mul (hfBound t ht) (hprefix t ht) (norm_nonneg _) hM
  rw [herrorEq]
  calc
    ‖f b * R b - f a * R a - ∫ t in a..b, f' t * R t‖ ≤
        ‖f b * R b‖ + ‖f a * R a‖ + ‖∫ t in a..b, f' t * R t‖ := by
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M * E + M * E + N * E * (b - a) :=
      add_le_add (add_le_add (hEnd b ⟨hab, le_rfl⟩) (hEnd a ⟨le_rfl, hab⟩)) hIntBound
    _ = E * (2 * M + N * (b - a)) := by ring

noncomputable def tupleFromList {j : ℕ} (l : List ℕ) (h : l.length = j) : Fin j → ℕ :=
  fun i => l.get (Fin.cast h.symm i)

theorem ofFn_tupleFromList {j : ℕ} (l : List ℕ) (h : l.length = j) :
    List.ofFn (tupleFromList l h) = l := by
  cases h
  rw [show tupleFromList l rfl = l.get from by
    funext i
    simp [tupleFromList]]
  exact List.ofFn_get l

theorem mem_boundedTuples_of_forall_le {j B : ℕ} (t : Fin j → ℕ)
    (ht : ∀ i, t i ≤ B) : t ∈ boundedTuples j B := by
  classical
  unfold boundedTuples
  refine Finset.mem_image.mpr ⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i)⟩,
    Finset.mem_univ _, ?_⟩
  funext i
  rfl

theorem tuple_product_perm_factors {j m : ℕ} (t : Fin j → ℕ)
    (ht : ∀ i, (t i).Prime) (hprod : (∏ i : Fin j, t i) = m) :
    List.Perm (List.ofFn t) m.primeFactorsList := by
  have hlistprod : (List.ofFn t).prod = m := by
    simpa only [List.prod_ofFn] using hprod
  have hprime : ∀ p ∈ List.ofFn t, p.Prime := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ht i
  exact Nat.primeFactorsList_unique hlistprod hprime

noncomputable def primeTupleFiber (j B m : ℕ) : Finset (Fin j → ℕ) :=
  (boundedTuples j B).filter fun t =>
    (∀ i, (t i).Prime) ∧ (∏ i : Fin j, t i) = m

theorem primeTupleFiber_card_le_factorial (j B m : ℕ) :
    (primeTupleFiber j B m).card ≤ j.factorial := by
  classical
  let l := m.primeFactorsList
  by_cases hj : j = l.length
  · subst j
    have himage : (primeTupleFiber l.length B m).image List.ofFn ⊆ l.permutations.toFinset := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨t, ht, rfl⟩
      rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
      have hperm := tuple_product_perm_factors t hprop.1 hprop.2
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
    calc
      _ = ((primeTupleFiber l.length B m).image List.ofFn).card := by
        symm
        exact Finset.card_image_of_injective _ List.ofFn_injective
      _ ≤ l.permutations.toFinset.card := Finset.card_le_card himage
      _ ≤ l.permutations.length := List.toFinset_card_le _
      _ = l.length.factorial := List.length_permutations _
      _ = l.length.factorial := rfl
  · have hempty : primeTupleFiber j B m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
      have hperm := tuple_product_perm_factors t hprop.1 hprop.2
      have hlen : j = l.length := by simpa [l] using hperm.length_eq
      exact hj hlen
    simp [hempty]

theorem primeTupleFiber_eq_empty_of_factor_length_ne {j B m : ℕ}
    (hj : j ≠ m.primeFactorsList.length) : primeTupleFiber j B m = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
  have hperm := tuple_product_perm_factors t hprop.1 hprop.2
  have hlen : j = m.primeFactorsList.length := by simpa using hperm.length_eq
  exact hj hlen

theorem primeTupleFiber_card_eq_factorial_of_squarefree
    (j B m : ℕ) (hm0 : m ≠ 0) (hmSq : Squarefree m)
    (hj : j = m.primeFactorsList.length)
    (hB : ∀ p ∈ m.primeFactorsList, p ≤ B) :
    (primeTupleFiber j B m).card = j.factorial := by
  classical
  subst j
  let l := m.primeFactorsList
  let P := l.permutations.toFinset
  have hn : l.Nodup := by simpa [l] using hmSq.nodup_primeFactorsList
  have hpermNodup : l.permutations.Nodup := List.nodup_permutations l hn
  have himage₁ : (primeTupleFiber l.length B m).image List.ofFn ⊆ P := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨t, ht, rfl⟩
    rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
    have hperm := tuple_product_perm_factors t hprop.1 hprop.2
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
  have himage₂ : P ⊆ (primeTupleFiber l.length B m).image List.ofFn := by
    intro q hq
    have hqperm : q ∈ l.permutations := List.mem_toFinset.mp hq
    have hperm : List.Perm q l := List.mem_permutations.mp hqperm
    have hlen : q.length = l.length := hperm.length_eq
    let t := tupleFromList q hlen
    have hlist : List.ofFn t = q := ofFn_tupleFromList q hlen
    have hprimeList : ∀ p ∈ q, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (hperm.mem_iff.mp hp)
    have hprodList : q.prod = m := by
      calc
        q.prod = l.prod := hperm.prod_eq
        _ = m := by simpa [l] using Nat.prod_primeFactorsList hm0
    have htPrime : ∀ i, (t i).Prime := by
      intro i
      exact hprimeList _ (List.get_mem q (Fin.cast hlen.symm i))
    have htBound : ∀ i, t i ≤ B := by
      intro i
      have hqmem : q.get (Fin.cast hlen.symm i) ∈ q :=
        List.get_mem q (Fin.cast hlen.symm i)
      have hfactor : t i ∈ m.primeFactorsList := by
        simpa [t, tupleFromList, l] using hperm.mem_iff.mp hqmem
      exact hB (t i) hfactor
    have htProd : (∏ i : Fin l.length, t i) = m := by
      rw [← List.prod_ofFn, hlist]
      exact hprodList
    have htMem : t ∈ primeTupleFiber l.length B m := by
      unfold primeTupleFiber
      apply Finset.mem_filter.mpr
      exact ⟨mem_boundedTuples_of_forall_le t htBound, htPrime, htProd⟩
    exact Finset.mem_image.mpr ⟨t, htMem, hlist⟩
  have hImage : (primeTupleFiber l.length B m).image List.ofFn = P :=
    Finset.Subset.antisymm himage₁ himage₂
  calc
    (primeTupleFiber l.length B m).card =
        ((primeTupleFiber l.length B m).image List.ofFn).card := by
          symm
          exact Finset.card_image_of_injective _ List.ofFn_injective
    _ = P.card := congrArg Finset.card hImage
    _ = l.permutations.length := by
      dsimp [P]
      exact List.toFinset_card_of_nodup hpermNodup
    _ = l.length.factorial := List.length_permutations l
    _ = m.primeFactorsList.length.factorial := rfl

theorem nonprime_vonMangoldt_div_log_bound (X : ℝ) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊ with ¬n.Prime,
      ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) ≤
      2 * Real.sqrt X * Real.log X / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterms :
      (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊ with ¬n.Prime,
        ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) ≤
      (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊ with ¬n.Prime,
        ArithmeticFunction.vonMangoldt n) / Real.log 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnnp⟩
    have hnpos : 1 ≤ n := by exact (Finset.mem_Ioc.mp hnI).1
    by_cases hn1 : n = 1
    · simp [hn1]
    · have hn2 : 2 ≤ n := by omega
      have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hlog2 hlogn
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime X] at hterms
  have hcheb := Chebyshev.psi_sub_theta_le (x := X) (by linarith)
  exact hterms.trans (div_le_div_of_nonneg_right hcheb hlog2.le)

theorem prime_coprime_of_lt {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p) :
    Nat.Coprime p k := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  exact (not_le_of_gt hkp) (Nat.le_of_dvd hkpos hdiv)

theorem primitive_eq_one_iff (k : ℕ) (hk : 1 ≤ k)
    (χ : DirichletCharacter ℂ k) : χ.primitiveCharacter = 1 ↔ χ = 1 := by
  letI : NeZero k := ⟨by omega⟩
  have h := DirichletCharacter.changeLevel_eq_one_iff
    (χ := χ.primitiveCharacter) χ.conductor_dvd_level
  rw [χ.changeLevel_primitiveCharacter] at h
  exact h.symm

theorem primitive_eval_nat (k p : ℕ) (hk : 1 ≤ k) (χ : DirichletCharacter ℂ k)
    (hcop : Nat.Coprime p k) :
    χ.primitiveCharacter (p : ℤ) = χ (p : ℤ) := by
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  letI : NeZero k := ⟨ne_of_gt hkpos⟩
  have hlevel := χ.changeLevel_primitiveCharacter
  have heval := congrArg (fun ψ : DirichletCharacter ℂ k => ψ (p : ℤ)) hlevel
  have hcop' : IsCoprime (p : ℤ) k := Nat.isCoprime_iff_coprime.mpr hcop
  have hchange := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    (χ := χ.primitiveCharacter) χ.conductor_dvd_level (ha := hcop')
  calc
    χ.primitiveCharacter (p : ℤ) =
        (DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter) (p : ℤ) :=
      hchange.symm
    _ = χ (p : ℤ) := heval

theorem prime_square_count_bound (Y M : ℝ) (hY : 2 ≤ Y) (hM : 0 ≤ M) :
    (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
        (fun (p : ℕ) => Y < (p : ℝ)),
      (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤ 4 * M / Y := by
  classical
  let k := ⌊Y⌋₊
  let N := max k (⌊Real.sqrt (2 * M)⌋₊ + 1)
  have hYpos : 0 < Y := by linarith
  have hkCast : (k : ℝ) ≤ Y := by
    dsimp [k]
    exact Nat.floor_le (by linarith)
  have hlt : Y < (k + 1 : ℝ) := by
    dsimp [k]
    exact Nat.lt_floor_add_one Y
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk] at hlt
    norm_num at hlt
    linarith
  have hsub :
      (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ)) ⊆
        Finset.Ioo k N := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp0, hYp⟩
    rcases Finset.mem_filter.mp hp0 with ⟨hpR, hpPrime⟩
    have hpRange : p < ⌊Real.sqrt (2 * M)⌋₊ + 1 := by
      simpa [primesUpTo] using hpR
    have hkp : k < p := by
      by_contra h
      have hp_le_k : p ≤ k := Nat.le_of_not_gt h
      have hpCast : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp_le_k
      linarith
    have hpN : p < N := by
      apply lt_of_lt_of_le hpRange
      exact le_max_right _ _
    exact Finset.mem_Ioo.mpr ⟨hkp, hpN⟩
  let S := (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ))
  let T := Finset.Ioo k N
  have hpoint :
      (∑ p ∈ S, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤
        ∑ p ∈ S, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp0, hYp⟩
    rcases Finset.mem_filter.mp hp0 with ⟨hpR, hpPrime⟩
    have hpPrime' : p.Prime := by simpa [primesUpTo] using hpPrime
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime'.pos
    have hden : 0 < (p : ℝ) ^ 2 := by positivity
    have hquot : 0 ≤ 2 * M / (p : ℝ) ^ 2 := by positivity
    have hfloor : (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ 2 * M / (p : ℝ) ^ 2 :=
      Nat.floor_le hquot
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfloor
  have hsubsetSum :
      (∑ p ∈ S, (2 * M) * ((p : ℝ) ^ 2)⁻¹) ≤
        ∑ p ∈ T, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (show S ⊆ T from hsub)
    intro p hp hpT
    positivity
  have hsum :
      (∑ p ∈ S, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤
        ∑ p ∈ T, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := hpoint.trans hsubsetSum
  have htail := sum_Ioo_inv_sq_le (α := ℝ) k N
  have hscaled :
      ∑ p ∈ Finset.Ioo k N, (2 * M) * ((p : ℝ) ^ 2)⁻¹ ≤
        (2 * M) * (2 / (k + 1 : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have hden : (2 : ℝ) / (k + 1 : ℝ) ≤ 2 / Y :=
    div_le_div_of_nonneg_left (by norm_num) hYpos (le_of_lt hlt)
  calc
    _ ≤ ∑ p ∈ Finset.Ioo k N, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := hsum
    _ ≤ (2 * M) * (2 / (k + 1 : ℝ)) := hscaled
    _ ≤ (2 * M) * (2 / Y) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 4 * M / Y := by ring

end ArtinPrimitiveRoots.TypeII.RoughProofs
