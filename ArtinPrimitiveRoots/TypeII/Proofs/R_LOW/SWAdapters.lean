import ArtinPrimitiveRoots.Ext.TypeIIInputs

namespace ArtinPrimitiveRoots.Proofs.RImplP.RLow

open Classical MeasureTheory intervalIntegral Finset

noncomputable def swPrimeInterval (l r : ℝ) : Finset ℕ :=
  (Finset.range (⌊r⌋₊ + 1)).filter fun p =>
    p.Prime ∧ l ≤ (p : ℝ) ∧ (p : ℝ) ≤ r

noncomputable def swPrimeOpenInterval (l r : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊l⌋₊ ⌊r⌋₊).filter Nat.Prime

theorem swPrimeOpen_subset_closed (l r : ℝ) (hr : 0 ≤ r) :
    swPrimeOpenInterval l r ⊆ swPrimeInterval l r := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpI, hpPrime⟩
  rcases Finset.mem_Ioc.mp hpI with ⟨hfloorL, hfloorR⟩
  have hfloorSucc : ⌊l⌋₊ + 1 ≤ p := Nat.succ_le_of_lt hfloorL
  have hlpNat : l < ((⌊l⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one l
  have hlp : l ≤ (p : ℝ) := by
    exact hlpNat.le.trans (by exact_mod_cast hfloorSucc)
  have hpR' : (p : ℝ) ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast hfloorR
  have hpR : (p : ℝ) ≤ r := hpR'.trans (Nat.floor_le hr)
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hpR)), hpPrime, hlp, hpR⟩

theorem swPrimeInterval_sdiff_card_le_one (l r : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r) :
    (swPrimeInterval l r \ swPrimeOpenInterval l r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  apply Nat.cast_injective (R := ℝ)
  have hpClosed := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have hqClosed := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
  have hpLower := hpClosed.2.1
  have hqLower := hqClosed.2.1
  have hpUpperNat : p ≤ ⌊r⌋₊ := Nat.le_floor hpClosed.2.2
  have hqUpperNat : q ≤ ⌊r⌋₊ := Nat.le_floor hqClosed.2.2
  have hpNot : p ∉ swPrimeOpenInterval l r := (Finset.mem_sdiff.mp hp).2
  have hqNot : q ∉ swPrimeOpenInterval l r := (Finset.mem_sdiff.mp hq).2
  have hpFloor : p ≤ ⌊l⌋₊ := by
    by_contra h
    have hlt : ⌊l⌋₊ < p := Nat.lt_of_not_ge h
    exact hpNot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlt, hpUpperNat⟩,
      hpClosed.1⟩)
  have hqFloor : q ≤ ⌊l⌋₊ := by
    by_contra h
    have hlt : ⌊l⌋₊ < q := Nat.lt_of_not_ge h
    exact hqNot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlt, hqUpperNat⟩,
      hqClosed.1⟩)
  have hpCast : (p : ℝ) ≤ (⌊l⌋₊ : ℝ) := by exact_mod_cast hpFloor
  have hqCast : (q : ℝ) ≤ (⌊l⌋₊ : ℝ) := by exact_mod_cast hqFloor
  have hpEq : (p : ℝ) = l := le_antisymm (hpCast.trans (Nat.floor_le hl)) hpLower
  have hqEq : (q : ℝ) = l := le_antisymm (hqCast.trans (Nat.floor_le hl)) hqLower
  exact hpEq.trans hqEq.symm

theorem swPrimeInterval_sum_split (f : ℕ → ℂ) (l r : ℝ) (hr : 0 ≤ r) :
    (∑ p ∈ swPrimeInterval l r, f p) =
      (∑ p ∈ swPrimeOpenInterval l r, f p) +
        ∑ p ∈ swPrimeInterval l r \ swPrimeOpenInterval l r, f p := by
  have hsub := swPrimeOpen_subset_closed l r hr
  have hunion : swPrimeOpenInterval l r ∪
      (swPrimeInterval l r \ swPrimeOpenInterval l r) = swPrimeInterval l r :=
    Finset.union_sdiff_of_subset hsub
  have hdisj : Disjoint (swPrimeOpenInterval l r)
      (swPrimeInterval l r \ swPrimeOpenInterval l r) := by
    rw [Finset.disjoint_left]
    intro p hp hpsdiff
    exact (Finset.mem_sdiff.mp hpsdiff).2 hp
  calc
    _ = ∑ p ∈ swPrimeOpenInterval l r ∪
          (swPrimeInterval l r \ swPrimeOpenInterval l r), f p := by
      conv_lhs => rw [← hunion]
    _ = _ := Finset.sum_union hdisj

theorem eventually_const_mul_log_rpow_le_x_rpow
    (a b K : ℝ) (hb : 0 < b) (hK : 0 < K) :
    ∀ᶠ x : ℝ in Filter.atTop,
      K * Real.rpow (Real.log x) a ≤ Real.rpow x b := by
  have hlittle := isLittleO_log_rpow_rpow_atTop a hb
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.rpow (Real.log x) a‖ ≤ (1 / K) * ‖Real.rpow x b‖ :=
    hlittle.bound (by positivity)
  filter_upwards [hbound, Filter.eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hright : 0 ≤ Real.rpow x b := Real.rpow_nonneg (by linarith) b
  have hnum : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog a
  have hbound' : Real.rpow (Real.log x) a ≤ (1 / K) * Real.rpow x b := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnum, abs_of_nonneg hright] using hx
  calc
    K * Real.rpow (Real.log x) a ≤ K * ((1 / K) * Real.rpow x b) :=
      mul_le_mul_of_nonneg_left hbound' hK.le
    _ = Real.rpow x b := by field_simp [ne_of_gt hK]

theorem eventually_rpow_ge_const (a K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in Filter.atTop, K ≤ Real.rpow x a := by
  have hlim : Filter.Tendsto (fun x : ℝ => Real.rpow x a)
      Filter.atTop Filter.atTop := tendsto_rpow_atTop ha
  exact hlim.eventually_ge_atTop K

theorem eventually_log_ge_const (K : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, K ≤ Real.log x :=
  Real.tendsto_log_atTop.eventually_ge_atTop K

theorem sw_threshold (γ A₀ A₂ xsw : ℝ) (hγ : 0 < γ)
    (_hA₀ : 0 < A₀) (_hA₂ : 0 < A₂) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 ≤ x ∧ max (2 * xsw) 4 ≤ Real.rpow x γ ∧
        Real.rpow (Real.log x) A₀ ≤ Real.rpow x (γ / 4) ∧
        4 ≤ Real.rpow x (γ / 2) ∧
        Real.sqrt 2 * (8 / Real.log 2) * Real.rpow (Real.log x) (A₂ + 1) ≤
          Real.rpow x (γ / 4) ∧
        2 * Real.rpow (Real.log x) A₂ ≤ Real.rpow x γ ∧
        (2 * Real.log 2 / γ ≤ Real.log x ∧
          1 / (γ / 2) ≤ Real.log x ∧
          1 / Real.rpow (γ / 2) (A₀ + 1) ≤ Real.log x ∧
          Real.log 4 ≤ Real.log x) := by
  let Bsw := A₀ + 1
  let c := γ / 2
  let Ktail := 8 / Real.log 2
  let L₀ := max (2 * Real.log 2 / γ)
    (max (1 / c) (max (1 / Real.rpow c Bsw) (Real.log 4)))
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop,
      2 ≤ x ∧ max (2 * xsw) 4 ≤ Real.rpow x γ ∧
        Real.rpow (Real.log x) A₀ ≤ Real.rpow x (γ / 4) ∧
        4 ≤ Real.rpow x (γ / 2) ∧
        Real.sqrt 2 * Ktail * Real.rpow (Real.log x) (A₂ + 1) ≤
          Real.rpow x (γ / 4) ∧
        2 * Real.rpow (Real.log x) A₂ ≤ Real.rpow x γ ∧
        L₀ ≤ Real.log x := by
    filter_upwards
      [Filter.eventually_ge_atTop (2 : ℝ),
        eventually_rpow_ge_const γ (max (2 * xsw) 4) hγ,
        eventually_const_mul_log_rpow_le_x_rpow A₀ (γ / 4) 1
          (by positivity) (by norm_num),
        eventually_rpow_ge_const (γ / 2) 4 (by positivity),
        eventually_const_mul_log_rpow_le_x_rpow (A₂ + 1) (γ / 4)
          (Real.sqrt 2 * Ktail) (by positivity) (by positivity),
        eventually_const_mul_log_rpow_le_x_rpow A₂ γ 2 hγ (by norm_num),
        eventually_log_ge_const L₀] with x hx₂ hY hmod hhalf htail hend hlog
    exact ⟨hx₂, hY, by simpa only [one_mul] using hmod,
      hhalf, htail, hend, hlog⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hlarge
  let x₀ := max 2 x₁
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx
  have hxlarge := hx₁ x ((le_max_right 2 x₁).trans hx)
  rcases hxlarge with ⟨hx₂, hY, hmod, hhalf, htail, hend, hlog⟩
  have hLbounds :
      (2 * Real.log 2 / γ ≤ Real.log x) ∧
        (1 / (γ / 2) ≤ Real.log x) ∧
        (1 / Real.rpow (γ / 2) (A₀ + 1) ≤ Real.log x) ∧
        (Real.log 4 ≤ Real.log x) := by
    have hmax : L₀ ≤ Real.log x := by simpa [L₀, c, Bsw] using hlog
    have h₁ : 2 * Real.log 2 / γ ≤ L₀ := le_max_left _ _
    have h₂ : 1 / (γ / 2) ≤ L₀ :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h₃ : 1 / Real.rpow (γ / 2) (A₀ + 1) ≤ L₀ := by
      calc
        _ ≤ max (1 / c) (max (1 / Real.rpow c Bsw) (Real.log 4)) :=
          le_max_of_le_right (le_max_left _ _)
        _ ≤ L₀ := le_max_of_le_right le_rfl
    have h₄ : Real.log 4 ≤ L₀ := by
      calc
        _ ≤ max (1 / Real.rpow c Bsw) (Real.log 4) := le_max_right _ _
        _ ≤ max (1 / c) (max (1 / Real.rpow c Bsw) (Real.log 4)) :=
          le_max_of_le_right le_rfl
        _ ≤ L₀ := le_max_of_le_right le_rfl
    exact ⟨h₁.trans hmax, h₂.trans hmax, h₃.trans hmax, h₄.trans hmax⟩
  exact ⟨hx₂, hY, hmod, hhalf, htail, hend, hLbounds⟩

theorem inv_log_hasDerivAt (y : ℝ) (hy : 2 ≤ y) :
    HasDerivAt (fun t : ℝ => (Real.log t)⁻¹)
      (-y⁻¹ / (Real.log y) ^ 2) y := by
  apply Real.hasDerivAt_inv_log <;> linarith

theorem inv_log_complex_hasDerivAt (y : ℝ) (hy : 2 ≤ y) :
    HasDerivAt (fun t : ℝ => ((Real.log t)⁻¹ : ℂ))
      ((-y⁻¹ / (Real.log y) ^ 2 : ℝ) : ℂ) y := by
  convert (inv_log_hasDerivAt y hy).ofReal_comp using 1 <;> simp

theorem eventually_log_rpow_le_rpow (a b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.rpow (Real.log x) a ≤ Real.rpow x b := by
  have hlittle := isLittleO_log_rpow_rpow_atTop a hb
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.rpow (Real.log x) a‖ ≤ ‖Real.rpow x b‖ := by
    have h := hlittle.bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h] with x hx
    simpa using hx
  filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hleft : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog a
  have hright : 0 ≤ Real.rpow x b := Real.rpow_nonneg (by linarith) b
  have habs : |Real.rpow (Real.log x) a| ≤ |Real.rpow x b| := by
    simpa only [Real.norm_eq_abs] using hx
  rw [abs_of_nonneg hleft, abs_of_nonneg hright] at habs
  exact habs

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

/-- Abel summation for a complex sequence with a uniform linear prefix estimate. -/
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

end ArtinPrimitiveRoots.Proofs.RImplP.RLow
