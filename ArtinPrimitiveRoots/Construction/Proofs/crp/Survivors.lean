import ArtinPrimitiveRoots.Construction.Proofs.crp.Block
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! The per-group-integer survivor bound of `con_rough_pairs`: an
absolute constant `Csv` with `#survivors ≤ Csv·(x/r)·V(W)²/log x`, uniformly in the box, in
`c ∈ {2,4}` and in the group integer `r ≤ x^0.11`. -/

namespace ArtinPrimitiveRoots.Construction.Proofs.CRP

open Classical
open Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction.Proofs.C4

theorem roughSieveProduct_nonneg' (y : ℝ) : 0 ≤ roughSieveProduct y := by
  unfold roughSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  have h1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith

/-- The absolute scale conditions used by the survivor bound. -/
theorem crp_eventually_scales (y₀ : ℝ) : ∀ᶠ x : ℝ in atTop,
    2 ≤ x ∧ 1 ≤ Real.log x ∧ y₀ ≤ Real.rpow x (1 / 500 : ℝ) ∧ y₀ ≤ roughCutoff x ∧
      roughCutoff x ≤ Real.rpow x (1 / 500 : ℝ) ∧ 4 ≤ Real.rpow x (46 / 100 : ℝ) := by
  have h1 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h3 : ∀ᶠ x : ℝ in atTop, y₀ ≤ Real.rpow x (1 / 500 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 500)).eventually_ge_atTop y₀
  have hLpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (24 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 24 / 100)).comp Real.tendsto_log_atTop
  have h4 : ∀ᶠ x : ℝ in atTop, y₀ ≤ roughCutoff x :=
    (Real.tendsto_exp_atTop.comp hLpow).eventually_ge_atTop y₀
  have h5 : ∀ᶠ x : ℝ in atTop, (500 : ℝ) ≤ Real.rpow (Real.log x) (76 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 76 / 100)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop 500
  have h6 : ∀ᶠ x : ℝ in atTop, (4 : ℝ) ≤ Real.rpow x (46 / 100 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 46 / 100)).eventually_ge_atTop 4
  filter_upwards [h1, h2, h3, h4, h5, h6] with x hx2 hL hz hW hL76 h46
  refine ⟨hx2, hL, hz, hW, ?_, h46⟩
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hsplit : Real.rpow (Real.log x) (24 / 100 : ℝ) *
      Real.rpow (Real.log x) (76 / 100 : ℝ) = Real.log x := by
    rw [pairRpow_mul hLpos]
    rw [show (24 / 100 + 76 / 100 : ℝ) = 1 by norm_num]
    exact Real.rpow_one _
  have hA : 0 ≤ Real.rpow (Real.log x) (24 / 100 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hmul := mul_le_mul_of_nonneg_left hL76 hA
  have hexp : Real.rpow (Real.log x) (24 / 100 : ℝ) ≤ Real.log x * (1 / 500) := by
    linarith
  calc roughCutoff x = Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ)) := rfl
    _ ≤ Real.exp (Real.log x * (1 / 500)) := Real.exp_le_exp.mpr hexp
    _ = Real.rpow x (1 / 500 : ℝ) := (Real.rpow_def_of_pos hxpos _).symm

/-- The survivor bound for one group integer `r`. -/
theorem pairSurvivors_card_le :
    ∃ Csv : ℝ, 0 < Csv ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ H₁ H₂ : ℝ, H₁ * H₂ ≤ 2 * x →
        Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₁ → H₁ ≤ 2 * Real.rpow x (54 / 100 : ℝ) →
        Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₂ → H₂ ≤ 2 * Real.rpow x (54 / 100 : ℝ) →
      ∀ c : ℕ, (c = 2 ∨ c = 4) → ∀ r : ℕ, 0 < r → (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) →
        (∀ p ∈ (primesUpTo (Real.rpow x (1 / 500 : ℝ))).filter (fun p : ℕ => p ∣ r), 5 ≤ p) →
        (∑ p ∈ (primesUpTo (Real.rpow x (1 / 500 : ℝ))).filter (fun p : ℕ => p ∣ r),
            1 / (p : ℝ)) ≤ 1 →
        ((pairSieveSurvivors H₁ H₂ (c * r)
            ((primesUpTo (Real.rpow x (1 / 500 : ℝ))).filter
              (fun p : ℕ => 2 < p ∧ ¬ p ∣ r))
            (roughCutoff x)).card : ℝ) ≤
          Csv * (x / r) * roughSieveProduct (roughCutoff x) ^ 2 / Real.log x := by
  obtain ⟨Cb, hCb, hCbP⟩ := exists_reciprocalPrimeBlockBoundForPrimeSet
  obtain ⟨K, hK, hBlockU⟩ := pairSieveBlock_upper_uniform (2 / 9) (3 * Cb) (by norm_num)
  set E : ℝ := Real.exp (-Real.eulerMascheroniConstant) with hEdef
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨y₀, hy₀, hMert⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.2 (E / 2) (by positivity)
  obtain ⟨xA, hxA, hAbs⟩ :=
    eventually_power_error_absorbed 192 (E ^ 2 / 4) (by norm_num) (by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (crp_eventually_scales y₀)
  refine ⟨K * (6000 * Real.exp (6 + 1 / 2) * E + 1), by positivity,
    max (max x₁ xA) 2, le_max_right _ _, ?_⟩
  intro x hx H₁ H₂ hHprod hH₁lo hH₁hi hH₂lo hH₂hi c hc r hr0 hrx h5 hrecip
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxxA : xA ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  obtain ⟨hx2, hL1, hzy, hWy, hWz, hH4⟩ := hx₁ x hxx₁
  have hxpos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hAbsX := hAbs x hxxA
  -- names for the scales
  set L := Real.log x with hLdef
  set z := Real.rpow x (1 / 500 : ℝ) with hzdef
  set W := roughCutoff x with hWdef
  set P := (primesUpTo z).filter (fun p : ℕ => 2 < p ∧ ¬ p ∣ r) with hPdef
  set e : ℝ → ℝ := fun t => Real.rpow x t with hedef
  have he_mul : ∀ s t : ℝ, e s * e t = e (s + t) := fun s t => pairRpow_mul hxpos s t
  have he_mono : ∀ s t : ℝ, s ≤ t → e s ≤ e t := fun s t hst =>
    Real.rpow_le_rpow_of_exponent_le hx1 hst
  have he_pos : ∀ t : ℝ, 0 < e t := fun t => Real.rpow_pos_of_pos hxpos t
  have hLpos : 0 < L := by linarith
  have hy₀z : 2 < z := lt_of_lt_of_le hy₀ hzy
  have hz2 : 2 ≤ z := hy₀z.le
  have hW2 : 2 ≤ W := by linarith
  have hH₁2 : 2 ≤ H₁ := by linarith
  have hH₂2 : 2 ≤ H₂ := by linarith
  have hcpos : 0 < c := by rcases hc with h | h <;> omega
  have hk : 0 < c * r := Nat.mul_pos hcpos hr0
  have hz0 : 0 ≤ z := by linarith
  have hmemP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z ∧ 2 < p ∧ ¬ p ∣ r := by
    intro p hp
    simp only [hPdef, Finset.mem_filter, primesUpTo, Finset.mem_range] at hp
    obtain ⟨⟨hlt, hpp⟩, h2, hpr⟩ := hp
    exact ⟨hpp, (Nat.le_floor_iff hz0).mp (Nat.lt_succ_iff.mp hlt), h2, hpr⟩
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (hmemP p hp).1
  have hcop : ∀ p ∈ P, Nat.Coprime (c * r) p := by
    intro p hp
    obtain ⟨hpp, -, h2, hpr⟩ := hmemP p hp
    refine Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
      intro hpc
      have hc4 : c ∣ 4 := by rcases hc with h | h <;> subst h <;> norm_num
      have hp4 : p ∣ 2 ^ 2 := by simpa using dvd_trans hpc hc4
      have hp2' : p ∣ 2 := hpp.dvd_of_dvd_pow hp4
      have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2'
      omega
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
      exact hpr
  have hPz : ∀ p ∈ P, (p : ℝ) ≤ z := fun p hp => (hmemP p hp).2.1
  have hgb : ∀ p ∈ P, 0 ≤ pairSieveG W p ∧ pairSieveG W p ≤ 1 - 2 / 9 := by
    intro p hp
    have h3 : 3 ≤ p := (hmemP p hp).2.2.1
    obtain ⟨h0, h79, -⟩ := pairSieveG_bounds h3 W
    exact ⟨h0, by linarith⟩
  have hblock : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), pairSieveG W p ≤
        3 * Cb := by
    intro v hv
    exact pairSieveG_block_sum_le W Cb v
      (fun p hp => (pairSieveG_bounds (hmemP p hp).2.2.1 W).2.2) (hCbP P hprime v hv) hv
  have hmainB := hBlockU (c * r) P W H₁ H₂ z hk hprime hcop hz2 hPz hH₁2 hH₂2 hgb hblock
  -- the Euler product
  have hprod := pairSieveG_product_le W z r hW2 hWz h5 hrecip
  have hprodNonneg : 0 ≤ ∏ p ∈ P, (1 - pairSieveG W p) := by
    apply Finset.prod_nonneg
    intro p hp
    have := (hgb p hp).2
    linarith
  -- Mertens at both ends
  have hlogz : Real.log z = L / 500 := by
    rw [hzdef, show Real.rpow x (1 / 500 : ℝ) = x ^ (1 / 500 : ℝ) from rfl,
      Real.log_rpow hxpos]
    ring
  have hlogW : Real.log W = Real.rpow L (24 / 100 : ℝ) := by
    rw [hWdef, roughCutoff, Real.log_exp]
  have hVz : roughSieveProduct z ≤ 750 * E / L := by
    have h := (abs_le.mp (hMert z hzy)).2
    rw [hlogz] at h
    rw [le_div_iff₀ hLpos]
    have hre : roughSieveProduct z * L = 500 * (roughSieveProduct z * (L / 500)) := by ring
    linarith
  set ℓ := Real.rpow L (24 / 100 : ℝ) with hℓdef
  have hVW : E / 2 ≤ roughSieveProduct W * ℓ := by
    have h := (abs_le.mp (hMert W hWy)).1
    rw [hlogW] at h
    linarith
  have hℓpos : 0 < ℓ := Real.rpow_pos_of_pos hLpos _
  have hℓL : ℓ ≤ L := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (show (24 / 100 : ℝ) ≤ 1 by norm_num)
    have h1 : Real.rpow L (1 : ℝ) = L := Real.rpow_one L
    calc ℓ = Real.rpow L (24 / 100 : ℝ) := rfl
      _ ≤ Real.rpow L (1 : ℝ) := h
      _ = L := h1
  have hVWnn : 0 ≤ roughSieveProduct W := roughSieveProduct_nonneg' W
  have hVznn : 0 ≤ roughSieveProduct z := roughSieveProduct_nonneg' z
  -- lower bound `(E²/4)/L^10 ≤ V(W)²/L`
  have hVWsq : (E ^ 2 / 4) / L ^ 10 ≤ roughSieveProduct W ^ 2 / L := by
    have hsq : E ^ 2 / 4 ≤ roughSieveProduct W ^ 2 * ℓ ^ 2 := by
      have h0 : 0 ≤ E / 2 := by positivity
      have hm := mul_le_mul hVW hVW h0 (by positivity)
      calc E ^ 2 / 4 = (E / 2) * (E / 2) := by ring
        _ ≤ (roughSieveProduct W * ℓ) * (roughSieveProduct W * ℓ) := hm
        _ = roughSieveProduct W ^ 2 * ℓ ^ 2 := by ring
    have hℓsq : ℓ ^ 2 ≤ L ^ 9 := by
      have h1 : ℓ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hℓpos.le hℓL 2
      have h2 : L ^ 2 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
      linarith
    have hstep : E ^ 2 / 4 ≤ roughSieveProduct W ^ 2 * L ^ 9 :=
      le_trans hsq (mul_le_mul_of_nonneg_left hℓsq (sq_nonneg _))
    rw [div_le_div_iff₀ (by positivity) hLpos]
    calc E ^ 2 / 4 * L ≤ (roughSieveProduct W ^ 2 * L ^ 9) * L :=
          mul_le_mul_of_nonneg_right hstep hLpos.le
      _ = roughSieveProduct W ^ 2 * L ^ 10 := by ring
  -- `x/r ≥ x^0.89`
  have hxr : e (89 / 100) ≤ x / r := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [le_div_iff₀ hrpos]
    have hx_eq : x = e (89 / 100) * e (11 / 100) := by
      rw [he_mul]
      rw [show (89 / 100 + 11 / 100 : ℝ) = 1 by norm_num]
      exact (Real.rpow_one x).symm
    calc e (89 / 100) * (r : ℝ) ≤ e (89 / 100) * e (11 / 100) :=
          mul_le_mul_of_nonneg_left hrx (he_pos _).le
      _ = x := hx_eq.symm
  -- the lattice error sum
  have hYge : (1 : ℝ) ≤ z ^ 10 := one_le_pow₀ (by linarith)
  have hYscale : z ^ 10 ≤ Real.rpow x (2 / 100 : ℝ) := by
    have h : z ^ 10 = Real.rpow x (2 / 100 : ℝ) := by
      rw [hzdef, show Real.rpow x (1 / 500 : ℝ) = x ^ (1 / 500 : ℝ) from rfl,
        ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    exact h.le
  have hHsum : H₁ + H₂ ≤ 4 * Real.rpow x (54 / 100 : ℝ) := by linarith
  have hkScale : ((c * r : ℕ) : ℝ) ≤ 4 * Real.rpow x (11 / 100 : ℝ) := by
    have hc4 : (c : ℝ) ≤ 4 := by rcases hc with h | h <;> subst h <;> norm_num
    push_cast
    have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    calc (c : ℝ) * r ≤ 4 * r := mul_le_mul_of_nonneg_right hc4 hr0'
      _ ≤ 4 * Real.rpow x (11 / 100 : ℝ) := by linarith
  have hErr := pairSieveLatticeErrors_scaled P W H₁ H₂ x (z ^ 10) hk hprime hcop hH₁2 hH₂2
    hYge hx1 hHsum hkScale hYscale
  have hErr' : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      pairSieveLatticeError P D W H₁ H₂ hk hprime hcop ≤ 192 * e (69 / 100) := by
    have h1 : Real.rpow x (54 / 100 : ℝ) * Real.rpow x (11 / 100 : ℝ) *
        (Real.rpow x (2 / 100 : ℝ)) ^ 2 = e (69 / 100) := by
      show e (54 / 100) * e (11 / 100) * e (2 / 100) ^ 2 = e (69 / 100)
      rw [pow_two, he_mul, he_mul, he_mul]
      norm_num
    have h2 : (Real.rpow x (11 / 100 : ℝ)) ^ 2 * (Real.rpow x (2 / 100 : ℝ)) ^ 3 =
        e (28 / 100) := by
      show e (11 / 100) ^ 2 * e (2 / 100) ^ 3 = e (28 / 100)
      rw [pow_two, pow_succ, pow_two, he_mul, he_mul, he_mul, he_mul]
      norm_num
    have h3 : e (28 / 100) ≤ e (69 / 100) := he_mono _ _ (by norm_num)
    calc _ ≤ _ := hErr
      _ = 64 * (Real.rpow x (54 / 100 : ℝ) * Real.rpow x (11 / 100 : ℝ) *
            (Real.rpow x (2 / 100 : ℝ)) ^ 2) +
          128 * ((Real.rpow x (11 / 100 : ℝ)) ^ 2 * (Real.rpow x (2 / 100 : ℝ)) ^ 3) := by
        ring
      _ = 64 * e (69 / 100) + 128 * e (28 / 100) := by rw [h1, h2]
      _ ≤ 192 * e (69 / 100) := by linarith
  have hErrAbs : 192 * e (69 / 100) ≤
      (x / r) * (roughSieveProduct W ^ 2 / L) := by
    have h := hAbsX
    have h' : (E ^ 2 / 4) * e (89 / 100) / L ^ 10 =
        e (89 / 100) * ((E ^ 2 / 4) / L ^ 10) := by ring
    calc 192 * e (69 / 100) = 192 * Real.rpow x (69 / 100 : ℝ) := rfl
      _ ≤ (E ^ 2 / 4) * Real.rpow x (89 / 100 : ℝ) / Real.log x ^ 10 := h
      _ = e (89 / 100) * ((E ^ 2 / 4) / L ^ 10) := h'
      _ ≤ (x / r) * (roughSieveProduct W ^ 2 / L) :=
        mul_le_mul hxr hVWsq (by positivity) (by
          have := (he_pos (89 / 100)).le
          linarith)
  -- the main term
  have hX' : H₁ * H₂ * (Nat.totient (c * r) : ℝ) / ((c * r : ℕ) : ℝ) ^ 2 ≤ x / r := by
    have hkpos : (0 : ℝ) < ((c * r : ℕ) : ℝ) := by exact_mod_cast hk
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [div_le_div_iff₀ (by positivity) hrpos]
    have hφ : (Nat.totient (c * r) : ℝ) ≤ ((c * r : ℕ) : ℝ) := by
      exact_mod_cast Nat.totient_le (c * r)
    have h2r : 2 * (r : ℝ) ≤ ((c * r : ℕ) : ℝ) := by
      push_cast
      have hc2 : (2 : ℝ) ≤ c := by rcases hc with h | h <;> subst h <;> norm_num
      have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have := mul_le_mul_of_nonneg_right hc2 hr0'
      linarith
    have hH0 : 0 ≤ H₁ * H₂ := mul_nonneg (by linarith) (by linarith)
    calc H₁ * H₂ * (Nat.totient (c * r) : ℝ) * r
        ≤ (2 * x) * ((c * r : ℕ) : ℝ) * r := by
          have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
          have hφ0 : (0 : ℝ) ≤ (Nat.totient (c * r) : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = x * ((c * r : ℕ) : ℝ) * (2 * r) := by ring
      _ ≤ x * ((c * r : ℕ) : ℝ) * ((c * r : ℕ) : ℝ) := by
          gcongr
      _ = x * ((c * r : ℕ) : ℝ) ^ 2 := by ring
  have hMain : H₁ * H₂ * (Nat.totient (c * r) : ℝ) / ((c * r : ℕ) : ℝ) ^ 2 *
      ∏ p ∈ P, (1 - pairSieveG W p) ≤
        (x / r) * (8 * Real.exp (6 + 1 / 2) * roughSieveProduct W ^ 2 *
          (750 * E / L)) := by
    have hX'nn : 0 ≤ H₁ * H₂ * (Nat.totient (c * r) : ℝ) / ((c * r : ℕ) : ℝ) ^ 2 := by
      have hH0 : 0 ≤ H₁ * H₂ := mul_nonneg (by linarith) (by linarith)
      positivity
    calc _ ≤ (x / r) * ∏ p ∈ P, (1 - pairSieveG W p) :=
          mul_le_mul_of_nonneg_right hX' hprodNonneg
      _ ≤ (x / r) * (8 * Real.exp (6 + 1 / 2) * roughSieveProduct W ^ 2 *
            roughSieveProduct z) := by
          apply mul_le_mul_of_nonneg_left hprod
          have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
          positivity
      _ ≤ (x / r) * (8 * Real.exp (6 + 1 / 2) * roughSieveProduct W ^ 2 *
            (750 * E / L)) := by
          apply mul_le_mul_of_nonneg_left _ (by
            have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
            positivity)
          apply mul_le_mul_of_nonneg_left hVz
          positivity
  -- assemble
  have hfinal := hmainB
  calc ((pairSieveSurvivors H₁ H₂ (c * r) P W).card : ℝ)
      ≤ K * (H₁ * H₂ * (Nat.totient (c * r) : ℝ) / ((c * r : ℕ) : ℝ) ^ 2 *
            ∏ p ∈ P, (1 - pairSieveG W p)) +
          K * ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
            pairSieveLatticeError P D W H₁ H₂ hk hprime hcop := hfinal
    _ ≤ K * ((x / r) * (8 * Real.exp (6 + 1 / 2) * roughSieveProduct W ^ 2 *
            (750 * E / L))) +
          K * ((x / r) * (roughSieveProduct W ^ 2 / L)) := by
        gcongr
        exact le_trans hErr' hErrAbs
    _ = K * (6000 * Real.exp (6 + 1 / 2) * E + 1) * (x / r) *
          roughSieveProduct W ^ 2 / L := by
        field_simp
        ring

end ArtinPrimitiveRoots.Construction.Proofs.CRP
