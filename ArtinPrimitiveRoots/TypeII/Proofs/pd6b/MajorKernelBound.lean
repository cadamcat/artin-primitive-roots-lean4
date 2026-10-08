import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CutoffBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical MeasureTheory Filter

noncomputable section

private def arcIndicator (c R t : ℝ) : ℝ := if |t - c| ≤ R then 1 else 0

private theorem arcIndicator_nonneg (c R t : ℝ) : 0 ≤ arcIndicator c R t := by
  unfold arcIndicator
  split_ifs <;> norm_num

private theorem arcIndicator_eq_indicator (c R : ℝ) :
    arcIndicator c R = (Set.Icc (c - R) (c + R)).indicator (fun _ => (1 : ℝ)) := by
  funext t
  have hiff : |t - c| ≤ R ↔ c - R ≤ t ∧ t ≤ c + R := by
    rw [abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [arcIndicator, Set.indicator, Set.mem_Icc, hiff]

private theorem arcIndicator_integrable (c R : ℝ) : Integrable (arcIndicator c R) := by
  rw [arcIndicator_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp only [Real.volume_Icc]; finiteness))

private theorem arcIndicator_integral (c R : ℝ) (hR : 0 ≤ R) :
    (∫ t : ℝ, arcIndicator c R t) = 2 * R := by
  rw [arcIndicator_eq_indicator]
  change (∫ t : ℝ, (Set.Icc (c - R) (c + R)).indicator (1 : ℝ → ℝ) t) = _
  rw [integral_indicator_one measurableSet_Icc]
  simp only [Measure.real, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ c + R - (c - R))]
  ring

private theorem additiveCharacter_norm_one (t : ℝ) : ‖additiveCharacter t‖ = 1 := by
  simp [additiveCharacter, Complex.norm_exp]

/-- The total major-arc character integral is bounded by the elementary arc covering mass. -/
theorem majorArcIntegral_norm_le (x Y A₀ v : ℝ) (hY : 0 < Y)
    (hM : 1 ≤ Real.rpow (Real.log x) A₀) :
    ‖∫ theta in (0 : ℝ)..1,
      if majorArc x Y A₀ theta then additiveCharacter (theta * v) else 0‖ ≤
        32 * (Real.rpow (Real.log x) A₀) ^ 3 / Y := by
  let M := Real.rpow (Real.log x) A₀
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  let f := fun theta : ℝ => if majorArc x Y A₀ theta then additiveCharacter (theta * v) else 0
  have hnorm (theta : ℝ) : ‖f theta‖ ≤ 1 := by
    dsimp [f]
    split_ifs <;> simp [additiveCharacter_norm_one]
  have htrivial : ‖∫ theta in (0 : ℝ)..1, f theta‖ ≤ 1 := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (fun theta ht => hnorm theta))
  by_cases hsmall : Y ≤ 4 * M
  · apply htrivial.trans
    apply (le_div_iff₀ hY).mpr
    have hcube : M ≤ M ^ 3 := by
      have hsq : 1 ≤ M ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq hMpos.le
      nlinarith
    change 1 * Y ≤ 32 * M ^ 3
    nlinarith
  have hlarge : 4 * M < Y := lt_of_not_ge hsmall
  let R := 2 * M / Y
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRlt : R < 1 := by
    dsimp [R]
    apply (div_lt_one hY).mpr
    linarith
  let N : ℕ := ⌊M⌋₊
  let H (k : ℕ) : Finset ℤ := Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))
  let inner (k : ℕ) (theta : ℝ) : ℝ :=
    ∑ h ∈ H k, arcIndicator ((h : ℝ) / (k : ℝ)) R theta
  let cover (theta : ℝ) : ℝ := ∑ k ∈ Finset.range (N + 1), inner k theta
  have hInnerInt (k : ℕ) : Integrable (inner k) := by
    exact integrable_finset_sum _ (fun h hh => arcIndicator_integrable _ _)
  have hCoverInt : Integrable cover := by
    exact integrable_finset_sum _ (fun k hk => hInnerInt k)
  have hInnerNonneg (k : ℕ) (theta : ℝ) : 0 ≤ inner k theta :=
    Finset.sum_nonneg (fun h hh => arcIndicator_nonneg _ _ _)
  have hCoverNonneg (theta : ℝ) : 0 ≤ cover theta :=
    Finset.sum_nonneg (fun k hk => hInnerNonneg k theta)
  have hcover (theta : ℝ) (ht : theta ∈ Set.Ioc (0 : ℝ) 1)
      (hmajor : majorArc x Y A₀ theta) : 1 ≤ cover theta := by
    rcases hmajor with ⟨h, k, hk₁, hkM, hgcd, z, hz⟩
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    let h' : ℤ := h + (k : ℤ) * z
    have hfrac : (h' : ℝ) / (k : ℝ) = (h : ℝ) / (k : ℝ) + (z : ℝ) := by
      dsimp [h']
      push_cast
      field_simp
    have hclose : |theta - (h' : ℝ) / (k : ℝ)| ≤ R := by
      rw [hfrac]
      simpa only [sub_add_eq_sub_sub] using hz
    have hquotLo : -(1 : ℝ) ≤ (h' : ℝ) / (k : ℝ) := by
      linarith [(abs_le.mp hclose).2, ht.1, hRlt]
    have hquotHi : (h' : ℝ) / (k : ℝ) ≤ 2 := by
      linarith [(abs_le.mp hclose).1, ht.2, hRlt]
    have hhLo : -(k : ℤ) ≤ h' := by
      have hr := (le_div_iff₀ hkpos).mp hquotLo
      have hr' : -(k : ℝ) ≤ (h' : ℝ) := by simpa using hr
      exact_mod_cast hr'
    have hhHi : h' ≤ 2 * (k : ℤ) := by
      have hr := (div_le_iff₀ hkpos).mp hquotHi
      exact_mod_cast hr
    have hh : h' ∈ H k := Finset.mem_Icc.mpr ⟨hhLo, hhHi⟩
    have hk : k ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le ((Nat.le_floor_iff hMpos.le).mpr hkM)
    have hAtom : arcIndicator ((h' : ℝ) / (k : ℝ)) R theta = 1 := by
      simp [arcIndicator, hclose]
    calc
      1 = arcIndicator ((h' : ℝ) / (k : ℝ)) R theta := hAtom.symm
      _ ≤ inner k theta := by
        dsimp only [inner]
        exact Finset.single_le_sum
          (fun (h : ℤ) hh => arcIndicator_nonneg ((h : ℝ) / (k : ℝ)) R theta) hh
      _ ≤ cover theta := by
        dsimp only [cover]
        exact Finset.single_le_sum (fun (k : ℕ) hk => hInnerNonneg k theta) hk
  have hbound : ‖∫ theta in (0 : ℝ)..1, f theta‖ ≤ ∫ theta : ℝ, cover theta := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_indicator measurableSet_Ioc]
    apply norm_integral_le_of_norm_le hCoverInt
    filter_upwards [] with theta
    by_cases ht : theta ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      by_cases hmajor : majorArc x Y A₀ theta
      · simpa [f, hmajor, additiveCharacter_norm_one] using hcover theta ht hmajor
      · simpa [f, hmajor] using hCoverNonneg theta
    · rw [Set.indicator_of_notMem ht]
      simpa using hCoverNonneg theta
  have hIntegral : (∫ theta : ℝ, cover theta) =
      ∑ k ∈ Finset.range (N + 1), ((H k).card : ℝ) * (2 * R) := by
    rw [integral_finset_sum _ (fun k hk => hInnerInt k)]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [inner]
    rw [integral_finset_sum _ (fun h hh => arcIndicator_integrable _ _)]
    simp_rw [arcIndicator_integral _ _ hRpos.le]
    simp
  have hCardH (k : ℕ) : (H k).card = 3 * k + 1 := by
    have h := Int.card_Icc_of_le (a := -(k : ℤ)) (b := 2 * (k : ℤ)) (by omega)
    have h' : ((H k).card : ℤ) = (3 * k + 1 : ℕ) := by dsimp [H]; omega
    exact_mod_cast h'
  have hN : (N : ℝ) ≤ M := Nat.floor_le hMpos.le
  have hIntegralLe : (∫ theta : ℝ, cover theta) ≤
      ((N : ℝ) + 1) * (3 * (N : ℝ) + 1) * (2 * R) := by
    rw [hIntegral]
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), (3 * (N : ℝ) + 1) * (2 * R) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hCardH]
        have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
        have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
        push_cast
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by simp; ring
  have hProduct : ((N : ℝ) + 1) * (3 * (N : ℝ) + 1) ≤ 8 * M ^ 2 := by
    have h1 : (N : ℝ) + 1 ≤ 2 * M := by linarith
    have h2 : 3 * (N : ℝ) + 1 ≤ 4 * M := by linarith
    have hmul := mul_le_mul h1 h2 (by positivity : 0 ≤ 3 * (N : ℝ) + 1)
      (by positivity : 0 ≤ 2 * M)
    nlinarith
  calc
    _ ≤ ∫ theta : ℝ, cover theta := hbound
    _ ≤ ((N : ℝ) + 1) * (3 * (N : ℝ) + 1) * (2 * R) := hIntegralLe
    _ ≤ (8 * M ^ 2) * (2 * R) := mul_le_mul_of_nonneg_right hProduct (by positivity)
    _ = 32 * M ^ 3 / Y := by dsimp [R]; ring

/-- The comparison kernel loses only `L^(3A₀)/Y` times the fixed cutoff bound. -/
theorem majorKernel_norm_bound (x Y A₀ t : ℝ) (aa bb : ℕ) (psi : ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hpsi : ∀ y : ℝ, |psi y| ≤ B)
    (hY : 0 < Y) (hL : 1 ≤ Real.log x) (hA : 0 < A₀) :
    ‖majorKernel x Y A₀ t aa bb psi‖ ≤
      32 * B * Real.rpow (Real.log x) (3 * A₀) / Y := by
  have hM : 1 ≤ Real.rpow (Real.log x) A₀ := Real.one_le_rpow hL hA.le
  have hphase := majorArcIntegral_norm_le x Y A₀ (t - (bb : ℝ) + (aa : ℝ)) hY hM
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hcube : (Real.rpow (Real.log x) A₀) ^ 3 =
      Real.rpow (Real.log x) (3 * A₀) := by
    calc
      _ = Real.rpow (Real.rpow (Real.log x) A₀) (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow (Real.log x) (A₀ * 3) := (Real.rpow_mul hLpos.le _ _).symm
      _ = _ := by congr 1 <;> ring
  rw [hcube] at hphase
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ B * (32 * Real.rpow (Real.log x) (3 * A₀) / Y) :=
      mul_le_mul (hpsi _) hphase (norm_nonneg _) hB
    _ = _ := by ring

end
end ArtinPrimitiveRoots.TypeII.PD
