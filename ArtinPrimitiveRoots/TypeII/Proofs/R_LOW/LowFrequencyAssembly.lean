import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.WiderWindow
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.SWAdapters
import ArtinPrimitiveRoots.TypeII.PD.Preliminaries
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.MertensBounds

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open Classical MeasureTheory Filter ArtinPrimitiveRoots.TypeII
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem low_frequency_from_counts (γ wMin wMax C δ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax) (hδ : 0 < δ)
    (hC : 0 < C)
    (hcount : ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ Cc xc : ℝ, 0 < Cc ∧ 2 ≤ xc ∧
        roughCountBound γ wMin (wMax + 1) A₀ A₁ Cc xc)
    (hdensity : ∃ K : ℝ, 0 < K ∧
      ∀ s ∈ Set.Icc wMin (wMax + 1), ∀ t ∈ Set.Icc wMin (wMax + 1),
        |ArtinPrimitiveRoots.Sieve.roughDensity γ s -
          ArtinPrimitiveRoots.Sieve.roughDensity γ t| ≤ K * |s - t|) :
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          (((if roughAbove m (Real.rpow x γ) then 1 else 0 : ℝ) : ℂ) *
                            χ (m : ZMod k) * Complex.exp
                              (Complex.I * (t + v) * Real.log (m : ℝ)) -
                            (if roughAbove m (roughCutoff x) then χ (m : ZMod k) else 0) *
                              ((ArtinPrimitiveRoots.Sieve.roughDensity γ
                                (Real.log (m : ℝ) / Real.log x) /
                                (Real.log x * roughSieveProduct (roughCutoff x)) : ℝ) : ℂ) *
                              Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A) := by
  intro A₀ A B₂ hA₀ hA hB₂
  let bExp : ℝ := max C B₂
  let A₁ : ℝ := A + bExp + 3
  let Cpd : ℝ := wMax + A₀ + 2
  let D : ℝ → ℝ := ArtinPrimitiveRoots.Sieve.roughDensity γ
  have hMinPos : 0 < wMin := hγ.trans hγw
  have hMaxPos : 0 < wMax := hMinPos.trans hw
  have hbExp : 0 < bExp := lt_of_lt_of_le hC (le_max_left _ _)
  have hA₁ : 0 < A₁ := by dsimp [A₁]; linarith
  have hCpd : 0 < Cpd := by dsimp [Cpd]; linarith
  have hwide : wMin < wMax + 1 := by linarith
  obtain ⟨K_D, hK_D, hDlip⟩ := hdensity
  let B_D : ℝ := |D wMin| + K_D * (wMax + 1 - wMin) + 1
  have hB_D : 0 < B_D := by
    have hwidth : 0 < wMax + 1 - wMin := by linarith
    dsimp [B_D]
    positivity
  have hDbound : ∀ w ∈ Set.Icc wMin (wMax + 1), |D w| ≤ B_D := by
    intro w hw'
    have hLip := hDlip w hw' wMin ⟨le_rfl, hwide.le⟩
    have hdist : |w - wMin| ≤ wMax + 1 - wMin := by
      rw [abs_of_nonneg (sub_nonneg.mpr hw'.1)]
      linarith [hw'.2]
    calc
      |D w| = |(D w - D wMin) + D wMin| := by congr 1; ring
      _ ≤ |D w - D wMin| + |D wMin| := abs_add_le _ _
      _ ≤ K_D * |w - wMin| + |D wMin| := add_le_add hLip le_rfl
      _ ≤ K_D * (wMax + 1 - wMin) + |D wMin| :=
        add_le_add (mul_le_mul_of_nonneg_left hdist hK_D.le) le_rfl
      _ ≤ B_D := by dsimp [B_D]; linarith
  obtain ⟨Cc, xc, hCc, hxc, hCounts⟩ := hcount A₀ A₁ hA₀ hA₁
  obtain ⟨_Cpd₀, xpd, _hCpd₀, hxpd, hPD⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.rough_counts δ Cpd (1 / 2) A₁
      hδ hCpd (by norm_num) (by norm_num) hA₁
  obtain ⟨_s₀, vLow, xmertens, _hs₀, hvLow, hxmertens, hMertens⟩ :=
    ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.rough_mertens_bounds
  have hevent : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ xc ≤ x ∧ xpd ≤ x ∧ xmertens ≤ x ∧
        1 ≤ Real.log x ∧ Real.rpow (Real.log x) A₁ ≤ Real.rpow x δ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop xc,
      eventually_ge_atTop xpd, eventually_ge_atTop xmertens,
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      ArtinPrimitiveRoots.Proofs.RImplP.RLow.eventually_log_rpow_le_rpow A₁ δ hδ]
      with x hx₂ hxc' hxpd' hxmertens' hL hpow
    exact ⟨hx₂, hxc', hxpd', hxmertens', hL, hpow⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hevent
  let C₀ : ℝ := 6 * Cc + (4 / vLow) * (3 * B_D + K_D) + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, x₀, hC₀, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx M hMx hwM l r hl hlr hr v t hv ht k hk hklog χ
  obtain ⟨hx₂, hxc', hxpd', hxmertens', hLone, hpower⟩ := hx₀ x hx
  let L : ℝ := Real.log x
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let u : ℝ := t + v
  let e : ℂ := if χ = 1 then 1 else 0
  let a : ℕ → ℂ := fun n => ((if roughAbove n (Real.rpow x γ) then 1 else 0 : ℝ) : ℂ) *
    χ (n : ZMod k)
  let b : ℕ → ℂ := fun n => if roughAbove n (roughCutoff x) then χ (n : ZMod k) else 0
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := hLone
  have hMpos : 0 < M := (Real.rpow_pos_of_pos hxpos δ).trans_le hMx
  have hlogMlo : wMin * L ≤ Real.log M :=
    (le_div_iff₀ hLpos).mp hwM.1
  have hlogMhi : Real.log M ≤ wMax * L :=
    (div_le_iff₀ hLpos).mp hwM.2
  have hMrough : Real.rpow x γ ≤ M := by
    calc
      Real.rpow x γ = Real.exp (L * γ) := Real.rpow_def_of_pos hxpos _
      _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right hγw.le hLpos.le
        nlinarith)
      _ = M := Real.exp_log hMpos
  have hMpd : M ≤ Real.rpow x Cpd := by
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (L * Cpd) := Real.exp_le_exp.mpr (by
        have hCpdMax : wMax ≤ Cpd := by dsimp [Cpd]; linarith
        have hh := mul_le_mul_of_nonneg_right hCpdMax hLpos.le
        nlinarith)
      _ = Real.rpow x Cpd := (Real.rpow_def_of_pos hxpos _).symm
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog2div : Real.log 2 / L ≤ 1 := by
    apply (div_le_iff₀ hLpos).2
    linarith
  have hratio2 : Real.log (2 * M) / L = Real.log M / L + Real.log 2 / L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMpos.ne']
    ring
  have hwMwide : Real.log M / L ∈ Set.Icc wMin (wMax + 1) :=
    ⟨hwM.1, hwM.2.trans (by linarith)⟩
  have hw2M : Real.log (2 * M) / L ∈ Set.Icc wMin (wMax + 1) := by
    rw [hratio2]
    exact ⟨by linarith [hwM.1, div_nonneg hlog2 hLpos.le],
      by linarith [hwM.2]⟩
  have hmem : ∀ y ∈ Set.Icc M (2 * M), Real.log y / L ∈ Set.Icc wMin (wMax + 1) := by
    intro y hy
    have hypos : 0 < y := hMpos.trans_le hy.1
    exact ⟨hwMwide.1.trans (div_le_div_of_nonneg_right
      (Real.log_le_log hMpos hy.1) hLpos.le),
      (div_le_div_of_nonneg_right (Real.log_le_log hypos hy.2) hLpos.le).trans hw2M.2⟩
  have hDcont : ContinuousOn (fun y => D (Real.log y / L)) (Set.Icc l r) := by
    have hdist : ∀ s ∈ Set.Icc M (2 * M), ∀ t ∈ Set.Icc M (2 * M),
        dist (D (Real.log s / L)) (D (Real.log t / L)) ≤
          (K_D / (L * M)) * dist s t := by
      intro s hs t ht
      simpa only [Real.dist_eq] using density_log_lipschitz D K_D wMin (wMax + 1)
        L M hK_D.le hLpos hMpos hDlip hmem s t hs.1 hs.2 ht.1 ht.2
    exact (LipschitzOnWith.of_dist_le' hdist).continuousOn.mono
      (fun _ hy => ⟨hl.trans hy.1, hy.2.trans hr⟩)
  have hVlower : vLow * Real.rpow L (-(24 / 100 : ℝ)) ≤ V :=
    (hMertens x hxmertens').2
  have hVpos : 0 < V :=
    (mul_pos hvLow (Real.rpow_pos_of_pos hLpos _)).trans_le hVlower
  have hVone : V ≤ 1 := by
    dsimp [V, roughSieveProduct]
    apply Finset.prod_le_one₀
    · intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hpReal : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_le
      have hpPos : (0 : ℝ) < (p : ℝ) := by linarith
      exact sub_nonneg.mpr ((div_le_one₀ hpPos).mpr hpReal)
    · intro p _hp
      exact sub_le_self _ (by positivity)
  have hLVlower : vLow ≤ L * V := by
    have hpMul : L * Real.rpow L (-(24 / 100 : ℝ)) =
        Real.rpow L (1 - 24 / 100 : ℝ) := by
      change L * L ^ (-(24 / 100 : ℝ)) = L ^ (1 - 24 / 100 : ℝ)
      calc
        L * L ^ (-(24 / 100 : ℝ)) = L ^ (1 : ℝ) * L ^ (-(24 / 100 : ℝ)) := by
          rw [Real.rpow_one]
        _ = L ^ ((1 : ℝ) + -(24 / 100 : ℝ)) := (Real.rpow_add hLpos _ _).symm
        _ = L ^ (1 - 24 / 100 : ℝ) := by congr 1
    calc
      vLow ≤ vLow * Real.rpow L (1 - 24 / 100 : ℝ) :=
        le_mul_of_one_le_right hvLow.le (Real.one_le_rpow hL1 (by norm_num))
      _ = L * (vLow * Real.rpow L (-(24 / 100 : ℝ))) := by rw [mul_left_comm, hpMul]
      _ ≤ L * V := mul_le_mul_of_nonneg_left hVlower hLpos.le
  have hendpoint : 1 ≤ M * Real.rpow L (-A₁) := by
    have hPM : Real.rpow L A₁ ≤ M := hpower.trans hMx
    calc
      1 = Real.rpow L A₁ * Real.rpow L (-A₁) := by
        change 1 = L ^ A₁ * L ^ (-A₁)
        rw [← Real.rpow_add hLpos, add_neg_cancel, Real.rpow_zero]
      _ ≤ M * Real.rpow L (-A₁) :=
        mul_le_mul_of_nonneg_right hPM (Real.rpow_nonneg hLpos.le _)
  have hkpd : (k : ℝ) ≤ Real.rpow L Cpd := hklog.trans
    (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [Cpd]; linarith))
  have hcount₁ : ∀ s ∈ Set.Icc l r,
      ‖(∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), a n) -
        ∫ y in l..s, e * ((D (Real.log y / L) / L : ℝ) : ℂ)‖ ≤
          Cc * M * Real.rpow L (-A₁) := by
    intro s hs
    have hbase := hCounts x hxc' M hMrough hwMwide hw2M k hk hklog χ l s
      hl hs.1 (hs.2.trans hr)
    have hmain : (∫ y in l..s, e * ((D (Real.log y / L) / L : ℝ) : ℂ)) =
        (if χ = 1 then ((1 / L) * ∫ y in l..s, D (Real.log y / L) : ℝ) else 0 : ℂ) := by
      by_cases hχ : χ = 1
      · simp only [e, hχ, ite_true, one_mul, intervalIntegral.integral_ofReal,
          intervalIntegral.integral_div]
        congr 1
        ring
      · simp [e, hχ]
    rw [hmain]
    exact hbase
  have hcount₂ : ∀ s ∈ Set.Icc l r,
      ‖(∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), b n) -
        ∫ y in l..s, e * (V : ℂ)‖ ≤ 2 * M * Real.rpow L (-A₁) := by
    intro s hs
    have hbase := (hPD x hxpd' M hMx hMpd l s hl hs.1 (hs.2.trans hr)).2.2
      k hk hkpd χ
    have hsum : (∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), b n) =
        ∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s ∧ roughAbove n (roughCutoff x)),
          χ (n : ZMod k) := by
      dsimp [b]
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter]
      tauto
    let P : ℂ := if χ = 1 then (V * (s - l + 1) : ℝ) else 0
    have hmainDiff : P - (∫ y in l..s, e * (V : ℂ)) = e * (V : ℂ) := by
      dsimp [P]
      by_cases hχ : χ = 1
      · simp [e, hχ]
        ring
      · simp [e, hχ]
    have heNorm : ‖e * (V : ℂ)‖ ≤ 1 := by
      by_cases hχ : χ = 1
      · simpa [e, hχ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hVpos] using hVone
      · simp [e, hχ]
    calc
      ‖(∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), b n) -
          ∫ y in l..s, e * (V : ℂ)‖ ≤
          ‖(∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
            (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), b n) - P‖ +
            ‖P - ∫ y in l..s, e * (V : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * Real.rpow L (-A₁) + 1 := by
        apply add_le_add
        · rw [hsum]
          exact hbase
        · rw [hmainDiff]
          exact heNorm
      _ ≤ 2 * M * Real.rpow L (-A₁) := by linarith
  have hErrPow : 0 ≤ Real.rpow L (-A₁) := Real.rpow_nonneg hLpos.le _
  have hTargetPow : 0 ≤ Real.rpow L (-A) := Real.rpow_nonneg hLpos.le _
  have hweighted := low_frequency_weighted_difference M l r L V u
    (Cc * M * Real.rpow L (-A₁)) (2 * M * Real.rpow L (-A₁))
    B_D K_D wMin (wMax + 1) a b D e hMpos hLpos hVpos hl hlr hr
    (by positivity) (by positivity) hB_D.le hK_D.le hDcont hDbound hDlip hmem hcount₁ hcount₂
  have hpowb1 : 1 ≤ Real.rpow L bExp := Real.one_le_rpow hL1 hbExp.le
  have hu : |u| ≤ 2 * Real.rpow L bExp := by
    have hv' : |v| ≤ Real.rpow L bExp := hv.trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
    have ht' : |t| ≤ Real.rpow L bExp := ht.trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
    calc
      |u| ≤ |t| + |v| := abs_add_le t v
      _ ≤ Real.rpow L bExp + Real.rpow L bExp := add_le_add ht' hv'
      _ = 2 * Real.rpow L bExp := by ring
  have hphaseGrowth : 1 + |u| ≤ 3 * Real.rpow L bExp := by
    linarith only [hu, hpowb1]
  have hKDdiv : K_D / L ≤ K_D := (div_le_self hK_D.le hL1)
  have hweightGrowth : B_D + K_D / L + B_D * |u| ≤
      (3 * B_D + K_D) * Real.rpow L bExp := by
    have hBscale := mul_le_mul_of_nonneg_left hpowb1 hB_D.le
    have hKscale := mul_le_mul_of_nonneg_left hpowb1 hK_D.le
    have huscale := mul_le_mul_of_nonneg_left hu hB_D.le
    nlinarith only [hBscale, hKscale, huscale, hKDdiv]
  have hsaving : Real.rpow L (-A₁) * Real.rpow L bExp ≤ Real.rpow L (-A) := by
    change L ^ (-A₁) * L ^ bExp ≤ L ^ (-A)
    rw [← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp [A₁]
    linarith
  have hroughErr : 2 * (Cc * M * Real.rpow L (-A₁)) * (1 + |u|) ≤
      (6 * Cc) * M * Real.rpow L (-A) := by
    calc
      _ ≤ 2 * (Cc * M * Real.rpow L (-A₁)) * (3 * Real.rpow L bExp) :=
        mul_le_mul_of_nonneg_left hphaseGrowth (by positivity)
      _ = (6 * Cc) * M * (Real.rpow L (-A₁) * Real.rpow L bExp) := by ring
      _ ≤ (6 * Cc) * M * Real.rpow L (-A) :=
        mul_le_mul_of_nonneg_left hsaving (by positivity)
  have hproxyWeight : (B_D + K_D / L + B_D * |u|) / (L * V) ≤
      ((3 * B_D + K_D) * Real.rpow L bExp) / vLow := by
    calc
      _ ≤ ((3 * B_D + K_D) * Real.rpow L bExp) / (L * V) :=
        (div_le_div_iff_of_pos_right (mul_pos hLpos hVpos)).mpr hweightGrowth
      _ ≤ ((3 * B_D + K_D) * Real.rpow L bExp) / vLow :=
        div_le_div_of_nonneg_left (by positivity) hvLow hLVlower
  have hproxyErr : 2 * (2 * M * Real.rpow L (-A₁)) *
      ((B_D + K_D / L + B_D * |u|) / (L * V)) ≤
      ((4 / vLow) * (3 * B_D + K_D)) * M * Real.rpow L (-A) := by
    calc
      _ ≤ 2 * (2 * M * Real.rpow L (-A₁)) *
          (((3 * B_D + K_D) * Real.rpow L bExp) / vLow) :=
        mul_le_mul_of_nonneg_left hproxyWeight (by positivity)
      _ = ((4 / vLow) * (3 * B_D + K_D)) * M *
          (Real.rpow L (-A₁) * Real.rpow L bExp) := by ring
      _ ≤ ((4 / vLow) * (3 * B_D + K_D)) * M * Real.rpow L (-A) :=
        mul_le_mul_of_nonneg_left hsaving (by positivity)
  have htotal := hweighted.trans (add_le_add hroughErr hproxyErr)
  have htotal' : ‖∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
      (fun n : ℕ => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r),
      (a n * Complex.exp (Complex.I * u * Real.log (n : ℝ)) -
        b n * ((D (Real.log (n : ℝ) / L) / (L * V) : ℝ) : ℂ) *
          Complex.exp (Complex.I * u * Real.log (n : ℝ)))‖ ≤
        C₀ * M * Real.rpow L (-A) := by
    apply htotal.trans
    have hMP : 0 ≤ M * Real.rpow L (-A) := by positivity
    have hcoeff : 6 * Cc + (4 / vLow) * (3 * B_D + K_D) ≤ C₀ := by
      dsimp [C₀]
      linarith
    calc
      _ = (6 * Cc + (4 / vLow) * (3 * B_D + K_D)) *
          (M * Real.rpow L (-A)) := by ring
      _ ≤ C₀ * (M * Real.rpow L (-A)) := mul_le_mul_of_nonneg_right hcoeff hMP
      _ = C₀ * M * Real.rpow L (-A) := by ring
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
  apply (div_le_iff₀ hMpos).2
  calc
    _ ≤ C₀ * M * Real.rpow L (-A) := by
      simpa only [a, b, D, L, V, u, Complex.ofReal_add, mul_assoc] using htotal'
    _ = _ := by ring

end ArtinPrimitiveRoots.Proofs.r_impl_muse
