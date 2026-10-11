import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII
noncomputable section

set_option maxHeartbeats 0 in
/-- Eventual elementary scales and uniform atom/mass bounds. Uses proved pd5 Atoms and HistoryPartition;
feeds positive rows, fixed-system bounds, boundary estimates and both frozen rank declarations. -/
theorem pd5_scale_facts (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x →
      1 ≤ S.L ∧ 2 ≤ S.N ∧
      Real.rpow S.L (1 / 2 : ℝ) ≤ (S.N : ℝ) ∧
      (S.N : ℝ) < Real.rpow S.L (1 / 2 : ℝ) + 2 ∧
      (slotCount S.x : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) ∧
      (memoryCutoff S : ℝ) ≤ 2 * S.L ^ 2 ∧ slotCount S.x ≤ S.N ∧
      ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
        bandMass S.x (F.a i) ≤ 2 * Real.log 2 ∧
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2 ∧
        ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p ∧
          memoryNu S.x K F.a F.q_d i p ≤
            (4 / Real.log 2) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by
  classical
  rcases hF with ⟨hBands, hqd0, hqd1, hA₀, _, _⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨xBandLo, hxBandLo, hBandLo⟩ := pd5_bandMass_lower_eventually F.a hBands
  have hK : 0 < K := hBands.1
  have hindex : (Finset.univ : Finset (Fin K)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, by omega⟩⟩
  have hBandUpperInd : ∀ i : Fin K, ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → bandMass x (F.a i) ≤ 2 * Real.log 2 := by
    intro i
    have hai := hBands.2.1 i
    obtain ⟨x₀, hx₀, hclose⟩ := band_mass (F.a i) (by linarith [hai.1])
      (by linarith [hai.2]) (Real.log 2) hlog2
    refine ⟨x₀, hx₀, ?_⟩
    intro x hx
    have habs := (hclose x hx).1
    have hbounds := abs_le.mp habs
    linarith
  choose xBandHi hBandHi using hBandUpperInd
  let xBand := max xBandLo (Finset.univ.sup' hindex xBandHi)
  have hxBand : 2 ≤ xBand := by
    dsimp [xBand]
    exact le_trans hxBandLo (le_max_left _ _)
  have hxBandLoBand : xBandLo ≤ xBand := le_max_left _ _
  have hxBandHiBand : ∀ i : Fin K, xBandHi i ≤ xBand := by
    intro i
    dsimp [xBand]
    exact le_trans (Finset.le_sup' xBandHi (Finset.mem_univ i)) (le_max_right _ _)

  obtain ⟨xPath, hxPath, hPath⟩ := pd5_pathLength_exponential_small
  have hLog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hLogOne : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Filter.tendsto_atTop.1 hLog 1
  have hLogFour : ∀ᶠ x : ℝ in atTop, 4 ≤ Real.log x :=
    Filter.tendsto_atTop.1 hLog 4
  have hHalf : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hLog
  have hHalfTwo : ∀ᶠ x : ℝ in atTop,
      2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) := Filter.tendsto_atTop.1 hHalf 2
  have hRatio : Tendsto (fun x : ℝ =>
      Real.rpow (Real.log x) (-(49 / 100 : ℝ))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => Real.rpow y (-(49 / 100 : ℝ)))
        atTop (𝓝 0) := by
      simpa [sub_eq_add_neg] using
        (tendsto_rpow_neg_atTop (by norm_num : 0 < (49 / 100 : ℝ)))
    exact hpow.comp hLog
  have hRatioHalf : ∀ᶠ x : ℝ in atTop,
      Real.rpow (Real.log x) (-(49 / 100 : ℝ)) < 1 / 2 :=
    hRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hXTwo : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hBandLoEventually : ∀ᶠ x : ℝ in atTop, xBandLo ≤ x :=
    eventually_ge_atTop xBandLo
  have hBandHiEventually : ∀ᶠ x : ℝ in atTop,
      (Finset.univ.sup' hindex xBandHi) ≤ x := eventually_ge_atTop _
  have hPathEventually : ∀ᶠ x : ℝ in atTop, xPath ≤ x := eventually_ge_atTop xPath
  have hAll : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ 4 ≤ Real.log x ∧
        2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
        Real.rpow (Real.log x) (-(49 / 100 : ℝ)) < 1 / 2 ∧
        xBandLo ≤ x ∧ (Finset.univ.sup' hindex xBandHi) ≤ x ∧ xPath ≤ x := by
    filter_upwards [hXTwo, hLogOne, hLogFour, hHalfTwo, hRatioHalf,
      hBandLoEventually, hBandHiEventually, hPathEventually]
      with x hx₂ hL₁ hL₄ hhalf hratio hxLo hxHi hxP
    exact ⟨hx₂, hL₁, hL₄, hhalf, hratio, hxLo, hxHi, hxP⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hAll
  have hx₀Two := (hx₀ x₀ le_rfl).1
  refine ⟨x₀, hx₀Two, ?_⟩
  intro S hxS
  have hx := hx₀ S.x hxS
  rcases hx with ⟨hx₂, hL₁, hL₄, hhalf, hratio, hxLo, hxHi, hxP⟩
  let L : ℝ := S.L
  have hL : L = Real.log S.x := rfl
  have hLone : 1 ≤ L := by simpa [L, hL] using hL₁
  have hLnonneg : 0 ≤ L := by linarith [hLone]
  have hLfour : 4 ≤ L := by simpa [L, hL] using hL₄

  have hNcast : (S.N : ℝ) = 2 * (momentR S.x : ℝ) := by
    simp [PDScale.N, pathLength]
  have hNceilLower : Real.rpow L (1 / 2 : ℝ) / 2 ≤ momentR S.x := by
    dsimp [momentR]
    exact Nat.le_ceil _
  have hNceilUpper : (momentR S.x : ℝ) <
      Real.rpow L (1 / 2 : ℝ) / 2 + 1 := by
    dsimp [momentR]
    exact Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hLnonneg _) (by norm_num))
  have hNlower : Real.rpow L (1 / 2 : ℝ) ≤ S.N := by
    rw [hNcast]
    nlinarith
  have hNupper : (S.N : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := by
    rw [hNcast]
    nlinarith
  have hNtwoReal : (2 : ℝ) ≤ (S.N : ℝ) := le_trans hhalf hNlower
  have hNtwo : 2 ≤ S.N := by exact_mod_cast hNtwoReal

  have hslotFloor : (slotCount S.x : ℝ) ≤ Real.rpow L (1 / 100 : ℝ) + 1 := by
    simp only [slotCount, momentJ, Nat.cast_add, Nat.cast_one]
    exact add_le_add (Nat.floor_le (Real.rpow_nonneg hLnonneg _)) le_rfl
  have hslotPowOne : 1 ≤ Real.rpow L (1 / 100 : ℝ) :=
    Real.one_le_rpow hLone (by norm_num)
  have hslotScale : (slotCount S.x : ℝ) ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by
    nlinarith [hslotFloor, hslotPowOne]

  have hcutoffCeil : (memoryCutoff S : ℝ) < Real.rpow L 2 + 1 := by
    dsimp [memoryCutoff]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hLnonneg _)
  have hpowTwo : Real.rpow L 2 = L ^ 2 := by
    rw [← Real.rpow_natCast]
    norm_num
  have hcutoffScale : (memoryCutoff S : ℝ) ≤ 2 * L ^ 2 := by
    rw [hpowTwo] at hcutoffCeil
    nlinarith [sq_nonneg (L - 1)]

  have hpowSub : Real.rpow L (1 / 100 : ℝ) /
      Real.rpow L (1 / 2 : ℝ) = Real.rpow L (1 / 100 - 1 / 2 : ℝ) := by
    exact (Real.rpow_sub (by linarith : 0 < L) (1 / 100 : ℝ) (1 / 2 : ℝ)).symm
  have hratioL : Real.rpow L (1 / 100 : ℝ) /
      Real.rpow L (1 / 2 : ℝ) ≤ 1 / 2 := by
    rw [hpowSub, show (1 / 100 : ℝ) - 1 / 2 = -(49 / 100 : ℝ) by norm_num, hL]
    exact hratio.le
  have hsmallSlot : Real.rpow L (1 / 100 : ℝ) ≤
      (1 / 2 : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < L) _)).1 hratioL
  have hslotLeNReal : (slotCount S.x : ℝ) ≤ (S.N : ℝ) := by
    calc
      (slotCount S.x : ℝ) ≤ Real.rpow L (1 / 100 : ℝ) + 1 := hslotFloor
      _ ≤ (1 / 2 : ℝ) * Real.rpow L (1 / 2 : ℝ) + 1 := by linarith [hsmallSlot]
      _ ≤ Real.rpow L (1 / 2 : ℝ) := by nlinarith [hhalf]
      _ ≤ (S.N : ℝ) := by exact_mod_cast hNlower
  have hslotLeN : slotCount S.x ≤ S.N := by exact_mod_cast hslotLeNReal

  have hBandLower := hBandLo S.x hxLo
  have hBandPath := hPath S.x hxP
  refine ⟨hLone, hNtwo, hNlower, hNupper, hslotScale, ?_, hslotLeN, ?_⟩
  · simpa [L, hL] using hcutoffScale
  · intro i
    have hai := hBands.2.1 i
    have hmassLower := hBandLower i
    have hmassUpper := (hBandHi i).2 S.x
      (le_trans (Finset.le_sup' xBandHi (Finset.mem_univ i)) hxHi)
    have hpathSmall (p : ℕ) (hp : p ∈ primeBand S.x (F.a i)) :
        ((pathLength S.x + 1 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
      have hpLower : Real.exp (Real.rpow L (1 / 10 : ℝ)) ≤ (p : ℝ) := by
        have hpBand := (Finset.mem_filter.mp hp).2.2.1
        have hexponent := Real.rpow_le_rpow_of_exponent_le hLone hai.1.le
        exact le_trans (Real.exp_le_exp.mpr hexponent) hpBand
      exact hpathSmallFromExp hBandPath hpLower
    have hmassPos : 0 < bandMass S.x (F.a i) := lt_of_lt_of_le (by positivity) hmassLower
    have hsum := pd5_memoryNu_mass_le_two hqd0 hqd1 i hmassPos
      (hpathSmall)
    refine ⟨hmassLower, hmassUpper, hsum, ?_⟩
    intro p hp
    have hsmall := hpathSmall p hp
    have hpplus : 0 < (p : ℝ) + 1 := by positivity
    have hbprime : (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d p := by
      have hbp := pd5_memoryBPrime_lower (x := S.x) hqd0 hqd1 p
      have hfrac : ((pathLength S.x + 1 : ℕ) : ℝ) /
          ((p : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hpplus]
        nlinarith [hsmall]
      linarith
    have hden : 0 < bandMass S.x (F.a i) * ((p : ℝ) + 1) *
        memoryBPrime S.x F.q_d p :=
      mul_pos (mul_pos hmassPos hpplus) (lt_of_lt_of_le (by norm_num) hbprime)
    have hnuNonneg : 0 ≤ memoryNu S.x K F.a F.q_d i p := by
      rw [memoryNu]
      exact div_nonneg (by norm_num) hden.le
    have hpLower : Real.exp (Real.rpow L (1 / 10 : ℝ)) ≤ (p : ℝ) := by
      have hpBand := (Finset.mem_filter.mp hp).2.2.1
      have hexponent := Real.rpow_le_rpow_of_exponent_le hLone hai.1.le
      exact le_trans (Real.exp_le_exp.mpr hexponent) hpBand
    have hfactor : (Real.log 2 / 2) *
          Real.exp (Real.rpow L (1 / 10 : ℝ)) ≤
        bandMass S.x (F.a i) * ((p : ℝ) + 1) := by
      apply mul_le_mul hmassLower (by nlinarith [hpLower]) (by positivity) (by positivity)
    have hdiv :
        2 / (bandMass S.x (F.a i) * ((p : ℝ) + 1)) ≤
          4 / (Real.log 2 * Real.exp (Real.rpow L (1 / 10 : ℝ))) := by
      apply (div_le_div_iff₀ (mul_pos hmassPos hpplus)
        (mul_pos hlog2 (Real.exp_pos _))).2
      nlinarith [hfactor]
    have hrewrite :
        4 / (Real.log 2 * Real.exp (Real.rpow L (1 / 10 : ℝ))) =
          (4 / Real.log 2) * Real.exp (-(Real.rpow L (1 / 10 : ℝ))) := by
      rw [Real.exp_neg]
      field_simp [ne_of_gt hlog2,
        ne_of_gt (Real.exp_pos (Real.rpow L (1 / 10 : ℝ)))]
    have hnu := pd5_memoryNu_bound_of_path_small (x := S.x) hqd0 hqd1 i p hmassPos hsmall
    refine ⟨hnuNonneg, ?_⟩
    calc
      memoryNu S.x K F.a F.q_d i p ≤
          2 / (bandMass S.x (F.a i) * ((p : ℝ) + 1)) := hnu
      _ ≤ 4 / (Real.log 2 * Real.exp (Real.rpow L (1 / 10 : ℝ))) := hdiv
      _ = (4 / Real.log 2) * Real.exp (-Real.rpow L (1 / 10 : ℝ)) := hrewrite
  where
    hpathSmallFromExp {x : ℝ} {p : ℕ}
        (hpath : ((pathLength x + 1 : ℕ) : ℝ) ≤
          Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) / 2)
        (hp : Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p : ℝ)) :
        ((pathLength x + 1 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
      linarith

end
end ArtinPrimitiveRoots.TypeII.PD
