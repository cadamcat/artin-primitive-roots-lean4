import ArtinPrimitiveRoots.TypeII.PD.Physical
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Smooth cutoff candidates for `completion`. The arc cutoff and the local properties of the
dyadic cutoff use Mathlib's flat smooth transition function. -/

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

def pd7_smoothStep (y : ℝ) : ℝ := Real.smoothTransition (y - 1)

def pd7_cauchyEta (y : ℝ) : ℝ := pd7_smoothStep y - pd7_smoothStep (y / 2)

def pd7_arcPsi (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 5) * Real.smoothTransition (5 - t)

lemma pd7_cauchyEta_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pd7_cauchyEta := by
  unfold pd7_cauchyEta pd7_smoothStep
  fun_prop

lemma pd7_cauchyEta_support : Function.support pd7_cauchyEta ⊆ Set.Icc 1 4 := by
  intro y hy
  change pd7_cauchyEta y ≠ 0 at hy
  by_contra hyOut
  have hyOutside : y < 1 ∨ 4 < y := by
    by_cases hylt : y < 1
    · exact Or.inl hylt
    · right
      by_contra hygt
      have hyhi : y ≤ 4 := le_of_not_gt hygt
      exact hyOut ⟨le_of_not_gt hylt, hyhi⟩
  rcases hyOutside with hyLow | hyHigh
  · have hφ₁ : pd7_smoothStep y = 0 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    have hφ₂ : pd7_smoothStep (y / 2) = 0 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    apply hy
    simp [pd7_cauchyEta, hφ₁, hφ₂]
  · have hφ₁ : pd7_smoothStep y = 1 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.one_of_one_le
      linarith
    have hφ₂ : pd7_smoothStep (y / 2) = 1 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.one_of_one_le
      linarith
    apply hy
    simp [pd7_cauchyEta, hφ₁, hφ₂]

lemma pd7_cauchyEta_nonneg (y : ℝ) : 0 ≤ pd7_cauchyEta y := by
  by_cases hy : y ≤ 0
  · have hφ₁ : pd7_smoothStep y = 0 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    have hφ₂ : pd7_smoothStep (y / 2) = 0 := by
      unfold pd7_smoothStep
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    simp [pd7_cauchyEta, hφ₁, hφ₂]
  · have hypos : 0 < y := lt_of_not_ge hy
    unfold pd7_cauchyEta
    exact sub_nonneg.mpr <| Real.smoothTransition.monotone <| by
      nlinarith

lemma pd7_cauchyEta_dyadic : IsDyadicPartition pd7_cauchyEta := by
  intro y hy
  let fpos : ℕ → ℝ := fun n => pd7_cauchyEta (y / (2 : ℝ) ^ n)
  let fneg : ℕ → ℝ := fun n => pd7_cauchyEta (y * (2 : ℝ) ^ (n + 1))
  obtain ⟨N₁, hN₁⟩ := pow_unbounded_of_one_lt y (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N₂, hN₂⟩ := pow_unbounded_of_one_lt (4 / y) (by norm_num : (1 : ℝ) < 2)
  let N : ℕ := max N₁ N₂
  have hpow₁ : (2 : ℝ) ^ N₁ ≤ (2 : ℝ) ^ N := by
    dsimp [N]
    gcongr
    · norm_num
    · exact le_max_left _ _
  have hpow₂ : (2 : ℝ) ^ N₂ ≤ (2 : ℝ) ^ N := by
    dsimp [N]
    gcongr
    · norm_num
    · exact le_max_right _ _
  have hyPow : y < (2 : ℝ) ^ N := hN₁.trans_le hpow₁
  have hfourPow : 4 / y < (2 : ℝ) ^ N := hN₂.trans_le hpow₂
  have hfrac : y / (2 : ℝ) ^ N < 1 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).2
    simpa using hyPow
  have hfourMult : 4 < y * (2 : ℝ) ^ N := by
    calc
      4 = (4 / y) * y := by field_simp [ne_of_gt hy]
      _ < (2 : ℝ) ^ N * y := mul_lt_mul_of_pos_right hfourPow hy
      _ = y * (2 : ℝ) ^ N := by ring
  have hstepZero : ∀ z : ℝ, z ≤ 1 → pd7_smoothStep z = 0 := by
    intro z hz
    unfold pd7_smoothStep
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  have hstepOne : ∀ z : ℝ, 2 ≤ z → pd7_smoothStep z = 1 := by
    intro z hz
    unfold pd7_smoothStep
    apply Real.smoothTransition.one_of_one_le
    linarith
  have hzeroPos : ∀ n : ℕ, N ≤ n → fpos n = 0 := by
    intro n hn
    have hpowNn : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ n := by
      gcongr
      norm_num
    have hratio : y / (2 : ℝ) ^ n ≤ y / (2 : ℝ) ^ N :=
      div_le_div_of_nonneg_left hy.le (by positivity) hpowNn
    have hratio' : y / (2 : ℝ) ^ n ≤ 1 := hratio.trans hfrac.le
    have hratio'' : (y / (2 : ℝ) ^ n) / 2 ≤ 1 := by linarith
    have h₁ := hstepZero (y / (2 : ℝ) ^ n) hratio'
    have h₂ := hstepZero ((y / (2 : ℝ) ^ n) / 2) hratio''
    dsimp [fpos, pd7_cauchyEta]
    rw [h₁, h₂]
    ring
  have honeNeg : ∀ n : ℕ, N ≤ n →
      pd7_smoothStep (y * (2 : ℝ) ^ n) = 1 := by
    intro n hn
    have hpowNn : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ n := by
      gcongr
      norm_num
    have hfourNn : 4 / y < (2 : ℝ) ^ n := hfourPow.trans_le hpowNn
    have hfourMultN : 4 < y * (2 : ℝ) ^ n := by
      calc
        4 = (4 / y) * y := by field_simp [ne_of_gt hy]
        _ < (2 : ℝ) ^ n * y := mul_lt_mul_of_pos_right hfourNn hy
        _ = y * (2 : ℝ) ^ n := by ring
    exact hstepOne _ (by linarith)
  have hzeroNeg : ∀ n : ℕ, N ≤ n → fneg n = 0 := by
    intro n hn
    have hstepN := honeNeg n hn
    have hn1 : N ≤ n + 1 := le_trans hn (Nat.le_succ _)
    have hstepN1 := honeNeg (n + 1) hn1
    have hscale : y * (2 : ℝ) ^ (n + 1) / 2 = y * (2 : ℝ) ^ n := by
      rw [pow_succ]
      field_simp
    dsimp [fneg, pd7_cauchyEta]
    rw [hscale, hstepN1, hstepN]
    ring
  have hfinitePos : (Function.support fpos).Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    change fpos n ≠ 0 at hn
    by_contra hnN
    exact hn (hzeroPos n (le_of_not_gt hnN))
  have hfiniteNeg : (Function.support fneg).Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    change fneg n ≠ 0 at hn
    by_contra hnN
    exact hn (hzeroNeg n (le_of_not_gt hnN))
  have hsumPos : Summable fpos := summable_of_hasFiniteSupport hfinitePos
  have hsumNeg : Summable fneg := summable_of_hasFiniteSupport hfiniteNeg
  have hpoint :
      (fun k : ℤ => pd7_cauchyEta (y / (2 : ℝ) ^ k)) = Int.rec fpos fneg := by
    funext k
    cases k with
    | ofNat n =>
        simp [fpos, zpow_natCast]
    | negSucc n =>
        have hpow : (2 : ℝ) ^ Int.negSucc n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
          simp [zpow_negSucc]
        change pd7_cauchyEta (y / (2 : ℝ) ^ Int.negSucc n) =
          pd7_cauchyEta (y * (2 : ℝ) ^ (n + 1))
        rw [hpow, div_inv_eq_mul]
  have htsumPos : (∑' n : ℕ, fpos n) = ∑ n ∈ Finset.range N, fpos n := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    exact hzeroPos n hnN
  have htsumNeg : (∑' n : ℕ, fneg n) = ∑ n ∈ Finset.range N, fneg n := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    exact hzeroNeg n hnN
  let pfun : ℕ → ℝ := fun n => pd7_smoothStep (y / (2 : ℝ) ^ n)
  have htermPos : ∀ n : ℕ, fpos n = pfun n - pfun (n + 1) := by
    intro n
    have hscale : (y / (2 : ℝ) ^ n) / 2 = y / (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      field_simp
    dsimp [fpos, pd7_cauchyEta, pfun]
    rw [hscale]
  have hsumPosFin : (∑ n ∈ Finset.range N, fpos n) = pd7_smoothStep y := by
    calc
      _ = ∑ n ∈ Finset.range N, (pfun n - pfun (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact htermPos n
      _ = pfun 0 - pfun N := Finset.sum_range_sub' pfun N
      _ = pd7_smoothStep y := by
        simp [pfun, hstepZero, hfrac.le]
  let nfun : ℕ → ℝ := fun n => pd7_smoothStep (y * (2 : ℝ) ^ n)
  have htermNeg : ∀ n : ℕ, fneg n = nfun (n + 1) - nfun n := by
    intro n
    have hscale : y * (2 : ℝ) ^ (n + 1) / 2 = y * (2 : ℝ) ^ n := by
      rw [pow_succ]
      field_simp
    dsimp [fneg, pd7_cauchyEta, nfun]
    rw [hscale]
  have hsumNegFin :
      (∑ n ∈ Finset.range N, fneg n) = 1 - pd7_smoothStep y := by
    have htel :
        (∑ n ∈ Finset.range N, (nfun n - nfun (n + 1))) = nfun 0 - nfun N :=
      Finset.sum_range_sub' nfun N
    calc
      _ = ∑ n ∈ Finset.range N, -(nfun n - nfun (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [htermNeg]
        ring
      _ = -∑ n ∈ Finset.range N, (nfun n - nfun (n + 1)) := by
        rw [Finset.sum_neg_distrib]
      _ = -(nfun 0 - nfun N) := by rw [htel]
      _ = 1 - pd7_smoothStep y := by
        have hN : nfun N = 1 := by
          dsimp [nfun]
          exact honeNeg N le_rfl
        simp [nfun, hN]
  calc
    (∑' k : ℤ, pd7_cauchyEta (y / (2 : ℝ) ^ k)) =
        (∑' n : ℕ, fpos n) + ∑' n : ℕ, fneg n := by
          rw [hpoint]
          exact tsum_int_rec hsumPos hsumNeg
    _ = pd7_smoothStep y + (1 - pd7_smoothStep y) := by
          rw [htsumPos, htsumNeg, hsumPosFin, hsumNegFin]
    _ = 1 := by ring

lemma pd7_cauchyEta_isCauchyCutoff : IsCauchyCutoff pd7_cauchyEta :=
  ⟨pd7_cauchyEta_contDiff, pd7_cauchyEta_support, pd7_cauchyEta_nonneg,
    pd7_cauchyEta_dyadic⟩

lemma pd7_arcPsi_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pd7_arcPsi := by
  unfold pd7_arcPsi
  fun_prop

lemma pd7_arcPsi_support : Function.support pd7_arcPsi ⊆ Set.Icc (-5 : ℝ) 5 := by
  intro t ht
  change pd7_arcPsi t ≠ 0 at ht
  by_contra htOut
  have hlow : -5 ≤ t := by
    by_contra h
    have ht' : t + 5 ≤ 0 := by linarith
    apply ht
    simp [pd7_arcPsi, Real.smoothTransition.zero_of_nonpos ht']
  have hhigh : t ≤ 5 := by
    by_contra h
    have ht' : 5 - t ≤ 0 := by linarith
    apply ht
    simp [pd7_arcPsi, Real.smoothTransition.zero_of_nonpos ht']
  exact htOut ⟨hlow, hhigh⟩

lemma pd7_arcPsi_hasCompactSupport : HasCompactSupport pd7_arcPsi := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact pd7_arcPsi_support

lemma pd7_arcPsi_one :
    ∀ t ∈ Set.Icc (-4 : ℝ) 4, pd7_arcPsi t = 1 := by
  intro t ht
  rcases ht with ⟨htlo, hthi⟩
  have hleft : 1 ≤ t + 5 := by linarith
  have hright : 1 ≤ 5 - t := by linarith
  simp [pd7_arcPsi, Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright]

lemma pd7_arcPsi_isCutoff : IsArcCutoff pd7_arcPsi :=
  ⟨pd7_arcPsi_contDiff, pd7_arcPsi_hasCompactSupport, pd7_arcPsi_one⟩

end

end ArtinPrimitiveRoots.TypeII.PD
