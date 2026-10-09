import ArtinPrimitiveRoots.Ext.SplittingInputs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

set_option autoImplicit false

universe u

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Ext.SplittingInputs
open Classical Complex

/-- Unit-window zero counts and cubic Mellin decay give absolute convergence. -/
theorem zero_family_summable_of_decay (f : ℝ → ℝ)
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 2 ≤ x) :
    Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
      else 0) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := hdecay 3 0 1 (by norm_num)
  obtain ⟨Czero, hCzero, hZeroCount⟩ := ext_dedekind_zero_count

  have hNatSeries : Summable (fun m : ℕ => Real.rpow (1 + (m : ℝ)) (-2 : ℝ)) := by
    have hbase : Summable (fun m : ℕ => Real.rpow (m : ℝ) (-2 : ℝ)) :=
      (Real.summable_nat_rpow).2 (by norm_num)
    convert hbase.comp_injective Nat.succ_injective using 1
    ext m
    simp only [Function.comp_apply, Nat.cast_succ, add_comm]
  have hIntSeries : Summable (fun k : ℤ => Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ)) := by
    exact Summable.of_nat_of_neg
      (by simpa using hNatSeries)
      (by simpa [Int.cast_neg, abs_neg] using hNatSeries)


  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hdisc : 1 ≤ absoluteDiscriminant K := by
    have hNat : 1 ≤ (NumberField.discr K).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
    simpa [absoluteDiscriminant, Nat.cast_natAbs] using
      (show (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) by exact_mod_cast hNat)
  have hlogD : 0 ≤ Real.log (absoluteDiscriminant K) := Real.log_nonneg hdisc
  let W : ℝ := Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ)
  have hW' : 0 ≤ W := by dsimp [W]; positivity
  let Xpow : ℝ := x
  have hXpow : 0 < Xpow := hxpos
  let cOuter : ℝ := 16 * CΦ * Czero * Xpow * W
  have hReBound (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) : ρ.re ≤ 1 := hρ.2.1.le

  let bins : ℤ → Set ℂ := fun k =>
    {ρ | (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1}
  have hPartition : ∀ ρ : ℂ, ∃! k : ℤ, ρ ∈ bins k := by
    intro ρ
    refine ⟨Int.floor ρ.im, ?_, ?_⟩
    · change (Int.floor ρ.im : ℝ) ≤ ρ.im ∧ ρ.im < (Int.floor ρ.im : ℝ) + 1
      exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
    · intro k hk
      change (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1 at hk
      have hlo : k ≤ Int.floor ρ.im := Int.le_floor.mpr hk.1
      have hhi : Int.floor ρ.im ≤ k := Int.floor_le_iff.mpr hk.2
      omega

  let F : ℂ → ℝ := fun ρ =>
    if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℝ) *
        ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖
    else 0
  have hFnonneg : ∀ ρ : ℂ, 0 ≤ F ρ := by
    intro ρ
    by_cases hρ : ρ ∈ nontrivialZeros K <;> simp [F, hρ] <;> positivity

  have hCountSub : ∀ k : ℤ, Summable (fun ρ : bins k =>
      if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0) := by
    intro k
    have h := (hZeroCount K k).1.comp_injective
      (i := fun ρ : bins k => (ρ : ℂ)) Subtype.val_injective
    have hcomp : Summable (fun ρ : bins k =>
        if ρ.1 ∈ nontrivialZeros K ∧ (k : ℝ) ≤ ρ.1.im ∧
            ρ.1.im < (k : ℝ) + 1 then (zeroMultiplicity K ρ.1 : ℝ) else 0) := by
      change Summable ((fun z : ℂ =>
        if z ∈ nontrivialZeros K ∧ (k : ℝ) ≤ z.im ∧ z.im < (k : ℝ) + 1 then
          (zeroMultiplicity K z : ℝ) else 0) ∘ fun ρ : bins k => (ρ : ℂ))
      exact h
    have hEqFun :
        (fun ρ : bins k =>
          if ρ.1 ∈ nontrivialZeros K ∧ (k : ℝ) ≤ ρ.1.im ∧
              ρ.1.im < (k : ℝ) + 1 then (zeroMultiplicity K ρ.1 : ℝ) else 0) =
        (fun ρ : bins k =>
          if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0) := by
      funext ρ
      by_cases hz : ρ.1 ∈ nontrivialZeros K
      · have hb : (k : ℝ) ≤ ρ.1.im ∧ ρ.1.im < (k : ℝ) + 1 := by
          exact ρ.2
        simp [hz, hb]
      · simp [hz]
    simpa only [hEqFun] using hcomp
  have hCountEq (k : ℤ) :
      (∑' ρ : bins k, if ρ.1 ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ.1 : ℝ) else 0) =
        dedekindZeroWindowCount K k := by
    rw [ArtinPrimitiveRoots.Ext.SplittingInputs.dedekindZeroWindowCount]
    calc
      _ = ∑' ρ : ℂ, (bins k).indicator
          (fun ρ => if ρ ∈ nontrivialZeros K then
            (zeroMultiplicity K ρ : ℝ) else 0) ρ :=
        tsum_subtype (bins k) _
      _ = _ := by
        apply tsum_congr
        intro ρ
        simp only [Set.indicator_apply]
        by_cases hbin : ρ ∈ bins k
        · have hb : (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1 := by
            simpa [bins] using hbin
          by_cases hzero : ρ ∈ nontrivialZeros K
          · simp [bins, hbin, hb, hzero, zeroMultiplicity]
          · simp [bins, hbin, hb, hzero]
        · have hbn : ¬ ((k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1) := by
            simpa [bins] using hbin
          simp [bins, hbin, hbn]

  have hTermBound (k : ℤ) (ρ : bins k) :
      F ρ.1 ≤
        (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) *
          (if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0) := by
    by_cases hρ : ρ.1 ∈ nontrivialZeros K
    · rcases hρ with ⟨hρre, hρlt, hρzero⟩
      have hρmem : ρ.1 ∈ nontrivialZeros K := ⟨hρre, hρlt, hρzero⟩
      have hRe := hReBound ρ.1 ⟨hρre, hρlt, hρzero⟩
      have hpow : Real.rpow x ρ.1.re ≤ Xpow := by
        dsimp [Xpow]
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hxone hRe
      have hcpow : ‖Complex.cpow (x : ℂ) ρ.1‖ = Real.rpow x ρ.1.re := by
        exact Complex.norm_cpow_eq_rpow_re_of_pos hxpos ρ.1
      have hdecay := hΦ ρ.1 hρre.le hρlt.le
      have hnorm :
          ‖Complex.cpow (x : ℂ) ρ.1 * mellinTransform f ρ.1‖ ≤
            CΦ * Xpow * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) := by
        calc
          _ = Real.rpow x ρ.1.re * ‖mellinTransform f ρ.1‖ := by
            rw [norm_mul, hcpow]
          _ ≤ Real.rpow x ρ.1.re *
              (CΦ * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg hxpos.le _)
          _ ≤ Xpow * (CΦ * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow
              (mul_nonneg hCΦ.le (Real.rpow_nonneg (by positivity) _))
          _ = CΦ * Xpow * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) := by ring
      have hbin := ρ.2
      change (k : ℝ) ≤ ρ.1.im ∧ ρ.1.im < (k : ℝ) + 1 at hbin
      have hdiff0 : 0 ≤ ρ.1.im - (k : ℝ) := by linarith [hbin.1]
      have hdiff1 : ρ.1.im - (k : ℝ) < 1 := by linarith [hbin.2]
      have hdiffAbs : |ρ.1.im - (k : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hdiff0]
        linarith
      have hkAbs : |(k : ℝ)| ≤ |ρ.1.im| + 1 := by
        calc
          |(k : ℝ)| = |ρ.1.im - (ρ.1.im - (k : ℝ))| := by congr 1; ring
          _ ≤ |ρ.1.im| + |(k : ℝ) - ρ.1.im| := by
            simpa [sub_zero, zero_sub, abs_neg] using
              abs_sub_le ρ.1.im 0 (ρ.1.im - (k : ℝ))
          _ = |ρ.1.im| + |ρ.1.im - (k : ℝ)| := by rw [abs_sub_comm]
          _ ≤ |ρ.1.im| + 1 := by linarith
      have hA : 1 + |(k : ℝ)| ≤ 2 * (1 + |ρ.1.im|) := by
        nlinarith [hkAbs, abs_nonneg ρ.1.im, abs_nonneg (k : ℝ)]
      have hbinDecay :
          Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) ≤
            8 * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) := by
        have hScale := Real.rpow_le_rpow_of_nonpos
          (by positivity : 0 < 1 + |(k : ℝ)|) hA (by norm_num : (-3 : ℝ) ≤ 0)
        have htwo : Real.rpow (2 : ℝ) (-3 : ℝ) = 1 / 8 := by
          calc
            Real.rpow (2 : ℝ) (-3 : ℝ) = (2 : ℝ) ^ (-3 : ℤ) := by
              simpa using (Real.rpow_intCast (2 : ℝ) (-3 : ℤ))
            _ = 1 / 8 := by norm_num
        have h' : (1 / 8 : ℝ) * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) ≤
            Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) := by
          calc
            _ = Real.rpow (2 : ℝ) (-3 : ℝ) *
                Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) := by rw [htwo]
            _ = Real.rpow (2 * (1 + |ρ.1.im|)) (-3 : ℝ) := by
              simpa using (Real.mul_rpow (x := (2 : ℝ))
                (y := 1 + |ρ.1.im|) (z := (-3 : ℝ))
                (by norm_num) (by positivity)).symm
            _ ≤ _ := hScale
        have hscaled := mul_le_mul_of_nonneg_left h' (by norm_num : 0 ≤ (8 : ℝ))
        nlinarith
      have hcoeff :
          CΦ * Xpow * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ) ≤
            8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) := by
        calc
          _ ≤ CΦ * Xpow *
              (8 * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hbinDecay (by positivity)
          _ = _ := by ring
      have hm : 0 ≤ (zeroMultiplicity K ρ.1 : ℝ) := Nat.cast_nonneg _
      calc
        F ρ.1 = (zeroMultiplicity K ρ.1 : ℝ) *
            ‖Complex.cpow (x : ℂ) ρ.1 * mellinTransform f ρ.1‖ := by
          simp [F, hρmem]
        _ ≤ (zeroMultiplicity K ρ.1 : ℝ) *
            (CΦ * Xpow * Real.rpow (1 + |ρ.1.im|) (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hnorm hm
        _ ≤ (zeroMultiplicity K ρ.1 : ℝ) *
            (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hcoeff hm
        _ = _ := by
          simp [hρmem]
          ring
    · simp [F, hρ]

  have hInner : ∀ k : ℤ, Summable (fun ρ : bins k => F ρ.1) := by
    intro k
    have hmajor : Summable (fun ρ : bins k =>
        (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) *
          (if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0)) :=
      (hCountSub k).mul_left _
    exact Summable.of_nonneg_of_le
      (fun ρ => hFnonneg ρ.1)
      (fun ρ => hTermBound k ρ)
      hmajor

  have hBinTsum (k : ℤ) :
      (∑' ρ : bins k, F ρ.1) ≤
        (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) *
          (Czero * (Real.log (absoluteDiscriminant K) +
            (Module.finrank ℚ K : ℝ) * Real.log (2 + |(k : ℝ)|))) := by
    let b : ℝ := 8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hscaled : Summable (fun ρ : bins k => b *
        (if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0)) :=
      (hCountSub k).mul_left b
    calc
      _ ≤ ∑' ρ : bins k, b *
          (if ρ.1 ∈ nontrivialZeros K then (zeroMultiplicity K ρ.1 : ℝ) else 0) :=
        (hInner k).tsum_le_tsum (fun ρ => by simpa [b] using hTermBound k ρ) hscaled
      _ = b * dedekindZeroWindowCount K k := by
        rw [(hCountSub k).tsum_mul_left b, hCountEq k]
      _ ≤ b * (Czero * (Real.log (absoluteDiscriminant K) +
            (Module.finrank ℚ K : ℝ) * Real.log (2 + |(k : ℝ)|))) := by
        exact mul_le_mul_of_nonneg_left (hZeroCount K k).2 hb

  have hBinMajor (k : ℤ) :
      (∑' ρ : bins k, F ρ.1) ≤ cOuter *
        Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ) := by
    have hlogk : Real.log (2 + |(k : ℝ)|) ≤ 2 * (1 + |(k : ℝ)|) := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |(k : ℝ)|)
      nlinarith [abs_nonneg (k : ℝ)]
    have hAone : 1 ≤ 2 * (1 + |(k : ℝ)|) := by
      nlinarith [abs_nonneg (k : ℝ)]
    have hnnonneg : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    have hmulLog :
        (Module.finrank ℚ K : ℝ) * Real.log (2 + |(k : ℝ)|) ≤
          (Module.finrank ℚ K : ℝ) * (2 * (1 + |(k : ℝ)|)) :=
      mul_le_mul_of_nonneg_left hlogk hnnonneg
    have hmulD : Real.log (absoluteDiscriminant K) ≤
        2 * (1 + |(k : ℝ)|) * Real.log (absoluteDiscriminant K) := by
      calc
        Real.log (absoluteDiscriminant K) = 1 * Real.log (absoluteDiscriminant K) := by ring
        _ ≤ 2 * (1 + |(k : ℝ)|) * Real.log (absoluteDiscriminant K) :=
          mul_le_mul_of_nonneg_right hAone hlogD
    have hlogmajor :
        Real.log (absoluteDiscriminant K) +
            (Module.finrank ℚ K : ℝ) * Real.log (2 + |(k : ℝ)|) ≤
          2 * (1 + |(k : ℝ)|) * W := by
      calc
        _ ≤ Real.log (absoluteDiscriminant K) +
              (Module.finrank ℚ K : ℝ) * (2 * (1 + |(k : ℝ)|)) := by
          linarith [hmulLog]
        _ ≤ 2 * (1 + |(k : ℝ)|) * Real.log (absoluteDiscriminant K) +
              (Module.finrank ℚ K : ℝ) * (2 * (1 + |(k : ℝ)|)) := by
          linarith [hmulD]
        _ = 2 * (1 + |(k : ℝ)|) * W := by
          simp [W]
          ring
    have hpowA : Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) *
        (1 + |(k : ℝ)|) = Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ) := by
      calc
        _ = Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) *
            Real.rpow (1 + |(k : ℝ)|) (1 : ℝ) := by
          congr 1
          exact (Real.rpow_one _).symm
        _ = Real.rpow (1 + |(k : ℝ)|) ((-3 : ℝ) + 1) :=
          (Real.rpow_add (by positivity) (-3 : ℝ) 1).symm
        _ = _ := by norm_num
    calc
      _ ≤ (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) *
          (Czero * (Real.log (absoluteDiscriminant K) +
            (Module.finrank ℚ K : ℝ) * Real.log (2 + |(k : ℝ)|))) := hBinTsum k
      _ ≤ (8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ)) *
          (Czero * (2 * (1 + |(k : ℝ)|) * W)) := by
        have hcountLog := mul_le_mul_of_nonneg_left hlogmajor hCzero.le
        have hBinCoeff : 0 ≤ 8 * CΦ * Xpow * Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCΦ.le) hXpow.le)
            (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left hcountLog hBinCoeff
      _ = cOuter * Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ) := by
        calc
          _ = (16 * CΦ * Czero * Xpow * W) *
              (Real.rpow (1 + |(k : ℝ)|) (-3 : ℝ) * (1 + |(k : ℝ)|)) := by ring
          _ = (16 * CΦ * Czero * Xpow * W) *
              Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ) := by rw [hpowA]
          _ = _ := by rfl

  have hOuter : Summable (fun k : ℤ => ∑' ρ : bins k, F ρ.1) := by
    exact Summable.of_nonneg_of_le
      (fun k : ℤ => tsum_nonneg (fun ρ : bins k => hFnonneg ρ.1))
      hBinMajor (hIntSeries.mul_left cOuter)
  have hGlobal : Summable F := by
    exact (summable_partition hFnonneg (s := bins) hPartition).2 ⟨hInner, hOuter⟩

  apply Summable.of_norm
  convert hGlobal using 1
  ext ρ
  by_cases hρ : ρ ∈ nontrivialZeros K
  · simp [F, hρ]
    ring
  · simp [F, hρ]

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
