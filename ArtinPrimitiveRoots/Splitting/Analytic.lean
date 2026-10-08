import ArtinPrimitiveRoots.Splitting.FieldBounds

/-!
# §7 smoothed prime-ideal estimate

Blueprint nodes `spl:mellin-integral`, `spl:left-line`, `spl:explicit-formula`, `spl:zero-sum`,
and `spl:smooth-estimate`; source `07-splitting.tex:112-225`.
-/

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs
open Classical
open Complex

/-- A smooth compactly supported test function on the positive half-line. -/
def IsSmoothPositiveTestFunction (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
    Function.support f ⊆ Set.Ioi 0

/-- **`spl:mellin-integral`**, `07-splitting.tex:130-145`. The Mellin transform is entire and
rapidly decreasing on every vertical strip; Mellin inversion and the Dedekind Euler logarithmic
derivative give the prime-ideal identity on `Re s = 2`. -/
theorem spl_mellin_integral (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f) :
    Differentiable ℂ (mellinTransform f) ∧
      (∀ (A : ℕ) (a b : ℝ), a ≤ b →
        ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
          ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ))) ∧
      (∀ (K : Type*) [Field K] [NumberField K] (x : ℝ), 0 < x →
        (primeIdealTheta K f x : ℂ) =
          verticalLineIntegral
            (fun s : ℂ => dedekindZetaLogDerivative K s *
              Complex.cpow (x : ℂ) s * mellinTransform f s) 2) := by
  sorry

/-- **`spl:left-line`**, `07-splitting.tex:147-170`. The functional equation and D3's Euler
bound at `1-s`, with the digamma strip estimate for the gamma factors, give an absolute constant
uniform in the number field. -/
theorem spl_left_line :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|)) := by
  sorry

/-- **`spl:explicit-formula`**, `07-splitting.tex:172-210`. The contour shift crosses the pole at
`1`, the nontrivial zeros with analytic multiplicity, and the trivial zero at `0`; the remaining
fixed-line integral is `O_f(x^(-1/2)(log D+n))`. -/
theorem spl_explicit_formula (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (x : ℝ), 2 ≤ x →
      ∃ R : ℂ,
      Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
      else 0) ∧
      (primeIdealTheta K f x : ℂ) =
        (x : ℂ) * mellinTransform f 1 -
          (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
            (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
          else 0) -
          ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0 + R ∧
      ‖R‖ ≤ C * Real.rpow x (-1 / 2 : ℝ) *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) := by
  sorry

set_option maxHeartbeats 1000000
/-- **`spl:zero-sum`**, `07-splitting.tex:212-224`. Zero counting in unit-height intervals and
rapid Mellin decay make the zero sum absolutely convergent and bound it by
`x^(1-δ)(log D+n)`. -/
theorem spl_zero_sum (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type*) [Field K] [NumberField K]
      (hzero : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 →
        meromorphicOrderAt (dedekindZetaSharp K) s ≤ 0)
      (x : ℝ) (hx : 2 ≤ x),
      Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℝ) *
          ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖ else 0) ∧
      (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
        (zeroMultiplicity K ρ : ℝ) *
          ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖ else 0) ≤
        C * Real.rpow x (1 - δ) *
          (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) ∧
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℝ) *
        ‖mellinTransform f 0‖ ≤ C * Module.finrank ℚ K := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := (spl_mellin_integral.{0} f hf).2.1 3 0 1 (by norm_num)
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

  let S₂ : ℝ := ∑' k : ℤ, Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ)
  have hS₂ : 0 ≤ S₂ := by
    dsimp [S₂]
    exact tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _
  let C : ℝ := 16 * CΦ * Czero * (S₂ + 1) + ‖mellinTransform f 0‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro K _ _ hzero x hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hdiscNat : (NumberField.discr K).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hdiscCast : ((NumberField.discr K).natAbs : ℝ) = absoluteDiscriminant K := by
    simp [absoluteDiscriminant, Nat.cast_natAbs]
  have hdiscNatOne : 1 ≤ (NumberField.discr K).natAbs :=
    Nat.one_le_iff_ne_zero.mpr hdiscNat
  have hdisc : 1 ≤ absoluteDiscriminant K := by
    rw [← hdiscCast]
    exact_mod_cast hdiscNatOne
  have hlogD : 0 ≤ Real.log (absoluteDiscriminant K) := Real.log_nonneg hdisc
  have hdegree : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hW : 0 ≤ Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ) := by
    positivity
  let W : ℝ := Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ)
  let Xpow : ℝ := Real.rpow x (1 - δ)
  have hXpow : 0 < Xpow := by
    dsimp [Xpow]
    exact Real.rpow_pos_of_pos hxpos _
  have hW' : 0 ≤ W := by simpa [W] using hW
  let cOuter : ℝ := 16 * CΦ * Czero * Xpow * W
  have hcOuter : 0 ≤ cOuter := by
    dsimp [cOuter]
    positivity

  have hReBound : ∀ ρ : ℂ, ρ ∈ nontrivialZeros K → ρ.re ≤ 1 - δ := by
    intro ρ hρ
    rcases hρ with ⟨hρre, hρlt, hρzero⟩
    by_contra hbound
    have hgt : 1 - δ < ρ.re := lt_of_not_ge hbound
    have hρpos : 0 < ρ.re := by linarith [hδ']
    have hρne : ρ ≠ 1 := by
      intro heq
      rw [heq] at hρlt
      norm_num at hρlt
    have hAnalytic := dedekindZetaSharp_analyticAt K hρpos hρne
    have hOrderNe : analyticOrderAt (dedekindZetaSharp K) ρ ≠ 0 :=
      hAnalytic.analyticOrderAt_ne_zero.mpr hρzero
    have hOrderPos : 0 < meromorphicOrderAt (dedekindZetaSharp K) ρ := by
      rw [hAnalytic.meromorphicOrderAt_eq]
      cases horder : analyticOrderAt (dedekindZetaSharp K) ρ with
      | top => simp
      | coe m =>
        have hmne : m ≠ 0 := by
          intro hm
          apply hOrderNe
          simp [horder, hm]
        have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
        simpa [horder] using (show (0 : ℤ) < (m : ℤ) by exact_mod_cast hmpos)
    exact (not_lt_of_ge (hzero ρ hgt hρne)) hOrderPos

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
          change (k : ℝ) ≤ ρ.1.im ∧ ρ.1.im < (k : ℝ) + 1
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
          · simp [bins, hbin, hb, hzero, zeroMultiplicity]
        · have hbn : ¬ ((k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1) := by
            simpa [bins] using hbin
          simp [bins, hbin, hbn, zeroMultiplicity]

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
        exact Real.rpow_le_rpow_of_exponent_le hxone hRe
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
          |(k : ℝ)| = |ρ.1.im - (ρ.1.im - (k : ℝ))| := by congr 1 <;> ring
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
          simp [F, hρmem]
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

  let e : (Σ k : ℤ, bins k) ≃ ℂ := Set.sigmaEquiv bins hPartition
  have hSigmaComp : Summable (F ∘ e) := (Equiv.summable_iff e).mpr hGlobal
  have hSigma : Summable (fun p : Σ k : ℤ, bins k => F p.2.1) := by
    have hEq : (F ∘ e) = fun p : Σ k : ℤ, bins k => F p.2.1 := by
      funext p
      rfl
    rw [hEq] at hSigmaComp
    exact hSigmaComp
  have hPartitionTsum :
      (∑' ρ : ℂ, F ρ) = ∑' k : ℤ, ∑' ρ : bins k, F ρ.1 := by
    calc
      _ = ∑' p : Σ k : ℤ, bins k, F (e p) := (Equiv.tsum_eq e F).symm
      _ = ∑' p : Σ k : ℤ, bins k, F p.2.1 := by
        apply tsum_congr
        intro p
        rfl
      _ = _ := by
        simpa using hSigma.tsum_sigma' (fun k => hInner k)
  have hOuterTsum :
      (∑' k : ℤ, ∑' ρ : bins k, F ρ.1) ≤ cOuter * S₂ := by
    calc
      _ ≤ ∑' k : ℤ, cOuter * Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ) :=
        hOuter.tsum_le_tsum hBinMajor (hIntSeries.mul_left cOuter)
      _ = cOuter * S₂ := by
        change (∑' k : ℤ, cOuter * Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ)) =
          cOuter * (∑' k : ℤ, Real.rpow (1 + |(k : ℝ)|) (-2 : ℝ))
        exact hIntSeries.tsum_mul_left cOuter
  have hCscale : 16 * CΦ * Czero * S₂ ≤ C := by
    dsimp [C]
    have hBnonneg : 0 ≤ 16 * CΦ * Czero := by positivity
    have hstep : 16 * CΦ * Czero * S₂ ≤ 16 * CΦ * Czero * (S₂ + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith [hS₂]) hBnonneg
    have hnorm0 : 0 ≤ ‖mellinTransform f 0‖ := norm_nonneg _
    linarith
  have hzeroSumBound :
      (∑' ρ : ℂ, F ρ) ≤ C * Xpow * W := by
    calc
      _ ≤ cOuter * S₂ := by rw [hPartitionTsum]; exact hOuterTsum
      _ = (16 * CΦ * Czero * S₂) * (Xpow * W) := by dsimp [cOuter]; ring
      _ ≤ C * (Xpow * W) :=
        mul_le_mul_of_nonneg_right hCscale (mul_nonneg (le_of_lt hXpow) hW')
      _ = C * Xpow * W := by ring

  have hsignature := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hresidueCoeff :
      InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 ≤
        Module.finrank ℚ K := by omega
  have hresidueCoeffR :
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℝ) ≤
        (Module.finrank ℚ K : ℝ) := by exact_mod_cast hresidueCoeff
  have hΦ0leC : ‖mellinTransform f 0‖ ≤ C := by
    dsimp [C]
    have hmain : 0 ≤ 16 * CΦ * Czero * (S₂ + 1) := by positivity
    linarith
  have hresidue :
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℝ) *
          ‖mellinTransform f 0‖ ≤ C * Module.finrank ℚ K := by
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * ‖mellinTransform f 0‖ :=
        mul_le_mul_of_nonneg_right hresidueCoeffR (norm_nonneg _)
      _ = ‖mellinTransform f 0‖ * (Module.finrank ℚ K : ℝ) := by ring
      _ ≤ C * Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_right hΦ0leC (Nat.cast_nonneg _)
  refine ⟨?_, ?_, hresidue⟩
  · change Summable F
    exact hGlobal
  · change (∑' ρ : ℂ, F ρ) ≤ C * Xpow * W
    exact hzeroSumBound

set_option maxHeartbeats 200000

/-- **`spl:smooth-estimate`**, `07-splitting.tex:112-225`. For each fixed smooth nonnegative
test function and `0 < δ < 1/2`, one constant works for every number field and every `x ≥ 2`:
`Θ_{K,f}(x) ≤ C (x + x^(1-δ)(log D+n))`. -/
theorem spl_smooth_estimate (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (f : ℝ → ℝ) (hf : IsSmoothPositiveTestFunction f)
    (hfnn : ∀ t : ℝ, 0 ≤ f t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K]
      (hzero : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 →
        meromorphicOrderAt (dedekindZetaSharp K) s ≤ 0)
      (x : ℝ) (hx : 2 ≤ x),
        primeIdealTheta K f x ≤
          C * (x + Real.rpow x (1 - δ) *
            (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K)) := by
  obtain ⟨Ce, hCe, hExplicit⟩ := spl_explicit_formula f hf
  obtain ⟨Cz, hCz, hZeroSum⟩ := spl_zero_sum f hf δ hδ hδ'
  let C : ℝ := 1 + ‖mellinTransform f 1‖ + 2 * Cz + Ce
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro K _ _ hzero x hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hδexp : 0 < 1 - δ := by linarith
  have hpowPos : 0 < Real.rpow x (1 - δ) := Real.rpow_pos_of_pos hxpos _
  have hpowOne : 1 ≤ Real.rpow x (1 - δ) := by
    calc
      1 = Real.rpow x 0 := by simp
      _ ≤ Real.rpow x (1 - δ) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
  have hpowTail : Real.rpow x (-1 / 2 : ℝ) ≤ Real.rpow x (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by linarith)

  have hdiscNat : (NumberField.discr K).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hdiscCast : ((NumberField.discr K).natAbs : ℝ) = absoluteDiscriminant K := by
    simp [absoluteDiscriminant, Nat.cast_natAbs]
  have hdiscNatOne : 1 ≤ (NumberField.discr K).natAbs :=
    Nat.one_le_iff_ne_zero.mpr hdiscNat
  have hdisc : 1 ≤ absoluteDiscriminant K := by
    rw [← hdiscCast]
    exact_mod_cast hdiscNatOne
  have hlogD : 0 ≤ Real.log (absoluteDiscriminant K) := Real.log_nonneg hdisc
  have hdegree : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hdegreeR : 0 < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr hdegree
  let W : ℝ := Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ)
  have hW : 0 < W := by dsimp [W]; positivity
  have hdegree_le_W : (Module.finrank ℚ K : ℝ) ≤ W := by
    dsimp [W]
    linarith

  obtain ⟨R, hExplicitSummable, hExplicitFormula, hR⟩ := hExplicit K x hx
  obtain ⟨hZeroSummable, hZeroBound, hResidueBound⟩ := hZeroSum K hzero x hx
  let zeroTerm : ℂ → ℂ := fun ρ =>
    if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
    else 0
  let zeroNorm : ℂ → ℝ := fun ρ =>
    if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℝ) *
        ‖Complex.cpow (x : ℂ) ρ * mellinTransform f ρ‖
    else 0
  have hNormEq : (fun ρ : ℂ => ‖zeroTerm ρ‖) = zeroNorm := by
    funext ρ
    by_cases hρ : ρ ∈ nontrivialZeros K
    · simp [zeroTerm, zeroNorm, hρ, norm_mul]
      ring
    · simp [zeroTerm, zeroNorm, hρ]
  have hNormSummable : Summable (fun ρ : ℂ => ‖zeroTerm ρ‖) := by
    rw [hNormEq]
    exact hZeroSummable
  have hComplexZeroBound :
      ‖∑' ρ : ℂ, zeroTerm ρ‖ ≤ Cz * Real.rpow x (1 - δ) * W := by
    calc
      _ ≤ ∑' ρ : ℂ, ‖zeroTerm ρ‖ := norm_tsum_le_tsum_norm hNormSummable
      _ = ∑' ρ : ℂ, zeroNorm ρ := by rw [hNormEq]
      _ ≤ Cz * Real.rpow x (1 - δ) * W := by
        simpa [zeroNorm, W] using hZeroBound

  have hResidueNorm :
      ‖((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
        mellinTransform f 0‖ ≤ Cz * (Module.finrank ℚ K : ℝ) := by
    simpa only [norm_mul, Complex.norm_natCast] using hResidueBound

  have hTriangle :
      ‖(x : ℂ) * mellinTransform f 1 - (∑' ρ : ℂ, zeroTerm ρ) -
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
          mellinTransform f 0 + R‖ ≤
        ‖(x : ℂ) * mellinTransform f 1‖ +
          ‖∑' ρ : ℂ, zeroTerm ρ‖ +
          ‖((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0‖ + ‖R‖ := by
    calc
      _ ≤ ‖(x : ℂ) * mellinTransform f 1 - (∑' ρ : ℂ, zeroTerm ρ) -
          ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0‖ + ‖R‖ := norm_add_le _ _
      _ ≤ (‖(x : ℂ) * mellinTransform f 1 - (∑' ρ : ℂ, zeroTerm ρ)‖ +
          ‖((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0‖) + ‖R‖ := by
        have hsub := norm_sub_le
          ((x : ℂ) * mellinTransform f 1 - (∑' ρ : ℂ, zeroTerm ρ))
          (((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0)
        nlinarith
      _ ≤ (‖(x : ℂ) * mellinTransform f 1‖ + ‖∑' ρ : ℂ, zeroTerm ρ‖ +
          ‖((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0‖) + ‖R‖ := by
        have hsub := norm_sub_le ((x : ℂ) * mellinTransform f 1) (∑' ρ : ℂ, zeroTerm ρ)
        linarith
      _ = _ := by ring

  have hthetaNorm :
      ‖(primeIdealTheta K f x : ℂ)‖ ≤
        ‖mellinTransform f 1‖ * x +
          Cz * Real.rpow x (1 - δ) * W + Cz * (Module.finrank ℚ K : ℝ) +
            Ce * Real.rpow x (-1 / 2 : ℝ) * W := by
    rw [hExplicitFormula]
    calc
      _ ≤ ‖(x : ℂ) * mellinTransform f 1‖ +
          ‖∑' ρ : ℂ, zeroTerm ρ‖ +
          ‖((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
            mellinTransform f 0‖ + ‖R‖ := hTriangle
      _ ≤ ‖mellinTransform f 1‖ * x +
          Cz * Real.rpow x (1 - δ) * W + Cz * (Module.finrank ℚ K : ℝ) +
            Ce * Real.rpow x (-1 / 2 : ℝ) * W := by
        have hmain : ‖(x : ℂ) * mellinTransform f 1‖ =
            ‖mellinTransform f 1‖ * x := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
          ring
        rw [hmain]
        dsimp [W] at *
        nlinarith [hComplexZeroBound, hResidueNorm, hR]

  have hthetaLeNorm : primeIdealTheta K f x ≤ ‖(primeIdealTheta K f x : ℂ)‖ := by
    rw [Complex.norm_real]
    exact le_abs_self _
  have hXWnonneg : 0 ≤ Real.rpow x (1 - δ) * W := by positivity
  have hTailAbsorb :
      Ce * Real.rpow x (-1 / 2 : ℝ) * W ≤ Ce * Real.rpow x (1 - δ) * W := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpowTail hCe.le) hW.le
  have hResidueAbsorb :
      Cz * (Module.finrank ℚ K : ℝ) ≤ Cz * Real.rpow x (1 - δ) * W := by
    calc
      _ ≤ Cz * W := mul_le_mul_of_nonneg_left hdegree_le_W hCz.le
      _ ≤ Cz * (Real.rpow x (1 - δ) * W) := by
        have := mul_le_mul_of_nonneg_right hpowOne hW.le
        nlinarith [hCz.le]
      _ = Cz * Real.rpow x (1 - δ) * W := by ring
  have hcombined :
      primeIdealTheta K f x ≤
        ‖mellinTransform f 1‖ * x + (2 * Cz + Ce) *
          (Real.rpow x (1 - δ) * W) := by
    calc
      _ ≤ ‖(primeIdealTheta K f x : ℂ)‖ := hthetaLeNorm
      _ ≤ ‖mellinTransform f 1‖ * x +
          Cz * Real.rpow x (1 - δ) * W + Cz * (Module.finrank ℚ K : ℝ) +
            Ce * Real.rpow x (-1 / 2 : ℝ) * W := hthetaNorm
      _ ≤ ‖mellinTransform f 1‖ * x + (2 * Cz + Ce) *
          (Real.rpow x (1 - δ) * W) := by
        have hsumAbsorb := add_le_add hResidueAbsorb hTailAbsorb
        dsimp [W] at *
        nlinarith [hsumAbsorb]

  have hcoeffX : ‖mellinTransform f 1‖ ≤ C := by
    dsimp [C]
    have hn : 0 ≤ ‖mellinTransform f 1‖ := norm_nonneg _
    linarith [hCz, hCe]
  have hcoeffY : 2 * Cz + Ce ≤ C := by
    dsimp [C]
    have hn : 0 ≤ ‖mellinTransform f 1‖ := norm_nonneg _
    linarith
  calc
    primeIdealTheta K f x ≤
        ‖mellinTransform f 1‖ * x + (2 * Cz + Ce) *
          (Real.rpow x (1 - δ) * W) := hcombined
    _ ≤ C * (x + Real.rpow x (1 - δ) * W) := by
      have hfirst := mul_le_mul_of_nonneg_right hcoeffX hxpos.le
      have hsecond := mul_le_mul_of_nonneg_right hcoeffY hXWnonneg
      calc
        _ ≤ C * x + C * (Real.rpow x (1 - δ) * W) := add_le_add hfirst hsecond
        _ = C * (x + Real.rpow x (1 - δ) * W) := by ring

end ArtinPrimitiveRoots.Splitting

end
