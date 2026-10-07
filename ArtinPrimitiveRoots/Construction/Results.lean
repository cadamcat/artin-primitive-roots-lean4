import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c2.PartialSummation
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.RoughDensity

/-! Statements for the prime construction in `12-construction.tex`. -/

namespace ArtinPrimitiveRoots.Construction

open Classical
open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction.ProofsC2

/-- `co:support`, 12-construction.tex:53-67. The construction multiplier is invariant under
marked primes; nonzero weights have the stated factorization and are bounded uniformly. -/
theorem support (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (hM : 0 < M) (hc : c = 2 ∨ c = 4) (ha : ValidBands K a)
    (hΨ₀ : ∀ y, 0 ≤ Ψ y) (hΨ₁ : ∀ y, Ψ y ≤ 1)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    ∃ B x₀ : ℝ, 0 < B ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (∀ h p, p ∈ markedPrimes x K a → p.Prime →
          conFactor x c K a (p * h) = conFactor x c K a h) ∧
        (∀ d, conWeight x M c u K a Ψ d ≠ 0 →
          x < (d : ℝ) ∧ (d : ℝ) < 2 * x ∧
            ∃ r Q : ℕ, d - 1 = c * r * Q ∧ Q.Prime ∧
              Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
              IsGroupInteger x K a r ∧ (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) ∧
              markedWeight x K a (1 / 2 : ℝ) (d - 1) =
                markedWeight x K a (1 / 2 : ℝ) r) ∧
        ∀ d, 0 ≤ conWeight x M c u K a Ψ d ∧
          conWeight x M c u K a Ψ d ≤ B := by
  sorry

/-- `con:type-ii`, 12-construction.tex:92-159. Here `R_γ` and `B_γ` are the rough indicator and
the Buchstab proxy, and the weight is the actual §12 weight. The threshold for `K` depends on the
Type II scale parameter only; the estimate is uniform in dyads, intervals, and coefficients. -/
theorem con_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M c : ℕ, ∀ u : ℤ,
      ∀ a : Fin K → ℝ, ValidBands K a →
      0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
      Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
      Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
      ∀ Ψ : ℝ → ℝ, (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) →
        Function.support Ψ ⊆ Set.Ioo 1 2 →
        ContDiff ℝ ⊤ Ψ → 0 < ∫ y in (1 : ℝ)..2, Ψ y →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ b : ℕ → ℂ,
                  (∀ n, b n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers Hn, ‖b n‖ ≤ 1) →
                  ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                    ∑ n ∈ dyadicIntegers Hn,
                      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
                        b n * (conWeight x M c u K a Ψ (m * n) : ℂ)‖ ≤
                    C₀ * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
  sorry

/-- `con:harmonic`, 12-construction.tex:184-237. The tail bound is for `r > x^ε` (every partial sum up to `R`; the
terms are nonnegative), as in the paper; the first skeleton bounded `r ≤ x^ε` (lane `c2b`, 2026-10-07). -/
theorem con_harmonic (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (K : ℕ) (a : Fin K → ℝ) (hM : 0 < M) (hc : 0 < c)
    (ha : ValidBands K a) (hΨ : IsTestFunction Ψ) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (groupHarmonicMass x K a =
          ∏ i : Fin K,
            deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) /
              bandMass x (a i)) ∧
        1 ≤ groupHarmonicMass x K a ∧ groupHarmonicMass x K a ≤ C ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ Cε xε : ℝ, 0 < Cε ∧ 2 ≤ xε ∧
            ∀ x : ℝ, xε ≤ x →
              ∀ R : ℕ, ∑ r ∈ (Finset.range (R + 1)).filter
                  (fun r => IsGroupInteger x K a r ∧ Real.rpow x ε < (r : ℝ)),
                markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) ≤
                      Cε * Real.exp (-ε * Real.rpow (Real.log x)
                        (1 - a ⟨K - 1, by
                          have hKpos : 0 < K := ha.1
                          omega⟩))) ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ Cε xε : ℝ, 0 < Cε ∧ 2 ≤ xε ∧
            ∀ x : ℝ, xε ≤ x →
              (∑ r ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun r =>
                    IsGroupInteger x K a r ∧ Real.rpow x ε < (r : ℝ)),
                  markedWeight x K a (1 / 2 : ℝ) r *
                    progressionPrimeSum x M c u Ψ r 1) ≤
                Cε * x * Real.exp (-ε * Real.rpow (Real.log x)
                  (1 - a ⟨K - 1, by
                    have hKpos : 0 < K := ha.1
                    omega⟩))) ∧
        (∀ r, IsGroupInteger x K a r →
          progressionPrimeSum x M c u Ψ r 1 ≤ C * x / (r : ℝ)) := by
  sorry

set_option maxHeartbeats 0
/-- `co:bv-smoothed`, 12-construction.tex:286-349. The progression hypotheses `hc24`, `hu`, `hcu`, `hcu'` (those of
`prop:controlled`) were added on 2026-10-07: without them the statement is false (lane `c2`, `M = 4, c = 2, u = 1`). -/
theorem bv_smoothed (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (ε κ : ℝ)
    (hM : 0 < M) (hc : 0 < c) (hcM : c ∣ M)
    (hc24 : c = 2 ∨ c = 4) (hu : Int.gcd u M = 1) (hcu : (c : ℤ) ∣ u - 1)
    (hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1)
    (hε : 0 < ε) (hεκ : ε < κ) (hκ : κ < 1 / 100)
    (ha : ValidBands K a) (hΨ : IsTestFunction Ψ) :
    ∀ A : ℝ, 0 < A →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ r : ℕ, IsGroupInteger x K a r →
            (r : ℝ) ≤ Real.rpow x ε →
              (∑ ℓ ∈ oddSquarefreeUpTo (Real.rpow x (1 / 2 - κ / 2)),
                |progressionPrimeSum x M c u Ψ r ℓ -
                  localSieveDensity M r ℓ * smoothedMainTerm x c r Ψ /
                    (Nat.totient (M / c) : ℝ)|) ≤
                  C * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
  intro A hA
  classical
  rcases hΨ with ⟨hΨsmooth, hΨsupp, hΨnonneg, hΨle, hΨint⟩
  let N : ℕ := M / c
  have hMN : c * N = M := by
    dsimp [N]
    exact Nat.mul_div_cancel' hcM
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (Nat.le_of_dvd hM hcM) hc
  let z : ℤ := (u - 1) / (c : ℤ)
  have hz : (c : ℤ) * z = u - 1 := by
    dsimp [z]
    exact Int.mul_ediv_cancel' hcu
  have hZgcd : Int.gcd z (N : ℤ) = 1 := by
    simpa [z, N] using hcu'
  let A' : ℝ := A + 3
  have hA' : 0 < A' := by dsimp [A']; linarith
  let eta : ℝ := (κ - ε) / 4
  let theta : ℝ := 1 / 2 - eta
  let beta : ℝ := 1 / 2 - κ / 2
  let gap : ℝ := (1 - ε) * theta - beta
  have heta : 0 < eta := by dsimp [eta]; linarith
  have htheta : 0 < theta := by dsimp [theta, eta]; nlinarith
  have hbeta : 0 < beta := by dsimp [beta]; linarith
  have hgapEq : gap = (κ - ε) * (1 + ε) / 4 := by
    dsimp [gap, theta, beta, eta]
    ring
  have hgap : 0 < gap := by rw [hgapEq]; positivity
  obtain ⟨CBV, yBV, hCBV, hyBV, hBV⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.bombieri_vinogradov A' eta hA' heta
  have hΨderiv : Continuous (deriv Ψ) := hΨsmooth.continuous_deriv (by simp)
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨderiv.continuousOn
  let B : ℝ := |B₀| + 1
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hΨderivBound (y : ℝ) (hy : y ∈ Set.Icc 1 2) : |deriv Ψ y| ≤ B := by
    have hnorm := hB₀ y hy
    calc
      |deriv Ψ y| = ‖deriv Ψ y‖ := by rw [Real.norm_eq_abs]
      _ ≤ B₀ := hnorm
      _ ≤ |B₀| + 1 := by linarith [le_abs_self B₀]
  let V : ℝ := Real.rpow (1 / 2 : ℝ) (-A')
  have hVpos : 0 < V := by
    dsimp [V]
    exact Real.rpow_pos_of_pos (by norm_num) _
  let C : ℝ := 20 * B * CBV * V
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨xMark, hxMark⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_markedPrimes_gt (max M 2) K a ha
  obtain ⟨xCut, hxCutPow⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_real_rpow_ge
      (δ := (9 / 100 : ℝ)) (B := 8) (by norm_num)
  obtain ⟨xLevel, hxLevel⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_real_rpow_ge
      (δ := gap) (B := (N : ℝ) * Real.rpow 8 theta) hgap
  obtain ⟨xLarge, hxLarge⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_real_rpow_ge
      (δ := (9 / 10 : ℝ)) (B := max yBV 2) (by norm_num)
  obtain ⟨xExp, hxExp⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_real_rpow_ge
      (δ := (1 : ℝ)) (B := Real.exp 1) (by norm_num)
  let x₀ : ℝ := max 2 (max xMark (max xCut (max xLevel (max xLarge xExp))) )
  refine ⟨C, x₀, hC, ?_, ?_⟩
  · exact le_trans (by norm_num) (le_max_left _ _)
  · intro x hx r hr hrex
    have hxParts : 2 ≤ x ∧ xMark ≤ x ∧ xCut ≤ x ∧ xLevel ≤ x ∧
        xLarge ≤ x ∧ xExp ≤ x := by
      dsimp [x₀] at hx
      simpa only [max_le_iff] using hx
    rcases hxParts with ⟨hx2, hxMarkX, hxCutX, hxLevelX, hxLargeX, hxExpX⟩
    have hxCut : 8 ≤ Real.rpow x (9 / 100 : ℝ) := hxCutPow x hxCutX
    have hxLevel : (N : ℝ) * Real.rpow 8 theta ≤ Real.rpow x gap :=
      hxLevel x hxLevelX
    have hxLarge : max yBV 2 ≤ Real.rpow x (9 / 10 : ℝ) :=
      hxLarge x hxLargeX
    have hxExp' : Real.exp 1 ≤ x := by
      calc
        Real.exp 1 ≤ Real.rpow x (1 : ℝ) := hxExp x hxExpX
        _ = x := Real.rpow_one x
    have hlogx : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxExp'
      simpa using h
    have hlogxpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlogx
    have hxpos : 0 < x := by linarith [hx2]
    have hMarksM (p : ℕ) (hp : p ∈ markedPrimes x K a) :
        (M : ℝ) < (p : ℝ) := by
      exact lt_of_le_of_lt (by exact_mod_cast (Nat.le_max_left M 2))
        (hxMark x hxMarkX p hp)
    have hMarks2 (p : ℕ) (hp : p ∈ markedPrimes x K a) :
        (2 : ℝ) < (p : ℝ) := by
      exact lt_of_le_of_lt (by exact_mod_cast (Nat.le_max_right M 2))
        (hxMark x hxMarkX p hp)
    have hrpos : 0 < r :=
      ArtinPrimitiveRoots.Construction.ProofsC2.groupInteger_pos_of_marks_gt_two
        x K r a hMarks2 hr
    have hrM : Nat.Coprime r M :=
      ArtinPrimitiveRoots.Construction.ProofsC2.groupInteger_coprime_modulus
        x M K r a hM hMarksM hr
    have hrN : Nat.Coprime r N := hrM.coprime_dvd_right (Nat.div_dvd_of_dvd hcM)
    let cr : ℝ := ((c * r : ℕ) : ℝ)
    have hcr : 0 < cr := by dsimp [cr]; positivity
    have hcLower : (2 : ℝ) ≤ (c : ℝ) := by
      rcases hc24 with h | h <;> norm_num [h]
    have hcUpper : (c : ℝ) ≤ 4 := by
      rcases hc24 with h | h <;> norm_num [h]
    have hcrUpper : cr ≤ 4 * Real.rpow x ε := by
      dsimp [cr]
      rw [Nat.cast_mul]
      calc
        (c : ℝ) * (r : ℝ) ≤ 4 * (r : ℝ) :=
          mul_le_mul_of_nonneg_right hcUpper (Nat.cast_nonneg _)
        _ ≤ 4 * Real.rpow x ε :=
          mul_le_mul_of_nonneg_left hrex (by norm_num)
    have hεsmall : ε < 1 / 100 := lt_trans hεκ hκ
    have hcutoff : Real.rpow x (9 / 10 : ℝ) ≤ (x - 1) / cr :=
      ArtinPrimitiveRoots.Construction.ProofsC2.real_interval_lower_cutoff
        x cr ε hx2 hεsmall hcr hcrUpper hxCut
    have hzUnit := ArtinPrimitiveRoots.Construction.ProofsC2.int_gcd_one_zmod_isUnit hZgcd
    let lo : ℝ := (x - 1) / cr
    let hi : ℝ := (2 * x - 1) / cr
    have hcrLower : (2 : ℝ) ≤ cr := by
      dsimp [cr]
      rw [Nat.cast_mul]
      have hrOne : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hrpos.ne')
      nlinarith [mul_le_mul_of_nonneg_right hcLower (show 0 ≤ (r : ℝ) by positivity)]
    have hlo0 : 0 ≤ lo := by
      dsimp [lo]
      exact div_nonneg (by linarith [hx2]) hcr.le
    have hloCut : Real.rpow x (9 / 10 : ℝ) ≤ lo := by
      simpa [lo] using hcutoff
    have hloGrow : Real.rpow x (1 - ε) / 8 ≤ lo := by
      exact ArtinPrimitiveRoots.Construction.ProofsC2.real_interval_lower_growth
        x cr ε hx2 hcr hcrUpper
    have hlohi : lo ≤ hi := by
      dsimp [lo, hi]
      rw [div_le_div_iff_of_pos_right hcr]
      nlinarith [hx2]
    let D : ℝ := Real.rpow x beta
    let S : Finset ℕ := oddSquarefreeUpTo D
    let Sgood : Finset ℕ := S.filter (fun ell => Nat.Coprime ell (M * r))
    let I := Sgood.attach
    have hEllPos (ell : ℕ) (hell : ell ∈ S) : 0 < ell := by
      have hell' : ell ∈ oddSquarefreeUpTo D := by simpa [S] using hell
      unfold oddSquarefreeUpTo at hell'
      have hOdd := (Finset.mem_filter.mp hell').2.1
      by_contra hn
      have hz0 : ell = 0 := Nat.eq_zero_of_not_pos hn
      subst ell
      simp at hOdd
    let crtData : ∀ i : {ell // ell ∈ Sgood},
        ∃ v : ℕ, v < N * i.1 ∧ Nat.Coprime v (N * i.1) ∧
          ∀ Q : ℕ,
            ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ i.1 ∣ c * r * Q + 1) ↔
              Q ≡ v [MOD N * i.1]) := by
      intro i
      rcases Finset.mem_filter.mp i.2 with ⟨hiS, hiGood⟩
      exact ArtinPrimitiveRoots.Construction.ProofsC2.progressionClass_data
        M c N r i.1 u z hMN hc hNpos (hEllPos i.1 hiS) hz hrN hZgcd hiGood
    let qI : {ell // ell ∈ Sgood} → ℕ := fun i => N * i.1
    let vI : {ell // ell ∈ Sgood} → ℕ := fun i => Classical.choose (crtData i)
    have hvSpec (i : {ell // ell ∈ Sgood}) :
        vI i < qI i ∧ Nat.Coprime (vI i) (qI i) ∧
          ∀ Q : ℕ,
            ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ i.1 ∣ c * r * Q + 1) ↔
              Q ≡ vI i [MOD qI i]) := by
      simpa [qI, vI] using Classical.choose_spec (crtData i)
    have hqInj : Set.InjOn qI I := by
      intro i hi j hj hij
      apply Subtype.ext
      exact Nat.mul_left_cancel hNpos hij
    have hhi2x : hi ≤ 2 * x := by
      dsimp [hi]
      rw [div_le_iff₀ hcr]
      have hcrOne : (1 : ℝ) ≤ cr := by linarith [hcrLower]
      have hmul : 2 * x ≤ (2 * x) * cr := by
        have h := mul_le_mul_of_nonneg_left hcrOne (by positivity : 0 ≤ 2 * x)
        simpa using h
      linarith
    have hfloorhi : ⌊hi⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_mono hhi2x
    have hT (n : ℕ) (hn : smoothProgressionFunction x c r Ψ (n : ℝ) ≠ 0) :
        n ∈ Finset.range (⌊2 * x⌋₊ + 1) := by
      have hsupport := ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_support_bounds
        x cr (Real.rpow x (9 / 10 : ℝ)) lo hi Ψ n hxpos hcr hlo0 hloCut rfl rfl hΨsupp
        (by simpa [smoothProgressionFunction, cr] using hn)
      have hnhi := (Finset.mem_Ioc.mp hsupport.2).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans hnhi hfloorhi))
    have hIntervalSupport (n : ℕ)
        (hn : smoothProgressionFunction x c r Ψ (n : ℝ) ≠ 0) :
        n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ := by
      exact (ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_support_bounds
        x cr (Real.rpow x (9 / 10 : ℝ)) lo hi Ψ n hxpos hcr hlo0 hloCut rfl rfl hΨsupp
        (by simpa [smoothProgressionFunction, cr] using hn)).2
    have hqBound (y : ℝ) (hy : y ∈ Set.Icc lo hi)
        (i : {ell // ell ∈ Sgood}) :
        qI i ≤ ⌊Real.rpow y theta⌋₊ := by
      have hiS := (Finset.mem_filter.mp i.2).1
      have hSRange : i.1 < ⌊D⌋₊ + 1 := by
        simpa [S, D, oddSquarefreeUpTo] using (Finset.mem_filter.mp hiS).1
      have hiNat : i.1 ≤ ⌊D⌋₊ := Nat.lt_succ_iff.mp hSRange
      have hDpos : 0 < D := by dsimp [D]; positivity
      have hiReal : (i.1 : ℝ) ≤ Real.rpow x beta := by
        calc
          (i.1 : ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast hiNat
          _ ≤ D := Nat.floor_le hDpos.le
          _ = Real.rpow x beta := rfl
      have hgapDef : gap = (1 - ε) * theta - beta := rfl
      have hprod := ArtinPrimitiveRoots.Construction.ProofsC2.nat_product_le_rpow_of_growth
        N i.1 x ε beta theta gap (by linarith [hx2]) htheta hiReal hgapDef hxLevel
      have hyLower : Real.rpow x (1 - ε) / 8 ≤ y := le_trans hloGrow hy.1
      have hbasepos : 0 < Real.rpow x (1 - ε) / 8 :=
        div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num)
      have hpower := Real.rpow_le_rpow hbasepos.le hyLower htheta.le
      have hqreal : ((N * i.1 : ℕ) : ℝ) ≤ Real.rpow y theta := by
        simpa [qI] using le_trans hprod hpower
      have hqnat : N * i.1 ≤ ⌊Real.rpow y theta⌋₊ := Nat.le_floor hqreal
      simpa [qI] using hqnat
    have hBVinterval (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (∑ q ∈ Finset.range (⌊Real.rpow y theta⌋₊ + 1),
          ArtinPrimitiveRoots.Ext.TypeIIInputs.primeProgressionError y q) ≤
          CBV * y * Real.rpow (Real.log y) (-A') := by
      have hy0 : yBV ≤ y := by
        exact le_trans (le_max_left yBV 2)
          (le_trans hxLarge (le_trans hloCut hy.1))
      simpa [theta] using hBV y hy0
    have hlogHalf (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (1 / 2 : ℝ) * Real.log x ≤ Real.log y := by
      have hpowy : Real.rpow x (9 / 10 : ℝ) ≤ y := le_trans hloCut hy.1
      have hlog := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hpowy
      rw [Real.log_rpow hxpos] at hlog
      nlinarith [hlogx]
    let f : ℝ → ℝ := smoothProgressionFunction x c r Ψ
    let E : ℝ → ℝ := fun t => CBV * t * Real.rpow (Real.log t) (-A')
    let coeff : {ell // ell ∈ Sgood} → ℕ → ℝ := fun i n =>
      ArtinPrimitiveRoots.Construction.ProofsC2.progressionClassIndicator
        (qI i) (vI i) n
    let α : {ell // ell ∈ Sgood} → ℝ := fun i =>
      1 / (Nat.totient (qI i) : ℝ)
    have hClass (i : {ell // ell ∈ Sgood}) (Q : ℕ) :
        ( (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ i.1 ∣ c * r * Q + 1) ↔
          (Q : ZMod (qI i)) = (vI i : ZMod (qI i))) := by
      constructor
      · intro h
        exact (ZMod.natCast_eq_natCast_iff Q (vI i) (qI i)).2
          ((hvSpec i).2.2 Q |>.mp h)
      · intro h
        exact (hvSpec i).2.2 Q |>.mpr
          ((ZMod.natCast_eq_natCast_iff Q (vI i) (qI i)).1 h)
    have hCut (n : ℕ)
        (hn : smoothProgressionFunction x c r Ψ (n : ℝ) ≠ 0) :
        Real.rpow x (9 / 10 : ℝ) < (n : ℝ) :=
      (ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_support_bounds
        x cr (Real.rpow x (9 / 10 : ℝ)) lo hi Ψ n hxpos hcr hlo0 hloCut rfl rfl hΨsupp
        (by simpa [smoothProgressionFunction, cr] using hn)).1
    have hRangeToIoc (i : {ell // ell ∈ Sgood}) :
        progressionPrimeSum x M c u Ψ r i.1 =
          ∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊, f (n : ℝ) * coeff i n := by
      have hbridge := ArtinPrimitiveRoots.Construction.ProofsC2.progressionPrimeSum_eq_crt_sum
        x M c u Ψ r i.1 (qI i) (vI i)
        (Finset.range (⌊2 * x⌋₊ + 1)) (by intro n hn; exact hn)
        (by intro n hn; exact hT n (by simpa [f] using hn))
        (by intro n hn; exact hCut n (by simpa [f] using hn))
        (by intro n; exact hClass i n)
      calc
        progressionPrimeSum x M c u Ψ r i.1 =
            ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
              smoothProgressionFunction x c r Ψ (n : ℝ) *
                ArtinPrimitiveRoots.Construction.ProofsC2.progressionClassIndicator
                  (qI i) (vI i) n := hbridge
        _ = ∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊, f (n : ℝ) * coeff i n := by
          simpa [f, coeff] using
            (ArtinPrimitiveRoots.Construction.ProofsC2.sum_range_eq_sum_Ioc_of_support
              x lo hi f (coeff i) hlohi hfloorhi
              (by intro n hn; exact hIntervalSupport n (by simpa [f] using hn)))
    have hcount (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (∑ i ∈ I,
          |ArtinPrimitiveRoots.Construction.ProofsC2.partialCoefficientSum (coeff i) y -
            α i * ArtinPrimitiveRoots.Ext.TypeIIInputs.logarithmicIntegral y|) ≤ E y := by
      have hsum := ArtinPrimitiveRoots.Construction.ProofsC2.sum_progression_class_errors_le_bv
        I qI vI (⌊Real.rpow y theta⌋₊) y hqInj
        (fun i hi => hqBound y hy i)
        (fun i hi => (hvSpec i).1)
        (fun i hi => (hvSpec i).2.1)
      have hcountTerm (i : {ell // ell ∈ Sgood}) :
          ArtinPrimitiveRoots.Construction.ProofsC2.partialCoefficientSum (coeff i) y =
            (((primesUpTo y).filter
              (fun p : ℕ => (p : ZMod (qI i)) = (vI i : ZMod (qI i)))).card : ℝ) := by
        simpa [coeff] using
          (ArtinPrimitiveRoots.Construction.ProofsC2.partialClassCount (qI i) (vI i) y)
      have hrewrite :
          (∑ i ∈ I,
            |ArtinPrimitiveRoots.Construction.ProofsC2.partialCoefficientSum (coeff i) y -
              α i * ArtinPrimitiveRoots.Ext.TypeIIInputs.logarithmicIntegral y|) =
            ∑ i ∈ I,
              |(((primesUpTo y).filter
                  (fun p : ℕ => (p : ZMod (qI i)) = (vI i : ZMod (qI i)))).card : ℝ) -
                ArtinPrimitiveRoots.Ext.TypeIIInputs.logarithmicIntegral y /
                  (Nat.totient (qI i) : ℝ)| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcountTerm]
        dsimp [α]
        ring_nf
      rw [hrewrite]
      calc
        _ ≤ ∑ q ∈ Finset.range (⌊Real.rpow y theta⌋₊ + 1),
            ArtinPrimitiveRoots.Ext.TypeIIInputs.primeProgressionError y q := hsum
        _ ≤ CBV * y * Real.rpow (Real.log y) (-A') := hBVinterval y hy
        _ = E y := rfl
    let arg : ℝ → ℝ := fun t => (cr * t + 1) / x
    have hargcont : Continuous arg := by fun_prop
    have hΨderivcont : Continuous (deriv Ψ) :=
      hΨsmooth.continuous_deriv (by simp)
    have hderivFormula (t : ℝ) :
        deriv f t = deriv Ψ (arg t) * (cr / x) := by
      simpa [f, arg, cr, smoothProgressionFunction] using
        (ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_hasDerivAt
          x c r Ψ hΨsmooth hxpos.ne' t).deriv
    have hderivcont : Continuous (deriv f) := by
      rw [show deriv f = fun t => deriv Ψ (arg t) * (cr / x) from funext hderivFormula]
      exact (hΨderivcont.comp hargcont).mul continuous_const
    have hderivInt : IntegrableOn (deriv f) (Set.Icc lo hi) :=
      hderivcont.continuousOn.integrableOn_compact isCompact_Icc
    have hfDiff : ∀ t ∈ Set.Icc lo hi, DifferentiableAt ℝ f t := by
      intro t ht
      exact (ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_hasDerivAt
        x c r Ψ hΨsmooth hxpos.ne' t).differentiableAt
    have hlo8 : 8 ≤ lo := by
      have hxOne : 1 ≤ x := by linarith [hx2]
      have hpow : Real.rpow x (9 / 100 : ℝ) ≤ Real.rpow x (9 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hxOne
          (by norm_num : (9 / 100 : ℝ) ≤ 9 / 10)
      exact le_trans hxCut (le_trans hpow hloCut)
    have hlogcont : ContinuousOn Real.log (Set.Icc lo hi) := by
      apply Real.continuousOn_log.mono
      intro t ht
      change t ≠ 0
      have ht8 : 8 ≤ t := le_trans hlo8 ht.1
      exact ne_of_gt (by linarith)
    have ht2 (t : ℝ) (ht : t ∈ Set.Icc lo hi) : 2 < t := by
      exact lt_of_lt_of_le (by norm_num) (le_trans hlo8 ht.1)
    have hlogpos (t : ℝ) (ht : t ∈ Set.Icc lo hi) : 0 < Real.log t :=
      Real.log_pos (by linarith [ht2 t ht])
    have hli (t : ℝ) (ht : t ∈ Set.Icc lo hi) :
        HasDerivAt ArtinPrimitiveRoots.Ext.TypeIIInputs.logarithmicIntegral
          (1 / Real.log t) t :=
      ArtinPrimitiveRoots.Construction.ProofsC2.logarithmicIntegral_hasDerivAt
        (ht2 t ht)
    have hliInt : IntervalIntegrable (fun t => 1 / Real.log t) volume lo hi := by
      apply ContinuousOn.intervalIntegrable_of_Icc hlohi
      apply continuousOn_const.div hlogcont
      intro t ht
      exact ne_of_gt (hlogpos t ht)
    have hfcont : Continuous f := by
      change Continuous (Ψ ∘ arg)
      exact hΨsmooth.continuous.comp hargcont
    have hflogInt : IntervalIntegrable (fun t => f t / Real.log t) volume lo hi := by
      apply ContinuousOn.intervalIntegrable_of_Icc hlohi
      apply hfcont.continuousOn.div hlogcont
      intro t ht
      exact ne_of_gt (hlogpos t ht)
    have hPInt : ∀ i ∈ I,
        IntervalIntegrable
          (fun t => deriv f t *
            ArtinPrimitiveRoots.Construction.ProofsC2.partialCoefficientSum (coeff i) t)
          volume lo hi := by
      intro i hiI
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlohi]
      exact integrableOn_mul_sum_Icc (coeff i) hlo0 hderivInt
    have hEcont : ContinuousOn E (Set.Icc lo hi) := by
      have hpcont : ContinuousOn
          (fun t => Real.rpow (Real.log t) (-A')) (Set.Icc lo hi) :=
        hlogcont.rpow_const (fun t ht => Or.inl (ne_of_gt (hlogpos t ht)))
      dsimp [E]
      exact (continuousOn_const.mul continuousOn_id).mul hpcont
    have hEInt : IntervalIntegrable (fun t => |deriv f t| * E t) volume lo hi := by
      apply ContinuousOn.intervalIntegrable_of_Icc hlohi
      exact hderivcont.continuousOn.abs.mul hEcont
    have hargIcc (t : ℝ) (ht : t ∈ Set.Icc lo hi) : arg t ∈ Set.Icc 1 2 := by
      have hta : (x - 1) / cr ≤ t := by simpa [lo] using ht.1
      have htb : t ≤ (2 * x - 1) / cr := by simpa [hi] using ht.2
      constructor
      · change 1 ≤ (cr * t + 1) / x
        apply (le_div_iff₀ hxpos).2
        have h := (div_le_iff₀ hcr).1 hta
        nlinarith
      · change (cr * t + 1) / x ≤ 2
        apply (div_le_iff₀ hxpos).2
        have h := (le_div_iff₀ hcr).1 htb
        nlinarith
    have hderivBound (t : ℝ) (ht : t ∈ Set.Icc lo hi) :
        |deriv f t| ≤ B * (cr / x) := by
      rw [hderivFormula, abs_mul]
      have hΨb := hΨderivBound (arg t) (hargIcc t ht)
      have hcrx : 0 ≤ cr / x := le_of_lt (div_pos hcr hxpos)
      calc
        |deriv Ψ (arg t)| * |cr / x| = |deriv Ψ (arg t)| * (cr / x) := by
          rw [abs_of_nonneg hcrx]
        _ ≤ B * (cr / x) := mul_le_mul_of_nonneg_right hΨb hcrx
    have hderivAbsInt : IntervalIntegrable (fun t => |deriv f t|) volume lo hi :=
      by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlohi]
        exact hderivInt.abs
    have hderivIntegral : (∫ t in lo..hi, |deriv f t|) ≤ B := by
      calc
        _ ≤ ∫ t in lo..hi, B * (cr / x) :=
          intervalIntegral.integral_mono_on hlohi hderivAbsInt
            (intervalIntegrable_const) (fun t ht => hderivBound t ht)
        _ = B := by
          rw [intervalIntegral.integral_const]
          dsimp [lo, hi]
          field_simp [hcr.ne', hxpos.ne']
          ring_nf
    have hΨone : Ψ 1 = 0 := by
      by_contra hn
      have hm := hΨsupp (Function.mem_support.mpr hn)
      exact (not_lt_of_ge le_rfl hm.1)
    have hΨtwo : Ψ 2 = 0 := by
      by_contra hn
      have hm := hΨsupp (Function.mem_support.mpr hn)
      exact (not_lt_of_ge le_rfl hm.2)
    have harglo : arg lo = 1 := by
      dsimp [arg, lo]
      field_simp [hxpos.ne', hcr.ne']
      ring
    have harghi : arg hi = 2 := by
      dsimp [arg, hi]
      field_simp [hxpos.ne', hcr.ne']
      ring
    have harglo' : ((((c * r : ℕ) : ℝ) * lo + 1) / x) = 1 := by
      simpa [arg, cr] using harglo
    have harghi' : ((((c * r : ℕ) : ℝ) * hi + 1) / x) = 2 := by
      simpa [arg, cr] using harghi
    have hfa : f lo = 0 := by
      change Ψ ((((c * r : ℕ) : ℝ) * lo + 1) / x) = 0
      rw [harglo']
      exact hΨone
    have hfb : f hi = 0 := by
      change Ψ ((((c * r : ℕ) : ℝ) * hi + 1) / x) = 0
      rw [harghi']
      exact hΨtwo
    have hRpos : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have htUpper (t : ℝ) (ht : t ∈ Set.Icc lo hi) : t ≤ x / (r : ℝ) := by
      have htb : t ≤ hi := ht.2
      apply (le_div_iff₀ hcr).1 at htb
      have htNonneg : 0 ≤ t := le_trans (by norm_num) (le_trans hlo8 ht.1)
      have hcrR : (2 : ℝ) * (r : ℝ) ≤ cr := by
        dsimp [cr]
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_right hcLower (Nat.cast_nonneg _)
      have hmul : 2 * (r : ℝ) * t ≤ cr * t :=
        mul_le_mul_of_nonneg_right hcrR htNonneg
      have hrt : t * (r : ℝ) ≤ x := by nlinarith [hmul, htb]
      exact (le_div_iff₀ hRpos).2 (by nlinarith [hrt])
    have hlogNegPow (t : ℝ) (ht : t ∈ Set.Icc lo hi) :
        Real.rpow (Real.log t) (-A') ≤
          V * Real.rpow (Real.log x) (-A') := by
      have hbasePos : 0 < (1 / 2 : ℝ) * Real.log x := by positivity
      have hpow : Real.rpow (Real.log t) (-A') ≤
          Real.rpow ((1 / 2 : ℝ) * Real.log x) (-A') :=
        Real.rpow_le_rpow_of_nonpos
          (x := (1 / 2 : ℝ) * Real.log x) (y := Real.log t) (z := -A')
          hbasePos (hlogHalf t ht) (by linarith [hA'])
      calc
        Real.rpow (Real.log t) (-A') ≤
            Real.rpow ((1 / 2 : ℝ) * Real.log x) (-A') := hpow
        _ = V * Real.rpow (Real.log x) (-A') := by
          change ((1 / 2 : ℝ) * Real.log x) ^ (-A') =
            Real.rpow (1 / 2) (-A') * (Real.log x) ^ (-A')
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          dsimp [V]
    have hEbound (t : ℝ) (ht : t ∈ Set.Icc lo hi) :
        E t ≤ CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A') := by
      have hpowNonneg : 0 ≤ Real.rpow (Real.log t) (-A') :=
        Real.rpow_nonneg (le_of_lt (hlogpos t ht)) _
      have hct : CBV * t ≤ CBV * (x / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left (htUpper t ht) hCBV.le
      calc
        E t = CBV * t * Real.rpow (Real.log t) (-A') := rfl
        _ ≤ CBV * (x / (r : ℝ)) * Real.rpow (Real.log t) (-A') :=
          mul_le_mul_of_nonneg_right hct hpowNonneg
        _ ≤ CBV * (x / (r : ℝ)) * (V * Real.rpow (Real.log x) (-A')) :=
          mul_le_mul_of_nonneg_left (hlogNegPow t ht)
            (by positivity)
        _ = CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A') := by ring
    have hfamily := ArtinPrimitiveRoots.Construction.ProofsC2.smoothFamilyError_of_aggregateEndpointControl
      I lo hi hlo0 hlohi coeff α E
      ArtinPrimitiveRoots.Ext.TypeIIInputs.logarithmicIntegral f
      hfDiff hderivInt hli hliInt hflogInt hPInt hEInt hcount hfa hfb
    have hEIntegral :
        (∫ t in lo..hi, |deriv f t| * E t) ≤
        (CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A')) * B := by
      let H : ℝ := CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A')
      have hHnonneg : 0 ≤ H := by dsimp [H]; positivity
      have hConstInt : IntervalIntegrable (fun t => |deriv f t| * H) volume lo hi :=
        hderivAbsInt.mul_const H
      have hmono := intervalIntegral.integral_mono_on hlohi hEInt hConstInt
        (fun t ht => mul_le_mul_of_nonneg_left (hEbound t ht) (abs_nonneg _))
      calc
        _ ≤ ∫ t in lo..hi, |deriv f t| * H := hmono
        _ = H * (∫ t in lo..hi, |deriv f t|) := by
          rw [intervalIntegral.integral_mul_const, mul_comm]
        _ ≤ H * B := mul_le_mul_of_nonneg_left hderivIntegral hHnonneg
        _ = _ := rfl
    have hlogA : Real.rpow (Real.log x) (-A') ≤ Real.rpow (Real.log x) (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlogx (by linarith [hA'])
    have hscaleFinal :
        (CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A')) * B ≤
          C * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
      have hcoef : B * CBV * (x / (r : ℝ)) * V ≤ C * (x / (r : ℝ)) := by
        dsimp [C]
        calc
          B * CBV * (x / (r : ℝ)) * V = (B * CBV * V) * (x / (r : ℝ)) := by ring
          _ ≤ (20 * B * CBV * V) * (x / (r : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hnonneg : 0 ≤ B * CBV * V := by positivity
            nlinarith [mul_nonneg (show 0 ≤ (19 : ℝ) by norm_num) hnonneg]
          _ = (20 * B * CBV * V) * (x / (r : ℝ)) := rfl
      have hpowNonneg : 0 ≤ Real.rpow (Real.log x) (-A) :=
        Real.rpow_nonneg (by linarith [hlogx]) _
      have hlogPrimeNonneg : 0 ≤ Real.rpow (Real.log x) (-A') :=
        Real.rpow_nonneg (by linarith [hlogx]) _
      have hcoefRhsNonneg : 0 ≤ C * (x / (r : ℝ)) := by positivity
      calc
        (CBV * (x / (r : ℝ)) * V * Real.rpow (Real.log x) (-A')) * B =
            (B * CBV * (x / (r : ℝ)) * V) * Real.rpow (Real.log x) (-A') := by ring
        _ ≤ (C * (x / (r : ℝ))) * Real.rpow (Real.log x) (-A) :=
          mul_le_mul hcoef hlogA hlogPrimeNonneg hcoefRhsNonneg
        _ = C * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by ring
    have hmainI :
        (∫ t in lo..hi, f t / Real.log t) = smoothedMainTerm x c r Ψ := by
      simpa [lo, hi, f, cr, Nat.cast_mul] using
        ArtinPrimitiveRoots.Construction.ProofsC2.smoothProgression_integral_eq_main
          x c r Ψ hxpos hcr
    have hTarget (i : {ell // ell ∈ Sgood}) :
        |progressionPrimeSum x M c u Ψ r i.1 -
            localSieveDensity M r i.1 * smoothedMainTerm x c r Ψ /
              (Nat.totient N : ℝ)| =
          |(∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊, f (n : ℝ) * coeff i n) -
              α i * (∫ t in lo..hi, f t / Real.log t)| := by
      have hiGood := (Finset.mem_filter.mp i.2).2
      have hEllM := hiGood.coprime_dvd_right (dvd_mul_right M r)
      have hNdivM : N ∣ M := ⟨c, hMN.symm.trans (Nat.mul_comm c N)⟩
      have hEllN := hEllM.coprime_dvd_right hNdivM
      have hNell : Nat.Coprime N i.1 := hEllN.symm
      have hphiN : 0 < Nat.totient N := Nat.totient_pos.mpr hNpos
      have hphiell : 0 < Nat.totient i.1 :=
        Nat.totient_pos.mpr (hEllPos i.1 (Finset.mem_filter.mp i.2).1)
      have hphi : Nat.totient (qI i) = Nat.totient N * Nat.totient i.1 := by
        simpa [qI] using Nat.totient_mul hNell
      have hlocal : localSieveDensity M r i.1 =
          1 / (Nat.totient i.1 : ℝ) := by
        unfold localSieveDensity
        rw [if_pos hiGood]
      have hDensity :
          localSieveDensity M r i.1 * smoothedMainTerm x c r Ψ /
              (Nat.totient N : ℝ) =
            smoothedMainTerm x c r Ψ / (Nat.totient (qI i) : ℝ) := by
        rw [hlocal, hphi]
        field_simp [hphiN.ne', hphiell.ne']
        rw [Nat.cast_mul]
        ring
      have hAlpha :
          α i * (∫ t in lo..hi, f t / Real.log t) =
            smoothedMainTerm x c r Ψ / (Nat.totient (qI i) : ℝ) := by
        rw [hmainI]
        dsimp [α]
        ring
      rw [hRangeToIoc i, hDensity, hAlpha]
    let G : ℕ → ℝ := fun ell =>
      |progressionPrimeSum x M c u Ψ r ell -
        localSieveDensity M r ell * smoothedMainTerm x c r Ψ /
          (Nat.totient N : ℝ)|
    let Fam : {ell // ell ∈ Sgood} → ℝ := fun i =>
      |(∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊, f (n : ℝ) * coeff i n) -
        α i * (∫ t in lo..hi, f t / Real.log t)|
    have hGoodSum : (∑ ell ∈ Sgood, G ell) = ∑ i ∈ I, Fam i := by
      calc
        (∑ ell ∈ Sgood, G ell) = ∑ i ∈ I, G i.1 := by
          symm
          simpa [I] using (Finset.sum_attach Sgood G)
        _ = ∑ i ∈ I, Fam i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hTarget i
    have hAll : (∑ ell ∈ S, G ell) = ∑ i ∈ I, Fam i := by
      calc
        (∑ ell ∈ S, G ell) = ∑ ell ∈ Sgood, G ell := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro ell hellS hellNot
          have hbad : ¬ Nat.Coprime ell (M * r) := by
            intro hcop
            exact hellNot (Finset.mem_filter.mpr ⟨hellS, hcop⟩)
          simp [G, localSieveDensity, hbad,
            ArtinPrimitiveRoots.Construction.ProofsC2.progressionPrimeSum_vanish_of_not_coprime
              x M c u Ψ r ell hu hbad]
        _ = ∑ i ∈ I, Fam i := hGoodSum
    have hTargetBound :
        (∑ ell ∈ S,
          |progressionPrimeSum x M c u Ψ r ell -
            localSieveDensity M r ell * smoothedMainTerm x c r Ψ /
              (Nat.totient N : ℝ)|) ≤
          C * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
      rw [hAll]
      exact le_trans hfamily (le_trans hEIntegral hscaleFinal)
    simpa [S, D, beta] using hTargetBound

set_option maxHeartbeats 200000

/-- `con:distribution`, 12-construction.tex:239-386; this records exactly the two downstream
conclusions, the weighted sieve-error sum and the two-sided total-mass comparison. -/
theorem con_distribution (M : ℕ) (Ψ : ℝ → ℝ)
    (hM : 0 < M) (hΨ : IsTestFunction Ψ) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ c : ℕ, (c = 2 ∨ c = 4) → c ∣ M → ∀ u : ℤ,
        Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
        Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
      ∀ K : ℕ, ∀ a : Fin K → ℝ, ValidBands K a →
        ∀ ε κ : ℝ, 0 < ε → ε < κ → κ < 1 / 100 →
          ∃ x₁ : ℝ, 2 ≤ x₁ ∧
            (∀ A : ℝ, 0 < A →
              ∃ C_A x_A : ℝ, 0 < C_A ∧ x₁ ≤ x_A ∧
                ∀ x : ℝ, x_A ≤ x →
                let J₀ := groupHarmonicMass x K a
                let D := Real.rpow x (1 / 2 - κ / 2)
                let errors r ℓ := progressionPrimeSum x M c u Ψ r ℓ -
                  localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1
                (∑ r ∈ (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
                      (fun r => IsGroupInteger x K a r),
                    ∑ ℓ ∈ oddSquarefreeUpTo D,
                      markedWeight x K a (1 / 2 : ℝ) r * |errors r ℓ|) ≤
                  C_A * x * J₀ * Real.rpow (Real.log x) (-A)) ∧
            ∀ x : ℝ, x₁ ≤ x →
                let J₀ := groupHarmonicMass x K a
                c₀ * x * J₀ / Real.log x ≤ conTotalMass x M c u K a Ψ ∧
                  conTotalMass x M c u K a Ψ ≤ C₀ * x * J₀ / Real.log x := by
  rcases hΨ with ⟨hΨsmooth, hΨsupp, hΨnonneg, hΨle, hΨint⟩
  have hTest : IsTestFunction Ψ := ⟨hΨsmooth, hΨsupp, hΨnonneg, hΨle, hΨint⟩
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro c hc24 hcM u hu hcu hcu' K a ha ε κ hε hεκ hκ
  have hcPos : 0 < c := by rcases hc24 with h | h <;> omega
  obtain ⟨Ch, xH, hCh, hxH, hHarm⟩ :=
    con_harmonic M c u Ψ K a hM hcPos ha hTest
  obtain ⟨xMarks, hxMarks⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_markedPrimes_gt (max M 2) K a ha
  obtain ⟨xExp, hxExp⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_real_rpow_ge
      (δ := (1 : ℝ)) (B := Real.exp 1) (by norm_num)
  let x₁ : ℝ := max 2 (max xH (max xMarks xExp))
  have hx₁ : 2 ≤ x₁ := by dsimp [x₁]; exact le_max_left _ _
  refine ⟨x₁, hx₁, ?_, ?_⟩
  · intro A hA
    let A' : ℝ := A + 4
    have hA' : 0 < A' := by dsimp [A']; linarith
    obtain ⟨Cbv, xBV, hCbv, hxBV, hBV⟩ :=
      bv_smoothed M c u K a Ψ ε κ hM hcPos hcM hc24 hu hcu hcu' hε hεκ hκ ha hTest A' hA'
    let x_A : ℝ := max x₁ xBV
    let C_A : ℝ := 5 * Cbv
    refine ⟨C_A, x_A, by dsimp [C_A]; positivity, ?_, ?_⟩
    · dsimp [x_A]
      exact le_max_left _ _
    · intro x hxA
      let J₀ : ℝ := groupHarmonicMass x K a
      let D : ℝ := Real.rpow x (1 / 2 - κ / 2)
      let R : Finset ℕ :=
        (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter (fun r => IsGroupInteger x K a r)
      let Lset : Finset ℕ := oddSquarefreeUpTo D
      let main : ℝ := smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ)
      have hxparts : x₁ ≤ x ∧ xBV ≤ x := by
        dsimp [x_A] at hxA
        exact (max_le_iff.mp hxA)
      rcases hxparts with ⟨hx₁x, hxBVx⟩
      have hxHle : xH ≤ x := le_trans (le_max_left xH (max xMarks xExp))
        (le_trans (le_max_right 2 (max xH (max xMarks xExp))) hx₁x)
      have hJbounds := hHarm x (le_trans (le_max_left xH (max xMarks xExp)) hx₁x)
      have hJlowerX : 1 ≤ J₀ := by simpa [J₀] using hJbounds.2.1
      have hxExpX : Real.exp 1 ≤ x := by
        have hX := hxExp x (le_trans (le_max_right xMarks xExp)
          (le_trans (le_max_right xH (max xMarks xExp)) hx₁x))
        simpa only [Real.rpow_one] using hX
      have hlogx : 1 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxExpX
        simpa using h
      have hxpos : 0 < x := by linarith [hx₁x]
      have hxge1 : 1 ≤ x := le_trans (by norm_num) hx₁x
      have hDpos : 0 < D := by dsimp [D]; positivity
      have hDone : 1 ≤ D := by
        have hb : 0 < 1 / 2 - κ / 2 := by dsimp; nlinarith [hκ]
        have hle : Real.rpow (1 : ℝ) (1 / 2 - κ / 2) ≤ D := by
          dsimp [D]
          exact Real.rpow_le_rpow (by norm_num) hxge1 hb.le
        simpa using hle
      have hDleX : D ≤ x := by
        have hb : 1 / 2 - κ / 2 ≤ (1 : ℝ) := by nlinarith [hκ]
        dsimp [D]
        exact Real.rpow_le_rpow_of_exponent_le hxge1 hb
      have hlogD : Real.log D ≤ Real.log x :=
        Real.log_le_log hDpos hDleX
      have hharmonic : harmonic ⌊D⌋₊ ≤ 2 * Real.log x := by
        have h := harmonic_floor_le_one_add_log D hDone
        have hupper : 1 + Real.log D ≤ 2 * Real.log x := by linarith [hlogD, hlogx]
        exact le_trans h hupper
      have hDensitySum :
          (∑ ell ∈ Lset, localSieveDensity M r ell) ≤
            4 * Real.rpow (Real.log x) 4 := by
        have h := ArtinPrimitiveRoots.Construction.ProofsC2.localSieveDensity_sum_le M r D
        have hpow : Real.rpow (Real.log x) 2 ≤ Real.rpow (Real.log x) 4 :=
          Real.rpow_le_rpow_of_exponent_le hlogx (by norm_num)
        have hharmonicSq : (harmonic ⌊D⌋₊ : ℝ) ^ 2 ≤
            (2 * Real.log x) ^ 2 := by nlinarith [hharmonic]
        calc
          _ ≤ (harmonic ⌊D⌋₊ : ℝ) ^ 2 := h
          _ ≤ 4 * Real.rpow (Real.log x) 2 := by
            have hsq := hharmonicSq
            have hlogNonneg : 0 ≤ Real.log x := by linarith [hlogx]
            have hpow2 : Real.rpow (Real.log x) 2 = (Real.log x) ^ 2 := by simp
            rw [hpow2]
            nlinarith [hsq]
          _ ≤ 4 * Real.rpow (Real.log x) 4 := by gcongr
      have hRpos (r : ℕ) (hr : r ∈ R) : 0 < r := by
        have hrGroup := (Finset.mem_filter.mp hr).2
        have hmark : ∀ p ∈ markedPrimes x K a, (2 : ℝ) < (p : ℝ) := by
          intro p hp
          have hxM : xMarks ≤ x := by
            have := le_trans (le_max_right xMarks xExp)
              (le_trans (le_max_right xH (max xMarks xExp)) hx₁x)
            exact this
          have hh := hxMarks x hxM p hp
          exact lt_trans (by exact_mod_cast (Nat.le_max_right M 2)) hh
        exact ArtinPrimitiveRoots.Construction.ProofsC2.groupInteger_pos_of_marks_gt_two
          x K r a hmark hrGroup
      have hSumWeight :
          (∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ)) ≤ J₀ := by
        let Hfun : ℕ → ℝ := fun q => if IsGroupInteger x K a q then
          markedWeight x K a (1 / 2 : ℝ) q / (q : ℝ) else 0
        have hWnonneg (q : ℕ) : 0 ≤ markedWeight x K a (1 / 2 : ℝ) q := by
          unfold markedWeight
          split_ifs
          · apply mul_nonneg
            · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _
            · apply Finset.prod_nonneg
              intro i hi
              apply div_nonneg (Nat.cast_nonneg _)
              unfold bandMass
              apply Finset.sum_nonneg
              intro p hp
              have hprime := (Finset.mem_filter.mp hp).2.1
              exact div_nonneg (by norm_num)
                (by exact_mod_cast hprime.pos.le)
          · simp
        have hHnonneg (q : ℕ) : 0 ≤ Hfun q := by
          dsimp [Hfun]
          split_ifs with hq
          · exact div_nonneg (hWnonneg q) (Nat.cast_nonneg _)
          · norm_num
        have hJne : (∑' q : ℕ, Hfun q) ≠ 0 := by
          have hEq : (∑' q : ℕ, Hfun q) = J₀ := by
            simp [Hfun, J₀, groupHarmonicMass]
          rw [hEq]
          linarith [hJlowerX]
        have hSummable : Summable Hfun := by
          by_contra hns
          apply hJne
          simpa [tsum_eq_zero_of_not_summable hns]
        have hsum := hSummable.sum_le_tsum R (fun q hq => hHnonneg q)
        calc
          _ = ∑ q ∈ R, Hfun q := by
            apply Finset.sum_congr rfl
            intro q hq
            simp [Hfun, R, hq]
          _ ≤ ∑' q : ℕ, Hfun q := hsum
          _ = J₀ := by simp [Hfun, J₀, groupHarmonicMass]
      sorry
  · intro x hx₁
    sorry

/-- `co:sieve-products`, 12-construction.tex:388-412. -/
theorem sieve_products (M : ℕ) (hM : 0 < M) :
    0 < singularProduct M ∧
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |progressionSieveProduct M y - singularProduct M * roughSieveProduct y| ≤
          ε * singularProduct M * roughSieveProduct y) ∧
    ∀ K : ℕ, ∀ a : Fin K → ℝ, ValidBands K a →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ r : ℕ, IsGroupInteger x K a r →
            (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) →
              (∑ p ∈ (primesUpTo (Real.rpow x (1 / 5 : ℝ))).filter
                    (fun p => p ∣ r), 1 / (p : ℝ)) ≤
                  (11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) *
                    Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) ∧
              (∀ y : ℝ, 2 ≤ y →
                |progressionSieveProductFor M r y - progressionSieveProduct M y| ≤
                  Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) *
                    progressionSieveProduct M y) := by
  sorry

/-- `co:initial-lower`, 12-construction.tex:414-450. The `o(1)` is expressed with an explicit
arbitrary error after the fixed parameters. -/
theorem initial_lower :
    ∃ C_s b₂ : ℝ, 0 < C_s ∧ 0 < b₂ ∧
      ∀ M c : ℕ, ∀ u : ℤ, ∀ K : ℕ, ∀ a : Fin K → ℝ,
        ∀ Ψ : ℝ → ℝ, IsTestFunction Ψ →
        ∀ κ ε : ℝ, 0 < κ → κ < 1 / 100 → 0 < ε → ε < κ →
        0 < M → (c = 2 ∨ c = 4) → c ∣ M →
        Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
        Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 → ValidBands K a →
        ∀ b : ℝ, 0 < b → b < b₂ → b < 1 / 2 - κ →
        ∀ η : ℝ, 0 < η →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧
            ∀ x : ℝ, x₀ ≤ x →
              (Real.rpow x b ≤ Real.rpow x (1 / 2 - κ / 2)) →
                roughConstructionMass x M c u K a Ψ (Real.rpow x b) ≥
                  (singularProduct M * conTotalMass x M c u K a Ψ / Real.log x) *
                    (Real.exp (-Real.eulerMascheroniConstant) / b *
                      (1 - C_s * Real.exp (-(1 / 20 : ℝ) / b)) - η) := by
  sorry

/-- `con:bin-mass`, 12-construction.tex:452-503. -/
theorem con_bin_mass (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (b κ ε : ℝ) (hM : 0 < M)
    (hc : c = 2 ∨ c = 4) (hcM : c ∣ M)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 100)
    (hε : 0 < ε) (hεκ : ε < κ) (ha : ValidBands K a)
    (hΨ : IsTestFunction Ψ) (hu : Int.gcd u M = 1)
    (hcu : (c : ℤ) ∣ u - 1)
    (hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1) :
    ∀ γ γ' : ℝ, b ≤ γ → γ < γ' → γ' ≤ 1 / 2 - κ →
      ∀ η : ℝ, 0 < η →
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            |primeDivisorBinSum x M c u K a Ψ γ γ' -
              (singularProduct M * conTotalMass x M c u K a Ψ *
                roughSieveProduct (roughCutoff x) * Real.log (γ' / γ))| ≤
              η * singularProduct M * conTotalMass x M c u K a Ψ *
                roughSieveProduct (roughCutoff x) := by
  sorry

/-- `co:bin-cost`, 12-construction.tex:505-561. -/
theorem bin_cost (M c : ℕ) (u : ℤ) (κ b : ℝ)
    (hM : 0 < M) (hc : 0 < c) (hcM : c ∣ M)
    (hκ : 0 < κ) (hκsmall : κ < 1 / 100) (hb : 0 < b) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ Ψ : ℝ → ℝ, IsTestFunction Ψ →
        ∀ γ γ' : ℝ, b ≤ γ → γ < γ' → γ' ≤ 1 / 2 - κ →
        ∀ η : ℝ, 0 < η →
          ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
            ∀ x : ℝ, x₀ ≤ x →
              let T :=
                ∑ q ∈ ((primesUpTo (Real.rpow x γ') : Finset ℕ).filter
                    (fun (q : ℕ) => Real.rpow x γ < (q : ℝ))),
                  ∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1),
                    if roughAbove m (Real.rpow x γ) then
                      conWeight x M c u K a Ψ (Nat.mul m q) else 0
              T ≤ (singularProduct M * conTotalMass x M c u K a Ψ / Real.log x) *
                (sSup ((fun t : ℝ => roughDensity γ (1 - t)) '' Set.Icc γ γ') *
                  Real.log (γ' / γ) + η) := by
  sorry

/-- `co:density-partition`, 12-construction.tex:563-592. -/
theorem density_partition :
    ∃ C_s C_d b₂ : ℝ, 0 < C_s ∧ 0 < C_d ∧ 0 < b₂ ∧
      ∀ M c : ℕ, ∀ u : ℤ, ∀ κ : ℝ,
        0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
        Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
        Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
        0 < κ → κ < 1 / 100 →
      ∀ b : ℝ, 0 < b → b < b₂ → b < 1 / 2 - κ →
        ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
          ∀ Ψ : ℝ → ℝ, IsTestFunction Ψ →
            ∃ J : ℕ, ∃ γ : Fin (J + 1) → ℝ,
              γ 0 = b ∧ γ (Fin.last J) = 1 / 2 - κ ∧
              (∀ i j, i.val < j.val → γ i < γ j) ∧
              (∑ j : Fin J,
                sSup ((fun t : ℝ => roughDensity (γ j.castSucc)
                  (1 - t)) '' Set.Icc (γ j.castSucc) (γ j.succ)) *
                  Real.log (γ j.succ / γ j.castSucc)) ≤
                ∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t + 1 / 10 ∧
              ∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t ≤
                roughDensity b 1 - 1 ∧
              ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
                ∀ x : ℝ, x₀ ≤ x →
                  roughConstructionMass x M c u K a Ψ (Real.rpow x (1 / 2 - κ)) ≥
                    (singularProduct M * conTotalMass x M c u K a Ψ / Real.log x) *
                      (9 / 10 - Real.exp (-Real.eulerMascheroniConstant) / b *
                        (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
                          C_d * Real.exp (-(1 / 20 : ℝ) / b)) - η) := by
  sorry

/-- `co:balanced-boxes`, 12-construction.tex:597-616. -/
theorem balanced_boxes :
    ∃ Cdyad : ℝ, 0 < Cdyad ∧
      ∀ M c : ℕ, ∀ u : ℤ, ∀ K : ℕ, ∀ a : Fin K → ℝ,
        ∀ Ψ : ℝ → ℝ, IsTestFunction Ψ → ∀ κ : ℝ,
          0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
          (Int.gcd u M = 1) → (c : ℤ) ∣ u - 1 →
          Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
          ValidBands K a → 0 < κ → κ < 1 / 100 →
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∃ N : ℕ, (N : ℝ) ≤ Cdyad * (κ * Real.log x + 1) ∧
          ∃ H₁ H₂ : Fin N → ℝ,
            (∀ i, x / 4 ≤ H₁ i * H₂ i ∧ H₁ i * H₂ i ≤ 2 * x ∧
              Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₁ i ∧
                H₁ i ≤ 2 * Real.rpow x (54 / 100 : ℝ) ∧
              Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₂ i ∧
                H₂ i ≤ 2 * Real.rpow x (54 / 100 : ℝ)) ∧
            (∀ d, 0 < conWeight x M c u K a Ψ d →
              roughAbove d (Real.rpow x (1 / 2 - κ)) → ¬ d.Prime →
                ∃ i m n, m ∈ dyadicIntegers (H₁ i) ∧ n ∈ dyadicIntegers (H₂ i) ∧
                  m.Prime ∧ n.Prime ∧ d = m * n) := by
  sorry

/-- `con:rough-pairs`, 12-construction.tex:617-734. Its leading constant is uniform in the marked
data and sieve parameters; only the progression and smoothing data affect it. -/
theorem con_rough_pairs (M : ℕ) (Ψ : ℝ → ℝ) (hM : 0 < M)
    (hΨ : IsTestFunction Ψ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ c : ℕ, (c = 2 ∨ c = 4) → ∀ u : ℤ,
        ∀ K : ℕ, ∀ a : Fin K → ℝ, ValidBands K a →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧
            ∀ x : ℝ, x₀ ≤ x →
              ∀ H₁ H₂ : ℝ,
                x / 4 ≤ H₁ * H₂ → H₁ * H₂ ≤ 2 * x →
                Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₁ →
                H₁ ≤ 2 * Real.rpow x (54 / 100 : ℝ) →
                Real.rpow x (46 / 100 : ℝ) / 2 ≤ H₂ →
                H₂ ≤ 2 * Real.rpow x (54 / 100 : ℝ) →
                  roughPairBoxSum x M c u K a Ψ H₁ H₂ ≤
                    C₁ * conTotalMass x M c u K a Ψ *
                      roughSieveProduct (roughCutoff x) ^ 2 := by
  sorry

/-- `co:balanced-cost`, 12-construction.tex:736-775. -/
theorem balanced_cost (M : ℕ) (Ψ : ℝ → ℝ) (C₁ Cdyad : ℝ)
    (hM : 0 < M) (hΨ : IsTestFunction Ψ) (hC₁ : 0 < C₁) (hCdyad : 0 < Cdyad) :
    ∀ c : ℕ, (c = 2 ∨ c = 4) → c ∣ M → ∀ u : ℤ,
      ∀ κ b : ℝ, 0 < κ → κ < 1 / 100 → 0 < b →
        Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
        Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
          ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
            let C₂ := (46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad
            ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
              ∀ x : ℝ, x₀ ≤ x →
                (∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
                  if roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime then
                    conWeight x M c u K a Ψ d else 0) ≤
                  C₂ * (κ + 1 / Real.log x) * conTotalMass x M c u K a Ψ /
                    Real.log x + η * conTotalMass x M c u K a Ψ / Real.log x := by
  sorry

/-- `co:completion`, 12-construction.tex:777-818. This is the frozen conclusion of
`ArtinPrimitiveRoots.prop_controlled`, so the target file uses this node as glue without changing
the proposition. -/
theorem co_completion (M : ℕ) (hM0 : 0 < M) (hM : 8 ∣ M) (c : ℕ)
    (hc : c = 2 ∨ c = 4) (u : ℤ) (hu : Int.gcd u M = 1)
    (hcu : (c : ℤ) ∣ u - 1)
    (hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      C * x / Real.log x ^ 2 ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧
            (p : ℤ) ≡ u [ZMOD M] ∧
            ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧
              Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧ 0 < r ∧
              ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r →
                Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) < (ℓ : ℝ) ∧
                  (ℓ : ℝ) < Real.exp (Real.rpow (Real.log x) (3 / 10 : ℝ))} :
            Set ℕ).ncard : ℝ) := by
  sorry

end ArtinPrimitiveRoots.Construction
