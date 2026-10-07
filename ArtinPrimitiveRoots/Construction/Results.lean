import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c1.SieveProductHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c1.HarmonicHelpers
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.RoughDensity

/-! Statements for the prime construction in `12-construction.tex`. -/

namespace ArtinPrimitiveRoots.Construction

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.Rough

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
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Xmass, hXmass, hmass⟩ := bandMass_lower_all ha
  let Xscale := Real.exp ((4 : ℝ) ^ 10)
  let x₀ := max Xmass Xscale
  let B := (4 / Real.log 2) ^ K
  have hXscale : 2 ≤ Xscale := by
    have h2 : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    exact h2.trans (Real.exp_le_exp.mpr (by norm_num))
  have hx₀ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_of_le_right hXscale
  have hB : 0 < B := by dsimp [B]; positivity
  have hcne : c ≠ 0 := by rcases hc with h | h <;> omega
  refine ⟨B, x₀, hB, hx₀, ?_⟩
  intro x hx
  have hXm : Xmass ≤ x := le_trans (le_max_left _ _) hx
  have hXs : Xscale ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hXs
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hXs
    simpa [Xscale, Real.log_exp] using hlog
  have hmassx : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass x (a i) :=
    hmass x hXm
  have hinv : ∀ h p, p ∈ markedPrimes x K a → p.Prime →
      conFactor x c K a (p * h) = conFactor x c K a h := by
    intro h p hp hprime
    exact conFactor_mul_marked hcne hp hprime
  have hweightBounds : ∀ d, 0 ≤ conWeight x M c u K a Ψ d ∧
      conWeight x M c u K a Ψ d ≤ B := by
    intro d
    by_cases hdcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M]
    · have hw : 0 ≤ markedWeight x K a (1 / 2 : ℝ) (d - 1) ∧
          markedWeight x K a (1 / 2 : ℝ) (d - 1) ≤ (4 / Real.log 2) ^ K :=
        markedWeight_nonneg_le (x := x) (K := K) (a := a) (h := d - 1) hmassx
      have hFnonneg : 0 ≤ conFactor x c K a (d - 1) := by
        unfold conFactor
        split_ifs <;> norm_num
      have hFle : conFactor x c K a (d - 1) ≤ 1 := by
        unfold conFactor
        split_ifs <;> norm_num
      rw [conWeight, if_pos hdcond]
      constructor
      · exact mul_nonneg (mul_nonneg (hΨ₀ _) hFnonneg) hw.1
      · calc
          Ψ ((d : ℝ) / x) * conFactor x c K a (d - 1) *
              markedWeight x K a (1 / 2 : ℝ) (d - 1) ≤ 1 * 1 * B := by
                gcongr
                · exact hw.1
                · exact hΨ₁ _
                · exact hw.2
          _ = B := by ring
    · simp only [conWeight, if_neg hdcond]
      exact ⟨le_rfl, hB.le⟩
  constructor
  · exact hinv
  · refine ⟨?_, hweightBounds⟩
    intro d hd
    have hcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] := by
      by_contra hn
      simp [conWeight, hn] at hd
    have hΨnz : Ψ ((d : ℝ) / x) ≠ 0 := by
      intro hzero
      apply hd
      simp [conWeight, hcond, hzero]
    have hFnz : conFactor x c K a (d - 1) ≠ 0 := by
      intro hzero
      apply hd
      simp [conWeight, hcond, hzero]
    have hWnz : markedWeight x K a (1 / 2 : ℝ) (d - 1) ≠ 0 := by
      intro hzero
      apply hd
      unfold conWeight
      rw [if_pos hcond, hzero]
      simp
    have hargmem : (d : ℝ) / x ∈ Function.support Ψ := by
      simpa [Function.support] using hΨnz
    have harg : (d : ℝ) / x ∈ Set.Ioo 1 2 := hsupp hargmem
    have hdlo : x < (d : ℝ) := by
      have h := (lt_div_iff₀ hxpos).mp harg.1
      simpa using h
    have hdhi : (d : ℝ) < 2 * x := (div_lt_iff₀ hxpos).mp harg.2
    obtain ⟨Q, hQ, hQlarge, hrep⟩ :
        ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
          d - 1 = c * markedPart x K a (d - 1) * Q := by
      by_cases hpred : ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
          d - 1 = c * markedPart x K a (d - 1) * Q
      · exact hpred
      · have htrue : ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
            d - 1 = c * markedPart x K a (d - 1) * Q := by
          simpa [conFactor] using hFnz
        exact False.elim (hpred htrue)
    let r := markedPart x K a (d - 1)
    have hrGroup : IsGroupInteger x K a r := by
      intro p hp hdiv
      exact prime_dvd_markedPart_mem hp (by simpa [r] using hdiv)
    have hdivCo : ∀ p, p ∈ markedPrimes x K a → p.Prime →
        (p ∣ d - 1 ↔ p ∣ r) := by
      intro p hpmem hp
      have hscale := markedPrime_scale_bounds hxpos hL ha hpmem
      have hpgt : 4 < p := by exact_mod_cast hscale.1
      have hpnotc : ¬ p ∣ c := by
        intro hpc
        rcases hc with hc2 | hc4
        · have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (by simpa [hc2] using hpc)
          omega
        · have hpc4 : p ∣ 4 := by simpa [hc4] using hpc
          have hpcPow : p ∣ (2 : ℕ) ^ 2 := by
            rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
            exact hpc4
          have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpcPow
          have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
          omega
      have hpQ : p < Q := by exact_mod_cast lt_trans hscale.2 hQlarge
      have hpnotQ : ¬ p ∣ Q := by
        intro hpq
        have hpeq : p = Q := (Nat.prime_dvd_prime_iff_eq hp hQ).mp hpq
        omega
      rw [hrep]
      constructor
      · intro hpdiv
        rcases hp.dvd_mul.mp hpdiv with hcr | hq
        · rcases hp.dvd_mul.mp hcr with hc' | hr
          · exact False.elim (hpnotc hc')
          · exact hr
        · exact False.elim (hpnotQ hq)
      · intro hr
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr c) Q
    have hWeq : markedWeight x K a (1 / 2 : ℝ) (d - 1) =
        markedWeight x K a (1 / 2 : ℝ) r :=
      markedWeight_eq_of_prime_dvd_iff hdivCo
    have hcR : (2 : ℝ) ≤ (c : ℝ) := by
      rcases hc with h | h <;> subst c <;> norm_num
    have hrnonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hfactorLower : 2 * (r : ℝ) * Real.rpow x (9 / 10 : ℝ) ≤
        (c : ℝ) * (r : ℝ) * (Q : ℝ) := by
      have hpowpos : 0 ≤ Real.rpow x (9 / 10 : ℝ) :=
        (Real.rpow_pos_of_pos hxpos _).le
      have hcrpos : 0 ≤ (c : ℝ) * (r : ℝ) := mul_nonneg (Nat.cast_nonneg c) hrnonneg
      calc
        2 * (r : ℝ) * Real.rpow x (9 / 10 : ℝ) ≤
            (c : ℝ) * (r : ℝ) * Real.rpow x (9 / 10 : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcR hrnonneg) hpowpos
        _ ≤ (c : ℝ) * (r : ℝ) * (Q : ℝ) :=
              mul_le_mul_of_nonneg_left hQlarge.le hcrpos
    have hfactorEq : (c : ℝ) * (r : ℝ) * (Q : ℝ) = (d : ℝ) - 1 := by
      have hdpos : 1 ≤ d := by omega
      have hcastSub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hdpos]
        simp
      have hcastRep : ((d - 1 : ℕ) : ℝ) = (c : ℝ) * (r : ℝ) * (Q : ℝ) := by
        exact_mod_cast hrep
      linarith [hcastSub, hcastRep]
    have hfactorUpper : (c : ℝ) * (r : ℝ) * (Q : ℝ) < 2 * x := by
      rw [hfactorEq]
      linarith
    have hrCore : (r : ℝ) * Real.rpow x (9 / 10 : ℝ) < x := by
      have := lt_of_le_of_lt hfactorLower hfactorUpper
      nlinarith
    have hpoweq : Real.rpow x (1 / 10 : ℝ) * Real.rpow x (9 / 10 : ℝ) = x := by
      calc
        _ = Real.rpow x ((1 / 10 : ℝ) + 9 / 10) :=
          (Real.rpow_add (x := x) hxpos (1 / 10 : ℝ) (9 / 10 : ℝ)).symm
        _ = Real.rpow x 1 := by congr 1 <;> norm_num
        _ = x := by simp [Real.rpow_one]
    have hrbound₁ : (r : ℝ) ≤ Real.rpow x (1 / 10 : ℝ) := by
      have hpos : 0 < Real.rpow x (9 / 10 : ℝ) := Real.rpow_pos_of_pos hxpos _
      have hlt : (r : ℝ) < x / Real.rpow x (9 / 10 : ℝ) :=
        (lt_div_iff₀ hpos).2 (by simpa [mul_comm] using hrCore)
      have hdivPow : x / Real.rpow x (9 / 10 : ℝ) = Real.rpow x (1 / 10 : ℝ) := by
        field_simp [ne_of_gt hpos]
        simpa [mul_comm] using hpoweq.symm
      rw [← hdivPow]
      exact hlt.le
    have hxone : 1 ≤ x := by linarith [hXs, hXscale]
    have hrbound : (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) :=
      hrbound₁.trans (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num))
    exact ⟨hdlo, hdhi, r, Q, by simpa [r] using hrep, hQ, hQlarge,
      hrGroup, hrbound, hWeq⟩

/-- `con:type-ii`, 12-construction.tex:92-159. Here `R_γ` and `B_γ` are the rough indicator and
the Buchstab proxy, and the weight is the actual §12 weight. The threshold for `K` depends on the
Type II scale parameter only; the estimate is uniform in dyads, intervals, and coefficients.
Correction 7 from review lane `rev-b` adds the interval and ordered scale conditions. -/
theorem con_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M c : ℕ, ∀ u : ℤ,
      ∀ a : Fin K → ℝ, ValidBands K a →
      0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
      Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
      Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
      ∀ Ψ : ℝ → ℝ, (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) →
        Function.support Ψ ⊆ Set.Ioo 1 2 →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → 0 < ∫ y in (1 : ℝ)..2, Ψ y →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
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

set_option maxHeartbeats 1000000 in
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
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Xlower, hXlower, hmassLower⟩ := bandMass_lower_all ha
  obtain ⟨Xupper, hXupper, hmassUpper⟩ := bandMass_upper_all ha
  obtain ⟨Xdisj, hXdisj⟩ := harmonic_primeBands_disjoint_large K a ha
  let Xscale := Real.exp ((100 : ℝ) ^ 10)
  let x₀ := max Xscale (max Xlower (max Xupper Xdisj))
  let B := (4 / Real.log 2) ^ K
  let Cmass := B * Real.exp (4 * (K : ℝ) * Real.log 2)
  let C := max 3 Cmass
  have hx₀4 : 4 ≤ x₀ := by
    have hxscale : 4 ≤ Xscale := by
      have h4 : 4 ≤ Real.exp (4 : ℝ) := by
        have hh := Real.add_one_le_exp (4 : ℝ)
        norm_num at hh ⊢
        linarith
      dsimp [Xscale]
      exact h4.trans (Real.exp_le_exp.mpr (by norm_num))
    exact le_trans hxscale (le_max_left _ _)
  have hx₀2 : 2 ≤ x₀ := by linarith
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, x₀, hC, hx₀2, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith [hx₀2, hx]
  have hx4 : 4 ≤ x := hx₀4.trans hx
  have hxscale : Xscale ≤ x := le_trans (le_max_left _ _) hx
  have hxlower0 : Xlower ≤ x₀ :=
    (le_max_left Xlower (max Xupper Xdisj)).trans (le_max_right Xscale _)
  have hxupper0 : Xupper ≤ x₀ :=
    (le_max_left Xupper Xdisj).trans <|
      (le_max_right Xlower _).trans (le_max_right Xscale _)
  have hxdisj0 : Xdisj ≤ x₀ :=
    (le_max_right Xupper Xdisj).trans <|
      (le_max_right Xlower _).trans (le_max_right Xscale _)
  have hxlower : Xlower ≤ x := hxlower0.trans hx
  have hxupper : Xupper ≤ x := hxupper0.trans hx
  have hxdisj : Xdisj ≤ x := hxdisj0.trans hx
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog' := Real.log_le_log (Real.exp_pos _) hxscale
    have hLbig : (100 : ℝ) ^ 10 ≤ Real.log x := by
      simpa [Xscale, Real.log_exp] using hlog'
    have hsmall : (4 : ℝ) ^ 10 ≤ (100 : ℝ) ^ 10 := by norm_num
    exact hsmall.trans hLbig
  have hmassxLower : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass x (a i) :=
    hmassLower x hxlower
  have hmassxUpper : ∀ i : Fin K, bandMass x (a i) ≤ 2 * Real.log 2 :=
    hmassUpper x hxupper
  have hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand x (a i)) (primeBand x (a j)) := hXdisj x hxdisj
  let S := markedPrimes x K a
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact prime_of_mem_markedPrimes hp
  have hfilterPrime : S.filter Nat.Prime = S := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hp
      exact ⟨hp, hSprime p hp⟩
  have hpairwise : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
      (fun i => primeBand x (a i)) := by
    intro i hi j hj hij
    exact hBands i j hij
  have hsumP : (∑ p ∈ S, 1 / (p : ℝ)) =
      ∑ i : Fin K, bandMass x (a i) := by
    rw [show S = Finset.univ.biUnion (fun i => primeBand x (a i)) by rfl]
    rw [Finset.sum_biUnion hpairwise]
    simp [bandMass]
  have hsumP_upper : (∑ p ∈ S, 1 / (p : ℝ)) ≤
      (K : ℝ) * (2 * Real.log 2) := by
    rw [hsumP]
    calc
      (∑ i : Fin K, bandMass x (a i)) ≤
          ∑ i : Fin K, 2 * Real.log 2 :=
            Finset.sum_le_sum fun i hi => hmassxUpper i
      _ = (K : ℝ) * (2 * Real.log 2) := by simp
  have hfactoredPrimes : ∀ p, p ∈ S → p.Prime := hSprime
  have hfact1 := hasSum_rpowSeries_factoredNumbers
      (s := S) (t := 1) (by norm_num) hfactoredPrimes
  have hterm1 (n : Nat.factoredNumbers S) :
      rpowSeriesTerm 1 n = 1 / (n : ℝ) := by
    have hn : (n : ℕ) ≠ 0 := n.property.1
    simp [rpowSeriesTerm, hn, Real.rpow_neg_one]
  have hrecipSum :
      (∑' n : Nat.factoredNumbers S, 1 / (n : ℝ)) =
        ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    calc
      (∑' n : Nat.factoredNumbers S, 1 / (n : ℝ)) =
          ∑' n : Nat.factoredNumbers S, rpowSeriesTerm 1 n := by
            apply tsum_congr
            exact fun n => (hterm1 n).symm
      _ = ∏ p ∈ S with p.Prime, (1 - Real.rpow (p : ℝ) (-1))⁻¹ :=
            hfact1.2.tsum_eq
      _ = ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
            rw [hfilterPrime]
            apply Finset.prod_congr rfl
            intro p hp
            simp [Real.rpow_neg_one]
  have hprimeFactorBound (p : ℕ) (hp : p ∈ S) :
      (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (2 / (p : ℝ)) := by
    have hscale := markedPrime_scale_bounds hxpos hL ha hp
    have hp4 : (4 : ℝ) < (p : ℝ) := hscale.1
    have hp0 : 0 < (p : ℝ) := by linarith
    let q := 1 / (p : ℝ)
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hqhalf : q ≤ 1 / 2 := by
      dsimp [q]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hden : 0 < 1 - q := by linarith
    have hfrac' : 1 / (1 - q) ≤ 1 + 2 * q := by
      apply (div_le_iff₀ hden).2
      have hprod := mul_nonneg hq0 (by linarith : 0 ≤ 1 - 2 * q)
      nlinarith
    have hfrac : (1 - q)⁻¹ ≤ 1 + 2 * q := by simpa [one_div] using hfrac'
    have hexp : 1 + 2 * q ≤ Real.exp (2 * q) := by
      have h := Real.add_one_le_exp (2 * q)
      linarith
    calc
      (1 - 1 / (p : ℝ))⁻¹ = (1 - q)⁻¹ := by simp [q]
      _ ≤ Real.exp (2 * q) := hfrac.trans hexp
      _ = Real.exp (2 / (p : ℝ)) := by congr 1; dsimp [q]; ring
  have hprod1 :
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) ≤
        Real.exp (2 * (∑ p ∈ S, 1 / (p : ℝ))) := by
    calc
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) ≤
          ∏ p ∈ S, Real.exp (2 / (p : ℝ)) := by
            apply Finset.prod_le_prod₀
            · intro p hp
              have hscale := markedPrime_scale_bounds hxpos hL ha hp
              have hp0 : 0 < (p : ℝ) := by linarith [hscale.1]
              have hq : 0 ≤ 1 / (p : ℝ) := by positivity
              have hden : 0 < 1 - 1 / (p : ℝ) := by
                have hp2 : (2 : ℝ) ≤ (p : ℝ) := by linarith [hscale.1]
                have hqle : 1 / (p : ℝ) ≤ 1 / 2 :=
                  one_div_le_one_div_of_le (by norm_num) hp2
                linarith
              exact inv_nonneg.mpr hden.le
            · intro p hp
              exact hprimeFactorBound p hp
      _ = Real.exp (2 * (∑ p ∈ S, 1 / (p : ℝ))) := by
            rw [← Real.exp_sum]
            congr 1
            calc
              (∑ p ∈ S, 2 / (p : ℝ)) =
                  ∑ p ∈ S, 2 * (1 / (p : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    ring
              _ = 2 * (∑ p ∈ S, 1 / (p : ℝ)) := by rw [← Finset.mul_sum]
  have hJ0rep := groupHarmonicMass_eq_tsum_factoredNumbers x K a
  have hweightSummable :
      Summable (fun n : Nat.factoredNumbers S =>
        markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact div_nonneg
        (markedWeight_nonneg_le (x := x) (K := K) (a := a) (h := n) hmassxLower).1
        (Nat.cast_nonneg _)
    · intro n
      have hw := markedWeight_nonneg_le (x := x) (K := K) (a := a) (h := n) hmassxLower
      have hnNat : 0 < (n : ℕ) := Nat.pos_of_ne_zero n.property.1
      have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hnNat
      calc
        markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) ≤
            B * (1 / (n : ℝ)) := by
              calc
                _ ≤ B / (n : ℝ) := div_le_div_of_nonneg_right hw.2 hn.le
                _ = B * (1 / (n : ℝ)) := by ring
        _ = B * rpowSeriesTerm 1 n := by rw [hterm1]
    · exact hfact1.1.mul_left B
  have hJupper : groupHarmonicMass x K a ≤ Cmass := by
    rw [hJ0rep]
    have htsum := hweightSummable.tsum_le_tsum
      (fun n => by
        have hw := markedWeight_nonneg_le (x := x) (K := K) (a := a) (h := n) hmassxLower
        have hnNat : 0 < (n : ℕ) := Nat.pos_of_ne_zero n.property.1
        have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hnNat
        calc
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) ≤
              B * (1 / (n : ℝ)) := by
                calc
                  _ ≤ B / (n : ℝ) := div_le_div_of_nonneg_right hw.2 hn.le
                  _ = B * (1 / (n : ℝ)) := by ring
          _ = B * rpowSeriesTerm 1 n := by rw [hterm1])
      (hfact1.1.mul_left B)
    calc
      (∑' n : Nat.factoredNumbers S,
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ)) ≤
          ∑' n : Nat.factoredNumbers S, B * rpowSeriesTerm 1 n := htsum
      _ = B * ∑' n : Nat.factoredNumbers S, rpowSeriesTerm 1 n := by rw [tsum_mul_left]
      _ = B * ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
          congr 1
          calc
            (∑' n : Nat.factoredNumbers S, rpowSeriesTerm 1 n) =
                ∑' n : Nat.factoredNumbers S, 1 / (n : ℝ) := by
                  apply tsum_congr
                  exact hterm1
            _ = ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := hrecipSum
      _ ≤ B * Real.exp (2 * (∑ p ∈ S, 1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hprod1 (by positivity)
      _ ≤ Cmass := by
          dsimp [Cmass]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.exp_le_exp.mpr (by nlinarith [hsumP_upper])
  let choices : Finset (Fin K → ℕ) :=
    Fintype.piFinset (fun i : Fin K => primeBand x (a i))
  let choiceProduct (f : Fin K → ℕ) : ℕ := ∏ i : Fin K, f i
  have hchoicePrime (f : Fin K → ℕ) (hf : f ∈ choices) (i : Fin K) :
      (f i).Prime := by
    have hmem : f i ∈ primeBand x (a i) := by
      exact Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
    exact (Finset.mem_filter.mp hmem).2.1
  have hchoiceGroup (f : Fin K → ℕ) (hf : f ∈ choices) :
      IsGroupInteger x K a (choiceProduct f) := by
    intro p hp hpd
    obtain ⟨i, hi, hdiv⟩ :=
      (_root_.Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) f).mp (by simpa [choiceProduct] using hpd)
    have hmem : f i ∈ primeBand x (a i) := by
      exact Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
    have hpi : (f i).Prime := (Finset.mem_filter.mp hmem).2.1
    have hpeq : p = f i := (Nat.prime_dvd_prime_iff_eq hp hpi).mp hdiv
    rw [hpeq]
    simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hmem⟩
  have hchoiceInjective : Set.InjOn choiceProduct (↑choices) := by
    intro f hf g hg hfg
    funext i
    have hfmem : f i ∈ primeBand x (a i) := by
      exact Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
    have hgmem (j : Fin K) : g j ∈ primeBand x (a j) := by
      exact Fintype.mem_piFinset.mp (by simpa [choices] using hg) j
    have hdiv : f i ∣ choiceProduct g := by
      rw [← hfg]
      exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    obtain ⟨j, hj, hdivj⟩ :=
      (_root_.Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (hchoicePrime f hf i)) g).mp
        (by simpa [choiceProduct] using hdiv)
    have hpEq : f i = g j :=
      (Nat.prime_dvd_prime_iff_eq (hchoicePrime f hf i) (hchoicePrime g hg j)).mp hdivj
    by_cases hji : j = i
    · simpa [hji] using hpEq
    · have hij : i ≠ j := fun heq => hji heq.symm
      have hdisj := hBands i j hij
      have hfj : f i ∈ primeBand x (a j) := by rw [hpEq]; exact hgmem j
      exact False.elim ((Finset.disjoint_left.mp hdisj) hfmem hfj)
  let choiceEmbedding : {f : Fin K → ℕ // f ∈ choices} ↪
      Nat.factoredNumbers S := {
    toFun := fun f => ⟨choiceProduct f, (isGroupInteger_iff_mem_factoredNumbers
      x K a (choiceProduct f)).mp (hchoiceGroup f f.property)⟩
    inj' := by
      intro f g hfg
      apply Subtype.ext
      exact hchoiceInjective f.property g.property (congrArg Subtype.val hfg)
  }
  have hmassPositive (i : Fin K) : 0 < bandMass x (a i) :=
    lt_of_lt_of_le (by positivity : 0 < Real.log 2 / 2) (hmassxLower i)
  have hchoiceTerm (f : Fin K → ℕ) (hf : f ∈ choices) :
      markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
        (choiceProduct f : ℝ) =
      ∏ i : Fin K, 1 / ((f i : ℝ) * bandMass x (a i)) := by
    have hw := harmonic_markedWeight_onePrimeChoice x K a f (by simpa [choices] using hf) hBands
    have hcast : (choiceProduct f : ℝ) = ∏ i : Fin K, (f i : ℝ) := by
      simp [choiceProduct]
    calc
      markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
          (choiceProduct f : ℝ) =
          (∏ i : Fin K, 1 / bandMass x (a i)) /
            (∏ i : Fin K, (f i : ℝ)) := by rw [hw, hcast]
      _ = ∏ i : Fin K,
          (1 / bandMass x (a i)) / (f i : ℝ) := by
            rw [← Finset.prod_div_distrib]
      _ = ∏ i : Fin K,
          1 / ((f i : ℝ) * bandMass x (a i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hfi : (f i : ℝ) ≠ 0 := by
              exact_mod_cast (hchoicePrime f hf i).ne_zero
            have hm : bandMass x (a i) ≠ 0 := (hmassPositive i).ne'
            field_simp [hfi, hm]
            <;> ring
  have hlocalChoiceSum (i : Fin K) :
      (∑ p ∈ primeBand x (a i),
        1 / ((p : ℝ) * bandMass x (a i))) = 1 := by
    have hm := hmassPositive i
    calc
      (∑ p ∈ primeBand x (a i),
        1 / ((p : ℝ) * bandMass x (a i))) =
          ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) / bandMass x (a i) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
            field_simp [hp0, hm.ne']
      _ = (∑ p ∈ primeBand x (a i), 1 / (p : ℝ)) / bandMass x (a i) := by
            rw [Finset.sum_div]
      _ = 1 := by
        rw [bandMass]
        exact div_self (by simpa [bandMass] using hm.ne')
  have hchoiceSum :
      (∑ f ∈ choices,
        markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
          (choiceProduct f : ℝ)) = 1 := by
    have hterm (f : Fin K → ℕ) (hf : f ∈ choices) :
        markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
          (choiceProduct f : ℝ) =
        ∏ i : Fin K, 1 / ((f i : ℝ) * bandMass x (a i)) :=
      hchoiceTerm f hf
    calc
      (∑ f ∈ choices,
          markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
            (choiceProduct f : ℝ)) =
          ∑ f ∈ choices, ∏ i : Fin K,
            1 / ((f i : ℝ) * bandMass x (a i)) := by
              apply Finset.sum_congr rfl
              intro f hf
              exact hterm f hf
      _ = ∏ i : Fin K,
            ∑ p ∈ primeBand x (a i), 1 / ((p : ℝ) * bandMass x (a i)) := by
              symm
              simpa [choices] using
                (Finset.prod_univ_sum
                  (fun i : Fin K => primeBand x (a i))
                  (fun i p => 1 / ((p : ℝ) * bandMass x (a i))))
      _ = 1 := by simp_rw [hlocalChoiceSum]; simp
  let choiceImage := choices.attach.map choiceEmbedding
  have hchoiceImageSum :
      (∑ n ∈ choiceImage,
        markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ)) = 1 := by
    calc
      (∑ n ∈ choiceImage,
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ)) =
          ∑ f ∈ choices.attach,
            markedWeight x K a (1 / 2 : ℝ) (choiceEmbedding f) /
              (choiceEmbedding f : ℝ) := by
                simp [choiceImage]
      _ = ∑ f ∈ choices.attach,
            markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
              (choiceProduct f : ℝ) := by
                apply Finset.sum_congr rfl
                intro f hf
                rfl
      _ = ∑ f ∈ choices,
            markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
              (choiceProduct f : ℝ) := by
                let F : (Fin K → ℕ) → ℝ := fun f =>
                  markedWeight x K a (1 / 2 : ℝ) (choiceProduct f) /
                    (choiceProduct f : ℝ)
                simpa [F] using (Finset.sum_attach choices F)
      _ = 1 := hchoiceSum
  have hJlower : 1 ≤ groupHarmonicMass x K a := by
    rw [hJ0rep]
    calc
      1 = ∑ n ∈ choiceImage,
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) := hchoiceImageSum.symm
      _ ≤ ∑' n : Nat.factoredNumbers S,
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) :=
            hweightSummable.sum_le_tsum choiceImage
              (fun n hn => div_nonneg
                (markedWeight_nonneg_le (x := x) (K := K) (a := a) (h := n)
                  hmassxLower).1 (Nat.cast_nonneg _))
  let iMax : Fin K := ⟨K - 1, by have hK := ha.1; omega⟩
  let aMax := a iMax
  have hAiMax : ∀ i : Fin K, a i ≤ aMax := by
    intro i
    by_cases hlt : i.val < iMax.val
    · exact (ha.2.2 i iMax hlt).le
    · have hEq : i = iMax := Fin.ext (by have := i.isLt; dsimp [iMax] at *; omega)
      simpa [hEq, aMax]
  have haMaxLower : (1 / 10 : ℝ) < aMax := (ha.2.1 iMax).1
  have haMaxUpper : aMax < 1 / 5 := (ha.2.1 iMax).2
  let Cshift := B * Real.exp (4 * Real.exp 2 * (K : ℝ) * Real.log 2)
  have hCshift : 0 < Cshift := by dsimp [Cshift]; positivity
  have hTailAt : ∀ ε : ℝ, 0 < ε → ∀ y : ℝ, x₀ ≤ y → ∀ R : ℕ,
      (∑ r ∈ (Finset.range (R + 1)).filter
        (fun r => IsGroupInteger y K a r ∧ Real.rpow y ε < (r : ℝ)),
        markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) ≤
      Cshift * Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) := by
    intro ε hε y hy R
    have hypos : 0 < y := lt_of_lt_of_le (by linarith [hx₀2]) hy
    have hy4 : 4 ≤ y := le_trans hx₀4 hy
    have hyScale : Xscale ≤ y := le_trans (le_max_left _ _) hy
    have hlogY : (100 : ℝ) ^ 10 ≤ Real.log y := by
      have hlog := Real.log_le_log (Real.exp_pos _) hyScale
      simpa [Xscale, Real.log_exp] using hlog
    have hLYpos : 0 < Real.log y := by nlinarith
    have hLYge1 : 1 ≤ Real.log y := by nlinarith
    have hRoot100 : Real.rpow ((100 : ℝ) ^ 10) (1 / 10 : ℝ) = 100 := by
      simpa using
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 100) 10 (1 / 10 : ℝ)).symm
    have hRootY : 100 ≤ Real.rpow (Real.log y) (1 / 10 : ℝ) := by
      calc
        100 = Real.rpow ((100 : ℝ) ^ 10) (1 / 10 : ℝ) := hRoot100.symm
        _ ≤ Real.rpow (Real.log y) (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hlogY (by norm_num)
    have hPowerMax : 100 ≤ Real.rpow (Real.log y) aMax :=
      le_trans hRootY (Real.rpow_le_rpow_of_exponent_le hLYge1 haMaxLower.le)
    let L := Real.log y
    let s := (Real.rpow L aMax)⁻¹
    let t := 1 - s
    have hpowMaxPos : 0 < Real.rpow L aMax := Real.rpow_pos_of_pos hLYpos _
    have hsPos : 0 < s := by dsimp [s]; positivity
    have hsSmall : s ≤ 1 / 100 := by
      have hInv : (Real.rpow L aMax)⁻¹ ≤ (100 : ℝ)⁻¹ :=
        (inv_le_inv₀ hpowMaxPos (by norm_num : (0 : ℝ) < 100)).2 hPowerMax
      simpa [s] using hInv
    have hsHalf : s ≤ 1 / 2 := by linarith
    have hsEq : s * Real.rpow L aMax = 1 := by
      dsimp [s]
      exact inv_mul_cancel₀ hpowMaxPos.ne'
    have htPos : 0 < t := by dsimp [t]; linarith
    have hmassLowerY : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass y (a i) := by
      have hyLower : Xlower ≤ y :=
        (le_trans (le_max_left Xlower (max Xupper Xdisj)) (le_max_right Xscale _)).trans hy
      exact hmassLower y hyLower
    have hmassUpperY : ∀ i : Fin K, bandMass y (a i) ≤ 2 * Real.log 2 := by
      have hyUpper : Xupper ≤ y :=
        (le_trans (le_max_left Xupper Xdisj) (le_trans (le_max_right Xlower _) (le_max_right Xscale _))).trans hy
      exact hmassUpper y hyUpper
    have hBandsY : ∀ i j : Fin K, i ≠ j →
        Disjoint (primeBand y (a i)) (primeBand y (a j)) := by
      have hyDisj : Xdisj ≤ y :=
        (le_trans (le_max_right Xupper Xdisj) (le_trans (le_max_right Xlower _) (le_max_right Xscale _))).trans hy
      exact hXdisj y hyDisj
    let Sy := markedPrimes y K a
    have hSyPrime : ∀ p ∈ Sy, p.Prime := by
      intro p hp
      exact prime_of_mem_markedPrimes hp
    have hSyFilter : Sy.filter Nat.Prime = Sy := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hp
        exact ⟨hp, hSyPrime p hp⟩
    have hpairwiseY : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
        (fun i => primeBand y (a i)) := by
      intro i hi j hj hij
      exact hBandsY i j hij
    have hsumPY : (∑ p ∈ Sy, 1 / (p : ℝ)) =
        ∑ i : Fin K, bandMass y (a i) := by
      rw [show Sy = Finset.univ.biUnion (fun i => primeBand y (a i)) by rfl]
      rw [Finset.sum_biUnion hpairwiseY]
      simp [bandMass]
    have hsumPYupper : (∑ p ∈ Sy, 1 / (p : ℝ)) ≤
        (K : ℝ) * (2 * Real.log 2) := by
      rw [hsumPY]
      calc
        (∑ i : Fin K, bandMass y (a i)) ≤
            ∑ i : Fin K, 2 * Real.log 2 :=
              Finset.sum_le_sum fun i hi => hmassUpperY i
        _ = (K : ℝ) * (2 * Real.log 2) := by simp
    have hExp98 : 2 ≤ Real.exp (98 : ℝ) := by
      have h := Real.add_one_le_exp (98 : ℝ)
      norm_num at h ⊢
      linarith
    have hExp100 : 2 * Real.exp 2 ≤ Real.exp 100 := by
      have heq : Real.exp 100 = Real.exp 2 * Real.exp 98 := by
        rw [show (100 : ℝ) = 2 + 98 by norm_num, Real.exp_add]
      calc
        2 * Real.exp 2 = Real.exp 2 * 2 := by ring
        _ ≤ Real.exp 2 * Real.exp 98 :=
          mul_le_mul_of_nonneg_left hExp98 (Real.exp_pos _).le
        _ = Real.exp 100 := heq.symm
    have hprimeLarge (p : ℕ) (hp : p ∈ Sy) : 2 * Real.exp 2 ≤ (p : ℝ) := by
      have hbi : p ∈ Finset.univ.biUnion (fun i : Fin K => primeBand y (a i)) := by
        simpa [Sy, markedPrimes] using hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hbi
      rcases Finset.mem_filter.mp hpi with ⟨_, ⟨_, hplower, _⟩⟩
      calc
        2 * Real.exp 2 ≤ Real.exp 100 := hExp100
        _ ≤ Real.exp (Real.rpow L (1 / 10 : ℝ)) :=
          Real.exp_le_exp.mpr hRootY
        _ ≤ Real.exp (Real.rpow L (a i)) := by
          exact Real.exp_le_exp.mpr
            (Real.rpow_le_rpow_of_exponent_le hLYge1 (ha.2.1 i).1.le)
        _ ≤ (p : ℝ) := hplower
    have hprimeShift (p : ℕ) (hp : p ∈ Sy) :
        Real.rpow (p : ℝ) (-t) ≤ Real.exp 2 / (p : ℝ) := by
      have hbi : p ∈ Finset.univ.biUnion (fun i : Fin K => primeBand y (a i)) := by
        simpa [Sy, markedPrimes] using hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hbi
      rcases Finset.mem_filter.mp hpi with ⟨_, ⟨_, hplower, hpupper⟩⟩
      have hpowI : Real.rpow L (a i) ≤ Real.rpow L aMax :=
        Real.rpow_le_rpow_of_exponent_le hLYge1 (hAiMax i)
      have hpLower := hprimeLarge p hp
      have hpPos : 0 < (p : ℝ) :=
        lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.exp 2) hpLower
      have hpUpper : (p : ℝ) ≤ Real.exp (2 * Real.rpow L aMax) := by
        calc
          (p : ℝ) ≤ Real.exp (2 * Real.rpow L (a i)) := hpupper
          _ ≤ Real.exp (2 * Real.rpow L aMax) := by
                apply Real.exp_le_exp.mpr
                have hnonneg : 0 ≤ Real.rpow L (a i) :=
                  (Real.rpow_pos_of_pos hLYpos _).le
                nlinarith [hpowI, hnonneg]
      have hlogp : Real.log (p : ℝ) ≤ 2 * Real.rpow L aMax := by
        calc
          Real.log (p : ℝ) ≤ Real.log (Real.exp (2 * Real.rpow L aMax)) :=
            Real.log_le_log hpPos hpUpper
          _ = 2 * Real.rpow L aMax := by rw [Real.log_exp]
      have hslog : s * Real.log (p : ℝ) ≤ 2 := by
        calc
          s * Real.log (p : ℝ) ≤ s * (2 * Real.rpow L aMax) :=
            mul_le_mul_of_nonneg_left hlogp hsPos.le
          _ = 2 := by
            calc
              s * (2 * Real.rpow L aMax) = 2 * (s * Real.rpow L aMax) := by ring
              _ = 2 := by rw [hsEq]; ring
      have harg : (-t) * Real.log (p : ℝ) =
          -Real.log (p : ℝ) + s * Real.log (p : ℝ) := by dsimp [t]; ring
      calc
        Real.rpow (p : ℝ) (-t) =
            Real.exp (-Real.log (p : ℝ)) *
              Real.exp (s * Real.log (p : ℝ)) := by
                calc
                  Real.rpow (p : ℝ) (-t) =
                      Real.exp (Real.log (p : ℝ) * (-t)) :=
                        Real.rpow_def_of_pos hpPos (-t)
                  _ = Real.exp (-Real.log (p : ℝ) + s * Real.log (p : ℝ)) := by
                        congr 1
                        calc
                          Real.log (p : ℝ) * (-t) = (-t) * Real.log (p : ℝ) := by ring
                          _ = -Real.log (p : ℝ) + s * Real.log (p : ℝ) := harg
                  _ = Real.exp (-Real.log (p : ℝ)) *
                        Real.exp (s * Real.log (p : ℝ)) := Real.exp_add _ _
        _ ≤ Real.exp (-Real.log (p : ℝ)) * Real.exp 2 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hslog) (Real.exp_pos _).le
        _ = Real.exp 2 / (p : ℝ) := by
              rw [Real.exp_neg, Real.exp_log hpPos]
              ring
    have hfactorShift (p : ℕ) (hp : p ∈ Sy) :
        (1 - Real.rpow (p : ℝ) (-t))⁻¹ ≤
          Real.exp (2 * Real.exp 2 / (p : ℝ)) := by
      have hpPos : 0 < (p : ℝ) := by
        exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.exp 2) (hprimeLarge p hp)
      let q := Real.rpow (p : ℝ) (-t)
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hqle : q ≤ 1 / 2 := by
        calc
          q ≤ Real.exp 2 / (p : ℝ) := hprimeShift p hp
          _ ≤ 1 / 2 := by
                apply (div_le_iff₀ hpPos).2
                nlinarith [hprimeLarge p hp]
      have hden : 0 < 1 - q := by linarith
      have hfrac : (1 - q)⁻¹ ≤ Real.exp (2 * q) := by
        have hfrac' : 1 / (1 - q) ≤ 1 + 2 * q := by
          apply (div_le_iff₀ hden).2
          have hh := mul_nonneg hq0 (by linarith : 0 ≤ 1 - 2 * q)
          nlinarith
        have hexp : 1 + 2 * q ≤ Real.exp (2 * q) := by
          have hh := Real.add_one_le_exp (2 * q)
          linarith
        simpa [one_div] using hfrac'.trans hexp
      calc
        (1 - Real.rpow (p : ℝ) (-t))⁻¹ = (1 - q)⁻¹ := by rfl
        _ ≤ Real.exp (2 * q) := hfrac
        _ ≤ Real.exp (2 * Real.exp 2 / (p : ℝ)) := by
              apply Real.exp_le_exp.mpr
              calc
                2 * q = 2 * Real.rpow (p : ℝ) (-t) := by rfl
                _ ≤ 2 * (Real.exp 2 / (p : ℝ)) :=
                  mul_le_mul_of_nonneg_left (hprimeShift p hp) (by norm_num)
                _ = 2 * Real.exp 2 / (p : ℝ) := by ring
    have hprodShift :
        (∏ p ∈ Sy with p.Prime,
          (1 - Real.rpow (p : ℝ) (-t))⁻¹) ≤
            Real.exp (2 * Real.exp 2 * (∑ p ∈ Sy, 1 / (p : ℝ))) := by
      rw [hSyFilter]
      calc
        (∏ p ∈ Sy, (1 - Real.rpow (p : ℝ) (-t))⁻¹) ≤
            ∏ p ∈ Sy, Real.exp (2 * Real.exp 2 / (p : ℝ)) := by
              apply Finset.prod_le_prod₀
              · intro p hp
                have hpPos : 0 < (p : ℝ) :=
                  lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.exp 2)
                    (hprimeLarge p hp)
                have hqle : Real.rpow (p : ℝ) (-t) ≤ 1 / 2 := by
                  calc
                    Real.rpow (p : ℝ) (-t) ≤ Real.exp 2 / (p : ℝ) := hprimeShift p hp
                    _ ≤ 1 / 2 := by
                      apply (div_le_iff₀ hpPos).2
                      nlinarith [hprimeLarge p hp]
                have hden : 0 < 1 - Real.rpow (p : ℝ) (-t) := by linarith
                exact inv_nonneg.mpr hden.le
              · intro p hp
                exact hfactorShift p hp
        _ = Real.exp (2 * Real.exp 2 * (∑ p ∈ Sy, 1 / (p : ℝ))) := by
              rw [← Real.exp_sum]
              congr 1
              calc
                (∑ p ∈ Sy, 2 * Real.exp 2 / (p : ℝ)) =
                    ∑ p ∈ Sy, (2 * Real.exp 2) * (1 / (p : ℝ)) := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      ring
                _ = (2 * Real.exp 2) * (∑ p ∈ Sy, 1 / (p : ℝ)) := by
                      rw [← Finset.mul_sum]
    have hfactShift := hasSum_rpowSeries_factoredNumbers
      (s := Sy) (t := t) htPos hSyPrime
    have hshiftedWeightSummable :
        Summable (fun n : Nat.factoredNumbers Sy =>
          markedWeight y K a (1 / 2 : ℝ) n * rpowSeriesTerm t n) := by
      apply Summable.of_nonneg_of_le
      · intro n
        have hrpow : 0 ≤ rpowSeriesTerm t n := by
          have hn : (n : ℕ) ≠ 0 := n.property.1
          simp only [rpowSeriesTerm, if_neg hn]
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        exact mul_nonneg
          (markedWeight_nonneg_le (x := y) (K := K) (a := a) (h := n) hmassLowerY).1
          hrpow
      · intro n
        have hw := markedWeight_nonneg_le (x := y) (K := K) (a := a) (h := n) hmassLowerY
        have hrpow : 0 ≤ rpowSeriesTerm t n := by
          have hn : (n : ℕ) ≠ 0 := n.property.1
          simp only [rpowSeriesTerm, if_neg hn]
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        exact mul_le_mul_of_nonneg_right hw.2 hrpow
      · exact hfactShift.1.mul_left B
    have hshiftSumBound :
        (∑' n : Nat.factoredNumbers Sy,
          markedWeight y K a (1 / 2 : ℝ) n * rpowSeriesTerm t n) ≤ Cshift := by
      have htsum := hshiftedWeightSummable.tsum_le_tsum
        (fun n => by
          have hw := markedWeight_nonneg_le
            (x := y) (K := K) (a := a) (h := n) hmassLowerY
          have hrpow : 0 ≤ rpowSeriesTerm t n := by
            have hn : (n : ℕ) ≠ 0 := n.property.1
            simp only [rpowSeriesTerm, if_neg hn]
            exact Real.rpow_nonneg (Nat.cast_nonneg _) _
          exact mul_le_mul_of_nonneg_right hw.2 hrpow)
        (hfactShift.1.mul_left B)
      calc
        (∑' n : Nat.factoredNumbers Sy,
          markedWeight y K a (1 / 2 : ℝ) n * rpowSeriesTerm t n) ≤
            ∑' n : Nat.factoredNumbers Sy, B * rpowSeriesTerm t n := htsum
        _ = B * ∏ p ∈ Sy with p.Prime,
              (1 - Real.rpow (p : ℝ) (-t))⁻¹ := by
                rw [tsum_mul_left, hfactShift.2.tsum_eq]
        _ ≤ B * Real.exp (2 * Real.exp 2 * (∑ p ∈ Sy, 1 / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left hprodShift (by positivity)
        _ ≤ Cshift := by
              dsimp [Cshift]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.mpr
              calc
                2 * Real.exp 2 * (∑ p ∈ Sy, 1 / (p : ℝ)) ≤
                    2 * Real.exp 2 * ((K : ℝ) * (2 * Real.log 2)) :=
                      mul_le_mul_of_nonneg_left hsumPYupper (by positivity)
                _ = 4 * Real.exp 2 * (K : ℝ) * Real.log 2 := by ring
    let T : Finset ℕ := (Finset.range (R + 1)).filter
      (fun r => IsGroupInteger y K a r ∧ Real.rpow y ε < (r : ℝ))
    have hTGroup : ∀ r ∈ T, IsGroupInteger y K a r := by
      intro r hr
      exact (Finset.mem_filter.mp hr).2.1
    let fNat (r : ℕ) : ℝ := if IsGroupInteger y K a r then
      markedWeight y K a (1 / 2 : ℝ) r * rpowSeriesTerm t r else 0
    let fSub (n : Nat.factoredNumbers Sy) : ℝ :=
      markedWeight y K a (1 / 2 : ℝ) n * rpowSeriesTerm t n
    have hfEq : ∀ r (hr : r ∈ T), fNat r = fSub ⟨r,
        (isGroupInteger_iff_mem_factoredNumbers y K a r).mp (hTGroup r hr)⟩ := by
      intro r hr
      simp [fNat, fSub, hTGroup r hr]
    have hfSubNonneg : ∀ n : Nat.factoredNumbers Sy, 0 ≤ fSub n := by
      intro n
      have hrpow : 0 ≤ rpowSeriesTerm t n := by
        have hn : (n : ℕ) ≠ 0 := n.property.1
        rw [rpowSeriesTerm, if_neg hn]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_nonneg
        (markedWeight_nonneg_le (x := y) (K := K) (a := a) (h := n) hmassLowerY).1
        hrpow
    have hpartial : (∑ r ∈ T, fNat r) ≤
        ∑' n : Nat.factoredNumbers Sy, fSub n := by
      exact finite_group_sum_le_tsum y K a T hTGroup fNat fSub hfEq
        hshiftedWeightSummable hfSubNonneg
    have hpowTail (r : ℕ) (hr : r ∈ T) :
        markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ) ≤
          Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) * fNat r := by
      have hm := Finset.mem_filter.mp hr
      have hGroup := hm.2.1
      have hrlarge := hm.2.2
      have hrpos : 0 < (r : ℝ) :=
        lt_trans (Real.rpow_pos_of_pos hypos ε) hrlarge
      have hlogr : ε * Real.log y ≤ Real.log (r : ℝ) := by
        have hlog := Real.log_le_log (Real.rpow_pos_of_pos hypos ε) hrlarge.le
        rw [Real.log_rpow hypos] at hlog
        exact hlog
      have hlogp : Real.log (r : ℝ) ≥ ε * Real.log y := hlogr
      have hsmallPow : Real.rpow (r : ℝ) (-s) ≤
          Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) := by
        have hmulp := mul_le_mul_of_nonpos_left hlogp (neg_nonpos.mpr hsPos.le)
        have hLmul : Real.log y * s = Real.rpow (Real.log y) (1 - aMax) := by
          calc
            Real.log y * s = Real.rpow (Real.log y) 1 /
                Real.rpow (Real.log y) aMax := by
                  dsimp [s, L]
                  rw [Real.rpow_one]
                  ring
            _ = Real.rpow (Real.log y) (1 - aMax) :=
              (Real.rpow_sub hLYpos 1 aMax).symm
        have hArg : Real.log (r : ℝ) * (-s) ≤
            -ε * Real.rpow (Real.log y) (1 - aMax) := by
          calc
            Real.log (r : ℝ) * (-s) = (-s) * Real.log (r : ℝ) := by ring
            _ ≤ (-s) * (ε * Real.log y) := hmulp
            _ = -ε * (Real.log y * s) := by ring
            _ = -ε * Real.rpow (Real.log y) (1 - aMax) := by rw [hLmul]
        calc
          Real.rpow (r : ℝ) (-s) =
              Real.exp (Real.log (r : ℝ) * (-s)) := Real.rpow_def_of_pos hrpos (-s)
          _ ≤ Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) :=
                Real.exp_le_exp.mpr hArg
      have htEq : (-1 : ℝ) = (-s) + (-t) := by dsimp [t]; ring
      have hsplit : Real.rpow (r : ℝ) (-1) =
          Real.rpow (r : ℝ) (-s) * Real.rpow (r : ℝ) (-t) := by
        calc
          Real.rpow (r : ℝ) (-1) = Real.rpow (r : ℝ) ((-s) + (-t)) := by rw [htEq]
          _ = Real.rpow (r : ℝ) (-s) * Real.rpow (r : ℝ) (-t) :=
            Real.rpow_add hrpos (-s) (-t)
      have hwt := markedWeight_nonneg_le
        (x := y) (K := K) (a := a) (h := r) hmassLowerY
      have hterm : rpowSeriesTerm t r = Real.rpow (r : ℝ) (-t) := by
        simp [rpowSeriesTerm, Nat.ne_of_gt (Nat.cast_pos.mp hrpos)]
      have hneg : Real.rpow (r : ℝ) (-1) = (r : ℝ)⁻¹ := by
        simpa [Real.rpow_one] using (Real.rpow_neg hrpos.le (1 : ℝ))
      have hgroupTerm : fNat r =
          markedWeight y K a (1 / 2 : ℝ) r * rpowSeriesTerm t r := by
        simp [fNat, hGroup]
      calc
        markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ) =
            markedWeight y K a (1 / 2 : ℝ) r * Real.rpow (r : ℝ) (-1) := by
              calc
                _ = markedWeight y K a (1 / 2 : ℝ) r * (r : ℝ)⁻¹ := by ring
                _ = _ := by rw [← hneg]
        _ = Real.rpow (r : ℝ) (-s) *
              (markedWeight y K a (1 / 2 : ℝ) r * Real.rpow (r : ℝ) (-t)) := by
              rw [hsplit]
              ring
        _ ≤ Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) *
              (markedWeight y K a (1 / 2 : ℝ) r * Real.rpow (r : ℝ) (-t)) :=
                mul_le_mul_of_nonneg_right hsmallPow
                  (mul_nonneg hwt.1 (Real.rpow_nonneg hrpos.le _))
        _ = Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) * fNat r := by
              rw [← hterm, hgroupTerm]
    have hfiniteTail :
        (∑ r ∈ T,
          markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) ≤
          Cshift * Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) := by
      calc
        (∑ r ∈ T,
            markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) ≤
            ∑ r ∈ T,
              Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) * fNat r :=
                Finset.sum_le_sum fun r hr => hpowTail r hr
        _ = Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) *
              ∑ r ∈ T, fNat r := by rw [← Finset.mul_sum]
        _ ≤ Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) *
              ∑' n : Nat.factoredNumbers Sy, fSub n :=
                mul_le_mul_of_nonneg_left hpartial (Real.exp_pos _).le
        _ ≤ Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) * Cshift :=
                mul_le_mul_of_nonneg_left hshiftSumBound (Real.exp_pos _).le
        _ = Cshift * Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) := by ring
    exact hfiniteTail
  have hOmegaEq (n : Nat.factoredNumbers S) :
      markedOmega x K a n = ((n : ℕ).primeFactors.card) := by
    let U (i : Fin K) := (primeBand x (a i)).filter (fun p => p ∣ (n : ℕ))
    have hpairU : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K))) U := by
      intro i hi j hj hij
      apply Finset.disjoint_left.mpr
      intro p hpi hpj
      exact (Finset.disjoint_left.mp (hBands i j hij))
        (Finset.mem_filter.mp hpi).1 (Finset.mem_filter.mp hpj).1
    have hUnion : Finset.univ.biUnion U = (n : ℕ).primeFactors := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
        rcases Finset.mem_filter.mp hpi with ⟨hband, hdiv⟩
        have hpPrime : p.Prime := (Finset.mem_filter.mp hband).2.1
        exact (Nat.mem_primeFactors_of_ne_zero n.property.1).mpr ⟨hpPrime, hdiv⟩
      · intro hp
        have hpFact := (Nat.mem_primeFactors_of_ne_zero n.property.1).mp hp
        have hpS : p ∈ S :=
          (Nat.mem_factoredNumbers'.mp n.property) p hpFact.1 hpFact.2
        have hpUnion : p ∈ Finset.univ.biUnion (fun i : Fin K => primeBand x (a i)) := by
          simpa [S, markedPrimes] using hpS
        rcases Finset.mem_biUnion.mp hpUnion with ⟨i, hi, hpi⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi,
          Finset.mem_filter.mpr ⟨hpi, hpFact.2⟩⟩
    calc
      markedOmega x K a n = ∑ i : Fin K, (U i).card := by
        unfold markedOmega
        apply Finset.sum_congr rfl
        intro i hi
        simp [U, bandOmega]
      _ = (Finset.univ.biUnion U).card := (Finset.card_biUnion hpairU).symm
      _ = ((n : ℕ).primeFactors.card) := by rw [hUnion]
  have hOmegaSum (n : Nat.factoredNumbers S) (i : Fin K) :
      (bandOmega x (a i) n : ℝ) =
        ∑ p ∈ primeBand x (a i), if p ∣ (n : ℕ) then (1 : ℝ) else 0 := by
    unfold bandOmega
    calc
      (((primeBand x (a i)).filter (fun p => p ∣ (n : ℕ))).card : ℝ) =
          ∑ p ∈ (primeBand x (a i)).filter (fun p => p ∣ (n : ℕ)), (1 : ℝ) := by simp
      _ = ∑ p ∈ primeBand x (a i), if p ∣ (n : ℕ) then (1 : ℝ) else 0 := by
            rw [Finset.sum_filter]
  have htupleIndicator (n : Nat.factoredNumbers S) (f : Fin K → ℕ) :
      (∏ i : Fin K, if f i ∣ (n : ℕ) then (1 : ℝ) else 0) =
        if ∀ i : Fin K, f i ∣ (n : ℕ) then 1 else 0 := by
    by_cases hall : ∀ i : Fin K, f i ∣ (n : ℕ)
    · simp [hall]
    · have hnotall := hall
      push_neg at hall
      obtain ⟨i, hi⟩ := hall
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
      simp [hnotall]
  have hOmegaProduct (n : Nat.factoredNumbers S) :
      (∏ i : Fin K, (bandOmega x (a i) n : ℝ)) =
        ∑ f ∈ choices, if ∀ i : Fin K, f i ∣ (n : ℕ) then 1 else 0 := by
    calc
      (∏ i : Fin K, (bandOmega x (a i) n : ℝ)) =
          ∏ i : Fin K, ∑ p ∈ primeBand x (a i),
            if p ∣ (n : ℕ) then (1 : ℝ) else 0 := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hOmegaSum n i
      _ = ∑ f ∈ choices,
          ∏ i : Fin K, if f i ∣ (n : ℕ) then (1 : ℝ) else 0 := by
            simpa [choices] using
              (Finset.prod_univ_sum
                (fun i : Fin K => primeBand x (a i))
                (fun i p => if p ∣ (n : ℕ) then (1 : ℝ) else 0))
      _ = ∑ f ∈ choices,
          if ∀ i : Fin K, f i ∣ (n : ℕ) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro f hf
            exact htupleIndicator n f
  let Vprod := ∏ i : Fin K, bandMass x (a i)
  let qOmegaConst := (2 : ℝ) ^ K / Vprod
  have hVprodPos : 0 < Vprod := by
    dsimp [Vprod]
    apply Finset.prod_pos
    intro i hi
    exact hmassPositive i
  have hpointWeight (n : Nat.factoredNumbers S) :
      markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) =
        qOmegaConst *
          ∑ f ∈ choices,
            if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0 := by
    by_cases hcover : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ (n : ℕ)
    · have hbandOmegaLower : ∀ i : Fin K, 1 ≤ bandOmega x (a i) n := by
        intro i
        obtain ⟨p, hp, hpd⟩ := hcover i
        have hmem : p ∈ (primeBand x (a i)).filter (fun p => p ∣ (n : ℕ)) :=
          Finset.mem_filter.mpr ⟨hp, hpd⟩
        have hcard : 0 < ((primeBand x (a i)).filter (fun p => p ∣ (n : ℕ))).card :=
          Finset.card_pos.mpr ⟨p, hmem⟩
        dsimp [bandOmega]
        omega
      have hOmegaLower : K ≤ markedOmega x K a n := by
        calc
          K = ∑ i : Fin K, 1 := by simp
          _ ≤ ∑ i : Fin K, bandOmega x (a i) n :=
                Finset.sum_le_sum fun i hi => hbandOmegaLower i
      have hcardLower : K ≤ ((n : ℕ).primeFactors.card) := by
        rw [← hOmegaEq n]
        exact hOmegaLower
      have hcancel : (1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K = 1 := by
        rw [← mul_pow]
        norm_num
      have hdecomp : ((n : ℕ).primeFactors.card) - K + K =
          (n : ℕ).primeFactors.card := Nat.sub_add_cancel hcardLower
      have hqpow : (1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K) =
          (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (n : ℕ).primeFactors.card := by
        calc
          (1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K) =
              (1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K) * 1 := by ring
          _ = (1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K) *
                ((1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K) := by rw [hcancel]
          _ = ((1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K) *
                (1 / 2 : ℝ) ^ K) * (2 : ℝ) ^ K := by ring
          _ = (1 / 2 : ℝ) ^ (((n : ℕ).primeFactors.card) - K + K) *
                (2 : ℝ) ^ K := by rw [← pow_add]
          _ = (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (n : ℕ).primeFactors.card := by
                rw [hdecomp]
                ring
      have hprodDiv :
          (∏ i : Fin K, (bandOmega x (a i) n : ℝ) / bandMass x (a i)) =
            (∏ i : Fin K, (bandOmega x (a i) n : ℝ)) / Vprod := by
        rw [Finset.prod_div_distrib]
      have hselectedOmega :
          (∑ f ∈ choices,
            if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) =
            halfOmegaTerm n * ∏ i : Fin K, (bandOmega x (a i) n : ℝ) := by
        calc
          (∑ f ∈ choices,
            if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) =
              ∑ f ∈ choices,
                halfOmegaTerm n *
                  (if ∀ i : Fin K, f i ∣ (n : ℕ) then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro f hf
                    by_cases hselected : ∀ i : Fin K, f i ∣ (n : ℕ)
                    · simp [hselected]
                    · simp [hselected]
          _ = halfOmegaTerm n *
                ∑ f ∈ choices,
                  if ∀ i : Fin K, f i ∣ (n : ℕ) then 1 else 0 := by
                  rw [← Finset.mul_sum]
          _ = halfOmegaTerm n * ∏ i : Fin K, (bandOmega x (a i) n : ℝ) := by
                  rw [← hOmegaProduct n]
      have hterm : halfOmegaTerm n =
          (1 / 2 : ℝ) ^ (n : ℕ).primeFactors.card / (n : ℝ) := by
        have hn : (n : ℕ) ≠ 0 := n.property.1
        simp [halfOmegaTerm, hn]
      rw [markedWeight, if_pos hcover, hOmegaEq n]
      rw [hprodDiv, hqpow, hselectedOmega, hterm]
      dsimp [qOmegaConst]
      ring
    · have hmissing : ∃ i : Fin K,
          ∀ p ∈ primeBand x (a i), ¬ p ∣ (n : ℕ) := by
        push_neg at hcover
        exact hcover
      have hzero :
          (∑ f ∈ choices,
            if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro f hf
        obtain ⟨i, hi⟩ := hmissing
        have hfi : f i ∈ primeBand x (a i) := by
          exact Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
        have hnot : ¬ f i ∣ (n : ℕ) := hi (f i) hfi
        have hnotAll : ¬ ∀ i : Fin K, f i ∣ (n : ℕ) := by
          intro hall
          exact hnot (hall i)
        simp [hnotAll]
      rw [markedWeight, if_neg hcover]
      simp [hzero, qOmegaConst]
  have hhalfOmegaSummable : Summable
      (fun n : Nat.factoredNumbers S => halfOmegaTerm n) :=
    (hasSum_halfOmega_factoredNumbers (S := S) hSprime).1
  have hhalfOmegaNonneg (n : Nat.factoredNumbers S) : 0 ≤ halfOmegaTerm n := by
    have hn : (n : ℕ) ≠ 0 := n.property.1
    simp [halfOmegaTerm, hn]
    positivity
  have hselectedSummable (f : Fin K → ℕ) (hf : f ∈ choices) :
      Summable (fun n : Nat.factoredNumbers S =>
        if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) := by
    apply Summable.of_nonneg_of_le
      (fun n => by
        by_cases hall : ∀ i : Fin K, f i ∣ (n : ℕ)
        · simpa only [if_pos hall] using hhalfOmegaNonneg n
        · simp [hall])
      (fun n => by
        by_cases hall : ∀ i : Fin K, f i ∣ (n : ℕ)
        · simp [hall]
        · simpa [hall] using hhalfOmegaNonneg n)
      hhalfOmegaSummable
  have hchoiceDsubset (f : Fin K → ℕ) (hf : f ∈ choices) :
      Finset.univ.image f ⊆ S := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    have hfi : f i ∈ primeBand x (a i) :=
      Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
    change f i ∈ markedPrimes x K a
    simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hfi⟩
  have hselectedSeries (f : Fin K → ℕ) (hf : f ∈ choices) :
      (∑' n : Nat.factoredNumbers S,
        if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) =
        ∑ E ∈ (Finset.univ.image f).powerset,
          (-1 : ℝ) ^ E.card *
            ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
    let Df := Finset.univ.image f
    have hDsub : Df ⊆ S := hchoiceDsubset f hf
    have hcondition (n : Nat.factoredNumbers S) :
        (∀ i : Fin K, f i ∣ (n : ℕ)) ↔ Df ⊆ (n : ℕ).primeFactors := by
      constructor
      · intro hall p hp
        rcases Finset.mem_image.mp hp with ⟨i, hi, hpi⟩
        rw [← hpi]
        exact (Nat.mem_primeFactors_of_ne_zero n.property.1).mpr
          ⟨hchoicePrime f (by simpa [choices] using hf) i, hall i⟩
      · intro hsub i
        have hmem : f i ∈ Df := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        have hprimeFactor := hsub hmem
        exact (Nat.mem_primeFactors_of_ne_zero n.property.1).mp hprimeFactor |>.2
    calc
      (∑' n : Nat.factoredNumbers S,
          if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0) =
          ∑' n : Nat.factoredNumbers S,
            if Df ⊆ (n : ℕ).primeFactors then halfOmegaTerm n else 0 := by
              apply tsum_congr
              intro n
              by_cases h : ∀ i : Fin K, f i ∣ (n : ℕ)
              · have h' := (hcondition n).mp h
                simp [h, h']
              · have h' : ¬ Df ⊆ (n : ℕ).primeFactors := by
                  intro hs
                  exact h ((hcondition n).mpr hs)
                simp [h, h']
      _ = ∑ E ∈ Df.powerset,
          (-1 : ℝ) ^ E.card *
            ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) :=
              tsum_halfOmega_selected hDsub hSprime
  have hEulerExpanded : groupHarmonicMass x K a =
      qOmegaConst * ∑ f ∈ choices,
        ∑ E ∈ (Finset.univ.image f).powerset,
          (-1 : ℝ) ^ E.card *
            ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
    rw [hJ0rep]
    calc
      (∑' n : Nat.factoredNumbers S,
          markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ)) =
          ∑' n : Nat.factoredNumbers S,
            qOmegaConst *
              ∑ f ∈ choices,
                if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0 := by
                  apply tsum_congr
                  exact hpointWeight
      _ = qOmegaConst *
            ∑' n : Nat.factoredNumbers S,
              ∑ f ∈ choices,
                if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0 :=
              tsum_mul_left
      _ = qOmegaConst *
            ∑ f ∈ choices,
              ∑' n : Nat.factoredNumbers S,
                if ∀ i : Fin K, f i ∣ (n : ℕ) then halfOmegaTerm n else 0 := by
              congr 1
              rw [Summable.tsum_finsetSum]
              intro f hf
              exact hselectedSummable f hf
      _ = qOmegaConst *
            ∑ f ∈ choices,
              ∑ E ∈ (Finset.univ.image f).powerset,
                (-1 : ℝ) ^ E.card *
                  ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro f hf
              exact hselectedSeries f hf
  have hEulerProductForm : groupHarmonicMass x K a =
      qOmegaConst * ∑ f ∈ choices,
        (∏ p ∈ Finset.univ.image f, (1 / 2 : ℝ) / ((p : ℝ) - 1)) *
          ∏ p ∈ S \ Finset.univ.image f,
            (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
    rw [hEulerExpanded]
    congr 1
    apply Finset.sum_congr rfl
    intro f hf
    exact halfOmega_selected_product_identity (hchoiceDsubset f hf)
  have hchoiceCoordInjective (f : Fin K → ℕ) (hf : f ∈ choices) :
      Function.Injective f := by
    intro i j hij
    by_contra hne
    have hfi : f i ∈ primeBand x (a i) :=
      Fintype.mem_piFinset.mp (by simpa [choices] using hf) i
    have hfj : f j ∈ primeBand x (a j) :=
      Fintype.mem_piFinset.mp (by simpa [choices] using hf) j
    have hdisj := hBands i j hne
    have hfi' : f i ∈ primeBand x (a j) := by rw [hij]; exact hfj
    exact (Finset.disjoint_left.mp hdisj) hfi hfi'
  have hchoiceComplement (f : Fin K → ℕ) (hf : f ∈ choices) :
      S \ Finset.univ.image f =
        Finset.univ.biUnion (fun i : Fin K => (primeBand x (a i)).erase (f i)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_sdiff.mp hp with ⟨hpS, hpnot⟩
      have hpUnion : p ∈ Finset.univ.biUnion (fun i : Fin K => primeBand x (a i)) := by
        simpa [S, markedPrimes] using hpS
      rcases Finset.mem_biUnion.mp hpUnion with ⟨i, hi, hpi⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, Finset.mem_erase.mpr ⟨?_, hpi⟩⟩
      intro hEq
      apply hpnot
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hEq.symm⟩
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
      rcases Finset.mem_erase.mp hpi with ⟨hneq, hband⟩
      have hpS : p ∈ S := by
        change p ∈ markedPrimes x K a
        simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hband⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hpS, ?_⟩
      intro hpImage
      rcases Finset.mem_image.mp hpImage with ⟨j, hj, hjEq⟩
      have hfj : f j ∈ primeBand x (a j) :=
        Fintype.mem_piFinset.mp (by simpa [choices] using hf) j
      have hpj : f j ∈ primeBand x (a i) := by rw [hjEq]; exact hband
      by_cases hji : j = i
      · subst j
        exact hneq hjEq.symm
      · have hdisj := hBands i j (Ne.symm hji)
        exact (Finset.disjoint_left.mp hdisj) hpj hfj
  have hchoicePairwiseErase (f : Fin K → ℕ) (hf : f ∈ choices) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
        (fun i => (primeBand x (a i)).erase (f i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    exact (Finset.disjoint_left.mp (hBands i j hij))
      (Finset.mem_erase.mp hpi).2 (Finset.mem_erase.mp hpj).2
  have hselectedProduct (f : Fin K → ℕ) (hf : f ∈ choices) :
      (∏ p ∈ Finset.univ.image f, (1 / 2 : ℝ) / ((p : ℝ) - 1)) *
        ∏ p ∈ S \ Finset.univ.image f,
          (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) =
        ∏ i : Fin K,
          ((1 / 2 : ℝ) / ((f i : ℝ) - 1)) *
            ∏ p ∈ (primeBand x (a i)).erase (f i),
              (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
    have hprodD :
        (∏ p ∈ Finset.univ.image f, (1 / 2 : ℝ) / ((p : ℝ) - 1)) =
          ∏ i : Fin K, (1 / 2 : ℝ) / ((f i : ℝ) - 1) := by
      apply Finset.prod_image
      intro i hi j hj heq
      exact hchoiceCoordInjective f hf heq
    have hprodComp :
        (∏ p ∈ S \ Finset.univ.image f,
          (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1))) =
          ∏ i : Fin K,
            ∏ p ∈ (primeBand x (a i)).erase (f i),
              (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
      rw [hchoiceComplement f hf, Finset.prod_biUnion (hchoicePairwiseErase f hf)]
    rw [hprodD, hprodComp, ← Finset.prod_mul_distrib]
  have hEulerFactorDeriv (i : Fin K) :
      deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) =
        ∑ p ∈ primeBand x (a i),
          (∏ q ∈ (primeBand x (a i)).erase p,
            (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1))) *
              (1 / ((p : ℝ) - 1)) := by
    have hfactor (p : ℕ) : HasDerivAt
        (fun t : ℝ => 1 + t / ((p : ℝ) - 1))
        (1 / ((p : ℝ) - 1)) (1 / 2) := by
      simpa [div_eq_mul_inv] using
        ((hasDerivAt_id (1 / 2 : ℝ)).div_const ((p : ℝ) - 1)).const_add 1
    have hdiff : ∀ p ∈ primeBand x (a i),
        DifferentiableAt ℝ (fun t : ℝ => 1 + t / ((p : ℝ) - 1)) (1 / 2) := by
      intro p hp
      exact (hfactor p).differentiableAt
    unfold markedEulerFactor
    rw [deriv_fun_finsetProd hdiff]
    apply Finset.sum_congr rfl
    intro p hp
    simp [smul_eq_mul, hfactor p |>.deriv]
  have hlocalTupleSum :
      (∑ f ∈ choices,
        ∏ i : Fin K,
          ((1 / 2 : ℝ) / ((f i : ℝ) - 1)) *
            ∏ p ∈ (primeBand x (a i)).erase (f i),
              (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1))) =
        ∏ i : Fin K,
          (1 / 2 : ℝ) * deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) := by
    calc
      _ = ∏ i : Fin K,
            ∑ p ∈ primeBand x (a i),
              ((1 / 2 : ℝ) / ((p : ℝ) - 1)) *
                ∏ q ∈ (primeBand x (a i)).erase p,
                  (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1)) := by
              symm
              simpa [choices] using
                (Finset.prod_univ_sum
                  (fun i : Fin K => primeBand x (a i))
                  (fun i p => ((1 / 2 : ℝ) / ((p : ℝ) - 1)) *
                    ∏ q ∈ (primeBand x (a i)).erase p,
                      (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1))))
      _ = ∏ i : Fin K,
            (1 / 2 : ℝ) * deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [hEulerFactorDeriv i]
              calc
                (∑ p ∈ primeBand x (a i),
                    (1 / 2 : ℝ) / ((p : ℝ) - 1) *
                      ∏ q ∈ (primeBand x (a i)).erase p,
                        (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1))) =
                    ∑ p ∈ primeBand x (a i), (1 / 2 : ℝ) *
                      ((∏ q ∈ (primeBand x (a i)).erase p,
                          (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1))) *
                        (1 / ((p : ℝ) - 1))) := by
                          apply Finset.sum_congr rfl
                          intro p hp
                          ring
                _ = (1 / 2 : ℝ) *
                      ∑ p ∈ primeBand x (a i),
                        (∏ q ∈ (primeBand x (a i)).erase p,
                            (1 + (1 / 2 : ℝ) / ((q : ℝ) - 1))) *
                          (1 / ((p : ℝ) - 1)) := by
                            rw [← Finset.mul_sum]
  have hEulerIdentity : groupHarmonicMass x K a =
      ∏ i : Fin K,
        deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) /
          bandMass x (a i) := by
    rw [hEulerProductForm]
    calc
      qOmegaConst *
          ∑ f ∈ choices,
            (∏ p ∈ Finset.univ.image f, (1 / 2 : ℝ) / ((p : ℝ) - 1)) *
              ∏ p ∈ S \ Finset.univ.image f,
                (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) =
          qOmegaConst * ∑ f ∈ choices,
            ∏ i : Fin K,
              ((1 / 2 : ℝ) / ((f i : ℝ) - 1)) *
                ∏ p ∈ (primeBand x (a i)).erase (f i),
                  (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
            apply congrArg
            apply Finset.sum_congr rfl
            intro f hf
            exact hselectedProduct f hf
      _ = qOmegaConst *
            ∏ i : Fin K,
              (1 / 2 : ℝ) * deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) := by
            rw [hlocalTupleSum]
      _ = ∏ i : Fin K,
            deriv (fun t => markedEulerFactor x (a i) t) (1 / 2) /
              bandMass x (a i) := by
            dsimp [qOmegaConst, Vprod]
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            field_simp [ne_of_gt hVprodPos]
            rw [← mul_pow]
            norm_num
  constructor
  · exact hEulerIdentity
  · refine ⟨hJlower, ?_, ?_, ?_, ?_⟩
    · exact hJupper.trans (le_max_right _ _)
    · intro ε hε
      refine ⟨Cshift, x₀, hCshift, hx₀2, ?_⟩
      intro y hy R
      exact hTailAt ε hε y hy R
    · intro ε hε
      refine ⟨3 * Cshift, x₀, by positivity, hx₀2, ?_⟩
      intro y hy
      let R := ⌊2 * y⌋₊
      let T := (Finset.range (R + 1)).filter
        (fun r => IsGroupInteger y K a r ∧ Real.rpow y ε < (r : ℝ))
      have hyPos : 0 < y := by linarith [hx₀2, hy]
      have hy4 : 4 ≤ y := by
        have hy0 : x₀ ≤ y := hy
        exact hx₀4.trans hy0
      have hlogY : (4 : ℝ) ^ 10 ≤ Real.log y := by
        have hyScale : Xscale ≤ y := le_trans (le_max_left _ _) hy
        have hlog := Real.log_le_log (Real.exp_pos _) hyScale
        have hbig : (100 : ℝ) ^ 10 ≤ Real.log y := by
          simpa [Xscale, Real.log_exp] using hlog
        have hsmall : (4 : ℝ) ^ 10 ≤ (100 : ℝ) ^ 10 := by norm_num
        exact hsmall.trans hbig
      have hmassLowerY : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass y (a i) := by
        have hyLower : Xlower ≤ y :=
          (le_trans (le_max_left Xlower (max Xupper Xdisj)) (le_max_right Xscale _)).trans hy
        exact hmassLower y hyLower
      have hsum : (∑ r ∈ T,
          markedWeight y K a (1 / 2 : ℝ) r *
            progressionPrimeSum y M c u Ψ r 1) ≤
          3 * y * (∑ r ∈ T,
            markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) := by
        calc
          (∑ r ∈ T,
              markedWeight y K a (1 / 2 : ℝ) r *
                progressionPrimeSum y M c u Ψ r 1) ≤
              ∑ r ∈ T,
                markedWeight y K a (1 / 2 : ℝ) r * (3 * y / (r : ℝ)) := by
                  apply Finset.sum_le_sum
                  intro r hr
                  have hmem := Finset.mem_filter.mp hr
                  have hcount := progressionPrimeSum_trivial_bound y M c u Ψ K a r hc ha hΨ
                    (by linarith [hlogY]) hy4 hmem.2.1
                  exact mul_le_mul_of_nonneg_left hcount
                    (markedWeight_nonneg_le (x := y) (K := K) (a := a) (h := r)
                      hmassLowerY).1
          _ = 3 * y * (∑ r ∈ T,
                markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) := by
                  calc
                    _ = ∑ r ∈ T,
                          (3 * y) *
                            (markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) := by
                              apply Finset.sum_congr rfl
                              intro r hr
                              ring
                    _ = 3 * y * (∑ r ∈ T,
                          markedWeight y K a (1 / 2 : ℝ) r / (r : ℝ)) := by
                              rw [← Finset.mul_sum]
      have htail := hTailAt ε hε y hy R
      calc
        (∑ r ∈ T,
            markedWeight y K a (1 / 2 : ℝ) r *
              progressionPrimeSum y M c u Ψ r 1) ≤
            3 * y * (Cshift * Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax))) :=
              hsum.trans (mul_le_mul_of_nonneg_left htail (by positivity))
        _ = (3 * Cshift) * y * Real.exp (-ε * Real.rpow (Real.log y) (1 - aMax)) := by ring
    · intro r hr
      have hcount := progressionPrimeSum_trivial_bound x M c u Ψ K a r hc ha hΨ hL hx4 hr
      have h3 : (3 : ℝ) ≤ C := le_max_left _ _
      have hratio : 0 ≤ x / (r : ℝ) := div_nonneg hxpos.le (Nat.cast_nonneg r)
      calc
        progressionPrimeSum x M c u Ψ r 1 ≤ 3 * x / (r : ℝ) := hcount
        _ = 3 * (x / (r : ℝ)) := by ring
        _ ≤ C * (x / (r : ℝ)) := mul_le_mul_of_nonneg_right h3 hratio
        _ = C * x / (r : ℝ) := by ring

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
  sorry

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
  refine ⟨singularProduct_pos M, progressionSieveProduct_relative M hM, ?_⟩
  intro K a ha
  obtain ⟨xCorr, hxCorr, hCorr⟩ := progressionSieveProductFor_relative M K a ha
  let xScale := Real.exp ((4 : ℝ) ^ 10)
  let x₀ := max xCorr xScale
  have hxScale : 2 ≤ xScale := by
    have htwo : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    exact htwo.trans (Real.exp_le_exp.mpr (by norm_num))
  have hx₀ : 2 ≤ x₀ := le_trans hxCorr (le_max_left _ _)
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx r hr hrbound
  have hxScaleX : xScale ≤ x := le_trans (le_max_right _ _) hx
  have hxCorrX : xCorr ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxScaleX
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hxScaleX
    simpa [xScale, Real.log_exp] using hlog
  refine ⟨groupPrimeReciprocal_sum_bound hxpos hL ha hr hrbound, ?_⟩
  intro y hy
  exact hCorr x hxCorrX r hr hrbound y hy

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

/-- `co:bin-cost`, 12-construction.tex:505-561. Correction 8 from review lane `rev-b` requires
the fixed progression assumptions from §12. -/
theorem bin_cost (M c : ℕ) (u : ℤ) (κ b : ℝ)
    (hM : 0 < M) (h8 : 8 ∣ M) (hc24 : c = 2 ∨ c = 4) (hcM : c ∣ M)
    (hu : Int.gcd u M = 1) (hcu : (c : ℤ) ∣ u - 1)
    (hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1)
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

set_option maxHeartbeats 1000000
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
  refine ⟨8, by norm_num, ?_⟩
  intro M c u K a Ψ hΨ κ hM h8 hc hcM hu hcu hcu' ha hκ₀ hκ₁
  obtain ⟨Bsup, xSup, hBsup, hxSup, hSupport⟩ :=
    support M c u K a Ψ hM hc ha hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1
  let Xscale := Real.exp ((4 : ℝ) ^ 10)
  let x₀ := max xSup Xscale
  have hXscale : 2 ≤ Xscale := by
    have h2 : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    exact h2.trans (Real.exp_le_exp.mpr (by norm_num))
  have hx₀ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_of_le_right hXscale
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  have hxSupx : xSup ≤ x := le_trans (le_max_left _ _) hx
  have hXscalex : Xscale ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hXscalex
  have hxone : 1 ≤ x := by linarith [hx₀, hx]
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hXscalex
    simpa [Xscale, Real.log_exp] using hlog
  have hSupportx := hSupport x hxSupx
  have hW : 0 < Real.rpow x (1 / 2 - κ) := Real.rpow_pos_of_pos hxpos _
  have hWcube : 2 * x < Real.rpow x (1 / 2 - κ) ^ 3 :=
    rough_cutoff_cube_gt hxpos hL hκ₁
  let L := Real.log x
  let I := ⌊4 * κ * L⌋₊ + 4
  let N := 2 * I
  let Hlow := Real.rpow x (46 / 100 : ℝ) / 2
  let Hhigh := Real.rpow x (54 / 100 : ℝ)
  let Hbase := Real.rpow x (1 / 2 - κ) / 2
  let rawH₁ (j : ℕ) := Hbase * (2 : ℝ) ^ j
  let H₁ : Fin N → ℝ := fun k =>
    max Hlow (min (rawH₁ (k.val / 2)) Hhigh)
  let H₂ : Fin N → ℝ := fun k =>
    x / (2 * H₁ k) * (2 : ℝ) ^ (k.val % 2)
  have hfloorL : (⌊4 * κ * L⌋₊ : ℝ) ≤ 4 * κ * L :=
    Nat.floor_le (by positivity)
  have hNbound : (N : ℝ) ≤ 8 * (κ * L + 1) := by
    dsimp [N, I]
    push_cast
    nlinarith [hfloorL]
  have hwidthExp : 2 ≤ Real.rpow x (3 / 100 : ℝ) := by
    have harg : 1 ≤ (3 / 100 : ℝ) * L := by
      have hLlarge : (3 : ℝ) ≤ (3 / 100 : ℝ) * L := by nlinarith [hL]
      linarith
    have hExp : Real.exp 1 ≤ Real.exp ((3 / 100 : ℝ) * L) := Real.exp_le_exp.mpr harg
    have htwo : 2 ≤ Real.exp 1 := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    have hpow : Real.rpow x (3 / 100 : ℝ) = Real.exp ((3 / 100 : ℝ) * L) := by
      simpa [L, mul_comm] using Real.rpow_def_of_pos hxpos (3 / 100 : ℝ)
    rw [hpow]
    exact htwo.trans hExp
  have hwidth : 2 * Real.rpow x (51 / 100 : ℝ) ≤ Hhigh := by
    have hexp : Real.rpow x (51 / 100 : ℝ) * Real.rpow x (3 / 100 : ℝ) = Hhigh := by
      dsimp [Hhigh]
      calc
        _ = Real.rpow x ((51 / 100 : ℝ) + 3 / 100) :=
          (Real.rpow_add hxpos _ _).symm
        _ = Real.rpow x (54 / 100 : ℝ) := by congr 1 <;> norm_num
    have hpowNonneg : 0 ≤ Real.rpow x (51 / 100 : ℝ) := (Real.rpow_pos_of_pos hxpos _).le
    calc
      2 * Real.rpow x (51 / 100 : ℝ) ≤
          Real.rpow x (3 / 100 : ℝ) * Real.rpow x (51 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_right hwidthExp hpowNonneg
      _ = Hhigh := by rw [mul_comm, hexp]
  have hwidthPow : Real.rpow x (1 / 2 + κ) *
      Real.rpow x (1 / 2 - κ) = x := by
    calc
      _ = Real.rpow x ((1 / 2 + κ) + (1 / 2 - κ)) :=
        (Real.rpow_add (x := x) hxpos (1 / 2 + κ) (1 / 2 - κ)).symm
      _ = Real.rpow x 1 := by congr 1 <;> ring
      _ = x := by simp [Real.rpow_one]
  have hratio : x / Real.rpow x (1 / 2 - κ) = Real.rpow x (1 / 2 + κ) := by
    exact (div_eq_iff (ne_of_gt hW)).2 hwidthPow.symm
  have hwidthExponent : 1 / 2 + κ < (51 / 100 : ℝ) := by linarith [hκ₁]
  have hwidth45 : Real.rpow x (46 / 100 : ℝ) ≤ Real.rpow x (49 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hscaleBase : Hlow ≤ Hbase := by
    dsimp [Hlow, Hbase]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hxone (by linarith)) (by norm_num)
  have hlowpos : 0 < Hlow := by dsimp [Hlow]; positivity
  have hhighpos : 0 < Hhigh := by dsimp [Hhigh]; positivity
  have hdenLowPos : 0 < 2 * Hlow := mul_pos (by norm_num) hlowpos
  have hdenHighPos : 0 < 2 * Hhigh := mul_pos (by norm_num) hhighpos
  have hHlowHigh : Hlow ≤ Hhigh := by
    dsimp [Hlow, Hhigh]
    exact (div_le_self (Real.rpow_nonneg (by linarith [hxone]) _) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num))
  have hH₁bounds : ∀ k : Fin N, Hlow ≤ H₁ k ∧ H₁ k ≤ Hhigh := by
    intro k
    dsimp [H₁]
    exact ⟨le_max_left _ _, max_le hHlowHigh (min_le_right _ _)⟩
  have hrem (k : Fin N) :
      (1 : ℝ) ≤ (2 : ℝ) ^ (k.val % 2) ∧ (2 : ℝ) ^ (k.val % 2) ≤ 2 := by
    have hb : k.val % 2 = 0 ∨ k.val % 2 = 1 := by omega
    rcases hb with hb | hb <;> simp [hb]
  have hH₂bounds : ∀ k : Fin N,
      Hlow ≤ H₂ k ∧ H₂ k ≤ 2 * Hhigh := by
    intro k
    have h₁ := hH₁bounds k
    have h₁pos : 0 < H₁ k := lt_of_lt_of_le hlowpos h₁.1
    have hDen : 2 * H₁ k ≤ 2 * Hhigh := mul_le_mul_of_nonneg_left h₁.2 (by norm_num)
    have hDen' : 2 * Hlow ≤ 2 * H₁ k := mul_le_mul_of_nonneg_left h₁.1 (by norm_num)
    have hrecipLo : 1 / (2 * Hhigh) ≤ 1 / (2 * H₁ k) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) h₁pos) hDen
    have hrecipHi : 1 / (2 * H₁ k) ≤ 1 / (2 * Hlow) :=
      one_div_le_one_div_of_le hdenLowPos hDen'
    have hbaseLo : x / (2 * Hhigh) = Hlow := by
      have hmix : Real.rpow x (46 / 100 : ℝ) * Real.rpow x (54 / 100 : ℝ) = x := by
        calc
          _ = Real.rpow x ((46 / 100 : ℝ) + 54 / 100) :=
            (Real.rpow_add hxpos _ _).symm
          _ = Real.rpow x 1 := by congr 1 <;> norm_num
          _ = x := by simp [Real.rpow_one]
      dsimp [Hlow, Hhigh]
      have hpos54 : 0 < Real.rpow x (54 / 100 : ℝ) := Real.rpow_pos_of_pos hxpos _
      apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) hpos54))).2
      calc
        x = Real.rpow x (46 / 100 : ℝ) * Real.rpow x (54 / 100 : ℝ) := hmix.symm
        _ = (Real.rpow x (46 / 100 : ℝ) / 2) *
              (2 * Real.rpow x (54 / 100 : ℝ)) := by field_simp
    have hbaseHi : x / (2 * Hlow) = Hhigh := by
      have hmix : Real.rpow x (46 / 100 : ℝ) * Real.rpow x (54 / 100 : ℝ) = x := by
        calc
          _ = Real.rpow x ((46 / 100 : ℝ) + 54 / 100) :=
            (Real.rpow_add hxpos _ _).symm
          _ = Real.rpow x 1 := by congr 1 <;> norm_num
          _ = x := by simp [Real.rpow_one]
      dsimp [Hlow, Hhigh]
      have hpos46 : 0 < Real.rpow x (46 / 100 : ℝ) := Real.rpow_pos_of_pos hxpos _
      apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num)
        (div_pos hpos46 (by norm_num : (0 : ℝ) < 2))))).2
      calc
        x = Real.rpow x (46 / 100 : ℝ) * Real.rpow x (54 / 100 : ℝ) := hmix.symm
        _ = Real.rpow x (54 / 100 : ℝ) *
              (2 * (Real.rpow x (46 / 100 : ℝ) / 2)) := by field_simp
    have hbasePos : 0 ≤ x / (2 * H₁ k) :=
      (div_pos hxpos (mul_pos (by norm_num) h₁pos)).le
    constructor
    · calc
        Hlow = x / (2 * Hhigh) := hbaseLo.symm
        _ ≤ x / (2 * H₁ k) := by
          calc
            _ = x * (1 / (2 * Hhigh)) := by ring
            _ ≤ x * (1 / (2 * H₁ k)) := mul_le_mul_of_nonneg_left hrecipLo hxpos.le
            _ = _ := by ring
        _ ≤ H₂ k := by
          dsimp [H₂]
          calc
            _ = x / (2 * H₁ k) * 1 := by ring
            _ ≤ x / (2 * H₁ k) * (2 : ℝ) ^ (k.val % 2) :=
              mul_le_mul_of_nonneg_left (hrem k).1 hbasePos
    · calc
        H₂ k = x / (2 * H₁ k) * (2 : ℝ) ^ (k.val % 2) := by rfl
        _ ≤ x / (2 * H₁ k) * 2 :=
          mul_le_mul_of_nonneg_left (hrem k).2 hbasePos
        _ ≤ 2 * Hhigh := by
          calc
            _ = (x / (2 * H₁ k)) * 2 := by rfl
            _ ≤ (x / (2 * Hlow)) * 2 := by
              apply mul_le_mul_of_nonneg_right _ (by norm_num)
              calc
                _ = x * (1 / (2 * H₁ k)) := by ring
                _ ≤ x * (1 / (2 * Hlow)) := mul_le_mul_of_nonneg_left hrecipHi hxpos.le
                _ = _ := by ring
            _ = 2 * Hhigh := by rw [hbaseHi]; ring
  have hboxes : ∀ k : Fin N,
      x / 4 ≤ H₁ k * H₂ k ∧ H₁ k * H₂ k ≤ 2 * x ∧
        Hlow ≤ H₁ k ∧ H₁ k ≤ 2 * Hhigh ∧ Hlow ≤ H₂ k ∧ H₂ k ≤ 2 * Hhigh := by
    intro k
    have hremk := hrem k
    have hprod : H₁ k * H₂ k = x / 2 * (2 : ℝ) ^ (k.val % 2) := by
      dsimp [H₂]
      have h1pos : H₁ k ≠ 0 := ne_of_gt (lt_of_lt_of_le hlowpos (hH₁bounds k).1)
      field_simp [h1pos]
    have hprodLo : x / 2 ≤ H₁ k * H₂ k := by
      rw [hprod]
      calc
        x / 2 = x / 2 * 1 := by ring
        _ ≤ x / 2 * (2 : ℝ) ^ (k.val % 2) :=
          mul_le_mul_of_nonneg_left hremk.1 (by positivity)
    have hprodHi : H₁ k * H₂ k ≤ x := by
      rw [hprod]
      calc
        x / 2 * (2 : ℝ) ^ (k.val % 2) ≤ x / 2 * 2 :=
          mul_le_mul_of_nonneg_left hremk.2 (by positivity)
        _ = x := by ring
    have h1 := hH₁bounds k
    have h2 := hH₂bounds k
    refine ⟨?_, le_trans hprodHi (by linarith), h1.1, ?_, h2.1, ?_⟩
    · linarith
    · exact le_trans h1.2 (by nlinarith [hhighpos])
    · exact le_trans h2.2 (by linarith)
  refine ⟨N, hNbound, H₁, H₂, ?_, ?_⟩
  · intro k
    have hk := hboxes k
    simpa [Hlow, Hhigh] using hk
  · intro d hweight hrough hdnot
    have hinterval : x < (d : ℝ) ∧ (d : ℝ) < 2 * x := by
      rcases (hSupportx.2.1 d (ne_of_gt hweight)) with ⟨hlo, hhi, _⟩
      exact ⟨hlo, hhi⟩
    have hroughP : ∀ p, p.Prime → p ∣ d → Real.rpow x (1 / 2 - κ) < (p : ℝ) :=
      fun p hp hpd => hrough p hp hpd
    obtain ⟨m, n, hm, hn, hmn, hmW, hnW⟩ :=
      exists_rough_semiprime_factorization (show 1 < x by linarith) hinterval.1 hinterval.2
        hroughP hdnot hW hWcube
    have hmnReal : (d : ℝ) = (m : ℝ) * (n : ℝ) := by exact_mod_cast hmn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.pos
    have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm.pos
    have hmUpperDiv : (m : ℝ) < 2 * x / (n : ℝ) :=
      (lt_div_iff₀ hnpos).2 (by simpa [hmnReal] using hinterval.2)
    have hnUpperDiv : (n : ℝ) < 2 * x / (m : ℝ) := by
      have hprod : (m : ℝ) * (n : ℝ) < 2 * x := by simpa [hmnReal] using hinterval.2
      exact (lt_div_iff₀ hmpos).2 (by simpa [mul_comm] using hprod)
    have hmRecip : 1 / (n : ℝ) ≤ 1 / Real.rpow x (1 / 2 - κ) :=
      one_div_le_one_div_of_le hW hnW.le
    have hnRecip : 1 / (m : ℝ) ≤ 1 / Real.rpow x (1 / 2 - κ) :=
      one_div_le_one_div_of_le hW hmW.le
    have hmUpper : (m : ℝ) < 2 * Real.rpow x (1 / 2 + κ) := by
      calc
        _ < 2 * x / (n : ℝ) := hmUpperDiv
        _ ≤ 2 * x / Real.rpow x (1 / 2 - κ) := by
          calc
            _ = 2 * x * (1 / (n : ℝ)) := by ring
            _ ≤ 2 * x * (1 / Real.rpow x (1 / 2 - κ)) :=
              mul_le_mul_of_nonneg_left hmRecip (by positivity)
            _ = _ := by ring
        _ = _ := by
          calc
            2 * x / Real.rpow x (1 / 2 - κ) =
                2 * (x / Real.rpow x (1 / 2 - κ)) := by ring
            _ = 2 * Real.rpow x (1 / 2 + κ) := by rw [hratio]
    have hnUpper : (n : ℝ) < 2 * Real.rpow x (1 / 2 + κ) := by
      calc
        _ < 2 * x / (m : ℝ) := hnUpperDiv
        _ ≤ 2 * x / Real.rpow x (1 / 2 - κ) := by
          calc
            _ = 2 * x * (1 / (m : ℝ)) := by ring
            _ ≤ 2 * x * (1 / Real.rpow x (1 / 2 - κ)) :=
              mul_le_mul_of_nonneg_left hnRecip (by positivity)
            _ = _ := by ring
        _ = _ := by
          calc
            2 * x / Real.rpow x (1 / 2 - κ) =
                2 * (x / Real.rpow x (1 / 2 - κ)) := by ring
            _ = 2 * Real.rpow x (1 / 2 + κ) := by rw [hratio]
    obtain ⟨j, hjI, hjlow, hjhigh⟩ :=
      exists_dyadic_scale_index hxpos hL hκ₀ hκ₁ hmW hmUpper
    have hbaseLow : Hlow ≤ rawH₁ j := by
      have h46_49 : Real.rpow x (46 / 100 : ℝ) ≤
          Real.rpow x (49 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
      have h49_α : Real.rpow x (49 / 100 : ℝ) ≤
          Real.rpow x (1 / 2 - κ) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith [hκ₁])
      have hpowj : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hbaseNonneg : 0 ≤ Real.rpow x (1 / 2 - κ) / 2 := by
        have hrpow : 0 ≤ Real.rpow x (1 / 2 - κ) := by positivity
        exact div_nonneg hrpow (by norm_num)
      dsimp [Hlow, rawH₁, Hbase]
      calc
        Real.rpow x (46 / 100 : ℝ) / 2 ≤ Real.rpow x (1 / 2 - κ) / 2 :=
          div_le_div_of_nonneg_right (h46_49.trans h49_α) (by norm_num)
        _ ≤ Real.rpow x (1 / 2 - κ) / 2 * (2 : ℝ) ^ j := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowj hbaseNonneg
    have hbaseHigh : rawH₁ j ≤ Hhigh := by
      exact (calc
        rawH₁ j ≤ (m : ℝ) := hjlow
        _ < 2 * Real.rpow x (1 / 2 + κ) := hmUpper
        _ ≤ 2 * Real.rpow x (51 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hxone hwidthExponent.le) (by norm_num)
        _ ≤ Hhigh := hwidth).le
    let b : ℕ := if (n : ℝ) < 2 * (x / (2 * rawH₁ j)) then 0 else 1
    let kval : ℕ := 2 * j + b
    have hbLt : b < 2 := by dsimp [b]; split_ifs <;> omega
    have hjI' : j < I := by simpa [I] using hjI
    have hkvalLt : kval < N := by
      change 2 * j + b < 2 * I
      omega
    let k : Fin N := ⟨kval, hkvalLt⟩
    have hkdiv : k.val / 2 = j := by dsimp [k, kval]; omega
    have hkrem : k.val % 2 = b := by dsimp [k, kval]; omega
    have hH₁sel : H₁ k = rawH₁ j := by
      dsimp [H₁]
      rw [hkdiv]
      simp [min_eq_left hbaseHigh, max_eq_right hbaseLow]
    have hH₂sel : H₂ k = x / (2 * rawH₁ j) * (2 : ℝ) ^ b := by
      dsimp [H₂]
      rw [hH₁sel, hkrem]
    have hrawPos : 0 < rawH₁ j := lt_of_lt_of_le hlowpos hbaseLow
    have hnBaseLo : x / (2 * rawH₁ j) < (n : ℝ) := by
      have hprodlo : x < (m : ℝ) * (n : ℝ) := by simpa [hmnReal] using hinterval.1
      have hmult : (m : ℝ) * (n : ℝ) < (2 * rawH₁ j) * (n : ℝ) :=
        mul_lt_mul_of_pos_right hjhigh hnpos
      apply (div_lt_iff₀ (mul_pos (by norm_num) hrawPos)).2
      calc
        x < (m : ℝ) * (n : ℝ) := hprodlo
        _ < (2 * rawH₁ j) * (n : ℝ) := hmult
        _ = (n : ℝ) * (2 * rawH₁ j) := by ring
    have hnBaseHi : (n : ℝ) < 4 * (x / (2 * rawH₁ j)) := by
      have hprodhi : (m : ℝ) * (n : ℝ) < 2 * x := by simpa [hmnReal] using hinterval.2
      have hrawProd : rawH₁ j * (n : ℝ) ≤ (m : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hjlow hnpos.le
      have hrawProdHi : rawH₁ j * (n : ℝ) < 2 * x :=
        lt_of_le_of_lt hrawProd hprodhi
      have hndiv : (n : ℝ) < 2 * x / rawH₁ j :=
        (lt_div_iff₀ hrawPos).2 (by simpa [mul_comm] using hrawProdHi)
      calc
        (n : ℝ) < 2 * x / rawH₁ j := hndiv
        _ = 4 * (x / (2 * rawH₁ j)) := by field_simp <;> norm_num
    have hnBox : H₂ k ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * H₂ k := by
      rw [hH₂sel]
      by_cases hmid : (n : ℝ) < 2 * (x / (2 * rawH₁ j))
      · have hb0 : b = 0 := by simp [b, hmid]
        rw [hb0]
        simp only [pow_zero, mul_one]
        exact ⟨hnBaseLo.le, hmid.le⟩
      · have hb1 : b = 1 := by simp [b, hmid]
        have hmid' : ¬ (n : ℝ) < (x / (2 * rawH₁ j)) * 2 := by
          simpa [mul_comm] using hmid
        rw [hb1]
        simp only [pow_one]
        exact ⟨le_of_not_gt hmid', (by nlinarith [hnBaseHi.le])⟩
    have hmBox : m ∈ dyadicIntegers (H₁ k) := by
      exact mem_dyadicIntegers_of_bounds (H := H₁ k)
        (by rw [hH₁sel]; exact hjlow) (by rw [hH₁sel]; exact hjhigh.le)
    have hnBox' : n ∈ dyadicIntegers (H₂ k) :=
      mem_dyadicIntegers_of_bounds hnBox.1 hnBox.2
    exact ⟨k, m, n, hmBox, hnBox', hm, hn, hmn⟩
set_option maxHeartbeats 200000
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

/-- The pair estimate supplied by `con_rough_pairs`, at its fixed leading constant. -/
def HasRoughPairBound (M : ℕ) (Ψ : ℝ → ℝ) (C₁ : ℝ) : Prop :=
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
                  roughSieveProduct (roughCutoff x) ^ 2

/-- The balanced box cover supplied by `balanced_boxes` at its fixed dyadic constant. -/
def HasBalancedBoxCover (Cdyad : ℝ) : Prop :=
  ∀ M c : ℕ, ∀ u : ℤ, ∀ K : ℕ, ∀ a : Fin K → ℝ,
    ∀ Ψ : ℝ → ℝ, IsTestFunction Ψ → ∀ κ : ℝ,
      0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
      Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
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
                    ∃ i m n, m ∈ dyadicIntegers (H₁ i) ∧
                      n ∈ dyadicIntegers (H₂ i) ∧ m.Prime ∧ n.Prime ∧ d = m * n)

/-- `co:balanced-cost`, 12-construction.tex:736-775. Correction from refutation lane `sol-gate-b`
ties `C₁` and `C_dyad` to their preceding estimates and includes `8 ∣ M`. -/
theorem balanced_cost (M : ℕ) (Ψ : ℝ → ℝ) (C₁ Cdyad : ℝ)
    (hM : 0 < M) (h8 : 8 ∣ M) (hΨ : IsTestFunction Ψ)
    (hC₁ : 0 < C₁) (hCdyad : 0 < Cdyad)
    (hPairs : HasRoughPairBound M Ψ C₁) (hCover : HasBalancedBoxCover Cdyad) :
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
