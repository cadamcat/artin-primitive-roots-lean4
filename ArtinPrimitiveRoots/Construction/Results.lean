import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c2.PartialSummation
import ArtinPrimitiveRoots.Construction.Proofs.C_BV.Mass
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c1.SieveProductHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c1.HarmonicHelpers
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.RoughDensity
import ArtinPrimitiveRoots.Construction.Proofs.c4.Density
import ArtinPrimitiveRoots.Construction.Proofs.c4.RoughRemoval
import ArtinPrimitiveRoots.Construction.Proofs.c4.TestFunction
import ArtinPrimitiveRoots.Construction.Proofs.c4.BalancedHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c4.RoughPairResidues
import ArtinPrimitiveRoots.Construction.Proofs.c4.PairBlock

/-! Statements for the prime construction in `12-construction.tex`. -/

namespace ArtinPrimitiveRoots.Construction

open Classical
open MeasureTheory
open Filter
open scoped Topology
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
      have hxparts : x₁ ≤ x ∧ xBV ≤ x := by
        dsimp [x_A] at hxA
        exact (max_le_iff.mp hxA)
      rcases hxparts with ⟨hx₁x, hxBVx⟩
      have hxHle : xH ≤ x := le_trans (le_max_left xH (max xMarks xExp))
        (le_trans (le_max_right 2 (max xH (max xMarks xExp))) hx₁x)
      have hJbounds := hHarm x hxHle
      have hJlowerX : 1 ≤ J₀ := by simpa [J₀] using hJbounds.2.1
      have hxExpX : Real.exp 1 ≤ x := by
        have hxExpLe : xExp ≤ x := le_trans (le_max_right xMarks xExp)
          (le_trans (le_max_right xH (max xMarks xExp))
            (le_trans (le_max_right 2 (max xH (max xMarks xExp))) hx₁x))
        have hX := hxExp x hxExpLe
        change Real.exp 1 ≤ Real.rpow x 1 at hX
        exact hX.trans_eq (Real.rpow_one x)
      have hlogx : 1 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxExpX
        simpa using h
      have hxpos : 0 < x := by linarith [hx₁x]
      have hxge1 : 1 ≤ x := le_trans (by norm_num : (1 : ℝ) ≤ 2)
        (hx₁.trans hx₁x)
      have hDpos : 0 < D := by dsimp [D]; positivity
      have hDone : 1 ≤ D := by
        have hb : 0 < 1 / 2 - κ / 2 := by nlinarith [hκ]
        have hle : Real.rpow (1 : ℝ) (1 / 2 - κ / 2) ≤ D := by
          dsimp [D]
          exact Real.rpow_le_rpow (by norm_num) hxge1 hb.le
        simpa using hle
      have hDleX : D ≤ x := by
        have hb : 1 / 2 - κ / 2 ≤ (1 : ℝ) := by nlinarith [hκ]
        dsimp [D]
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le hxge1 hb)
      have hlogD : Real.log D ≤ Real.log x :=
        Real.log_le_log hDpos hDleX
      have hharmonic : harmonic ⌊D⌋₊ ≤ 2 * Real.log x := by
        have h := harmonic_floor_le_one_add_log D hDone
        have hupper : 1 + Real.log D ≤ 2 * Real.log x := by linarith [hlogD, hlogx]
        exact le_trans h hupper
      have hDensitySum (r : ℕ) :
          (∑ ell ∈ Lset, localSieveDensity M r ell) ≤
            4 * Real.rpow (Real.log x) 4 := by
        have h := ArtinPrimitiveRoots.Construction.ProofsC2.localSieveDensity_sum_le M r D
        have hpow : Real.rpow (Real.log x) 2 ≤ Real.rpow (Real.log x) 4 :=
          Real.rpow_le_rpow_of_exponent_le hlogx (by norm_num)
        have hharmonicNonneg : 0 ≤ (harmonic ⌊D⌋₊ : ℝ) := by
          have hq : 0 ≤ harmonic ⌊D⌋₊ := by
            unfold harmonic
            apply Finset.sum_nonneg
            intro i hi
            positivity
          exact_mod_cast hq
        have hharmonicSq : (harmonic ⌊D⌋₊ : ℝ) ^ 2 ≤
            (2 * Real.log x) ^ 2 := by nlinarith [hharmonic, hharmonicNonneg]
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
            have := le_trans (le_max_left xMarks xExp)
              (le_trans (le_max_right xH (max xMarks xExp))
                (le_trans (le_max_right 2 (max xH (max xMarks xExp))) hx₁x))
            exact this
          have hh := hxMarks x hxM p hp
          exact lt_of_le_of_lt (by exact_mod_cast (Nat.le_max_right M 2)) hh
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
            · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _
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
            have hqGroup : IsGroupInteger x K a q := (Finset.mem_filter.mp hq).2
            simp [Hfun, hqGroup]
          _ ≤ ∑' q : ℕ, Hfun q := hsum
          _ = J₀ := by simp [Hfun, J₀, groupHarmonicMass]
      have hWeightNonneg (r : ℕ) :
          0 ≤ markedWeight x K a (1 / 2 : ℝ) r := by
        unfold markedWeight
        split_ifs
        · apply mul_nonneg
          · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _
          · apply Finset.prod_nonneg
            intro i hi
            apply div_nonneg (Nat.cast_nonneg _)
            unfold bandMass
            apply Finset.sum_nonneg
            intro p hp
            have hprime := (Finset.mem_filter.mp hp).2.1
            exact div_nonneg (by norm_num) (by exact_mod_cast hprime.pos.le)
        · simp
      have hLocalErr (r : ℕ) (hr : r ∈ R) :
          (∑ ell ∈ Lset,
            |progressionPrimeSum x M c u Ψ r ell -
              localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|) ≤
            5 * Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
        have hrGroup : IsGroupInteger x K a r := (Finset.mem_filter.mp hr).2
        have hrpos : 0 < r := hRpos r hr
        have hrFloor : r ≤ ⌊Real.rpow x ε⌋₊ :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
        have hrBound : (r : ℝ) ≤ Real.rpow x ε := by
          exact (Nat.cast_le.mpr hrFloor).trans
            (Nat.floor_le (Real.rpow_nonneg hxpos.le ε))
        have hBVr := hBV x hxBVx r hrGroup hrBound
        have hBVsum :
            (∑ ell ∈ Lset,
              |progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell *
                  smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ)|) ≤
              Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A') := by
          simpa [Lset, D] using hBVr
        let B : ℝ := smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ)
        let E : ℝ := Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A')
        have hOneL : 1 ∈ Lset := by
          have hDoneCast : ((1 : ℕ) : ℝ) ≤ D := by exact_mod_cast hDone
          have hOneFloor : 1 ≤ ⌊D⌋₊ := Nat.le_floor hDoneCast
          have hOneFloorPos : 0 < ⌊D⌋₊ := by omega
          simp [Lset, oddSquarefreeUpTo, hOneFloorPos]
        have hsumB :
            (∑ ell ∈ Lset,
              |progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell * B|) ≤ E := by
          calc
            _ = ∑ ell ∈ Lset,
                  |progressionPrimeSum x M c u Ψ r ell -
                    localSieveDensity M r ell *
                      smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ)| := by
                apply Finset.sum_congr rfl
                intro ell hell
                congr 1
                dsimp [B]
                ring
            _ ≤ E := by simpa [E] using hBVsum
        have hBVone :
            |progressionPrimeSum x M c u Ψ r 1 - B| ≤ E := by
          have hsingle := Finset.single_le_sum
            (fun ell hell => abs_nonneg
              (progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell * B)) hOneL
          have hg1 : localSieveDensity M r 1 = 1 := by
            simp [localSieveDensity]
          have hsingle' :
              |progressionPrimeSum x M c u Ψ r 1 -
                localSieveDensity M r 1 * B| ≤
              ∑ ell ∈ Lset,
                |progressionPrimeSum x M c u Ψ r ell -
                  localSieveDensity M r ell * B| := by
            exact hsingle
          exact le_trans (by simpa [hg1] using hsingle') hsumB
        have hDensityNonneg (ell : ℕ) : 0 ≤ localSieveDensity M r ell := by
          unfold localSieveDensity
          split_ifs <;> positivity
        have hDensityTotal :
            0 ≤ ∑ ell ∈ Lset, localSieveDensity M r ell :=
          Finset.sum_nonneg fun ell hell => hDensityNonneg ell
        have hpow : Real.rpow (Real.log x) 4 *
            Real.rpow (Real.log x) (-A') = Real.rpow (Real.log x) (-A) := by
          calc
            _ = Real.rpow (Real.log x) (4 + (-A')) :=
              (Real.rpow_add (by linarith [hlogx]) 4 (-A')).symm
            _ = Real.rpow (Real.log x) (-A) := by
              congr 1
              dsimp [A']
              ring
        have hTri (ell : ℕ) :
            |progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1| ≤
              |progressionPrimeSum x M c u Ψ r ell -
                  localSieveDensity M r ell * B| +
                localSieveDensity M r ell * |progressionPrimeSum x M c u Ψ r 1 - B| := by
          have hg := hDensityNonneg ell
          calc
            _ = |(progressionPrimeSum x M c u Ψ r ell -
                    localSieveDensity M r ell * B) +
                  localSieveDensity M r ell * (B - progressionPrimeSum x M c u Ψ r 1)| := by
                    congr 1
                    ring
            _ ≤ _ := abs_add_le _ _
            _ = _ := by
              calc
                _ = |progressionPrimeSum x M c u Ψ r ell -
                      localSieveDensity M r ell * B| +
                    |localSieveDensity M r ell| *
                      |B - progressionPrimeSum x M c u Ψ r 1| := by rw [abs_mul]
                _ = |progressionPrimeSum x M c u Ψ r ell -
                      localSieveDensity M r ell * B| +
                    localSieveDensity M r ell *
                      |progressionPrimeSum x M c u Ψ r 1 - B| := by
                  rw [abs_of_nonneg hg, abs_sub_comm B (progressionPrimeSum x M c u Ψ r 1)]
        have hsumTri :
            (∑ ell ∈ Lset,
              |progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|) ≤
              (∑ ell ∈ Lset,
                |progressionPrimeSum x M c u Ψ r ell -
                  localSieveDensity M r ell * B|) +
                (∑ ell ∈ Lset, localSieveDensity M r ell) *
                  |progressionPrimeSum x M c u Ψ r 1 - B| := by
          calc
            _ ≤ ∑ ell ∈ Lset,
                  (|progressionPrimeSum x M c u Ψ r ell -
                    localSieveDensity M r ell * B| +
                    localSieveDensity M r ell *
                      |progressionPrimeSum x M c u Ψ r 1 - B|) :=
                Finset.sum_le_sum fun ell hell => hTri ell
            _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]
        have hsumBound :
            (∑ ell ∈ Lset,
              |progressionPrimeSum x M c u Ψ r ell -
                localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|) ≤
              E + (4 * Real.rpow (Real.log x) 4) * E := by
          calc
            _ ≤ _ := hsumTri
            _ ≤ E + (4 * Real.rpow (Real.log x) 4) * E := by
              have hL4nonneg : 0 ≤ 4 * Real.rpow (Real.log x) 4 :=
                mul_nonneg (by norm_num)
                  (Real.rpow_nonneg (by linarith [hlogx]) _)
              exact add_le_add hsumB
                (mul_le_mul (hDensitySum r) hBVone (abs_nonneg _)
                  hL4nonneg)
        dsimp [E]
        calc
          _ ≤ Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A') +
              (4 * Real.rpow (Real.log x) 4) *
                (Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A')) := hsumBound
          _ ≤ 5 * Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
            calc
              _ = Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A') +
                    4 * Cbv * (x / (r : ℝ)) *
                      (Real.rpow (Real.log x) 4 * Real.rpow (Real.log x) (-A')) := by
                dsimp [E]
                ring
              _ = Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A') +
                    4 * Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
                rw [hpow]
              _ ≤ Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) +
                    4 * Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow_of_exponent_le hlogx (by dsimp [A']; linarith))
                    (by positivity)
                · exact le_rfl
              _ = _ := by ring
      have hWeightedErr :
          (∑ r ∈ R,
            markedWeight x K a (1 / 2 : ℝ) r *
              (∑ ell ∈ Lset,
                |progressionPrimeSum x M c u Ψ r ell -
                  localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|)) ≤
            C_A * x * J₀ * Real.rpow (Real.log x) (-A) := by
        have hCoeffNonneg : 0 ≤ 5 * Cbv * x * Real.rpow (Real.log x) (-A) := by
          apply mul_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · norm_num
              · exact hCbv.le
            · exact hxpos.le
          · exact Real.rpow_nonneg (le_of_lt (by linarith [hlogx])) _
        calc
          _ ≤ ∑ r ∈ R,
              markedWeight x K a (1 / 2 : ℝ) r *
                (5 * Cbv * (x / (r : ℝ)) * Real.rpow (Real.log x) (-A)) := by
              apply Finset.sum_le_sum
              intro r hr
              exact mul_le_mul_of_nonneg_left (hLocalErr r hr) (hWeightNonneg r)
          _ = (5 * Cbv * x * Real.rpow (Real.log x) (-A)) *
                (∑ r ∈ R,
                  markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ)) := by
              calc
                _ = ∑ r ∈ R,
                    (5 * Cbv * x * Real.rpow (Real.log x) (-A)) *
                      (markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    have hrpos := hRpos r hr
                    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrpos)]
                _ = _ := by rw [Finset.mul_sum]
          _ ≤ (5 * Cbv * x * Real.rpow (Real.log x) (-A)) * J₀ :=
              mul_le_mul_of_nonneg_left hSumWeight hCoeffNonneg
          _ = C_A * x * J₀ * Real.rpow (Real.log x) (-A) := by
              dsimp [C_A]
              ring
      have hWeightedErrTarget :
          (∑ r ∈ R,
            ∑ ell ∈ Lset,
              markedWeight x K a (1 / 2 : ℝ) r *
                |progressionPrimeSum x M c u Ψ r ell -
                  localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|) ≤
            C_A * x * J₀ * Real.rpow (Real.log x) (-A) := by
        calc
          _ = ∑ r ∈ R,
                markedWeight x K a (1 / 2 : ℝ) r *
                  (∑ ell ∈ Lset,
                    |progressionPrimeSum x M c u Ψ r ell -
                      localSieveDensity M r ell * progressionPrimeSum x M c u Ψ r 1|) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.mul_sum]
          _ ≤ _ := hWeightedErr
      simpa [J₀, D, R, Lset] using hWeightedErrTarget
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
  obtain ⟨C_s, b₂₀, hCs, hb₂₀, hInitial⟩ := initial_lower
  obtain ⟨b₀, hb₀, C_d, hCd, hCdBound⟩ := ArtinPrimitiveRoots.Sieve.lem_density.2
  let b₂ : ℝ := min b₂₀ b₀
  have hb₂ : 0 < b₂ := lt_min hb₂₀ hb₀
  refine ⟨C_s, C_d, b₂, hCs, hCd, hb₂, ?_⟩
  intro M c u κ hM hM8 hc hcM hu hcu hcu' hκ hκsmall b hb hbb₂ hbk
  obtain ⟨K₀, hbinCost⟩ :=
    bin_cost M c u κ b hM hM8 hc hcM hu hcu hcu' hκ hκsmall hb
  refine ⟨K₀, ?_⟩
  intro K hK a ha Ψ hΨ
  have hbe : b < 1 / 2 - κ := hbk
  obtain ⟨J, γ, hJ, hγ0, hγend, hγbounds, hγstrict, hBudget⟩ :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.exists_roughDensity_partition_budget
      b (1 / 2 - κ) hb hbe (by linarith)
  have hIntegral := ArtinPrimitiveRoots.Construction.Proofs.C4.roughDensity_integral_le
    b κ hb hκ hκsmall hbe
  refine ⟨J, γ, hγ0, hγend, hγstrict, hBudget, hIntegral, ?_⟩
  intro η hη
  have hJreal : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  let ηbin : ℝ := η / (2 * (J : ℝ))
  have hηbin : 0 < ηbin := by dsimp [ηbin]; positivity
  have hcosts : ∀ j : Fin J, ∃ C x₀ : ℝ,
      0 < C ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum
            x M c u K a Ψ (γ j.castSucc) (γ j.succ) ≤
          (singularProduct M * conTotalMass x M c u K a Ψ / Real.log x) *
            (sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
              Set.Icc (γ j.castSucc) (γ j.succ)) *
              Real.log (γ j.succ / γ j.castSucc) + ηbin) := by
    intro j
    have hγlt : γ j.castSucc < γ j.succ :=
      hγstrict _ _ (by simp)
    obtain ⟨C, x₀, hC, hx₀, hCost⟩ :=
      hbinCost K hK a ha Ψ hΨ (γ j.castSucc) (γ j.succ)
        (hγbounds j.castSucc).1 hγlt (hγbounds j.succ).2 ηbin hηbin
    refine ⟨C, x₀, hC, hx₀, ?_⟩
    intro x hx
    simpa [ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum] using hCost x hx
  choose Cj xj hCj hxj hCostj using hcosts
  have hxjNonneg : ∀ j : Fin J, 0 ≤ xj j := fun j => by linarith [hxj j]
  let xsum : ℝ := ∑ j : Fin J, xj j
  have hxsum : 0 ≤ xsum := Finset.sum_nonneg fun j _ => hxjNonneg j
  have hxjLeSum (j : Fin J) : xj j ≤ xsum := by
    dsimp [xsum]
    apply Finset.single_le_sum
    · intro i hi
      exact hxjNonneg i
    · exact Finset.mem_univ j
  obtain ⟨B, xS, hB, hxS₂, hSupport⟩ :=
    support M c u K a Ψ hM hc ha hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1
  have hsing : 0 < singularProduct M := (sieve_products M hM).1
  have hε : 0 < κ / 2 := by linarith
  have hεκ : κ / 2 < κ := by linarith
  have hbInitial : b < b₂₀ := lt_of_lt_of_le hbb₂ (min_le_left b₂₀ b₀)
  obtain ⟨xInit, hxInit₂, hInitialX⟩ :=
    hInitial M c u K a Ψ hΨ κ (κ / 2) hκ hκsmall hε hεκ
      hM hc hcM hu hcu hcu' ha b hb hbInitial hbk (η / 2) (by linarith)
  let xBound : ℝ := xS + xInit + xsum
  have hxBound₂ : 2 ≤ xBound := by
    dsimp [xBound]
    linarith [hxS₂, hxInit₂, hxsum]
  refine ⟨xBound, hxBound₂, ?_⟩
  intro x hxBound
  have hxS : xS ≤ x := by dsimp [xBound] at hxBound; linarith [hxsum]
  have hxInit : xInit ≤ x := by dsimp [xBound] at hxBound; linarith [hxsum]
  have hx : 2 ≤ x := le_trans hxBound₂ hxBound
  have hWeightSupport := hSupport x hxS
  rcases hWeightSupport with ⟨_, hSupportD, hWeightD⟩
  have hweight : ∀ d, 0 ≤ conWeight x M c u K a Ψ d := fun d => (hWeightD d).1
  have hsupport : ∀ d, conWeight x M c u K a Ψ d ≠ 0 →
      x < (d : ℝ) ∧ (d : ℝ) < 2 * x := by
    intro d hd
    rcases hSupportD d hd with ⟨hlo, hrest⟩
    exact ⟨hlo, hrest.1⟩
  have htotal : 0 ≤ conTotalMass x M c u K a Ψ := by
    unfold conTotalMass
    apply Finset.sum_nonneg
    intro d hd
    exact hweight d
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  let S : ℝ := singularProduct M * conTotalMass x M c u K a Ψ / Real.log x
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have he : (1 / 2 : ℝ) - κ < 1 / 2 := by linarith
  have hbe : b < (1 / 2 : ℝ) - κ := hbk
  have hremoval :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.roughConstructionMass_le_binPairSums
      x M c u K a Ψ b (1 / 2 - κ) J γ hx hb hbe he hJ
      hγ0 hγend hγbounds hγstrict hweight hsupport
  have hBinEach (j : Fin J) :
      ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum
          x M c u K a Ψ (γ j.castSucc) (γ j.succ) ≤
        S * (sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
          Set.Icc (γ j.castSucc) (γ j.succ)) *
          Real.log (γ j.succ / γ j.castSucc) + ηbin) := by
    have hxj' : xj j ≤ x := (hxjLeSum j).trans (by dsimp [xBound] at hxBound; linarith [hxsum])
    simpa [S] using hCostj j x hxj'
  have hEtaSum : (∑ _j : Fin J, ηbin) = η / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [ηbin]
    field_simp
  have hBinCostSum :
      (∑ j : Fin J,
        ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum
          x M c u K a Ψ (γ j.castSucc) (γ j.succ)) ≤
        S * ((∑ j : Fin J,
          sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
            Set.Icc (γ j.castSucc) (γ j.succ)) *
            Real.log (γ j.succ / γ j.castSucc)) + η / 2) := by
    calc
      _ ≤ ∑ j : Fin J,
          S * (sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
            Set.Icc (γ j.castSucc) (γ j.succ)) *
            Real.log (γ j.succ / γ j.castSucc) + ηbin) :=
              Finset.sum_le_sum fun j _ => hBinEach j
      _ = S * ((∑ j : Fin J,
          sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
            Set.Icc (γ j.castSucc) (γ j.succ)) *
            Real.log (γ j.succ / γ j.castSucc)) + η / 2) := by
              calc
                _ = ∑ j : Fin J,
                    (S * (sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
                      Set.Icc (γ j.castSucc) (γ j.succ)) *
                      Real.log (γ j.succ / γ j.castSucc)) + S * ηbin) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                _ = (∑ j : Fin J,
                    S * (sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
                      Set.Icc (γ j.castSucc) (γ j.succ)) *
                      Real.log (γ j.succ / γ j.castSucc))) +
                    (∑ j : Fin J, S * ηbin) := by
                      rw [Finset.sum_add_distrib]
                _ = S * (∑ j : Fin J,
                    sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
                      Set.Icc (γ j.castSucc) (γ j.succ)) *
                      Real.log (γ j.succ / γ j.castSucc)) +
                    S * (∑ j : Fin J, ηbin) := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                _ = _ := by rw [hEtaSum]; ring
  have hFcont :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.roughDensity_integrand_continuous
      b κ hb hκ hκsmall hbk
  have hFint : IntervalIntegrable
      (fun t : ℝ => roughDensity t (1 - t) / t) MeasureTheory.volume b (1 / 2 - κ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hbe)
    apply hFcont.mono
    intro t ht
    exact ⟨le_trans le_rfl ht.1, le_trans ht.2 (by linarith)⟩
  have hconstInt : IntervalIntegrable (fun _ : ℝ => (1 / 10 : ℝ))
      MeasureTheory.volume b (1 / 2 - κ) := by
    exact continuousOn_const.intervalIntegrable
  have hconstVal :
      (∫ t in b..(1 / 2 - κ), (1 / 10 : ℝ)) = ((1 / 2 - κ) - b) / 10 := by
    simp [intervalIntegral.integral_const]
    ring
  have hBudgetSplit :
      (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t + 1 / 10) =
        (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) +
          ((1 / 2 - κ) - b) / 10 := by
    rw [intervalIntegral.integral_add hFint hconstInt, hconstVal]
  have hlen : ((1 / 2 - κ) - b) / 10 ≤ (1 / 10 : ℝ) := by
    have hlen' : (1 / 2 - κ) - b ≤ 1 := by linarith
    nlinarith
  have hBudgetSplitLe :
      (∑ j : Fin J,
        sSup ((fun t : ℝ => roughDensity (γ j.castSucc) (1 - t)) ''
          Set.Icc (γ j.castSucc) (γ j.succ)) *
          Real.log (γ j.succ / γ j.castSucc)) ≤
        (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) + 1 / 10 := by
    calc
      _ ≤ ∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t + 1 / 10 := hBudget
      _ = (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) +
          ((1 / 2 - κ) - b) / 10 := hBudgetSplit
      _ ≤ _ := add_le_add_right hlen _
  have hIntegralDensity :
      (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) + 1 / 10 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 9 / 10 := by
    have hDb : roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) :=
      hCdBound b hb (lt_of_lt_of_le hbb₂ (min_le_right b₂₀ b₀))
    linarith [hIntegral, hDb]
  have hBinCostBound :
      (∑ j : Fin J,
        ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum
          x M c u K a Ψ (γ j.castSucc) (γ j.succ)) ≤
        S * (Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 9 / 10 + η / 2) := by
    apply hBinCostSum.trans
    apply mul_le_mul_of_nonneg_left _ hS
    simpa [add_comm] using
      add_le_add_right (hBudgetSplitLe.trans hIntegralDensity) (η / 2)
  have hrpow : Real.rpow x b ≤ Real.rpow x (1 / 2 - κ / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) (by linarith)
  have hLow :
      S * (Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 - C_s * Real.exp (-(1 / 20 : ℝ) / b)) - η / 2) ≤
        roughConstructionMass x M c u K a Ψ (Real.rpow x b) := by
    simpa [S] using hInitialX x hxInit hrpow
  have hCombined :
      S * (Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 - C_s * Real.exp (-(1 / 20 : ℝ) / b)) - η / 2) ≤
        roughConstructionMass x M c u K a Ψ (Real.rpow x (1 / 2 - κ)) +
          S * (Real.exp (-Real.eulerMascheroniConstant) / b *
            (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 9 / 10 + η / 2) := by
    calc
      _ ≤ roughConstructionMass x M c u K a Ψ (Real.rpow x b) := hLow
      _ ≤ roughConstructionMass x M c u K a Ψ (Real.rpow x (1 / 2 - κ)) +
          ∑ j : Fin J,
            ArtinPrimitiveRoots.Construction.Proofs.C4.binPairSum
              x M c u K a Ψ (γ j.castSucc) (γ j.succ) := hremoval
      _ ≤ _ := add_le_add_right hBinCostBound _
  have hCoeff :
      (9 / 10 - Real.exp (-Real.eulerMascheroniConstant) / b *
        (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
          C_d * Real.exp (-(1 / 20 : ℝ) / b)) - η) =
      (Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 - C_s * Real.exp (-(1 / 20 : ℝ) / b)) - η / 2) -
        (Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 9 / 10 + η / 2) := by
    ring
  calc
    S * (9 / 10 - Real.exp (-Real.eulerMascheroniConstant) / b *
        (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
          C_d * Real.exp (-(1 / 20 : ℝ) / b)) - η) =
        S * ((Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 - C_s * Real.exp (-(1 / 20 : ℝ) / b)) - η / 2) -
          (Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 9 / 10 + η / 2)) := by
            rw [hCoeff]
    _ ≤ roughConstructionMass x M c u K a Ψ (Real.rpow x (1 / 2 - κ)) := by
      nlinarith [hCombined]

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

set_option maxHeartbeats 8000000 in
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
  classical
  intro c hc hcM u κ b hκ hκsmall hb hu hcu hcu'
  let δ : ℝ := min (b / 2) (1 / 5)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ktype, hTypeK⟩ := con_type_ii δ (2 / 5) (45 / 100) (55 / 100)
    (1 / 4) 2 hδ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Ktype, ?_⟩
  intro K hK a ha
  obtain ⟨Ctype, xType, hCtype, hxType₂, hTypeAt⟩ :=
    hTypeK K hK M c u a ha hM h8 hc hcM hu hcu hcu' Ψ
      hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1 hΨ.1 hΨ.2.2.2.2
  obtain ⟨xCover, hxCover₂, hCoverAt⟩ :=
    hCover M c u K a Ψ hΨ κ hM h8 hc hcM hu hcu hcu' ha hκ hκsmall
  obtain ⟨xPair, hxPair₂, hPairAt⟩ := hPairs c hc u K a ha
  obtain ⟨B, xSupport, hB, hxSupport₂, hSupportAt⟩ :=
    support M c u K a Ψ hM hc ha hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1
  have hcpos : 0 < c := by rcases hc with h | h <;> simp [h]
  obtain ⟨c₀, C₀, hc₀, hC₀, hDistribution⟩ := con_distribution M Ψ hM hΨ
  have hε : 0 < κ / 2 := by linarith
  have hεκ : κ / 2 < κ := by linarith
  obtain ⟨xDistribution, hxDistribution₂, hDistributionErrors, hMass⟩ :=
    hDistribution c hc hcM u hu hcu hcu' K a ha (κ / 2) κ hε hεκ hκsmall
  obtain ⟨Cmass, xMass, hCmass, hxMass₂, hHarmonic⟩ :=
    con_harmonic M c u Ψ K a hM hcpos ha hΨ
  dsimp only
  intro η hη
  let E : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hE : 0 < E := by positivity
  obtain ⟨yMertens, hyMertens, hMertens⟩ :=
    Ext.TypeIIInputs.mertens.2 (E / 2) (by positivity)
  have hW_atTop : Tendsto (fun x : ℝ => roughCutoff x) atTop atTop := by
    unfold roughCutoff
    have hpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (24 / 100 : ℝ))
        atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    exact Real.tendsto_exp_atTop.comp hpow
  have hWevent : ∀ᶠ x : ℝ in atTop, yMertens ≤ roughCutoff x :=
    hW_atTop.eventually (eventually_ge_atTop yMertens)
  obtain ⟨xW, hxW⟩ := Filter.eventually_atTop.mp hWevent
  let Cpow : ℝ := E / 2 * (45 / 100 : ℝ)
  have hCpow : 0 < Cpow := by dsimp [Cpow]; positivity
  have hLpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (76 / 100 : ℝ))
      atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hCpowL : Tendsto (fun x : ℝ => Cpow * Real.rpow (Real.log x) (76 / 100 : ℝ))
      atTop atTop := hLpow.const_mul_atTop hCpow
  have hCpowEvent : ∀ᶠ x : ℝ in atTop,
      1 ≤ Cpow * Real.rpow (Real.log x) (76 / 100 : ℝ) :=
    hCpowL.eventually (eventually_ge_atTop 1)
  obtain ⟨xProxy, hxProxy⟩ := Filter.eventually_atTop.mp hCpowEvent
  have hInvLog : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hConstLog2 : Tendsto (fun _ : ℝ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  have hLog2OverLog : Tendsto (fun x : ℝ => Real.log 2 / Real.log x)
      atTop (𝓝 0) := by
    have h := hConstLog2.mul hInvLog
    convert h using 1 <;> simp [div_eq_mul_inv]
  let qfun : ℝ → ℝ := fun x => (46 / 100 : ℝ) - Real.log 2 / Real.log x
  have hqfun : Tendsto qfun atTop (𝓝 (46 / 100 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => (46 / 100 : ℝ)) atTop
        (𝓝 (46 / 100 : ℝ)) := tendsto_const_nhds
    have h := hconst.sub hLog2OverLog
    simpa [qfun] using h
  have hqCorrection : Tendsto
      (fun x : ℝ => (qfun x)⁻¹ ^ 2 - (46 / 100 : ℝ)⁻¹ ^ 2)
      atTop (𝓝 0) := by
    have hqInv := hqfun.inv₀ (by norm_num : (46 / 100 : ℝ) ≠ 0)
    have hqInvSq := hqInv.pow 2
    have hconstSq : Tendsto (fun _ : ℝ => (46 / 100 : ℝ)⁻¹ ^ 2) atTop
        (𝓝 ((46 / 100 : ℝ)⁻¹ ^ 2)) := tendsto_const_nhds
    have h := hqInvSq.sub hconstSq
    simpa [qfun] using h
  let ηcoeff : ℝ := η / (4 * (C₁ * Cdyad + 1))
  have hηcoeff : 0 < ηcoeff := by dsimp [ηcoeff]; positivity
  have hCoeffEvent : ∀ᶠ x : ℝ in atTop,
      (qfun x)⁻¹ ^ 2 - (46 / 100 : ℝ)⁻¹ ^ 2 < ηcoeff :=
    hqCorrection.eventually (Iio_mem_nhds hηcoeff)
  obtain ⟨xCoeff, hxCoeff⟩ := Filter.eventually_atTop.mp hCoeffEvent
  let ηerror : ℝ := c₀ * η / (16 * Ctype * Cdyad)
  have hηerror : 0 < ηerror := by dsimp [ηerror]; positivity
  have hInvL3 : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (-3 : ℝ))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp Real.tendsto_log_atTop
  have hErrorEvent : ∀ᶠ x : ℝ in atTop,
      Real.rpow (Real.log x) (-3 : ℝ) < ηerror :=
    hInvL3.eventually (Iio_mem_nhds hηerror)
  obtain ⟨xError, hxError⟩ := Filter.eventually_atTop.mp hErrorEvent
  let xCore : ℝ := max (Real.exp 200)
    (max xCover (max xPair (max xType (max xSupport (max xDistribution xMass)))) )
  let x₀ : ℝ := max xCore (max xW (max xProxy (max xCoeff xError)))
  have hExp200 : 2 ≤ Real.exp (200 : ℝ) := by
    have h := Real.add_one_le_exp (200 : ℝ)
    nlinarith
  have hxCore0 : xCore ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have hx₀₂ : 2 ≤ x₀ := by
    have hExpCore : Real.exp (200 : ℝ) ≤ xCore := by
      dsimp [xCore]
      exact le_max_left _ _
    exact hExp200.trans (hExpCore.trans hxCore0)
  refine ⟨x₀, hx₀₂, ?_⟩
  intro x hx
  have hxCore : xCore ≤ x := hxCore0.trans hx
  have hxCoverCore : xCover ≤ xCore := by simp [xCore]
  have hxPairCore : xPair ≤ xCore := by simp [xCore]
  have hxTypeCore : xType ≤ xCore := by simp [xCore]
  have hxSupportCore : xSupport ≤ xCore := by simp [xCore]
  have hxDistributionCore : xDistribution ≤ xCore := by simp [xCore]
  have hxMassCore : xMass ≤ xCore := by simp [xCore]
  have hxCover : xCover ≤ x := hxCoverCore.trans hxCore
  have hxPair : xPair ≤ x := hxPairCore.trans hxCore
  have hxType : xType ≤ x := hxTypeCore.trans hxCore
  have hxSupport : xSupport ≤ x := hxSupportCore.trans hxCore
  have hxDistribution : xDistribution ≤ x := hxDistributionCore.trans hxCore
  have hxMass : xMass ≤ x := hxMassCore.trans hxCore
  have hxEvents : max xW (max xProxy (max xCoeff xError)) ≤ x := by
    have hle : max xW (max xProxy (max xCoeff xError)) ≤ x₀ := by
      dsimp [x₀]
      exact le_max_right _ _
    exact hle.trans hx
  have hxW' : xW ≤ x := by
    have hle : xW ≤ max xW (max xProxy (max xCoeff xError)) := le_max_left _ _
    exact hle.trans hxEvents
  have hxProxy' : xProxy ≤ x := by
    have hle : xProxy ≤ max xProxy (max xCoeff xError) := le_max_left _ _
    exact (le_trans hle (le_max_right xW _)).trans hxEvents
  have hxCoeff' : xCoeff ≤ x := by
    have hle : xCoeff ≤ max xCoeff xError := le_max_left _ _
    exact (le_trans hle (le_max_right xProxy _)).trans (le_max_right xW _ |>.trans hxEvents)
  have hxError' : xError ≤ x := by
    have hle : xError ≤ max xCoeff xError := le_max_right _ _
    exact (le_trans hle (le_max_right xProxy _)).trans (le_max_right xW _ |>.trans hxEvents)
  have hxExp : Real.exp (200 : ℝ) ≤ x := by
    have hExpCore : Real.exp (200 : ℝ) ≤ xCore := by dsimp [xCore]; exact le_max_left _ _
    exact hExpCore.trans hxCore
  have hx2 : 2 ≤ x := hExp200.trans hxExp
  have hxlarge : 1 < x := by linarith
  have hLlarge : 200 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (200 : ℝ)) hxExp
    simpa using h
  have hLpos : 0 < Real.log x := Real.log_pos hxlarge
  have hCutoff : roughCutoff x < Real.rpow x (2 / 5 : ℝ) :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.roughCutoff_lt_two_fifths hxlarge hLlarge
  have hyW : yMertens ≤ roughCutoff x := hxW x hxW'
  have hMertensX := hMertens (roughCutoff x) hyW
  have hlogW : Real.log (roughCutoff x) =
      Real.rpow (Real.log x) (24 / 100 : ℝ) := by simp [roughCutoff]
  have hVprod : E / 2 ≤ roughSieveProduct (roughCutoff x) *
      Real.rpow (Real.log x) (24 / 100 : ℝ) := by
    have habs := abs_le.mp hMertensX
    rw [hlogW] at habs
    dsimp [E] at habs ⊢
    linarith
  have hLpow24pos : 0 < Real.rpow (Real.log x) (24 / 100 : ℝ) :=
    Real.rpow_pos_of_pos hLpos _
  have hVpos : 0 < roughSieveProduct (roughCutoff x) := by
    by_contra hn
    have hle : roughSieveProduct (roughCutoff x) ≤ 0 := le_of_not_gt hn
    have hmul : roughSieveProduct (roughCutoff x) *
        Real.rpow (Real.log x) (24 / 100 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hLpow24pos.le
    linarith [hVprod]
  have hVlower : E / 2 / Real.rpow (Real.log x) (24 / 100 : ℝ) ≤
      roughSieveProduct (roughCutoff x) :=
    (div_le_iff₀ hLpow24pos).2 (by simpa [mul_comm] using hVprod)
  have hxProxyLarge := hxProxy x hxProxy'
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have he : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) he
      _ = 1 := Real.log_exp 1
  have hlog2ratio : Real.log 2 / Real.log x ≤ 1 / 200 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith [hlog2le1, hLlarge]
  have hqLower : (45 / 100 : ℝ) ≤ qfun x := by
    dsimp [qfun]
    linarith [hlog2ratio]
  have hqPos : 0 < qfun x := lt_of_lt_of_le (by norm_num) hqLower
  have hLpow24 : Real.rpow (Real.log x) (24 / 100 : ℝ) ≠ 0 :=
    (ne_of_gt hLpow24pos)
  have hRatioPow : Real.rpow (Real.log x) (76 / 100 : ℝ) =
      Real.log x / Real.rpow (Real.log x) (24 / 100 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) (1 - 24 / 100) := by congr 1 <;> norm_num
      _ = Real.rpow (Real.log x) 1 /
          Real.rpow (Real.log x) (24 / 100 : ℝ) := Real.rpow_sub hLpos 1 (24 / 100 : ℝ)
      _ = _ := by simp
  have hCpowEq : Cpow * Real.rpow (Real.log x) (76 / 100 : ℝ) =
      (E / 2 / Real.rpow (Real.log x) (24 / 100 : ℝ)) *
        ((45 / 100 : ℝ) * Real.log x) := by
    rw [hRatioPow]
    dsimp [Cpow]
    field_simp [hLpow24]
    <;> ring
  have hLogmLower (H : ℝ) (hHlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
      (m : ℕ) (hm : m ∈ dyadicIntegers H) :
      qfun x * Real.log x ≤ Real.log (m : ℝ) := by
    have hmBounds :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval H hm
    have hmBounds' :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff H m |>.mp hmBounds
    have hHpos : 0 < H := lt_of_lt_of_le
      (div_pos (Real.rpow_pos_of_pos (by linarith : 0 < x) _) (by norm_num)) hHlo
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hHpos hmBounds'.1
    have hlogHM := Real.log_le_log hHpos hmBounds'.1
    have hlogH := ArtinPrimitiveRoots.Construction.Proofs.C4.dyadic_log_lower_exact
      hxlarge hHlo
    have hqExact : qfun x * Real.log x =
        (46 / 100 : ℝ) * Real.log x - Real.log 2 := by
      dsimp [qfun]
      field_simp [ne_of_gt hLpos]
      <;> ring
    linarith
  have hVLogm (H : ℝ) (hHlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
      (m : ℕ) (hm : m ∈ dyadicIntegers H) :
      1 ≤ roughSieveProduct (roughCutoff x) * Real.log (m : ℝ) := by
    have hlogmLower := hLogmLower H hHlo m hm
    have hlogm45 : (45 / 100 : ℝ) * Real.log x ≤ Real.log (m : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hqLower hLpos.le) hlogmLower
    calc
      1 ≤ Cpow * Real.rpow (Real.log x) (76 / 100 : ℝ) := hxProxyLarge
      _ = (E / 2 / Real.rpow (Real.log x) (24 / 100 : ℝ)) *
          ((45 / 100 : ℝ) * Real.log x) := hCpowEq
      _ ≤ roughSieveProduct (roughCutoff x) * ((45 / 100 : ℝ) * Real.log x) :=
        mul_le_mul_of_nonneg_right hVlower (by positivity)
      _ ≤ roughSieveProduct (roughCutoff x) * Real.log (m : ℝ) :=
        mul_le_mul_of_nonneg_left hlogm45 hVpos.le
  have hProxyEq (H : ℝ) (hHlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
      (hHhi : H ≤ 2 * Real.rpow x (54 / 100 : ℝ)) (m : ℕ)
      (hm : m ∈ dyadicIntegers H) :
      roughProxy x (2 / 5) m =
        if roughAbove m (roughCutoff x) then
          1 / (roughSieveProduct (roughCutoff x) * Real.log (m : ℝ)) else 0 := by
    have hmBounds :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval H hm
    have hmBounds' :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff H m |>.mp hmBounds
    have hHpos : 0 < H := lt_of_lt_of_le
      (div_pos (Real.rpow_pos_of_pos (by linarith : 0 < x) _) (by norm_num)) hHlo
    have hmpos : 0 < (m : ℝ) := by
      have : H ≤ (m : ℝ) := hmBounds'.1
      exact lt_of_lt_of_le hHpos this
    have hm2pos : 0 < 2 * H := by positivity
    have hlogmUpper := Real.log_le_log hmpos hmBounds'.2
    have hwin := ArtinPrimitiveRoots.Construction.Proofs.C4.dyadic_log_scales_in_window
      hxlarge hLlarge hHlo hHhi
    have hlog2Hupper : Real.log (2 * H) ≤ (55 / 100 : ℝ) * Real.log x :=
      (div_le_iff₀ hLpos).1 hwin.2.2
    have hsUpper : Real.log (m : ℝ) / Real.log x ≤ 55 / 100 :=
      (div_le_iff₀ hLpos).2 (hlogmUpper.trans hlog2Hupper)
    have hlogmPos : 0 < Real.log (m : ℝ) := by
      have hlogmLower := hLogmLower H hHlo m hm
      have hlogm45 : (45 / 100 : ℝ) * Real.log x ≤ Real.log (m : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hqLower hLpos.le) hlogmLower
      exact lt_of_lt_of_le (mul_pos (by norm_num) hLpos) hlogm45
    have hwidth : Real.log (m : ℝ) / Real.log x < 2 * (2 / 5 : ℝ) := by
      norm_num
      linarith
    have hD := ArtinPrimitiveRoots.Construction.Proofs.C4.roughDensity_eq_one_div
      (2 / 5) (Real.log (m : ℝ) / Real.log x) (by norm_num) hwidth
    exact ArtinPrimitiveRoots.Construction.Proofs.C4.roughProxy_eq_one_div_log
      hLpos hVpos hlogmPos hD
  have hProxyLeOne (H : ℝ) (hHlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
      (hHhi : H ≤ 2 * Real.rpow x (54 / 100 : ℝ)) (m : ℕ)
      (hm : m ∈ dyadicIntegers H) :
      0 ≤ roughProxy x (2 / 5) m ∧ roughProxy x (2 / 5) m ≤ 1 := by
    rw [hProxyEq H hHlo hHhi m hm]
    by_cases hrough : roughAbove m (roughCutoff x)
    · simp only [if_pos hrough]
      have hlogmPos : 0 < Real.log (m : ℝ) := by
        have hmBounds :=
          ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval H hm
        have hmBounds' :=
          ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff H m |>.mp hmBounds
        have hHpos : 0 < H := lt_of_lt_of_le
          (div_pos (Real.rpow_pos_of_pos (by linarith : 0 < x) _) (by norm_num)) hHlo
        have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hHpos hmBounds'.1
        have hlogm := ArtinPrimitiveRoots.Construction.Proofs.C4.dyadic_log_lower_exact
          hxlarge hHlo
        have hlogm1 := Real.log_le_log hHpos hmBounds'.1
        have hlogm45 : (45 / 100 : ℝ) * Real.log x ≤ Real.log (m : ℝ) := by
          have hh := hLogmLower H hHlo m hm
          linarith [hqLower]
        exact lt_of_lt_of_le (mul_pos (by norm_num) hLpos) hlogm45
      have hdenpos : 0 < roughSieveProduct (roughCutoff x) * Real.log (m : ℝ) :=
        mul_pos hVpos hlogmPos
      exact ⟨one_div_nonneg.mpr hdenpos.le,
        (div_le_one hdenpos).2 (hVLogm H hHlo m hm)⟩
    · simp [hrough]
  have hProxyLeScale (H : ℝ) (hHlo : Real.rpow x (46 / 100 : ℝ) / 2 ≤ H)
      (hHhi : H ≤ 2 * Real.rpow x (54 / 100 : ℝ)) (m : ℕ)
      (hm : m ∈ dyadicIntegers H) :
      roughProxy x (2 / 5) m ≤
        1 / (roughSieveProduct (roughCutoff x) * (qfun x * Real.log x)) := by
    rw [hProxyEq H hHlo hHhi m hm]
    by_cases hrough : roughAbove m (roughCutoff x)
    · simp only [if_pos hrough]
      have hlogmLower := hLogmLower H hHlo m hm
      have hdenLower : roughSieveProduct (roughCutoff x) *
          (qfun x * Real.log x) ≤
            roughSieveProduct (roughCutoff x) * Real.log (m : ℝ) :=
        mul_le_mul_of_nonneg_left hlogmLower hVpos.le
      have hdenpos : 0 < roughSieveProduct (roughCutoff x) *
          (qfun x * Real.log x) := mul_pos hVpos (mul_pos hqPos hLpos)
      exact one_div_le_one_div_of_le hdenpos hdenLower
    · simp [hrough]
      positivity
  obtain ⟨N, hNbound, H₁, H₂, hBoxBounds, hCoverPairs⟩ := hCoverAt x hxCover
  let gamma : ℝ := 2 / 5
  let P : ℕ → ℝ := fun m => roughIndicator x gamma m
  let Bp : ℕ → ℝ := fun m => roughProxy x gamma m
  let E₁ : Fin N → ℝ := fun i =>
    ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
      (P m - Bp m) * P n * conWeight x M c u K a Ψ (m * n)
  let E₂ : Fin N → ℝ := fun i =>
    ∑ m ∈ dyadicIntegers (H₂ i), ∑ n ∈ dyadicIntegers (H₁ i),
      (P m - Bp m) * Bp n * conWeight x M c u K a Ψ (m * n)
  have hTypeErrors (i : Fin N) :
      ∃ z₁ z₂ : ℂ,
        z₁ = (E₁ i : ℂ) ∧ z₂ = (E₂ i : ℂ) ∧
        ‖z₁‖ ≤ Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) ∧
        ‖z₂‖ ≤ Ctype * (H₂ i * H₁ i) * Real.rpow (Real.log x) (-6 : ℝ) := by
    rcases hBoxBounds i with ⟨hprodlo, hprodupp, hH₁lo, hH₁hi, hH₂lo, hH₂hi⟩
    have hxone : 1 ≤ x := by linarith
    have hpowδ : Real.rpow x δ ≤ Real.rpow x (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hxone (by dsimp [δ]; exact min_le_right _ _)
    have hpowBox :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.rpow_one_fifth_le_dyadic_lower
        hxlarge hLlarge
    have hδH₁ : Real.rpow x δ ≤ H₁ i := hpowδ.trans (hpowBox.trans hH₁lo)
    have hδH₂ : Real.rpow x δ ≤ H₂ i := hpowδ.trans (hpowBox.trans hH₂lo)
    have hscale₁ :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadic_log_scales_in_window
        hxlarge hLlarge hH₁lo hH₁hi
    have hscale₂ :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadic_log_scales_in_window
        hxlarge hLlarge hH₂lo hH₂hi
    let I₁ : Set ℕ :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicCoordinateInterval (H₁ i)
    let I₂ : Set ℕ :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicCoordinateInterval (H₂ i)
    letI : DecidablePred (fun m : ℕ => m ∈ I₁) := fun _ => Classical.propDecidable _
    letI : DecidablePred (fun m : ℕ => m ∈ I₂) := fun _ => Classical.propDecidable _
    let D₁ : Finset ℕ := @Finset.filter ℕ (fun m => m ∈ I₁)
      (fun _ => Classical.propDecidable _) (dyadicIntegers (H₁ i))
    let D₂ : Finset ℕ := @Finset.filter ℕ (fun m => m ∈ I₂)
      (fun _ => Classical.propDecidable _) (dyadicIntegers (H₂ i))
    have hI₁ : ArtinPrimitiveRoots.TypeII.IsNatInterval I₁ := by
      exact ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicCoordinateInterval_isNatInterval
        (H₁ i)
    have hI₂ : ArtinPrimitiveRoots.TypeII.IsNatInterval I₂ := by
      exact ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicCoordinateInterval_isNatInterval
        (H₂ i)
    have hI₁sub : I₁ ⊆ {m : ℕ | H₁ i ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H₁ i} := by
      intro m hm
      exact ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff
        (H₁ i) m |>.mp hm
    have hI₂sub : I₂ ⊆ {m : ℕ | H₂ i ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H₂ i} := by
      intro m hm
      exact ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff
        (H₂ i) m |>.mp hm
    have hfilter₁ :
        (dyadicIntegers (H₁ i)).filter (fun m => m ∈ I₁) = dyadicIntegers (H₁ i) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hm
        exact ⟨hm, ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₁ i) hm⟩
    have hfilter₂ :
        (dyadicIntegers (H₂ i)).filter (fun m => m ∈ I₂) = dyadicIntegers (H₂ i) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hm
        exact ⟨hm, ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₂ i) hm⟩
    have hD₁ : D₁ = dyadicIntegers (H₁ i) := by
      ext m
      simp only [D₁, Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hm
        exact ⟨hm, ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₁ i) hm⟩
    have hD₂ : D₂ = dyadicIntegers (H₂ i) := by
      ext m
      simp only [D₂, Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hm
        exact ⟨hm, ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₂ i) hm⟩
    let βP : ℕ → ℂ := fun n =>
      if n ∈ dyadicIntegers (H₂ i) then (roughIndicator x gamma n : ℂ) else 0
    let βB : ℕ → ℂ := fun n =>
      if n ∈ dyadicIntegers (H₁ i) then (roughProxy x gamma n : ℂ) else 0
    have hβPsupport : ∀ n, βP n ≠ 0 →
        n ∈ dyadicIntegers (H₂ i) ∧ roughAbove n (roughCutoff x) := by
      intro n hn
      dsimp [βP] at hn
      split_ifs at hn with hmem
      · have hR : roughIndicator x gamma n ≠ 0 := by exact_mod_cast hn
        have hrough : roughAbove n (Real.rpow x gamma) := by
          dsimp [roughIndicator] at hR
          split_ifs at hR with hrough
          · exact hrough
          · simp at hR
        exact ⟨hmem, ArtinPrimitiveRoots.Construction.Proofs.C4.roughAbove_mono_cutoff
          hCutoff.le hrough⟩
      · simp at hn
    have hβPbound : ∀ n ∈ dyadicIntegers (H₂ i), ‖βP n‖ ≤ 1 := by
      intro n hn
      simp [βP, hn, roughIndicator]
      <;> split_ifs <;> norm_num
    have hβBsupport : ∀ n, βB n ≠ 0 →
        n ∈ dyadicIntegers (H₁ i) ∧ roughAbove n (roughCutoff x) := by
      intro n hn
      dsimp [βB] at hn
      split_ifs at hn with hmem
      · have hR : roughProxy x gamma n ≠ 0 := by exact_mod_cast hn
        have hEq := hProxyEq (H₁ i) hH₁lo hH₁hi n hmem
        rw [hEq] at hR
        by_cases hrough : roughAbove n (roughCutoff x)
        · exact ⟨hmem, hrough⟩
        · simp [hrough] at hR
      · simp at hn
    have hβBbound : ∀ n ∈ dyadicIntegers (H₁ i), ‖βB n‖ ≤ 1 := by
      intro n hn
      simp only [βB, if_pos hn]
      have hB := hProxyLeOne (H₁ i) hH₁lo hH₁hi n hn
      have hAbs : |roughProxy x gamma n| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hB.1], hB.2⟩
      simpa using hAbs
    have hβPval : ∀ n ∈ dyadicIntegers (H₂ i), βP n = (P n : ℂ) := by
      intro n hn
      simp [βP, P, hn]
    have hβBval : ∀ n ∈ dyadicIntegers (H₁ i), βB n = (Bp n : ℂ) := by
      intro n hn
      simp [βB, Bp, hn]
    let z₁ : ℂ :=
      ∑ m ∈ D₁,
        ∑ n ∈ dyadicIntegers (H₂ i),
          ((roughIndicator x (2 / 5) m - roughProxy x (2 / 5) m : ℝ) : ℂ) *
            βP n * (conWeight x M c u K a Ψ (m * n) : ℂ)
    let z₂ : ℂ :=
      ∑ m ∈ D₂,
        ∑ n ∈ dyadicIntegers (H₁ i),
          ((roughIndicator x (2 / 5) m - roughProxy x (2 / 5) m : ℝ) : ℂ) *
            βB n * (conWeight x M c u K a Ψ (m * n) : ℂ)
    have hz₁Eq : z₁ = (E₁ i : ℂ) := by
      calc
        z₁ = ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
            (((P m - Bp m) * P n * conWeight x M c u K a Ψ (m * n) : ℝ) : ℂ) := by
          dsimp [z₁]
          rw [hD₁]
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          rw [hβPval n hn]
          simp only [Complex.ofReal_sub, Complex.ofReal_mul]
          ring
        _ = (E₁ i : ℂ) := by
          dsimp [E₁]
          simp only [Complex.ofReal_sum]
    have hz₂Eq : z₂ = (E₂ i : ℂ) := by
      calc
        z₂ = ∑ m ∈ dyadicIntegers (H₂ i), ∑ n ∈ dyadicIntegers (H₁ i),
            (((P m - Bp m) * Bp n * conWeight x M c u K a Ψ (m * n) : ℝ) : ℂ) := by
          dsimp [z₂]
          rw [hD₂]
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          rw [hβBval n hn]
          simp only [Complex.ofReal_sub, Complex.ofReal_mul]
          ring
        _ = (E₂ i : ℂ) := by
          dsimp [E₂]
          simp only [Complex.ofReal_sum]
    refine ⟨z₁, z₂, hz₁Eq, hz₂Eq, ?_, ?_⟩
    ·
      have hprodlo' : (1 / 4 : ℝ) * x ≤ H₁ i * H₂ i := by nlinarith [hprodlo]
      simpa [z₁, D₁] using hTypeAt x hxType (H₁ i) (H₂ i) hδH₁ hδH₂ hprodlo' hprodupp
        hscale₁.1 hscale₁.2 I₁ hI₁ hI₁sub βP hβPsupport hβPbound
    ·
      have hprodlo' : (1 / 4 : ℝ) * x ≤ H₂ i * H₁ i := by nlinarith [hprodlo]
      have hprodupp' : H₂ i * H₁ i ≤ 2 * x := by nlinarith [hprodupp]
      simpa [z₂, D₂] using hTypeAt x hxType (H₂ i) (H₁ i) hδH₂ hδH₁ hprodlo' hprodupp'
        hscale₂.1 hscale₂.2 I₂ hI₂ hI₂sub βB hβBsupport hβBbound
  choose z₁ z₂ hZ₁Eq hZ₂Eq hZ₁Bound hZ₂Bound using hTypeErrors
  have hE₁Abs (i : Fin N) : |E₁ i| ≤
      Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) := by
    have h := hZ₁Bound i
    rw [hZ₁Eq i] at h
    simpa using h
  have hE₂Abs (i : Fin N) : |E₂ i| ≤
      Ctype * (H₂ i * H₁ i) * Real.rpow (Real.log x) (-6 : ℝ) := by
    have h := hZ₂Bound i
    rw [hZ₂Eq i] at h
    simpa using h
  let w : ℕ → ℝ := conWeight x M c u K a Ψ
  have hWeightNonneg (d : ℕ) : 0 ≤ w d := by
    have h := hSupportAt x hxSupport
    exact (h.2.2 d).1
  let rawPairBox : Fin N → ℝ := fun i =>
    ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
      P m * P n * w (m * n)
  let proxyPairBox : Fin N → ℝ := fun i =>
    ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
      Bp m * Bp n * w (m * n)
  have hE₂reorder (i : Fin N) : E₂ i =
      ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
        Bp m * (P n - Bp n) * w (m * n) := by
    dsimp [E₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.mul_comm n m]
    ring
  have hPairIdentity (i : Fin N) :
      rawPairBox i - proxyPairBox i = E₁ i + E₂ i := by
    rw [hE₂reorder]
    dsimp [rawPairBox, proxyPairBox, E₁, P, Bp, w]
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  let scale : ℝ := 1 / (roughSieveProduct (roughCutoff x) * (qfun x * Real.log x))
  have hscalePos : 0 < scale := by
    dsimp [scale]
    positivity
  have hProxyPairBound (i : Fin N) :
      proxyPairBox i ≤ scale ^ 2 * roughPairBoxSum x M c u K a Ψ (H₁ i) (H₂ i) := by
    rcases hBoxBounds i with ⟨hprodlo, hprodupp, hH₁lo, hH₁hi, hH₂lo, hH₂hi⟩
    have hterm (m : ℕ) (hm : m ∈ dyadicIntegers (H₁ i))
        (n : ℕ) (hn : n ∈ dyadicIntegers (H₂ i)) :
        Bp m * Bp n * w (m * n) ≤ scale ^ 2 *
          (if roughAbove m (roughCutoff x) ∧ roughAbove n (roughCutoff x)
            then w (m * n) else 0) := by
      by_cases hmrough : roughAbove m (roughCutoff x)
      · by_cases hnrough : roughAbove n (roughCutoff x)
        · have hBm := hProxyLeScale (H₁ i) hH₁lo hH₁hi m hm
          have hBn := hProxyLeScale (H₂ i) hH₂lo hH₂hi n hn
          have hBnonneg := (hProxyLeOne (H₂ i) hH₂lo hH₂hi n hn).1
          have hmult : Bp m * Bp n ≤ scale * scale :=
            mul_le_mul hBm hBn hBnonneg hscalePos.le
          have hw := hWeightNonneg (m * n)
          calc
            _ ≤ (scale * scale) * w (m * n) := mul_le_mul_of_nonneg_right hmult hw
            _ = scale ^ 2 * (if roughAbove m (roughCutoff x) ∧
                roughAbove n (roughCutoff x) then w (m * n) else 0) := by
                  simp [hmrough, hnrough, pow_two]
        · have hBnZero : Bp n = 0 := by
            dsimp [Bp]
            rw [hProxyEq (H₂ i) hH₂lo hH₂hi n hn]
            simp [hnrough]
          simp [hnrough, hBnZero]
      · have hBmZero : Bp m = 0 := by
          dsimp [Bp]
          rw [hProxyEq (H₁ i) hH₁lo hH₁hi m hm]
          simp [hmrough]
        simp [hmrough, hBmZero]
    calc
      proxyPairBox i ≤
          ∑ m ∈ dyadicIntegers (H₁ i), ∑ n ∈ dyadicIntegers (H₂ i),
            scale ^ 2 *
              (if roughAbove m (roughCutoff x) ∧ roughAbove n (roughCutoff x)
                then w (m * n) else 0) := by
          dsimp [proxyPairBox]
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro n hn
          exact hterm m hm n hn
      _ = scale ^ 2 * roughPairBoxSum x M c u K a Ψ (H₁ i) (H₂ i) := by
          dsimp [roughPairBoxSum, w]
          simp_rw [← Finset.mul_sum]
  have hPairBoundAt (i : Fin N) :
      roughPairBoxSum x M c u K a Ψ (H₁ i) (H₂ i) ≤
        C₁ * conTotalMass x M c u K a Ψ * roughSieveProduct (roughCutoff x) ^ 2 := by
    rcases hBoxBounds i with ⟨hprodlo, hprodupp, hH₁lo, hH₁hi, hH₂lo, hH₂hi⟩
    exact hPairAt x hxPair (H₁ i) (H₂ i) hprodlo hprodupp hH₁lo hH₁hi hH₂lo hH₂hi
  have hProxyPairUpper (i : Fin N) :
      proxyPairBox i ≤
        (C₁ * conTotalMass x M c u K a Ψ) / (qfun x * Real.log x) ^ 2 := by
    have h := hProxyPairBound i
    have hPair := hPairBoundAt i
    have hmassNonneg : 0 ≤ conTotalMass x M c u K a Ψ := by
      have hWeights := hSupportAt x hxSupport |>.2.2
      unfold conTotalMass
      apply Finset.sum_nonneg
      intro d hd
      exact hWeights d |>.1
    calc
      proxyPairBox i ≤ scale ^ 2 * roughPairBoxSum x M c u K a Ψ (H₁ i) (H₂ i) := h
      _ ≤ scale ^ 2 *
          (C₁ * conTotalMass x M c u K a Ψ * roughSieveProduct (roughCutoff x) ^ 2) :=
        mul_le_mul_of_nonneg_left hPair (sq_nonneg scale)
      _ = (C₁ * conTotalMass x M c u K a Ψ) / (qfun x * Real.log x) ^ 2 := by
        dsimp [scale]
        field_simp [ne_of_gt hVpos, ne_of_gt hqPos, ne_of_gt hLpos]
        <;> ring
  have hRawPairUpper (i : Fin N) :
      rawPairBox i ≤
        (C₁ * conTotalMass x M c u K a Ψ) / (qfun x * Real.log x) ^ 2 +
          4 * Ctype * x * Real.rpow (Real.log x) (-6 : ℝ) := by
    rcases hBoxBounds i with ⟨hprodlo, hprodupp, hH₁lo, hH₁hi, hH₂lo, hH₂hi⟩
    have hEupper : E₁ i + E₂ i ≤ |E₁ i| + |E₂ i| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    have hE₂Abs' : |E₂ i| ≤
        Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) := by
      simpa [mul_comm] using hE₂Abs i
    have hEsmall : E₁ i + E₂ i ≤
        2 * Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) := by
      calc
        _ ≤ |E₁ i| + |E₂ i| := hEupper
        _ ≤ Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) +
              Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) :=
            add_le_add (hE₁Abs i) hE₂Abs'
        _ = _ := by ring
    have hTypeCoefficient :
        2 * Ctype * (H₁ i * H₂ i) ≤ 4 * Ctype * x := by
      calc
        2 * Ctype * (H₁ i * H₂ i) ≤ (2 * Ctype) * (2 * x) :=
          mul_le_mul_of_nonneg_left hprodupp (by positivity)
        _ = 4 * Ctype * x := by ring
    have hTypeErr :
        2 * Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) ≤
          4 * Ctype * x * Real.rpow (Real.log x) (-6 : ℝ) :=
      mul_le_mul_of_nonneg_right hTypeCoefficient
        (Real.rpow_nonneg hLpos.le _)
    calc
      rawPairBox i = proxyPairBox i + (E₁ i + E₂ i) := by linarith [hPairIdentity i]
      _ ≤ proxyPairBox i +
          2 * Ctype * (H₁ i * H₂ i) * Real.rpow (Real.log x) (-6 : ℝ) :=
        by simpa [add_comm] using add_le_add_right hEsmall (proxyPairBox i)
      _ ≤ (C₁ * conTotalMass x M c u K a Ψ) / (qfun x * Real.log x) ^ 2 +
          4 * Ctype * x * Real.rpow (Real.log x) (-6 : ℝ) := by
        exact add_le_add (hProxyPairUpper i) hTypeErr
  have hPrimeRough (p : ℕ) (hp : p.Prime) (hpt :
      Real.rpow x (2 / 5 : ℝ) < (p : ℝ)) :
      roughIndicator x (2 / 5) p = 1 := by
    have hrough := ArtinPrimitiveRoots.Construction.Proofs.C4.roughAbove_of_prime_gt hp hpt
    unfold roughIndicator
    rw [if_pos hrough]
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let compositePred : ℕ → Prop := fun d =>
    roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime
  let A : Finset ℕ := R.filter (fun d => compositePred d ∧ 0 < w d)
  let compositeMass : ℝ := ∑ d ∈ R, if compositePred d then w d else 0
  have hCompositeEq : compositeMass = ∑ d ∈ A, w d := by
    dsimp [compositeMass, A, compositePred]
    calc
      _ = ∑ d ∈ R,
            if (roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime) ∧ 0 < w d
              then w d else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            by_cases hbad : roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime
            · by_cases hpos : 0 < w d
              · simp [hbad, hpos]
              · have hzero : w d = 0 := le_antisymm (le_of_not_gt hpos) (hWeightNonneg d)
                simp [hbad, hpos, hzero]
            · have hbad' :
                  ¬ ((roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime) ∧ 0 < w d) :=
                fun h => hbad h.1
              change (if roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime
                then w d else 0) =
                if (roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime) ∧ 0 < w d
                  then w d else 0
              simp only [if_neg hbad, if_neg hbad']
      _ = ∑ d ∈ R.filter
            (fun d => (roughAbove d (Real.rpow x (1 / 2 - κ)) ∧ ¬ d.Prime) ∧ 0 < w d),
            w d := by
            symm
            rw [Finset.sum_filter]
  have hCoverExist (d : ℕ) (hd : d ∈ A) :
      ∃ v : Fin N × (ℕ × ℕ),
        v.2.1 ∈ dyadicIntegers (H₁ v.1) ∧
        v.2.2 ∈ dyadicIntegers (H₂ v.1) ∧
        (v.2.1).Prime ∧ (v.2.2).Prime ∧ d = v.2.1 * v.2.2 := by
    simp only [A, Finset.mem_filter] at hd
    rcases hd with ⟨_, ⟨hbad, hwd⟩⟩
    rcases hCoverPairs d hwd hbad.1 hbad.2 with
      ⟨i, m, n, hm, hn, hmp, hnp, hEq⟩
    exact ⟨(i, (m, n)), hm, hn, hmp, hnp, hEq⟩
  let chosen (d : ℕ) (hd : d ∈ A) : Fin N × (ℕ × ℕ) :=
    Classical.choose (hCoverExist d hd)
  have hChosen (d : ℕ) (hd : d ∈ A) :
      (chosen d hd).2.1 ∈ dyadicIntegers (H₁ (chosen d hd).1) ∧
      (chosen d hd).2.2 ∈ dyadicIntegers (H₂ (chosen d hd).1) ∧
      ((chosen d hd).2.1).Prime ∧ ((chosen d hd).2.2).Prime ∧
        d = (chosen d hd).2.1 * (chosen d hd).2.2 := by
    exact Classical.choose_spec (hCoverExist d hd)
  let boxFamily (i : Fin N) : Finset (Fin N × (ℕ × ℕ)) :=
    ((dyadicIntegers (H₁ i)).product (dyadicIntegers (H₂ i))).image
      (fun mn => (i, mn))
  let boxUnion : Finset (Fin N × (ℕ × ℕ)) :=
    Finset.univ.biUnion boxFamily
  let pairWeight (v : Fin N × (ℕ × ℕ)) : ℝ :=
    P v.2.1 * P v.2.2 * w (v.2.1 * v.2.2)
  let B : Finset (Option (Fin N × (ℕ × ℕ))) := boxUnion.image some
  let f (d : ℕ) : Option (Fin N × (ℕ × ℕ)) :=
    if hd : d ∈ A then some (chosen d hd) else none
  let wb (v : Option (Fin N × (ℕ × ℕ))) : ℝ :=
    v.elim 0 pairWeight
  have hBoxDisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)) boxFamily := by
    intro i hi j hj hij
    change Disjoint (boxFamily i) (boxFamily j)
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    change v ∈ ((dyadicIntegers (H₁ i)).product (dyadicIntegers (H₂ i))).image
      (fun mn => (i, mn)) at hvi
    change v ∈ ((dyadicIntegers (H₁ j)).product (dyadicIntegers (H₂ j))).image
      (fun mn => (j, mn)) at hvj
    obtain ⟨mn, _, hmn⟩ := Finset.mem_image.mp hvi
    obtain ⟨mn', _, hmn'⟩ := Finset.mem_image.mp hvj
    have hij' : i = j := by
      have hEq : (i, mn) = (j, mn') := hmn.trans hmn'.symm
      exact congrArg Prod.fst hEq
    exact hij hij'
  have hFamilyInjective (i : Fin N) : Set.InjOn (fun mn => (i, mn))
      (↑((dyadicIntegers (H₁ i)).product (dyadicIntegers (H₂ i))) : Set (ℕ × ℕ)) := by
    intro mn hmn mn' hmn' hEq
    exact congrArg Prod.snd hEq
  have hBoxUnionSum :
      (∑ v ∈ boxUnion, pairWeight v) = ∑ i : Fin N, rawPairBox i := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset (Fin N)),
            ∑ mn ∈ (dyadicIntegers (H₁ i)).product (dyadicIntegers (H₂ i)),
              pairWeight (i, mn) := by
          dsimp [boxUnion]
          rw [Finset.sum_biUnion hBoxDisjoint]
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [boxFamily]
          exact Finset.sum_image (hFamilyInjective j)
      _ = ∑ i : Fin N, rawPairBox i := by
          simp [Finset.sum_product, pairWeight, rawPairBox, P, w]
  have hCoverMap (d : ℕ) (hd : d ∈ A) : f d ∈ B := by
    have hv := hChosen d hd
    have hfd : f d = some (chosen d hd) := by simp [f, hd]
    rw [hfd]
    apply Finset.mem_image.mpr
    refine ⟨chosen d hd, ?_, rfl⟩
    change chosen d hd ∈ Finset.univ.biUnion boxFamily
    rw [Finset.mem_biUnion]
    refine ⟨(chosen d hd).1, Finset.mem_univ _, ?_⟩
    change chosen d hd ∈ boxFamily (chosen d hd).1
    dsimp [boxFamily]
    apply Finset.mem_image.mpr
    refine ⟨(chosen d hd).2, Finset.mem_product.mpr ⟨hv.1, hv.2.1⟩, rfl⟩
  have hinj : Set.InjOn f A := by
    intro d hd e he hde
    change d ∈ A at hd
    change e ∈ A at he
    have hfd : f d = some (chosen d hd) := by
      dsimp [f]
      rw [dif_pos hd]
    have hfe : f e = some (chosen e he) := by
      dsimp [f]
      rw [dif_pos he]
    rw [hfd, hfe] at hde
    have hchosen : chosen d hd = chosen e he := Option.some.inj hde
    calc
      d = (chosen d hd).2.1 * (chosen d hd).2.2 := (hChosen d hd).2.2.2.2
      _ = (chosen e he).2.1 * (chosen e he).2.2 := by rw [hchosen]
      _ = e := (hChosen e he).2.2.2.2.symm
  have hPnonneg (m : ℕ) : 0 ≤ P m := by
    dsimp [P, roughIndicator]
    split_ifs <;> norm_num
  have hBound (d : ℕ) (hd : d ∈ A) : w d ≤ wb (f d) := by
    have hv := hChosen d hd
    have hmLarge : Real.rpow x (2 / 5 : ℝ) < ((chosen d hd).2.1 : ℝ) := by
      rcases hBoxBounds (chosen d hd).1 with ⟨_, _, hHlo, _, _, _⟩
      have hmBounds :=
        ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₁ (chosen d hd).1) hv.1
      have hmLower :=
        ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff
          (H₁ (chosen d hd).1) (chosen d hd).2.1 |>.mp hmBounds
      exact lt_of_lt_of_le
        (ArtinPrimitiveRoots.Construction.Proofs.C4.two_fifths_lt_dyadic_lower
          hxlarge hLlarge) (hHlo.trans hmLower.1)
    have hnLarge : Real.rpow x (2 / 5 : ℝ) < ((chosen d hd).2.2 : ℝ) := by
      rcases hBoxBounds (chosen d hd).1 with ⟨_, _, _, _, hHlo, _⟩
      have hnBounds :=
        ArtinPrimitiveRoots.Construction.Proofs.C4.dyadicIntegers_subset_coordinateInterval
          (H₂ (chosen d hd).1) hv.2.1
      have hnLower :=
        ArtinPrimitiveRoots.Construction.Proofs.C4.mem_dyadicCoordinateInterval_iff
          (H₂ (chosen d hd).1) (chosen d hd).2.2 |>.mp hnBounds
      exact lt_of_lt_of_le
        (ArtinPrimitiveRoots.Construction.Proofs.C4.two_fifths_lt_dyadic_lower
          hxlarge hLlarge) (hHlo.trans hnLower.1)
    have hPm : P (chosen d hd).2.1 = 1 := by
      change roughIndicator x (2 / 5 : ℝ) (chosen d hd).2.1 = 1
      exact hPrimeRough _ hv.2.2.1 hmLarge
    have hPn : P (chosen d hd).2.2 = 1 := by
      change roughIndicator x (2 / 5 : ℝ) (chosen d hd).2.2 = 1
      exact hPrimeRough _ hv.2.2.2.1 hnLarge
    have hfd : f d = some (chosen d hd) := by simp [f, hd]
    rw [hfd]
    simp only [wb, Option.elim_some]
    dsimp [pairWeight]
    rw [hPm, hPn, ← hv.2.2.2.2]
    simp
  have hBnonneg (v : Option (Fin N × (ℕ × ℕ))) (hv : v ∈ B) : 0 ≤ wb v := by
    change v ∈ boxUnion.image some at hv
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
    simp only [wb, Option.elim_some]
    dsimp [pairWeight]
    exact mul_nonneg (mul_nonneg (hPnonneg _) (hPnonneg _)) (hWeightNonneg _)
  have hCompositeBox : (∑ d ∈ A, w d) ≤ ∑ v ∈ B, wb v :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.finite_sum_le_superset_of_injective
      A B f w wb hinj hCoverMap hBound hBnonneg
  have hBoxWeightedSum : (∑ v ∈ B, wb v) = ∑ i : Fin N, rawPairBox i := by
    calc
      _ = ∑ v ∈ boxUnion, wb (some v) := by
        dsimp [B]
        exact Finset.sum_image (by
          intro v hv v' hv' hEq
          exact Option.some.inj hEq)
      _ = ∑ v ∈ boxUnion, pairWeight v := by simp [wb]
      _ = ∑ i : Fin N, rawPairBox i := hBoxUnionSum
  let L : ℝ := Real.log x
  let mass : ℝ := conTotalMass x M c u K a Ψ
  let Acoef : ℝ := C₁ * Cdyad
  let kappaPlusInvL : ℝ := κ + 1 / L
  have hLpos' : 0 < L := by simpa [L] using hLpos
  have hxpos' : 0 < x := by linarith
  have hmassNonnegFinal : 0 ≤ mass := by
    dsimp [mass, conTotalMass]
    apply Finset.sum_nonneg
    intro d hd
    exact hWeightNonneg d
  have hJ₀ : 1 ≤ groupHarmonicMass x K a := (hHarmonic x hxMass).2.1
  have hmassLower : c₀ * x / L ≤ mass := by
    have hnum : c₀ * x * 1 ≤ c₀ * x * groupHarmonicMass x K a :=
      mul_le_mul_of_nonneg_left hJ₀ (mul_nonneg hc₀.le (by linarith))
    calc
      c₀ * x / L = c₀ * x * 1 / L := by ring
      _ ≤ c₀ * x * groupHarmonicMass x K a / L :=
        div_le_div_of_nonneg_right hnum hLpos.le
      _ ≤ conTotalMass x M c u K a Ψ := (hMass x hxDistribution).1
      _ = mass := by rfl
  have hmassOverL : c₀ * x / L ^ 2 ≤ mass / L := by
    have h := div_le_div_of_nonneg_right hmassLower hLpos.le
    calc
      c₀ * x / L ^ 2 = (c₀ * x / L) / L := by field_simp [ne_of_gt hLpos]
      _ ≤ mass / L := h
  have hLbig : 200 ≤ L := by simpa [L] using hLlarge
  have hcountBound : κ * L + 1 ≤ 2 * L := by
    have hκL : κ * L ≤ L / 100 := by
      calc
        κ * L ≤ (1 / 100 : ℝ) * L :=
          mul_le_mul_of_nonneg_right (le_of_lt hκsmall) hLpos'.le
        _ = L / 100 := by ring
    have hOne : (1 : ℝ) ≤ L / 200 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 200)).2
      nlinarith [hLbig]
    nlinarith [hκL, hOne, hLbig]
  have hInvL : 1 / L ≤ 1 / 200 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith [hLbig]
  have hkappaPlusNonneg : 0 ≤ kappaPlusInvL := by
    dsimp [kappaPlusInvL]
    positivity
  have hkappaPlusLeOne : kappaPlusInvL ≤ 1 := by
    dsimp [kappaPlusInvL]
    linarith [hκsmall, hInvL]
  have hPerBoxNonneg :
      0 ≤ C₁ * mass / (qfun x * L) ^ 2 +
        4 * Ctype * x * Real.rpow L (-6 : ℝ) := by
    apply add_nonneg
    · exact div_nonneg (mul_nonneg hC₁.le hmassNonnegFinal) (sq_nonneg _)
    · exact mul_nonneg (by positivity)
        (Real.rpow_nonneg hLpos'.le (-6 : ℝ))
  have hSummed :
      compositeMass ≤ Cdyad * (κ * L + 1) *
        (C₁ * mass / (qfun x * L) ^ 2 +
          4 * Ctype * x * Real.rpow L (-6 : ℝ)) := by
    have hRaw :
        compositeMass ≤ (N : ℝ) *
          (C₁ * mass / (qfun x * L) ^ 2 +
            4 * Ctype * x * Real.rpow L (-6 : ℝ)) := by
      calc
        compositeMass = ∑ d ∈ A, w d := hCompositeEq
        _ ≤ ∑ v ∈ B, wb v := hCompositeBox
        _ = ∑ i : Fin N, rawPairBox i := hBoxWeightedSum
        _ ≤ ∑ i : Fin N,
              (C₁ * mass / (qfun x * L) ^ 2 +
                4 * Ctype * x * Real.rpow L (-6 : ℝ)) := by
              apply Finset.sum_le_sum
              intro i hi
              simpa [mass, L] using hRawPairUpper i
        _ = (N : ℝ) *
              (C₁ * mass / (qfun x * L) ^ 2 +
                4 * Ctype * x * Real.rpow L (-6 : ℝ)) := by
              simp [Finset.sum_add_distrib]
              <;> ring
    calc
      compositeMass ≤ (N : ℝ) *
          (C₁ * mass / (qfun x * L) ^ 2 +
            4 * Ctype * x * Real.rpow L (-6 : ℝ)) := hRaw
      _ ≤ Cdyad * (κ * L + 1) *
            (C₁ * mass / (qfun x * L) ^ 2 +
              4 * Ctype * x * Real.rpow L (-6 : ℝ)) :=
          mul_le_mul_of_nonneg_right hNbound hPerBoxNonneg
  have hSummedRewrite :
      Cdyad * (κ * L + 1) *
          (C₁ * mass / (qfun x * L) ^ 2 +
            4 * Ctype * x * Real.rpow L (-6 : ℝ)) =
        Acoef * kappaPlusInvL * (qfun x)⁻¹ ^ 2 * mass / L +
          Cdyad * (κ * L + 1) * 4 * Ctype * x * Real.rpow L (-6 : ℝ) := by
    dsimp [Acoef, kappaPlusInvL, L]
    field_simp [ne_of_gt hLpos, ne_of_gt hqPos]
    <;> ring
  have hSummedRaw :
      compositeMass ≤
        Acoef * kappaPlusInvL * (qfun x)⁻¹ ^ 2 * mass / L +
          Cdyad * (κ * L + 1) * 4 * Ctype * x * Real.rpow L (-6 : ℝ) :=
    hSummed.trans_eq hSummedRewrite
  have hqSquareBound :
      (qfun x)⁻¹ ^ 2 ≤ (46 / 100 : ℝ)⁻¹ ^ 2 + ηcoeff := by
    have h := hxCoeff x hxCoeff'
    linarith
  have hCoeffAbsorb : Acoef * kappaPlusInvL * ηcoeff ≤ η / 2 := by
    have hA : 0 ≤ Acoef := by dsimp [Acoef]; positivity
    have hAk : Acoef * kappaPlusInvL ≤ Acoef := by
      simpa using mul_le_mul_of_nonneg_left hkappaPlusLeOne hA
    have hAkη : Acoef * kappaPlusInvL * η ≤ Acoef * η :=
      mul_le_mul_of_nonneg_right hAk hη.le
    have hden : 0 < 4 * (C₁ * Cdyad + 1) := by positivity
    dsimp [Acoef, ηcoeff]
    field_simp [ne_of_gt hden]
    nlinarith [hAkη]
  have hProxyBudget :
      Acoef * kappaPlusInvL * (qfun x)⁻¹ ^ 2 * mass / L ≤
        ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + (η / 2) * mass / L := by
    have hfactor : 0 ≤ Acoef * kappaPlusInvL * mass / L := by positivity
    calc
      _ = (Acoef * kappaPlusInvL * mass / L) * (qfun x)⁻¹ ^ 2 := by ring
      _ ≤ (Acoef * kappaPlusInvL * mass / L) *
            ((46 / 100 : ℝ)⁻¹ ^ 2 + ηcoeff) :=
          mul_le_mul_of_nonneg_left hqSquareBound hfactor
      _ = ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L +
            (Acoef * kappaPlusInvL * ηcoeff) * (mass / L) := by
          dsimp [Acoef]
          ring
      _ ≤ ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + (η / 2) * (mass / L) := by
          let baseTerm :=
            ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) * kappaPlusInvL * mass / L
          have hterm := mul_le_mul_of_nonneg_right hCoeffAbsorb
            (div_nonneg hmassNonnegFinal hLpos'.le)
          calc
            _ = (Acoef * kappaPlusInvL * ηcoeff * (mass / L)) + baseTerm := by
              dsimp [baseTerm]
              ring
            _ ≤ (η / 2) * (mass / L) + baseTerm :=
              add_le_add_left hterm baseTerm
            _ = baseTerm + (η / 2) * (mass / L) := by ring
      _ = ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + (η / 2) * mass / L := by ring
  have hErrCount :
      Cdyad * (κ * L + 1) * 4 * Ctype * x * Real.rpow L (-6 : ℝ) ≤
        8 * Ctype * Cdyad * x * Real.rpow L (-5 : ℝ) := by
    have hcoeff := mul_le_mul_of_nonneg_left hcountBound hCdyad.le
    calc
      _ = (Cdyad * (κ * L + 1)) *
          (4 * Ctype * x * Real.rpow L (-6 : ℝ)) := by ring
      _ ≤ (Cdyad * (2 * L)) *
          (4 * Ctype * x * Real.rpow L (-6 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (by
            exact mul_nonneg (by positivity)
              (Real.rpow_nonneg hLpos'.le (-6 : ℝ)))
      _ = 8 * Ctype * Cdyad * x * Real.rpow L (-5 : ℝ) := by
          have hpow : L * Real.rpow L (-6 : ℝ) = Real.rpow L (-5 : ℝ) := by
            calc
              _ = Real.rpow L 1 * Real.rpow L (-6 : ℝ) := by simp
              _ = Real.rpow L (1 + (-6 : ℝ)) := (Real.rpow_add hLpos _ _).symm
              _ = Real.rpow L (-5 : ℝ) := by congr 1 <;> norm_num
          calc
            _ = 8 * Ctype * Cdyad * x *
                (L * Real.rpow L (-6 : ℝ)) := by ring
            _ = _ := by rw [hpow]
  have hpowCombine : L ^ 2 * Real.rpow L (-5 : ℝ) = Real.rpow L (-3 : ℝ) := by
    have hRpow2 : Real.rpow L (2 : ℝ) = L ^ 2 := Real.rpow_natCast L 2
    calc
      _ = Real.rpow L (2 : ℝ) * Real.rpow L (-5 : ℝ) := by
        rw [← hRpow2]
      _ = Real.rpow L ((2 : ℝ) + (-5 : ℝ)) := (Real.rpow_add hLpos' _ _).symm
      _ = Real.rpow L (-3 : ℝ) := by congr 1 <;> norm_num
  have hErrScale :
      16 * Ctype * Cdyad * Real.rpow L (-3 : ℝ) < c₀ * η := by
    have h := hxError x hxError'
    have h' : Real.rpow L (-3 : ℝ) < c₀ * η / (16 * Ctype * Cdyad) := by
      simpa [L, ηerror] using h
    have hden : 0 < 16 * Ctype * Cdyad := by positivity
    have hmul := (lt_div_iff₀ hden).1 h'
    nlinarith [hmul]
  have hErrDirect :
      8 * Ctype * Cdyad * x * Real.rpow L (-5 : ℝ) ≤
        (η / 2) * (c₀ * x / L ^ 2) := by
    rw [show (η / 2) * (c₀ * x / L ^ 2) = (η * c₀ * x) / (2 * L ^ 2) by
      field_simp [ne_of_gt hLpos]
      <;> ring]
    apply (le_div_iff₀ (by positivity : 0 < 2 * L ^ 2)).2
    have hmul := mul_lt_mul_of_pos_right hErrScale (by linarith : 0 < x)
    have hmul' :
        16 * Ctype * Cdyad * x * (L ^ 2 * Real.rpow L (-5 : ℝ)) ≤
          c₀ * η * x := by
      rw [hpowCombine]
      nlinarith [hmul]
    calc
      8 * Ctype * Cdyad * x * Real.rpow L (-5 : ℝ) * (2 * L ^ 2) =
          16 * Ctype * Cdyad * x * (L ^ 2 * Real.rpow L (-5 : ℝ)) := by ring
      _ ≤ c₀ * η * x := hmul'
      _ = η * c₀ * x := by ring
  have hErrBudget :
      Cdyad * (κ * L + 1) * 4 * Ctype * x * Real.rpow L (-6 : ℝ) ≤
        (η / 2) * mass / L := by
    calc
      _ ≤ 8 * Ctype * Cdyad * x * Real.rpow L (-5 : ℝ) := hErrCount
      _ ≤ (η / 2) * (c₀ * x / L ^ 2) := hErrDirect
      _ ≤ (η / 2) * (mass / L) :=
        mul_le_mul_of_nonneg_left hmassOverL (by positivity)
      _ = (η / 2) * mass / L := by ring
  have hFinalBound :
      compositeMass ≤
        ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + η * mass / L := by
    calc
      compositeMass ≤
          Acoef * kappaPlusInvL * (qfun x)⁻¹ ^ 2 * mass / L +
            Cdyad * (κ * L + 1) * 4 * Ctype * x * Real.rpow L (-6 : ℝ) :=
        hSummedRaw
      _ ≤ (((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + (η / 2) * mass / L) +
            (η / 2) * mass / L := add_le_add hProxyBudget hErrBudget
      _ = ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
            kappaPlusInvL * mass / L + η * mass / L := by ring
  change compositeMass ≤
    ((46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad) *
      (κ + 1 / Real.log x) * conTotalMass x M c u K a Ψ / Real.log x +
      η * conTotalMass x M c u K a Ψ / Real.log x
  simpa [L, mass, kappaPlusInvL] using hFinalBound

set_option maxHeartbeats 8000000 in
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
  classical
  let Ψ : ℝ → ℝ := c4TestFunction
  have hΨ : IsTestFunction Ψ := by
    simpa [Ψ] using c4TestFunction_isTestFunction
  obtain ⟨C₁, hC₁, hRoughPairs⟩ := con_rough_pairs M Ψ hM0 hΨ
  have hPairs : HasRoughPairBound M Ψ C₁ := by
    intro c' hc' u' K' a' ha'
    exact hRoughPairs c' hc' u' K' a' ha'
  obtain ⟨Cdyad, hCdyad, hBoxes⟩ := balanced_boxes
  have hCover : HasBalancedBoxCover Cdyad := by
    unfold HasBalancedBoxCover
    exact hBoxes
  obtain ⟨C_s, C_d, b₂, hCs, hCd, hb₂, hDensityNode⟩ := density_partition
  have hS : 0 < singularProduct M := (sieve_products M hM0).1
  let E : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hE : 0 < E := by positivity
  let C₂ : ℝ := (46 / 100 : ℝ)⁻¹ ^ 2 * C₁ * Cdyad
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  let κ : ℝ := min (1 / 200) (singularProduct M / (8 * (C₂ + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκsmall : κ < 1 / 100 := by
    have hκle : κ ≤ 1 / 200 := min_le_left _ _
    linarith
  have hκC₂ : C₂ * κ < singularProduct M / 4 := by
    have hden : 0 < 8 * (C₂ + 1) := by positivity
    have hκle : κ ≤ singularProduct M / (8 * (C₂ + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ hden).mp hκle
    nlinarith [hmul, hS]
  obtain ⟨b, hb, hbb₂, hbk, hbsmall, hSmallError⟩ :=
    ArtinPrimitiveRoots.Construction.exists_small_completion_b
      C_s C_d b₂ κ E hCs hCd hb₂ hκ hκsmall hE
  have hcM : c ∣ M := by
    rcases hc with hc2 | hc4
    · subst c
      exact dvd_trans (by norm_num : 2 ∣ 8) hM
    · subst c
      exact dvd_trans (by norm_num : 4 ∣ 8) hM
  obtain ⟨Kden, hDensityK⟩ :=
    hDensityNode M c u κ hM0 hM hc hcM hu hcu hcu' hκ hκsmall
      b hb hbb₂ hbk
  obtain ⟨Kbal, hBalancedK⟩ :=
    balanced_cost M Ψ C₁ Cdyad hM0 hM hΨ hC₁ hCdyad hPairs hCover
      c hc hcM u κ b hκ hκsmall hb hu hcu hcu'
  let K : ℕ := max 1 (max Kden Kbal)
  have hK : 0 < K := by dsimp [K]; omega
  have hKden : Kden ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left Kden Kbal) (le_max_right 1 (max Kden Kbal))
  have hKbal : Kbal ≤ K := by
    dsimp [K]
    exact le_trans (le_max_right Kden Kbal) (le_max_right 1 (max Kden Kbal))
  let a : Fin K → ℝ := fun i =>
    (1 / 10 : ℝ) + (1 / 10 : ℝ) *
      (((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ))
  have ha : ValidBands K a := by
    refine ⟨hK, ?_, ?_⟩
    · intro i
      have hnumPos : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos i.val
      have hnumLtNat : i.val + 1 < K + 1 := by omega
      have hnumLt : ((i.val + 1 : ℕ) : ℝ) < ((K + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnumLtNat
      have hdenPos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos K
      have hratioPos : 0 < ((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) :=
        div_pos hnumPos hdenPos
      have hratioLt : ((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) < 1 :=
        (div_lt_one hdenPos).2 hnumLt
      have hprodPos : 0 < (1 / 10 : ℝ) *
          (((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) :=
        mul_pos (by norm_num) hratioPos
      have hprodLt : (1 / 10 : ℝ) *
          (((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) < 1 / 10 := by
        simpa only [mul_one] using
          (mul_lt_mul_of_pos_left hratioLt
            (by norm_num : (0 : ℝ) < 1 / 10))
      have hLower : (1 / 10 : ℝ) < a i := by
        dsimp [a]
        simpa using add_lt_add_right hprodPos (1 / 10 : ℝ)
      have hUpper : a i < 1 / 5 := by
        dsimp [a]
        calc
          _ < (1 / 10 : ℝ) + 1 / 10 := by
            simpa using add_lt_add_right hprodLt (1 / 10 : ℝ)
          _ = 1 / 5 := by norm_num
      exact ⟨hLower, hUpper⟩
    · intro i j hij
      have hij' : ((i.val + 1 : ℕ) : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by
        have hijNat : i.val + 1 < j.val + 1 := by omega
        exact_mod_cast hijNat
      have hdenPos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos K
      have hratio :
          ((i.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) <
            ((j.val + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) :=
        div_lt_div_of_pos_right hij' hdenPos
      dsimp [a]
      nlinarith
  have hε : 0 < κ / 2 := by positivity
  have hεκ : κ / 2 < κ := by linarith
  obtain ⟨c₀, C₀, hc₀, hC₀, hDistribution⟩ := con_distribution M Ψ hM0 hΨ
  obtain ⟨xDistribution, hxDistribution₂, hDistributionErrors, hMass⟩ :=
    hDistribution c hc hcM u hu hcu hcu' K a ha (κ / 2) κ hε hεκ hκsmall
  have hcpos : 0 < c := by rcases hc with h | h <;> simp [h]
  obtain ⟨Cmass, xMass, hCmass, hxMass₂, hHarmonic⟩ :=
    con_harmonic M c u Ψ K a hM0 hcpos ha hΨ
  obtain ⟨B, xSupport, hB, hxSupport₂, hSupport⟩ :=
    support M c u K a Ψ hM0 hc ha hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1
  have hηdensity : 0 < (1 / 20 : ℝ) := by norm_num
  obtain ⟨J, γ, hγ0, hγend, hγstrict, hBudget, hIntegral, hDensityAfter⟩ :=
    hDensityK K hKden a ha Ψ hΨ
  obtain ⟨xDensity, hxDensity₂, hDensityMass⟩ :=
    hDensityAfter (1 / 20 : ℝ) hηdensity
  let ηbalanced : ℝ := singularProduct M / 20
  have hηbalanced : 0 < ηbalanced := by dsimp [ηbalanced]; positivity
  obtain ⟨xBalanced, hxBalanced₂, hCompositeBound⟩ :=
    hBalancedK K hKbal a ha ηbalanced hηbalanced
  let Lthreshold : ℝ := max 4096 (20 * C₂ / singularProduct M + 1)
  let xScale : ℝ := Real.exp Lthreshold
  let xInner : ℝ := max xDistribution (max xMass (max xDensity xBalanced))
  let xLarge : ℝ := max xSupport xInner
  let X : ℝ := max xScale xLarge
  have hC : 0 < singularProduct M * c₀ / (4 * B) := by positivity
  refine ⟨singularProduct M * c₀ / (4 * B), hC, X, ?_⟩
  intro x hx
  have hxScale : xScale ≤ x := le_trans (le_max_left _ _) hx
  have hxLarge : xLarge ≤ x := le_trans (le_max_right _ _) hx
  have hxSupport : xSupport ≤ x := le_trans (le_max_left _ _) hxLarge
  have hxInner : xInner ≤ x := le_trans (le_max_right _ _) hxLarge
  have hxDistSub : xDistribution ≤ xInner := le_max_left _ _
  have hxMassSub : xMass ≤ xInner :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hxDensitySub : xDensity ≤ xInner :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxBalancedSub : xBalanced ≤ xInner :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxDistribution : xDistribution ≤ x := le_trans hxDistSub hxInner
  have hxMass : xMass ≤ x := le_trans hxMassSub hxInner
  have hxDensity : xDensity ≤ x := le_trans hxDensitySub hxInner
  have hxBalanced : xBalanced ≤ x := le_trans hxBalancedSub hxInner
  have hxpos : 0 < x := by
    have hxScalePos : 0 < xScale := Real.exp_pos _
    exact lt_of_lt_of_le hxScalePos hxScale
  have hxone : 1 < x := by
    have hThresholdLarge : (1 : ℝ) < Lthreshold := by
      have hLarge : (4096 : ℝ) ≤ Lthreshold := by
        dsimp [Lthreshold]
        exact le_max_left _ _
      linarith
    have hScaleOne : 1 < xScale := by
      dsimp [xScale]
      have hExp : Lthreshold + 1 ≤ Real.exp Lthreshold := Real.add_one_le_exp Lthreshold
      linarith
    exact lt_of_lt_of_le hScaleOne (le_trans (le_max_left _ _) hx)
  let L : ℝ := Real.log x
  have hLpos : 0 < L := Real.log_pos hxone
  have hLlarge : 4096 ≤ L := by
    have hLog := Real.log_le_log (Real.exp_pos Lthreshold) hxScale
    have hThr : 4096 ≤ Lthreshold := by dsimp [Lthreshold]; exact le_max_left _ _
    have hlogX : Lthreshold ≤ L := by
      simpa [L, xScale, Real.log_exp] using hLog
    exact hThr.trans hlogX
  have hC₂L : C₂ / L ≤ singularProduct M / 20 := by
    have hratio : 20 * C₂ / singularProduct M < L := by
      have hThr : 20 * C₂ / singularProduct M + 1 ≤ Lthreshold := by
        dsimp [Lthreshold]
        exact le_max_right _ _
      have hLog := Real.log_le_log (Real.exp_pos Lthreshold) hxScale
      have hlogX : Lthreshold ≤ L := by
        simpa [L, xScale, Real.log_exp] using hLog
      linarith [hThr.trans hlogX]
    have hmul := (div_lt_iff₀ hS).1 hratio
    apply (div_le_iff₀ hLpos).2
    nlinarith [hmul]
  have hCutoff : roughCutoff x < Real.rpow x (2 / 5 : ℝ) :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.roughCutoff_lt_two_fifths
      hxone (by linarith [hLlarge])
  have hCutoffX : roughCutoff x < x := by
    calc
      roughCutoff x < Real.rpow x (2 / 5 : ℝ) := hCutoff
      _ < Real.rpow x 1 := Real.rpow_lt_rpow_of_exponent_lt hxone (by norm_num)
      _ = x := by simp [Real.rpow_one]
  let weight : ℕ → ℝ := conWeight x M c u K a Ψ
  have hSupportAt := hSupport x hxSupport
  have hWeightNonneg (d : ℕ) : 0 ≤ weight d := by
    simpa [weight] using (hSupportAt.2.2 d).1
  have hWeightLe (d : ℕ) : weight d ≤ B := by
    simpa [weight] using (hSupportAt.2.2 d).2
  let mass : ℝ := conTotalMass x M c u K a Ψ
  have hmassNonneg : 0 ≤ mass := by
    dsimp [mass, conTotalMass]
    apply Finset.sum_nonneg
    intro d hd
    exact hWeightNonneg d
  have hMassAt := hMass x hxDistribution
  have hJ₀ : 1 ≤ groupHarmonicMass x K a := (hHarmonic x hxMass).2.1
  have hmassLower : c₀ * x / L ≤ mass := by
    have hdistLower :
        c₀ * x * groupHarmonicMass x K a / L ≤ mass := by
      simpa [mass, L] using hMassAt.1
    have hnum : c₀ * x ≤ c₀ * x * groupHarmonicMass x K a := by
      have hmul := mul_le_mul_of_nonneg_left hJ₀ (mul_nonneg hc₀.le hxpos.le)
      simpa using hmul
    calc
      c₀ * x / L = (c₀ * x) / L := rfl
      _ ≤ (c₀ * x * groupHarmonicMass x K a) / L :=
        div_le_div_of_nonneg_right hnum hLpos.le
      _ ≤ mass := hdistLower
  have hmassOverL : c₀ * x / L ^ 2 ≤ mass / L := by
    have h := div_le_div_of_nonneg_right hmassLower hLpos.le
    calc
      c₀ * x / L ^ 2 = (c₀ * x / L) / L := by field_simp [ne_of_gt hLpos]
      _ ≤ mass / L := h
  let y := Real.rpow x (1 / 2 - κ)
  let roughMass := roughConstructionMass x M c u K a Ψ y
  let primeMass : ℝ :=
    ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1), if d.Prime then weight d else 0
  let compositeMass : ℝ :=
    ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
      if roughAbove d y ∧ ¬ d.Prime then weight d else 0
  have hyx : y < x := by
    dsimp [y]
    have hexp : (1 / 2 : ℝ) - κ < 1 := by nlinarith [hκ]
    simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hxone hexp
  have hPrimeRough : ∀ d : ℕ, d.Prime → 0 < weight d → roughAbove d y := by
    intro d hdPrime hdweight
    have hdSupport := hSupportAt.2.1 d (ne_of_gt hdweight)
    intro p hp hpd
    have hpEq : p = d := by
      rcases (Nat.dvd_prime hdPrime).mp hpd with hpOne | hpD
      · exact False.elim (hp.ne_one hpOne)
      · exact hpD
    have hdy : y < (d : ℝ) := lt_trans hyx hdSupport.1
    simpa [hpEq] using hdy
  have hroughSplit : roughMass = primeMass + compositeMass := by
    dsimp [roughMass, primeMass, compositeMass, roughConstructionMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hzero : weight d = 0
    · simp [weight, hzero]
    have hdweight : 0 < weight d := by
      by_contra hn
      have hle : weight d ≤ 0 := le_of_not_gt hn
      exact hzero (le_antisymm hle (hWeightNonneg d))
    by_cases hdPrime : d.Prime
    · have hrough := hPrimeRough d hdPrime hdweight
      simp [hdPrime, hrough, weight]
    · simp [hdPrime, weight]
  have hηdensity : 0 < (1 / 20 : ℝ) := by norm_num
  have hDensityAt := hDensityMass x hxDensity
  have hDenseCoefficient :
      (13 / 20 : ℝ) ≤ 9 / 10 -
        E / b * (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
          C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 1 / 20 := by
    linarith [hSmallError]
  have hDensityLower :
      (13 / 20 : ℝ) * singularProduct M * mass / L ≤ roughMass := by
    have hfactor : 0 ≤ singularProduct M * mass / L := by positivity
    have hDenseAt :
        roughMass ≥ (singularProduct M * mass / L) *
          (9 / 10 - E / b *
            (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
              C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 1 / 20) := by
      simpa [roughMass, mass, L, y] using hDensityAt
    calc
      (13 / 20 : ℝ) * singularProduct M * mass / L =
          (singularProduct M * mass / L) * (13 / 20 : ℝ) := by ring
      _ ≤ (singularProduct M * mass / L) *
          (9 / 10 - E / b *
            (C_s * Real.exp (-(1 / 20 : ℝ) / b) +
              C_d * Real.exp (-(1 / 20 : ℝ) / b)) - 1 / 20) :=
        mul_le_mul_of_nonneg_left hDenseCoefficient hfactor
      _ ≤ roughMass := hDenseAt
  have hBalancedAt := hCompositeBound x hxBalanced
  have hCompCoefficient :
      C₂ * (κ + 1 / L) + ηbalanced ≤ (7 / 20 : ℝ) * singularProduct M := by
    dsimp [ηbalanced]
    rw [show C₂ * (κ + 1 / L) = C₂ * κ + C₂ / L by ring]
    have hcoef := add_le_add hκC₂.le hC₂L
    calc
      (C₂ * κ + C₂ / L) + singularProduct M / 20 ≤
          (singularProduct M / 4 + singularProduct M / 20) + singularProduct M / 20 :=
        by linarith [hcoef]
      _ = (7 / 20 : ℝ) * singularProduct M := by ring
  have hCompositeUpper :
      compositeMass ≤ (7 / 20 : ℝ) * singularProduct M * mass / L := by
    have hfactor : 0 ≤ mass / L := by positivity
    have hcomp : compositeMass ≤
        C₂ * (κ + 1 / L) * mass / L + ηbalanced * mass / L := by
      simpa [compositeMass, mass, L, C₂, weight, y] using hBalancedAt
    have hcomp' : compositeMass ≤
        (C₂ * (κ + 1 / L) + ηbalanced) * (mass / L) := by
      calc
        compositeMass ≤
            C₂ * (κ + 1 / L) * mass / L + ηbalanced * mass / L := hcomp
        _ = (C₂ * (κ + 1 / L) + ηbalanced) * (mass / L) := by
          field_simp [ne_of_gt hLpos]
          <;> ring
    calc
      compositeMass ≤ (C₂ * (κ + 1 / L) + ηbalanced) * (mass / L) := hcomp'
      _ ≤ ((7 / 20 : ℝ) * singularProduct M) * (mass / L) :=
        mul_le_mul_of_nonneg_right hCompCoefficient hfactor
      _ = (7 / 20 : ℝ) * singularProduct M * mass / L := by ring
  have hPrimeMassLower :
      (3 / 10 : ℝ) * (singularProduct M * (mass / L)) ≤ primeMass := by
    let roughScale : ℝ := singularProduct M * (mass / L)
    have hDensityScale : (13 / 20 : ℝ) * roughScale ≤ roughMass := by
      convert hDensityLower using 1 <;> dsimp [roughScale] <;> ring
    have hCompositeScale : compositeMass ≤ (7 / 20 : ℝ) * roughScale := by
      convert hCompositeUpper using 1 <;> dsimp [roughScale] <;> ring
    have hres :
        (3 / 10 : ℝ) * roughScale ≤ roughMass - compositeMass := by
      linarith [hDensityScale, hCompositeScale]
    have hres' :
        (3 / 10 : ℝ) * (singularProduct M * (mass / L)) ≤
          roughMass - compositeMass := by
      simpa [roughScale] using hres
    calc
      _ ≤ roughMass - compositeMass := hres'
      _ = primeMass := by rw [hroughSplit]; ring
  let Good : Finset ℕ :=
    (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun p => p.Prime ∧ 0 < weight p)
  have hPrimeMassEq : primeMass = ∑ p ∈ Good, weight p := by
    have hpoint (p : ℕ) :
        (if p.Prime then weight p else 0) =
          if p.Prime ∧ 0 < weight p then weight p else 0 := by
      by_cases hp : p.Prime
      · by_cases hw : 0 < weight p
        · simp [hp, hw]
        · have hz : weight p = 0 := le_antisymm (le_of_not_gt hw) (hWeightNonneg p)
          simp [hp, hw, hz]
      · simp [hp]
    calc
      primeMass =
          ∑ p ∈ Finset.range (⌊2 * x⌋₊ + 1),
            (if p.Prime ∧ 0 < weight p then weight p else 0) := by
              dsimp [primeMass]
              apply Finset.sum_congr rfl
              intro p hp
              exact hpoint p
      _ = ∑ p ∈ Good, weight p := by
        dsimp [Good]
        rw [Finset.sum_filter]
  have hPrimeMassUpper : primeMass ≤ (Good.card : ℝ) * B := by
    rw [hPrimeMassEq]
    calc
      _ ≤ ∑ p ∈ Good, B := by
        apply Finset.sum_le_sum
        intro p hp
        exact hWeightLe p
      _ = (Good.card : ℝ) * B := by simp
  have hPrimeMassLowerX :
      (3 / 10 : ℝ) * singularProduct M * c₀ * x / L ^ 2 ≤ primeMass := by
    have hmult := mul_le_mul_of_nonneg_left hmassOverL
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 10) hS.le)
    calc
      (3 / 10 : ℝ) * singularProduct M * c₀ * x / L ^ 2 =
          (3 / 10 : ℝ) * singularProduct M * (c₀ * x / L ^ 2) := by ring
      _ ≤ (3 / 10 : ℝ) * singularProduct M * (mass / L) := hmult
      _ = (3 / 10 : ℝ) * (singularProduct M * (mass / L)) := by ring
      _ ≤ primeMass := hPrimeMassLower
  have hCoeffFinal :
      (singularProduct M * c₀ / (4 * B)) * B ≤
        (3 / 10 : ℝ) * singularProduct M * c₀ := by
    have hcoeff : (singularProduct M * c₀ / (4 * B)) * B =
        singularProduct M * c₀ / 4 := by
      field_simp [ne_of_gt hB]
      <;> ring
    rw [hcoeff]
    have hpos : 0 < singularProduct M * c₀ := mul_pos hS hc₀
    nlinarith
  have hGoodCard :
      singularProduct M * c₀ / (4 * B) * x / L ^ 2 ≤ (Good.card : ℝ) := by
    apply le_of_mul_le_mul_right _ hB
    calc
      (singularProduct M * c₀ / (4 * B) * x / L ^ 2) * B =
          ((singularProduct M * c₀ / (4 * B)) * B) * (x / L ^ 2) := by ring
      _ ≤ ((3 / 10 : ℝ) * singularProduct M * c₀) * (x / L ^ 2) :=
        mul_le_mul_of_nonneg_right hCoeffFinal (div_nonneg hxpos.le (sq_nonneg L))
      _ = (3 / 10 : ℝ) * singularProduct M * c₀ * x / L ^ 2 := by ring
      _ ≤ (Good.card : ℝ) * B := hPrimeMassLowerX.trans hPrimeMassUpper
  let Target : Set ℕ := {p : ℕ |
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧
      (p : ℤ) ≡ u [ZMOD M] ∧
      ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧
        Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧ 0 < r ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r →
          Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) < (ℓ : ℝ) ∧
            (ℓ : ℝ) < Real.exp (Real.rpow (Real.log x) (3 / 10 : ℝ))}
  have hGoodSubset : (Good : Set ℕ) ⊆ Target := by
    intro p hp
    change p ∈ Good at hp
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpData⟩
    rcases hpData with ⟨hpPrime, hpWeight⟩
    have hSupportP := hSupportAt.2.1 p (ne_of_gt hpWeight)
    rcases hSupportP with ⟨hpLo, hpHi, hFactorData⟩
    rcases hFactorData with
      ⟨r, Q, hfactor, hQ, hQlarge, hrGroup, hrBound, hMarkedWeight⟩
    have hconCond : 1 < p ∧ (p : ℤ) ≡ u [ZMOD M] := by
      by_contra hn
      have hzeroP : weight p = 0 := by simp [weight, conWeight, hn]
      exact (ne_of_gt hpWeight) hzeroP
    have hrpos : 0 < r := by
      by_contra hnot
      have hrzero : r = 0 := Nat.eq_zero_of_not_pos hnot
      have hpminus : p - 1 = 0 := by simpa [hrzero] using hfactor
      omega
    have hLbase : 1 < L := by linarith [hLlarge]
    have hPowerBase : (2 : ℝ) ^ 10 < L := by
      norm_num at hLlarge ⊢
      linarith
    have hLogPower : 10 * Real.log 2 < Real.log L := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 10) hPowerBase
      rw [Real.log_pow] at h
      simpa [mul_comm] using h
    have hLogRatio : Real.log 2 < Real.log L / 10 := by
      have hLogPower' : Real.log 2 * 10 < Real.log L := by
        nlinarith [hLogPower]
      exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2 hLogPower'
    have hLpowTen : 2 < Real.rpow L (1 / 10 : ℝ) := by
      have hexp : Real.exp (Real.log 2) <
          Real.exp (Real.log L * (1 / 10 : ℝ)) :=
        Real.exp_lt_exp.mpr (by
          calc
            Real.log 2 < Real.log L / 10 := hLogRatio
            _ = Real.log L * (1 / 10 : ℝ) := by ring)
      have hTwo : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
      have hRpow : Real.rpow L (1 / 10 : ℝ) =
          Real.exp (Real.log L * (1 / 10 : ℝ)) :=
        Real.rpow_def_of_pos hLpos _
      calc
        2 = Real.exp (Real.log 2) := hTwo.symm
        _ < Real.exp (Real.log L * (1 / 10 : ℝ)) := hexp
        _ = Real.rpow L (1 / 10 : ℝ) := hRpow.symm
    have hRpowMul : Real.rpow L (3 / 10 : ℝ) =
        Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 10 : ℝ) := by
      have hsum : (1 / 5 : ℝ) + 1 / 10 = 3 / 10 := by norm_num
      rw [← hsum]
      exact Real.rpow_add hLpos _ _
    have hPrimeDivs : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r →
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) < (ℓ : ℝ) ∧
          (ℓ : ℝ) < Real.exp (Real.rpow (Real.log x) (3 / 10 : ℝ)) := by
      intro ℓ hℓ hℓr
      have hℓmarked : ℓ ∈ markedPrimes x K a := hrGroup ℓ hℓ hℓr
      simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hℓmarked
      rcases hℓmarked with ⟨i, hℓband⟩
      rcases (Finset.mem_filter.mp hℓband).2 with ⟨hℓprimeBand, hℓlower, hℓupper⟩
      have haLower : (1 / 10 : ℝ) < a i := (ha.2.1 i).1
      have haUpper : a i < 1 / 5 := (ha.2.1 i).2
      have hLpowLower : Real.rpow L (1 / 10 : ℝ) < Real.rpow L (a i) :=
        Real.rpow_lt_rpow_of_exponent_lt hLbase haLower
      have hLpowUpper : Real.rpow L (a i) ≤ Real.rpow L (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLbase.le haUpper.le
      have hPrimeDivLower :
          Real.exp (Real.rpow L (1 / 10 : ℝ)) < (ℓ : ℝ) :=
        lt_of_lt_of_le (Real.exp_lt_exp.mpr hLpowLower) hℓlower
      have hPrimeDivUpper :
          (ℓ : ℝ) < Real.exp (Real.rpow L (3 / 10 : ℝ)) := by
        have hExponent : 2 * Real.rpow L (a i) < Real.rpow L (3 / 10 : ℝ) := by
          calc
            2 * Real.rpow L (a i) ≤ 2 * Real.rpow L (1 / 5 : ℝ) :=
              mul_le_mul_of_nonneg_left hLpowUpper (by norm_num)
            _ < Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 10 : ℝ) := by
              have hmul := mul_lt_mul_of_pos_left hLpowTen
                (Real.rpow_pos_of_pos hLpos (1 / 5 : ℝ))
              nlinarith [hmul]
            _ = Real.rpow L (3 / 10 : ℝ) := hRpowMul.symm
        exact lt_of_le_of_lt hℓupper (Real.exp_lt_exp.mpr hExponent)
      have hPrimeDivLower' :
          Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) < (ℓ : ℝ) := by
        simpa [L] using hPrimeDivLower
      have hPrimeDivUpper' :
          (ℓ : ℝ) < Real.exp (Real.rpow (Real.log x) (3 / 10 : ℝ)) := by
        simpa [L] using hPrimeDivUpper
      exact ⟨hPrimeDivLower', hPrimeDivUpper'⟩
    have hclass : (p : ℤ) ≡ u [ZMOD M] := hconCond.2
    refine ⟨hpPrime, hpLo, hpHi, hclass, r, Q, hfactor, hQ, hQlarge, hrpos, ?_⟩
    intro ℓ hℓ hℓr
    exact hPrimeDivs ℓ hℓ hℓr
  have hTargetFinite : Target.Finite := by
    apply (Finset.finite_toSet (Finset.range (⌊2 * x⌋₊ + 1))).subset
    intro p hp
    simp only [Target, Set.mem_setOf_eq] at hp
    have h2x : 0 ≤ 2 * x := by positivity
    have hpFloor : p ≤ ⌊2 * x⌋₊ :=
      (Nat.le_floor_iff h2x).2 (le_of_lt hp.2.2.1)
    exact Finset.mem_range.mpr (by omega)
  have hCard : Good.card ≤ Target.ncard := by
    calc
      Good.card = (Good : Set ℕ).ncard := (Set.ncard_coe_finset Good).symm
      _ ≤ Target.ncard := Set.ncard_le_ncard hGoodSubset hTargetFinite
  have hCardReal : (Good.card : ℝ) ≤ (Target.ncard : ℝ) := by exact_mod_cast hCard
  have hPrimeWeightCoeff :
      singularProduct M * c₀ / (4 * B) * B ≤
        (3 / 10 : ℝ) * singularProduct M * c₀ := by
    have hEq : singularProduct M * c₀ / (4 * B) * B = singularProduct M * c₀ / 4 := by
      field_simp [ne_of_gt hB]
      <;> ring
    rw [hEq]
    have hpos : 0 < singularProduct M * c₀ := mul_pos hS hc₀
    nlinarith
  have hGoodCard :
      singularProduct M * c₀ / (4 * B) * x / L ^ 2 ≤ (Good.card : ℝ) := by
    apply le_of_mul_le_mul_right _ hB
    calc
      (singularProduct M * c₀ / (4 * B) * x / L ^ 2) * B =
          ((singularProduct M * c₀ / (4 * B)) * B) * (x / L ^ 2) := by ring
      _ ≤ ((3 / 10 : ℝ) * singularProduct M * c₀) * (x / L ^ 2) :=
        mul_le_mul_of_nonneg_right hPrimeWeightCoeff (div_nonneg hxpos.le (sq_nonneg L))
      _ = (3 / 10 : ℝ) * singularProduct M * c₀ * x / L ^ 2 := by ring
      _ ≤ primeMass := hPrimeMassLowerX
      _ ≤ (Good.card : ℝ) * B := hPrimeMassUpper
  calc
    singularProduct M * c₀ / (4 * B) * x / Real.log x ^ 2 ≤ (Good.card : ℝ) := by
      simpa [L] using hGoodCard
    _ ≤ (Target.ncard : ℝ) := hCardReal

end ArtinPrimitiveRoots.Construction
