import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c1.SieveProductHelpers
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
  let x₀ := Real.exp ((4 : ℝ) ^ 10)
  have hx₀4 : 4 ≤ x₀ := by
    dsimp [x₀]
    have h4 : 4 ≤ Real.exp (4 : ℝ) := by
      have hh := Real.add_one_le_exp (4 : ℝ)
      norm_num at hh ⊢
      linarith
    exact h4.trans (Real.exp_le_exp.mpr (by norm_num))
  have hx₀2 : 2 ≤ x₀ := by linarith
  refine ⟨3, x₀, by norm_num, hx₀2, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith [hx₀2, hx]
  have hx4 : 4 ≤ x := hx₀4.trans hx
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hx
    simpa [x₀, Real.log_exp] using hlog
  constructor
  · exact sorry
  · refine ⟨sorry, sorry, sorry, sorry, ?_⟩
    intro r hr
    exact progressionPrimeSum_trivial_bound x M c u Ψ K a r hc ha hΨ hL hx4 hr

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
