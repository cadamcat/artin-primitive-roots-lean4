import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.RoughDensity
import ArtinPrimitiveRoots.Construction.Proofs.c4.Density
import ArtinPrimitiveRoots.Construction.Proofs.c4.RoughRemoval
import ArtinPrimitiveRoots.Construction.Proofs.c4.TestFunction

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
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → 0 < ∫ y in (1 : ℝ)..2, Ψ y →
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
  obtain ⟨C_s, b₂₀, hCs, hb₂₀, hInitial⟩ := initial_lower
  obtain ⟨b₀, hb₀, C_d, hCd, hCdBound⟩ := ArtinPrimitiveRoots.Sieve.lem_density.2
  let b₂ : ℝ := min b₂₀ b₀
  have hb₂ : 0 < b₂ := lt_min hb₂₀ hb₀
  refine ⟨C_s, C_d, b₂, hCs, hCd, hb₂, ?_⟩
  intro M c u κ hM hM8 hc hcM hu hcu hcu' hκ hκsmall b hb hbb₂ hbk
  have hcpos : 0 < c := by rcases hc with h | h <;> simp [h]
  obtain ⟨K₀, hbinCost⟩ := bin_cost M c u κ b hM hcpos hcM hκ hκsmall hb
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
