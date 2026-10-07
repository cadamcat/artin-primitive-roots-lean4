import Mathlib
import ArtinPrimitiveRoots.TypeII.Defs
import OAI.NumberTheory.PrimeGaps.Main

/-! External analytic inputs used by the Type II and construction arguments. -/

namespace ArtinPrimitiveRoots.Ext.TypeIIInputs

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

/-- The Meissel–Mertens constant, defined as the limit of the reciprocal-prime sum error. -/
noncomputable def meisselMertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun y : ℝ =>
    (∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y))

/-- Prime-counting function on a real interval, with primes counted by an explicit finite set. -/
noncomputable def primeIntervalCount (y₁ y₂ : ℝ) : ℝ :=
  ((primesUpTo y₂).filter fun p => y₁ < (p : ℝ)).card

/-- `Li(y)` with lower endpoint `2`. -/
noncomputable def logarithmicIntegral (y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-- Maximum prime progression error, in the `π` form used by §12. -/
noncomputable def primeProgressionError (y : ℝ) (q : ℕ) : ℝ :=
  ((Finset.range q).filter (fun v => Nat.Coprime v q)).fold max 0 fun v =>
    |(((primesUpTo y).filter (fun p => (p : ZMod q) = (v : ZMod q))).card : ℝ) -
      logarithmicIntegral y / (Nat.totient q : ℝ)|

/-- `ext:bombieri-vinogradov`, 12-construction.tex:286-292 (`con:bv-input`); matching OAI
`bombieriVinogradov` (`PrimeGaps/Main.lean:158`), converted to the prime-counting form. -/
theorem bombieri_vinogradov :
    ∀ A η : ℝ, 0 < A → 0 < η →
      ∃ C y₀ : ℝ, 0 < C ∧ 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          (∑ q ∈ Finset.range (⌊Real.rpow y (1 / 2 - η)⌋₊ + 1),
            primeProgressionError y q) ≤ C * y * Real.rpow (Real.log y) (-A) := by
  sorry

lemma primeCharacterPrefix_eq_range {d : ℕ} (χ : DirichletCharacter ℂ d) (x : ℝ) :
    OAI.LargePrimeGaps.primeCharacterPrefix x χ =
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  classical
  let f : ℕ → ℂ := fun n =>
    (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hzero : f 0 = 0 := by
    simp [f, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hrange : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    ext n
    simp
  have hioc : Finset.Ioc 0 ⌊x⌋₊ = (Finset.Icc 0 ⌊x⌋₊).erase 0 := by
    ext n
    simp
  have hremove :
      (∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).erase 0, f n) =
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hn'
    have hn0 : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_erase.mpr ⟨hne, hn⟩)
    subst n
    exact hzero
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) = _
  calc
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by rw [hioc, hremove]
    _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n := by rw [← hrange]

/-- `ext:siegel-walfisz`, PP `01-preliminaries.tex:24-40`, Proposition 2.1; matching OAI
`siegelWalfisz` (`PrimeGaps/Main.lean:142`). -/
theorem siegel_walfisz :
    ∀ A B : ℝ, 0 < A → 0 < B →
      ∃ C x₀ : ℝ, 0 < C ∧ 1 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.rpow (Real.log x) B →
            ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
              ‖(∑ n ∈ Finset.range (⌊x⌋₊ + 1),
                  (χ (n : ZMod d) : ℂ) *
                    (ArithmeticFunction.vonMangoldt n : ℂ)) -
                    (if χ = 1 then (x : ℂ) else 0)‖ ≤
                  C * x * Real.rpow (Real.log x) (-A) := by
  intro A B hA hB
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ := OAI.LargePrimeGaps.siegelWalfisz A B hA hB
  refine ⟨M, x₀, hM, hx₀, ?_⟩
  intro x hx d hd hdlog χ hχ
  have h := hSW x hx d hd hdlog χ hχ
  rw [OAI.LargePrimeGaps.primeCharacterError, primeCharacterPrefix_eq_range] at h
  exact h

/-- `ext:mertens`, PD Lemma 2.1; 11-sieve.tex:159-164; 12-construction.tex:398-402. The
first assertion is the second Mertens theorem; the second is its product form. Matching PNT+
`mertens_second_theorem` (`RosserSchoenfeldPrime.lean:824-825`) and `E₃.bound''`
(`Mertens.lean:2419). -/
theorem mertens :
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |(∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y) -
          meisselMertensConstant| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |roughSieveProduct y * Real.log y - Real.exp (-Real.eulerMascheroniConstant)| ≤ ε) := by
  sorry

/-- `ext:dirichlet-orthogonality`, 12-construction.tex:116-120; matching Mathlib
`DirichletCharacter.sum_char_inv_mul_char_eq` (`Orthogonality.lean:79`). -/
theorem dirichlet_orthogonality (M : ℕ) (hM : 0 < M)
    (u v : ZMod M) (hu : IsUnit u) :
    (if v = u then (1 : ℂ) else 0) =
      (1 / (Nat.totient M : ℂ)) *
        ∑ χ : DirichletCharacter ℂ M,
          star (χ u) * χ v := by
  sorry

/-- The Mellin-Fourier transform of the logarithmic-coordinate test function used in §12. -/
noncomputable def logFourierTransform (Ψ : ℝ → ℝ) (v : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℂ) *
    ∫ s : ℝ, (Ψ (Real.exp s) : ℂ) * Complex.exp (-Complex.I * v * s)

/-- `ext:fourier-inversion`, 12-construction.tex:133-140; matching Mathlib
`Continuous.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean:174`). -/
theorem fourier_inversion (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ⊤ Ψ)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    (∀ y : ℝ, 0 < y →
      (Ψ y : ℂ) = ∫ v : ℝ,
        logFourierTransform Ψ v * Complex.exp (Complex.I * v * Real.log y)) ∧
    (∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ v : ℝ, ‖logFourierTransform Ψ v‖ ≤
        C * Real.rpow (1 + |v|) (-(N : ℝ))) := by
  sorry

/-- `ext:derivative-test` — PP `01-preliminaries.tex:88-106`, Proposition 2.3; matching OAI
`first_derivative_sum_bound` (`DiscreteFirstDerivative.lean:147-151`). -/
theorem derivative_test (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i < N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i < N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Icc 0 N)) :
    ‖∑ i ∈ Finset.range N, additiveCharacter (f i)‖ ≤ 2 / β := by
  sorry

/-- `ext:pnt` — PD Lemma 2.1 and 11-sieve.tex:223-226; matching PNT+ `pi_asymp`
(`Consequences.lean:786`). -/
theorem pnt :
    ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |primeIntervalCount y (2 * y) - y / Real.log y| ≤ ε * y / Real.log y := by
  sorry

/-- `ext:dirichlet-L` — PP `02-long-prime.tex:312-323`; matching Mathlib
`DirichletCharacter.LFunction` and `differentiable_LFunction` (`DirichletContinuation.lean:98`). -/
theorem dirichlet_L (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunction χ s = LSeries (χ ·) s) ∧
    (χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ)) := by
  sorry

/-- `ext:jensen` — PP `02-long-prime.tex:392-394`; matching Mathlib
`AnalyticOnNhd.sum_divisor_le` (`JensenFormula.lean:389-392`). -/
theorem jensen (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hfc : f c ≠ 0) :
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ f z = 0} ≤
      (Real.log (⨆ z ∈ Metric.closedBall c R, ‖f z‖) - Real.log ‖f c‖) /
        Real.log (R / r) := by
  sorry

end ArtinPrimitiveRoots.Ext.TypeIIInputs
