import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.PP_PRIME

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open MeasureTheory

noncomputable def mangoldtIntervalPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
      (fun n : ℕ => 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N ∧ n ∈ I),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))

noncomputable def smoothedMangoldtPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊3 * N⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ)) *
        (g ((n : ℝ) / N) : ℂ)

noncomputable def mellinKernel (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ w : ℝ in Set.Ioi 0,
    (g w : ℂ) * Complex.exp (z * Real.log w) / (w : ℂ)

/-- The kernel is Mathlib's Mellin transform, with the positive-base power
rewritten only on the domain of integration. -/
theorem mellinKernel_eq_mellin (g : ℝ → ℝ) (z : ℂ) :
    mellinKernel g z = mellin (fun w : ℝ => (g w : ℂ)) z := by
  unfold mellinKernel mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [smul_eq_mul]
  have hwpos : 0 < w := hw
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwpos.ne'
  have hlog : Complex.log (w : ℂ) = (Real.log w : ℂ) :=
    (Complex.ofReal_log hwpos.le).symm
  rw [Complex.cpow_def_of_ne_zero hwC, hlog]
  have hexp : Complex.exp (Real.log w : ℂ) = (w : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hwpos]
  calc
    (g w : ℂ) * Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ) =
        (Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ)) * (g w : ℂ) := by ring
    _ = Complex.exp ((z - 1) * (Real.log w : ℂ)) * (g w : ℂ) := by
      rw [← hexp, ← Complex.exp_sub]
      congr 1
      ring
    _ = Complex.exp ((Real.log w : ℂ) * (z - 1)) * (g w : ℂ) := by
      congr 2
      ring

/-- Compact support and derivative control give a uniform vertical Mellin bound. -/
theorem mellinKernel_uniform_decay (g : ℝ → ℝ) (L A : ℝ)
    (hL : 1 ≤ L) (hA : 0 < A)
    (hg : ContDiff ℝ ⊤ g)
    (hsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hderiv : ∀ j w, |iteratedDeriv j g w| ≤
      K j * Real.rpow L ((j : ℝ) * (A + 4))) :
    ∀ j : ℕ, ∃ Mj : ℝ, 0 < Mj ∧
      ∀ α v : ℝ, |α| ≤ 1 →
        ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
          Mj * Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
            Real.rpow (1 + |v|) (-(j : ℝ)) := by
  sorry

/-- Mellin inversion on a compactly supported smooth positive-coordinate weight. -/
theorem mellinKernel_inversion (g : ℝ → ℝ)
    (hg : ContDiff ℝ ⊤ g)
    (hsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    (c w : ℝ) (hw : 0 < w) :
    (g w : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
        Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
  sorry

/-- The sharp von Mangoldt polynomial has uniform cancellation in every natural interval. -/
theorem prime_mangoldt_interval_bound :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ K x₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N} →
                      ‖mangoldtIntervalPolynomial N q χ t I‖ ≤
                        K * Real.rpow L (-A - 2) := by
  sorry

/-- The prime-power terms are a uniform lower-order error in a dyadic interval. -/
theorem prime_power_removal {N : ℝ} (hN : 4 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ)
    (hI : I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N}) :
    ‖mangoldtIntervalPolynomial N q χ t I -
      ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I),
        (Real.log (p : ℝ) : ℂ) * χ (p : ZMod q) *
          Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ))‖ ≤
      100 * Real.rpow N (-1 / 2) * (Real.log (3 * N)) ^ 2 := by
  sorry

/-- Final interval Abel transfer and logarithm removal, to be assembled from the preceding bounds. -/
theorem prime_polynomial_core :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                      ‖primeDirichletPolynomial N q χ t I‖ ≤
                        C₀ * Real.rpow L (-A) := by
  sorry

end ArtinPrimitiveRoots.Proofs.PP_PRIME
