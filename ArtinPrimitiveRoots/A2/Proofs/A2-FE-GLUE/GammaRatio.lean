import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import OAI.NumberTheory.DirichletL.GammaZeroDetector
import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2FreqP

private theorem gamma_ne_zero_of_im {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hz
  have h := congrArg Complex.im hn
  simpa using h

theorem gammaC_ratio_polynomial (x : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gammaℂ ((x : ℂ) + t * Complex.I) /
        Complex.Gammaℂ (1 - ((x : ℂ) + t * Complex.I))‖ ≤ C * (2 + |t|) ^ N := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (-x)
  let δ : ℝ := x + (N : ℝ) / 2 - 1 / 2
  let a : ℝ := (N : ℝ) / 2 + 1 / 2
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * δ)
  have hnumPos : 0 < x + N := by
    have hN' : -x < (N : ℝ) := by exact_mod_cast hN
    dsimp [δ] at *
    linarith
  have hshiftPos : 0 < (n : ℝ) - 2 * δ := by
    have hn' : 2 * δ < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hGammaRatio (t : ℝ) :
      ‖Complex.Gamma ((x : ℂ) + (N : ℂ) + t * Complex.I) /
        Complex.Gamma (1 - ((x : ℂ) + t * Complex.I) + n)‖ ≤
        Real.Gamma (x + N) / Real.Gamma (1 - x + n) := by
    have h := OAI.CubicReflectionKernel.Gamma_shifted_pair_bound a δ t n ?_ ?_
    · have h₁ : (a : ℂ) + (δ + t * Complex.I) =
          (x : ℂ) + (N : ℂ) + t * Complex.I := by
        simp [a, δ]
        ring
      have h₂ : (a : ℂ) - (δ + t * Complex.I) + n =
          1 - ((x : ℂ) + t * Complex.I) + n := by
        simp [a, δ]
        ring
      have h₃ : a + δ = x + N := by dsimp [a, δ]; ring
      have h₄ : a - δ + n = 1 - x + n := by dsimp [a, δ]; ring
      rw [h₁, h₂] at h
      rw [h₃, h₄] at h
      exact h
    · dsimp [a, δ]
      linarith [hnumPos]
    · exact hshiftPos
  have hKpos : 0 < Real.Gamma (x + N) / Real.Gamma (1 - x + n) := by
    apply div_pos
    · exact Real.Gamma_pos_of_pos hnumPos
    · have hden : 0 < 1 - x + (n : ℝ) := by
        have heq : 1 - x + (n : ℝ) = (x + N) + ((n : ℝ) - 2 * δ) := by
          dsimp [δ]
          ring
        rw [heq]
        exact add_pos hnumPos hshiftPos
      exact Real.Gamma_pos_of_pos hden
  refine ⟨(Real.Gamma (x + N) / Real.Gamma (1 - x + n)) *
    (|1 - x| + (n : ℝ) + 2) ^ n * Real.rpow (2 * Real.pi) (1 - 2 * x), ?_, n, ?_⟩
  · apply mul_pos
    · apply mul_pos hKpos
      exact pow_pos (by positivity : 0 < |1 - x| + (n : ℝ) + 2) _
    · exact Real.rpow_pos_of_pos (by positivity) _
  · intro t ht
    have htne : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at ht
      norm_num at ht
    let s : ℂ := (x : ℂ) + t * Complex.I
    let P : ℂ := ∏ k ∈ Finset.range N, (s + (k : ℂ))
    let Q : ℂ := ∏ k ∈ Finset.range n, (1 - s + (k : ℂ))
    have hPne : P ≠ 0 := by
      dsimp [P]
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk hz
      have him := congrArg Complex.im hz
      have : t = 0 := by simpa [s] using him
      exact htne this
    have hQne : Q ≠ 0 := by
      dsimp [Q]
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk hz
      have him := congrArg Complex.im hz
      have : -t = 0 := by simpa [s] using him
      exact htne (neg_eq_zero.mp this)
    have hshiftP := OAI.SevenEighths.GammaZeroDetector.gamma_shift s
      (by simpa [s] using htne) N
    have hshiftQ := OAI.SevenEighths.GammaZeroDetector.gamma_shift (1 - s)
      (by simpa [s] using neg_ne_zero.mpr htne) n
    have hshiftP' : Complex.Gamma (s + (N : ℂ)) = Complex.Gamma s * P := by
      simpa [P] using hshiftP
    have hshiftQ' : Complex.Gamma (1 - s + n) = Complex.Gamma (1 - s) * Q := by
      simpa [Q] using hshiftQ
    have hGammaS : Complex.Gamma s ≠ 0 := gamma_ne_zero_of_im (by simpa [s] using htne)
    have hGammaOneS : Complex.Gamma (1 - s) ≠ 0 :=
      gamma_ne_zero_of_im (by simpa [s] using neg_ne_zero.mpr htne)
    have hratio : Complex.Gamma s / Complex.Gamma (1 - s) =
        (Complex.Gamma (s + (N : ℂ)) / Complex.Gamma (1 - s + n)) * (Q / P) := by
      calc
        _ = (Complex.Gamma (s + (N : ℂ)) / P) /
              (Complex.Gamma (1 - s + n) / Q) := by
          rw [hshiftP', hshiftQ']
          field_simp [hPne, hQne, hGammaS, hGammaOneS] <;> ring
        _ = _ := by
          field_simp [hPne, hQne, hGammaS, hGammaOneS] <;> ring
    have htermP (k : ℕ) (hk : k ∈ Finset.range N) :
        1 ≤ ‖s + (k : ℂ)‖ := by
      have him := Complex.abs_im_le_norm (s + (k : ℂ))
      have him' : |(s + (k : ℂ)).im| = |t| := by simp [s]
      rw [him'] at him
      exact ht.trans him
    have hPnorm : (1 : ℝ) ≤ ‖P‖ := by
      dsimp [P]
      rw [norm_prod]
      calc
        1 = ∏ _k ∈ Finset.range N, (1 : ℝ) := by simp
        _ ≤ ∏ k ∈ Finset.range N, ‖s + (k : ℂ)‖ :=
          Finset.prod_le_prod₀ (by intro k hk; positivity)
            (fun k hk => htermP k hk)
    have htermQ (k : ℕ) (hk : k ∈ Finset.range n) :
        ‖1 - s + (k : ℂ)‖ ≤ (|1 - x| + (n : ℝ) + 2) * (2 + |t|) := by
      have hnorm := Complex.norm_le_abs_re_add_abs_im (1 - s + (k : ℂ))
      have hre : |(1 - s + (k : ℂ)).re| ≤ |1 - x| + (k : ℝ) := by
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hx := abs_add_le (1 - x) (k : ℝ)
        simpa [s] using hx
      have him : |(1 - s + (k : ℂ)).im| = |t| := by simp [s]
      have hklt : (k : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
      rw [him] at hnorm
      calc
        ‖1 - s + (k : ℂ)‖ ≤ |(1 - s + (k : ℂ)).re| + |t| := hnorm
        _ ≤ |1 - x| + (n : ℝ) + |t| := by linarith [hre, hklt]
        _ ≤ (|1 - x| + (n : ℝ) + 2) * (2 + |t|) := by
          let A : ℝ := |1 - x| + (n : ℝ) + 2
          have hA : 1 ≤ A := by
            dsimp [A]
            have h₁ : (0 : ℝ) ≤ |1 - x| := abs_nonneg _
            have h₂ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
            linarith
          have hT : 0 ≤ |t| := abs_nonneg t
          have hAA : A ≤ 2 * A := by nlinarith [hA]
          have hAT : |t| ≤ A * |t| := by
            calc
              |t| = 1 * |t| := by ring
              _ ≤ A * |t| := mul_le_mul_of_nonneg_right hA hT
          have hsum := add_le_add hAA hAT
          calc
            _ ≤ A + |t| := by dsimp [A]; linarith
            _ ≤ 2 * A + A * |t| := hsum
            _ = A * (2 + |t|) := by ring
    have hQnorm : ‖Q‖ ≤
        ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) ^ n := by
      dsimp [Q]
      rw [norm_prod]
      calc
        _ ≤ ∏ _k ∈ Finset.range n,
              ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) :=
          Finset.prod_le_prod₀ (by intro k hk; positivity)
            (fun k hk => htermQ k hk)
        _ = _ := by simp
    have hGammaBound :
        ‖Complex.Gamma (s + (N : ℂ)) / Complex.Gamma (1 - s + n)‖ ≤
          Real.Gamma (x + N) / Real.Gamma (1 - x + n) := by
      have h := hGammaRatio t
      have h₁ : (x : ℂ) + (N : ℂ) + t * Complex.I = s + (N : ℂ) := by
        simp [s]
        ring
      have h₂ : 1 - ((x : ℂ) + t * Complex.I) + n = 1 - s + n := by
        simp [s]
      rw [h₁, h₂] at h
      exact h
    have hbase :
        ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ ≤
          (Real.Gamma (x + N) / Real.Gamma (1 - x + n)) *
            ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) ^ n := by
      calc
        ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ =
            ‖Complex.Gamma (s + (N : ℂ)) / Complex.Gamma (1 - s + n)‖ * ‖Q / P‖ := by
          rw [hratio, norm_mul]
        _ = ‖Complex.Gamma (s + (N : ℂ)) / Complex.Gamma (1 - s + n)‖ *
              (‖Q‖ / ‖P‖) := by
          rw [show ‖Q / P‖ = ‖Q‖ / ‖P‖ from norm_div Q P]
        _ ≤ (Real.Gamma (x + N) / Real.Gamma (1 - x + n)) *
              ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) ^ n := by
          have hQP : ‖Q‖ / ‖P‖ ≤
              ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) ^ n := by
            calc
              ‖Q‖ / ‖P‖ ≤ ‖Q‖ := div_le_self (norm_nonneg _) hPnorm
              _ ≤ _ := hQnorm
          exact mul_le_mul hGammaBound hQP
            (div_nonneg (norm_nonneg _) (norm_nonneg _)) (le_of_lt hKpos)
    have hGammaC : ‖Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)‖ =
        Real.rpow (2 * Real.pi) (1 - 2 * x) *
          ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ := by
      have hpow₁ :
          ‖((2 * Real.pi : ℝ) : ℂ) ^ (-s)‖ = Real.rpow (2 * Real.pi) (-x) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        simp [s]
      have hpow₂ :
          ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))‖ =
            Real.rpow (2 * Real.pi) (-(1 - x)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        simp [s]
      rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def]
      have hbaseCast : (2 : ℂ) * (Real.pi : ℂ) =
          ((2 * Real.pi : ℝ) : ℂ) := by norm_num [Complex.ofReal_mul]
      simp_rw [hbaseCast]
      simp only [norm_div, norm_mul, hpow₁, hpow₂]
      norm_num
      have hGammaDen : ‖Complex.Gamma (1 - s)‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr hGammaOneS
      field_simp [hGammaDen]
      rw [Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.pi),
        Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.pi),
        Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.pi)]
      rw [← Real.exp_add]
      congr 1 <;> ring
    calc
      ‖Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)‖ =
          Real.rpow (2 * Real.pi) (1 - 2 * x) *
            ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ := hGammaC
      _ ≤ Real.rpow (2 * Real.pi) (1 - 2 * x) *
            ((Real.Gamma (x + N) / Real.Gamma (1 - x + n)) *
              ((|1 - x| + (n : ℝ) + 2) * (2 + |t|)) ^ n) :=
          mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [mul_pow]; ring

end ArtinPrimitiveRoots.Proofs.A2FreqP
