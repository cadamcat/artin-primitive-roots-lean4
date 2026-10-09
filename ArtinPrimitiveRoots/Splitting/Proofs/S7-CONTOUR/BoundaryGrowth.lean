import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpPrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HadamardTail
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpLogDeriv
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- Both boundary lines are regular and have polynomial logarithmic-derivative growth. -/
theorem sharp_boundary_line_growth (K : Type*) [Field K] [NumberField K]
    (σ : ℝ) (hσ : σ = (-1 / 2 : ℝ) ∨ σ = 2) :
    Continuous (fun t : ℝ =>
      dedekindZetaLogDerivative K ((σ : ℂ) + t * Complex.I)) ∧
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      ‖dedekindZetaLogDerivative K ((σ : ℂ) + t * Complex.I)‖ ≤
        B * Real.rpow (1 + |t|) (4 : ℝ) := by
  let line : ℝ → ℂ := fun t => (σ : ℂ) + t * Complex.I
  let L : ℝ → ℂ := fun t => dedekindZetaLogDerivative K (line t)
  have hre (t : ℝ) : (line t).re = σ := by simp [line]
  have him (t : ℝ) : (line t).im = t := by simp [line]
  have hfacts : -1 < σ ∧ σ ≠ 0 ∧ σ ≠ 1 ∧ |σ| ≤ 2 ∧
      σ ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
    rcases hσ with h | h <;> norm_num [h]
  have hxi (t : ℝ) : dedekindXi K (line t) ≠ 0 := by
    intro hz
    have hmem := ((xi_zero_dictionary K).1 (line t)).mp hz
    have hpos := hmem.1
    have hlt := hmem.2.1
    rw [hre] at hpos hlt
    rcases hσ with h | h
    · rw [h] at hpos
      norm_num at hpos
    · rw [h] at hlt
      norm_num at hlt
  have han (t : ℝ) : AnalyticAt ℂ (dedekindZetaLogDerivative K) (line t) := by
    refine (sharp_regular_of_re_gt_neg_one K (line t)
      (by rw [hre]; exact hfacts.1) ?_ ?_ (hxi t)).2.2
    · intro hz
      have h := congrArg Complex.re hz
      simp only [hre, Complex.zero_re] at h
      exact hfacts.2.1 h
    · intro hz
      have h := congrArg Complex.re hz
      simp only [hre, Complex.one_re] at h
      exact hfacts.2.2.1 h
  have hline : Continuous line :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcont : Continuous L := continuous_iff_continuousAt.mpr fun t =>
    (han t).continuousAt.comp hline.continuousAt
  obtain ⟨b0, hb0⟩ := (isCompact_Icc : IsCompact (Set.Icc (-3 : ℝ) 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨Cxi, hCxi, hxiBound⟩ := xi_logderiv_bound K
  obtain ⟨Cerr, hCerr, herror⟩ := sharp_xi_difference_bound K
  let B : ℝ := |b0| + 11 * Cxi + Cerr + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨hcont, B, hB, ?_⟩
  intro t
  let u : ℝ := 1 + |t|
  have huone : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) huone
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have huu2 : u ≤ u ^ 2 := by nlinarith
  have hu24 : u ^ 2 ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hu4 : 1 ≤ u ^ 4 := hu2.trans hu24
  have huu4 : u ≤ u ^ 4 := huu2.trans hu24
  have hrpow : Real.rpow u (4 : ℝ) = u ^ 4 := by
    simp only [Real.rpow_eq_pow]
    exact Real.rpow_ofNat u 4
  change ‖L t‖ ≤ B * Real.rpow u (4 : ℝ)
  rw [hrpow]
  by_cases ht : 3 ≤ |t|
  · have hgap (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) :
        (1 / 2 : ℝ) ≤ ‖line t - ρ‖ := by
      have habs : (1 / 2 : ℝ) ≤ |(line t).re - ρ.re| := by
        rw [hre]
        rcases hσ with h | h
        · rw [h]
          linarith [hρ.1, neg_le_abs ((-1 / 2 : ℝ) - ρ.re)]
        · rw [h]
          linarith [hρ.2.1, le_abs_self ((2 : ℝ) - ρ.re)]
      exact habs.trans (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (line t - ρ))
    have hnorm : ‖line t‖ ≤ 2 * u := by
      calc
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |σ| + |t| := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        _ ≤ 2 + |t| := add_le_add hfacts.2.2.2.1 le_rfl
        _ ≤ 2 * u := by dsimp [u]; linarith [abs_nonneg t]
    have hpoly : 1 + ‖line t‖ * (1 + ‖line t‖ / (1 / 2 : ℝ)) ≤ 11 * u ^ 4 := by
      have hmul : ‖line t‖ * (1 + 2 * ‖line t‖) ≤ (2 * u) * (1 + 4 * u) := by
        apply mul_le_mul hnorm
        · linarith
        · positivity
        · positivity
      have hquad : 1 + (2 * u) * (1 + 4 * u) ≤ 11 * u ^ 2 := by
        nlinarith only [hu2, huu2]
      calc
        _ = 1 + ‖line t‖ * (1 + 2 * ‖line t‖) := by ring
        _ ≤ 1 + (2 * u) * (1 + 4 * u) := add_le_add le_rfl hmul
        _ ≤ 11 * u ^ 2 := hquad
        _ ≤ 11 * u ^ 4 := mul_le_mul_of_nonneg_left hu24 (by norm_num)
    have hxiAt : ‖deriv (dedekindXi K) (line t) / dedekindXi K (line t)‖ ≤
        11 * Cxi * u ^ 4 := by
      calc
        _ ≤ Cxi * (1 + ‖line t‖ * (1 + ‖line t‖ / (1 / 2 : ℝ))) :=
          hxiBound (line t) (1 / 2) (by norm_num) hgap
        _ ≤ Cxi * (11 * u ^ 4) := mul_le_mul_of_nonneg_left hpoly hCxi.le
        _ = _ := by ring
    have herr : ‖L t + deriv (dedekindXi K) (line t) / dedekindXi K (line t)‖ ≤
        Cerr * Real.log (2 + |t|) := by
      simpa only [him, L] using herror (line t)
        (by rw [hre]; exact hfacts.2.2.2.2) (by rwa [him]) (hxi t)
    have hlog : Real.log (2 + |t|) ≤ u ^ 4 := by
      calc
        _ ≤ (2 + |t|) - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = u := by dsimp [u]; ring
        _ ≤ u ^ 4 := huu4
    have htail : ‖L t‖ ≤ (11 * Cxi + Cerr) * u ^ 4 := by
      calc
        _ = ‖(L t + deriv (dedekindXi K) (line t) / dedekindXi K (line t)) -
            deriv (dedekindXi K) (line t) / dedekindXi K (line t)‖ := by congr 1; ring
        _ ≤ ‖L t + deriv (dedekindXi K) (line t) / dedekindXi K (line t)‖ +
            ‖deriv (dedekindXi K) (line t) / dedekindXi K (line t)‖ := norm_sub_le _ _
        _ ≤ Cerr * Real.log (2 + |t|) + 11 * Cxi * u ^ 4 := add_le_add herr hxiAt
        _ ≤ Cerr * u ^ 4 + 11 * Cxi * u ^ 4 :=
          add_le_add (mul_le_mul_of_nonneg_left hlog hCerr.le) le_rfl
        _ = _ := by ring
    exact htail.trans (mul_le_mul_of_nonneg_right
      (by dsimp [B]; linarith [abs_nonneg b0]) (by positivity))
  · have hmem : t ∈ Set.Icc (-3 : ℝ) 3 := by
      have habs := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨habs.1.le, habs.2.le⟩
    calc
      ‖L t‖ ≤ b0 := hb0 t hmem
      _ ≤ |b0| := le_abs_self _
      _ ≤ B := by dsimp [B]; linarith
      _ ≤ B * u ^ 4 := by nlinarith [hB.le]

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
