import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.FunctionalEquation
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.GammaLines
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.PrefactorReflection
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.PrimeNormSum
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.ZeroSum
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Boundary
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroEndpoint
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HadamardTail
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroWindows
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Heights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».XiHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GammaHorizontal
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrefactorDeriv
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpLogDeriv
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».FinitePatch
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpPrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectanglePatch
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PoleIntegrals
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectangleResidues
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WeightedRectangle
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».HorizontalLimits
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GoodContours
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WindowSums
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».WeightDecay
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».LineIntegrability
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».BoundaryGrowth
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

universe u

open scoped NumberField BigOperators Interval Topology
open NumberField IsDedekindDomain Filter MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting
open Classical

-- The smooth-test hypothesis is expanded here to keep this helper file below Analytic.lean.
theorem mellin_entire (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) :
    Differentiable ℂ (mellinTransform f) := by
  sorry

theorem mellin_decay (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) :
    ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)) := by
  sorry

theorem euler_log_norm_summable (K : Type u) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) × ℕ =>
      Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
        Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * σ)) := by
  have hEuler := ArtinPrimitiveRoots.Ext.SplittingInputs.ext_dedekind_euler_logderiv K
    (s := (σ : ℂ)) (by simpa using hσ)
  let F : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun w =>
    Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
      Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * σ)
  let G : HeightOneSpectrum (𝓞 K) → ℕ → ℂ := fun v j =>
    (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j + 1 : ℕ) : ℂ) * (σ : ℂ))
  have hterm (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) : (F (v, j) : ℂ) = G v j := by
    dsimp only [F, G]
    rw [Real.rpow_eq_pow]
    rw [Complex.ofReal_mul,
      Complex.ofReal_cpow (show 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) from Nat.cast_nonneg _)]
    push_cast <;> rfl
  have hinner (v : HeightOneSpectrum (𝓞 K)) : Summable (fun j : ℕ => F (v, j)) := by
    apply Complex.summable_ofReal.mp
    exact (hEuler.1 v).congr fun j => (hterm v j).symm
  have houter : Summable (fun v : HeightOneSpectrum (𝓞 K) => ∑' j : ℕ, F (v, j)) := by
    apply Complex.summable_ofReal.mp
    refine hEuler.2.1.congr fun v => ?_
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun j => (hterm v j).symm
  have hnonneg : 0 ≤ F := by
    intro w
    have hN : 1 ≤ (Ideal.absNorm w.1.asIdeal : ℝ) := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w.1).le
    exact mul_nonneg (Real.log_nonneg hN) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact (summable_prod_of_nonneg hnonneg).2 ⟨hinner, houter⟩

theorem mellin_prime_identity (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 0 < x) :
    (primeIdealTheta K f x : ℂ) = verticalLineIntegral
      (fun s : ℂ => dedekindZetaLogDerivative K s *
        Complex.cpow (x : ℂ) s * mellinTransform f s) 2 := by
  sorry

theorem euler_right_line_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + t * Complex.I)‖ ≤
        B * Module.finrank ℚ K := by
  let Z : ℝ := ∑' m : ℕ, Real.rpow (m : ℝ) (-(5 / 4 : ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨8 * Z + 1, by linarith, ?_⟩
  intro K _ _ t
  obtain ⟨hprimeSum, hprimeBound⟩ := prime_norm_power_sum_bound K
    (σ := (5 / 4 : ℝ)) (by norm_num)
  let s : ℂ := (3 / 2 : ℝ) + t * Complex.I
  have hs : 1 < s.re := by simp [s]; norm_num
  let F : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) /
      ((Ideal.absNorm v.asIdeal : ℂ) ^ s - 1)
  have hF (v : HeightOneSpectrum (𝓞 K)) :
      ‖F v‖ ≤ 8 * Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-(5 / 4 : ℝ)) := by
    let N : ℝ := Ideal.absNorm v.asIdeal
    have hNtwo : 2 ≤ N := by
      dsimp only [N]
      exact_mod_cast (show 2 ≤ Ideal.absNorm v.asIdeal from
        NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hN : 0 < N := by linarith
    have hP : 2 ≤ Real.rpow N (3 / 2 : ℝ) := by
      calc
        2 ≤ N := hNtwo
        _ = Real.rpow N 1 := (Real.rpow_one _).symm
        _ ≤ Real.rpow N (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hnorm : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ s‖ = Real.rpow N (3 / 2 : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos (by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v
        omega)]
      simp [s, N]
    have hden : Real.rpow N (3 / 2 : ℝ) / 2 ≤
        ‖(Ideal.absNorm v.asIdeal : ℂ) ^ s - 1‖ := by
      have h := norm_sub_norm_le ((Ideal.absNorm v.asIdeal : ℂ) ^ s) (1 : ℂ)
      rw [hnorm, norm_one] at h
      linarith
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hlogBound : Real.log N ≤ 4 * Real.rpow N (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (x := N) (ε := (1 / 4 : ℝ)) hN.le (by norm_num)
      rw [← Real.rpow_eq_pow] at h
      linarith
    calc
      ‖F v‖ = Real.log N / ‖(Ideal.absNorm v.asIdeal : ℂ) ^ s - 1‖ := by
        dsimp only [F]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
        change |Real.log N| / _ = _
        rw [abs_of_nonneg hlog]
      _ ≤ Real.log N / (Real.rpow N (3 / 2 : ℝ) / 2) :=
        div_le_div_of_nonneg_left hlog (by positivity) hden
      _ = 2 * Real.log N * Real.rpow N (-(3 / 2 : ℝ)) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_neg hN.le]
        field_simp [(Real.rpow_pos_of_pos hN (3 / 2 : ℝ)).ne'] <;> ring
      _ ≤ 8 * Real.rpow N (1 / 4 : ℝ) * Real.rpow N (-(3 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN.le _)
      _ = 8 * Real.rpow N (-(5 / 4 : ℝ)) := by
        simp only [Real.rpow_eq_pow]
        rw [mul_assoc, ← Real.rpow_add hN]
        norm_num
  have heq : dedekindZetaLogDerivative K s = ∑' v : HeightOneSpectrum (𝓞 K), F v := by
    rw [(ArtinPrimitiveRoots.Ext.SplittingInputs.ext_dedekind_euler_logderiv K hs).2.2]
    exact tsum_congr fun v =>
      (ArtinPrimitiveRoots.Splitting.S7ExtEuler.prime_power_hasSum v hs).tsum_eq
  calc
    ‖dedekindZetaLogDerivative K s‖ ≤
        ∑' v : HeightOneSpectrum (𝓞 K), 8 * Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-(5 / 4 : ℝ)) := by
      rw [heq]
      exact tsum_of_norm_bounded (hprimeSum.mul_left 8).hasSum hF
    _ = 8 * ∑' v : HeightOneSpectrum (𝓞 K),
        Real.rpow (Ideal.absNorm v.asIdeal : ℝ) (-(5 / 4 : ℝ)) := tsum_mul_left
    _ ≤ 8 * ((Module.finrank ℚ K : ℝ) * Z) := mul_le_mul_of_nonneg_left hprimeBound (by norm_num)
    _ ≤ (8 * Z + 1) * (Module.finrank ℚ K : ℝ) := by
      calc
        _ = 8 * Z * (Module.finrank ℚ K : ℝ) := by ring
        _ ≤ 8 * Z * (Module.finrank ℚ K : ℝ) + (Module.finrank ℚ K : ℝ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)
        _ = _ := by ring

theorem reflected_line_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-t) * Complex.I)‖ +
          Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |t|) := by
  obtain ⟨A, hA, hpref⟩ := prefactor_reflection_bound
  refine ⟨A, hA, ?_⟩
  intro K _ _ t
  have hgood (u : ℝ) (hu : u ≠ 0) :
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + u * Complex.I)‖ ≤
        ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-u) * Complex.I)‖ +
          Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |u|) := by
    let s : ℂ := (-1 / 2 : ℝ) + u * Complex.I
    let s' : ℂ := (3 / 2 : ℝ) + (-u) * Complex.I
    let P : ℂ → ℂ := fun z => deriv (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K) z /
      ArtinPrimitiveRoots.Hecke.dedekindPrefactor K z
    have hre : s.re = (-1 / 2 : ℝ) := by simp [s]
    have hsim : s.im ≠ 0 := by simpa [s] using hu
    have hxi : dedekindXi K s ≠ 0 := by
      intro hz
      have hpos := (((xi_zero_dictionary K).1 s).mp hz).1
      rw [hre] at hpos
      norm_num at hpos
    have hreflect : 1 - s = s' := by
      dsimp only [s, s']
      apply Complex.ext <;> simp <;> ring
    have heq : dedekindZetaLogDerivative K s =
        -dedekindZetaLogDerivative K s' + P s + P s' := by
      have h := sharp_functional_logderiv K hsim hxi
      rw [hreflect] at h
      exact h
    have hp : ‖P s‖ + ‖P s'‖ ≤ Real.log (absoluteDiscriminant K) +
        A * Module.finrank ℚ K * Real.log (2 + |u|) := hpref K u hu
    calc
      _ = ‖-dedekindZetaLogDerivative K s' + P s + P s'‖ := congrArg norm heq
      _ ≤ (‖-dedekindZetaLogDerivative K s'‖ + ‖P s‖) + ‖P s'‖ :=
        (norm_add_le (-dedekindZetaLogDerivative K s' + P s) (P s')).trans
          (add_le_add (norm_add_le (-dedekindZetaLogDerivative K s') (P s)) le_rfl)
      _ = ‖dedekindZetaLogDerivative K s'‖ + ‖P s‖ + ‖P s'‖ := by rw [norm_neg]
      _ ≤ ‖dedekindZetaLogDerivative K s'‖ + Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |u|) := by linarith only [hp]
  have hcont (σ : ℝ) (hσ : σ = (-1 / 2 : ℝ) ∨ σ = (3 / 2 : ℝ)) :
      Continuous (fun u : ℝ => dedekindZetaLogDerivative K ((σ : ℂ) + u * Complex.I)) := by
    let line : ℝ → ℂ := fun u => (σ : ℂ) + u * Complex.I
    have hre (u : ℝ) : (line u).re = σ := by simp [line]
    have hfacts : -1 < σ ∧ σ ≠ 0 ∧ σ ≠ 1 := by
      rcases hσ with h | h <;> norm_num [h]
    have hxi (u : ℝ) : dedekindXi K (line u) ≠ 0 := by
      intro hz
      have hmem := ((xi_zero_dictionary K).1 (line u)).mp hz
      have hpos := hmem.1
      have hlt := hmem.2.1
      rw [hre] at hpos hlt
      rcases hσ with h | h
      · rw [h] at hpos
        norm_num at hpos
      · rw [h] at hlt
        norm_num at hlt
    have han (u : ℝ) : AnalyticAt ℂ (dedekindZetaLogDerivative K) (line u) := by
      refine (sharp_regular_of_re_gt_neg_one K (line u)
        (by rw [hre]; exact hfacts.1) ?_ ?_ (hxi u)).2.2
      · intro hz
        have h := congrArg Complex.re hz
        simp only [hre, Complex.zero_re] at h
        exact hfacts.2.1 h
      · intro hz
        have h := congrArg Complex.re hz
        simp only [hre, Complex.one_re] at h
        exact hfacts.2.2 h
    have hline : Continuous line :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact continuous_iff_continuousAt.mpr fun u =>
      (han u).continuousAt.comp hline.continuousAt
  have hcLeft : Continuous (fun u : ℝ =>
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + u * Complex.I)‖) :=
    (hcont (-1 / 2) (Or.inl rfl)).norm
  have hcRight : Continuous (fun u : ℝ =>
      ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-u) * Complex.I)‖) := by
    simpa only [Function.comp_def, Complex.ofReal_neg] using
      ((hcont (3 / 2) (Or.inr rfl)).comp continuous_neg).norm
  have hlog : Continuous (fun u : ℝ => Real.log (2 + |u|)) := by
    have harg : Continuous (fun u : ℝ => (2 : ℝ) + |u|) :=
      continuous_const.add continuous_abs
    refine continuous_iff_continuousAt.mpr fun u => ?_
    exact (Real.continuousAt_log (by positivity : 2 + |u| ≠ 0)).comp
      (f := fun v : ℝ => 2 + |v|) (x := u) harg.continuousAt
  have hcRhs : Continuous (fun u : ℝ =>
      ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-u) * Complex.I)‖ +
        Real.log (absoluteDiscriminant K) +
        A * Module.finrank ℚ K * Real.log (2 + |u|)) :=
    (hcRight.add continuous_const).add (continuous_const.mul hlog)
  by_cases ht : t ≠ 0
  · exact hgood t ht
  · have ht0 : t = 0 := Classical.not_not.mp ht
    subst t
    have hl : Tendsto (fun u : ℝ =>
        ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + u * Complex.I)‖)
        (𝓝[>] (0 : ℝ))
        (𝓝 ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + (0 : ℝ) * Complex.I)‖) :=
      hcLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hr : Tendsto (fun u : ℝ =>
        ‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-u) * Complex.I)‖ +
          Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |u|))
        (𝓝[>] (0 : ℝ))
        (𝓝 (‖dedekindZetaLogDerivative K ((3 / 2 : ℝ) + (-(0 : ℝ)) * Complex.I)‖ +
          Real.log (absoluteDiscriminant K) +
          A * Module.finrank ℚ K * Real.log (2 + |(0 : ℝ)|))) :=
      hcRhs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hl hr (by
      filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
      exact hgood u (ne_of_gt hu))

theorem zero_family_summable (f : ℝ → ℝ)
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 2 ≤ x) :
    Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
      else 0) := by
  exact zero_family_summable_of_decay f hdecay K x hx

theorem contour_shift (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (hleft : ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|)))
    (K : Type u) [Field K] [NumberField K] (x : ℝ) (hx : 2 ≤ x) :
    verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
      Complex.cpow (x : ℂ) s * mellinTransform f s) 2 =
      (x : ℂ) * mellinTransform f 1 -
        (∑' ρ : ℂ, if ρ ∈ nontrivialZeros K then
          (zeroMultiplicity K ρ : ℂ) * Complex.cpow (x : ℂ) ρ * mellinTransform f ρ
          else 0) -
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) *
          mellinTransform f 0 +
        verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
          Complex.cpow (x : ℂ) s * mellinTransform f s) (-1 / 2) := by
  let W : ℂ → ℂ := fun s => Complex.cpow (x : ℂ) s * mellinTransform f s
  let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s * W s
  let F : ℂ → ℂ := fun ρ => if ρ ∈ nontrivialZeros K then
    (zeroMultiplicity K ρ : ℂ) * W ρ else 0
  let N : ℂ := ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ)
  obtain ⟨hW, hdW⟩ := cpow_weight_entire_decay (mellinTransform f) hentire hdecay x hx
  change Differentiable ℂ W at hW
  obtain ⟨C, hC, hbound⟩ := hdW 6 (-1 / 2) 2 (by norm_num)
  have hWdecay : ∀ s : ℂ, (-1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖W s‖ ≤ C * Real.rpow (1 + |s.im|) (-6 : ℝ) := by
    simpa only [Nat.cast_ofNat] using hbound
  have hint (σ : ℝ) (hσ : σ = (-1 / 2 : ℝ) ∨ σ = 2) :
      Integrable (fun t : ℝ => H ((σ : ℂ) + t * Complex.I)) := by
    obtain ⟨hL, B, hB, hLB⟩ := sharp_boundary_line_growth K σ hσ
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcontW : Continuous (fun t : ℝ => W ((σ : ℂ) + t * Complex.I)) :=
      hW.continuous.comp hline
    change Integrable (fun t : ℝ =>
      dedekindZetaLogDerivative K ((σ : ℂ) + t * Complex.I) * W ((σ : ℂ) + t * Complex.I))
    apply integrable_product_of_growth_decay _ _ hL.aestronglyMeasurable
      hcontW.aestronglyMeasurable B C hB.le hC.le hLB
    intro t
    have hσstrip : σ ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
      rcases hσ with h | h <;> norm_num [h]
    simpa using hWdecay ((σ : ℂ) + t * Complex.I)
      (by simpa using hσstrip.1) (by simpa using hσstrip.2)
  obtain ⟨a, b, ha, hb, hsigns, havoid, hbottom, htop⟩ :=
    good_contour_sequences K W C hC.le hWdecay
  let Z : ℕ → Finset ℂ := fun n => (zero_strip_finite K (a n) (b n)).toFinset
  have hZ (n : ℕ) (ρ : ℂ) :
      ρ ∈ Z n ↔ ρ ∈ nontrivialZeros K ∧ a n ≤ ρ.im ∧ ρ.im ≤ b n := by
    simp only [Z, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hF : Summable F := by
    simpa only [F, W, mul_assoc] using zero_family_summable f hdecay K x hx
  have hcover (ρ : ℂ) (hne : F ρ ≠ 0) : ∀ᶠ n in atTop, ρ ∈ Z n := by
    have hρ : ρ ∈ nontrivialZeros K := by
      by_contra hnot
      exact hne (by simp only [F, if_neg hnot])
    filter_upwards [ha.eventually (eventually_le_atBot ρ.im),
      hb.eventually (eventually_ge_atTop ρ.im)] with n hnlow hnup
    exact (hZ n ρ).mpr ⟨hρ, hnlow, hnup⟩
  have hsumF := finset_sum_tendsto_of_eventually_mem F hF Z hcover
  have hsumEq (n : ℕ) : (∑ ρ ∈ Z n, F ρ) =
      ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [F, if_pos ((hZ n ρ).mp hρ).1]
  have hsum : Tendsto (fun n : ℕ => ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ)
      atTop (𝓝 (∑' ρ : ℂ, F ρ)) := by
    simpa only [hsumEq] using hsumF
  have hright := MeasureTheory.intervalIntegral_tendsto_integral
    (hint 2 (Or.inr rfl)) ha hb
  have hleftlim := MeasureTheory.intervalIntegral_tendsto_integral
    (hint (-1 / 2) (Or.inl rfl)) ha hb
  have hrect (n : ℕ) := sharp_weighted_rectangle_identity K W hW (a n) (b n)
    (hsigns n).1 (hsigns n).2 (fun ρ hρ => (havoid n ρ hρ).1)
    (fun ρ hρ => (havoid n ρ hρ).2) (Z n) (hZ n)
  have hboundary : Tendsto (fun n : ℕ =>
      (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (a n : ℂ) * Complex.I)) -
        (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (b n : ℂ) * Complex.I)) +
        Complex.I * (∫ t : ℝ in a n..b n, H ((2 : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ in a n..b n, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)))
      atTop (𝓝 (Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)))) := by
    simpa only [H, Complex.ofReal_ofNat, sub_self, zero_add] using
      ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
        (hleftlim.const_mul Complex.I)
  have hresidue : Tendsto (fun n : ℕ => 2 * (Real.pi : ℂ) * Complex.I *
      (W 1 - N * W 0 - ∑ ρ ∈ Z n, (zeroMultiplicity K ρ : ℂ) * W ρ))
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I *
        (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hsum)
  have hlimit : Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := by
    exact tendsto_nhds_unique (hboundary.congr' (Filter.Eventually.of_forall hrect)) hresidue
  have hcancel : (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
      (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
      2 * (Real.pi : ℂ) * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      _ = Complex.I * (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) -
          Complex.I * (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by ring
      _ = 2 * (Real.pi : ℂ) * Complex.I * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) := hlimit
      _ = _ := by ring
  have hshift : verticalLineIntegral H 2 = W 1 - (∑' ρ : ℂ, F ρ) - N * W 0 +
      verticalLineIntegral H (-1 / 2) := by
    unfold verticalLineIntegral
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hcoef : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
    have he : (∫ t : ℝ, H ((2 : ℂ) + t * Complex.I)) =
        (2 * (Real.pi : ℂ)) * (W 1 - N * W 0 - ∑' ρ : ℂ, F ρ) +
          (∫ t : ℝ, H (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by
      linear_combination hcancel
    rw [he, mul_add, ← mul_assoc, inv_mul_cancel₀ hcoef, one_mul]
    ring
  have hW1 : W 1 = (x : ℂ) * mellinTransform f 1 := by
    dsimp [W]
    congr 1
    exact Complex.cpow_one (x : ℂ)
  have hW0 : W 0 = mellinTransform f 0 := by
    calc
      W 0 = (1 : ℂ) * mellinTransform f 0 :=
        congrArg (fun z : ℂ => z * mellinTransform f 0) (Complex.cpow_zero (x : ℂ))
      _ = _ := one_mul _
  rw [hW1, hW0] at hshift
  simpa only [H, W, F, N, mul_assoc] using hshift

theorem left_integral_bound (f : ℝ → ℝ)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (hleft : ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (t : ℝ),
      ‖dedekindZetaLogDerivative K ((-1 / 2 : ℝ) + t * Complex.I)‖ ≤
        C * (Real.log (absoluteDiscriminant K) +
          Module.finrank ℚ K * Real.log (2 + |t|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (x : ℝ), 2 ≤ x →
      ‖verticalLineIntegral (fun s : ℂ => dedekindZetaLogDerivative K s *
        Complex.cpow (x : ℂ) s * mellinTransform f s) (-1 / 2)‖ ≤
      C * Real.rpow x (-1 / 2 : ℝ) *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := hdecay 3 (-1 / 2) (-1 / 2) le_rfl
  obtain ⟨CL, hCL, hL⟩ := hleft
  refine ⟨CL * CΦ / 2, by positivity, ?_⟩
  intro K _ _ x hx
  have hxpos : 0 < x := by linarith
  have hdisc : 1 ≤ absoluteDiscriminant K := by
    have hNat : 1 ≤ (NumberField.discr K).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
    simpa [absoluteDiscriminant, Nat.cast_natAbs] using
      (show (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) by exact_mod_cast hNat)
  let d : ℝ := Real.log (absoluteDiscriminant K)
  let n : ℝ := Module.finrank ℚ K
  let X : ℝ := Real.rpow x (-1 / 2 : ℝ)
  let A : ℝ := CL * CΦ * X * (d + n)
  let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s *
    Complex.cpow (x : ℂ) s * mellinTransform f s
  let line : ℝ → ℂ := fun t => (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)
  have hd : 0 ≤ d := Real.log_nonneg hdisc
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hX : 0 < X := Real.rpow_pos_of_pos hxpos _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound (t : ℝ) : ‖H (line t)‖ ≤ A * (1 + t ^ 2)⁻¹ := by
    let u : ℝ := 1 + |t|
    have huone : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
    have hu : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) huone
    have hlog : Real.log (2 + |t|) ≤ u := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |t|)
      dsimp [u]
      linarith
    have hdgrow : d ≤ d * u := by nlinarith
    have hweight : d + n * Real.log (2 + |t|) ≤ (d + n) * u := by
      calc
        _ ≤ d + n * u := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hn)
        _ ≤ d * u + n * u := add_le_add hdgrow le_rfl
        _ = _ := by ring
    have hLbound : ‖dedekindZetaLogDerivative K (line t)‖ ≤ CL * ((d + n) * u) := by
      exact (hL K t).trans (mul_le_mul_of_nonneg_left hweight hCL.le)
    have hM : ‖mellinTransform f (line t)‖ ≤ CΦ * Real.rpow u (-3 : ℝ) := by
      simpa [line, u] using hΦ (line t) (by simp [line]) (by simp [line])
    have hcpow : ‖Complex.cpow (x : ℂ) (line t)‖ = X := by
      have hnorm : ‖Complex.cpow (x : ℂ) (line t)‖ = Real.rpow x (line t).re :=
        Complex.norm_cpow_eq_rpow_re_of_pos hxpos (line t)
      have hre : (line t).re = (-1 / 2 : ℝ) := by simp [line]
      exact hnorm.trans (congrArg (Real.rpow x) hre)
    have hpow : u * Real.rpow u (-3 : ℝ) = Real.rpow u (-2 : ℝ) := by
      calc
        _ = Real.rpow u (1 : ℝ) * Real.rpow u (-3 : ℝ) := by
          exact congrArg (fun z : ℝ => z * Real.rpow u (-3 : ℝ)) (Real.rpow_one u).symm
        _ = Real.rpow u ((1 : ℝ) + (-3 : ℝ)) := (Real.rpow_add hu _ _).symm
        _ = _ := by norm_num
    have hinv : Real.rpow u (-2 : ℝ) = (u ^ 2)⁻¹ :=
      (Real.rpow_neg hu.le (2 : ℝ)).trans
        (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_two u))
    have hsq : 1 + t ^ 2 ≤ u ^ 2 := by
      dsimp [u]
      nlinarith [abs_nonneg t, sq_abs t]
    have hcompare : Real.rpow u (-2 : ℝ) ≤ (1 + t ^ 2)⁻¹ := by
      rw [hinv]
      simpa only [one_div] using
        one_div_le_one_div_of_le (by positivity : 0 < 1 + t ^ 2) hsq
    calc
      ‖H (line t)‖ = ‖dedekindZetaLogDerivative K (line t)‖ * X *
          ‖mellinTransform f (line t)‖ := by
        change ‖dedekindZetaLogDerivative K (line t) *
          Complex.cpow (x : ℂ) (line t) * mellinTransform f (line t)‖ = _
        rw [norm_mul, norm_mul, hcpow]
      _ ≤ (CL * ((d + n) * u)) * X * (CΦ * Real.rpow u (-3 : ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hLbound hX.le
        · exact hM
        · exact norm_nonneg _
        · positivity
      _ = A * (u * Real.rpow u (-3 : ℝ)) := by dsimp [A]; ring
      _ = A * Real.rpow u (-2 : ℝ) := by rw [hpow]
      _ ≤ A * (1 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hcompare hA
  have hmajor : Integrable (fun t : ℝ => A * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  have hint : ‖∫ t : ℝ, H (line t)‖ ≤ A * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, A * (1 + t ^ 2)⁻¹ :=
        MeasureTheory.norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hbound)
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  have hcoef : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  change ‖verticalLineIntegral H (-1 / 2)‖ ≤ CL * CΦ / 2 * X * (d + n)
  calc
    ‖verticalLineIntegral H (-1 / 2)‖ = (2 * Real.pi)⁻¹ * ‖∫ t : ℝ, H (line t)‖ := by
      rw [verticalLineIntegral, norm_mul, hcoef]
    _ ≤ (2 * Real.pi)⁻¹ * (A * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = CL * CΦ / 2 * X * (d + n) := by
      dsimp [A]
      field_simp [Real.pi_ne_zero]
      <;> ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
