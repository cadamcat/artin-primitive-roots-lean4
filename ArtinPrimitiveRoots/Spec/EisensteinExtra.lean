import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.LinearAlgebra.Countable

/-! Remaining Eisenstein and resolvent nodes E3--E7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- E3 `spec:eis-smooth` — P-SPEC.md:239, 385–388. In the convergence region, the series is
smooth with normally convergent coordinate derivatives and is an eigenfunction of every partial
Laplacian. -/
theorem E3_eis_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) :
    IsSmoothX F (eisSeries F Γ σ s) ∧
    (∀ w z, partialLap F w (eisSeries F Γ σ s) z =
      (1 - 4 * s ^ 2) * eisSeries F Γ σ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
          ∀ q, ∀ p, p ∈ K →
            ‖iteratedFDeriv ℝ n
              (fun p => eisTerm F Γ σ s (ptX F p) q) p v‖ ≤ m q) := by
  sorry

/-- E4 `spec:eis-siegel` — P-SPEC.md:240, 390–395. On each Siegel set there is at most one
upper-triangular seed coset; the remaining terms and their gradients are uniformly summable on
compact parameter sets in `2 < Re s < 3`. Correction from review lane `rev-spec`: state pointwise
summability and use the corrected Siegel set. Correction from `sol-gate-spec`: use the field norm
of the triangular matrix's upper-left entry in the leading term. -/
theorem E4_eis_siegel (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F))
    (Kₛ : Set ℂ) (hKₛ : IsCompact Kₛ)
    (hKₛstrip : Kₛ ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3}) :
    ∀ i : d.ι,
      (∀ q q' : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F → q = q') ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
        Summable (fun q' : {q : CuspCosets F Γ σ //
          σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F} =>
            (‖eisTerm F Γ σ s ((d.σ i) • z) q'.1‖ +
              ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q'.1) z‖)) ∧
        (∑' q' : {q : CuspCosets F Γ σ //
          σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F},
          (‖eisTerm F Γ σ s ((d.σ i) • z) q'.1‖ +
            ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q'.1) z‖)) ≤ C) ∧
      (∀ q : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
          let b := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i
          eisTerm F Γ σ s ((d.σ i) • z) q =
            ((absFieldNorm F (b 0 0) : ℝ) : ℂ) ^ (1 + 2 * s) *
              ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  sorry

/-- E5 `spec:seed` — P-SPEC.md:241, 131–133. The truncated seed and its defect are locally finite,
smooth and invariant; the defect is compactly supported modulo `Γ`, entire as an `L²` family, and
has the explicit height-only formula in the active cusp. Correction from review lane `rev-spec`:
include the cusp-separation property at the cutoff threshold. -/
theorem E5_seed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∀ s z,
      {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0}.Finite ∧
      (Nat.card {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0} ≤ 1)) ∧
    (∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
      ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
        spectralParameter F s * eisSeed F Γ σ τ s z = eisSeedDefect F Γ σ τ s z) ∧
    (∃ K : Set (X F), IsCompact K ∧ ∀ s,
      {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ orbitSaturation F Γ K) ∧
    (∃ G : ℂ → L2Space F D, AnalyticOnNhd ℂ G Set.univ ∧
      ∀ s, ∀ᵐ z ∂(volX F), z ∈ D → G s z = eisSeedDefect F Γ σ τ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
          ∀ s p, Φ s p = iteratedFDeriv ℝ n
            (fun q => eisSeed F Γ σ τ s (ptX F q)) p v) ∧
    (∀ s z, z ∈ cuspTail F Γ σ A₀ →
      ∃ γ : Γ,
        eisSeedDefect F Γ σ τ s z =
          -(placeCount F : ℂ) *
            (((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ 2 *
                deriv (deriv (fun t : ℝ => (τ t : ℂ)))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) +
              (1 + 4 * s) *
                ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) *
                deriv (fun t : ℝ => (τ t : ℂ))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) ) *
            ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  sorry

/-- E6 `spec:identify` — P-SPEC.md:242, 397–400. On the convergence ball, the series minus its
cutoff seed is bounded with bounded gradient, lies in the energy graph, and solves the weak
resolvent equation with source equal to the negative seed defect. Correction from `sol-gate-spec`:
require a genuine separated cusp cutoff and calibrated energy representatives. -/
theorem E6_identify (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ) (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (gL2 : L2Space F D)
    (hg : ∀ᵐ z ∂(volX F), z ∈ D →
      gL2 z = eisSeedDefect F Γ σ τ s z) :
    let w := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖w z‖ ≤ B ∧ ‖fullGradient F w z‖ ≤ B) ∧
    (∃ x : E.V, (∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z) ∧
      (∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z) ∧
      E.M x = faResolvent E (spectralParameter F s) (-gL2)) := by
  sorry

/-- The compact energy error and strict Fredholm threshold used by E7. The `sol-gate-spec`
correction makes the compact coercivity input and its center threshold explicit. -/
structure SpectralGapData {D : Set (X F)}
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D)) (s₁ : ℝ) where
  K : E.V →L[ℂ] L2Space F D
  compact : IsCompactOperator K
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  estimate : ∀ x : E.V, ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2
  below : placeCount F * (1 - 4 * s₁ ^ 2) < 1 / c

private def specContinuousLinearSandwich {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (L : A →L[ℂ] B) (R : B →L[ℂ] A) :
    (A →L[ℂ] A) →L[ℂ] (B →L[ℂ] B) :=
  (ContinuousLinearMap.compL ℂ B A B L).comp
    ((ContinuousLinearMap.compL ℂ B A A).flip R)

set_option maxHeartbeats 1000000

/-- E7 `spec:l2-cont` — P-SPEC.md:243, 402–404. The correction is analytic on the connected
continuation domain and has a simple pole at `s₁` with the stated projected-resolvent residue.
Correction from `sol-gate-spec`: use the actual seed-defect source, calibrated energy graph, and
compact Fredholm estimate below the center. -/
theorem E7_l2_cont (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (s₁ : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1 / 2)
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) (gap : SpectralGapData E s₁)
    (G : ℂ → L2Space F D) (hG : AnalyticOnNhd ℂ G Set.univ)
    (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (hsource : ∀ s, ∀ᵐ z ∂(volX F), z ∈ D →
      G s z = eisSeedDefect F Γ σ τ s z)
    (lam₁ : ℝ)
    (hLam1 : lam₁ = placeCount F * (1 - 4 * s₁ ^ 2))
    (P : E.V →L[ℂ] E.V) (N : Submodule ℂ E.V)
    (hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P ∧
      N = (E.A (lam₁ : ℂ)).toLinearMap.ker)
    (κ : ℝ) (hκ : κ = (lam₁ + 1) / (8 * placeCount F * s₁)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s₁ ∧
      let u : ℂ → L2Space F D := fun s =>
        faResolvent E (spectralParameter F s) (-G s)
      let θ : L2Space F D := -κ • (E.M.comp (P.comp E.M.adjoint)) (G (s₁ : ℂ))
      AnalyticOnNhd ℂ u (contDomain s₁ ε) ∧
      (∃ Ψ : ℂ → L2Space F D,
        AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s) ∧
      ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
        ∀ᵐ z ∂(volX F), z ∈ D →
          l2Lift F Γ D (u s) z =
            eisSeries F Γ σ s z - eisSeed F Γ σ τ s z := by
  classical
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hsprod : 0 ≤ (1 / 2 - s₁) * (1 / 2 + s₁) :=
    mul_nonneg (by linarith) (by linarith)
  have hbase : 0 ≤ 1 - 4 * s₁ ^ 2 := by nlinarith [hsprod]
  have hlam₁_nonneg : 0 ≤ lam₁ := by
    rw [hLam1]
    exact mul_nonneg hr.le hbase
  have hlam₁_lt : lam₁ < 1 / gap.c := by
    rw [hLam1]
    exact gap.below
  have hF := F2_resolvent E gap.K gap.compact gap.c gap.C
    gap.c_pos gap.C_nonneg gap.estimate
  have hOff := hF.2.2.1
  have hInvAnalytic := hF.2.2.2.1
  have hlocal := hF.2.2.2.2.1 lam₁ hlam₁_nonneg hlam₁_lt
  rcases hlocal with ⟨_, _, hlocalP⟩
  rcases hlocalP with ⟨P₀, δ, B, hδ, hP₀id, hP₀range, hP₀self, hB, hExpand⟩
  let ε : ℝ := min s₁ (δ / (24 * placeCount F * s₁))
  have hεden : 0 < 24 * placeCount F * s₁ := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hs₀ (div_pos hδ hεden)
  have hεle : ε ≤ s₁ := min_le_left _ _
  have hsq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hsq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]
    ring
  have hinner_re (z : ℂ) :
      (1 - 4 * z ^ 2).re = 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 := by
    calc
      (1 - 4 * z ^ 2).re = 1 - (4 * z ^ 2).re := by
        rw [Complex.sub_re]
        simp only [Complex.one_re]
      _ = 1 - 4 * (z ^ 2).re := by
        rw [Complex.mul_re]
        norm_num
      _ = 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 := by rw [hsq_re]; ring
  have hinner_im (z : ℂ) :
      (1 - 4 * z ^ 2).im = -8 * z.re * z.im := by
    calc
      (1 - 4 * z ^ 2).im = -(4 * z ^ 2).im := by
        rw [Complex.sub_im]
        simp only [Complex.one_im, zero_sub]
      _ = -4 * (z ^ 2).im := by
        rw [Complex.mul_im]
        norm_num
      _ = -8 * z.re * z.im := by rw [hsq_im]; ring
  have hparam_re (z : ℂ) :
      (spectralParameter F z).re =
        placeCount F * (1 - 4 * z.re ^ 2 + 4 * z.im ^ 2) := by
    change ((placeCount F : ℂ) * (1 - 4 * z ^ 2)).re = _
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinner_re]
  have hparam_im (z : ℂ) :
      (spectralParameter F z).im = -8 * placeCount F * z.re * z.im := by
    change ((placeCount F : ℂ) * (1 - 4 * z ^ 2)).im = _
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, hinner_im]
    ring
  have hparamAnalytic : AnalyticOnNhd ℂ (spectralParameter F) Set.univ := by
    intro z hz
    fun_prop [spectralParameter]
  have hstripOff (z : ℂ)
      (hz : z ∈ {s : ℂ | 0 < s.re ∧ s.re < 4 ∧ 0 < s.im ∧ s.im < 1}) :
      ¬ ((spectralParameter F z).im = 0 ∧ 0 ≤ (spectralParameter F z).re) := by
    have hne : (spectralParameter F z).im ≠ 0 := by
      rw [hparam_im]
      have hre : z.re ≠ 0 := ne_of_gt hz.1
      have him : z.im ≠ 0 := ne_of_gt hz.2.2.1
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hr)) hre) him
    exact fun h => hne h.1
  have hconvOff (z : ℂ)
      (hz : z ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
      ¬ ((spectralParameter F z).im = 0 ∧ 0 ≤ (spectralParameter F z).re) := by
    have hdist : ‖z - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreabs : |z.re - (5 / 2 : ℝ)| < 1 / 2 := by
      have h := Complex.abs_re_le_norm (z - (5 / 2 : ℂ))
      have hre : (z - (5 / 2 : ℂ)).re = z.re - (5 / 2 : ℝ) := by simp
      rw [hre] at h
      exact lt_of_le_of_lt h hdist
    have himabs : |z.im| < 1 / 2 := by
      have h := Complex.abs_im_le_norm (z - (5 / 2 : ℂ))
      have him : (z - (5 / 2 : ℂ)).im = z.im := by simp
      rw [him] at h
      exact lt_of_le_of_lt h hdist
    have hre : 2 < z.re := by
      have h := (abs_lt.mp hreabs).1
      norm_num at h
      linarith
    have himsq : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      have h := abs_lt.mp himabs
      nlinarith
    have hreal : (spectralParameter F z).re < 0 := by
      rw [hparam_re]
      have hq : 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hr hq
    exact fun h => (not_le_of_gt hreal) h.2
  have hfaStrip : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      {z : ℂ | 0 < z.re ∧ z.re < 4 ∧ 0 < z.im ∧ z.im < 1} := by
    exact hInvAnalytic.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact hstripOff z hz)
  have hfaConv : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
    exact hInvAnalytic.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact hconvOff z hz)
  have hparamCenter : spectralParameter F (s₁ : ℂ) = (lam₁ : ℂ) := by
    rw [hLam1]
    simp [spectralParameter]
    <;> ring
  have hfactor (z : ℂ) :
      (lam₁ : ℂ) - spectralParameter F z =
        4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ)) := by
    rw [← hparamCenter]
    simp [spectralParameter]
    ring
  have hdistToCenter (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      ‖z - (s₁ : ℂ)‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hsumNorm (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      ‖z + (s₁ : ℂ)‖ ≤ 3 * s₁ := by
    have heq : z + (s₁ : ℂ) = (z - (s₁ : ℂ)) + (2 * (s₁ : ℂ)) := by ring
    rw [heq]
    have hnorm2 : ‖(2 * (s₁ : ℂ))‖ = 2 * s₁ := by
      have hcast : (2 * (s₁ : ℂ)) = ((2 * s₁ : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      ‖(z - (s₁ : ℂ)) + 2 * (s₁ : ℂ)‖ ≤
          ‖z - (s₁ : ℂ)‖ + ‖2 * (s₁ : ℂ)‖ := norm_add_le _ _
      _ ≤ ε + 2 * s₁ := add_le_add (le_of_lt (hdistToCenter z hz)) (le_of_eq hnorm2)
      _ ≤ 3 * s₁ := by nlinarith [hεle]
  have himage (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      spectralParameter F z ∈ Metric.ball (lam₁ : ℂ) δ := by
    have hnormfactor :
        ‖(lam₁ : ℂ) - spectralParameter F z‖ ≤
          12 * placeCount F * s₁ * ε := by
      rw [hfactor]
      have hnorm :
          ‖4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ))‖ =
            4 * placeCount F * ‖z - (s₁ : ℂ)‖ * ‖z + (s₁ : ℂ)‖ := by
        simp [norm_mul, Complex.norm_real, abs_of_pos hr]
        <;> ring
      rw [hnorm]
      calc
        4 * placeCount F * ‖z - (s₁ : ℂ)‖ * ‖z + (s₁ : ℂ)‖ ≤
            4 * placeCount F * ε * (3 * s₁) := by
              gcongr
              · exact le_of_lt (hdistToCenter z hz)
              · exact hsumNorm z hz
        _ = 12 * placeCount F * s₁ * ε := by ring
    have hsmall : 12 * placeCount F * s₁ * ε < δ := by
      have hden : 0 < 24 * placeCount F * s₁ :=
        hεden
      have hε' : ε ≤ δ / (24 * placeCount F * s₁) := min_le_right _ _
      have hmul : 12 * placeCount F * s₁ * ε ≤
          12 * placeCount F * s₁ * (δ / (24 * placeCount F * s₁)) :=
        mul_le_mul_of_nonneg_left hε' (by positivity)
      have hval : 12 * placeCount F * s₁ *
          (δ / (24 * placeCount F * s₁)) = δ / 2 := by
        field_simp [hden.ne']
        ring
      rw [hval] at hmul
      linarith [hδ]
    have hdist : dist (spectralParameter F z) (lam₁ : ℂ) < δ := by
      rw [dist_eq_norm, norm_sub_rev]
      exact lt_of_le_of_lt hnormfactor hsmall
    exact Metric.mem_ball.mpr hdist
  have hsum_ne (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      z + (s₁ : ℂ) ≠ 0 := by
    intro h
    have hzeq : z = -(s₁ : ℂ) := by
      calc
        z = z + (s₁ : ℂ) - (s₁ : ℂ) := by ring
        _ = -(s₁ : ℂ) := by rw [h]; ring
    have hdist := hdistToCenter z hz
    have hbelow : ‖z - (s₁ : ℂ)‖ < s₁ := lt_of_lt_of_le hdist hεle
    have heq : -(s₁ : ℂ) - (s₁ : ℂ) = ((-2 * s₁ : ℝ) : ℂ) := by push_cast; ring
    have hbelow' : ‖((-2 * s₁ : ℝ) : ℂ)‖ < s₁ := by simpa [hzeq, heq] using hbelow
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : -2 * s₁ ≤ 0)] at hbelow'
    linarith
  have hparam_ne (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε)
      (hne : z ≠ (s₁ : ℂ)) : spectralParameter F z ≠ (lam₁ : ℂ) := by
    intro heq
    have hprodne :
        4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (by exact_mod_cast hr.ne')
        · exact sub_ne_zero.mpr hne
      · exact hsum_ne z hz
    apply hprodne
    rw [← hfactor, heq]
    simp
  have hInvPunct : AnalyticOnNhd ℂ (faInverse E)
      (Metric.ball (lam₁ : ℂ) δ \ {(lam₁ : ℂ)}) := by
    intro z hz
    have hzball : z ∈ Metric.ball (lam₁ : ℂ) δ := hz.1
    have hzne : z ≠ (lam₁ : ℂ) := by simpa using hz.2
    have hopen : IsOpen (Metric.ball (lam₁ : ℂ) δ \ {(lam₁ : ℂ)}) :=
      IsOpen.sdiff Metric.isOpen_ball isClosed_singleton
    have heq : faInverse E =ᶠ[𝓝 z] fun w : ℂ =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹) • P₀ + B w := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact (hExpand w hw.1 (by simpa using hw.2)).2
    have hform : AnalyticAt ℂ (fun w : ℂ =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹) • P₀ + B w) z := by
      let coeff : ℂ → ℂ := fun w =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹)
      have hden : (lam₁ : ℂ) - z ≠ 0 := sub_ne_zero.mpr hzne.symm
      have hcoef : AnalyticAt ℂ coeff z := by
        dsimp [coeff]
        fun_prop
      let smulP : ℂ →L[ℂ] (E.V →L[ℂ] E.V) :=
        ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) P₀
      have hsmulMap : AnalyticAt ℂ (fun c : ℂ => smulP c) (coeff z) :=
        ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
          (F := E.V →L[ℂ] E.V) smulP (coeff z)
      have hsmul : AnalyticAt ℂ (fun w : ℂ => coeff w • P₀) z := by
        have h := hsmulMap.comp_of_eq hcoef rfl
        have h' : AnalyticAt ℂ (fun w : ℂ => smulP (coeff w)) z := by
          change AnalyticAt ℂ ((fun c : ℂ => smulP c) ∘ coeff) z
          exact h
        have heq : (fun w : ℂ => smulP (coeff w)) =
            (fun w : ℂ => coeff w • P₀) := by
          funext w
          simp [smulP, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.id_apply]
        rw [heq] at h'
        exact h'
      exact hsmul.add (hB z hzball)
    exact hform.congr heq.symm
  have hfaPunct : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}) := by
    exact hInvPunct.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact ⟨himage z hz.1, hparam_ne z hz.1 (by simpa using hz.2)⟩)
  have hfaDomain : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z)) (contDomain s₁ ε) := by
    intro z hz
    have hz' : z ∈ ({w : ℂ | 0 < w.re ∧ w.re < 4 ∧ 0 < w.im ∧ w.im < 1} ∪
        Metric.ball (5 / 2 : ℂ) (1 / 2)) ∪
        (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}) := by
      simpa [contDomain] using hz
    rcases hz' with hleft | hpunct
    · rcases hleft with hstrip | hconv
      · exact hfaStrip z hstrip
      · exact hfaConv z (by simpa using hconv)
    · exact hfaPunct z hpunct
  let sandwich : (E.V →L[ℂ] E.V) →L[ℂ]
      (L2Space F D →L[ℂ] L2Space F D) :=
    @specContinuousLinearSandwich E.V (L2Space F D)
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) E.M E.M.adjoint
  have hu : AnalyticOnNhd ℂ
      (fun z : ℂ => faResolvent E (spectralParameter F z) (-G z))
      (contDomain s₁ ε) := by
    intro z hz
    have hfa := hfaDomain z hz
    have hmap : AnalyticAt ℂ (fun T : E.V →L[ℂ] E.V => sandwich T)
        (faInverse E (spectralParameter F z)) :=
      ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E.V →L[ℂ] E.V)
        (F := L2Space F D →L[ℂ] L2Space F D) sandwich
        (faInverse E (spectralParameter F z))
    have hresOp : AnalyticAt ℂ
        (fun w : ℂ => faResolvent E (spectralParameter F w)) z := by
      have hcomp := hmap.comp_of_eq hfa rfl
      have heq : ((fun T : E.V →L[ℂ] E.V => sandwich T) ∘
          (fun w : ℂ => faInverse E (spectralParameter F w))) =
          (fun w : ℂ => faResolvent E (spectralParameter F w)) := by
        funext w
        simp [faResolvent, sandwich, specContinuousLinearSandwich,
          ContinuousLinearMap.compL_apply]
      rw [heq] at hcomp
      exact hcomp
    have hGneg : AnalyticAt ℂ (fun w : ℂ => -G w) z := by
      have hGz := hG z (Set.mem_univ z)
      fun_prop
    have happ : AnalyticAt ℂ
        (fun p : L2Space F D × (L2Space F D →L[ℂ] L2Space F D) =>
          (ContinuousLinearMap.apply ℂ (L2Space F D) p.1) p.2)
        (-G z, faResolvent E (spectralParameter F z)) := by
      let eval : L2Space F D →L[ℂ]
          (L2Space F D →L[ℂ] L2Space F D) →L[ℂ] L2Space F D :=
        ContinuousLinearMap.apply ℂ (L2Space F D)
      exact eval.analyticAt_bilinear (-G z, faResolvent E (spectralParameter F z))
    have hresult := happ.comp₂ hGneg hresOp
    simpa only [ContinuousLinearMap.apply_apply] using hresult
  have hNclosed : IsClosed (N : Set E.V) := by
    rw [hP.2.2.2]
    exact (E.A (lam₁ : ℂ)).isClosed_ker
  letI : CompleteSpace N := hNclosed.completeSpace_coe
  letI : N.HasOrthogonalProjection := inferInstance
  have hprojection_eq_star (Q : E.V →L[ℂ] E.V)
      (hQr : Q.range = N) (hQid : Q.comp Q = Q) (hQs : IsSelfAdjoint Q) :
      Q = N.starProjection := by
    ext x
    have hmem : Q x ∈ N := by
      have hx : Q x ∈ Q.range := ⟨x, rfl⟩
      rw [hQr] at hx
      exact hx
    have hQon (y : E.V) (hy : y ∈ N) : Q y = y := by
      have hy' : y ∈ Q.range := by rw [hQr]; exact hy
      obtain ⟨y', hy'⟩ := hy'
      have hQidApply : Q (Q y') = Q y' := by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (fun T : E.V →L[ℂ] E.V => T y') hQid
      calc
        Q y = Q (Q y') := congrArg Q hy'.symm
        _ = Q y' := hQidApply
        _ = y := hy'
    have horth : ∀ y ∈ N, inner ℂ (x - Q x) y = 0 := by
      intro y hy
      rw [inner_sub_left]
      have hsym : inner ℂ (Q x) y = inner ℂ x (Q y) := by
        simpa only [ContinuousLinearMap.coe_coe] using hQs.isSymmetric x y
      rw [hsym, hQon y hy, sub_self]
    exact congrArg Subtype.val
      (N.eq_starProjection_of_mem_of_inner_eq_zero hmem horth).symm
  have hP_eq_P₀ : P = P₀ := by
    have hP₀range' : P₀.range = N := by
      calc
        P₀.range = (E.A (lam₁ : ℂ)).toLinearMap.ker := hP₀range
        _ = N := hP.2.2.2.symm
    calc
      P = N.starProjection := hprojection_eq_star P hP.1 hP.2.1 hP.2.2.1
      _ = P₀ := (hprojection_eq_star P₀ hP₀range' hP₀id hP₀self).symm
  have hLiftOnD (v : L2Space F D) :
      ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D v z = v z := by
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
    letI : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
    letI : Countable (Fin 2 → 𝓞 F) := inferInstance
    letI : Countable (Fin 2 → Fin 2 → 𝓞 F) := inferInstance
    letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
      change Countable (Fin 2 → Fin 2 → 𝓞 F)
      infer_instance
    letI : Countable (SL(2,𝓞 F)) :=
      (Subtype.val_injective : Function.Injective
        (fun g : SL(2,𝓞 F) => (g : Matrix (Fin 2) (Fin 2) (𝓞 F)))).countable
    letI : Countable Γ :=
      (Subtype.val_injective : Function.Injective
        (fun γ : Γ => (γ : SL(2,𝓞 F)))).countable
    have hnoOverlap : ∀ᵐ z ∂(volX F),
        ∀ γ : Γ, γ ≠ 1 → z ∈ D → (γ : SL(2,𝓞 F)) • z ∉ D := by
      rw [ae_all_iff]
      intro γ
      by_cases hγ : γ = 1
      · filter_upwards [] with z hne hzD
        exact False.elim (hne hγ)
      · have hneInv : γ⁻¹ ≠ (1 : Γ) := by simpa using hγ
        have hdis := hD.aedisjoint (i := γ⁻¹) (j := (1 : Γ)) hneInv
        have hsdiff := hdis.sdiff_ae_eq_right
        filter_upwards [hsdiff] with z hz
        intro hne hzD hγz
        have hzOne : z ∈ (1 : Γ) • D := by
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          simpa using hzD
        have hmem := hz.mpr hzOne
        have hnot := (Set.mem_sdiff z).mp hmem |>.2
        have htranslate : z ∈ (γ⁻¹ : Γ) • D := by
          have hscalar : (((γ⁻¹ : Γ)⁻¹ : Γ) : SL(2,𝓞 F)) =
              (γ : SL(2,𝓞 F)) := by simp
          rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
          change (((γ⁻¹ : Γ)⁻¹ : Γ) : SL(2,𝓞 F)) • z ∈ D
          rw [hscalar]
          exact hγz
        exact hnot htranslate
    filter_upwards [hnoOverlap] with z hzGood hzD
    rw [l2Lift]
    have hterm (γ : Γ) (hγ : γ ≠ 1) :
        (if (γ : SL(2,𝓞 F)) • z ∈ D then
          v ((γ : SL(2,𝓞 F)) • z) else 0) = 0 := by
      have hzγ := hzGood γ hγ hzD
      simp [hzγ]
    rw [tsum_eq_single (1 : Γ) hterm]
    simp [hzD]
  let C₀ : L2Space F D →L[ℂ] L2Space F D := sandwich P
  let C₁ : ℂ → L2Space F D →L[ℂ] L2Space F D := fun z =>
    sandwich (B (spectralParameter F z))
  let a : ℂ → ℂ := fun z =>
    -(((lam₁ + 1 : ℝ) : ℂ) /
      ((4 : ℂ) * (placeCount F : ℂ) * (z + (s₁ : ℂ))))
  let Ψ : ℂ → L2Space F D := fun z =>
    a z • C₀ (G z) - (z - (s₁ : ℂ)) • C₁ z (G z)
  have hBparam : AnalyticOnNhd ℂ (fun z : ℂ => B (spectralParameter F z))
      (Metric.ball (s₁ : ℂ) ε) := by
    exact hB.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact himage z hz)
  have hC₁analytic : AnalyticOnNhd ℂ C₁ (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    change AnalyticAt ℂ (fun w : ℂ => sandwich (B (spectralParameter F w))) z
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E.V →L[ℂ] E.V)
      (F := L2Space F D →L[ℂ] L2Space F D) sandwich
      (B (spectralParameter F z))).comp_of_eq (hBparam z hz) rfl
  have hC₀G : AnalyticOnNhd ℂ (fun z : ℂ => C₀ (G z))
      (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hGz := hG z (Set.mem_univ z)
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := L2Space F D) (F := L2Space F D) C₀ (G z)).comp_of_eq hGz rfl
  have hC₁G : AnalyticOnNhd ℂ (fun z : ℂ => C₁ z (G z))
      (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hCz := hC₁analytic z hz
    have hGz := hG z (Set.mem_univ z)
    have happ : AnalyticAt ℂ
        (fun p : L2Space F D × (L2Space F D →L[ℂ] L2Space F D) =>
          (ContinuousLinearMap.apply ℂ (L2Space F D) p.1) p.2)
        (G z, C₁ z) := by
      let eval : L2Space F D →L[ℂ]
          (L2Space F D →L[ℂ] L2Space F D) →L[ℂ] L2Space F D :=
        ContinuousLinearMap.apply ℂ (L2Space F D)
      exact eval.analyticAt_bilinear (G z, C₁ z)
    have hresult := happ.comp₂ hGz hCz
    simpa only [ContinuousLinearMap.apply_apply] using hresult
  have haAnalytic : AnalyticOnNhd ℂ a (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hsum := hsum_ne z hz
    have hden : (4 : ℂ) * (placeCount F : ℂ) * (z + (s₁ : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast hr.ne')
      · exact hsum
    dsimp [a]
    fun_prop
  have hΨAnalytic : AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have haz := haAnalytic z hz
    have hC₀z := hC₀G z hz
    have hC₁z := hC₁G z hz
    have hterm₁ : AnalyticAt ℂ (fun w : ℂ => a w • C₀ (G w)) z := haz.smul hC₀z
    have hscale₂ : AnalyticAt ℂ (fun w : ℂ => w - (s₁ : ℂ)) z :=
      analyticAt_id.sub analyticAt_const
    have hterm₂ : AnalyticAt ℂ
        (fun w : ℂ => (w - (s₁ : ℂ)) • C₁ w (G w)) z := hscale₂.smul hC₁z
    have hsub := hterm₁.sub hterm₂
    have hfun :
        (fun w : ℂ => a w • C₀ (G w)) -
            (fun w : ℂ => (w - (s₁ : ℂ)) • C₁ w (G w)) =
          (fun w : ℂ => a w • C₀ (G w) - (w - (s₁ : ℂ)) • C₁ w (G w)) := by
      funext w
      rfl
    rw [hfun] at hsub
    exact hsub
  have haCenter : a (s₁ : ℂ) = -(κ : ℂ) := by
    dsimp [a]
    rw [hκ]
    push_cast
    field_simp [hr.ne', hs₀.ne']
    <;> ring
  refine ⟨ε, hε, hεle, ?_, ?_, ?_⟩
  · exact hu
  · refine ⟨Ψ, hΨAnalytic, ?_, ?_⟩
    · dsimp [Ψ]
      simp [haCenter, C₀, sandwich, specContinuousLinearSandwich,
        ContinuousLinearMap.compL_apply] <;> rfl
    · intro z hz hzne
      have hExpz := hExpand (spectralParameter F z) (himage z hz)
        (hparam_ne z hz hzne)
      have hExpz' : faInverse E (spectralParameter F z) =
          (((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹) • P +
            B (spectralParameter F z) := by
        rw [hP_eq_P₀]
        exact hExpz.2
      have hscalar : (z - (s₁ : ℂ)) *
          (((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹) = -a z := by
        rw [hfactor]
        dsimp [a]
        have hrC : (placeCount F : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
        field_simp [hrC, sub_ne_zero.mpr hzne, hsum_ne z hz]
        <;> ring
      have hres : faResolvent E (spectralParameter F z) (-G z) =
          -((((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹)) • C₀ (G z) -
            C₁ z (G z) := by
        rw [faResolvent, hExpz']
        simp [C₀, C₁, sandwich, specContinuousLinearSandwich,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.map_neg,
          ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
        <;> abel
      change Ψ z = (z - (s₁ : ℂ)) •
        faResolvent E (spectralParameter F z) (-G z)
      dsimp [Ψ]
      rw [hres]
      simp only [smul_sub, smul_smul, mul_neg]
      rw [hscalar]
      simp
  · intro s hs
    have hE6 := E6_identify Γ D hD σ τ cut s hs E e (G s) (hsource s)
    obtain ⟨x, hM, hGr, hRes⟩ := hE6.2
    have hRes' : ∀ᵐ z ∂(volX F), z ∈ D →
        E.M x z = faResolvent E (spectralParameter F s) (-G s) z :=
      MeasureTheory.ae_imp_of_ae_restrict (Lp.ext_iff.mp hRes)
    have hLift := hLiftOnD (faResolvent E (spectralParameter F s) (-G s))
    filter_upwards [hLift, hRes', hM] with z hzL hzR hzM
    intro hzD
    exact (hzL hzD).trans ((hzR hzD).symm.trans (hzM hzD))

end ArtinPrimitiveRoots.A1.Spec
