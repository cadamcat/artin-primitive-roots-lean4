import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.constantCell_finite_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.regularized_cprod_continuation
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.regularized_residue_eval
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.torusCoeff_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.adapted_domain_measurable_representative

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Assemble the finite analytic cell sums, the Euler-product regularization, and the torus
Laurent value to obtain the constant term.
Uses constantCell_finite_analytic, regularized_cprod_continuation, torusCoeff_analytic,
regularized_residue_eval, adapted_domain_measurable_representative, eisenstein_constantTerm.
Feeds the frozen theta_constantTerm with fourierRawM definitionally equal to its famM scalar. -/
theorem theta_constantTerm_assembly {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (hEuler : FourierEulerHyp T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : FourierIdealFix sec g 𝔞) (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) :
    torusCoeff P R.theta g Pd 0 = (κF F)⁻¹ *
      (limUnder (𝓝[>] (1 / 6 : ℝ))
        (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ))) *
      ∑' δ : Fˣ ⧸ G.Δ, fourierRawM μ sec (1 / 6)
        (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
  obtain ⟨Q, hmQ, hbQ, hQ, hQeq⟩ :=
    adapted_domain_measurable_representative 𝔞 Pd hPd hb
  obtain ⟨η, hη, hηε, hηle, htorus⟩ :=
    torusCoeff_analytic hFam R g 𝔞 h𝔞 hfix Q hQ hbQ hmQ 0
  obtain ⟨T, hzero, hsmall, hlarge⟩ := constantCell_finite_analytic hFam g
  obtain ⟨B, hB, hB0, hBeq⟩ := regularized_cprod_continuation T0 hEuler
  let a (s : ℂ) (δ : Fˣ ⧸ G.Δ) :=
    scalarOf P G (sec s).f (sec s).fC (P.tc.rat (diagGL (Quotient.out δ)) * g)
  let b (s : ℂ) (δ : Fˣ ⧸ G.Δ) :=
    fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g)
  let Φ (s : ℂ) := (s - 1 / 6) * (∑ δ ∈ T, a s δ) +
    (κF F)⁻¹ * B s * (∑ δ ∈ T, b s δ)
  have hΦ : AnalyticOnNhd ℂ Φ {s | 0 < s.re} := by
    have ha : AnalyticOnNhd ℂ (fun s => ∑ δ ∈ T, a s δ) {s | 0 < s.re} :=
      Finset.analyticOnNhd_fun_sum T hsmall
    have hb' : AnalyticOnNhd ℂ (fun s => ∑ δ ∈ T, b s δ) {s | 0 < s.re} :=
      Finset.analyticOnNhd_fun_sum T hlarge
    have hd : AnalyticOnNhd ℂ (fun s : ℂ => s - 1 / 6) {s | 0 < s.re} := by
      fun_prop
    have hk : AnalyticOnNhd ℂ (fun _ : ℂ => (((κF F)⁻¹ : ℝ) : ℂ)) {s | 0 < s.re} := by
      fun_prop
    exact (hd.mul ha).add ((hk.mul hB).mul hb')
  have hscalar (s : ℂ) (δ : Fˣ ⧸ G.Δ) :
      scalarM P G μ (sec s) (P.tc.rat (diagGL (Quotient.out δ)) * g) =
        (κF F)⁻¹ * cprod T0 s * b s δ := by
    simp only [scalarM, b, fourierRawM, hFam.T0_eq]
  have heq : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      (s - 1 / 6) * torusCoeff P (R.E s) g Q 0 = Φ s := by
    intro s hsball
    have hr : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
      exact lt_of_le_of_lt
        (by simpa using Complex.abs_re_le_norm (s - (5 / 2 : ℂ)))
        (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hsball)
    have hs : 1 / 2 < s.re := by
      have := (abs_lt.mp hr).1
      linarith
    have hs0 : 0 < s.re := by linarith
    have hs1 : 1 / 6 < s.re := by linarith
    have hfixs : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (sec s).f (sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G (sec s).f (sec s).fC h := hfix s
    have hsum : (∑' δ : Fˣ ⧸ G.Δ,
        (a s δ + scalarM P G μ (sec s) (P.tc.rat (diagGL (Quotient.out δ)) * g))) =
        ∑ δ ∈ T, (a s δ + scalarM P G μ (sec s)
          (P.tc.rat (diagGL (Quotient.out δ)) * g)) := by
      apply tsum_eq_sum
      intro δ hδ
      have hz := hzero s hs0 δ hδ
      simp only [hscalar, a, b, hz.1, hz.2, mul_zero, add_zero]
    have hseries : R.E s = eisenstein P G (sec s) := funext (R.E_series s hsball)
    rw [hseries]
    rw [eisenstein_constantTerm P G μ hs (sec s) g 𝔞 h𝔞 hfixs Q hQ]
    change (s - 1 / 6) * (∑' δ : Fˣ ⧸ G.Δ,
      (a s δ + scalarM P G μ (sec s) (P.tc.rat (diagGL (Quotient.out δ)) * g))) = Φ s
    rw [hsum]
    simp_rw [hscalar]
    dsimp only [Φ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hBeq s hs1]
    ring
  obtain ⟨Ψ, hΨ, hΨ0, hΨeq⟩ := R.laurent_torus g Q hbQ hmQ 0
  have hLaurent : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = torusCoeff P R.theta g Q 0 ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Q 0 := by
    refine ⟨Ψ, hΨ.mono (Metric.ball_subset_ball hηε), hΨ0, ?_⟩
    intro s hs hns
    exact hΨeq s (Metric.ball_subset_ball hηε hs) hns
  have hres := regularized_residue_eval η hη hηle
    (fun s => torusCoeff P (R.E s) g Q 0) Φ (torusCoeff P R.theta g Q 0)
    htorus hΦ hLaurent heq
  have hcoeff : torusCoeff P R.theta g Pd 0 = torusCoeff P R.theta g Q 0 := by
    unfold torusCoeff
    rw [measure_congr hQeq, setIntegral_congr_set hQeq]
  rw [hcoeff, hres]
  have hsum0 : (∑' δ : Fˣ ⧸ G.Δ, b (1 / 6) δ) = ∑ δ ∈ T, b (1 / 6) δ := by
    apply tsum_eq_sum
    intro δ hδ
    exact (hzero (1 / 6) (by norm_num) δ hδ).2
  change Φ (1 / 6) = (κF F)⁻¹ * _ * ∑' δ : Fˣ ⧸ G.Δ, b (1 / 6) δ
  rw [hsum0]
  simp only [Φ, sub_self, zero_mul, zero_add, hB0]

end ArtinPrimitiveRoots.A1.Theta
