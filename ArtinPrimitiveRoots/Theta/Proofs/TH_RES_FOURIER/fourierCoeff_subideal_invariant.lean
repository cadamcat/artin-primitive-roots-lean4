import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.torusCoeff_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.analytic_residue_unique
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

/-- Normalized nonzero-frequency residue coefficients agree on an adapted ideal and any
nonzero subideal, including different bounded null-measurable domain choices.
Guide: sol-thin-thglobal/PROOFS.md:855–861. Uses torusCoeff_analytic,
analytic_residue_unique, and eisenstein_whittaker. Feeds the choice independence in thetaWhit. -/
theorem fourierCoeff_subideal_invariant {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hsub : 𝔟 ≤ 𝔞)
    (Pd Qd : Set (InfinitePlace F → ℂ)) (ν : Fˣ)
    (hPd : FourierAdaptedDomain sec g 𝔞 Pd (ν : F))
    (hQd : FourierAdaptedDomain sec g 𝔟 Qd (ν : F)) :
    torusCoeff P R.theta g Pd (ν : F) = torusCoeff P R.theta g Qd (ν : F) := by
  classical
  rcases hPd with ⟨h𝔞, hfix, hPfund, hPb, hPfreq⟩
  rcases hQd with ⟨h𝔟, hfix', hQfund, hQb, hQfreq⟩
  obtain ⟨Pd', hPdm, hPdb, hPfund', hPae⟩ :=
    adapted_domain_measurable_representative 𝔞 Pd hPfund hPb
  obtain ⟨Qd', hQdm, hQdb, hQfund', hQae⟩ :=
    adapted_domain_measurable_representative 𝔟 Qd hQfund hQb
  have hPdRep : torusCoeff P R.theta g Pd' (ν : F) =
      torusCoeff P R.theta g Pd (ν : F) := by
    unfold torusCoeff
    rw [measure_congr hPae, setIntegral_congr_set hPae]
  have hQdRep : torusCoeff P R.theta g Qd' (ν : F) =
      torusCoeff P R.theta g Qd (ν : F) := by
    unfold torusCoeff
    rw [measure_congr hQae, setIntegral_congr_set hQae]
  obtain ⟨η₁, hη₁, hη₁R, hη₁six, hf⟩ :=
    torusCoeff_analytic hFam R g 𝔞 h𝔞 hfix Pd' hPfund' hPdb hPdm (ν : F)
  obtain ⟨η₂, hη₂, hη₂R, hη₂six, hf'⟩ :=
    torusCoeff_analytic hFam R g 𝔟 h𝔟 hfix' Qd' hQfund' hQdb hQdm (ν : F)
  let η := min η₁ η₂
  have hη : 0 < η := lt_min hη₁ hη₂
  have hηR : η ≤ R.ε := (min_le_left _ _).trans hη₁R
  have hdom_mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₁ ⊆
        ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₂ := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr ⟨Metric.ball_subset_ball hε hs.1, hs.2⟩
  have hfη : AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g Pd' (ν : F))
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
    hf.mono (hdom_mono (min_le_left _ _))
  have hf'η : AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g Qd' (ν : F))
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
    hf'.mono (hdom_mono (min_le_right _ _))
  have hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      torusCoeff P (R.E s) g Pd' (ν : F) =
        (1 : ℂ) * torusCoeff P (R.E s) g Qd' (ν : F) := by
    intro s hs
    have hdist := Metric.mem_ball.mp hs
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [dist_eq_norm] using hdist
    have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
      have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
      simpa [Complex.sub_re] using (lt_of_le_of_lt hle hnorm)
    have hsHalf : 1 / 2 < s.re := by
      have hlow := (abs_lt.mp hreal).1
      linarith
    have hE : R.E s = eisenstein P G (sec s) := by
      funext x
      exact R.E_series s hs x
    have hleft := eisenstein_whittaker P G μ hsHalf (sec s) g 𝔞 h𝔞 (hfix s)
      Pd' hPfund' ν hPfreq
    have hright := eisenstein_whittaker P G μ hsHalf (sec s) g 𝔟 h𝔟 (hfix' s)
      Qd' hQfund' ν hQfreq
    calc
      torusCoeff P (R.E s) g Pd' (ν : F) =
          torusCoeff P (eisenstein P G (sec s)) g Pd' (ν : F) := by rw [hE]
      _ = whittakerE P G μ (sec s) (P.tc.rat (diagGL ν) * g) := hleft
      _ = torusCoeff P (eisenstein P G (sec s)) g Qd' (ν : F) := hright.symm
      _ = (1 : ℂ) * torusCoeff P (R.E s) g Qd' (ν : F) := by
        rw [← hE]
        simp
  obtain ⟨Ψ, hΨ, hΨ₀, hΨeq⟩ :=
    R.laurent_torus g Pd' hPdb hPdm (ν : F)
  obtain ⟨Ψ', hΨ', hΨ'₀, hΨ'eq⟩ :=
    R.laurent_torus g Qd' hQdb hQdm (ν : F)
  have hr : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = torusCoeff P R.theta g Pd' (ν : F) ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Pd' (ν : F) := by
    refine ⟨Ψ, hΨ.mono (Metric.ball_subset_ball hηR), hΨ₀, ?_⟩
    intro s hs hne
    exact hΨeq s (Metric.ball_subset_ball hηR hs) hne
  have hr' : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = torusCoeff P R.theta g Qd' (ν : F) ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Qd' (ν : F) := by
    refine ⟨Ψ', hΨ'.mono (Metric.ball_subset_ball hηR), hΨ'₀, ?_⟩
    intro s hs hne
    exact hΨ'eq s (Metric.ball_subset_ball hηR hs) hne
  have hres := analytic_residue_unique η hη
    (fun s => torusCoeff P (R.E s) g Pd' (ν : F))
    (fun s => torusCoeff P (R.E s) g Qd' (ν : F))
    (torusCoeff P R.theta g Pd' (ν : F))
    (torusCoeff P R.theta g Qd' (ν : F)) (1 : ℂ)
    hfη hf'η hr hr' hseries
  calc
    torusCoeff P R.theta g Pd (ν : F) =
        torusCoeff P R.theta g Pd' (ν : F) := hPdRep.symm
    _ = (1 : ℂ) * torusCoeff P R.theta g Qd' (ν : F) := hres
    _ = torusCoeff P R.theta g Qd' (ν : F) := by simp
    _ = torusCoeff P R.theta g Qd (ν : F) := hQdRep

end ArtinPrimitiveRoots.A1.Theta
