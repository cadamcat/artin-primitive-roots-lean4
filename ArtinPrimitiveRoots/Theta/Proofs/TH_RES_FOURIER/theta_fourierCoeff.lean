import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.fourierCoeff_subideal_invariant

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem torusCoeff_congr_ae {P : CoverPackage D S H A} (Ψ : P.tc.G → ℂ)
    (g : P.tc.G) (Q Pd : Set (InfinitePlace F → ℂ)) (ν : F)
    (hQPd : Q =ᵐ[volume] Pd) :
    torusCoeff P Ψ g Q ν = torusCoeff P Ψ g Pd ν := by
  unfold torusCoeff
  rw [measure_congr hQPd, setIntegral_congr_set hQPd]

theorem fourierFirstCoeff_measurable_domain {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)),
      FourierAdaptedDomain sec g 𝔞 Pd 1 ∧ MeasurableSet Pd ∧
        fourierFirstCoeff R g = torusCoeff P R.theta g Pd 1 := by
  classical
  obtain ⟨𝔞₀, Pd₀, hPd₀, _⟩ := theta_adapted_domain_exists hFam g
  have hex : ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)), FourierAdaptedDomain sec g 𝔞 Pd 1 :=
    ⟨𝔞₀, Pd₀, hPd₀⟩
  let 𝔞 := Classical.choose hex
  let Pd := Classical.choose (Classical.choose_spec hex)
  have hPd : FourierAdaptedDomain sec g 𝔞 Pd 1 := Classical.choose_spec
    (Classical.choose_spec hex)
  rcases hPd with ⟨h𝔞, hfix, hfund, hb, hfreq⟩
  obtain ⟨Q, hQm, hQb, hQfund, hQeq⟩ :=
    adapted_domain_measurable_representative 𝔞 Pd hfund hb
  have hQadapt : FourierAdaptedDomain sec g 𝔞 Q 1 :=
    ⟨h𝔞, hfix, hQfund, hQb, hfreq⟩
  have hcoeff : fourierFirstCoeff R g = torusCoeff P R.theta g Pd 1 := by
    unfold fourierFirstCoeff
    rw [dif_pos hex]
  have hrep : torusCoeff P R.theta g Q 1 = torusCoeff P R.theta g Pd 1 :=
    torusCoeff_congr_ae R.theta g Q Pd 1 hQeq
  exact ⟨𝔞, Q, hQadapt, hQm, hcoeff.trans hrep.symm⟩

theorem torusCoeff_residue_congr_of_series {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g g' : P.tc.G)
    (𝔞 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd Qd : Set (InfinitePlace F → ℂ)) (ν ν' : F) (q : ℂ)
    (hPd : FourierAdaptedDomain sec g 𝔞 Pd ν)
    (hQd : FourierAdaptedDomain sec g' 𝔟 Qd ν')
    (hPm : MeasurableSet Pd) (hQm : MeasurableSet Qd)
    (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      torusCoeff P (R.E s) g Pd ν = q * torusCoeff P (R.E s) g' Qd ν') :
    torusCoeff P R.theta g Pd ν = q * torusCoeff P R.theta g' Qd ν' := by
  rcases hPd with ⟨h𝔞, hfix, hfund, hb, hν⟩
  rcases hQd with ⟨h𝔟, hfix', hfund', hb', hν'⟩
  obtain ⟨η₁, hη₁, hη₁R, hη₁six, hf⟩ :=
    torusCoeff_analytic hFam R g 𝔞 h𝔞 hfix Pd hfund hb hPm ν
  obtain ⟨η₂, hη₂, hη₂R, hη₂six, hf'⟩ :=
    torusCoeff_analytic hFam R g' 𝔟 h𝔟 hfix' Qd hfund' hb' hQm ν'
  let η := min η₁ η₂
  have hη : 0 < η := lt_min hη₁ hη₂
  have hηR : η ≤ R.ε := (min_le_left _ _).trans hη₁R
  have hη₂R : η ≤ R.ε := (min_le_right _ _).trans hη₂R
  have hdom_mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₁ ⊆
        ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₂ := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr ⟨Metric.ball_subset_ball hε hs.1, hs.2⟩
  have hfη : AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g Pd ν)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
    hf.mono (hdom_mono (min_le_left _ _))
  have hf'η : AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g' Qd ν')
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
    hf'.mono (hdom_mono (min_le_right _ _))
  obtain ⟨Ψ, hΨ, hΨ₀, hΨeq⟩ := R.laurent_torus g Pd hb hPm ν
  obtain ⟨Ψ', hΨ', hΨ'₀, hΨ'eq⟩ := R.laurent_torus g' Qd hb' hQm ν'
  have hr : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = torusCoeff P R.theta g Pd ν ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Pd ν := by
    refine ⟨Ψ, hΨ.mono (Metric.ball_subset_ball hηR), hΨ₀, ?_⟩
    intro s hs hne
    exact hΨeq s (Metric.ball_subset_ball hηR hs) hne
  have hr' : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = torusCoeff P R.theta g' Qd ν' ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g' Qd ν' := by
    refine ⟨Ψ', hΨ'.mono (Metric.ball_subset_ball hη₂R), hΨ'₀, ?_⟩
    intro s hs hne
    exact hΨ'eq s (Metric.ball_subset_ball hη₂R hs) hne
  exact analytic_residue_unique η hη
    (fun s => torusCoeff P (R.E s) g Pd ν)
    (fun s => torusCoeff P (R.E s) g' Qd ν')
    (torusCoeff P R.theta g Pd ν) (torusCoeff P R.theta g' Qd ν') q
    hfη hf'η hr hr' hseries

/-- Transport a nonzero-frequency residue coefficient to the chosen first coefficient.
Guide: sol-thin-thglobal/PROOFS.md:862–869. Uses adapted-domain existence,
analytic_residue_unique, torusCoeff_analytic, and eisenstein_whittaker.
Feeds the frozen theta_fourierCoeff by definitional identification of the extracted data. -/
theorem theta_fourierCoeff_assembly {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : Fˣ)
    (hPd : FourierAdaptedDomain sec g 𝔞 Pd (ν : F)) :
    torusCoeff P R.theta g Pd (ν : F) =
      fourierFirstCoeff R (P.tc.rat (diagGL ν) * g) := by
  classical
  rcases hPd with ⟨h𝔞, hfix, hfund, hb, hν⟩
  obtain ⟨Q, hQm, hQb, hQfund, hQeq⟩ :=
    adapted_domain_measurable_representative 𝔞 Pd hfund hb
  have hQadapt : FourierAdaptedDomain sec g 𝔞 Q (ν : F) :=
    ⟨h𝔞, hfix, hQfund, hQb, hν⟩
  let gν := P.tc.rat (diagGL ν) * g
  obtain ⟨𝔟, Q', hQ'adapt, hQ'm, hfirst⟩ :=
    fourierFirstCoeff_measurable_domain hFam R gν
  rcases hQ'adapt with ⟨h𝔟, hfix', hQ'fund, hQ'b, hν'⟩
  have hQadapt' : FourierAdaptedDomain sec gν 𝔟 Q' 1 :=
    ⟨h𝔟, hfix', hQ'fund, hQ'b, hν'⟩
  have hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      torusCoeff P (R.E s) g Q (ν : F) =
        (1 : ℂ) * torusCoeff P (R.E s) gν Q' 1 := by
    intro s hs
    have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := Metric.mem_ball.mp hs
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [dist_eq_norm] using hdist
    have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
      have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
      simpa [Complex.sub_re] using lt_of_le_of_lt hle hnorm
    have hsHalf : 1 / 2 < s.re := by
      have hlow := (abs_lt.mp hreal).1
      linarith
    have hE : R.E s = eisenstein P G (sec s) :=
      funext (R.E_series s hs)
    have hfixS : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (sec s).f (sec s).fC
          (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G (sec s).f (sec s).fC h := by
      intro ξ hξ h
      exact hfix s ξ hξ h
    have hfix'S : ∀ ξ ∈ (𝔟 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (sec s).f (sec s).fC
          (h * (gν⁻¹ * nFin P ξ * gν)) = scalarOf P G (sec s).f (sec s).fC h := by
      intro ξ hξ h
      exact hfix' s ξ hξ h
    have hleft := eisenstein_whittaker P G μ hsHalf (sec s) g 𝔞 h𝔞
      hfixS Q hQfund ν hν
    have hright := eisenstein_whittaker P G μ hsHalf (sec s) gν 𝔟 h𝔟
      hfix'S Q' hQ'fund (1 : Fˣ) hν'
    have hdiag : diagGL (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL]
    have hratdiag : P.tc.rat (diagGL (1 : Fˣ)) = 1 := by
      rw [hdiag, map_one]
    simpa using (calc
      torusCoeff P (R.E s) g Q (ν : F) =
          torusCoeff P (eisenstein P G (sec s)) g Q (ν : F) := by rw [hE]
      _ = whittakerE P G μ (sec s) gν := hleft
      _ = whittakerE P G μ (sec s) (P.tc.rat (diagGL (1 : Fˣ)) * gν) := by
        rw [hratdiag, one_mul]
      _ = torusCoeff P (eisenstein P G (sec s)) gν Q' 1 := hright.symm
      _ = torusCoeff P (R.E s) gν Q' 1 := by rw [hE]
      )
  have hres := torusCoeff_residue_congr_of_series hFam R g gν
    𝔞 𝔟 Q Q' (ν : F) 1 1 hQadapt hQadapt' hQm hQ'm hseries
  calc
    torusCoeff P R.theta g Pd (ν : F) = torusCoeff P R.theta g Q (ν : F) :=
      (torusCoeff_congr_ae R.theta g Q Pd (ν : F) hQeq).symm
    _ = (1 : ℂ) * torusCoeff P R.theta gν Q' 1 := hres
    _ = fourierFirstCoeff R gν := by rw [one_mul, hfirst.symm]

end ArtinPrimitiveRoots.A1.Theta
