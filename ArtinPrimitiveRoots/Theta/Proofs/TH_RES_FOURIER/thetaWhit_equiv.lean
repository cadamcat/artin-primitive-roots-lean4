import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_fourierCoeff

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem fourierBall_re_gt_half (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
    1 / 2 < s.re := by
  have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := Metric.mem_ball.mp hs
  have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
    simpa [dist_eq_norm] using hdist
  have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
    have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    simpa [Complex.sub_re] using lt_of_le_of_lt hle hnorm
  have hlow := (abs_lt.mp hreal).1
  linarith

theorem fourierFirstCoeff_congr_of_whittakerE {P : CoverPackage D S H A}
    {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    {sec : ∀ s : ℂ, GlobalSection P G s} {T0 : Finset (FinPlace F)}
    (hFam : FourierFamilyHyp μ sec T0) (R : FourierResidueData sec)
    (g g' : P.tc.G) (q : ℂ)
    (hW : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      whittakerE P G μ (sec s) g' = q * whittakerE P G μ (sec s) g) :
    fourierFirstCoeff R g' = q * fourierFirstCoeff R g := by
  classical
  obtain ⟨𝔞, Pd, hPd, hPm, hfirst⟩ :=
    fourierFirstCoeff_measurable_domain hFam R g
  obtain ⟨𝔟, Qd, hQd, hQm, hfirst'⟩ :=
    fourierFirstCoeff_measurable_domain hFam R g'
  rcases hPd with ⟨h𝔞, hfix, hfund, hb, hν⟩
  rcases hQd with ⟨h𝔟, hfix', hQfund, hQb, hν'⟩
  have hPadapt : FourierAdaptedDomain sec g 𝔞 Pd 1 :=
    ⟨h𝔞, hfix, hfund, hb, hν⟩
  have hQadapt : FourierAdaptedDomain sec g' 𝔟 Qd 1 :=
    ⟨h𝔟, hfix', hQfund, hQb, hν'⟩
  have hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      torusCoeff P (R.E s) g' Qd 1 = q * torusCoeff P (R.E s) g Pd 1 := by
    intro s hs
    have hsHalf := fourierBall_re_gt_half s hs
    have hE : R.E s = eisenstein P G (sec s) :=
      funext (R.E_series s hs)
    have hfixS : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (sec s).f (sec s).fC
          (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G (sec s).f (sec s).fC h := by
      intro ξ hξ h
      exact hfix s ξ hξ h
    have hfix'S : ∀ ξ ∈ (𝔟 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (sec s).f (sec s).fC
          (h * (g'⁻¹ * nFin P ξ * g')) = scalarOf P G (sec s).f (sec s).fC h := by
      intro ξ hξ h
      exact hfix' s ξ hξ h
    have hleft := eisenstein_whittaker P G μ hsHalf (sec s) g 𝔞 h𝔞
      hfixS Pd hfund (1 : Fˣ) hν
    have hright := eisenstein_whittaker P G μ hsHalf (sec s) g' 𝔟 h𝔟
      hfix'S Qd hQfund (1 : Fˣ) hν'
    have hdiag : diagGL (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL]
    have hratdiag : P.tc.rat (diagGL (1 : Fˣ)) = 1 := by
      rw [hdiag, map_one]
    have hW' : whittakerE P G μ (sec s) (P.tc.rat (diagGL (1 : Fˣ)) * g') =
        whittakerE P G μ (sec s) g' := by
      rw [hratdiag, one_mul]
    have hWbase : whittakerE P G μ (sec s) (P.tc.rat (diagGL (1 : Fˣ)) * g) =
        whittakerE P G μ (sec s) g := by
      rw [hratdiag, one_mul]
    calc
      torusCoeff P (R.E s) g' Qd 1 =
          torusCoeff P (eisenstein P G (sec s)) g' Qd 1 := by rw [hE]
      _ = whittakerE P G μ (sec s) (P.tc.rat (diagGL (1 : Fˣ)) * g') := hright
      _ = whittakerE P G μ (sec s) g' := hW'
      _ = q * whittakerE P G μ (sec s) g := hW s hs
      _ = q * whittakerE P G μ (sec s) (P.tc.rat (diagGL (1 : Fˣ)) * g) := by
        rw [hWbase.symm]
      _ = q * torusCoeff P (eisenstein P G (sec s)) g Pd 1 := by
        simpa using congrArg (fun z : ℂ => q * z) hleft.symm
      _ = q * torusCoeff P (R.E s) g Pd 1 := by rw [← hE]
  have hres := torusCoeff_residue_congr_of_series hFam R g' g
    𝔟 𝔞 Qd Pd 1 1 q hQadapt hPadapt hQm hPm hseries
  calc
    fourierFirstCoeff R g' = torusCoeff P R.theta g' Qd 1 := hfirst'
    _ = q * torusCoeff P R.theta g Pd 1 := hres
    _ = q * fourierFirstCoeff R g := by rw [hfirst]

/-- Genuineness and the exact S and exterior unipotent character laws for the chosen
first residue coefficient.
Uses adapted-domain existence, analytic_residue_unique, torusCoeff_analytic, whittakerE_equiv.
Feeds the frozen thetaWhit_equiv; no rationality assumption is made on S-unipotents. -/
theorem thetaWhit_equiv_assembly {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) :
    (∀ ζ g, fourierFirstCoeff R (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * fourierFirstCoeff R g) ∧
    (∀ x g, fourierFirstCoeff R (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * fourierFirstCoeff R g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, fourierFirstCoeff R (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * fourierFirstCoeff R g) := by
  constructor
  · intro ζ g
    apply fourierFirstCoeff_congr_of_whittakerE hFam R g
      (P.tc.z ζ * g) ((ζ : ℂˣ) : ℂ)
    intro s hs
    exact (whittakerE_equiv P G μ (fourierBall_re_gt_half s hs) (sec s)).1 ζ g
  constructor
  · intro x g
    apply fourierFirstCoeff_congr_of_whittakerE hFam R g
      (P.tc.nS (Multiplicative.ofAdd x) * g) (S.e A x)
    intro s hs
    exact (whittakerE_equiv P G μ (fourierBall_re_gt_half s hs) (sec s)).2.1 x g
  · intro v hv x g
    apply fourierFirstCoeff_congr_of_whittakerE hFam R g
      (P.tc.n v (Multiplicative.ofAdd x) * g) (A.ψ v x)
    intro s hs
    exact (whittakerE_equiv P G μ (fourierBall_re_gt_half s hs) (sec s)).2.2.1 v hv x g

end ArtinPrimitiveRoots.A1.Theta
