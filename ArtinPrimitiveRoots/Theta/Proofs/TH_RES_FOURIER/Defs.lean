import ArtinPrimitiveRoots.Theta.Reduction

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The existing family hypotheses used by residue Fourier arguments, bundled without
introducing new section data. Guide: sol-thin-thglobal/PROOFS.md:835–882.
Uses GlobalSection, and is supplied by the fields of the frozen AnalyticFamily. -/
structure FourierFamilyHyp {P : CoverPackage D S H A} {G : GlobalDatum P}
    (μ : ∀ v : FinPlace F, LocHaar v) (sec : ∀ s : ℂ, GlobalSection P G s)
    (T0 : Finset (FinPlace F)) : Prop where
  T0_eq : ∀ s, (sec s).T0 = T0
  fC_sph : ∀ s w, (sec s).fC w = sphC s
  f_analytic : ∀ v (g : (P.loc v).L),
    AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re}
  M_analytic : ∀ v ∈ T0, ∀ g : (P.loc v).L,
    AnalyticOnNhd ℂ (fun s => intertwine (P.loc v) (μ v) ((sec s).f v) g) {s | 0 < s.re}
  J_analytic : ∀ v ∈ T0, ∀ g : (P.loc v).L,
    AnalyticOnNhd ℂ (fun s => jacquet (P.loc v) A (μ v) (rtr g ((sec s).f v))) {s | 0 < s.re}
  level : ∀ v ∈ T0, ∃ m, (P.loc v).m0 ≤ m ∧
    ∀ s g, ∀ k ∈ (P.loc v).Kc m, (sec s).f v (g * k) = (sec s).f v g

/-- The continuation fields needed here, extracted from the frozen ContinuedEis.
Guide: sol-thin-thglobal/PROOFS.md:835–882. Uses no package theorem. -/
structure FourierResidueData {P : CoverPackage D S H A} {G : GlobalDatum P}
    (sec : ∀ s : ℂ, GlobalSection P G s) where
  ε : ℝ
  ε_pos : 0 < ε
  E : ℂ → P.tc.G → ℂ
  E_series : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
    E s g = eisenstein P G (sec s) g
  E_analytic : ∀ g, AnalyticOnNhd ℂ (fun s => E s g)
    (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε)
  theta : P.tc.G → ℂ
  laurent : ∀ g, ∃ Ψ : ℂ → ℂ,
    AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧ Ψ (1 / 6) = theta g ∧
    ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E s g
  laurent_torus : ∀ (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)),
    Bornology.IsBounded Pd → MeasurableSet Pd → ∀ ν : F, ∃ Ψ : ℂ → ℂ,
    AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧
    Ψ (1 / 6) = torusCoeff P theta g Pd ν ∧
    ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, s ≠ 1 / 6 →
      Ψ s = (s - 1 / 6) * torusCoeff P (E s) g Pd ν

/-- Uniform fixation by the finite translations of an ideal at g.
Guide: sol-thin-thglobal/PROOFS.md:851–855. Uses scalarOf and nFin. -/
def FourierIdealFix {P : CoverPackage D S H A} {G : GlobalDatum P}
    (sec : ∀ s : ℂ, GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Prop :=
  ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
    scalarOf P G (sec s).f (sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
      scalarOf P G (sec s).f (sec s).fC h

/-- The exact adapted-domain predicate in the frozen thetaWhit definition.
Guide: sol-thin-thglobal/PROOFS.md:851–861. Uses FourierIdealFix. -/
def FourierAdaptedDomain {P : CoverPackage D S H A} {G : GlobalDatum P}
    (sec : ∀ s : ℂ, GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : F) : Prop :=
  𝔞 ≠ 0 ∧ FourierIdealFix sec g 𝔞 ∧
    IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume ∧ Bornology.IsBounded Pd ∧
    ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1

/-- Choice of the first residue coefficient, with exactly thetaWhit's choice predicate.
Guide: sol-thin-thglobal/PROOFS.md:851–861. Uses FourierAdaptedDomain. -/
def fourierFirstCoeff {P : CoverPackage D S H A} {G : GlobalDatum P}
    {sec : ∀ s : ℂ, GlobalSection P G s} (R : FourierResidueData sec) (g : P.tc.G) : ℂ :=
  if h : ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)), FourierAdaptedDomain sec g 𝔞 Pd 1
  then torusCoeff P R.theta g h.choose_spec.choose 1 else 0

/-- The intertwined scalar with the cprod and kappa factors removed.
Guide: sol-thin-thglobal/PROOFS.md:835–845. Uses the same local vectors as scalarM. -/
def fourierRawM {P : CoverPackage D S H A} {G : GlobalDatum P}
    (μ : ∀ v : FinPlace F, LocHaar v) (sec : ∀ s : ℂ, GlobalSection P G s)
    (s : ℂ) (g : P.tc.G) : ℂ :=
  scalarOf P G (fun v => if hv : v ∈ (sec s).T0 then
      intertwine (P.loc v) (μ v) ((sec s).f v)
    else sphWeyl P G v (fun h => hv ((sec s).sub h)) s)
    (fun w => intertwineC ((sec s).fC w)) g

/-- Entire numerator and nonvanishing denominator underlying the Euler-product ratio.
Guide: sol-thin-thglobal/PROOFS.md:843–845. Supplied in Res from the existing Hecke/zeta helpers. -/
def FourierEulerHyp (T0 : Finset (FinPlace F)) : Prop :=
  ∃ L N : ℂ → ℂ,
    AnalyticOnNhd ℂ L {s | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → L s ≠ 0) ∧
    Differentiable ℂ N ∧
    (∀ s : ℂ, 1 < s.re → N s = (s - 1) * L s) ∧
    ∀ s : ℂ, 1 / 6 < s.re → cprod T0 s = L (6 * s) / L (6 * s + 1)

end ArtinPrimitiveRoots.A1.Theta
