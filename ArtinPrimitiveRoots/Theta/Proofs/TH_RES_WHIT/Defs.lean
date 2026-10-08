import ArtinPrimitiveRoots.Theta.Reduction

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1 MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- **def:analytic-family**: a family of global sections, holomorphic on `Re s > 0`, with spherical
complex components (P-SPEC narrowing), a common `T0` and a uniform level. -/
structure AnalyticFamily (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) where
  sec : ∀ s : ℂ, GlobalSection P G s
  T0 : Finset (FinPlace F)
  T0_eq : ∀ s, (sec s).T0 = T0
  fC_sph : ∀ s w, (sec s).fC w = sphC s
  f_analytic : ∀ v (g : (P.loc v).L), AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re}
  M_analytic : ∀ v ∈ T0, ∀ g : (P.loc v).L,
    AnalyticOnNhd ℂ (fun s => intertwine (P.loc v) (μ v) ((sec s).f v) g) {s | 0 < s.re}
  J_analytic : ∀ v ∈ T0, ∀ g : (P.loc v).L,
    AnalyticOnNhd ℂ (fun s => jacquet (P.loc v) A (μ v) (rtr g ((sec s).f v))) {s | 0 < s.re}
  level : ∀ v ∈ T0, ∃ m, (P.loc v).m0 ≤ m ∧
    ∀ s g, ∀ k ∈ (P.loc v).Kc m, (sec s).f v (g * k) = (sec s).f v g

/-- **res:continuation** (consumer object): the continuation of `E(·, Φ_s)` to P-SPEC's domain,
its residue `θ` at `1/6`, and the commutation of the residue with torus integrals.
Corrected per rev-theta to include archimedean smoothness of the residue; C11 of `sol-gate-theta`
adds joint root-orbit smoothness. -/
structure ContinuedEis {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) where
  ε : ℝ
  ε_pos : 0 < ε
  E : ℂ → P.tc.G → ℂ
  E_series : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g, E s g = eisenstein P G (Fam.sec s) g
  E_analytic : ∀ g, AnalyticOnNhd ℂ (fun s => E s g) (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε)
  theta : P.tc.G → ℂ
  laurent : ∀ g, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧ Ψ (1 / 6) = theta g ∧
    ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E s g
  laurent_torus : ∀ (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)), Bornology.IsBounded Pd →
    MeasurableSet Pd → ∀ ν : F, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧
      Ψ (1 / 6) = torusCoeff P theta g Pd ν ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * torusCoeff P (E s) g Pd ν
  theta_cont : ∀ g h, Continuous fun y : S.FSˣ => theta (g * P.tc.aS y * h)
  archSmooth : ∀ (g : P.tc.G) (w : InfinitePlace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => theta (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))
  jointRoots : JointRootSmooth P theta

/-- The Whittaker function of `θ`: its first torus coefficient over an adapted lattice (well
defined by `theta_fourierCoeff`). -/
def thetaWhit {P : CoverPackage D S H A} {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    {Fam : AnalyticFamily P G μ} (C : ContinuedEis Fam) (g : P.tc.G) : ℂ :=
  if h : ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧ (∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd volume ∧ Bornology.IsBounded Pd ∧
      ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1
  then torusCoeff P C.theta g h.choose_spec.choose 1 else 0

/-- Families varying only at `v0`, with that place inserted into the fixed support. -/
def ExteriorFamily {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (v0 : FinPlace F) (Fam' : AnalyticFamily P G μ) : Prop :=
  Fam'.T0 = insert v0 Fam.T0 ∧
    ∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v

/-- Right translation as a map on the space of local sections. -/
def sectionRtr {v : FinPlace F} (L : FinLocalCover D H v) (T : TorusRep D H v)
    (s : ℂ) (h : L.L) (f : sectionSpace L T s) : sectionSpace L T s :=
  ⟨rtr h f, IsSection.rtr f.property h⟩

/-- The local section coordinates of a family after translating a lift at `s0`. -/
def familySectionCoords {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (x : P.RP)
    (v : S.Sf) : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6) :=
  ⟨rtr (P.compF v.1 x) ((Fam.sec (1 / 6)).f v.1),
    IsSection.rtr ((Fam.sec (1 / 6)).f_sec v.1) (P.compF v.1 x)⟩

/-- Frozen residue interfaces, supplied by Res to the independent proof modules.
All field types are the existing theorem interfaces; this introduces no additional assumption
when constructed from those theorems. -/
structure ThetaResidueLaws (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) : Prop where
  continuation : ∀ (Fam : AnalyticFamily P G μ), Nonempty (ContinuedEis Fam)
  fourierCoeff : ∀ (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
      (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
      (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
      (Pd : Set (InfinitePlace F → ℂ))
      (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd volume) (hb : Bornology.IsBounded Pd)
      (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1),
      torusCoeff P C.theta g Pd (ν : F) = thetaWhit C (P.tc.rat (diagGL ν) * g)
  equiv : ∀ (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam),
      (∀ ζ g, thetaWhit C (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaWhit C g) ∧
      (∀ x g, thetaWhit C (P.tc.nS (Multiplicative.ofAdd x) * g) = S.e A x * thetaWhit C g) ∧
      (∀ v, v ∉ S.Sf → ∀ x g, thetaWhit C (P.tc.n v (Multiplicative.ofAdd x) * g) =
        A.ψ v x * thetaWhit C g)
  dependsOnM : ∀ (Fam Fam' : AnalyticFamily P G μ) (C : ContinuedEis Fam)
      (C' : ContinuedEis Fam') (hT : Fam.T0 = Fam'.T0)
      (hM : ∀ v ∈ Fam.T0, intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) =
        intertwine (P.loc v) (μ v) ((Fam'.sec (1 / 6)).f v)),
      C.theta = C'.theta
  linearTranslate : ∀ (v0 : FinPlace F) (Fam Fam' Fam'' : AnalyticFamily P G μ)
      (C : ContinuedEis Fam) (C' : ContinuedEis Fam') (C'' : ContinuedEis Fam''),
      ((∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v ∧ (Fam''.sec s).f v = (Fam.sec s).f v) →
        ∀ c : ℂ, (∀ s, (Fam''.sec s).f v0 = (Fam.sec s).f v0 + c • (Fam'.sec s).f v0) →
          C''.theta = C.theta + c • C'.theta) ∧
      (∀ h : (P.loc v0).L, (∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
        (∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0)) →
          ∀ g, C'.theta g = C.theta (g * P.emb v0 h))

end ArtinPrimitiveRoots.A1.Theta
