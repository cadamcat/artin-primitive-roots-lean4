import Mathlib.LinearAlgebra.Basis.Basic
import ArtinPrimitiveRoots.Theta.Res

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1 Module
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The finite-place multilinear normalization at exterior identity components.
Uses exists_globalDatum,
LocHaar.nonempty, exists_theta_ne_zero, thetaWhit_ne_zero, thetaWhit_multilinear. -/
structure ThetaNormalizationInput (P : CoverPackage D S H A) where
  G : GlobalDatum P
  μ : ∀ v : FinPlace F, LocHaar v
  Fam : AnalyticFamily P G μ
  C : ContinuedEis Fam
  level : Fam.T0 = S.Sf
  nonzero : ∃ g, C.theta g ≠ 0
  Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ
  x : ∀ v : S.Sf, (G.T v.1).V
  eval_ne_zero : Λ x ≠ 0
  coefficient : ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam') (r : P.RP),
    Fam'.T0 = S.Sf →
    (∀ s v, v ∉ S.Sf → (Fam'.sec s).f v = (Fam.sec s).f v) →
    (∀ v, v ∉ S.Sf → P.compF v r = 1) →
    thetaWhit C' (P.q r) =
      Λ (fun v => jacquet (P.loc v.1) A (μ v.1)
        (rtr (P.compF v.1 r) ((Fam'.sec (1 / 6)).f v.1))) *
      ∏ w, jacquetC (rtr (P.compC w r) (sphC (1 / 6)))

/-- A common product neighborhood and the actual analytic big-cell family it defines.
Uses exists_T5_section and
ThetaNormalizationInput; no Fourier or regularity fields are assumed. -/
structure ThetaCommonSections (P : CoverPackage D S H A)
    (N : ThetaNormalizationInput P) (𝓛 : Finset (SChar S)) where
  Uv : ∀ v : S.Sf, Set (v.1.adicCompletion F)
  open_Uv : ∀ v, IsOpen (Uv v)
  compact_Uv : ∀ v, IsCompact (Uv v)
  one_Uv : ∀ v, 1 ∈ Uv v
  unit_Uv : ∀ v y, y ∈ Uv v → Valued.v y = 1
  sixth_Uv : ∀ v y, y ∈ Uv v →
    ∃ c : (v.1.adicCompletion F)ˣ, y = ((c ^ 6 : (v.1.adicCompletion F)ˣ) : _)
  character_kernel : ∀ L ∈ 𝓛, ∀ y : S.FSˣ,
    (∀ v, (y : S.FS).1 v ∈ Uv v) → (∀ w, (y : S.FS).2 w = 1) → L.L y = 1
  φ : ∀ v : S.Sf, v.1.adicCompletion F → (N.G.T v.1).V
  locally_constant : ∀ v, IsLocallyConstant (φ v)
  compact_support : ∀ v, HasCompactSupport (φ v)
  Fam : AnalyticFamily P N.G N.μ
  C : ContinuedEis Fam
  level : Fam.T0 = S.Sf
  finite_section : ∀ s v, (Fam.sec s).f v.1 = bigCell (P.loc v.1) (N.G.T v.1) s (φ v)
  exterior_section : ∀ s v, v ∉ S.Sf → (Fam.sec s).f v = (N.Fam.sec s).f v
  jacquet_indicator : ∀ v (y : (v.1.adicCompletion F)ˣ),
    jacquet (P.loc v.1) A (N.μ v.1)
      (rtr ((P.loc v.1).a y) ((Fam.sec (1 / 6)).f v.1)) =
      (Uv v).indicator (fun _ => N.x v) (y : v.1.adicCompletion F)

/-- The common finite product neighborhood, including its empty-index case.
Uses ThetaCommonSections.Uv. -/
def thetaCommonU {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) :
    Set (∀ v : S.Sf, v.1.adicCompletion F) := {y | ∀ v, y v ∈ B.Uv v}

/-- The genuine iterated right-root derivative. Its expression is definitionally equal to
Assemble.Rderiv; keeping it here avoids a circular import of the consumer module.
Uses only nS and fderiv. -/
def thetaFamilyDeriv (P : CoverPackage D S H A) (m : InfinitePlace F → ℤ)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ :=
  (Finset.univ : Finset (InfinitePlace F)).toList.foldr (fun w acc g =>
    fderiv ℝ (fun z : ℂ => acc (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m w : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => acc (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I) Ψ

/-- The exact scalar removed from the product of complex derivative coefficients.
Uses the chosen nonzero multilinear evaluation. -/
def thetaNormalizationScalar {P : CoverPackage D S H A} (N : ThetaNormalizationInput P) : ℂ :=
  N.Λ N.x * ∏ _w : InfinitePlace F, (-(4 * Real.pi * Complex.I) * besselConst)

/-- The undifferentiated constant term, with the paper's residue and covolume normalization.
Uses theta_constantTerm's actual formula. -/
def thetaFamilyBaseN {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (g : P.tc.G) : ℂ :=
  (κF F)⁻¹ * resCprod B.Fam.T0 *
    ∑' δ : Fˣ ⧸ N.G.Δ, scalarOf P N.G (famM B.Fam)
      (fun _ => intertwineC (sphC (1 / 6))) (P.tc.rat (diagGL (Quotient.out δ)) * g)

/-- The normalized theta function for an admissible angular type.
Uses the actual common-family residue. -/
def thetaFamilyTheta {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (L : SChar S) (g : P.tc.G) : ℂ :=
  (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m B.C.theta g

/-- The normalized derivative of the residue's constant term.
Uses thetaFamilyBaseN. -/
def thetaFamilyThetaN {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (L : SChar S) (g : P.tc.G) : ℂ :=
  (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g

/-- W and WS use the same normalized differentiated Whittaker coefficient.
Uses thetaWhit of the actual common family. -/
def thetaFamilyW {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (L : SChar S) (g : P.tc.G) : ℂ :=
  (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaWhit B.C) g

/-- The actual normalized exterior spherical coordinate, definitionally equal to WvAll.
Uses the tame Weyl basis and jacquet. -/
def thetaExteriorWv (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (g : P.tc.G) : ℂ :=
  if hv : v ∉ S.Sf then
    if hh : ∃ k, P.emb v k = g then
      (Basis.mk (G.B v hv).weyl.linIndep (G.B v hv).weyl.spans.ge).coord 0
        (jacquet (P.loc v) A (μ v) (rtr hh.choose (sphWeyl P G v hv (1 / 6))))
    else 0
  else 0

/-- The exact undifferentiated factorization supplied by frozen thetaWhit_factor.
Uses no new family field. -/
def ThetaBaseFactorization {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) : Prop :=
  ∀ (ν : Fˣ) (ε : Bool) (gS : P.tc.G), gS ∈ P.tc.GS →
    ∀ (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) → ∀ (g : FinPlace F → P.tc.G),
      (∀ v ∈ T, g v ∈ P.tc.Gloc v) →
    thetaWhit B.C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaWhit B.C (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν))

/-- The three residue action laws supplied by frozen Rderiv_spec at the common level.
Uses the actual derivative expression. -/
def ThetaDerivativeAction {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) : Prop :=
  ∀ m : InfinitePlace F → ℤ,
    (∀ γ g, thetaFamilyDeriv P m B.C.theta (P.tc.rat γ * g) = thetaFamilyDeriv P m B.C.theta g) ∧
    (∀ ζ g, thetaFamilyDeriv P m B.C.theta (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyDeriv P m B.C.theta g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, thetaFamilyDeriv P m B.C.theta (g * k) = thetaFamilyDeriv P m B.C.theta g)

/-- The exact full-lattice Fourier theorem supplied by frozen torus_fourier_expansion.
The general C-infinity theorem,
not a pointwise-convergence assumption for the normalized theta family. -/
def ThetaTorusFourierInput (P : CoverPackage D S H A) : Prop :=
  ∀ (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), 𝔞 ≠ 0 →
    (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x, Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g)) →
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => Ψ (nInf P x * g)) →
    ∀ (Pd : Set (InfinitePlace F → ℂ)),
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume →
      Bornology.IsBounded Pd →
      HasSum (fun ν : {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1} =>
        torusCoeff P Ψ g Pd ν) (Ψ g)

/-- The universal frozen factorization input needed to move a nonzero Whittaker value
back to the S-part before choosing the normalization vectors.
Supplied by thetaWhit_factor. -/
def ThetaFactorizationInput (P : CoverPackage D S H A) : Prop :=
  ∀ (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    (Fam : AnalyticFamily P G μ), Fam.T0 = S.Sf → ∀ C : ContinuedEis Fam,
    ∀ (ν : Fˣ) (ε : Bool) (gS : P.tc.G), gS ∈ P.tc.GS →
    ∀ (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) → ∀ (g : FinPlace F → P.tc.G),
      (∀ v ∈ T, g v ∈ P.tc.Gloc v) →
    thetaWhit C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaWhit C (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, thetaExteriorWv P G μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), thetaExteriorWv P G μ v (P.tc.a v (toLoc v ν))

/-- The exterior laws supplied verbatim by frozen WvAll_spec.
Uses thetaExteriorWv. -/
def ThetaExteriorSpec (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) : Prop :=
  (∀ v, v ∉ S.Sf → ∀ ζ g, thetaExteriorWv P G μ v (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaExteriorWv P G μ v g) ∧
  (∀ v, v ∉ S.Sf → ∀ x g, thetaExteriorWv P G μ v (P.tc.n v (Multiplicative.ofAdd x) * g) =
    A.ψ v x * thetaExteriorWv P G μ v g) ∧
  (∀ v, v ∉ S.Sf → ∀ g, ∀ k ∈ P.tc.Kext, k ∈ P.tc.Gloc v → thetaExteriorWv P G μ v (g * k) = thetaExteriorWv P G μ v g) ∧
  (∀ v, v ∉ S.Sf → ∀ (e : ℤ) (u : (v.adicCompletion F)ˣ),
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    thetaExteriorWv P G μ v (P.tc.a v ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) =
      sphericalTable D A v e u)

/-- Only already-frozen upstream laws, assembled by the consumer module. These are
explicit inputs to avoid importing Assemble back into its own helper files.
Uses Rderiv_spec, thetaWhit_factor,
thetaWhit_nFin, WvAll_spec and torus_fourier_expansion; assumes no ThetaFamily field. -/
structure ThetaFamilyUpstream {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) : Prop where
  action : ThetaDerivativeAction B
  commutation : ∀ m g Pd ν, Bornology.IsBounded Pd → MeasurableSet Pd →
    torusCoeff P (thetaFamilyDeriv P m B.C.theta) g Pd ν =
      thetaFamilyDeriv P m (fun h => torusCoeff P B.C.theta h Pd ν) g
  factor : ThetaBaseFactorization B
  finite_unipotent : ∀ η h,
    thetaWhit B.C (nFin P η * h) = psiInf 1 (infEmbA (-η)) * thetaWhit B.C h
  exterior : ThetaExteriorSpec P N.G N.μ
  torus_fourier : ThetaTorusFourierInput P
end ArtinPrimitiveRoots.A1.Theta
