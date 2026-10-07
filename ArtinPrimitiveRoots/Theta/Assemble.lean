import Mathlib.LinearAlgebra.Basis.Basic
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Res

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1
open Module

variable {F : Type} [Field F] [NumberField F]

/-! ## P-ASSEMBLE -/

section Assemble

open MeasureTheory Filter Topology

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- `n(z)` at one complex place `w`. -/
def nAt (P : CoverPackage D S H A) (w : InfinitePlace F) (z : ℂ) : P.tc.G :=
  P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))

/-- The right Lie derivative `(∂₁ - m i ∂₂)|₀ Ψ(g · n_w(x₁ + i x₂))` at the complex place `w`. -/
def derivAt (P : CoverPackage D S H A) (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ)
    (g : P.tc.G) : ℂ :=
  fderiv ℝ (fun z : ℂ => Ψ (g * nAt P w z)) 0 1 -
    (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => Ψ (g * nAt P w z)) 0 Complex.I

/-- **def:R-deriv** (P-SPEC obligation (2)): `R(X_m) = Π_w (∂₁ - m_w i ∂₂)`, applied to the residue. -/
def Rderiv (P : CoverPackage D S H A) (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ :=
  (Finset.univ : Finset (InfinitePlace F)).toList.foldr (fun w acc => derivAt P w (m w) acc) Ψ

/-- **asm:R-deriv**: `R(X_m)` commutes with left translations, preserves genuineness, automorphy,
right `Kext`-invariance and smoothness of `θ`, commutes with torus coefficients, and on Whittaker
coefficients acts at each complex place by the derivative vector `f_{m_w}` of `sphC`. -/
theorem Rderiv_spec {P : CoverPackage D S H A} {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam) (m : InfinitePlace F → ℤ) :
    (∀ γ g, Rderiv P m C.theta (P.tc.rat γ * g) = Rderiv P m C.theta g) ∧
    (∀ ζ g, Rderiv P m C.theta (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * Rderiv P m C.theta g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, Rderiv P m C.theta (g * k) = Rderiv P m C.theta g) ∧
    (∀ g Pd ν, Bornology.IsBounded Pd → MeasurableSet Pd →
      torusCoeff P (Rderiv P m C.theta) g Pd ν = Rderiv P m (fun h => torusCoeff P C.theta h Pd ν) g) := by
  sorry

/-- **asm:fourier**: Fourier expansion along `N(F_∞)` of a smooth function, periodic for
`infEmb 𝔞`, over the dual lattice `{ν : ψ_∞(ν𝔞) = 1} ⊆ F`. -/
theorem torus_fourier_expansion (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hper : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x, Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g))
    (hsmooth : ContDiff ℝ ⊤ fun x => Ψ (nInf P x * g)) (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd) :
    HasSum (fun ν : {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1} =>
      torusCoeff P Ψ g Pd ν) (Ψ g) := by
  sorry

/-- **asm:nfin**: `W_θ(nFin(η) h) = ψ_∞(-η) W_θ(h)`; with right invariance this kills `W_θ(a(ν)g)` for
`ν` outside the dual of an adapted lattice (T3 over all `ν ∈ F^×`). -/
theorem thetaWhit_nFin {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (η : F) (h : P.tc.G) :
    thetaWhit C (nFin P η * h) = psiInf 1 (infEmbA (-η)) * thetaWhit C h := by
  sorry

/-- The coordinate along `e₀` of a tame basis. -/
def tameCoord0 {D : FieldData F} {H : HilbertData F} {v : FinPlace F} {T : TorusRep D H v}
    (B : TameTorusBasis T) : T.V →ₗ[ℂ] ℂ :=
  (Basis.mk B.linIndep B.spans.ge).coord 0

/-- **def:Wv**: the normalized exterior spherical Whittaker function on `G` (`0` off `Gloc v`):
`Wv(emb k) = c₀(𝒥(π(k) f°'))`, `c₀` the `e₀`-coordinate of the Weyl basis (`c₀(u) = 1`). -/
def WvAll (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    (v : FinPlace F) (h : P.tc.G) : ℂ :=
  if hv : v ∉ S.Sf then
    if hh : ∃ k, P.emb v k = h then
      tameCoord0 (G.B v hv).weyl
        (jacquet (P.loc v) A (μ v) (rtr hh.choose (sphWeyl P G v hv (1 / 6))))
    else 0
  else 0

/-- **asm:Wv**: the fields `Wv_genuine`, `Wv_equiv`, `Wv_right`, `Wv_table` for `WvAll`. -/
theorem WvAll_spec (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) :
    (∀ v, v ∉ S.Sf → ∀ ζ g, WvAll P G μ v (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, WvAll P G μ v (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ g, ∀ k ∈ P.tc.Kext, k ∈ P.tc.Gloc v → WvAll P G μ v (g * k) = WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ (e : ℤ) (u : (v.adicCompletion F)ˣ),
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      WvAll P G μ v (P.tc.a v ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) =
        sphericalTable D A v e u) := by
  sorry

/-- **asm:factor** (T4): the Whittaker function of `θ` factors as `W_S · Π_{v∈T} W_v · Π' W_v(a_v(ν))`
(here `W_S = W`), by induction on `T` with `theta_exterior_whittaker` and
`whittaker_theta_dim_le_one`. -/
theorem thetaWhit_factor {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (hT : Fam.T0 = S.Sf)
    (C : ContinuedEis Fam) (ν : Fˣ) (ε : Bool) (gS : P.tc.G) (hgS : gS ∈ P.tc.GS)
    (T : Finset (FinPlace F)) (hT' : ∀ v ∈ T, v ∉ S.Sf) (g : FinPlace F → P.tc.G)
    (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    thetaWhit C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaWhit C (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, WvAll P G μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
  sorry

/-- **asm:main**: for every finite family of admissible S-characters there is a theta family on
the cover of `P`. -/
theorem exists_thetaFamily (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v)
    (𝓛 : Finset (SChar S)) : Nonempty (ThetaFamily P.tc 𝓛) := by
  sorry

/-- **th:theta-interface** under the Steinberg relation (P-COVER gap G1). With G1 resolved by a
`HilbertData` field, this is the frozen `theta_interface`. -/
theorem theta_interface_of_steinberg (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (A : AddCharData F) (hSt : ∀ v, SteinbergAt H v) :
    ∃ C : ThetaCover D S H A, ∀ 𝓛 : Finset (SChar S), Nonempty (ThetaFamily C 𝓛) := by
  sorry

/-- **cor:theta-exterior-coefficient** (03:186–222; A2 request), table form. -/
theorem sphericalTable_product (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) (𝔄 : Ideal (𝓞 F)) (h𝔄 : S.IsExterior 𝔄) (a : Fˣ)
    (ha : S.IsGen (a : F) 𝔄 ∧ Bd.Allowed a) :
    (Function.mulSupport fun v : {v : FinPlace F // v ∉ S.Sf} =>
      sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a)) (unitPart v.1 (toLoc v.1 a))).Finite ∧
    (∀ (c n : Ideal (𝓞 F)) (cg : Fˣ), Squarefree c → 𝔄 = c * n ^ 3 →
      S.IsGen (cg : F) c ∧ Bd.Allowed cg →
      ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf},
          sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a)) (unitPart v.1 (toLoc v.1 a)) =
        gamma D S A 2 c (cg : F) * ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          (((Ideal.absNorm n : ℝ))⁻¹ : ℝ)) ∧
    ((∀ c n : Ideal (𝓞 F), Squarefree c → 𝔄 ≠ c * n ^ 3) →
      ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf},
          sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a)) (unitPart v.1 (toLoc v.1 a)) = 0) := by
  sorry

/-- **cor:theta-exterior-coefficient** (family form, eq:theta-exterior-coefficient): from `Wv_table`. -/
theorem theta_exterior_coefficient {C : ThetaCover D S H A} {𝓛 : Finset (SChar S)}
    (TF : ThetaFamily C 𝓛) (Bd : BData S H) (𝔄 : Ideal (𝓞 F)) (h𝔄 : S.IsExterior 𝔄) (a : Fˣ)
    (ha : S.IsGen (a : F) 𝔄 ∧ Bd.Allowed a) :
    (Function.mulSupport fun v : {v : FinPlace F // v ∉ S.Sf} => TF.Wv v.1 (C.a v.1 (toLoc v.1 a))).Finite ∧
    (∀ (c n : Ideal (𝓞 F)) (cg : Fˣ), Squarefree c → 𝔄 = c * n ^ 3 →
      S.IsGen (cg : F) c ∧ Bd.Allowed cg →
      ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, TF.Wv v.1 (C.a v.1 (toLoc v.1 a)) =
        gamma D S A 2 c (cg : F) * ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          (((Ideal.absNorm n : ℝ))⁻¹ : ℝ)) ∧
    ((∀ c n : Ideal (𝓞 F), Squarefree c → 𝔄 ≠ c * n ^ 3) →
      ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, TF.Wv v.1 (C.a v.1 (toLoc v.1 a)) = 0) := by
  sorry

end Assemble

end ArtinPrimitiveRoots.A1.Theta
