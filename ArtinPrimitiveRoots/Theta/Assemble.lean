import Mathlib.LinearAlgebra.Basis.Basic
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.IdealLatticeChart
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.DualIdealEquiv
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.IdealCharacterChart
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.FourierCoordinateDerivative
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.PeriodicTorusLift
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.SmoothPeriodicCoordinate
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.TorusDerivativeLift
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.ProductFourierMultiplier
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.ProductFourierDecay
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.SummableQuadraticProduct
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.PeriodicFourierSummable
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.NormalizedBasisIntegral
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.LatticeCoefficientChart
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.IdealSmoothTorusChart
import ArtinPrimitiveRoots.Theta.Res
import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».ResidueActions
import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».RootActions
import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».BoundedIntegralDerivative
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_factor_iteration
import ArtinPrimitiveRoots.Theta.Proofs.TH_ASSEMBLE.theta_interface_of_steinberg

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
coefficients acts at each complex place by the derivative vector `f_{m_w}` of `sphC`.
Corrected per rev-theta to require archimedean smoothness of the residue; C11 of `sol-gate-theta`
requires the joint root smoothness field on `ContinuedEis`. The exterior level `Fam.T0 = S.Sf`
is required per `sol-thin-thglobal` for the stated full `Kext`-invariance. -/
theorem Rderiv_spec {P : CoverPackage D S H A} {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam) (m : InfinitePlace F → ℤ)
    (hT : Fam.T0 = S.Sf) :
    (∀ (g : P.tc.G) (w : InfinitePlace F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => C.theta (g * P.tc.nS
          (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))) →
    (∀ γ g, Rderiv P m C.theta (P.tc.rat γ * g) = Rderiv P m C.theta g) ∧
    (∀ ζ g, Rderiv P m C.theta (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * Rderiv P m C.theta g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, Rderiv P m C.theta (g * k) = Rderiv P m C.theta g) ∧
    (∀ g Pd ν, Bornology.IsBounded Pd → MeasurableSet Pd →
      torusCoeff P (Rderiv P m C.theta) g Pd ν = Rderiv P m (fun h => torusCoeff P C.theta h Pd ν) g) := by
  sorry

/-- **asm:fourier**: Fourier expansion along `N(F_∞)` of a smooth function, periodic for
`infEmb 𝔞`, over the dual lattice `{ν : ψ_∞(ν𝔞) = 1} ⊆ F`. C9 of `sol-gate-theta` uses C-infinity
regularity for the archimedean input. -/
theorem torus_fourier_expansion (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hper : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x, Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g))
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => Ψ (nInf P x * g))
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd) :
    HasSum (fun ν : {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1} =>
      torusCoeff P Ψ g Pd ν) (Ψ g) := by
  classical
  obtain ⟨n, b, e, F₀, hspan, hF₀, hSum, hChar⟩ :=
    ArtinPrimitiveRoots.Proofs.thsol_torusf.ideal_smooth_torus_chart
      P Ψ g (Units.mk0 𝔞 h𝔞) hper hsmooth
  have hPd' : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pd volume := by
    rw [hspan]
    exact hPd
  have hCoeff (ν : {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf ν (infEmbA ξ) = 1}) :
      torusCoeff P Ψ g Pd ν.1 = UnitAddTorus.mFourierCoeff F₀ (e ν) :=
    ArtinPrimitiveRoots.Proofs.thsol_torusf.torus_coeff_lattice_chart
      P Ψ g b F₀ hF₀ ν.1 (e ν) (hChar ν) Pd hPd' hb
  have hn0 : nInf P 0 = 1 := by
    change P.tc.nS 1 = 1
    exact map_one _
  have hEval : F₀ 0 = Ψ g := by
    have hq0 : (fun _ : Fin (n + 1) => ((0 : ℝ) : UnitAddCircle)) =
        (0 : UnitAddTorus (Fin (n + 1))) := by
      ext i
      simp
    have h := hF₀ 0
    simpa only [Pi.zero_apply, hq0, map_zero, hn0, one_mul] using h
  have hm0 (k : Fin (n + 1) → ℤ) : UnitAddTorus.mFourier k 0 = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
      fourier_eval_zero, Finset.prod_const_one]
  have hSum0 : HasSum (UnitAddTorus.mFourierCoeff F₀) (Ψ g) := by
    simpa only [hm0, smul_eq_mul, mul_one, hEval] using
      UnitAddTorus.hasSum_mFourier_series_apply_of_summable hSum 0
  have hTransport : HasSum
      (fun ν : {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
          psiInf ν (infEmbA ξ) = 1} => UnitAddTorus.mFourierCoeff F₀ (e ν)) (Ψ g) :=
    e.hasSum_iff.mpr hSum0
  exact hTransport.congr_fun hCoeff

/-- **asm:nfin**: `W_θ(nFin(η) h) = ψ_∞(-η) W_θ(h)`; with right invariance this kills `W_θ(a(ν)g)` for
`ν` outside the dual of an adapted lattice (T3 over all `ν ∈ F^×`). -/
theorem thetaWhit_nFin {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (η : F) (h : P.tc.G) :
    thetaWhit C (nFin P η * h) = psiInf 1 (infEmbA (-η)) * thetaWhit C h := by
  sorry

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
  exact WvAll_properties P G μ

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
  exact thetaWhit_factor_iteration Fam hT C ν ε gS hgS T hT' g hg

/-- **asm:main**: for every finite family of admissible S-characters there is a theta family on
the cover of `P`. Corrected per rev-theta through the regularity fields of `ThetaFamily`; C10/C11
of `sol-gate-theta` require the cover topology and joint root smoothness. The correction from
`sol-gate-theta2` also requires the producer's cover to carry the canonical restricted-product
topology. -/
theorem exists_thetaFamily (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v)
    (hRP : HasRestrictedProductTopology P) (𝓛 : Finset (SChar S)) :
    Nonempty (ThetaFamily P.tc 𝓛) := by
  have hFactor : ThetaFactorizationInput P := by
    intro G μ Fam hT C
    exact thetaWhit_factor Fam hT C
  obtain ⟨N⟩ := theta_normalization_input P hSt hFactor
  obtain ⟨B⟩ := theta_T5_common_sections P N 𝓛
  have Q : ThetaFamilyUpstream B := {
    action := fun m => by
      have hr := Rderiv_spec B.Fam B.C m B.level B.C.archSmooth
      exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
    commutation := fun m => (Rderiv_spec B.Fam B.C m B.level B.C.archSmooth).2.2.2
    factor := thetaWhit_factor B.Fam B.level B.C
    finite_unipotent := thetaWhit_nFin B.Fam B.C
    exterior := WvAll_spec P N.G N.μ
    torus_fourier := torus_fourier_expansion P }
  exact ⟨thetaFamily_from_normalized_sections hRP N 𝓛 B Q⟩

/-- **th:theta-interface** under the Steinberg relation (P-COVER gap G1). With G1 resolved by a
`HilbertData` field, this is the explicit-Steinberg form of the corrected `theta_interface`.
Corrected per rev-theta through the regularity fields of `ThetaFamily`; C10/C11 of `sol-gate-theta`
fix the topology and add joint root smoothness, while C2 returns the compatible `CoverPackage`.
The `sol-gate-theta2` correction also returns its canonical restricted-product topology witness. -/
theorem theta_interface_of_steinberg (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (A : AddCharData F) (hSt : ∀ v, SteinbergAt H v) :
    ∃ P : CoverPackage D S H A, HasRestrictedProductTopology P ∧
      ∀ 𝓛 : Finset (SChar S), Nonempty (ThetaFamily P.tc 𝓛) := by
  exact theta_interface_from_family_constructor D S H A hSt
    (fun P hRP 𝓛 => exists_thetaFamily P hSt hRP 𝓛)

private theorem unitPart_isLocUnit (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    IsLocUnit v (unitPart v x) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hxv : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
    rw [← WithZero.exp_log hx0]
    simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_exists_uniformizer F).choose_spec
  have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
    simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
    change Valued.v ((x : v.adicCompletion F) *
      (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
    rw [map_mul, map_zpow₀, hxv, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    congr 1
    simp
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hval' : Valued.v (((unitPart v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [hval]
    rw [hval']

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
