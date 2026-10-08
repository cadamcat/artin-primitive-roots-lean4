import Mathlib.LinearAlgebra.Basis.Basic
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».FINITE_CHAR
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Res
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

local instance thetaExterior_residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance thetaExterior_residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

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
  sorry

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

private lemma thetaExterior_count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma thetaExterior_count_spanSingleton_integral (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma thetaExterior_count_spanSingleton (v : FinPlace F) (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    thetaExterior_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    thetaExterior_count_spanSingleton_integral v n hn,
    thetaExterior_count_spanSingleton_integral v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn)
      (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma thetaExterior_count_principal_eq_ordv (v : FinPlace F) (a : Fˣ) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
      ordv v (toLoc v a) := by
  have hval : HeightOneSpectrum.valuation F v (a : F) =
      WithZero.exp (-ordv v (toLoc v a)) := by
    have hx0 : Valued.v (toLoc v a : v.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero (toLoc v a))
    have hxv : Valued.v (toLoc v a : v.adicCompletion F) =
        WithZero.exp (-ordv v (toLoc v a)) := by
      rw [← WithZero.exp_log hx0]
      simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
    have hcoe : (toLoc v a : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (a : F) := rfl
    rw [hcoe] at hxv
    have hxv' : Valued.v ((a : F) : v.adicCompletion F) =
        WithZero.exp (-ordv v (toLoc v a)) := by
      change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _
      exact hxv
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hxv'
    exact hxv'
  rw [thetaExterior_count_spanSingleton v (a : F) (Units.ne_zero a), hval]
  simp

private lemma thetaExterior_cubeFactorsExterior (𝔄 c n : Ideal (𝓞 F))
    (h𝔄 : S.IsExterior 𝔄) (hfactor : 𝔄 = c * n ^ 3) :
    S.IsExterior c ∧ S.IsExterior n := by
  have hc0 : c ≠ ⊥ := by
    intro hc
    apply h𝔄.1
    rw [hfactor, hc]
    simp
  have hn0 : n ≠ ⊥ := by
    intro hn
    apply h𝔄.1
    rw [hfactor, hn]
    simp
  have hnPow : n ^ 3 ≤ n := by
    rw [pow_succ]
    exact Ideal.mul_le_right (I := n ^ 2) (J := n)
  constructor
  · refine ⟨hc0, ?_⟩
    intro v hvS hcv
    apply h𝔄.2 v hvS
    rw [hfactor]
    exact le_trans (Ideal.mul_le_left (I := c) (J := n ^ 3)) hcv
  · refine ⟨hn0, ?_⟩
    intro v hvS hnv
    apply h𝔄.2 v hvS
    rw [hfactor]
    calc
      c * n ^ 3 ≤ n ^ 3 := Ideal.mul_le_right (I := c) (J := n ^ 3)
      _ ≤ n := hnPow
      _ ≤ v.asIdeal := hnv

private lemma thetaExterior_count_spanSingleton_mul (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x * y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) +
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)]

private lemma thetaExterior_gen_mul_cube
    (c n : Ideal (𝓞 F)) (cg ng : Fˣ)
    (hA : S.IsExterior (c * n ^ 3))
    (hcg : S.IsGen (cg : F) c) (hng : S.IsGen (ng : F) n) :
    S.IsGen ((cg * ng ^ 3 : Fˣ) : F) (c * n ^ 3) := by
  refine ⟨hA, Units.ne_zero _, ?_⟩
  intro v hv
  have hgenProd : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((cg * ng ^ 3 : Fˣ) : F)) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (cg : F)) +
          3 * FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (ng : F)) := by
      calc
        FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
              ((cg * ng ^ 3 : Fˣ) : F)) =
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (cg : F)) +
              FractionalIdeal.count F v
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((ng : F) ^ 3)) := by
          simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
            thetaExterior_count_spanSingleton_mul v (cg : F) ((ng : F) ^ 3)
              (Units.ne_zero cg) (pow_ne_zero 3 (Units.ne_zero ng))
        _ = FractionalIdeal.count F v
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (cg : F)) +
              3 * FractionalIdeal.count F v
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (ng : F)) := by
          rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
          ring
  have hidealProd : FractionalIdeal.count F v
        ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
          3 * FractionalIdeal.count F v (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.count_mul F v
          (FractionalIdeal.coeIdeal_ne_zero.mpr hcg.1.1)
          (pow_ne_zero 3 (FractionalIdeal.coeIdeal_ne_zero.mpr hng.1.1)),
        FractionalIdeal.count_pow]
      ring
  calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((cg * ng ^ 3 : Fˣ) : F)) =
        FractionalIdeal.count F v (c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
          3 * FractionalIdeal.count F v (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [hgenProd, hcg.2.2 v hv, hng.2.2 v hv]
    _ = FractionalIdeal.count F v
          ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hidealProd.symm

private lemma thetaExterior_allowed_mul_cube (Bd : BData S H) (cg ng : Fˣ)
    (hcg : Bd.Allowed cg) (hng : Bd.Allowed ng) : Bd.Allowed (cg * ng ^ 3) := by
  change (QuotientGroup.mk (S.diagU (cg * ng ^ 3)) : S.V) ∈ Bd.B
  rw [map_mul, map_pow]
  exact Bd.B.mul_mem hcg (Bd.B.pow_mem hng 3)

private lemma thetaExterior_residueRep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private lemma thetaExterior_residueIntegralCongr (v : FinPlace F) (a b : 𝓞 F)
    (hab : Valued.v (((a : F) : v.adicCompletion F) - ((b : F) : v.adicCompletion F)) < 1) :
    residue v (a : F) = residue v (b : F) := by
  have hab' : Valued.v (algebraMap F (v.adicCompletion F) ((a : F) - (b : F))) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_sub] using hab
  have hval : HeightOneSpectrum.valuation F v ((a : F) - (b : F)) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hab'
  have hmem : a - b ∈ v.asIdeal := (v.valuation_lt_one_iff_mem (K := F) _).1 hval
  have hresA : residue v (a : F) = Ideal.Quotient.mk v.asIdeal a := by
    simpa using thetaExterior_residueRep v _ a 1
      (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  have hresB : residue v (b : F) = Ideal.Quotient.mk v.asIdeal b := by
    simpa using thetaExterior_residueRep v _ b 1
      (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  rw [hresA, hresB]
  have hzero : Ideal.Quotient.mk v.asIdeal (a - b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 hmem
  have hsub : Ideal.Quotient.mk v.asIdeal a - Ideal.Quotient.mk v.asIdeal b = 0 := by
    simpa only [map_sub] using hzero
  exact (sub_eq_zero.mp hsub)

private lemma thetaExterior_residueCongr (v : FinPlace F) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1)
    (hxy : HeightOneSpectrum.valuation F v (x - y) < 1) : residue v x = residue v y := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hcd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbnot : b.val ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp b.property
  have hdnot : d.val ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp d.property
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 hbnot
  have hdval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F d.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := d.val)).2 hdnot
  have hcross : algebraMap (𝓞 F) F (a * d.val - c * b.val) =
      (x - y) * algebraMap (𝓞 F) F b.val * algebraMap (𝓞 F) F d.val := by
    simp only [map_sub, map_mul]
    rw [← hab, ← hcd]
    ring
  have hmem : a * d.val - c * b.val ∈ v.asIdeal := by
    apply (v.valuation_lt_one_iff_mem (K := F) _).1
    change HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F (a * d.val - c * b.val)) < 1
    rw [hcross, map_mul, map_mul, hbval, hdval, mul_one, mul_one]
    exact hxy
  have hqcross : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal d.val =
      Ideal.Quotient.mk v.asIdeal c * Ideal.Quotient.mk v.asIdeal b.val := by
    have hzero := (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    simpa only [map_sub, map_mul, sub_eq_zero] using hzero
  have hbq : Ideal.Quotient.mk v.asIdeal b.val ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hbnot
  have hdq : Ideal.Quotient.mk v.asIdeal d.val ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hdnot
  calc
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b.val :=
      thetaExterior_residueRep v x a b.val hbnot hab
    _ = Ideal.Quotient.mk v.asIdeal c / Ideal.Quotient.mk v.asIdeal d.val :=
      (div_eq_div_iff hbq hdq).2 hqcross
    _ = residue v y :=
      (thetaExterior_residueRep v y c d.val hdnot hcd).symm

private lemma thetaExterior_chiCongr (D : FieldData F) (v : FinPlace F) (x y : F)
    (hres : residue v x = residue v y) : chi D v x = chi D v y := by
  have hχ : chiAlg v x = chiAlg v y := by
    unfold chiAlg
    rw [hres]
  unfold chi
  rw [hres, hχ]

private lemma thetaExterior_localUnitApproximant (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 := by
  let O := v.adicCompletionIntegers F
  let uO : O := ⟨(u : v.adicCompletion F), hu.1⟩
  let uInvO : O := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hu.2⟩
  have hprod : uO * uInvO = (1 : O) := by
    apply Subtype.ext
    simp [uO, uInvO]
  have hresNe : IsLocalRing.residue O uO ≠ 0 := by
    intro hz
    have hp := congrArg (IsLocalRing.residue O) hprod
    rw [map_mul, map_one, hz, zero_mul] at hp
    exact zero_ne_one hp
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let r := e.symm (IsLocalRing.residue O uO)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective r
  have hbar : e (Ideal.Quotient.mk v.asIdeal a) = IsLocalRing.residue O uO := by
    rw [ha]
    exact e.apply_symm_apply _
  have hresA : IsLocalRing.residue O uO =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a) := by
    rw [← hbar, v.residueFieldEquivAdicCompletionIntegers_apply_mk]
  have ha_not : a ∉ v.asIdeal := by
    intro hamem
    have hmk : Ideal.Quotient.mk v.asIdeal a = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hamem
    have hzero : IsLocalRing.residue O uO = 0 := by
      rw [← hbar, hmk]
      rfl
    exact hresNe hzero
  have hdiff_mem : uO - algebraMap (𝓞 F) O a ∈ IsLocalRing.maximalIdeal O := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    have hzero : IsLocalRing.residue O (uO - algebraMap (𝓞 F) O a) = 0 := by
      rw [map_sub]
      have hresA' : IsLocalRing.residue O uO =
          IsLocalRing.residue O (algebraMap (𝓞 F) O a) := by
        change IsLocalRing.residue O uO =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a)
        exact hresA
      rw [hresA', sub_self]
    exact hzero
  have hmax (z : O) : z ∈ IsLocalRing.maximalIdeal O ↔
      Valued.v (z : v.adicCompletion F) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (v.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))
  have hlt : Valued.v ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) < 1 :=
    (hmax _).1 hdiff_mem
  have hmap : ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    exact (HeightOneSpectrum.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers
      (K := F) (v := v) a).symm
  have hcoerce : ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      (u : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    change (uO : v.adicCompletion F) -
      ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) = _
    rw [hmap]
  rw [hcoerce] at hlt
  exact ⟨a, ha_not, hlt⟩

private lemma thetaExterior_localChiOfApprox (D : FieldData F) (v : FinPlace F)
    (t : (v.adicCompletion F)ˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hta : Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1) :
    localChi D v t = chi D v (a : F) := by
  have hex : ∃ b : 𝓞 F, b ∉ v.asIdeal ∧ Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1 := ⟨a, ha, hta⟩
  have hcmp' : Valued.v (((hex.choose : F) : v.adicCompletion F) -
      ((a : F) : v.adicCompletion F)) < 1 := by
    have h := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_sub_lt hta hex.choose_spec.2
    have hEq : ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) -
        ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose)) =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose) -
            algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by ring
    rw [hEq] at h
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_sub,
      v.valuedAdicCompletion_eq_valuation'] using h
  have hres : residue v (hex.choose : F) = residue v (a : F) :=
    thetaExterior_residueIntegralCongr v hex.choose a hcmp'
  have hchi := thetaExterior_chiCongr D v (hex.choose : F) (a : F) hres
  unfold localChi
  rw [dif_pos hex]
  exact hchi

private lemma thetaExterior_localChiToLoc (D : FieldData F) (v : FinPlace F)
    (x : Fˣ) (hx : HeightOneSpectrum.valuation F v (x : F) = 1) :
    localChi D v (toLoc v x) = chi D v (x : F) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  have hvalInv : Valued.v (((toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simp [hval]
  have hu : IsLocUnit v (toLoc v x) := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvalInv]
  obtain ⟨a, ha, hta⟩ := thetaExterior_localUnitApproximant v (toLoc v x) hu
  have hvalSub : HeightOneSpectrum.valuation F v ((x : F) - (a : F)) < 1 := by
    have hta' : Valued.v
        (algebraMap F (v.adicCompletion F) ((x : F) - (a : F))) < 1 := by
      change Valued.v ((toLoc v x : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 at hta
      have hcast : (toLoc v x : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) (x : F) := rfl
      rw [hcast, ← map_sub] at hta
      exact hta
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hta'
  have hres : residue v (a : F) = residue v (x : F) := by
    have hvalSwap : HeightOneSpectrum.valuation F v ((a : F) - (x : F)) < 1 := by
      rw [show (a : F) - (x : F) = -((x : F) - (a : F)) by ring, Valuation.map_neg]
      exact hvalSub
    exact (thetaExterior_residueCongr v (a : F) (x : F) (v.valuation_le_one a)
      (le_of_eq hx) hvalSwap)
  have hchi := thetaExterior_chiCongr D v (a : F) (x : F) hres
  calc
    localChi D v (toLoc v x) = chi D v (a : F) :=
      thetaExterior_localChiOfApprox D v (toLoc v x) a ha hta
    _ = chi D v (x : F) := hchi

private theorem thetaExterior_trace_eq_pair_sum_re [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
  have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
    rw [hring.symm] at htrace
    exact htrace
  rw [hall]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
  apply Finset.sum_congr rfl
  intro w hw
  have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
      φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w] at h
      have h' := InfinitePlace.mk_eq_iff.mp h
      rcases h' with h' | h'
      · exact Or.inl (by simpa using h')
      · right
        have hc := congrArg ComplexEmbedding.conjugate h'
        simpa using hc
    · intro h
      rw [← InfinitePlace.mk_embedding w]
      apply InfinitePlace.mk_eq_iff.mpr
      rcases h with h | h
      · exact Or.inl (by simpa using h)
      · right
        have hc := congrArg ComplexEmbedding.conjugate h
        simpa using hc
  have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    apply IsTotallyComplex.complexEmbedding_not_isReal w.embedding
    rw [ComplexEmbedding.isReal_iff]
    exact h.symm
  have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
    ext φ
    simp [hmk]
  change (∑ φ ∈ Finset.univ.filter
    (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
  rw [hset, Finset.sum_pair hneq]

private theorem thetaExterior_trace_eq_two_real_sum [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  rw [thetaExterior_trace_eq_pair_sum_re]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

private theorem thetaExterior_archExp_eq_trace [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F, -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I *
          ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
            rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
      rw [thetaExterior_trace_eq_two_real_sum]
      ring

private lemma thetaExterior_e_singleOutside (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf) (z : F)
    (hout : ∀ w : FinPlace F, w ∉ S.Sf → w ≠ v →
      HeightOneSpectrum.valuation F w z ≤ 1) :
    S.e A (S.diag z) * A.ψ v (algebraMap F (v.adicCompletion F) z) = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let f : FinPlace F → ℂ := fun w => A.ψ w (algebraMap F (w.adicCompletion F) z)
  have hfinite : (Function.mulSupport f).Finite := (A.trivial_on_F z).1
  have hsplit : (∏ᶠ w : FinPlace F, f w) =
      (∏ w ∈ S.Sf, f w) *
        ∏ᶠ w ∈ ((S.Sf : Set (FinPlace F))ᶜ), f w := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hfinite Set.inter_subset_right) (f := f)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have houtside : ∀ w : FinPlace F, w ∉ S.Sf → w ≠ v → f w = 1 := by
    intro w hwS hw
    have hmem : algebraMap F (w.adicCompletion F) z ∈
        w.adicCompletionIntegers F := by
      change (z : w.adicCompletion F) ∈ w.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hout w hwS hw
    exact A.integral w _ hmem
  have htail : (∏ᶠ w ∈ ((S.Sf : Set (FinPlace F))ᶜ), f w) = f v := by
    have hsupp : ((S.Sf : Set (FinPlace F))ᶜ ∩ Function.mulSupport f) ⊆
        ({v} : Finset (FinPlace F)) := by
      intro w hw
      rcases hw with ⟨hwS, hwf⟩
      by_contra hne
      have hneV : w ≠ v := by
        intro hEq
        apply hne
        simp [hEq]
      exact (Function.mem_mulSupport.mp hwf) (houtside w hwS hneV)
    have hsingle : ↑({v} : Finset (FinPlace F)) ⊆
        (S.Sf : Set (FinPlace F))ᶜ := by
      intro w hw
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hw
      simpa [hw] using hv
    rw [finprod_mem_eq_prod_of_subset f hsupp hsingle]
    simp
  have hglobal := (A.trivial_on_F z).2
  rw [hsplit, htail, ← thetaExterior_archExp_eq_trace (F := F) z] at hglobal
  change (∏ w ∈ S.Sf, A.ψ w (algebraMap F (w.adicCompletion F) z)) *
      A.ψ v (algebraMap F (v.adicCompletion F) z) *
      ∏ w : InfinitePlace F, psiC (w.embedding z) = 1 at hglobal
  have hSprod :
      (∏ w ∈ S.Sf, A.ψ w (algebraMap F (w.adicCompletion F) z)) =
        ∏ w : S.Sf, A.ψ w.1 (algebraMap F (w.1.adicCompletion F) z) := by
    exact (Finset.prod_coe_sort S.Sf
      (fun w => A.ψ w (algebraMap F (w.adicCompletion F) z))).symm
  have hglobal' :
      (∏ w : S.Sf, A.ψ w.1 (algebraMap F (w.1.adicCompletion F) z)) *
        ((∏ w : InfinitePlace F, psiC (w.embedding z)) *
          A.ψ v (algebraMap F (v.adicCompletion F) z)) = 1 := by
    calc
      _ = (∏ w ∈ S.Sf, A.ψ w (algebraMap F (w.adicCompletion F) z)) *
            A.ψ v (algebraMap F (v.adicCompletion F) z) *
            ∏ w : InfinitePlace F, psiC (w.embedding z) := by rw [← hSprod]; ac_rfl
      _ = 1 := hglobal
  simpa [SData.e, SData.diag, mul_assoc] using hglobal'

private lemma thetaExterior_e_integralOutside (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (z : F)
    (hout : ∀ v : FinPlace F, v ∉ S.Sf →
      HeightOneSpectrum.valuation F v z ≤ 1) :
    S.e A (S.diag z) = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let f : FinPlace F → ℂ := fun v => A.ψ v (algebraMap F (v.adicCompletion F) z)
  have hfinite : (Function.mulSupport f).Finite := (A.trivial_on_F z).1
  have hsplit : (∏ᶠ w : FinPlace F, f w) =
      (∏ w ∈ S.Sf, f w) * ∏ᶠ w ∈ ((S.Sf : Set (FinPlace F))ᶜ), f w := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hfinite Set.inter_subset_right) (f := f)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have htail : (∏ᶠ w ∈ ((S.Sf : Set (FinPlace F))ᶜ), f w) = 1 := by
    apply finprod_mem_eq_one_of_forall_eq_one
    intro w hw
    have hmem : algebraMap F (w.adicCompletion F) z ∈
        w.adicCompletionIntegers F := by
      change (z : w.adicCompletion F) ∈ w.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hout w hw
    exact A.integral w _ hmem
  have hglobal := (A.trivial_on_F z).2
  rw [hsplit, htail, ← thetaExterior_archExp_eq_trace (F := F) z] at hglobal
  simp only [mul_one] at hglobal
  have hSprod : (∏ w ∈ S.Sf, A.ψ w (algebraMap F (w.adicCompletion F) z)) =
      ∏ w : S.Sf, A.ψ w.1 (algebraMap F (w.1.adicCompletion F) z) :=
    (Finset.prod_coe_sort S.Sf
      (fun w => A.ψ w (algebraMap F (w.adicCompletion F) z))).symm
  have hglobal' :
      (∏ w : S.Sf, A.ψ w.1 (algebraMap F (w.1.adicCompletion F) z)) *
        ∏ w : InfinitePlace F,
          Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ))) = 1 := by
    calc
      _ = (∏ w ∈ S.Sf, f w) *
            ∏ w : InfinitePlace F,
              Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ))) := by
                simp only [f]
                rw [← hSprod]
      _ = 1 := by simpa only [f, psiC] using hglobal
  simpa [SData.e, SData.diag, psiC, mul_assoc] using hglobal'

private lemma thetaExterior_residueAlgMap (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  simpa using thetaExterior_residueRep v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)

private lemma thetaExterior_residueNeZeroOfValOne (v : FinPlace F) (x : F)
    (hx : HeightOneSpectrum.valuation F v x = 1) : residue v x ≠ 0 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x (le_of_eq hx)
  have hbnot : b.val ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp b.property
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 hbnot
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) := by
    have h := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using h
  have hanot : a ∉ v.asIdeal := by
    apply (v.valuation_eq_one_iff_notMem (K := F) (r := a)).1
    rw [← hval]
    exact hx
  have haq : Ideal.Quotient.mk v.asIdeal a ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hanot
  have hbq : Ideal.Quotient.mk v.asIdeal b.val ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hbnot
  rw [thetaExterior_residueRep v x a b.val hbnot hab]
  exact div_ne_zero haq hbq

private lemma thetaExterior_val_lt_one_le_exp_neg_one (v : FinPlace F) (x : F)
    (hx : HeightOneSpectrum.valuation F v x < 1) :
    HeightOneSpectrum.valuation F v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hvne : HeightOneSpectrum.valuation F v x ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hx0
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v x) < 0 := by
    rw [← WithZero.exp_log hvne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    exact hx
  have hlog' : WithZero.log (HeightOneSpectrum.valuation F v x) ≤ -1 := by omega
  calc
    HeightOneSpectrum.valuation F v x =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v x)) :=
      (WithZero.exp_log hvne).symm
    _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr hlog'

private lemma thetaExterior_psiCongr (A : AddCharData F) (v : FinPlace F)
    (x y : F) (hxy : HeightOneSpectrum.valuation F v (x - y) ≤ 1) :
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
      A.ψ v (algebraMap F (v.adicCompletion F) y) := by
  have hmem : algebraMap F (v.adicCompletion F) (x - y) ∈ v.adicCompletionIntegers F := by
    change ((x - y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxy
  have hphase : A.ψ v (algebraMap F (v.adicCompletion F) (x - y)) = 1 :=
    A.integral v _ hmem
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) x) (algebraMap F (v.adicCompletion F) y)
  have hyne : A.ψ v (algebraMap F (v.adicCompletion F) y) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v) (algebraMap F (v.adicCompletion F) y)).ne_zero
  have harg : algebraMap F (v.adicCompletion F) (x - y) =
      algebraMap F (v.adicCompletion F) x - algebraMap F (v.adicCompletion F) y := by
    rw [← map_sub]
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
        (A.ψ v (algebraMap F (v.adicCompletion F) x) /
          A.ψ v (algebraMap F (v.adicCompletion F) y)) *
          A.ψ v (algebraMap F (v.adicCompletion F) y) := by
            rw [div_mul_cancel₀ _ hyne]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (x - y)) *
          A.ψ v (algebraMap F (v.adicCompletion F) y) := by rw [← hdiv, ← harg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) y) := by rw [hphase, one_mul]

private lemma thetaExterior_phaseErr (A : AddCharData F) (v : FinPlace F)
    (p : Fˣ) (hpval : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) = 1 := by
  have hvalNum : HeightOneSpectrum.valuation F v ((a : F) - b) ≤ WithZero.exp (-1 : ℤ) := by
    change v.valuation F (algebraMap (𝓞 F) F (a - b)) ≤ WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    apply (v.intValuation_le_pow_iff_mem (a - b) 1).2
    simpa using hab
  have hvalDiv : HeightOneSpectrum.valuation F v (((a : F) - b) / (p : F)) ≤ 1 := by
    rw [map_div₀, hpval]
    have hpos : 0 < WithZero.exp (-1 : ℤ) :=
      lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    exact (div_le_one₀ hpos).2 hvalNum
  have hlocal : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) ∈
      v.adicCompletionIntegers F := by
    change ((((a : F) - b) / (p : F) : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hvalDiv
  exact A.integral v _ hlocal

private lemma thetaExterior_phaseCongr (A : AddCharData F) (v : FinPlace F)
    (p : Fˣ) (hpval : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
  have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) =
      algebraMap F (v.adicCompletion F) ((a : F) / (p : F)) -
        algebraMap F (v.adicCompletion F) ((b : F) / (p : F)) := by
    have hF : ((a : F) - b) / (p : F) = (a : F) / (p : F) - (b : F) / (p : F) := by
      field_simp [Units.ne_zero p]
    rw [hF, map_sub]
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) ((a : F) / (p : F)))
    (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))
  have hbne : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v)
      (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))).ne_zero
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
        (A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) /
          A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))) *
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
          rw [div_mul_cancel₀ _ hbne]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) *
          A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [← hdiv, ← harg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [thetaExterior_phaseErr A v p hpval a b hab, one_mul]

private lemma thetaExterior_valOfPrincipalCount (v : FinPlace F) (x : Fˣ) (m : ℤ)
    (hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) = m) :
    HeightOneSpectrum.valuation F v (x : F) = WithZero.exp (-m) := by
  have hprincipal := thetaExterior_count_spanSingleton v (x : F) (Units.ne_zero x)
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v (x : F)) = -m := by
    have h := hcount
    rw [hprincipal] at h
    linarith
  have hne : HeightOneSpectrum.valuation F v (x : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr (Units.ne_zero x)
  calc
    HeightOneSpectrum.valuation F v (x : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (x : F))) :=
      (WithZero.exp_log hne).symm
    _ = WithZero.exp (-m) := by rw [hlog]

private lemma thetaExterior_genVal (S : SData F CE condη) (I : Ideal (𝓞 F)) (x : Fˣ)
    (hx : S.IsGen (x : F) I) (v : FinPlace F) (hv : v ∉ S.Sf) :
    HeightOneSpectrum.valuation F v (x : F) =
      WithZero.exp (-FractionalIdeal.count F v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
  apply thetaExterior_valOfPrincipalCount v x _
  exact hx.2.2 v hv

private lemma thetaExterior_count_prime_zero (v w : FinPlace F) (hvw : v ≠ w) :
    FractionalIdeal.count F w
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
  have hwnonzero : w.asIdeal ≠ ⊥ := by simpa [Ideal.zero_eq_bot] using w.ne_bot
  rw [FractionalIdeal.count_coe F w v.ne_bot]
  have hfac : (Associates.mk w.asIdeal).count (Associates.mk v.asIdeal).factors = 0 := by
    by_contra hne
    have hdvd := (Associates.count_ne_zero_iff_dvd v.ne_bot w.irreducible).mp hne
    rw [Ideal.dvd_iff_le] at hdvd
    have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hdvd
    exact hvw (HeightOneSpectrum.ext heq)
  exact_mod_cast hfac

private lemma thetaExterior_toLocIsLocUnit (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  have hvalInv : Valued.v (((toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simp [hval]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvalInv]

private lemma thetaExterior_chiIdealPow_prime (D : FieldData F) (v : FinPlace F)
    (x : F) (j : ℤ) : chiIdealPow D v.asIdeal x j = chiPow D v x j := by
  have hnf : UniqueFactorizationMonoid.normalizedFactors v.asIdeal = {v.asIdeal} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible]
    simp [normalize_eq]
  simp [chiIdealPow, hnf, v.isPrime, v.ne_bot]

private lemma thetaExterior_prod_primes_ne_bot (T : Finset (FinPlace F)) :
    (∏ v ∈ T, v.asIdeal) ≠ (⊥ : Ideal (𝓞 F)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert v T hv ih =>
      rw [Finset.prod_insert hv]
      intro hzero
      rw [Ideal.mul_eq_bot] at hzero
      rcases hzero with hzero | hzero
      · exact v.ne_bot hzero
      · exact ih hzero

private lemma thetaExterior_chiIdealPow_prod_primes
    (D : FieldData F) (S : SData F CE condη) (T : Finset (FinPlace F))
    (x : F) (e : ℤ) :
    chiIdealPow D (∏ v ∈ T, v.asIdeal) x e =
      ∏ v ∈ T, chiPow D v x e := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  induction T using Finset.induction_on with
  | empty =>
      simpa using SB.ideal_one x e
  | @insert v T hv ih =>
      rw [Finset.prod_insert hv]
      rw [SB.ideal_mul v.asIdeal (∏ w ∈ T, w.asIdeal) v.ne_bot
        (thetaExterior_prod_primes_ne_bot T) x e]
      rw [thetaExterior_chiIdealPow_prime D v x e, ih]
      rw [Finset.prod_insert hv]

private lemma thetaExterior_phaseScale (A : AddCharData F) (v : FinPlace F)
    (p π : Fˣ)
    (hpval : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (hπval : HeightOneSpectrum.valuation F v (π : F) = WithZero.exp (-1 : ℤ))
    (u₀ t₀ : 𝓞 F)
    (hclose : HeightOneSpectrum.valuation F v ((p : F) / (π : F) - (u₀ : F)) < 1)
    (ht₀u₀ : t₀ - u₀ ∈ v.asIdeal) (y : 𝓞 F) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((y : F) * (t₀ : F) / (p : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((y : F) / (π : F))) := by
  have hcloseLe : HeightOneSpectrum.valuation F v ((p : F) / (π : F) - (u₀ : F)) ≤
      WithZero.exp (-1 : ℤ) :=
    thetaExterior_val_lt_one_le_exp_neg_one v _ hclose
  have ht₀u₀val : HeightOneSpectrum.valuation F v ((t₀ : F) - (u₀ : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    change v.valuation F (algebraMap (𝓞 F) F (t₀ - u₀)) ≤ WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem (t₀ - u₀) 1).2 (by simpa using ht₀u₀)
  have hu₀ratio : HeightOneSpectrum.valuation F v ((u₀ : F) - (p : F) / (π : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [show (u₀ : F) - (p : F) / (π : F) = -((p : F) / (π : F) - (u₀ : F)) by ring,
      Valuation.map_neg]
    exact hcloseLe
  have hdelta : HeightOneSpectrum.valuation F v ((t₀ : F) - (p : F) / (π : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [show (t₀ : F) - (p : F) / (π : F) =
      ((t₀ : F) - u₀) + ((u₀ : F) - (p : F) / (π : F)) by ring]
    exact (v.valuation F).map_add_le ht₀u₀val hu₀ratio
  have hyval : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := v.valuation_le_one y
  have hnum : HeightOneSpectrum.valuation F v
      ((y : F) * ((t₀ : F) - (p : F) / (π : F))) ≤
        HeightOneSpectrum.valuation F v (p : F) := by
    rw [map_mul]
    calc
      _ ≤ 1 * HeightOneSpectrum.valuation F v ((t₀ : F) - (p : F) / (π : F)) :=
        mul_le_mul_of_nonneg_right hyval
          (WithZero.zero_le (HeightOneSpectrum.valuation F v ((t₀ : F) - (p : F) / (π : F))))
      _ = HeightOneSpectrum.valuation F v ((t₀ : F) - (p : F) / (π : F)) := by simp
      _ ≤ WithZero.exp (-1 : ℤ) := hdelta
      _ = HeightOneSpectrum.valuation F v (p : F) := hpval.symm
  have harg : ((y : F) * (t₀ : F) / (p : F)) - (y : F) / (π : F) =
      ((y : F) * ((t₀ : F) - (p : F) / (π : F))) / (p : F) := by
    field_simp [Units.ne_zero p, Units.ne_zero π] <;> ring
  have hval : HeightOneSpectrum.valuation F v
      (((y : F) * (t₀ : F) / (p : F)) - (y : F) / (π : F)) ≤ 1 := by
    rw [harg, map_div₀]
    have hp_pos : 0 < HeightOneSpectrum.valuation F v (p : F) :=
      lt_of_le_of_ne zero_le (Ne.symm (by rw [hpval]; exact WithZero.exp_ne_zero))
    exact (div_le_one₀ hp_pos).2 hnum
  exact thetaExterior_psiCongr A v _ _ hval

private lemma thetaExterior_gammaPrime (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ)
    (hp : S.IsGen (p : F) v.asIdeal) :
    gamma D S A 2 v.asIdeal (p : F) =
      chi D v ((p : F) / unif v) ^ 2 * g2 D A v := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := ArtinPrimitiveRoots.A2.bridgeResidueField v
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F v
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hvalP : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    simpa [hcountP] using thetaExterior_valOfPrincipalCount v p 1 hcountP
  have hvalπ : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (v.valuation_exists_uniformizer F).choose_spec
  let π : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
  have hvalπ' : HeightOneSpectrum.valuation F v (π : F) = WithZero.exp (-1 : ℤ) := by
    exact hvalπ
  let r : Fˣ := p / π
  have hvalr : HeightOneSpectrum.valuation F v (r : F) = 1 := by
    simpa [r, Units.val_div_eq_div_val, map_div₀, hvalP, hvalπ']
  have hlocUnit : IsLocUnit v (toLoc v r) := thetaExterior_toLocIsLocUnit v r hvalr
  obtain ⟨u₀, hu₀, happrox⟩ := thetaExterior_localUnitApproximant v (toLoc v r) hlocUnit
  have hclose : HeightOneSpectrum.valuation F v ((r : F) - (u₀ : F)) < 1 := by
    have happrox' : Valued.v
        (algebraMap F (v.adicCompletion F) ((r : F) - (u₀ : F))) < 1 := by
      change Valued.v ((toLoc v r : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F u₀)) < 1 at happrox
      have hcast : (toLoc v r : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) (r : F) := rfl
      rw [hcast, ← map_sub] at happrox
      exact happrox
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using happrox'
  have hresr : residue v (r : F) = Ideal.Quotient.mk v.asIdeal u₀ := by
    have hcongr := thetaExterior_residueCongr v (r : F) (u₀ : F)
      (le_of_eq hvalr) (v.valuation_le_one u₀) hclose
    rw [hcongr, thetaExterior_residueAlgMap]
  let t : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk v.asIdeal u₀
  have ht_nonzero : t ≠ 0 := by
    intro ht
    exact hu₀ ((Ideal.Quotient.eq_zero_iff_mem).1 (by simpa [t] using ht))
  have ht_out : Ideal.Quotient.mk v.asIdeal t.out = t := by simp
  have ht_res : residue v (t.out : F) = residue v (r : F) := by
    calc
      residue v (t.out : F) = Ideal.Quotient.mk v.asIdeal t.out :=
        thetaExterior_residueAlgMap v t.out
      _ = t := ht_out
      _ = residue v (r : F) := hresr.symm
  have ht_out_mem : t.out - u₀ ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hzero : Ideal.Quotient.mk v.asIdeal (t.out - u₀) = 0 := by
      rw [map_sub, ht_out]
      simp [t]
    exact hzero
  have hvalOutU : HeightOneSpectrum.valuation F v ((t.out : F) - (u₀ : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    change v.valuation F (algebraMap (𝓞 F) F (t.out - u₀)) ≤ WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem (t.out - u₀) 1).2 (by simpa using ht_out_mem)
  have hcloseLe : HeightOneSpectrum.valuation F v ((r : F) - (u₀ : F)) ≤
      WithZero.exp (-1 : ℤ) :=
    thetaExterior_val_lt_one_le_exp_neg_one v _ hclose
  have hvalOutR : HeightOneSpectrum.valuation F v ((t.out : F) - (r : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [show (t.out : F) - (r : F) =
      ((t.out : F) - (u₀ : F)) + ((u₀ : F) - (r : F)) by ring]
    have hu0r : HeightOneSpectrum.valuation F v ((u₀ : F) - (r : F)) ≤
        WithZero.exp (-1 : ℤ) := by
      rw [show (u₀ : F) - (r : F) = -((r : F) - (u₀ : F)) by ring,
        Valuation.map_neg]
      exact hcloseLe
    exact (v.valuation F).map_add_le hvalOutU hu0r
  obtain ⟨hchars, _, hψData⟩ :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR D S A v hv p hp
  obtain ⟨χ₂, hχ₂⟩ := hchars 2
  obtain ⟨ψc, _, hψc⟩ := hψData
  have hχt : χ₂ t = chi D v (r : F) ^ 2 := by
    have hresOut : residue v (algebraMap (𝓞 F) F t.out) = residue v (r : F) := by
      change residue v (t.out : F) = residue v (r : F)
      exact ht_res
    have hresOutNe : residue v (algebraMap (𝓞 F) F t.out) ≠ 0 := by
      rw [hresOut]
      exact thetaExterior_residueNeZeroOfValOne v (r : F) hvalr
    have hchiOut := thetaExterior_chiCongr D v
      (algebraMap (𝓞 F) F t.out) (r : F) hresOut
    rw [hχ₂ t, chiPow, if_neg hresOutNe]
    change chi D v (algebraMap (𝓞 F) F t.out) ^ 2 = chi D v (r : F) ^ 2
    exact congrArg (fun z : ℂ => z ^ 2) hchiOut
  have honeDiff : (1 : 𝓞 F ⧸ v.asIdeal).out - (1 : 𝓞 F) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hout1 : Ideal.Quotient.mk v.asIdeal (1 : 𝓞 F ⧸ v.asIdeal).out = 1 := by simp
    rw [map_sub, hout1]
    simp
  have honeNum (x : 𝓞 F ⧸ v.asIdeal) :
      x.out * (1 : 𝓞 F ⧸ v.asIdeal).out - x.out ∈ v.asIdeal := by
    have hmem : x.out * ((1 : 𝓞 F ⧸ v.asIdeal).out - 1) ∈ v.asIdeal :=
      v.asIdeal.mul_mem_left x.out honeDiff
    rw [show x.out * (1 : 𝓞 F ⧸ v.asIdeal).out - x.out =
      x.out * ((1 : 𝓞 F ⧸ v.asIdeal).out - 1) by ring]
    exact hmem
  have hψone (x : 𝓞 F ⧸ v.asIdeal) :
      ψc x = A.ψ v (algebraMap F (v.adicCompletion F)
        ((x.out : F) / (p : F))) := by
    have h := hψc (1 : 𝓞 F ⧸ v.asIdeal) x
    have hmul : (1 : 𝓞 F ⧸ v.asIdeal) * x = x := one_mul x
    rw [hmul] at h
    calc
      ψc x = A.ψ v (algebraMap F (v.adicCompletion F)
          ((x.out : F) * ((1 : 𝓞 F ⧸ v.asIdeal).out : F) / (p : F))) := h
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F))) :=
        thetaExterior_phaseCongr A v p hvalP (x.out * (1 : 𝓞 F ⧸ v.asIdeal).out)
          x.out (honeNum x)
  have hψnegOne (x : 𝓞 F ⧸ v.asIdeal) :
      ψc (-x) = A.ψ v (algebraMap F (v.adicCompletion F) (-((x.out : F) / (p : F)))) := by
    calc
      ψc (-x) = (ψc x)⁻¹ := AddChar.map_neg_eq_inv ψc x
      _ = (A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F))))⁻¹ := by
        rw [hψone x]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (-((x.out : F) / (p : F)))) :=
        by
          simpa only [map_neg] using
            (AddChar.map_neg_eq_inv (A.ψ v)
              (algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F)))).symm
  have hψscaled (y : 𝓞 F ⧸ v.asIdeal) :
      ψc (t * y) = A.ψ v (algebraMap F (v.adicCompletion F)
        ((y.out : F) / (π : F))) := by
    calc
      ψc (t * y) = A.ψ v (algebraMap F (v.adicCompletion F)
          ((algebraMap (𝓞 F) F y.out * algebraMap (𝓞 F) F t.out) / (p : F))) :=
        hψc t y
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          ((y.out : F) * (t.out : F) / (p : F))) := by rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((y.out : F) / (π : F))) :=
        thetaExterior_phaseScale A v p π hvalP hvalπ' u₀ t.out
          (by simpa [r] using hclose) ht_out_mem y.out
  have hsixNotMem : (6 : 𝓞 F) ∉ v.asIdeal := by
    intro h6
    exact hv (S.over6 v h6)
  have hchiNeg : chi D v (-1 : F) = 1 := by
    have hvalneg : HeightOneSpectrum.valuation F v (-1 : F) = 1 := by simp
    have hlocal := thetaExterior_localChiToLoc D v (-1 : Fˣ) hvalneg
    have hlocalOne := (localChi_basic (D := D) (v := v) hsixNotMem).2.1
    have htoLocNeg : toLoc v (-1 : Fˣ) = (-1 : (v.adicCompletion F)ˣ) := by
      apply Units.ext
      simp [toLoc]
    calc
      chi D v (-1 : F) = localChi D v (toLoc v (-1 : Fˣ)) := hlocal.symm
      _ = 1 := by rw [htoLocNeg]; exact hlocalOne
  have hresNeg : residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) =
      residue v (-1 : F) := by
    calc
      residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) =
          Ideal.Quotient.mk v.asIdeal ((-1 : 𝓞 F ⧸ v.asIdeal).out) :=
        thetaExterior_residueAlgMap v _
      _ = (-1 : 𝓞 F ⧸ v.asIdeal) := by simp
      _ = residue v (-1 : F) := by
        have h := thetaExterior_residueAlgMap v (-1 : 𝓞 F)
        simpa using h.symm
  have hchi2Neg : χ₂ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hresne : residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) ≠ 0 := by
      rw [hresNeg]
      exact thetaExterior_residueNeZeroOfValOne v (-1 : F) (by simp)
    have hχneg := thetaExterior_chiCongr D v
      (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) (-1 : F) hresNeg
    calc
      χ₂ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 2 := hχ₂ _
      _ = chi D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) ^ (2 : ℤ) := by
        simp only [chiPow, if_neg hresne]
      _ = chi D v (-1 : F) ^ (2 : ℤ) :=
        congrArg (fun z : ℂ => z ^ (2 : ℤ)) hχneg
      _ = 1 := by simp [hchiNeg]
  have hchiNegMul (y : 𝓞 F ⧸ v.asIdeal) :
      χ₂ (-(t * y)) = χ₂ t * χ₂ y := by
    have hneg : -(t * y) = (-1 : 𝓞 F ⧸ v.asIdeal) * (t * y) := by ring
    rw [hneg, map_mul, hchi2Neg, one_mul, map_mul]
  have heGamma (x : 𝓞 F ⧸ v.asIdeal) :
      S.e A (S.diag ((algebraMap (𝓞 F) F x.out) / (p : F))) = ψc (-x) := by
    let z : F := (algebraMap (𝓞 F) F x.out) / (p : F)
    have hout : ∀ w : FinPlace F, w ∉ S.Sf → w ≠ v →
        HeightOneSpectrum.valuation F w z ≤ 1 := by
      intro w hwS hwv
      have hwgen := thetaExterior_genVal S v.asIdeal p hp w hwS
      have hwcnt := thetaExterior_count_prime_zero v w hwv.symm
      rw [hwcnt] at hwgen
      have hwvalp : HeightOneSpectrum.valuation F w (p : F) = 1 := by
        simpa using hwgen
      dsimp [z]
      rw [map_div₀, hwvalp, div_one]
      exact w.valuation_le_one x.out
    have he := thetaExterior_e_singleOutside D S A v hv z hout
    have hpsiZ : ψc (-x) = A.ψ v (algebraMap F (v.adicCompletion F) (-z)) := by
      simpa [z] using hψnegOne x
    have hψZinv : ψc (-x) = (A.ψ v (algebraMap F (v.adicCompletion F) z))⁻¹ := by
      have hmapNeg : algebraMap F (v.adicCompletion F) (-z) =
          -(algebraMap F (v.adicCompletion F) z) := by rw [map_neg]
      rw [hmapNeg] at hpsiZ
      exact hpsiZ.trans (AddChar.map_neg_eq_inv (A.ψ v)
        (algebraMap F (v.adicCompletion F) z))
    calc
      S.e A (S.diag z) = (A.ψ v (algebraMap F (v.adicCompletion F) z))⁻¹ :=
        eq_inv_of_mul_eq_one_left he
      _ = ψc (-x) := hψZinv.symm
  let G : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x =>
    chiPow D v (algebraMap (𝓞 F) F x.out) 2 * ψc (-x)
  let G₂ : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y =>
    chiPow D v (algebraMap (𝓞 F) F y.out) 2 *
      A.ψ v (algebraMap F (v.adicCompletion F) ((y.out : F) / (π : F)))
  have hsumGamma :
      (∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
        chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) 2 *
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) / (p : F)))) =
        (chi D v (r : F) ^ 2) *
          (∑ᶠ y : 𝓞 F ⧸ v.asIdeal,
            chiPow D v (algebraMap (𝓞 F) F y.out) 2 *
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((y.out : F) / (π : F)))) := by
    calc
      _ = ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          chiPow D v (algebraMap (𝓞 F) F x.out) 2 * ψc (-x) := by
            apply finsum_congr
            intro x
            rw [thetaExterior_chiIdealPow_prime D v _ 2, heGamma x]
      _ = ∑ᶠ y : 𝓞 F ⧸ v.asIdeal,
          chiPow D v (algebraMap (𝓞 F) F (-(t * y)).out) 2 * ψc (-(-(t * y))) := by
            let e : (𝓞 F ⧸ v.asIdeal) ≃ (𝓞 F ⧸ v.asIdeal) := {
              toFun := fun y => -(t * y)
              invFun := fun x => t⁻¹ * (-x)
              left_inv := by
                intro y
                dsimp
                calc
                  t⁻¹ * (-(-(t * y))) = t⁻¹ * (t * y) := by rw [neg_neg]
                  _ = (t⁻¹ * t) * y := by rw [← mul_assoc]
                  _ = y := by
                    have hcancel : t⁻¹ * t = 1 := inv_mul_cancel₀ ht_nonzero
                    simp only [hcancel, one_mul]
              right_inv := by
                intro x
                dsimp
                calc
                  -(t * (t⁻¹ * (-x))) = -((t * t⁻¹) * (-x)) := by rw [← mul_assoc]
                  _ = x := by
                    have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht_nonzero
                    simp only [hcancel, one_mul, neg_neg] }
            change (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, G x) =
              ∑ᶠ y : 𝓞 F ⧸ v.asIdeal, G (e y)
            exact (finsum_eq_of_bijective
              (f := fun y : 𝓞 F ⧸ v.asIdeal => G (e y)) (g := G)
              e e.bijective (fun _ => rfl)).symm
      _ = ∑ᶠ y : 𝓞 F ⧸ v.asIdeal,
          χ₂ (-(t * y)) * ψc (-( -(t * y))) := by
            apply finsum_congr
            intro y
            simpa only [hχ₂]
      _ = ∑ᶠ y : 𝓞 F ⧸ v.asIdeal,
          χ₂ t * (chiPow D v (algebraMap (𝓞 F) F y.out) 2 *
            A.ψ v (algebraMap F (v.adicCompletion F)
              ((y.out : F) / (π : F)))) := by
            apply finsum_congr
            intro y
            calc
              χ₂ (-(t * y)) * ψc (-(-(t * y))) =
                  χ₂ t * χ₂ y * ψc (t * y) := by
                simpa only [hchiNegMul y, neg_neg]
              _ = _ := by rw [hχ₂ y, hψscaled y]; ac_rfl
      _ = (chi D v (r : F) ^ 2) * (∑ᶠ y : 𝓞 F ⧸ v.asIdeal, G₂ y) := by
            simpa only [G₂, hχt] using (mul_finsum G₂ (χ₂ t)).symm
  simp only [gamma, g2]
  rw [hsumGamma]
  simp [r, π, Units.val_div_eq_div_val, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private lemma thetaExterior_prime_dvd_prod
    (T : Finset (FinPlace F)) (v : FinPlace F) (hv : v ∈ T) :
    v.asIdeal ∣ ∏ w ∈ T, w.asIdeal := by
  rw [Ideal.dvd_iff_le]
  rw [← Finset.mul_prod_erase T (fun w => w.asIdeal) hv]
  exact Ideal.mul_le_left

private lemma thetaExterior_pairwise_coprime
    (T : Finset (FinPlace F)) :
    (T : Set (FinPlace F)).Pairwise (fun v w => IsCoprime v.asIdeal w.asIdeal) := by
  intro v hv w hw hvw
  have hne : v.asIdeal ≠ w.asIdeal := by
    intro heq
    exact hvw (HeightOneSpectrum.ext heq)
  letI := v.isMaximal
  letI := w.isMaximal
  exact Ideal.isCoprime_of_isMaximal hne

private lemma thetaExterior_val_unif (v : FinPlace F) :
    HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
  simpa [unif] using (v.valuation_exists_uniformizer F).choose_spec

private lemma thetaExterior_val_div_unif (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = WithZero.exp (-1 : ℤ)) :
    HeightOneSpectrum.valuation F v ((x : F) / unif v) = 1 := by
  rw [map_div₀, hx, thetaExterior_val_unif]
  simp

private lemma thetaExterior_count_le_one_of_squarefree
    (v : FinPlace F) (I : Ideal (𝓞 F)) (hI : I ≠ 0) (hsq : Squarefree I) :
    (Associates.mk v.asIdeal).count (Associates.mk I).factors ≤ 1 := by
  have hnotpow : ¬ v.asIdeal ^ 2 ∣ I := by
    intro hpow
    have hpow' : v.asIdeal * v.asIdeal ∣ I := by simpa [pow_two] using hpow
    exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI).mp hsq)
      v.asIdeal v.irreducible hpow'
  by_contra hle
  have htwo : 2 ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by omega
  have hpow : v.asIdeal ^ 2 ∣ I := by
    rw [← Associates.mk_dvd_mk]
    simp only [Associates.dvd_eq_le, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
      (Associates.irreducible_mk.mpr v.irreducible)).2 htwo
  exact hnotpow hpow

private lemma thetaExterior_count_eq_one_of_dvd_squarefree
    (v : FinPlace F) (I : Ideal (𝓞 F)) (hI : I ≠ 0) (hsq : Squarefree I)
    (hdiv : v.asIdeal ∣ I) :
    (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1 := by
  have hne : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd hI v.irreducible).2 hdiv
  have hle := thetaExterior_count_le_one_of_squarefree v I hI hsq
  omega

private lemma thetaExterior_chi_pow_nat
    (D : FieldData F) (S : SData F CE condη) (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : F) (hx : HeightOneSpectrum.valuation F v x = 1) (n : ℕ) :
    chi D v (x ^ n) = chi D v x ^ n := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  induction n with
  | zero =>
      have hres : residue v (1 : F) ≠ 0 :=
        thetaExterior_residueNeZeroOfValOne v 1 (by simp)
      have hχne : chi D v (1 : F) ≠ 0 := by
        intro hz
        have hnorm := SB.chi_norm v 1 hres
        rw [hz] at hnorm
        norm_num at hnorm
      have hmul := SB.chi_mul v hv (1 : F) 1 (by simp) (by simp)
      have hmul' : chi D v (1 : F) = chi D v (1 : F) * chi D v (1 : F) := by
        simpa using hmul
      have hχmul : chi D v (1 : F) * (1 - chi D v (1 : F)) = 0 := by
        calc
          chi D v (1 : F) * (1 - chi D v (1 : F)) =
              chi D v (1 : F) - chi D v (1 : F) * chi D v (1 : F) := by ring
          _ = 0 := by rw [← hmul']; ring
      have hone : chi D v (1 : F) = 1 := by
        rcases mul_eq_zero.mp hχmul with hz | hz
        · exact (hχne hz).elim
        · exact (sub_eq_zero.mp hz).symm
      simpa using hone
  | succ n ih =>
      have hvaln : HeightOneSpectrum.valuation F v (x ^ n) = 1 := by
        rw [map_pow, hx]
        simp
      calc
        chi D v (x ^ (n + 1)) = chi D v (x ^ n * x) := by rw [pow_succ]
        _ = chi D v (x ^ n) * chi D v x :=
          SB.chi_mul v hv (x ^ n) x hvaln.le hx.le
        _ = chi D v x ^ n * chi D v x := by rw [ih]
        _ = chi D v x ^ (n + 1) := by rw [pow_succ]

private lemma thetaExterior_chi_six_of_unit
    (D : FieldData F) (S : SData F CE condη) (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : F) (hx : HeightOneSpectrum.valuation F v x = 1) :
    chi D v x ^ (6 : ℕ) = 1 := by
  exact (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).chi_six v x
    (thetaExterior_residueNeZeroOfValOne v x hx)

private lemma thetaExterior_val_units_zpow (v : FinPlace F) (π : Fˣ) (m : ℤ)
    (hπ : HeightOneSpectrum.valuation F v (π : F) = WithZero.exp (-1 : ℤ)) :
    HeightOneSpectrum.valuation F v ((π ^ m : Fˣ) : F) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

private lemma thetaExterior_localChi_unitPart_eq_chi
    (D : FieldData F) (S : SData F CE condη) (v : FinPlace F) (hv : v ∉ S.Sf)
    (a : Fˣ) (e : ℤ) (he : ordv v (toLoc v a) = e) :
    localChi D v (unitPart v (toLoc v a)) =
      chi D v ((a : F) / (unif v) ^ e) := by
  let π : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
  have hπ : HeightOneSpectrum.valuation F v (π : F) = WithZero.exp (-1 : ℤ) :=
    thetaExterior_val_unif v
  let x : Fˣ := a / π ^ e
  have hcounta : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = e := by
    rw [thetaExterior_count_principal_eq_ordv, he]
  have hvala : HeightOneSpectrum.valuation F v (a : F) = WithZero.exp (-e) :=
    thetaExterior_valOfPrincipalCount v a e hcounta
  have hvalπpow := thetaExterior_val_units_zpow v π e hπ
  have hvalx : HeightOneSpectrum.valuation F v (x : F) = 1 := by
    change HeightOneSpectrum.valuation F v ((a / π ^ e : Fˣ) : F) = 1
    rw [Units.val_div_eq_div_val, map_div₀, hvala, hvalπpow]
    simp
  have hloc : toLoc v x = unitPart v (toLoc v a) := by
    change toLoc v x = toLoc v a * (toLoc v π) ^ (-ordv v (toLoc v a))
    rw [he]
    simp [x, toLoc, div_eq_mul_inv, zpow_neg]
  have hlocal := thetaExterior_localChiToLoc D v x hvalx
  rw [hloc] at hlocal
  simpa [x, π] using hlocal

private lemma thetaExterior_chi_mod_six
    (x y : ℂ) (hx : x ^ (6 : ℕ) = 1) (hy : y ^ (6 : ℕ) = 1)
    (i j : ℕ) (hi : i = 0 ∨ i = 1) :
    (x * y ^ 3) ^ (2 * (i + 3 * j)) = if i = 0 then 1 else x ^ 2 := by
  have hx3 : (x ^ 2) ^ (3 : ℕ) = 1 := by
    calc
      (x ^ 2) ^ 3 = x ^ (2 * 3) := by rw [← pow_mul]
      _ = x ^ 6 := by congr 1 <;> norm_num
      _ = 1 := hx
  have hy2 : (y ^ 3 : ℂ) ^ (2 : ℕ) = 1 := by
    calc
      (y ^ 3) ^ 2 = y ^ (3 * 2) := by rw [← pow_mul]
      _ = y ^ 6 := by congr 1 <;> norm_num
      _ = 1 := hy
  rcases hi with hi | hi
  · subst i
    have hxmod : (0 + 3 * j) % 3 = 0 := by omega
    have hymod : (2 * (0 + 3 * j)) % 2 = 0 := by omega
    have hxp : x ^ (2 * (0 + 3 * j)) = 1 := by
      calc
        _ = (x ^ 2) ^ (0 + 3 * j) := by rw [pow_mul]
        _ = (x ^ 2) ^ 0 := by rw [pow_eq_pow_mod (0 + 3 * j) hx3, hxmod]
        _ = 1 := by simp
    have hyp : (y ^ 3 : ℂ) ^ (2 * (0 + 3 * j)) = 1 := by
      rw [pow_eq_pow_mod (2 * (0 + 3 * j)) hy2, hymod]
      simp
    rw [mul_pow, hxp, hyp]
    simp
  · subst i
    have hxmod : (1 + 3 * j) % 3 = 1 := by omega
    have hymod : (2 * (1 + 3 * j)) % 2 = 0 := by omega
    have hxp : x ^ (2 * (1 + 3 * j)) = x ^ 2 := by
      calc
        _ = (x ^ 2) ^ (1 + 3 * j) := by rw [pow_mul]
        _ = (x ^ 2) ^ 1 := by rw [pow_eq_pow_mod (1 + 3 * j) hx3, hxmod]
        _ = x ^ 2 := by simp
    have hyp : (y ^ 3 : ℂ) ^ (2 * (1 + 3 * j)) = 1 := by
      rw [pow_eq_pow_mod (2 * (1 + 3 * j)) hy2, hymod]
      simp
    rw [mul_pow, hxp, hyp]
    simp

private lemma thetaExterior_localSymbol_factor
    (D : FieldData F) (S : SData F CE condη)
    (I c n : Ideal (𝓞 F)) (a cg ng ε : Fˣ)
    (hfactor : I = c * n ^ 3) (hA : S.IsGen (a : F) I)
    (hcg : S.IsGen (cg : F) c) (hng : S.IsGen (ng : F) n)
    (hε : ε ∈ S.US) (hdecomp : a = ε ^ 6 * (cg * ng ^ 3))
    (hsq : Squarefree c) (v : FinPlace F) (hv : v ∉ S.Sf) :
    localChi D v (unitPart v (toLoc v a)) ^ (2 * ordv v (toLoc v a)) =
      if v.asIdeal ∣ c then chi D v ((cg : F) / unif v) ^ 2 else 1 := by
  classical
  let i : ℕ := (Associates.mk v.asIdeal).count (Associates.mk c).factors
  let j : ℕ := (Associates.mk v.asIdeal).count (Associates.mk n).factors
  let e : ℤ := ordv v (toLoc v a)
  have hcountc : FractionalIdeal.count F v
      (c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (i : ℤ) := by
    rw [FractionalIdeal.count_coe F v hcg.1.1]
  have hcountn : FractionalIdeal.count F v
      (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (j : ℤ) := by
    rw [FractionalIdeal.count_coe F v hng.1.1]
  have hcountProd : FractionalIdeal.count F v
      ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (i : ℤ) + 3 * (j : ℤ) := by
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
      FractionalIdeal.count_mul F v
        (FractionalIdeal.coeIdeal_ne_zero.mpr hcg.1.1)
        (pow_ne_zero 3 (FractionalIdeal.coeIdeal_ne_zero.mpr hng.1.1)),
      FractionalIdeal.count_pow, hcountc, hcountn]
    ring
  have hcountA : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
      (i : ℤ) + 3 * (j : ℤ) := by
    calc
      _ = FractionalIdeal.count F v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hA.2.2 v hv
      _ = FractionalIdeal.count F v
          ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
            rw [hfactor]
      _ = _ := hcountProd
  have he : e = (i : ℤ) + 3 * (j : ℤ) := by
    dsimp [e]
    calc
      ordv v (toLoc v a) =
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) :=
        (thetaExterior_count_principal_eq_ordv v a).symm
      _ = _ := hcountA
  have heord : ordv v (toLoc v a) = (i : ℤ) + 3 * (j : ℤ) := by
    simpa [e] using he
  have hile : i ≤ 1 :=
    thetaExterior_count_le_one_of_squarefree v c hcg.1.1 hsq
  have hdivCount : v.asIdeal ∣ c → i = 1 := by
    intro hdiv
    exact thetaExterior_count_eq_one_of_dvd_squarefree v c hcg.1.1 hsq hdiv
  have hnotdivCount : ¬v.asIdeal ∣ c → i = 0 := by
    intro hnotdiv
    by_contra hne
    exact hnotdiv ((Associates.count_ne_zero_iff_dvd hcg.1.1 v.irreducible).mp
      (by simpa [i] using hne))
  let π : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
  have hπ : HeightOneSpectrum.valuation F v (π : F) = WithZero.exp (-1 : ℤ) :=
    thetaExterior_val_unif v
  have hvalcg : HeightOneSpectrum.valuation F v (cg : F) = WithZero.exp (-(i : ℤ)) := by
    have h := thetaExterior_genVal S c cg hcg v hv
    rw [hcountc] at h
    exact h
  have hvalng : HeightOneSpectrum.valuation F v (ng : F) = WithZero.exp (-(j : ℤ)) := by
    have h := thetaExterior_genVal S n ng hng v hv
    rw [hcountn] at h
    exact h
  have hvalε : HeightOneSpectrum.valuation F v (ε : F) = 1 := by
    have hε' : ε ∈ (S.Sf : Set (FinPlace F)).unit F := by
      simpa [SData.US] using hε
    exact Set.unit_valuation_eq_one (S.Sf : Set (FinPlace F)) F ⟨ε, hε'⟩ hv
  let xC : Fˣ := cg / π ^ (i : ℤ)
  let xN : Fˣ := ng / π ^ (j : ℤ)
  let xA : Fˣ := a / π ^ e
  have hvalxC : HeightOneSpectrum.valuation F v (xC : F) = 1 := by
    change HeightOneSpectrum.valuation F v ((cg / π ^ (i : ℤ) : Fˣ) : F) = 1
    rw [Units.val_div_eq_div_val, map_div₀, hvalcg,
      thetaExterior_val_units_zpow v π (i : ℤ) hπ]
    simp
  have hvalxN : HeightOneSpectrum.valuation F v (xN : F) = 1 := by
    change HeightOneSpectrum.valuation F v ((ng / π ^ (j : ℤ) : Fˣ) : F) = 1
    rw [Units.val_div_eq_div_val, map_div₀, hvalng,
      thetaExterior_val_units_zpow v π (j : ℤ) hπ]
    simp
  have hvalε6 : HeightOneSpectrum.valuation F v ((ε ^ 6 : Fˣ) : F) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, hvalε]
    simp
  have hvalxN3 : HeightOneSpectrum.valuation F v ((xN ^ 3 : Fˣ) : F) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, hvalxN]
    simp
  have hX : xA = ε ^ 6 * xC * xN ^ 3 := by
    have hπfac : π ^ ((i : ℤ) + (j : ℤ) * 3) =
        π ^ (i : ℤ) * (π ^ (j : ℤ)) ^ 3 := by
      rw [zpow_add, zpow_mul]
      rfl
    have he' : e = (i : ℤ) + (j : ℤ) * 3 := by rw [he]; ring
    calc
      xA = a / (π ^ (i : ℤ) * (π ^ (j : ℤ)) ^ 3) := by
        change a / π ^ e = _
        rw [he', hπfac]
      _ = ε ^ 6 * (cg * ng ^ 3) /
            (π ^ (i : ℤ) * (π ^ (j : ℤ)) ^ 3) := by rw [hdecomp]
      _ = ε ^ 6 * (cg / π ^ (i : ℤ)) * (ng / π ^ (j : ℤ)) ^ 3 := by
        simp only [div_eq_mul_inv, mul_pow, inv_pow]
        rw [mul_inv_rev]
        ac_rfl
  have hcounta : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = e := by
    simpa [e] using thetaExterior_count_principal_eq_ordv v a
  have hvala : HeightOneSpectrum.valuation F v (a : F) = WithZero.exp (-e) :=
    thetaExterior_valOfPrincipalCount v a e hcounta
  have hvalxA : HeightOneSpectrum.valuation F v (xA : F) = 1 := by
    change HeightOneSpectrum.valuation F v ((a / π ^ e : Fˣ) : F) = 1
    rw [Units.val_div_eq_div_val, map_div₀, hvala,
      thetaExterior_val_units_zpow v π e hπ]
    simp
  have hlocal : localChi D v (unitPart v (toLoc v a)) = chi D v (xA : F) := by
    have h := thetaExterior_localChi_unitPart_eq_chi D S v hv a e rfl
    simpa [xA, π, e] using h
  have hchiε6 : chi D v ((ε ^ 6 : Fˣ) : F) = 1 := by
    calc
      chi D v ((ε ^ 6 : Fˣ) : F) = chi D v (ε : F) ^ (6 : ℕ) :=
        thetaExterior_chi_pow_nat D S v hv (ε : F) hvalε 6
      _ = 1 := thetaExterior_chi_six_of_unit D S v hv (ε : F) hvalε
  have hchiX : chi D v (xA : F) =
      chi D v (xC : F) * chi D v (xN : F) ^ 3 := by
    have hvalProd : HeightOneSpectrum.valuation F v
        (((ε ^ 6 : Fˣ) : F) * (xC : F)) = 1 := by
      rw [map_mul, hvalε6, hvalxC]
      simp
    calc
      chi D v (xA : F) =
          chi D v (((ε ^ 6 : Fˣ) : F) * (xC : F) * (xN : F) ^ 3) := by
            have hxArg : (xA : F) =
                ((ε ^ 6 : Fˣ) : F) * (xC : F) * (xN : F) ^ 3 := by
              simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_assoc] using
                congrArg (fun u : Fˣ => (u : F)) hX
            rw [hxArg]
      _ = chi D v (((ε ^ 6 : Fˣ) : F) * (xC : F)) *
            chi D v ((xN : F) ^ 3) :=
        (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).chi_mul v hv
          (((ε ^ 6 : Fˣ) : F) * (xC : F)) ((xN : F) ^ 3)
          hvalProd.le (by rw [map_pow, hvalxN]; simp)
      _ = chi D v ((ε ^ 6 : Fˣ) : F) * chi D v (xC : F) *
            chi D v (xN : F) ^ 3 := by
          rw [(ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).chi_mul v hv
            ((ε ^ 6 : Fˣ) : F) (xC : F) hvalε6.le hvalxC.le,
            thetaExterior_chi_pow_nat D S v hv (xN : F) hvalxN 3]
      _ = chi D v (xC : F) * chi D v (xN : F) ^ 3 := by rw [hchiε6, one_mul]
  have hchiC6 : chi D v (xC : F) ^ (6 : ℕ) = 1 :=
    thetaExterior_chi_six_of_unit D S v hv (xC : F) hvalxC
  have hchiN6 : chi D v (xN : F) ^ (6 : ℕ) = 1 :=
    thetaExterior_chi_six_of_unit D S v hv (xN : F) hvalxN
  have hiNat : i = 0 ∨ i = 1 := by omega
  have hpow : chi D v (xA : F) ^ (2 * e) =
      if i = 0 then 1 else chi D v (xC : F) ^ 2 := by
    rw [hchiX, he]
    have hcast : ((2 * (i + 3 * j) : ℕ) : ℤ) =
        2 * ((i : ℤ) + 3 * (j : ℤ)) := by norm_num
    rw [← hcast, zpow_natCast]
    exact thetaExterior_chi_mod_six (chi D v (xC : F)) (chi D v (xN : F))
      hchiC6 hchiN6 i j hiNat
  have hlocalPow :
      localChi D v (unitPart v (toLoc v a)) ^ (2 * ordv v (toLoc v a)) =
        if i = 0 then 1 else chi D v (xC : F) ^ 2 := by
    rw [hlocal]
    exact hpow
  by_cases hdiv : v.asIdeal ∣ c
  · have hi : i = 1 := hdivCount hdiv
    rw [hlocalPow]
    simp [hi, hdiv, xC, π]
  · have hi : i = 0 := hnotdivCount hdiv
    rw [hlocalPow]
    simp [hi, hdiv]

private lemma thetaExterior_sphericalTable_local_factor
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (I c n : Ideal (𝓞 F)) (a cg ng ε : Fˣ)
    (hfactor : I = c * n ^ 3) (hA : S.IsGen (a : F) I)
    (hcg : S.IsGen (cg : F) c) (hng : S.IsGen (ng : F) n)
    (hε : ε ∈ S.US) (hdecomp : a = ε ^ 6 * (cg * ng ^ 3))
    (hsq : Squarefree c) (v : FinPlace F) (hv : v ∉ S.Sf) :
    sphericalTable D A v (ordv v (toLoc v a)) (unitPart v (toLoc v a)) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^
        (-(FractionalIdeal.count F v
          (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ) *
        (if v.asIdeal ∣ c then
          (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            g2 D A v * chi D v ((cg : F) / unif v) ^ 2
         else 1) := by
  classical
  let i : ℕ := (Associates.mk v.asIdeal).count (Associates.mk c).factors
  let j : ℕ := (Associates.mk v.asIdeal).count (Associates.mk n).factors
  let e : ℤ := ordv v (toLoc v a)
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hcountc : FractionalIdeal.count F v
      (c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (i : ℤ) := by
    rw [FractionalIdeal.count_coe F v hcg.1.1]
  have hcountn : FractionalIdeal.count F v
      (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (j : ℤ) := by
    rw [FractionalIdeal.count_coe F v hng.1.1]
  have hcountProd : FractionalIdeal.count F v
      ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (i : ℤ) + 3 * (j : ℤ) := by
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
      FractionalIdeal.count_mul F v
        (FractionalIdeal.coeIdeal_ne_zero.mpr hcg.1.1)
        (pow_ne_zero 3 (FractionalIdeal.coeIdeal_ne_zero.mpr hng.1.1)),
      FractionalIdeal.count_pow, hcountc, hcountn]
    ring
  have hcountA : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
      (i : ℤ) + 3 * (j : ℤ) := by
    calc
      _ = FractionalIdeal.count F v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hA.2.2 v hv
      _ = FractionalIdeal.count F v
          ((c * n ^ 3 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
            rw [hfactor]
      _ = _ := hcountProd
  have he : e = (i : ℤ) + 3 * (j : ℤ) := by
    dsimp [e]
    calc
      ordv v (toLoc v a) =
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) :=
        (thetaExterior_count_principal_eq_ordv v a).symm
      _ = _ := hcountA
  have hile : i ≤ 1 :=
    thetaExterior_count_le_one_of_squarefree v c hcg.1.1 hsq
  have hdivIff : v.asIdeal ∣ c ↔ i = 1 := by
    constructor
    · exact thetaExterior_count_eq_one_of_dvd_squarefree v c hcg.1.1 hsq
    · intro hi
      have hne : i ≠ 0 := by omega
      exact (Associates.count_ne_zero_iff_dvd hcg.1.1 v.irreducible).mp
        (by simpa [i] using hne)
  have heord : ordv v (toLoc v a) = (i : ℤ) + 3 * (j : ℤ) := by
    simpa [e] using he
  have hnonneg : ¬ ordv v (toLoc v a) < 0 := by
    rw [heord]
    omega
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.cast_pos.mpr
      (Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)
  have hsymbol := thetaExterior_localSymbol_factor D S I c n a cg ng ε
    hfactor hA hcg hng hε hdecomp hsq v hv
  by_cases hdiv : v.asIdeal ∣ c
  · have hi : i = 1 := hdivIff.mp hdiv
    have heval : ordv v (toLoc v a) = 3 * (j : ℤ) + 1 := by rw [heord, hi]; ring
    have hmod : ordv v (toLoc v a) % 3 = 1 := by rw [heval]; omega
    have hquot : ordv v (toLoc v a) / 3 = (j : ℤ) := by rw [heval]; omega
    have hqsplit : q ^ (-(j : ℝ) - 1 / 2) =
        q ^ (-(j : ℝ)) * q ^ (-(1 / 2 : ℝ)) := by
      rw [show -(j : ℝ) - (1 / 2 : ℝ) =
        (-(j : ℝ)) + (-(1 / 2 : ℝ)) by ring, Real.rpow_add hqpos]
    calc
      _ = (((q ^ (-(j : ℝ) - 1 / 2) : ℝ) : ℝ) : ℂ) *
            g2 D A v * chi D v ((cg : F) / unif v) ^ 2 := by
        simp [sphericalTable, q, hsymbol, hdiv, hnonneg, hmod, hquot] <;> ac_rfl
      _ = _ := by
        rw [hqsplit, Complex.ofReal_mul]
        simp [q, hcountn, hdiv] <;> ac_rfl
  · have hi : i = 0 := by
      by_contra hne
      have hone : i = 1 := by omega
      exact hdiv (hdivIff.mpr hone)
    have heval : ordv v (toLoc v a) = 3 * (j : ℤ) := by
      rw [heord, hi]
      simp
    have hmod : ordv v (toLoc v a) % 3 = 0 := by rw [heval]; omega
    have hquot : ordv v (toLoc v a) / 3 = (j : ℤ) := by rw [heval]; omega
    simpa [sphericalTable, q, hsymbol, hdiv, hnonneg, hmod, hquot, hi, hcountn]

private lemma thetaExterior_gamma_finset
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) (T : Finset (FinPlace F)) :
    ∀ (hT : ∀ v ∈ T, v ∉ S.Sf),
    ∀ cg : Fˣ,
      S.IsGen (cg : F) (∏ v ∈ T, v.asIdeal) ∧ Bd.Allowed cg →
      gamma D S A 2 (∏ v ∈ T, v.asIdeal) (cg : F) =
        ∏ v ∈ T, g2 D A v * chi D v ((cg : F) / unif v) ^ 2 := by
  classical
  intro hT
  revert hT
  induction T using Finset.induction_on with
  | empty =>
      intro hT cg hcg
      simp only [Finset.prod_empty] at hcg ⊢
      letI : Unique (𝓞 F ⧸ (1 : Ideal (𝓞 F))) := by
        rw [Ideal.one_eq_top]
        infer_instance
      let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
      let f : (𝓞 F ⧸ (1 : Ideal (𝓞 F))) → ℂ := fun x =>
        chiIdealPow D ⊤ (algebraMap (𝓞 F) F x.out) 2 *
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) / (cg : F)))
      let x0 : 𝓞 F := Quotient.out (0 : 𝓞 F ⧸ (1 : Ideal (𝓞 F)))
      let z0 : F := (algebraMap (𝓞 F) F x0) / (cg : F)
      have htopne : (1 : Ideal (𝓞 F)) ≠ ⊥ := by simp
      have hfzero : f 0 = 1 := by
        have hχ0 : chiIdealPow D ⊤ (algebraMap (𝓞 F) F x0) 2 = 1 :=
          SB.ideal_one _ _
        have hout : ∀ w : FinPlace F, w ∉ S.Sf →
            HeightOneSpectrum.valuation F w z0 ≤ 1 := by
          intro w hw
          have hcountTop : FractionalIdeal.count F w
              ((1 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
            simpa using FractionalIdeal.count_one F w
          have hvalCg : HeightOneSpectrum.valuation F w (cg : F) = 1 := by
            have hval := thetaExterior_genVal S (1 : Ideal (𝓞 F)) cg hcg.1 w hw
            rw [hcountTop] at hval
            simpa using hval
          have hvalNum : HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x0) ≤ 1 :=
            w.valuation_le_one x0
          change HeightOneSpectrum.valuation F w
            ((algebraMap (𝓞 F) F x0) / (cg : F)) ≤ 1
          rw [map_div₀, hvalCg, div_one]
          exact hvalNum
        have he := thetaExterior_e_integralOutside D S A z0 hout
        change chiIdealPow D ⊤ (algebraMap (𝓞 F) F x0) 2 *
          S.e A (S.diag z0) = 1
        rw [hχ0, one_mul]
        exact he
      have hf : ∀ x : 𝓞 F ⧸ (1 : Ideal (𝓞 F)), f x = 1 := by
        intro x
        rw [Subsingleton.elim x 0]
        exact hfzero
      have hsum : (∑ᶠ x : 𝓞 F ⧸ (1 : Ideal (𝓞 F)), f x) = 1 := by
        rw [finsum_eq_single f 0 (fun x hx => False.elim (hx (Subsingleton.elim x 0)))]
        exact hfzero
      simpa [gamma, Ideal.one_eq_top, hsum, f]
  | @insert v T hv ih =>
      intro hT cg hcg
      have hTrest : ∀ w ∈ T, w ∉ S.Sf := by
        intro w hw
        exact hT w (by simp [hw])
      have hvT : ∀ w ∈ T, v ≠ w := by
        intro w hw heq
        subst w
        exact hv hw
      let P : Ideal (𝓞 F) := v.asIdeal
      let J : Ideal (𝓞 F) := ∏ w ∈ T, w.asIdeal
      have hfactor : (∏ w ∈ insert v T, w.asIdeal) = P * J := by
        simp [P, J, Finset.prod_insert, hv]
      have hJne : J ≠ ⊥ := by
        exact thetaExterior_prod_primes_ne_bot T
      have hJext : S.IsExterior J := by
        refine ⟨hJne, ?_⟩
        intro w hwS hle
        apply hcg.1.1.2 w hwS
        rw [hfactor]
        exact le_trans (Ideal.mul_le_right (I := P) (J := J)) hle
      have hPext : S.IsExterior P := by
        refine ⟨v.ne_bot, ?_⟩
        intro w hwS hle
        have heq : P = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
        have hplaces : v = w := HeightOneSpectrum.ext heq
        exact (hT v (by simp)) (hplaces ▸ hwS)
      have hpairCop : (T : Set (FinPlace F)).Pairwise
          (fun w z => IsCoprime w.asIdeal z.asIdeal) :=
        thetaExterior_pairwise_coprime T
      have hpairRel : (T : Set (FinPlace F)).Pairwise
          (fun w z => IsRelPrime w.asIdeal z.asIdeal) := by
        intro w hw z hz hwz
        exact (hpairCop hw hz hwz).isRelPrime
      have hsqJ : Squarefree J := by
        change Squarefree (∏ w ∈ T, w.asIdeal)
        refine Finset.squarefree_prod_of_pairwise_isCoprime hpairRel ?_
        intro w hw
        exact (irreducible_iff_prime.mp w.irreducible).squarefree
      have hcop : IsCoprime P J := by
        change IsCoprime P (∏ w ∈ T, w.asIdeal)
        exact IsCoprime.prod_right fun w hw => by
          have hneq : P ≠ w.asIdeal := by
            intro heq
            have hplaces : v = w := HeightOneSpectrum.ext heq
            exact hv (hplaces ▸ hw)
          letI := v.isMaximal
          letI := w.isMaximal
          exact Ideal.isCoprime_of_isMaximal hneq
      obtain ⟨p, hpgen, hpallow⟩ := Bd.exists_allowed P hPext
      let d : Fˣ := cg / p
      have hpd : p * d = cg := by
        simp [d]
      have hdgen : S.IsGen (d : F) J := by
        refine ⟨hJext, Units.ne_zero d, ?_⟩
        intro w hwS
        have hcountProd : FractionalIdeal.count F w
            ((P * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
            FractionalIdeal.count F w
              (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
            FractionalIdeal.count F w
              (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [FractionalIdeal.coeIdeal_mul,
            FractionalIdeal.count_mul F w
              (FractionalIdeal.coeIdeal_ne_zero.mpr hPext.1)
              (FractionalIdeal.coeIdeal_ne_zero.mpr hJext.1)]
        have hcountProdInsert : FractionalIdeal.count F w
            ((∏ z ∈ insert v T, z.asIdeal : Ideal (𝓞 F)) :
              FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
            FractionalIdeal.count F w
              (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
            FractionalIdeal.count F w
              (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [hfactor]
          exact hcountProd
        have hdiv := thetaExterior_count_spanSingleton_div w (cg : F) (p : F)
          (Units.ne_zero cg) (Units.ne_zero p)
        calc
          FractionalIdeal.count F w
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (d : F)) =
              FractionalIdeal.count F w
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (cg : F)) -
              FractionalIdeal.count F w
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) := by
                  simpa [d] using hdiv
          _ = FractionalIdeal.count F w
              (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
                rw [hcg.1.2.2 w hwS, hpgen.2.2 w hwS]
                rw [hcountProdInsert]
                ring
      have hdallow : Bd.Allowed d := by
        change (QuotientGroup.mk (S.diagU d) : S.V) ∈ Bd.B
        rw [map_div]
        exact Bd.B.div_mem hcg.2 hpallow
      have hcrt := gamma_crt D S A H Bd 2 P J hPext hJext
        (irreducible_iff_prime.mp v.irreducible).squarefree hsqJ hcop p d
        ⟨hpgen, hpallow⟩ ⟨hdgen, hdallow⟩
      have hrec := ih hTrest d ⟨hdgen, hdallow⟩
      have hprime := thetaExterior_gammaPrime D S A v (hT v (by simp)) p hpgen
      have hcountJv : FractionalIdeal.count F v
          (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        have hnotdiv : ¬ v.asIdeal ∣ J := by
          intro hdiv
          have hle : J ≤ P := Ideal.dvd_iff_le.mp hdiv
          have htop : P ⊔ J = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hcop
          have htop' : P ⊔ J = P := sup_eq_left.mpr hle
          rw [htop'] at htop
          exact v.isPrime.ne_top htop
        have hcount :
            (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 := by
          by_contra hne
          exact hnotdiv ((Associates.count_ne_zero_iff_dvd hJne v.irreducible).mp hne)
        rw [FractionalIdeal.count_coe F v hJne]
        exact_mod_cast hcount
      have hvaldV : HeightOneSpectrum.valuation F v (d : F) = 1 := by
        have h := thetaExterior_genVal S J d hdgen v (hT v (by simp))
        rw [hcountJv] at h
        simpa using h
      have hvalpV : HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (-1 : ℤ) := by
        have h := thetaExterior_genVal S P p hpgen v (hT v (by simp))
        rw [FractionalIdeal.count_self F v] at h
        exact h
      have hvalpW (w : FinPlace F) (hw : w ∈ T) :
          HeightOneSpectrum.valuation F w (p : F) = 1 := by
        have hcount := thetaExterior_count_prime_zero v w (hvT w hw)
        have h := thetaExterior_genVal S P p hpgen w (hT w (by simp [hw]))
        rw [hcount] at h
        simpa using h
      have hvaldW (w : FinPlace F) (hw : w ∈ T) :
          HeightOneSpectrum.valuation F w (d : F) = WithZero.exp (-1 : ℤ) := by
        have hdivw := thetaExterior_prime_dvd_prod T w hw
        have hcountAssoc := thetaExterior_count_eq_one_of_dvd_squarefree
          w J hJext.1 hsqJ hdivw
        have hcount : FractionalIdeal.count F w
            (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 := by
          rw [FractionalIdeal.count_coe F w hJext.1]
          exact_mod_cast hcountAssoc
        have h := thetaExterior_genVal S J d hdgen w (hT w (by simp [hw]))
        rw [hcount] at h
        exact h
      have hchiV : chi D v ((cg : F) / unif v) =
          chi D v ((p : F) / unif v) * chi D v (d : F) := by
        have harg : (cg : F) / unif v = ((p : F) / unif v) * (d : F) := by
          rw [← hpd]
          simp only [Units.val_mul]
          field_simp [unif_ne_zero v]
          <;> ring
        rw [harg]
        exact (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).chi_mul v
          (hT v (by simp)) ((p : F) / unif v) (d : F)
          (by
            rw [map_div₀, hvalpV, thetaExterior_val_unif]
            simp)
          hvaldV.le
      have hchiW (w : FinPlace F) (hw : w ∈ T) :
          chi D w ((cg : F) / unif w) =
            chi D w (p : F) * chi D w ((d : F) / unif w) := by
        have harg : (cg : F) / unif w = (p : F) * ((d : F) / unif w) := by
          rw [← hpd]
          simp only [Units.val_mul]
          field_simp [unif_ne_zero w]
          <;> ring
        rw [harg]
        exact (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).chi_mul w
          (hT w (by simp [hw])) (p : F) ((d : F) / unif w)
          (hvalpW w hw).le
          (by
            rw [map_div₀, hvaldW w hw, thetaExterior_val_unif]
            simp)
      have hchiVpow : chi D v ((cg : F) / unif v) ^ 2 =
          chi D v ((p : F) / unif v) ^ 2 * chi D v (d : F) ^ 2 := by
        rw [hchiV, mul_pow]
      have hchiWpow (w : FinPlace F) (hw : w ∈ T) :
          chi D w ((cg : F) / unif w) ^ 2 =
            chi D w (p : F) ^ 2 * chi D w ((d : F) / unif w) ^ 2 := by
        rw [hchiW w hw, mul_pow]
      have hrest :
          (∏ w ∈ T, chiPow D w (p : F) 2) *
            (∏ w ∈ T, g2 D A w * chi D w ((d : F) / unif w) ^ 2) =
          ∏ w ∈ T, g2 D A w * chi D w ((cg : F) / unif w) ^ 2 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro w hw
        simp [hchiWpow w hw, chiPow,
          thetaExterior_residueNeZeroOfValOne w (p : F) (hvalpW w hw)]
        ring
      have hpdVal : ((p * d : Fˣ) : F) = (cg : F) :=
        congrArg (fun u : Fˣ => (u : F)) hpd
      calc
        gamma D S A 2 (∏ w ∈ insert v T, w.asIdeal) (cg : F) =
            gamma D S A 2 (P * J) (cg : F) := by rw [hfactor]
        _ = gamma D S A 2 (P * J) ((p * d : Fˣ) : F) := by rw [← hpdVal]
        _ =
            chiIdealPow D P (d : F) 2 * chiIdealPow D J (p : F) 2 *
              gamma D S A 2 P (p : F) * gamma D S A 2 J (d : F) := hcrt
        _ = (g2 D A v * chi D v ((cg : F) / unif v) ^ 2) *
              ∏ w ∈ T, g2 D A w * chi D w ((cg : F) / unif w) ^ 2 := by
          rw [thetaExterior_chiIdealPow_prime D v (d : F) 2,
            thetaExterior_chiIdealPow_prod_primes D S T (p : F) 2,
            hprime, hrec]
          have hchiPowV : chiPow D v (d : F) 2 = chi D v (d : F) ^ 2 := by
            simp [chiPow, thetaExterior_residueNeZeroOfValOne v (d : F) hvaldV]
          rw [hchiPowV]
          calc
            _ = (chi D v (d : F) ^ 2 *
                (chi D v ((p : F) / unif v) ^ 2 * g2 D A v)) *
                ((∏ w ∈ T, chiPow D w (p : F) 2) *
                  ∏ w ∈ T, g2 D A w * chi D w ((d : F) / unif w) ^ 2) := by ac_rfl
            _ = _ := by
              rw [hrest]
              calc
                _ = (g2 D A v *
                    (∏ w ∈ T, g2 D A w * chi D w ((cg : F) / unif w) ^ 2)) *
                    (chi D v ((p : F) / unif v) ^ 2 * chi D v (d : F) ^ 2) := by ac_rfl
                _ = _ := by rw [hchiVpow]; ac_rfl
        _ = ∏ w ∈ insert v T, g2 D A w * chi D w ((cg : F) / unif w) ^ 2 := by
          rw [Finset.prod_insert hv]

private lemma thetaExterior_squarefree_factorization
    (S : SData F CE condη) (I : Ideal (𝓞 F)) (hI : S.IsExterior I)
    (hsq : Squarefree I) :
    ∃ T : Finset (FinPlace F),
      I = ∏ v ∈ T, v.asIdeal ∧
        (∀ v : FinPlace F, v.asIdeal ∣ I ↔ v ∈ T) ∧
        ∀ v ∈ T, v ∉ S.Sf := by
  classical
  have hIne : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI.1
  let T : Finset (FinPlace F) := (Ideal.finite_factors hIne).toFinset
  have hsupport : Function.mulSupport (fun v : FinPlace F => v.maxPowDividing I) ⊆
      {v : FinPlace F | v.asIdeal ∣ I} := by
    intro v hv
    by_contra hdiv
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra hne
      exact hdiv ((Associates.count_ne_zero_iff_dvd hIne v.irreducible).mp hne)
    have hmax : v.maxPowDividing I = 1 := by
      simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
    exact (Function.mem_mulSupport.mp hv) hmax
  have hfinprod : (∏ᶠ v : FinPlace F, v.maxPowDividing I) =
      ∏ v ∈ T, v.maxPowDividing I := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsupport
      (Ideal.finite_factors hIne)]
  have hfactor : I = ∏ v ∈ T, v.asIdeal := by
    calc
      I = ∏ᶠ v : FinPlace F, v.maxPowDividing I :=
        (Ideal.finprod_heightOneSpectrum_factorization hIne).symm
      _ = ∏ v ∈ T, v.maxPowDividing I := hfinprod
      _ = ∏ v ∈ T, v.asIdeal := by
        refine Finset.prod_congr rfl ?_
        intro v hvT
        have hdiv : v.asIdeal ∣ I :=
          (Ideal.finite_factors hIne).mem_toFinset.mp (by simpa [T] using hvT)
        have hcount := thetaExterior_count_eq_one_of_dvd_squarefree v I hIne hsq hdiv
        simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
  refine ⟨T, hfactor, ?_, ?_⟩
  · intro v
    constructor
    · intro hdiv
      exact (Ideal.finite_factors hIne).mem_toFinset.mpr hdiv
    · intro hmem
      exact (Ideal.finite_factors hIne).mem_toFinset.mp (by simpa [T] using hmem)
  · intro v hvT hvS
    have hdiv : v.asIdeal ∣ I :=
      (Ideal.finite_factors hIne).mem_toFinset.mp (by simpa [T] using hvT)
    exact hI.2 v hvS (Ideal.dvd_iff_le.mp hdiv)

private lemma thetaExterior_primePower_factorization
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∃ T : Finset (FinPlace F),
      I = ∏ v ∈ T, v.asIdeal ^
        (Associates.mk v.asIdeal).count (Associates.mk I).factors ∧
      (∀ v : FinPlace F, v.asIdeal ∣ I ↔ v ∈ T) := by
  classical
  let T : Finset (FinPlace F) := (Ideal.finite_factors hI).toFinset
  have hsupport : Function.mulSupport (fun v : FinPlace F => v.maxPowDividing I) ⊆
      {v : FinPlace F | v.asIdeal ∣ I} := by
    intro v hv
    by_contra hdiv
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra hne
      exact hdiv ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hne)
    have hmax : v.maxPowDividing I = 1 := by
      simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
    exact (Function.mem_mulSupport.mp hv) hmax
  have hfinprod : (∏ᶠ v : FinPlace F, v.maxPowDividing I) =
      ∏ v ∈ T, v.maxPowDividing I := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsupport
      (Ideal.finite_factors hI)]
  refine ⟨T, ?_, ?_⟩
  · calc
      I = ∏ᶠ v : FinPlace F, v.maxPowDividing I :=
        (Ideal.finprod_heightOneSpectrum_factorization hI).symm
      _ = ∏ v ∈ T, v.maxPowDividing I := hfinprod
      _ = ∏ v ∈ T, v.asIdeal ^
          (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
        rfl
  · intro v
    constructor
    · intro hdiv
      exact (Ideal.finite_factors hI).mem_toFinset.mpr hdiv
    · intro hmem
      exact (Ideal.finite_factors hI).mem_toFinset.mp (by simpa [T] using hmem)

private lemma thetaExterior_absNorm_primePower_factorization
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∃ T : Finset (FinPlace F),
      I = ∏ v ∈ T, v.asIdeal ^
        (Associates.mk v.asIdeal).count (Associates.mk I).factors ∧
      (∀ v : FinPlace F, v.asIdeal ∣ I ↔ v ∈ T) ∧
      (Ideal.absNorm I : ℝ) =
        ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^
          (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  obtain ⟨T, hT, hmem⟩ := thetaExterior_primePower_factorization I hI
  refine ⟨T, hT, hmem, ?_⟩
  have hN : Ideal.absNorm I = ∏ v ∈ T,
      Ideal.absNorm v.asIdeal ^
        (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    simpa only [map_prod, map_pow] using congrArg Ideal.absNorm hT
  exact_mod_cast hN

private def thetaExterior_placeFinset (S : SData F CE condη)
    (T : Finset (FinPlace F)) (hT : ∀ v ∈ T, v ∉ S.Sf) :
    Finset {v : FinPlace F // v ∉ S.Sf} :=
  T.attach.map ⟨(fun v => ⟨v.1, hT v.1 v.2⟩), by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg (fun z : {v : FinPlace F // v ∉ S.Sf} => z.1) hxy⟩

private lemma thetaExterior_prod_placeFinset (S : SData F CE condη)
    (T : Finset (FinPlace F)) (hT : ∀ v ∈ T, v ∉ S.Sf) (f : FinPlace F → ℂ) :
    ∏ v ∈ thetaExterior_placeFinset S T hT, f v.1 = ∏ v ∈ T, f v := by
  classical
  let e : {w // w ∈ T} ↪ {v : FinPlace F // v ∉ S.Sf} :=
    ⟨fun w => ⟨w.1, hT w.1 w.2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : {v : FinPlace F // v ∉ S.Sf} => z.1) hxy⟩
  change (∏ v ∈ T.attach.map e, f v.1) = ∏ v ∈ T, f v
  rw [Finset.prod_map]
  calc
    (∏ w ∈ T.attach, f (e w).1) = ∏ w ∈ T.attach, f w.1 := by
      apply Finset.prod_congr rfl
      intro w hw
      rfl
    _ = ∏ w ∈ T, f w := Finset.prod_attach T f

private lemma thetaExterior_mem_placeFinset (S : SData F CE condη)
    (T : Finset (FinPlace F)) (hT : ∀ v ∈ T, v ∉ S.Sf)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    (⟨v, hv⟩ : {v : FinPlace F // v ∉ S.Sf}) ∈ thetaExterior_placeFinset S T hT ↔ v ∈ T := by
  classical
  unfold thetaExterior_placeFinset
  constructor
  · intro hmem
    rcases Finset.mem_map.mp hmem with ⟨w, hw, heq⟩
    have hval : w.1 = v := congrArg (fun z : {v : FinPlace F // v ∉ S.Sf} => z.1) heq
    simpa [hval] using w.2
  · intro hvT
    apply Finset.mem_map.mpr
    refine ⟨⟨v, hvT⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

private lemma thetaExterior_nNorm_finprod (S : SData F CE condη)
    (n : Ideal (𝓞 F)) (hn : S.IsExterior n) :
    (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf},
      (((Ideal.absNorm v.1.asIdeal : ℝ) ^
        (-(FractionalIdeal.count F v.1
          (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ)) =
      (((Ideal.absNorm n : ℝ)⁻¹ : ℝ) : ℂ) := by
  classical
  obtain ⟨T, hfactor, hmem, hnorm⟩ :=
    thetaExterior_absNorm_primePower_factorization n hn.1
  have hT : ∀ v ∈ T, v ∉ S.Sf := by
    intro v hvT hvS
    apply hn.2 v hvS
    exact Ideal.dvd_iff_le.mp ((hmem v).2 hvT)
  let U := thetaExterior_placeFinset S T hT
  let fN : {v : FinPlace F // v ∉ S.Sf} → ℂ := fun w =>
    (((Ideal.absNorm w.1.asIdeal : ℝ) ^
      (-(FractionalIdeal.count F w.1
        (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ)
  have hsub : Function.mulSupport fN ⊆ (U : Set {v : FinPlace F // v ∉ S.Sf}) := by
    intro w hw
    have hdiv : w.1.asIdeal ∣ n := by
      by_contra hnotdiv
      have hcountAssoc : (Associates.mk w.1.asIdeal).count
          (Associates.mk n).factors = 0 := by
        by_contra hne
        exact hnotdiv ((Associates.count_ne_zero_iff_dvd hn.1 w.1.irreducible).mp hne)
      have hcount : FractionalIdeal.count F w.1
          (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        rw [FractionalIdeal.count_coe F w.1 hn.1]
        exact_mod_cast hcountAssoc
      have hone : fN w = 1 := by
        simp [fN, hcount]
      exact (Function.mem_mulSupport.mp hw) hone
    exact (thetaExterior_mem_placeFinset S T hT w.1 w.2).2 ((hmem w.1).mp hdiv)
  have hprod : (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fN w) =
      ∏ w ∈ U, fN w := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsub U.finite_toSet]
    simp
  let gN : FinPlace F → ℂ := fun v =>
    (((Ideal.absNorm v.asIdeal : ℝ) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk n).factors : ℝ)) : ℝ) : ℂ)
  have hmap : (∏ w ∈ U, fN w) = ∏ v ∈ T, gN v := by
    calc
      _ = ∏ w ∈ U, gN w.1 := by
        refine Finset.prod_congr rfl ?_
        intro w hw
        have hcount : FractionalIdeal.count F w.1
            (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
              ((Associates.mk w.1.asIdeal).count (Associates.mk n).factors : ℤ) := by
          rw [FractionalIdeal.count_coe F w.1 hn.1]
        simp [fN, gN, hcount]
      _ = ∏ v ∈ T, gN v := thetaExterior_prod_placeFinset S T hT gN
  have hnormReal :
      (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^
        (-((Associates.mk v.asIdeal).count (Associates.mk n).factors : ℝ))) =
        (Ideal.absNorm n : ℝ)⁻¹ := by
    calc
      _ = ∏ v ∈ T,
          (((Ideal.absNorm v.asIdeal : ℝ) ^
            ((Associates.mk v.asIdeal).count (Associates.mk n).factors : ℝ))⁻¹) := by
        refine Finset.prod_congr rfl ?_
        intro v hvT
        have hpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) :=
          Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors
            ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)
        rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
      _ = (∏ v ∈ T,
            (Ideal.absNorm v.asIdeal : ℝ) ^
              (Associates.mk v.asIdeal).count (Associates.mk n).factors)⁻¹ := by
        rw [Finset.prod_inv_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro v hvT
        rw [Real.rpow_natCast]
      _ = (Ideal.absNorm n : ℝ)⁻¹ := by rw [← hnorm]
  calc
    _ = ∏ v ∈ T, gN v := hprod.trans hmap
    _ = (((∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^
          (-((Associates.mk v.asIdeal).count (Associates.mk n).factors : ℝ))) : ℝ) : ℂ) := by
        simp only [gN, Complex.ofReal_prod]
    _ = (((Ideal.absNorm n : ℝ)⁻¹ : ℝ) : ℂ) := by rw [hnormReal]

private lemma thetaExterior_nNorm_finite (S : SData F CE condη)
    (n : Ideal (𝓞 F)) (hn : S.IsExterior n) :
    Function.HasFiniteMulSupport (fun w : {v : FinPlace F // v ∉ S.Sf} =>
      (((Ideal.absNorm w.1.asIdeal : ℝ) ^
        (-(FractionalIdeal.count F w.1
          (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ)) := by
  classical
  let fN : {v : FinPlace F // v ∉ S.Sf} → ℂ := fun w =>
    (((Ideal.absNorm w.1.asIdeal : ℝ) ^
      (-(FractionalIdeal.count F w.1
        (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ)
  have hdivFinite : {w : {v : FinPlace F // v ∉ S.Sf} | w.1.asIdeal ∣ n}.Finite :=
    Set.Finite.preimage
      (f := Subtype.val)
      (by
        intro x _ y _ hxy
        exact Subtype.ext hxy)
      (Ideal.finite_factors hn.1)
  have hsub : Function.mulSupport fN ⊆
      {w : {v : FinPlace F // v ∉ S.Sf} | w.1.asIdeal ∣ n} := by
    intro w hw
    by_contra hnotdiv
    have hcountAssoc : (Associates.mk w.1.asIdeal).count
        (Associates.mk n).factors = 0 := by
      by_contra hne
      exact hnotdiv ((Associates.count_ne_zero_iff_dvd hn.1 w.1.irreducible).mp hne)
    have hcount : FractionalIdeal.count F w.1
        (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      rw [FractionalIdeal.count_coe F w.1 hn.1]
      exact_mod_cast hcountAssoc
    have hone : fN w = 1 := by simp [fN, hcount]
    exact (Function.mem_mulSupport.mp hw) hone
  change (Function.mulSupport fN).Finite
  exact Set.Finite.subset hdivFinite hsub

private lemma thetaExterior_finset_rpow_prod {α : Type*}
    (T : Finset α) (q : α → ℝ) (r : ℝ) (hq : ∀ v ∈ T, 0 < q v) :
    ∏ v ∈ T, q v ^ r = (∏ v ∈ T, q v) ^ r := by
  classical
  revert hq
  induction T using Finset.induction_on with
  | empty => intro hq; simp
  | @insert v T hv ih =>
      intro hq
      have hqv : 0 < q v := hq v (by simp)
      have hqT : ∀ w ∈ T, 0 < q w := by
        intro w hw
        exact hq w (by simp [hw])
      have hprodT : 0 < ∏ w ∈ T, q w := Finset.prod_pos hqT
      calc
        ∏ w ∈ insert v T, q w ^ r = q v ^ r * ∏ w ∈ T, q w ^ r :=
          Finset.prod_insert hv
        _ = q v ^ r * (∏ w ∈ T, q w) ^ r := by rw [ih hqT]
        _ = (q v * ∏ w ∈ T, q w) ^ r :=
          (Real.mul_rpow hqv.le hprodT.le).symm
        _ = (∏ w ∈ insert v T, q w) ^ r := by rw [Finset.prod_insert hv]

private lemma thetaExterior_cubeDecomp_of_no_residue_two
    (S : SData F CE condη) (I : Ideal (𝓞 F)) (hI : S.IsExterior I)
    (hres : ∀ v : FinPlace F, v ∉ S.Sf →
      (Associates.mk v.asIdeal).count (Associates.mk I).factors % 3 ≠ 2) :
    ∃ c n : Ideal (𝓞 F), Squarefree c ∧ I = c * n ^ 3 := by
  classical
  have hIne : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI.1
  let T : Finset (FinPlace F) := (Ideal.finite_factors hIne).toFinset
  let exp (v : FinPlace F) : ℕ :=
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  let c : Ideal (𝓞 F) := ∏ v ∈ T, (if exp v % 3 = 1 then v.asIdeal else ⊤)
  let n : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ (exp v / 3)
  have hresAll (v : FinPlace F) : exp v % 3 ≠ 2 := by
    by_cases hv : v ∈ S.Sf
    · have hnotdiv : ¬ v.asIdeal ∣ I := by
        rw [Ideal.dvd_iff_le]
        exact hI.2 v hv
      have hz : exp v = 0 := by
        by_contra hne
        exact hnotdiv
          ((Associates.count_ne_zero_iff_dvd hIne v.irreducible).mp (by simpa [exp] using hne))
      simp [exp, hz]
    · exact hres v hv
  have hfinSupport : Function.mulSupport (fun v : FinPlace F => v.asIdeal ^ exp v) ⊆
      {v : FinPlace F | v.asIdeal ∣ I} := by
    intro v hv
    have hz : exp v ≠ 0 := by
      intro hz
      simp [hz] at hv
    exact (Associates.count_ne_zero_iff_dvd hIne v.irreducible).mp (by simpa [exp] using hz)
  have hfac : (∏ᶠ v : FinPlace F, v.asIdeal ^ exp v) =
      ∏ v ∈ T, v.asIdeal ^ exp v := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hfinSupport
      (Ideal.finite_factors hIne)]
  have hIprod : I = ∏ v ∈ T, v.asIdeal ^ exp v := by
    calc
      I = ∏ᶠ v : FinPlace F, v.maxPowDividing I :=
        (Ideal.finprod_heightOneSpectrum_factorization hIne).symm
      _ = ∏ᶠ v : FinPlace F, v.asIdeal ^ exp v := by
        rfl
      _ = ∏ v ∈ T, v.asIdeal ^ exp v := hfac
  have hpoint (v : FinPlace F) (hv : v ∈ T) :
      v.asIdeal ^ exp v = (if exp v % 3 = 1 then v.asIdeal else ⊤) *
        (v.asIdeal ^ (exp v / 3)) ^ 3 := by
    have hm := hresAll v
    have hcases : exp v % 3 = 0 ∨ exp v % 3 = 1 := by omega
    rcases hcases with hzero | hone
    · calc
        v.asIdeal ^ exp v = v.asIdeal ^ ((exp v / 3) * 3) :=
          congrArg (fun k : ℕ => v.asIdeal ^ k) (by omega)
        _ = (v.asIdeal ^ (exp v / 3)) ^ 3 := by rw [pow_mul]
        _ = (if exp v % 3 = 1 then v.asIdeal else ⊤) *
              (v.asIdeal ^ (exp v / 3)) ^ 3 := by simp [hzero, Ideal.one_eq_top]
    · calc
        v.asIdeal ^ exp v = v.asIdeal ^ ((exp v / 3) * 3 + 1) :=
          congrArg (fun k : ℕ => v.asIdeal ^ k) (by omega)
        _ = v.asIdeal ^ ((exp v / 3) * 3) * v.asIdeal ^ 1 := by rw [pow_add]
        _ = (v.asIdeal ^ (exp v / 3)) ^ 3 * v.asIdeal ^ 1 := by rw [pow_mul]
        _ = v.asIdeal * (v.asIdeal ^ (exp v / 3)) ^ 3 := by rw [pow_one, mul_comm]
        _ = (if exp v % 3 = 1 then v.asIdeal else ⊤) *
              (v.asIdeal ^ (exp v / 3)) ^ 3 := by simp [hone]
  have hprodpoint : (∏ v ∈ T, v.asIdeal ^ exp v) = c * n ^ 3 := by
    change (∏ v ∈ T, v.asIdeal ^ exp v) =
      (∏ v ∈ T, (if exp v % 3 = 1 then v.asIdeal else ⊤)) *
        (∏ v ∈ T, v.asIdeal ^ (exp v / 3)) ^ 3
    calc
      (∏ v ∈ T, v.asIdeal ^ exp v) =
          ∏ v ∈ T, (if exp v % 3 = 1 then v.asIdeal else ⊤) *
            (v.asIdeal ^ (exp v / 3)) ^ 3 := by
        refine Finset.prod_congr rfl ?_
        intro v hv
        exact hpoint v hv
      _ = (∏ v ∈ T, (if exp v % 3 = 1 then v.asIdeal else ⊤)) *
            (∏ v ∈ T, v.asIdeal ^ (exp v / 3)) ^ 3 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hsq : Squarefree c := by
    rw [show c = ∏ v ∈ T, (if exp v % 3 = 1 then v.asIdeal else ⊤) by rfl]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro v hv w hw hvw
      change IsRelPrime (if exp v % 3 = 1 then v.asIdeal else ⊤)
        (if exp w % 3 = 1 then w.asIdeal else ⊤)
      have htop : IsUnit (⊤ : Ideal (𝓞 F)) := by
        simpa [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 F)))
      by_cases hvc : exp v % 3 = 1
      · by_cases hwc : exp w % 3 = 1
        · have hvm : v.asIdeal.IsMaximal := v.isMaximal
          have hwm : w.asIdeal.IsMaximal := w.isMaximal
          have hne : v.asIdeal ≠ w.asIdeal := by
            intro heq
            exact hvw (HeightOneSpectrum.ext heq)
          letI := hvm
          letI := hwm
          simpa [hvc, hwc] using (Ideal.isCoprime_of_isMaximal hne).isRelPrime
        · simpa [hvc, hwc] using htop.isRelPrime_right
      · simpa [hvc] using htop.isRelPrime_left
    · intro v hv
      by_cases hvmod : exp v % 3 = 1
      · simpa [hvmod] using (irreducible_iff_prime.mp v.irreducible).squarefree
      · simp [hvmod]
  exact ⟨c, n, hsq, hIprod.trans hprodpoint⟩

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
  classical
  have hfinite : (Function.mulSupport fun v : {v : FinPlace F // v ∉ S.Sf} =>
      sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a))
        (unitPart v.1 (toLoc v.1 a))).Finite := by
    have hdivFinite : {v : {v : FinPlace F // v ∉ S.Sf} | v.1.asIdeal ∣ 𝔄}.Finite :=
      Set.Finite.preimage (f := Subtype.val)
        (by
          intro x hx y hy hxy
          exact Subtype.ext hxy)
        (Ideal.finite_factors ha.1.1.1)
    have hsub : Function.mulSupport (fun v : {v : FinPlace F // v ∉ S.Sf} =>
        sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a))
          (unitPart v.1 (toLoc v.1 a))) ⊆
        {v : {v : FinPlace F // v ∉ S.Sf} | v.1.asIdeal ∣ 𝔄} := by
      intro v hv
      by_contra hvnot
      have hnotdiv : ¬ v.1.asIdeal ∣ 𝔄 := by
        intro hdiv
        apply hvnot
        exact hdiv
      have hval : ¬ 𝔄 ≤ v.1.asIdeal := by
        intro hle
        exact hnotdiv (Ideal.dvd_iff_le.mpr hle)
      have hcountA : FractionalIdeal.count F v.1
          (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        rw [FractionalIdeal.count_coe F v.1 ha.1.1.1]
        have hfac : (Associates.mk v.1.asIdeal).count
            (Associates.mk 𝔄).factors = 0 := by
          by_contra hne
          have hdvd := (Associates.count_ne_zero_iff_dvd ha.1.1.1 v.1.irreducible).mp hne
          rw [Ideal.dvd_iff_le] at hdvd
          exact hval hdvd
        exact_mod_cast hfac
      have hcounta := ha.1.2.2 v.1 v.2
      have he : ordv v.1 (toLoc v.1 a) = 0 := by
        rw [← thetaExterior_count_principal_eq_ordv v.1 a, hcounta, hcountA]
      have htable : sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a))
          (unitPart v.1 (toLoc v.1 a)) = 1 := by
        rw [he]
        simp [sphericalTable]
      exact (Function.mem_mulSupport.mp hv) htable
    exact Set.Finite.subset hdivFinite hsub
  refine ⟨hfinite, ?_⟩
  constructor
  · intro c n cg hsq hfactor hcg
    have hcnext : S.IsExterior c ∧ S.IsExterior n :=
      thetaExterior_cubeFactorsExterior 𝔄 c n h𝔄 hfactor
    have hAext : S.IsExterior (c * n ^ 3) := by
      rw [← hfactor]
      exact h𝔄
    obtain ⟨ng, hnggen, hngAllowed⟩ := Bd.exists_allowed n hcnext.2
    have hprodGen : S.IsGen ((cg * ng ^ 3 : Fˣ) : F) (c * n ^ 3) :=
      thetaExterior_gen_mul_cube c n cg ng hAext hcg.1 hnggen
    have hprodGen' : S.IsGen ((cg * ng ^ 3 : Fˣ) : F) 𝔄 := by
      rw [hfactor]
      exact hprodGen
    have hprodAllowed : Bd.Allowed (cg * ng ^ 3) :=
      thetaExterior_allowed_mul_cube Bd cg ng hcg.2 hngAllowed
    obtain ⟨ε, hε, haeq⟩ :=
      Bd.allowed_unique 𝔄 a (cg * ng ^ 3) ha ⟨hprodGen', hprodAllowed⟩
    let fN : {v : FinPlace F // v ∉ S.Sf} → ℂ := fun w =>
      (((Ideal.absNorm w.1.asIdeal : ℝ) ^
        (-(FractionalIdeal.count F w.1
          (n : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ)) : ℝ) : ℂ)
    let fC : {v : FinPlace F // v ∉ S.Sf} → ℂ := fun w =>
      if w.1.asIdeal ∣ c then
        (((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          g2 D A w.1 * chi D w.1 ((cg : F) / unif w.1) ^ 2
      else 1
    have hpoint (w : {v : FinPlace F // v ∉ S.Sf}) :
        sphericalTable D A w.1 (ordv w.1 (toLoc w.1 a)) (unitPart w.1 (toLoc w.1 a)) =
          fN w * fC w := by
      rw [thetaExterior_sphericalTable_local_factor D S A 𝔄 c n a cg ng ε
        hfactor ha.1 hcg.1 hnggen hε haeq hsq w.1 w.2]
    have hfNfinite : Function.HasFiniteMulSupport fN := by
      simpa [fN] using thetaExterior_nNorm_finite S n hcnext.2
    have hfCfinite : Function.HasFiniteMulSupport fC := by
      classical
      have hdivFinite :
          {w : {v : FinPlace F // v ∉ S.Sf} | w.1.asIdeal ∣ c}.Finite :=
        Set.Finite.preimage
          (f := Subtype.val)
          (by
            intro x _ y _ hxy
            exact Subtype.ext hxy)
          (Ideal.finite_factors hcnext.1.1)
      have hsub : Function.mulSupport fC ⊆
          {w : {v : FinPlace F // v ∉ S.Sf} | w.1.asIdeal ∣ c} := by
        intro w hw
        by_contra hnot
        have hdiv : ¬ w.1.asIdeal ∣ c := hnot
        have hone : fC w = 1 := by simp [fC, hdiv]
        exact (Function.mem_mulSupport.mp hw) hone
      change (Function.mulSupport fC).Finite
      exact Set.Finite.subset hdivFinite hsub
    have hprodSplit :
        (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf},
          sphericalTable D A w.1 (ordv w.1 (toLoc w.1 a)) (unitPart w.1 (toLoc w.1 a))) =
          (∏ᶠ w, fN w) * (∏ᶠ w, fC w) := by
      calc
        _ = ∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fN w * fC w := by
          apply finprod_congr
          intro w
          exact hpoint w
        _ = _ := finprod_mul_distrib hfNfinite hfCfinite
    have hNvalue : (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fN w) =
        (((Ideal.absNorm n : ℝ)⁻¹ : ℝ) : ℂ) := by
      simpa [fN] using thetaExterior_nNorm_finprod S n hcnext.2
    obtain ⟨T, hcfactor, hcmem, hTc⟩ :=
      thetaExterior_squarefree_factorization S c hcnext.1 hsq
    let U := thetaExterior_placeFinset S T hTc
    let gC : FinPlace F → ℂ := fun v =>
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        g2 D A v * chi D v ((cg : F) / unif v) ^ 2
    have hCsub : Function.mulSupport fC ⊆ (U : Set {v : FinPlace F // v ∉ S.Sf}) := by
      intro w hw
      by_cases hdiv : w.1.asIdeal ∣ c
      · exact (thetaExterior_mem_placeFinset S T hTc w.1 w.2).2 ((hcmem w.1).mp hdiv)
      · have hone : fC w = 1 := by simp [fC, hdiv]
        exact ((Function.mem_mulSupport.mp hw) hone).elim
    have hCprod : (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fC w) =
        (((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          gamma D S A 2 c (cg : F) := by
      have hcgT : S.IsGen (cg : F) (∏ v ∈ T, v.asIdeal) := by
        rw [← hcfactor]
        exact hcg.1
      have hgamma := thetaExterior_gamma_finset D S A H Bd T hTc cg
        ⟨hcgT, hcg.2⟩
      have hcnormNat : Ideal.absNorm c = ∏ v ∈ T, Ideal.absNorm v.asIdeal := by
        simpa only [map_prod] using congrArg Ideal.absNorm hcfactor
      have hcnorm : (Ideal.absNorm c : ℝ) =
          ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) := by
        exact_mod_cast hcnormNat
      have hqpos (v : FinPlace F) (hv : v ∈ T) :
          0 < (Ideal.absNorm v.asIdeal : ℝ) :=
        Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)
      have hplace : (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fC w) =
          ∏ w ∈ U, fC w := by
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hCsub U.finite_toSet]
        simp
      calc
        _ = ∏ w ∈ U, fC w := hplace
        _ = ∏ v ∈ T, gC v := by
          calc
            _ = ∏ w ∈ U, gC w.1 := by
              refine Finset.prod_congr rfl ?_
              intro w hw
              have hvT : w.1 ∈ T :=
                (thetaExterior_mem_placeFinset S T hTc w.1 w.2).mp hw
              have hdiv : w.1.asIdeal ∣ c := (hcmem w.1).2 hvT
              simp [fC, gC, hdiv]
            _ = ∏ v ∈ T, gC v := thetaExterior_prod_placeFinset S T hTc gC
        _ = (((∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℝ) : ℂ) *
              (∏ v ∈ T, g2 D A v * chi D v ((cg : F) / unif v) ^ 2) := by
          calc
            _ = ∏ v ∈ T,
                (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  (g2 D A v * chi D v ((cg : F) / unif v) ^ 2) := by
              refine Finset.prod_congr rfl ?_
              intro v hv
              simp [gC]
              ac_rfl
            _ = _ := by rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
        _ = (((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              gamma D S A 2 c (cg : F) := by
          rw [thetaExterior_finset_rpow_prod T
            (fun v => (Ideal.absNorm v.asIdeal : ℝ)) (-(1 / 2 : ℝ)) hqpos,
            ← hcnorm, hgamma.symm, hcfactor]
    calc
      _ = (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fN w) *
            (∏ᶠ w : {v : FinPlace F // v ∉ S.Sf}, fC w) := hprodSplit
      _ = (((Ideal.absNorm n : ℝ)⁻¹ : ℝ) : ℂ) *
            ((((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              gamma D S A 2 c (cg : F)) := by rw [hNvalue, hCprod]
      _ = gamma D S A 2 c (cg : F) *
            ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
            (((Ideal.absNorm n : ℝ))⁻¹ : ℝ) := by ac_rfl
  · intro hnot
    by_contra hprod
    have hAn : 𝔄 ≠ 0 := by simpa [Ideal.zero_eq_bot] using h𝔄.1
    have hres : ∀ v : FinPlace F, v ∉ S.Sf →
        (Associates.mk v.asIdeal).count (Associates.mk 𝔄).factors % 3 ≠ 2 := by
      intro v hv hmod
      have hordeq : ordv v (toLoc v a) =
          (Associates.mk v.asIdeal).count (Associates.mk 𝔄).factors := by
        rw [← thetaExterior_count_principal_eq_ordv v a, ha.1.2.2 v hv,
          FractionalIdeal.count_coe F v hAn]
      have hmod' : ordv v (toLoc v a) % 3 = 2 := by
        rw [hordeq]
        have hmodCast :
            (((Associates.mk v.asIdeal).count (Associates.mk 𝔄).factors % 3 : ℕ) : ℤ) = 2 := by
          exact_mod_cast hmod
        rw [Int.natCast_mod] at hmodCast
        norm_num at hmodCast
        exact hmodCast
      let f : {v : FinPlace F // v ∉ S.Sf} → ℂ := fun v =>
        sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a)) (unitPart v.1 (toLoc v.1 a))
      have hz : f ⟨v, hv⟩ = 0 := by
        dsimp [f]
        by_cases hneg : ordv v (toLoc v a) < 0
        · simp [sphericalTable, hneg]
        · simp [sphericalTable, hneg, hmod']
      have hmem : (⟨v, hv⟩ : {v : FinPlace F // v ∉ S.Sf}) ∈ Function.mulSupport f := by
        exact Function.mem_mulSupport.mpr (by rw [hz]; exact zero_ne_one)
      rw [finprod_eq_prod_of_mulSupport_subset_of_finite f (Set.Subset.rfl) hfinite] at hprod
      have hzeroProd := Finset.prod_eq_zero (hfinite.mem_toFinset.mpr hmem) hz
      exact hprod hzeroProd
    obtain ⟨c, n, hsq, heq⟩ := thetaExterior_cubeDecomp_of_no_residue_two S 𝔄 h𝔄 hres
    exact (hnot c n hsq) heq

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
  classical
  have htable (v : FinPlace F) (hv : v ∉ S.Sf) :
      TF.Wv v (C.a v (toLoc v a)) =
        sphericalTable D A v (ordv v (toLoc v a)) (unitPart v (toLoc v a)) := by
    let e := ordv v (toLoc v a)
    let u := unitPart v (toLoc v a)
    have hdecomp : toLoc v a =
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u := by
      change toLoc v a =
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e *
          (toLoc v a *
            (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ (-e))
      have hcancel : (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e *
          (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ (-e) = 1 := by
        rw [← zpow_add]
        simp
      calc
        toLoc v a = toLoc v a * 1 := by simp
        _ = toLoc v a *
            ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e *
              (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ (-e)) := by
          rw [hcancel, mul_one]
        _ = (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e *
              (toLoc v a *
                (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ (-e)) := by ac_rfl
    have hu : IsLocUnit v u := unitPart_isLocUnit v (toLoc v a)
    calc
      TF.Wv v (C.a v (toLoc v a)) =
          TF.Wv v (C.a v
            ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) := by
        rw [hdecomp]
      _ = sphericalTable D A v e u := TF.Wv_table v hv e u hu.1 hu.2
      _ = sphericalTable D A v (ordv v (toLoc v a)) (unitPart v (toLoc v a)) := by
        simp [e, u]
  have hfun :
      (fun v : {v : FinPlace F // v ∉ S.Sf} => TF.Wv v.1 (C.a v.1 (toLoc v.1 a))) =
        fun v => sphericalTable D A v.1 (ordv v.1 (toLoc v.1 a))
          (unitPart v.1 (toLoc v.1 a)) := by
    funext v
    exact htable v.1 v.2
  obtain ⟨hfinite, hvalue, hzero⟩ :=
    sphericalTable_product D S A H Bd 𝔄 h𝔄 a ha
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hfinite
  · intro c n cg hsq hAn hgen
    rw [hfun]
    exact hvalue c n cg hsq hAn hgen
  · intro hnot
    rw [hfun]
    exact hzero hnot

end Assemble

end ArtinPrimitiveRoots.A1.Theta
