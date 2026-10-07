import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Reduction

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-RES -/

section Res

open MeasureTheory Filter Topology

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- `ζ_F^{T0}(u) = ζ_F(u) Π_{v∈T0} (1 - q_v^{-u})` (Mathlib `NumberField.dedekindZeta`). -/
def zetaT0 (T0 : Finset (FinPlace F)) (u : ℂ) : ℂ :=
  NumberField.dedekindZeta F u * ∏ v ∈ T0, (1 - (qv v : ℂ) ^ (-u))

/-- **res:zeta**: `Π_{v∉T0} c_v(s) = ζ_F^{T0}(6s)/ζ_F^{T0}(6s+1)` for `Re s > 1/6`. -/
theorem cprod_eq_zeta_ratio (T0 : Finset (FinPlace F)) (s : ℂ) (hs : 1 / 6 < s.re) :
    cprod T0 s = zetaT0 T0 (6 * s) / zetaT0 T0 (6 * s + 1) := by
  sorry

/-- **res:pole**: `cprod` has a simple pole at `s0 = 1/6` with nonzero residue. -/
theorem cprod_pole (T0 : Finset (FinPlace F)) :
    ∃ ε > 0, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧ Ψ (1 / 6) ≠ 0 ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, 1 / 6 < s.re → Ψ s = (s - 1 / 6) * cprod T0 s := by
  sorry

/-- The residue of `cprod` at `1/6`. -/
def resCprod (T0 : Finset (FinPlace F)) : ℂ :=
  limUnder (𝓝[>] (1 / 6 : ℝ)) fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)

theorem resCprod_ne_zero (T0 : Finset (FinPlace F)) : resCprod T0 ≠ 0 := by
  sorry

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
its residue `θ` at `1/6`, and the commutation of the residue with torus integrals. -/
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

/-- **res:continuation** (existence, from P-REDUCTION `red:decompose` and P-SPEC
`exists_continuedEisenstein`). -/
theorem exists_continuedEis {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) : Nonempty (ContinuedEis Fam) := by
  sorry

/-- The `M(1/6)`-data of a family: `M_v(1/6) f_v` at `v ∈ T0`, `f°'_v` elsewhere. -/
def famM {P : CoverPackage D S H A} {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    (Fam : AnalyticFamily P G μ) (v : FinPlace F) : (P.loc v).L → (G.T v).V :=
  if hv : v ∈ Fam.T0 then intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v)
  else sphWeyl P G v (fun h => hv ((Fam.T0_eq (1 / 6)) ▸ (Fam.sec (1 / 6)).sub h)) (1 / 6)

/-- **res:theta-constant**: the constant term of `θ` is `κ_F⁻¹ · res · Σ_δ Θ^M(a(δ)g)`. -/
theorem theta_constantTerm {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd) :
    torusCoeff P C.theta g Pd 0 = (κF F)⁻¹ * resCprod Fam.T0 *
      ∑' δ : Fˣ ⧸ G.Δ, scalarOf P G (famM Fam) (fun _ => intertwineC (sphC (1 / 6)))
        (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
  sorry

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

/-- **res:theta-whittaker**: every torus coefficient of `θ` with `ν ≠ 0` over an adapted lattice is
`W_θ(a(ν) g)`; `W_θ` is genuine and `(N, ψ)`-equivariant at every place. -/
theorem theta_fourierCoeff {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    torusCoeff P C.theta g Pd (ν : F) = thetaWhit C (P.tc.rat (diagGL ν) * g) := by
  sorry

theorem thetaWhit_equiv {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam) :
    (∀ ζ g, thetaWhit C (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaWhit C g) ∧
    (∀ x g, thetaWhit C (P.tc.nS (Multiplicative.ofAdd x) * g) = S.e A x * thetaWhit C g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, thetaWhit C (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * thetaWhit C g) := by
  sorry

/-- **res:depends-on-M** (via P-REDUCTION and P-SPEC `res_lincomb_eq_zero` only): `θ` depends only on
the `M(1/6)`-data. -/
theorem theta_depends_on_M {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam Fam' : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (C' : ContinuedEis Fam') (hT : Fam.T0 = Fam'.T0)
    (hM : ∀ v ∈ Fam.T0, intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) =
      intertwine (P.loc v) (μ v) ((Fam'.sec (1 / 6)).f v)) :
    C.theta = C'.theta := by
  sorry

/-- **res:linear-translate**: `θ` is linear in the section at one place and right translation of
that section translates `θ`. -/
theorem theta_linear_translate {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (v0 : FinPlace F) (Fam Fam' Fam'' : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (C' : ContinuedEis Fam') (C'' : ContinuedEis Fam'') :
    ((∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v ∧ (Fam''.sec s).f v = (Fam.sec s).f v) →
      ∀ c : ℂ, (∀ s, (Fam''.sec s).f v0 = (Fam.sec s).f v0 + c • (Fam'.sec s).f v0) →
        C''.theta = C.theta + c • C'.theta) ∧
    (∀ h : (P.loc v0).L, (∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
      (∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0)) →
        ∀ g, C'.theta g = C.theta (g * P.emb v0 h)) := by
  sorry

/-- **res:exterior-whittaker**: at `v0 ∉ S`, `M(1/6) f ↦ W_θ(g)` (`g` commuting with the `v0`-part)
is a well-defined Whittaker functional on `Θ_{v0}`; P-LOCAL-WHIT then makes it unique. -/
theorem theta_exterior_whittaker {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G) (hg : ∀ h : (P.loc v0).L, g * P.emb v0 h = P.emb v0 h * g) :
    ∃ Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ,
      IsWhittakerOn (P.loc v0) A (thetaSpace (P.loc v0) (G.T v0) (μ v0)) Λ ∧
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
        Fam'.T0 = insert v0 Fam.T0 → (∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
          thetaWhit C' g = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0)) := by
  sorry

/-- **res:root-generation**: at a tame place the root subgroups generate a nontrivial central element. -/
theorem center_mem_root_closure {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    ∃ ζ : rootsOfUnity 3 ℂ, ζ ≠ 1 ∧ L.z ζ ∈ Subgroup.closure (Set.range L.n ∪ Set.range L.nbar) := by
  sorry

/-- **res:nonzero**: a nonzero `θ` has a nonzero Whittaker coefficient. -/
theorem thetaWhit_ne_zero {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (hθ : ∃ g, C.theta g ≠ 0) : ∃ g, thetaWhit C g ≠ 0 := by
  sorry

/-- **res:theta-exists**: big-cell sections at `S_f` and spherical sections elsewhere give `θ ≠ 0`. -/
theorem exists_theta_ne_zero (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) :
    ∃ (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam), Fam.T0 = S.Sf ∧
      (∀ v ∈ S.Sf, ∃ φ : v.adicCompletion F → (G.T v).V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
        ∀ s, (Fam.sec s).f v = bigCell (P.loc v) (G.T v) s φ) ∧ ∃ g, C.theta g ≠ 0 := by
  sorry

/-- **res:theta-multilinear**: with the data outside `S_f` fixed, `W_θ(g)` is a multilinear form in
the local Jacquet vectors at `S_f` at `s0`, times the complex spherical Jacquet values. -/
theorem thetaWhit_multilinear {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (x0 : P.RP) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam') (x : P.RP), Fam'.T0 = Fam.T0 →
        (∀ s, ∀ v, v ∉ S.Sf → (Fam'.sec s).f v = (Fam.sec s).f v) →
        (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) →
          thetaWhit C' (P.q x) =
            Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) ((Fam'.sec (1 / 6)).f v.1))) *
              ∏ w, jacquetC (rtr (P.compC w x) (sphC (1 / 6))) := by
  sorry

end Res

end ArtinPrimitiveRoots.A1.Theta
