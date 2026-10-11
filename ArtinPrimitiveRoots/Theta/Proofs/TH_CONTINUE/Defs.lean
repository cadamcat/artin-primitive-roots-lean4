import ArtinPrimitiveRoots.Theta.Reduction

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The section data used by TH-CONTINUE. Keeping this independent of `AnalyticFamily` avoids
an import cycle with `Res.lean`. -/
structure ContinuedEisInput (P : CoverPackage D S H A) (G : GlobalDatum P) where
  sec : ∀ s : ℂ, GlobalSection P G s
  T0 : Finset (FinPlace F)
  T0_eq : ∀ s, (sec s).T0 = T0
  fC_sph : ∀ s w, (sec s).fC w = sphC s
  f_analytic : ∀ v (g : (P.loc v).L),
    AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re}
  level : ∀ v ∈ T0, ∃ m, (P.loc v).m0 ≤ m ∧
    ∀ s g, ∀ k ∈ (P.loc v).Kc m, (sec s).f v (g * k) = (sec s).f v g

variable [IsTotallyComplex F]

/-- A common level, finite components, and cusp continuations aligned to one radius.
The radius bound keeps all coefficient functions analytic on the residue ball.
Inputs: `exists_classical_components`,
`red_decompose`, `Spec.exists_continuedEisenstein`, and `exists_restrict`. -/
structure ContinuedEisComponents {P : CoverPackage D S H A} {G : GlobalDatum P}
    (I : ContinuedEisInput P G) where
  hsub : S.Sf ⊆ I.T0
  m : FinPlace F → ℕ
  hm : ∀ v ∈ I.T0, (P.loc v).m0 ≤ m v
  hlevel : ∀ s g, ∀ k ∈ levelSet P I.T0 hsub m,
    scalarOf P G (I.sec s).f (I.sec s).fC (g * k) =
      scalarOf P G (I.sec s).f (I.sec s).fC g
  J : Finset P.tc.G
  finite_components : ∀ j ∈ J, ∃ x : P.RP, P.q x = j ∧ ∀ w, P.compC w x = 1
  detect : ∀ Ψ : P.tc.G → ℂ, (∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g) →
    (∀ g, ∀ k ∈ levelSet P I.T0 hsub m, Ψ (g * k) = Ψ g) →
    (∀ g, ∀ k ∈ infCompact P, Ψ (g * k) = Ψ g) →
    (∀ j ∈ J, ∀ z, classicalOf P Ψ j z = 0) → ∀ g, Ψ g = 0
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ (1 / 12 : ℝ)
  Γ : J → Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
  finiteIndex : ∀ j, (Γ j).FiniteIndex
  free : ∀ j, ArtinPrimitiveRoots.A1.Spec.FreeAction F (Γ j)
  cuspCount : J → ℕ
  σ : ∀ j, Fin (cuspCount j) → Matrix.SpecialLinearGroup (Fin 2) F
  c : ∀ j, Fin (cuspCount j) → ℂ → ℂ
  c_analytic : ∀ j i, AnalyticOnNhd ℂ (c j i) {s | 0 < s.re}
  d : ∀ j i, ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F (Γ j) (σ j i) (1 / 6)
  d_radius : ∀ j i, (d j i).ε = ε
  series_component : ∀ (j : J) (s : ℂ), 1 / 2 < s.re → ∀ z,
    classicalOf P (eisenstein P G (I.sec s)) j z =
      ∑ i, c j i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F (Γ j) (σ j i) s z

/-- The continued finite cusp sum on one component. -/
def ContinuedEisComponents.componentE {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) (j : C.J)
    (s : ℂ) (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  ∑ i, C.c j i s * (C.d j i).E s z

/-- The residue of the finite cusp sum on one component. -/
def ContinuedEisComponents.componentTheta {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) (j : C.J)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  ∑ i, C.c j i (1 / 6) * (C.d j i).res z

/-- Adelic reconstruction of the component formulas. `point_transport` records the same
representation for the continued functions and their original series; its multiplier is
independent of the spectral parameter. No claim is made outside the continuation domain.
-/
structure ContinuedEisReconstruction {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) where
  E : ℂ → P.tc.G → ℂ
  theta : P.tc.G → ℂ
  E_aut : ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε, ∀ γ g,
    E s (P.tc.rat γ * g) = E s g
  E_level : ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε, ∀ g,
    ∀ k ∈ levelSet P I.T0 C.hsub C.m, E s (g * k) = E s g
  E_compact : ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε, ∀ g,
    ∀ k ∈ infCompact P, E s (g * k) = E s g
  theta_aut : ∀ γ g, theta (P.tc.rat γ * g) = theta g
  theta_level : ∀ g, ∀ k ∈ levelSet P I.T0 C.hsub C.m, theta (g * k) = theta g
  theta_compact : ∀ g, ∀ k ∈ infCompact P, theta (g * k) = theta g
  E_component : ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε, ∀ j : C.J,
    classicalOf P (E s) j = C.componentE j s
  theta_component : ∀ j : C.J, classicalOf P theta j = C.componentTheta j
  point_transport : ∀ g, ∃ (j : C.J) (a : ℂ) (z : ArtinPrimitiveRoots.A1.Spec.X F),
    (∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε,
      E s g = a * C.componentE j s z) ∧
    theta g = a * C.componentTheta j z ∧
    ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      eisenstein P G (I.sec s) g = a * classicalOf P (eisenstein P G (I.sec s)) j z

/-- One fixed classical component along an entire left archimedean unipotent orbit, with
continuous positive coordinates. Compact parameter sets therefore have compact coordinate
images contained in `Spec.posSet`. -/
def ContinuedEisTorusCharts {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) : Prop :=
  ∀ g, ∃ (j : C.J) (a : ℂ) (p : (InfinitePlace F → ℂ) → ArtinPrimitiveRoots.A1.Spec.Coord F),
    Continuous p ∧ (∀ x, p x ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) ∧
    (∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε, ∀ x,
      R.E s (nInf P x * g) = a * C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) ∧
    ∀ x, R.theta (nInf P x * g) =
      a * C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))

end ArtinPrimitiveRoots.A1.Theta
