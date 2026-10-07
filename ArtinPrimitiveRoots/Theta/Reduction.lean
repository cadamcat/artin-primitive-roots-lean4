import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-REDUCTION -/

section Reduction

open MeasureTheory

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- `a(y)` at the complex places, `y_w > 0` (junk `1` otherwise). -/
def aInf (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ) : P.tc.G :=
  if hy : ∀ w, 0 < y w then
    ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
      P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod
  else 1

/-- The classical function on `X = (ℍ³)^r` attached to `Ψ : G → ℂ` and a finite-adelic point `g`:
`z = (x_w + j y_w)_w ↦ Ψ(n_∞(x) a_∞(y) g)`. -/
def classicalOf (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  Ψ (nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)) *
    aInf P (fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)) * g)

/-- The level `K_f(T0, m)`: `q x` with `x_v ∈ Kc(m_v)` on `T0`, `x_v ∈ Kmax_v` off `T0`, and
trivial complex components. -/
def levelSet (P : CoverPackage D S H A) (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0)
    (m : FinPlace F → ℕ) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ w, P.compC w x = 1) ∧
    (∀ v ∈ T0, P.compF v x ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v x ∈ (P.tame v (fun h => hv (hT0 h))).Kmax}

/-- The archimedean maximal compact `PU(2)^r` inside `G`. -/
def infCompact (P : CoverPackage D S H A) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ v, P.compF v x = 1) ∧
    ∀ w, ∃ k : GL (Fin 2) ℂ, (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P.compC w x = QuotientGroup.mk k}

/-- **red:components** (strong approximation for `SL₂`, finiteness of `F^×\𝔸_f^×/det K_f 𝔸_f^{×2}`):
finitely many finite-adelic points `g_j`; an automorphic, level- and `PU(2)^r`-invariant function
vanishing on all `g_∞ g_j` vanishes. -/
theorem exists_classical_components (P : CoverPackage D S H A) (T0 : Finset (FinPlace F))
    (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ) :
    ∃ J : Finset P.tc.G, (∀ gj ∈ J, ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) ∧
      ∀ Ψ : P.tc.G → ℂ, (∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g) →
        (∀ g, ∀ k ∈ levelSet P T0 hT0 m, Ψ (g * k) = Ψ g) →
        (∀ g, ∀ k ∈ infCompact P, Ψ (g * k) = Ψ g) →
        (∀ gj ∈ J, ∀ z, classicalOf P Ψ gj z = 0) → ∀ g, Ψ g = 0 := by
  sorry

/-- **red:congruence** (Kubota's splitting on `Γ(N₀)`, archimedean Iwasawa, free action): for each
`g_j` there is a finite-index, freely acting `Γ'' ≤ SL₂(O_F)` with
`rat(γ) n_∞(x) a_∞(y) g_j = n_∞(x′) a_∞(y′) g_j k_∞ k`, `(x′, y′)` the coordinates of `γ • z`. -/
theorem exists_good_subgroup [IsTotallyComplex F] (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) :
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)), Γ.FiniteIndex ∧
      ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ ∧
      ∀ γ ∈ Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
        ∃ k ∈ levelSet P T0 hT0 m, ∃ kinf ∈ infCompact P,
          P.tc.rat (Matrix.SpecialLinearGroup.toGL
              (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * nInf P x * aInf P y * gj =
            nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
                ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) *
              aInf P (fun w => ArtinPrimitiveRoots.A1.Spec.height
                ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) * gj * (kinf * k) := by
  sorry

/-- **red:decompose** (P-SPEC obligation (1)): for sections with spherical complex components and a
uniform level, on the component of `g_j` the adelic Eisenstein series is a finite combination of
P-SPEC Eisenstein series of one good `Γ''`, with coefficients holomorphic on `Re s > 0`; the adelic
series converges absolutely for `Re s > 1/2`. -/
theorem red_decompose [IsTotallyComplex F] (P : CoverPackage D S H A) (G : GlobalDatum P)
    (sec : ∀ s : ℂ, GlobalSection P G s) (T0 : Finset (FinPlace F)) (hT0 : ∀ s, (sec s).T0 = T0)
    (hsub : S.Sf ⊆ T0) (hC : ∀ s w, (sec s).fC w = sphC s) (m : FinPlace F → ℕ)
    (hlevel : ∀ s, ∀ g, ∀ k ∈ levelSet P T0 hsub m,
      scalarOf P G (sec s).f (sec s).fC (g * k) = scalarOf P G (sec s).f (sec s).fC g)
    (han : ∀ v (g : (P.loc v).L), AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re})
    (gj : P.tc.G) (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) :
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)), Γ.FiniteIndex ∧
      ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ ∧
      ∃ (ι : Type) (_ : Fintype ι) (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F) (c : ι → ℂ → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) {s | 0 < s.re}) ∧
        ∀ s : ℂ, 1 / 2 < s.re → ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
          (∀ w, 0 < y w) →
          (Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
            ‖scalarOf P G (sec s).f (sec s).fC (P.tc.rat (Quotient.out γ) * (nInf P x * aInf P y * gj))‖) ∧
          eisenstein P G (sec s) (nInf P x * aInf P y * gj) =
            ∑ i, c i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ i) s
              (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
  sorry

/-- **red:constant-term**: vanishing adelic constant coefficients (over every adapted lattice at
every point) give vanishing classical constant terms at every cusp and height, in the form of
P-SPEC `res_lincomb_eq_zero`. -/
theorem classical_constTerm_eq_zero [IsTotallyComplex F] (P : CoverPackage D S H A)
    (Ψ : P.tc.G → ℂ) (gj : P.tc.G) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    (hΓ : ∀ γ ∈ Γ, ∀ z, classicalOf P Ψ gj (γ • z) = classicalOf P Ψ gj z)
    (hΨ : ∀ (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 → (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h, Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h) →
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd volume → Bornology.IsBounded Pd → torusCoeff P Ψ g Pd 0 = 0) :
    ∀ (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ Pτ : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) Pτ volume ∧
        ∫ x in Pτ, classicalOf P Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) = 0 := by
  sorry

end Reduction

end ArtinPrimitiveRoots.A1.Theta
