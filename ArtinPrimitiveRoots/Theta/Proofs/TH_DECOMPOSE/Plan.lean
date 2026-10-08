import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Eis
import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.QuotientGeometry
import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.ScalarSupport

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Level and compact sets, parameterized to avoid importing `Reduction`. -/
def redLevel (P : CoverPackage D S H A) (T0 : Finset (FinPlace F))
    (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ w, P.compC w x = 1) ∧
    (∀ v ∈ T0, P.compF v x ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v x ∈ (P.tame v (fun h => hv (hsub h))).Kmax}

def redCompact (P : CoverPackage D S H A) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ v, P.compF v x = 1) ∧
    ∀ w, ∃ k : GL (Fin 2) ℂ, (k : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.unitaryGroup (Fin 2) ℂ ∧ P.compC w x = QuotientGroup.mk k}

/-- The common subgroup and the untwisted rational-cusp parametrization. -/
structure RedDecomposeGeometry [IsTotallyComplex F] (P : CoverPackage D S H A)
    (G : GlobalDatum P) (a : (InfinitePlace F → ℝ) → P.tc.G)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (gj : P.tc.G) where
  Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
  hfinite : Γ.FiniteIndex
  hfree : ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ
  cuspLag : ∀ (τ : Matrix.SpecialLinearGroup (Fin 2) F) (γ : Γ)
    (ε : (𝓞 F)ˣ) (μ : F),
    τ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) * τ =
      ArtinPrimitiveRoots.A1.Spec.cuspUnitMatrix F ε μ →
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε) ^ 2 ∈ G.Δ
  ι : Type
  fintype : Fintype ι
  σ : ι → Matrix.SpecialLinearGroup (Fin 2) F
  e : Quotient (QuotientGroup.rightRel (Bstar G)) ≃
    (Σ i, (Fˣ ⧸ G.Δ) × ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
  repr : ∀ p, e.symm p = Quotient.mk _
    (diagGL (Quotient.out p.2.1) * Matrix.SpecialLinearGroup.toGL
      ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F p.2.2.out.1))
  action : ∀ γ ∈ Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
    (∀ w, 0 < y w) → ∃ k ∈ redLevel P T0 hsub m, ∃ kinf ∈ redCompact P,
      P.tc.rat (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * nInf P x * a y * gj =
      nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
        ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) *
      a (fun w => ArtinPrimitiveRoots.A1.Spec.height
        ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) * gj * (kinf * k)

/-- Shrink a good subgroup so every cusp diagonal ratio belongs to `Δ`. -/
theorem red_decompose_part1 [IsTotallyComplex F] (P : CoverPackage D S H A)
    (G : GlobalDatum P) (a : (InfinitePlace F → ℝ) → P.tc.G)
    (ha : a = fun y => if hy : ∀ w, 0 < y w then
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
        P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod else 1)
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1)
    (hgood : ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)), Γ.FiniteIndex ∧
      ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ ∧
      ∀ γ ∈ Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (∀ w, 0 < y w) → ∃ k ∈ redLevel P T0 hsub m,
      ∃ kinf ∈ redCompact P,
      P.tc.rat (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * nInf P x * a y * gj =
      nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
        ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) *
      a (fun w => ArtinPrimitiveRoots.A1.Spec.height
        ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) * gj * (kinf * k)) :
    Nonempty (RedDecomposeGeometry P G a T0 hsub m gj) := by
  obtain ⟨N, hN, hNfinite, hNlag⟩ := exists_cusp_lagrangian_congruence P G
  obtain ⟨Γ₀, hfinite, hfree, haction⟩ := hgood
  let Γ := Γ₀ ⊓ Spec.congrSubgroup F N
  letI : Γ₀.FiniteIndex := hfinite
  letI : (Spec.congrSubgroup F N).FiniteIndex := hNfinite
  letI : Γ.FiniteIndex := inferInstance
  obtain ⟨ι, hι, σ, hσ⟩ := Spec.exists_cusp_reps F Γ
  obtain ⟨e, he⟩ := cusp_fiber_equiv P G (Σ i, Spec.CuspCosets F Γ (σ i))
    (fun p => (σ p.1)⁻¹ * Spec.toSLF F (p.2.out : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) hσ
  let rearrange : ((Fˣ ⧸ G.Δ) × (Σ i, Spec.CuspCosets F Γ (σ i))) ≃
      (Σ i, (Fˣ ⧸ G.Δ) × Spec.CuspCosets F Γ (σ i)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨{
    Γ := Γ
    hfinite := inferInstance
    hfree := ?_
    cuspLag := ?_
    ι := ι
    fintype := hι
    σ := σ
    e := e.trans rearrange
    repr := ?_
    action := ?_ }⟩
  · intro γ hγ z hz
    exact hfree γ hγ.1 z hz
  · intro τ γ ε μ hconj
    exact hNlag τ γ γ.property.2 ε μ hconj
  · intro p
    exact he (rearrange.symm p)
  · intro γ hγ x y hy
    exact haction γ hγ.1 x y hy

/-- The finite torus coefficients, with support independent of the parameter. -/
theorem th_decompose_part2 [IsTotallyComplex F] (P : CoverPackage D S H A)
    (G : GlobalDatum P) (sec : ∀ s : ℂ, GlobalSection P G s)
    (T0 : Finset (FinPlace F)) (hT0 : ∀ s, (sec s).T0 = T0)
    (hsub : S.Sf ⊆ T0) (hC : ∀ s w, (sec s).fC w = sphC s)
    (m : FinPlace F → ℕ) (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v)
    (hlevel : ∀ s g, ∀ k ∈ redLevel P T0 hsub m,
      scalarOf P G (sec s).f (sec s).fC (g * k) = scalarOf P G (sec s).f (sec s).fC g)
    (han : ∀ v (g : (P.loc v).L), AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re})
    (a : (InfinitePlace F → ℝ) → P.tc.G)
    (ha : a = fun y => if hy : ∀ w, 0 < y w then
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
        P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod else 1)
    (gj : P.tc.G) (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1)
    (d : RedDecomposeGeometry P G a T0 hsub m gj) :
    ∃ (Ds : d.ι → Finset (Fˣ ⧸ G.Δ)) (b : d.ι → (Fˣ ⧸ G.Δ) → ℂ → ℂ),
      (∀ i δ, AnalyticOnNhd ℂ (b i δ) {s | 0 < s.re}) ∧
      (∀ i δ, δ ∉ Ds i → ∀ s, b i δ s = 0) ∧
      ∀ s : ℂ, 1 / 2 < s.re → ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (∀ w, 0 < y w) → ∀ p,
      scalarOf P G (sec s).f (sec s).fC
        (P.tc.rat (Quotient.out (d.e.symm p)) * (nInf P x * a y * gj)) =
      b p.1 p.2.1 s * ArtinPrimitiveRoots.A1.Spec.eisTerm F d.Γ (d.σ p.1) s
        (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) p.2.2 := by
  have hlocal (v : FinPlace F) : (G.Alag v).FiniteIndex :=
    local_lagrangian_finiteIndex P G v
  have hclasses (T : Finset (FinPlace F)) := finite_exterior_lagrangian_classes P G T
  have htame (v : FinPlace F) (hv : v ∉ S.Sf) (x : (v.adicCompletion F)ˣ)
      (hx : x ∉ G.Alag v) := tame_lam_sigma_eq_zero P G v hv x hx
  have hsupport (g : P.tc.G) := finite_diagonal_scalar_support P G sec T0 hT0 g
  sorry

/-- Absolute convergence and finite-sum reindexing once the terms have been separated. -/
theorem th_decompose_part3 [IsTotallyComplex F]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) [Γ.FiniteIndex]
    {ι U Q : Type} [Fintype ι] (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (e : Q ≃ (Σ i, U × ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)))
    (Ds : ι → Finset U) (b : ι → U → ℂ) (t : Q → ℂ)
    (s : ℂ) (hs : 1 / 2 < s.re) (z : ArtinPrimitiveRoots.A1.Spec.X F)
    (hzero : ∀ i δ, δ ∉ Ds i → b i δ = 0)
    (hterm : ∀ p, t (e.symm p) = b p.1 p.2.1 *
      ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ p.1) s z p.2.2) :
    Summable (fun q => ‖t q‖) ∧
      ∑' q, t q = ∑ i, (∑ δ ∈ Ds i, b i δ) *
        ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ i) s z := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
