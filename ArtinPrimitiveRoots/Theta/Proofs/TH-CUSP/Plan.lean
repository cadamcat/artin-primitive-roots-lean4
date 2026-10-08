import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The classical value in coordinates, with the positive diagonal supplied by `Reduction`. -/
def cuspClassical (P : CoverPackage D S H A)
    (a : (InfinitePlace F → ℝ) → P.tc.G) (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  Ψ (nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)) *
    a (fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)) * gj)

/-- Projective Iwasawa follows from equality of the corresponding hyperbolic points. -/
theorem cusp_arch_iwasawa (g : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x x' : ℂ) (y y' : ℝ) (hy : 0 < y) (hy' : 0 < y')
    (hcoord : g • ArtinPrimitiveRoots.A1.Spec.pt x y = ArtinPrimitiveRoots.A1.Spec.pt x' y') :
    ∃ k : GL (Fin 2) ℂ, (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL g) : PGL2 ℂ) *
        QuotientGroup.mk (upperM ℂ x) *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) =
      QuotientGroup.mk (upperM ℂ x') *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (y' : ℂ) (Complex.ofReal_ne_zero.mpr hy'.ne'))) *
        QuotientGroup.mk k := by
  have hproj (u : ℂ) (v : ℝ) (hv : 0 < v) :
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat u v hv)) : PGL2 ℂ) =
      QuotientGroup.mk (upperM ℂ u) *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (v : ℂ) (Complex.ofReal_ne_zero.mpr hv.ne'))) := by
    have hs : (Real.sqrt v : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
    have hs2 : (Real.sqrt v : ℂ) * (Real.sqrt v : ℂ) = (v : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hv.le
    let c : ℂˣ := Units.mk0 (Real.sqrt v : ℂ) hs
    have he : Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.ptMat u v hv) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c =
        upperM ℂ u * diagM ℂ (Units.mk0 (v : ℂ) (Complex.ofReal_ne_zero.mpr hv.ne')) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.toGL, ArtinPrimitiveRoots.A1.Spec.ptMat, upperM, diagM,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, c, hs, hs2]
    have hc : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈
        Subgroup.center (GL (Fin 2) ℂ) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hcq : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : PGL2 ℂ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    have heq := congrArg (fun t : GL (Fin 2) ℂ => (QuotientGroup.mk t : PGL2 ℂ)) he
    simpa only [QuotientGroup.mk_mul, hcq, mul_one] using heq
  have hq : (QuotientGroup.mk (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy) :
      ArtinPrimitiveRoots.A1.Spec.H3) =
      QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy') := by
    rw [ArtinPrimitiveRoots.A1.Spec.pt, ArtinPrimitiveRoots.A1.Spec.pt,
      dite_eq_left hy, dite_eq_left hy'] at hcoord
    change (QuotientGroup.mk (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy) :
      ArtinPrimitiveRoots.A1.Spec.H3) =
      QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy') at hcoord
    exact hcoord
  let kSL := (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy')⁻¹ *
    (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)
  have hk : kSL ∈ ArtinPrimitiveRoots.A1.Spec.SU2 :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hq.symm)
  refine ⟨Matrix.SpecialLinearGroup.toGL kSL, hk, ?_⟩
  calc
    _ = (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL g) : PGL2 ℂ) *
        QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)) := by
      rw [mul_assoc, hproj]
    _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)) := by simp only [map_mul, QuotientGroup.mk_mul]
    _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy' * kSL)) := by
      congr 2
      dsimp only [kSL]
      group
    _ = _ := by
      simp only [map_mul, QuotientGroup.mk_mul]
      rw [hproj]

/-- Archimedean Iwasawa transports the cusp integrand to one adelic unipotent orbit. -/
theorem classical_constTerm_eq_zero_part1 [IsTotallyComplex F]
    (P : CoverPackage D S H A) (a : (InfinitePlace F → ℝ) → P.tc.G)
    (ha : a = fun y => if hy : ∀ w, 0 < y w then
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
        P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod else 1)
    (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1)
    (hAut : ∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g)
    (hInf : ∀ g, ∀ k ∈ {k | ∃ x : P.RP, P.q x = k ∧ (∀ v, P.compF v x = 1) ∧
      ∀ w, ∃ u : GL (Fin 2) ℂ, (u : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.unitaryGroup (Fin 2) ℂ ∧ P.compC w x = QuotientGroup.mk u}, Ψ (g * k) = Ψ g)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    ∃ g', ∀ x, cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) =
      Ψ (nInf P x * g') := by
  sorry

/-- A common adapted ideal is a finite-index sublattice of the cusp translations. -/
theorem th_cusp_part2 [IsTotallyComplex F] (P : CoverPackage D S H A)
    (Ψ : P.tc.G → ℂ) (g' : P.tc.G)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) (hfinite : Γ.FiniteIndex)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hlevel : ∀ g : P.tc.G, ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F,
      𝔞 ≠ 0 ∧ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (P₀ Pτ : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        Ψ (h * (g'⁻¹ * nFin P ξ * g')) = Ψ h) ∧
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom ≤
        ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) ∧
      (((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom).relIndex
        (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) ≠ 0) ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        P₀ volume ∧ Bornology.IsBounded P₀ ∧ (0 < (volume P₀).toReal) ∧
      IsAddFundamentalDomain (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) Pτ volume := by
  sorry

/-- Constant-term integrands are periodic under the rational cusp translations. -/
theorem th_cusp_periodic [IsTotallyComplex F] (P : CoverPackage D S H A)
    (a : (InfinitePlace F → ℝ) → P.tc.G) (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    (hΓ : ∀ γ ∈ Γ, ∀ z, cuspClassical P a Ψ gj (γ • z) = cuspClassical P a Ψ gj z)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    ∀ μ ∈ ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ, ∀ x,
      cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F (μ + x) y) =
        cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
  sorry

/-- A zero integral descends from a finite-index period sublattice, including nonintegrable functions. -/
theorem th_cusp_part3 (Λ₀ Λ : AddSubgroup (InfinitePlace F → ℂ))
    (hle : Λ₀ ≤ Λ) (hindex : Λ₀.relIndex Λ ≠ 0)
    (P₀ Pτ : Set (InfinitePlace F → ℂ))
    (hP₀ : IsAddFundamentalDomain Λ₀ P₀ volume)
    (hPτ : IsAddFundamentalDomain Λ Pτ volume)
    (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : ∀ μ ∈ Λ, ∀ x, f (μ + x) = f x) (hzero : ∫ x in P₀, f x = 0) :
    ∫ x in Pτ, f x = 0 := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
