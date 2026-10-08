import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Eis
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.CentralKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Arithmetic
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.StrongApprox

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The positive-height branch of the frozen `aInf` definition. -/
def th_classical_archTerm (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : P.tc.G :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
    P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod

/-- Lift the upper-half-space section with identity components at all finite places. -/
theorem th_classical_arch_lift (P : CoverPackage D S H A)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    ∃ r : P.RP, P.q r = nInf P x * th_classical_archTerm P y hy ∧
      (∀ v, P.compF v r = 1) ∧ ∀ w, P.compC w r =
        QuotientGroup.mk (upperM ℂ (x w) * diagM ℂ
          (Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne'))) := by
  sorry

/-- Projective Iwasawa decomposition uses the full unitary compact. -/
theorem th_classical_pgl_reconstruction (g : PGL2 ℂ) :
    ∃ (x : ℂ) (y : ℝ) (hy : 0 < y) (k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      g = QuotientGroup.mk (upperM ℂ x * diagM ℂ
        (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')) * k) := by
  have hroots : ∀ u : ℂˣ, ∃ v : ℂˣ, v ^ Fintype.card (Fin 2) = u := by
    intro u
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℂ) (by decide : 0 < 2)
    have hv0 : v ≠ 0 := by
      intro hv0
      exact u.ne_zero (by simpa [hv0] using hv.symm)
    refine ⟨Units.mk0 v hv0, ?_⟩
    apply Units.ext
    simpa using hv
  obtain ⟨s, hs⟩ := Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots hroots g
  induction s using Quotient.inductionOn with
  | _ h =>
    change (QuotientGroup.mk (h : GL (Fin 2) ℂ) : PGL2 ℂ) = g at hs
    let z : Spec.H3 := QuotientGroup.mk h
    have hy : 0 < Spec.height z := by
      rw [Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos z
    let a : SL(2, ℂ) := Spec.ptMat (Spec.horiz z) (Spec.height z) hy
    have hpoint : (QuotientGroup.mk a : Spec.H3) = QuotientGroup.mk h := by
      simpa only [Spec.pt, dif_pos hy] using Spec.pt_horiz_height z
    let k : SL(2, ℂ) := a⁻¹ * h
    have hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hpoint)
    have hsection : (QuotientGroup.mk (a : GL (Fin 2) ℂ) : PGL2 ℂ) =
        QuotientGroup.mk (upperM ℂ (Spec.horiz z) * diagM ℂ
          (Units.mk0 (Spec.height z : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) := by
      have hroot : (Real.sqrt (Spec.height z) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
      change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨Units.mk0 (Real.sqrt (Spec.height z) : ℂ) hroot, ?_⟩
      ext i j
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      fin_cases i <;> fin_cases j
      all_goals
        simp [a, Matrix.diagonal, Matrix.scalar, Spec.ptMat, upperM, diagM,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
          Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
        <;> field_simp [hroot]
        <;> norm_num [Real.mul_self_sqrt hy.le]
        <;> rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
    refine ⟨Spec.horiz z, Spec.height z, hy, (k : GL (Fin 2) ℂ), hk, ?_⟩
    rw [← hs, QuotientGroup.mk_mul, ← hsection, ← QuotientGroup.mk_mul]
    apply congrArg (fun t : GL (Fin 2) ℂ => (QuotientGroup.mk t : PGL2 ℂ))
    change Matrix.SpecialLinearGroup.toGL h =
      Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL (a⁻¹ * h)
    rw [← map_mul, mul_inv_cancel_left]

/-- The Iwasawa coordinates of a special-linear translate are its actual hyperbolic coordinates. -/
theorem th_classical_sl_reconstruction (g : SL(2, ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y) :
    ∃ k : GL (Fin 2) ℂ,
      (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∃ hy' : 0 < Spec.height (g • Spec.pt x y),
        (QuotientGroup.mk (g : GL (Fin 2) ℂ) : PGL2 ℂ) *
            QuotientGroup.mk (upperM ℂ x * diagM ℂ
              (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) =
          QuotientGroup.mk (upperM ℂ (Spec.horiz (g • Spec.pt x y)) * diagM ℂ
            (Units.mk0 (Spec.height (g • Spec.pt x y) : ℂ)
              (Complex.ofReal_ne_zero.mpr hy'.ne')) * k) := by
  sorry

/-- The prescribed finite level, before applying the global central quotient. -/
def th_classical_finiteLevel (P : CoverPackage D S H A) (T0 : Finset (FinPlace F))
    (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ) (k : P.RP) : Prop :=
  (∀ w, P.compC w k = 1) ∧
    (∀ v ∈ T0, P.compF v k ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v k ∈ (P.tame v (fun h => hv (hT0 h))).Kmax

/-- Finite-component equality in the global cover allows the central tuples killed by `q`. -/
def th_classical_finiteEq (P : CoverPackage D S H A) (r s : P.RP) : Prop :=
  ∃ ζ : FinPlace F → rootsOfUnity 3 ℂ,
    (Function.mulSupport ζ).Finite ∧ (∏ᶠ v, ζ v) = 1 ∧
      ∀ v, P.compF v r = (P.loc v).z (ζ v) * P.compF v s

/-- Finite-adelic reduction, including the residual central phase in the representatives. -/
theorem th_classical_finite_components (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) :
    ∃ J : Finset P.RP, (∀ j ∈ J, ∀ w, P.compC w j = 1) ∧
      ∀ r : P.RP, ∃ γ : GL (Fin 2) F, ∃ j ∈ J, ∃ k : P.RP,
        th_classical_finiteLevel P T0 hT0 m k ∧
          th_classical_finiteEq P (P.ratRP γ * r) (j * k) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
