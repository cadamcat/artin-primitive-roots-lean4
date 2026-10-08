import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Eis
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.CentralKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Arithmetic
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.StrongApprox
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Determinant
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Projected

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
  classical
  obtain ⟨rN, hNq, hNF, hNC⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hN (v : FinPlace F) : P.compF v rN = 1 := by
    rw [hNF v]
    by_cases hv : v ∈ S.Sf <;> simp [hv]
  let u (w : InfinitePlace F) : ℂˣ :=
    Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')
  choose rA hAq hAF hAC using fun w => P.aS_components (S.atComplex w (u w))
  have hcompU (v : S.Sf) (w : InfinitePlace F) : S.compU v (S.atComplex w (u w)) = 1 := by
    apply Units.ext
    simp [SData.compU, SData.atComplex]
  have hcompC (w w' : InfinitePlace F) :
      S.compC w (S.atComplex w' (u w')) = if w' = w then u w else 1 := by
    by_cases h : w' = w
    · subst w'
      apply Units.ext
      simp [SData.compC, SData.atComplex]
    · have h' : w ≠ w' := fun he => h he.symm
      apply Units.ext
      simp [SData.compC, SData.atComplex, h, h']
  have hAfin (w : InfinitePlace F) (v : FinPlace F) : P.compF v (rA w) = 1 := by
    rw [hAF w v]
    by_cases hv : v ∈ S.Sf <;> simp [hv, hcompU, (P.loc v).a_one]
  have hdiag : diagM ℂ (1 : ℂˣ) = (1 : GL (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM]
  have hAinf (w' w : InfinitePlace F) : P.compC w (rA w') =
      if w' = w then QuotientGroup.mk (diagM ℂ (u w)) else 1 := by
    rw [hAC w' w, hcompC]
    by_cases h : w' = w <;> simp [h, hdiag]
  have single (l : List (InfinitePlace F)) (hl : l.Nodup) (w : InfinitePlace F)
      (hw : w ∈ l) (a : PGL2 ℂ) : (l.map fun w' => if w' = w then a else 1).prod = a := by
    induction l with
    | nil => simp at hw
    | cons b l ih =>
      obtain ⟨hb, hl⟩ := List.nodup_cons.mp hl
      simp only [List.mem_cons] at hw
      by_cases h : b = w
      · subst b
        have htail : (l.map fun w' => if w' = w then a else 1).prod = 1 := by
          apply List.prod_eq_one
          intro z hz
          obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hz
          have hne : w' ≠ w := by
            intro he
            subst w'
            exact hb hw'
          simp [hne]
        simp [htail]
      · have hw' : w ∈ l := by
          obtain hEq | hmem := hw
          · exact (h hEq.symm).elim
          · exact hmem
        simp only [List.map_cons, List.prod_cons, if_neg h, one_mul]
        exact ih hl hw'
  let rArch : P.RP := ((Finset.univ : Finset (InfinitePlace F)).toList.map rA).prod
  have hrq : P.q rArch = th_classical_archTerm P y hy := by
    rw [show rArch = ((Finset.univ : Finset (InfinitePlace F)).toList.map rA).prod from rfl,
      map_list_prod]
    simp only [List.map_map]
    change ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w => P.q (rA w)).prod =
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w => P.tc.aS (S.atComplex w (u w))).prod
    simp only [hAq]
  have hrF (v : FinPlace F) : P.compF v rArch = 1 := by
    rw [show rArch = ((Finset.univ : Finset (InfinitePlace F)).toList.map rA).prod from rfl,
      map_list_prod]
    simp only [List.map_map]
    change ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w => P.compF v (rA w)).prod = 1
    apply List.prod_eq_one
    intro z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact hAfin w v
  have hrC (w : InfinitePlace F) : P.compC w rArch = QuotientGroup.mk (diagM ℂ (u w)) := by
    rw [show rArch = ((Finset.univ : Finset (InfinitePlace F)).toList.map rA).prod from rfl,
      map_list_prod]
    simp only [List.map_map]
    change ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w' => P.compC w (rA w')).prod = _
    simp only [hAinf]
    exact single (Finset.univ : Finset (InfinitePlace F)).toList
      (Finset.nodup_toList _) w (Finset.mem_toList.mpr (Finset.mem_univ w)) _
  refine ⟨rN * rArch, ?_, ?_, ?_⟩
  · rw [map_mul, hNq, hrq]
    rfl
  · intro v
    rw [map_mul, hN v, hrF v, one_mul]
  · intro w
    rw [map_mul, hNC w, hrC w, ← QuotientGroup.mk_mul]

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
  classical
  let C := {ζ : rootsOfUnity 3 ℂ // ∃ h : P.RP,
    (∀ w, P.compC w h = 1) ∧ P.q h = P.tc.z ζ}
  let _ : Fintype C := Fintype.ofFinite C
  choose s hsC hsQ using fun ζ : C => ζ.2
  obtain ⟨J0, hJ0, hred⟩ := th_classical_projected_finite_components P T0 hT0 m hm
  let J : Finset P.RP := (Finset.univ ×ˢ J0).image (fun p : C × P.RP => s p.1 * p.2)
  refine ⟨J, ?_, ?_⟩
  · intro j hj w
    obtain ⟨⟨ζ, j0⟩, hp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨_, hj0⟩ := Finset.mem_product.mp hp
    rw [map_mul, hsC ζ w, hJ0 j0 hj0 w, one_mul]
  · intro r
    obtain ⟨γ, j0, hj0, k, hk, hp⟩ := hred r
    let r' : P.RP := P.ratRP γ * r
    obtain ⟨x, hxF, hxC⟩ := P.comp_surj (fun v => P.compF v r') (fun _ => 1) (P.comp_restricted r')
    let h : P.RP := x * (j0 * k)⁻¹
    have hhF (v : FinPlace F) : (P.loc v).pr (P.compF v h) = 1 := by
      simp only [h, map_mul, map_inv, hxF]
      change (P.loc v).pr (P.compF v r') *
        ((P.loc v).pr (P.compF v j0) * (P.loc v).pr (P.compF v k))⁻¹ = 1
      have hp' : (P.loc v).pr (P.compF v r') =
          (P.loc v).pr (P.compF v j0) * (P.loc v).pr (P.compF v k) := by
        simpa only [r', map_mul] using hp v
      rw [hp']
      exact mul_inv_cancel _
    have hhC (w : InfinitePlace F) : P.compC w h = 1 := by
      simp only [h, map_mul, map_inv, hxC, hJ0 j0 hj0 w, hk.1 w, one_mul, inv_one]
    obtain ⟨ζ, hζ, _⟩ := th_classical_central_kernel P h hhF hhC
    let ζC : C := ⟨ζ, h, hhC, hζ⟩
    have hqx : P.q x = P.q ((s ζC * j0) * k) := by
      have hhq : P.q x * (P.q (j0 * k))⁻¹ = P.q (s ζC) := by
        simpa only [h, map_mul, map_inv] using hζ.trans (hsQ ζC).symm
      have hxq := mul_inv_eq_iff_eq_mul.mp hhq
      simpa only [map_mul, mul_assoc] using hxq
    obtain ⟨ξ, hξfin, hξprod, hξF, _⟩ := (P.q_eq x ((s ζC * j0) * k)).mp hqx
    refine ⟨γ, s ζC * j0, Finset.mem_image.mpr ⟨(ζC, j0),
      Finset.mem_product.mpr ⟨Finset.mem_univ ζC, hj0⟩, rfl⟩, k, hk,
      ξ, hξfin, hξprod, ?_⟩
    intro v
    rw [← hxF v]
    exact hξF v

end ArtinPrimitiveRoots.A1.Theta
