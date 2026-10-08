import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ArchMatrixResidue
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields

set_option autoImplicit false
open NumberField Matrix Topology
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem theta_root_step_matrix_chart {P : CoverPackage D S H A}
    (T0 : Finset (FinPlace F)) (hsub : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (g : P.tc.G) (Ψ : P.tc.G → ℂ)
    (f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion)
    (hrep : ∀ M : InfinitePlace F → GL (Fin 2) ℂ,
      ∀ k ∈ levelSet P T0 hsub m,
        Ψ (P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * g * k) =
          f (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)))
    (w : InfinitePlace F) (a : ℤ) :
    ∃ f' : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' thetaMatrixRegion ∧
      ∀ M : InfinitePlace F → GL (Fin 2) ℂ,
        ∀ k ∈ levelSet P T0 hsub m,
          thetaRootStep w a Ψ
            (P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * g * k) =
              f' (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) := by
  let E := InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ
  obtain ⟨rg, hrg⟩ := P.q_surj g
  have hreps (v : InfinitePlace F) : ∃ A : GL (Fin 2) ℂ,
      (QuotientGroup.mk A : PGL2 ℂ) = P.compC v rg := Quotient.mk_surjective _
  choose A hA using hreps
  let u : ℂ → InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ :=
    fun z v => !![1, (Pi.single w z : InfinitePlace F → ℂ) v; 0, 1]
  let h : E × ℂ → E := fun p v =>
    p.1 v * (A v : Matrix (Fin 2) (Fin 2) ℂ) * u p.2 v *
      ((A v)⁻¹ : GL (Fin 2) ℂ)
  let U : Set (E × ℂ) := {p | p.1 ∈ thetaMatrixRegion}
  have hregOpen : IsOpen (thetaMatrixRegion (F := F)) := by
    have ho (v : InfinitePlace F) : IsOpen {M : E | (M v).det ≠ 0} := by
      apply isOpen_ne_fun _ continuous_const
      simp only [Matrix.det_fin_two]
      fun_prop
    simpa only [thetaMatrixRegion, Set.ofPred_forall] using isOpen_iInter_of_finite ho
  have hU : IsOpen U := hregOpen.preimage continuous_fst
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := by
    apply contDiff_pi.mpr
    intro v
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [h, u, Matrix.mul_apply, Fin.sum_univ_two]
    by_cases hv : v = w
    · subst v
      simp only [Pi.single_eq_same]
      fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      all_goals fun_prop
    · simp only [Pi.single_eq_of_ne hv]
      fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      all_goals fun_prop
  have hmaps : Set.MapsTo h U thetaMatrixRegion := by
    intro p hp v
    change (p.1 v * (A v : Matrix (Fin 2) (Fin 2) ℂ) * u p.2 v *
      ((A v)⁻¹ : GL (Fin 2) ℂ)).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    have hu : (u p.2 v).det = 1 := by simp [u, Matrix.det_fin_two]
    rw [hu, mul_one]
    exact mul_ne_zero (mul_ne_zero (hp v) (A v).det_ne_zero) ((A v)⁻¹).det_ne_zero
  let φ : E × ℂ → ℂ := f ∘ h
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ U :=
    hf.comp hsmooth.contDiffOn hmaps
  let ins : E → E × ℂ := fun M => (M, 0)
  have hins : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ins :=
    contDiff_id.prodMk contDiff_const
  have hinsU : Set.MapsTo ins thetaMatrixRegion U := fun _ hM => hM
  let f' : E → ℂ := fun M => fderiv ℝ φ (M, 0) (0, (1 : ℂ)) -
    (a : ℂ) * Complex.I * fderiv ℝ φ (M, 0) (0, Complex.I)
  have hdir (z : ℂ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun M : E => fderiv ℝ φ (M, 0) (0, z)) thetaMatrixRegion := by
    have hd := (hφ.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (contDiffOn_const (c := ((0 : E), z)))
    exact hd.comp hins.contDiffOn hinsU
  refine ⟨f', (hdir 1).sub (contDiffOn_const.mul (hdir Complex.I)), ?_⟩
  intro M k hk
  have hcurve (z : ℂ) :
      Ψ (P.q (thetaArchRP P (fun v => QuotientGroup.mk (M v))) * g * k *
        nInf P (Pi.single w z)) = φ ((fun v => (M v : Matrix (Fin 2) (Fin 2) ℂ)), z) := by
    have hk0 := hk
    obtain ⟨rk, hrk, hrkC, -⟩ := hk0
    let Mt : InfinitePlace F → GL (Fin 2) ℂ := fun v =>
      M v * A v * upperM ℂ ((Pi.single w z : InfinitePlace F → ℂ) v) * (A v)⁻¹
    have hgroup : thetaArchRP P (fun v => QuotientGroup.mk (M v)) * rg * rk *
        thetaArchRP P (fun v => QuotientGroup.mk
          (upperM ℂ ((Pi.single w z : InfinitePlace F → ℂ) v))) =
        thetaArchRP P (fun v => QuotientGroup.mk (Mt v)) * rg * rk := by
      apply P.comp_ext
      · intro v
        simp only [map_mul, thetaArchRP_compF, one_mul, mul_one]
      · intro v
        simp only [map_mul, thetaArchRP_compC, hrkC, mul_one, Mt,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, hA]
        group
    have hqgroup := congrArg P.q hgroup
    simp only [map_mul, hrg, hrk, thetaArchRP_nInf] at hqgroup
    rw [hqgroup, hrep Mt k hk]
    rfl
  let insL : ℂ →L[ℝ] (E × ℂ) :=
    (0 : ℂ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℂ)
  have hinsL (z : ℂ) : insL z = (0, z) := by simp [insL]
  have hderiv (v : ℂ) :
      fderiv ℝ (fun z : ℂ => Ψ
        (P.q (thetaArchRP P (fun v => QuotientGroup.mk (M v))) * g * k *
          nInf P (Pi.single w z))) 0 v =
        fderiv ℝ φ ((fun v => (M v : Matrix (Fin 2) (Fin 2) ℂ)), 0) (0, v) := by
    let p : E × ℂ := ((fun v => (M v : Matrix (Fin 2) (Fin 2) ℂ)), 0)
    have hp : p ∈ U := fun v => (M v).det_ne_zero
    have hD := (hφ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    have hC : fderiv ℝ (fun z : ℂ => p + insL z) 0 = insL := by
      convert (insL.hasFDerivAt.const_add p).fderiv using 1 <;> rfl
    have hCd := ((insL.hasFDerivAt (x := (0 : ℂ))).const_add p).differentiableAt
    calc
      _ = fderiv ℝ (fun z : ℂ => φ (p + insL z)) 0 v := by
        apply congrArg (fun f0 : ℂ → ℂ => fderiv ℝ f0 0 v)
        funext z
        simpa [p, hinsL] using hcurve z
      _ = ((fderiv ℝ φ (p + insL 0)).comp
          (fderiv ℝ (fun z : ℂ => p + insL z) 0)) v := by
        change fderiv ℝ (φ ∘ (fun z : ℂ => p + insL z)) 0 v = _
        rw [fderiv_comp 0 (by convert hD using 1 <;> simp only [map_zero, add_zero]) hCd]
        rfl
      _ = _ := by
        simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
        apply congrArg (fderiv ℝ φ p)
        convert congrArg (fun d : ℂ →L[ℝ] (E × ℂ) => d v) hC using 1 <;> rfl
  change fderiv ℝ (fun z : ℂ => Ψ
      (P.q (thetaArchRP P (fun v => QuotientGroup.mk (M v))) * g * k *
        nInf P (Pi.single w z))) 0 1 -
    (a : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => Ψ
      (P.q (thetaArchRP P (fun v => QuotientGroup.mk (M v))) * g * k *
        nInf P (Pi.single w z))) 0 Complex.I = _
  rw [hderiv 1, hderiv Complex.I]

/-- Each finite right-root derivative fold has a smooth ambient matrix formula at the
same finite level as the reconstructed residue. -/
theorem theta_residue_matrix_chart_derivatives
    [IsTotallyComplex F] {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (a : InfinitePlace F → ℤ) (g : P.tc.G) :
    ∃ f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion ∧
      ∀ M : InfinitePlace F → GL (Fin 2) ℂ,
        ∀ k ∈ levelSet P I.T0 C.hsub C.m,
          thetaFamilyDeriv P a R.theta
            (P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * g * k) =
              f (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hfold (ws : List (InfinitePlace F)) :
      ∃ f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ,
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion ∧
        ∀ M : InfinitePlace F → GL (Fin 2) ℂ,
          ∀ k ∈ levelSet P I.T0 C.hsub C.m,
            (ws.foldr (fun w acc => thetaRootStep w (a w) acc) R.theta)
              (P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * g * k) =
                f (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) := by
    induction ws with
    | nil => exact theta_residue_arch_matrix_representation R g
    | cons w ws ih =>
      obtain ⟨f, hf, hrep⟩ := ih
      exact theta_root_step_matrix_chart I.T0 C.hsub C.m g
        (ws.foldr (fun w acc => thetaRootStep w (a w) acc) R.theta) f hf hrep w (a w)
  exact hfold (Finset.univ : Finset (InfinitePlace F)).toList

end ArtinPrimitiveRoots.Proofs.majorant_sol
