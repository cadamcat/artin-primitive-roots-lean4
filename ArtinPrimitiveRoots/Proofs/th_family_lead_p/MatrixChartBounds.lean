import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MatrixChartDerivatives

set_option autoImplicit false
open NumberField Matrix Topology
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1.Theta

private theorem partial_iteratedFDeriv_smooth
    {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s : Set E) (hs : IsOpen s) (φ : E × X → ℂ)
    (hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (s ×ˢ Set.univ))
    (n : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × X => iteratedFDeriv ℝ n (fun x => φ (p.1, x)) p.2)
      (s ×ˢ Set.univ) := by
  induction n with
  | zero =>
    convert hφ.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ X ℂ).symm : ℂ →L[ℝ] X [×0]→L[ℝ] ℂ) using 1 <;> rfl
  | succ n ih =>
    intro p hp
    have ihAt := ih.contDiffAt ((hs.prod isOpen_univ).mem_nhds hp)
    have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (E × X) × X => (q.1.1, q.2)) (p, p.2) := by fun_prop
    have hj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry (fun q : E × X =>
          fun x : X => iteratedFDeriv ℝ n (fun y => φ (q.1, y)) x)) (p, p.2) := by
      convert ihAt.comp (p, p.2) hmap using 1 <;> rfl
    have hD := hj.fderiv (g := fun q : E × X => q.2)
      (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
    have hDc := hD.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) ℂ).symm :
        _ →L[ℝ] X [×(n + 1)]→L[ℝ] ℂ)
    convert hDc.contDiffWithinAt using 1 <;> rfl

variable {F : Type} [Field F] [NumberField F]

/-- Partial left-root derivatives of a smooth matrix formula are uniformly bounded on
a compact set of root coordinates and invertible ambient matrix parameters. -/
theorem theta_matrix_chart_left_root_derivative_bounds
    (f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion)
    (n : ℕ) (Kx : Set (InfinitePlace F → ℂ)) (hKx : IsCompact Kx)
    (CM : Set (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ))
    (hCM : IsCompact CM) (hreg : CM ⊆ thetaMatrixRegion) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ M ∈ CM, ∀ x ∈ Kx,
      ‖iteratedFDeriv ℝ n
        (fun x : InfinitePlace F → ℂ =>
          f (fun w => (upperM ℂ (x w) : Matrix (Fin 2) (Fin 2) ℂ) * M w)) x‖ ≤ Cb := by
  let E := InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ
  let X := InfinitePlace F → ℂ
  let h : E × X → E := fun p w => !![1, p.2 w; 0, 1] * p.1 w
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [h, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals fun_prop
  have hregOpen : IsOpen (thetaMatrixRegion (F := F)) := by
    have ho (w : InfinitePlace F) : IsOpen {M : E | (M w).det ≠ 0} := by
      apply isOpen_ne_fun _ continuous_const
      simp only [Matrix.det_fin_two]
      fun_prop
    simpa only [thetaMatrixRegion, Set.ofPred_forall] using isOpen_iInter_of_finite ho
  have hmaps : Set.MapsTo h (thetaMatrixRegion ×ˢ Set.univ) thetaMatrixRegion := by
    intro p hp w
    change (!![1, p.2 w; 0, 1] * p.1 w).det ≠ 0
    rw [Matrix.det_mul]
    simpa [Matrix.det_fin_two] using hp.1 w
  let φ : E × X → ℂ := f ∘ h
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
      (thetaMatrixRegion ×ˢ Set.univ) := hf.comp hsmooth.contDiffOn hmaps
  have hpartial := partial_iteratedFDeriv_smooth thetaMatrixRegion hregOpen φ hφ n
  have hsub : CM ×ˢ Kx ⊆ thetaMatrixRegion ×ˢ Set.univ :=
    fun p hp => ⟨hreg hp.1, Set.mem_univ _⟩
  have hc : IsCompact
      ((fun p : E × X => iteratedFDeriv ℝ n (fun x => φ (p.1, x)) p.2) '' (CM ×ˢ Kx)) :=
    (hCM.prod hKx).image_of_continuousOn (hpartial.continuousOn.mono hsub)
  obtain ⟨C, hC⟩ := hc.isBounded.subset_closedBall (0 : _)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro M hM x hx
  have hmem := hC (Set.mem_image_of_mem _ (show (M, x) ∈ CM ×ˢ Kx from ⟨hM, hx⟩))
  have hbound : ‖iteratedFDeriv ℝ n (fun x => φ (M, x)) x‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hmem
  exact hbound.trans (le_max_left _ _)

end ArtinPrimitiveRoots.Proofs.majorant_sol
