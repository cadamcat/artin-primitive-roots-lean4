import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Spec.Interface
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

open scoped Classical Matrix

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- The image of the complex unitary matrices in the projective group. -/
def complexUnitary : Set (PGL2 ℂ) :=
  QuotientGroup.mk '' {k : GL (Fin 2) ℂ |
    (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}

/-- Complex Iwasawa decomposition, with a unitary final factor. -/
theorem complex_iwasawa (g : PGL2 ℂ) :
    ∃ (x : ℂ) (y : ℂˣ) (k : PGL2 ℂ),
      k ∈ complexUnitary ∧ g = nC x * aC y * k := by
  classical
  refine Quotient.inductionOn g ?_
  intro a
  let c : ℂ := a 1 0
  let d : ℂ := a 1 1
  have hdet : a 0 0 * d - a 0 1 * c ≠ 0 := by
    simpa [c, d, Matrix.det_fin_two] using Matrix.GeneralLinearGroup.det_ne_zero a
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    exact hdet (by simp [h.1, h.2])
  have hpos : 0 < Complex.normSq c + Complex.normSq d := by
    rcases hcd with hc | hd
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hc) (Complex.normSq_nonneg d)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg c) (Complex.normSq_pos.mpr hd)
  let r : ℝ := Real.sqrt (Complex.normSq c + Complex.normSq d)
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hnormr : Complex.normSq (r : ℂ) = Complex.normSq c + Complex.normSq d := by
    rw [Complex.normSq_ofReal]
    exact Real.mul_self_sqrt hpos.le
  have henergy : c * star c + d * star d = (r : ℂ) ^ 2 := by
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_add]
    exact_mod_cast (Real.sq_sqrt hpos.le).symm
  let u : ℂ := c / (r : ℂ)
  let v : ℂ := d / (r : ℂ)
  have hnormrow : Complex.normSq u + Complex.normSq v = 1 := by
    dsimp [u, v]
    rw [Complex.normSq_div, Complex.normSq_div, hnormr, ← add_div, div_self hpos.ne']
  have hrow : u * star u + v * star v = 1 := by
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_add]
    exact_mod_cast hnormrow
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![star v, -star u; u, v]
  have hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, mul_comm, add_comm] using hrow
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
      ring
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
      ring
    · simpa [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using hrow
  let k : GL (Fin 2) ℂ := Unitary.toUnits ⟨M, hM⟩
  let t : ℂˣ := Units.mk0 (r : ℂ) hr0
  let x : ℂ := (a 0 0 * star c + a 0 1 * star d) / (r : ℂ) ^ 2
  let y : ℂˣ := Units.mk0 ((a 0 0 * d - a 0 1 * c) / (r : ℂ) ^ 2)
    (div_ne_zero hdet (pow_ne_zero 2 hr0))
  have htri : a * k⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) t * upperM ℂ x * diagM ℂ y := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((a : Matrix (Fin 2) (Fin 2) ℂ) * star M) i j =
      ((Matrix.scalar (Fin 2) (r : ℂ) * !![1, x; 0, 1]) * !![(y : ℂ), 0; 0, 1]) i j
    fin_cases i <;> fin_cases j
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, x, y, u, v]
      field_simp
      ring
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, x, y, u, v]
      field_simp
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, u, v, c, d]
      ring
    · simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, u, v, c, d]
      field_simp
      simp only [c, d, Complex.star_def] at henergy
      linear_combination henergy
  have hfactor : a = Matrix.GeneralLinearGroup.scalar (Fin 2) t * upperM ℂ x * diagM ℂ y * k := by
    calc
      a = (a * k⁻¹) * k := by group
      _ = _ := by rw [htri]
  have hscalar : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : PGL2 ℂ) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨t, rfl⟩
  refine ⟨x, y, QuotientGroup.mk k, ⟨k, hM, rfl⟩, ?_⟩
  calc
    QuotientGroup.mk a = QuotientGroup.mk
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t * upperM ℂ x * diagM ℂ y * k) :=
      congrArg QuotientGroup.mk hfactor
    _ = nC x * aC y * QuotientGroup.mk k := by
      simp only [QuotientGroup.mk_mul, hscalar, one_mul, nC, aC]

/-- Unitary representatives form a compact set and normalize the spherical section. -/
theorem complex_unitary_control :
    IsCompact complexUnitary ∧ ∀ (s : ℂ) (k : PGL2 ℂ),
      k ∈ complexUnitary → sphC s k = 1 := by
  classical
  have hclosed : IsClosed (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        {U | U * star U = 1} := by
      ext U
      exact Matrix.mem_unitaryGroup_iff
    rw [heq]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.star) continuous_const
  have hcompact : IsCompact (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hclosed
    intro U hU
    change ∀ i j, U i j ∈ Metric.closedBall (0 : ℂ) 1
    intro i j
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      entry_norm_bound_of_unitary hU i j
  let : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) :=
    isCompact_iff_compactSpace.mp hcompact
  have hcont : Continuous
      (fun U : Matrix.unitaryGroup (Fin 2) ℂ => (Unitary.toUnits U : GL (Fin 2) ℂ)) :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have himage : complexUnitary = Set.range
      (fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
        (QuotientGroup.mk (Unitary.toUnits U) : PGL2 ℂ)) := by
    ext k
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨(a : Matrix (Fin 2) (Fin 2) ℂ), ha⟩, ?_⟩
      apply congrArg QuotientGroup.mk
      exact Units.ext rfl
    · rintro ⟨U, rfl⟩
      exact ⟨Unitary.toUnits U, U.property, rfl⟩
  refine ⟨himage ▸ isCompact_range (QuotientGroup.continuous_mk.comp hcont), ?_⟩
  rintro s k ⟨a, ha, rfl⟩
  have hdet : ‖(a : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary ha)
  have hrow : ‖a 1 0‖ ^ 2 + ‖a 1 1‖ ^ 2 = 1 := by
    have heq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
      (Unitary.mul_star_self_of_mem ha)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.star_def, Complex.mul_conj, ← Complex.ofReal_add, Matrix.one_apply_eq] at heq
    simp only [Complex.normSq_eq_norm_sq] at heq
    exact_mod_cast heq
  simp only [sphC_mk, sphericalC, hdet, hrow, div_self one_ne_zero,
    Complex.ofReal_one, Complex.one_cpow]

/-- A continuous complex section is bounded by a spherical section at its real parameter. -/
theorem sectionC_norm_majorant (s : ℂ) (f : PGL2 ℂ → ℂ)
    (hf : IsSectionC s f) (hc : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : PGL2 ℂ,
      ‖f g‖ ≤ C * ‖sphC (s.re : ℂ) g‖ := by
  obtain ⟨C, hC⟩ := complex_unitary_control.1.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro g
  obtain ⟨x, y, k, hk, rfl⟩ := complex_iwasawa g
  simp only [nC, aC]
  rw [hf x y k, (sphC_isSection (s.re : ℂ)).1 x y k,
    complex_unitary_control.2 (s.re : ℂ) k hk, mul_one, norm_mul]
  have hpos : 0 < Complex.normSq (y : ℂ) :=
    Complex.normSq_pos.mpr (Units.ne_zero y)
  have hnorm : ‖(Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ =
      ‖(Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + (s.re : ℂ))‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  rw [hnorm, mul_comm _ ‖f k‖]
  exact mul_le_mul_of_nonneg_right ((hC k hk).trans (le_max_left _ _)) (norm_nonneg _)

/-- A projective complex matrix determines the hyperbolic point whose height is its spherical norm. -/
theorem complex_spherical_height_point (h : PGL2 ℂ) :
    ∃ z : ArtinPrimitiveRoots.A1.Spec.H3,
      ∀ (σ : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ),
        ‖sphC (σ : ℂ) (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) * h)‖ =
          ArtinPrimitiveRoots.A1.Spec.height (γ • z) ^ (1 + 2 * σ) := by
  classical
  let e : PGL2 ℂ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ :=
    Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e h)
  have hu' : (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL u) : PGL2 ℂ) = h := by
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk u) = h
    rw [hu]
    exact e.symm_apply_apply h
  have hheight (v : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk v) =
        (‖v 1 0‖ ^ 2 + ‖v 1 1‖ ^ 2)⁻¹ := by
    simp [ArtinPrimitiveRoots.A1.Spec.height, ArtinPrimitiveRoots.A1.Spec.herm,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  have hpos (v : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      0 < ‖v 1 0‖ ^ 2 + ‖v 1 1‖ ^ 2 := by
    by_cases h10 : v 1 0 = 0
    · have h11 : v 1 1 ≠ 0 := by
        intro h11
        have hvdet := v.property
        rw [Matrix.det_fin_two, h10, h11] at hvdet
        norm_num at hvdet
      positivity
    · positivity
  refine ⟨QuotientGroup.mk u, ?_⟩
  intro σ γ
  have hprod : (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) : PGL2 ℂ) * h =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL (γ * u)) := by
    rw [← hu', map_mul, QuotientGroup.mk_mul]
  rw [hprod]
  change ‖sphC (σ : ℂ) (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL (γ * u)))‖ =
    ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk (γ * u)) ^ (1 + 2 * σ)
  rw [hheight]
  simp only [sphC_mk, sphericalC, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    (γ * u).property, norm_one, one_div]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr (hpos (γ * u)))]
  simp

end ArtinPrimitiveRoots.A1.Theta
