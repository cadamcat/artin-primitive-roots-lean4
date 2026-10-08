import ArtinPrimitiveRoots.Theta.LocalInt

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
  sorry

/-- A continuous complex section is bounded by a spherical section at its real parameter. -/
theorem sectionC_norm_majorant (s : ℂ) (f : PGL2 ℂ → ℂ)
    (hf : IsSectionC s f) (hc : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : PGL2 ℂ,
      ‖f g‖ ≤ C * ‖sphC (s.re : ℂ) g‖ := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
