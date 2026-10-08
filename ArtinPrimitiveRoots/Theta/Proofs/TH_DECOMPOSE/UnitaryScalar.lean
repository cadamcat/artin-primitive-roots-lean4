import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.ScalarAnalytic

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

/-- The spherical complex scalar is invariant under right unitary multiplication. -/
theorem sphC_right_unitary (s : ℂ) (g : PGL2 ℂ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    sphC s (g * QuotientGroup.mk k) = sphC s g := by
  have hden_eq (a : Matrix (Fin 2) (Fin 2) ℂ) :
      ‖a 1 0‖ ^ 2 + ‖a 1 1‖ ^ 2 = ((a * star a) 1 1).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq]
  have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) *
      star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hdstar : Matrix.det (star (k : Matrix (Fin 2) (Fin 2) ℂ)) =
      star (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  have hdet : Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) *
      star (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    calc
      _ = Matrix.det ((k : Matrix (Fin 2) (Fin 2) ℂ) *
          star (k : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [Matrix.det_mul, hdstar]
      _ = 1 := by rw [hk']; simp
  have hnorm : ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hdet
    simpa only [norm_mul, norm_star, norm_one, sq] using h
  have hdetnorm : ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    have hnonneg : 0 ≤ ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_nonneg _
    nlinarith
  let a := Quotient.out g
  have ha : QuotientGroup.mk a = g := Quotient.out_eq _
  have hden : ‖(a * k : GL (Fin 2) ℂ).val 1 0‖ ^ 2 +
      ‖(a * k : GL (Fin 2) ℂ).val 1 1‖ ^ 2 =
      ‖a.val 1 0‖ ^ 2 + ‖a.val 1 1‖ ^ 2 := by
    rw [hden_eq, hden_eq]
    change ((((a : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) *
      star ((a : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) 1 1).re = _
    rw [star_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℂ)
        (star (k : Matrix (Fin 2) (Fin 2) ℂ)) (star (a : Matrix (Fin 2) (Fin 2) ℂ)), hk']
    simp
  have hnum : ‖(a * k : GL (Fin 2) ℂ).val.det‖ = ‖a.val.det‖ := by
    change ‖Matrix.det ((a : Matrix (Fin 2) (Fin 2) ℂ) *
      (k : Matrix (Fin 2) (Fin 2) ℂ))‖ = _
    rw [Matrix.det_mul, norm_mul, hdetnorm, mul_one]
  have hscalar : sphericalC s (a * k) = sphericalC s a := by
    unfold sphericalC
    rw [hnum, hden]
  calc
    _ = sphC s (QuotientGroup.mk (a * k)) := by rw [← ha, QuotientGroup.mk_mul]
    _ = sphericalC s (a * k) := sphC_mk s (a * k)
    _ = sphericalC s a := hscalar
    _ = sphC s g := by rw [← ha, sphC_mk]

end ArtinPrimitiveRoots.A1.Theta
