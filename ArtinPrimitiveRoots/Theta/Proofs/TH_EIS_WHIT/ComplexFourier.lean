import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.ComplexIntegral

set_option autoImplicit false
open MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A nonzero complex Fourier frequency is a torus translation of the Jacquet integral. -/
theorem whit_complex_fourier_dilation (s : ℂ) (f : PGL2 ℂ → ℂ)
    (hf : IsSectionC s f) (b : ℂˣ) (g : PGL2 ℂ) :
    (∫ u : ℂ, psiC (-((b : ℂ) * u)) * f (wC * nC u * g)) =
      ((Complex.normSq (b : ℂ) : ℂ) ^ (s - (1 : ℂ) / 2)) *
        jacquetC (rtr (aC b * g) f) := by
  classical
  have hmat (u : ℂ) : weylM ℂ * upperM ℂ u * diagM ℂ b =
      Matrix.GeneralLinearGroup.scalar (Fin 2) b *
        (diagM ℂ b⁻¹ * weylM ℂ * upperM ℂ (u / (b : ℂ))) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, weylM, upperM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;>
      field_simp [b.ne_zero] <;> ring
  have hscalar : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b) :
      PGL2 ℂ) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨b, rfl⟩
  have hgroup (u : ℂ) : wC * nC u * (aC b * g) =
      aC b⁻¹ * (wC * nC (u / (b : ℂ)) * g) := by
    have h := congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ)) (hmat u)
    have h' : wC * nC u * aC b = aC b⁻¹ * wC * nC (u / (b : ℂ)) := by
      simpa only [QuotientGroup.mk_mul, hscalar, one_mul, aC, wC, nC] using h
    calc
      _ = (wC * nC u * aC b) * g := by group
      _ = _ := by rw [h']; group
  let R : ℝ := ‖(b : ℂ)‖
  let q : ℝ := Complex.normSq (b : ℂ)
  have hR : 0 < R := norm_pos_iff.mpr b.ne_zero
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hq : 0 < q := Complex.normSq_pos.mpr b.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : q = R ^ 2 := Complex.normSq_eq_norm_sq (b : ℂ)
  have hphase : ‖(R : ℂ) / (b : ℂ)‖ = 1 := by simp [R, b.ne_zero]
  let ρ : Circle := ⟨(R : ℂ) / (b : ℂ), mem_sphere_zero_iff_norm.mpr hphase⟩
  have hchange (u : ℂ) : u / (b : ℂ) = rotation ρ (R⁻¹ • u) := by
    change u / (b : ℂ) = (ρ : ℂ) * (R⁻¹ • u)
    rw [RCLike.real_smul_eq_coe_mul]
    dsimp only [ρ]
    rw [RCLike.ofReal_inv]
    change u / (b : ℂ) = (R : ℂ) / (b : ℂ) * ((R : ℂ)⁻¹ * u)
    field_simp [hRC, b.ne_zero]
  let kernel : ℂ → ℂ := fun u => psiC (-((b : ℂ) * u)) * f (wC * nC u * g)
  have hscale : (∫ u : ℂ, kernel (u / (b : ℂ))) = (q : ℂ) * ∫ u : ℂ, kernel u := by
    calc
      _ = ∫ u : ℂ, kernel (rotation ρ (R⁻¹ • u)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => congrArg kernel (hchange u))
      _ = (R ^ 2 : ℝ) • ∫ u : ℂ, kernel (rotation ρ u) := by
        simpa only [Complex.finrank_real_complex] using
          Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
            (fun u : ℂ => kernel (rotation ρ u)) hR.le
      _ = (R ^ 2 : ℝ) • ∫ u : ℂ, kernel u := by
        rw [MeasureTheory.integral_comp (rotation ρ) kernel]
      _ = _ := by rw [← hqR, RCLike.real_smul_eq_coe_mul]; rfl
  let C : ℂ := (Complex.normSq (b⁻¹ : ℂˣ) : ℂ) ^ ((1 : ℂ) / 2 + s)
  have hsection (h : PGL2 ℂ) : f (aC b⁻¹ * h) = C * f h := by
    have hzero : upperM ℂ 0 = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperM]
    have hsec := hf 0 b⁻¹ h
    change f (QuotientGroup.mk (upperM ℂ 0) * aC b⁻¹ * h) = C * f h at hsec
    simpa only [hzero, QuotientGroup.mk_one, one_mul] using hsec
  have hpoint (u : ℂ) :
      psiC (-u) * f (wC * nC u * (aC b * g)) = C * kernel (u / (b : ℂ)) := by
    rw [hgroup, hsection]
    have hbu : (b : ℂ) * (u / (b : ℂ)) = u := by field_simp
    simp only [kernel, hbu]
    ring
  have hbasePow : C = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) := by
    dsimp only [C]
    rw [Units.val_inv_eq_inv_val, Complex.normSq_inv, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hq.le ((1 : ℂ) / 2 + s), ← Complex.cpow_neg]
  have hcoef : C * (q : ℂ) = (q : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    calc
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) * (q : ℂ) ^ (1 : ℂ) := by
        rw [hbasePow, Complex.cpow_one]
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s) + 1) :=
        (Complex.cpow_add _ _ hqC).symm
      _ = _ := by congr 1; ring
  have hW : jacquetC (rtr (aC b * g) f) =
      (q : ℂ) ^ ((1 : ℂ) / 2 - s) * ∫ u : ℂ, kernel u := by
    calc
      _ = ∫ u : ℂ, psiC (-u) * f (wC * nC u * (aC b * g)) := rfl
      _ = ∫ u : ℂ, C * kernel (u / (b : ℂ)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = C * ∫ u : ℂ, kernel (u / (b : ℂ)) := integral_const_mul _ _
      _ = (C * (q : ℂ)) * ∫ u : ℂ, kernel u := by rw [hscale]; ring
      _ = _ := by rw [hcoef]
  change (∫ u : ℂ, kernel u) =
    (q : ℂ) ^ (s - (1 : ℂ) / 2) * jacquetC (rtr (aC b * g) f)
  rw [hW, ← mul_assoc, ← Complex.cpow_add _ _ hqC]
  have hexp : (s - (1 : ℂ) / 2) + ((1 : ℂ) / 2 - s) = 0 := by ring
  rw [hexp, Complex.cpow_zero, one_mul]

end ArtinPrimitiveRoots.A1.Theta
