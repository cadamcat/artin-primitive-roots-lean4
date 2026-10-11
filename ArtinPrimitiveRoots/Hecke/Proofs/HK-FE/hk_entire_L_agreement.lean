import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Entire uncompleted H1 function and exact series agreement on its convergence half-plane.
Uses H1 rayMellinAgreement and reciprocal normalization. -/
theorem hk_entire_L_agreement [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) :
    Differentiable ℂ (hkEntireL ψ) ∧ ∀ s : ℂ, 1 < s.re → hkEntireL ψ s = LSeriesRay ψ s := by
  classical
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  letI : Fintype (RayClassGroup m) := Fintype.ofFinite _
  let R := hkRayRepresentatives m
  have hdiff : Differentiable ℂ (hkEntireL ψ) := by
    change Differentiable ℂ
      (fun s : ℂ => rayMellinNormalization K s *
        (rayCharacterFEPair R ψ).Λ (s / 2))
    exact (differentiable_rayMellinNormalization K).mul
      ((rayCharacter_completed_entire R ψ hψ).comp (differentiable_id.div_const 2))
  refine ⟨hdiff, ?_⟩
  intro s hs
  apply LSeriesRay_eq_of_entire_real_agreement ψ (hkEntireL ψ) hdiff ?_ s hs
  intro σ hσ
  have hσ' : (1 : ℝ) / 2 < (((σ : ℂ) / 2).re) := by
    norm_num [Complex.div_re]
    linarith
  rw [hkEntireL, rayCharacterFEPair_Λ_eq_sum R ψ hσ']
  have hpartial : ∀ C : RayClassGroup m,
      (rayFEPair m (R.ideal C) (R.coprime C)).Λ ((σ : ℂ) / 2) =
        rayMellinFactor K (σ : ℂ) * rayClassPartialZeta C (σ : ℂ) := by
    intro C
    let J : (Ideal (𝓞 K))⁰ :=
      ⟨R.ideal C, mem_nonZeroDivisors_of_ne_zero (R.coprime C).1⟩
    have hclass : (rayClass m (R.ideal C) (R.coprime C))⁻¹ = C := by
      rw [R.class_eq C]
      exact inv_inv C
    simpa only [J, hclass] using
      (rayFEPair_Λ_eq_partialZeta_real m J (R.coprime C) (s := σ) hσ)
  simp_rw [hpartial]
  have hsum :
      (∑ C : RayClassGroup m,
        (ψ C : ℂ) * (rayMellinFactor K (σ : ℂ) * rayClassPartialZeta C (σ : ℂ))) =
      rayMellinFactor K (σ : ℂ) *
        ∑ C : RayClassGroup m, (ψ C : ℂ) * rayClassPartialZeta C (σ : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [hsum, ← mul_assoc, rayMellinNormalization_mul_factor K (by simpa using hσ),
    one_mul, ← LSeriesRay_eq_rayClassPartialZeta_sum ψ hσ]

end ArtinPrimitiveRoots.Hecke
