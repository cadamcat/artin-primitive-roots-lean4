import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_class_invariance
import ArtinPrimitiveRoots.Proofs.hkfe_mellin_p.WeightedPoint


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory DedekindResidue
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinPrimitiveRoots.Hecke.Theta
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The weighted ordinary-class sum is H1's ray-character sum. Orthogonality also removes
the zero point at the unit modulus. Guide: sol-thin-hk2/PROOFS.md:1340–1370,1512–1537;
sol-thin-hk1/PROOFS.md:1021–1067. Uses H1's ray ideal parametrization, weighted unit-box
unfolding and hk_point_ideal_integral; no primitive FE assumption is needed. -/
theorem hk_weighted_theta_eq_ray_character [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) {t : ℝ} (ht : 0 < t) :
    hkWeightedH ψ t = (rayCharacterFEPair (hkRayRepresentatives m) ψ).f t := by
  classical
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  letI : Fintype (RayClassGroup m) := Fintype.ofFinite _
  let R := hkRayRepresentatives m
  let Irep : ClassGroup (𝓞 K) → NumberFieldFractionalIdealGroup K := classRep K
  let Eof : RayClassGroup m → ClassGroup (𝓞 K) := fun C =>
    ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1)
  let scale (E : ClassGroup (𝓞 K)) :=
    (idealNormR K (Irep E))⁻¹ ^ 2 * heckeBeta K * t
  let tail (C : RayClassGroup m) : ℂ :=
    (ψ C : ℂ) * (hkFEIdealRayGtail m (R.ideal C) (R.coprime C)
      ((idealNormR K (idealUnit (R.ideal C) (R.coprime C).1))⁻¹ ^ 2 *
        heckeBeta K * t) : ℂ)
  have hInt : ∀ E : ClassGroup (𝓞 K), ∀ C : RayClassGroup m,
      IntegrableOn (fun v : logSpace K =>
        hkFEIdealWeightTheta (hkFEIdealRayClassPointWeight ψ C) (Irep E)
          (heckeWeights K (scale E) v))
        (ZSpan.fundamentalDomain
          ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)) := by
    intro E C
    by_cases hE : E = Eof C
    · subst E
      have hOrd : ClassGroup.mk K (Irep (Eof C)) =
          ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := by
        dsimp [Irep, Eof]
        rw [mk_classRep]
      simpa [Irep, scale] using hkFEIdealWeightTheta_integrableOn_box
        ψ C (Irep (Eof C)) (R.ideal C) (R.coprime C) (R.class_eq C) hOrd ht
    · have hne : ClassGroup.mk K (Irep E) ≠
          ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := by
        intro h
        apply hE
        dsimp [Eof]
        calc
          E = ClassGroup.mk K (Irep E) := by dsimp [Irep]; rw [mk_classRep]
          _ = ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := h
      exact hkFEIdealWeightTheta_integrableOn_box_of_class_ne
        ψ C (Irep E) (R.ideal C) (R.coprime C) (R.class_eq C) hne (scale E)
  have hdecomp (E : ClassGroup (𝓞 K)) :
      hkNormalizedG ψ (Irep E) t = hkFEWeightedZeroAverage ψ (Irep E) +
        ∑ C : RayClassGroup m,
          hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) (Irep E) t := by
    have hN : 0 < idealNormR K (Irep E) := idealNormR_pos K (Irep E)
    have hscaled : 0 < scale E := by
      dsimp [scale]
      exact mul_pos (mul_pos (pow_pos (inv_pos.mpr hN) 2) (heckeBeta_pos K)) ht
    have h := hkFEWeightedG_eq_zero_add_components ψ (Irep E) hscaled (hInt E)
    simpa [Irep, scale, hkNormalizedG, hkFEIdealWeightNormalizedG] using h
  have hcomp (E : ClassGroup (𝓞 K)) (C : RayClassGroup m) :
      hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) (Irep E) t =
        if E = Eof C then tail C else 0 := by
    by_cases hE : E = Eof C
    · subst E
      have hOrd : ClassGroup.mk K (Irep (Eof C)) =
          ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := by
        dsimp [Irep, Eof]
        rw [mk_classRep]
      simpa [tail, Irep, Eof, scale] using
        (hkFEIdealWeightNormalizedG_rayGtail ψ C (Irep (Eof C))
          (R.ideal C) (R.coprime C) (R.class_eq C) hOrd ht)
    · have hne : ClassGroup.mk K (Irep E) ≠
          ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := by
        intro h
        apply hE
        dsimp [Eof]
        calc
          E = ClassGroup.mk K (Irep E) := by dsimp [Irep]; rw [mk_classRep]
          _ = ClassGroup.mk K (idealUnit (R.ideal C) (R.coprime C).1) := h
      simp [hE, hkFEIdealWeightNormalizedG_eq_zero_of_class_ne ψ C (Irep E)
        (R.ideal C) (R.coprime C) (R.class_eq C) hne t]
  have hdouble :
      (∑ E : ClassGroup (𝓞 K), ∑ C : RayClassGroup m,
        hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) (Irep E) t) =
        ∑ C : RayClassGroup m, tail C := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C hC
    calc
      (∑ E : ClassGroup (𝓞 K),
          hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) (Irep E) t) =
        ∑ E : ClassGroup (𝓞 K), if E = Eof C then tail C else 0 := by
          apply Finset.sum_congr rfl
          intro E hE
          rw [hcomp]
      _ = tail C := by
        rw [Finset.sum_ite_eq' Finset.univ (Eof C) (fun _ => tail C)]
        simp
  have hsumZero : ∑ E : ClassGroup (𝓞 K), hkFEWeightedZeroAverage ψ (Irep E) = 0 := by
    by_cases hm : m.finitePart = 0
    · exact hkFEWeightedZeroAverage_sum_eq_zero_of_finitePart_zero ψ hψ hm
    · simp [hkFEWeightedZeroAverage, hkPointWeight, hm]
  have hRhsTail : ∑ C : RayClassGroup m, tail C =
      ∑ C : RayClassGroup m, (ψ C : ℂ) *
        (rayF m (R.ideal C) (R.coprime C) t : ℂ) := by
    have hterm : ∀ C : RayClassGroup m, tail C =
        (ψ C : ℂ) *
          ((rayF m (R.ideal C) (R.coprime C) t : ℝ) - rayPrimalConstant m : ℂ) := by
      intro C
      dsimp [tail]
      rw [hkFEIdealRayGtail_eq_rayF_sub_constant (R.ideal C) (R.coprime C) ht]
      push_cast
      ring
    have hconst : ∑ C : RayClassGroup m,
        (ψ C : ℂ) * (rayPrimalConstant m : ℂ) = 0 := by
      rw [← Finset.sum_mul, rayClassCharacter_sum_eq_zero ψ hψ]
      simp
    calc
      ∑ C : RayClassGroup m, tail C =
          ∑ C : RayClassGroup m,
            ((ψ C : ℂ) * (rayF m (R.ideal C) (R.coprime C) t : ℂ) -
              (ψ C : ℂ) * (rayPrimalConstant m : ℂ)) := by
          apply Finset.sum_congr rfl
          intro C hC
          rw [hterm C]
          push_cast
          ring
      _ = _ := by
          rw [Finset.sum_sub_distrib, hconst, sub_zero]
  have hH : hkWeightedH ψ t =
      (∑ E : ClassGroup (𝓞 K), hkFEWeightedZeroAverage ψ (Irep E)) +
        ∑ C : RayClassGroup m, tail C := by
    calc
      hkWeightedH ψ t =
          ∑ E : ClassGroup (𝓞 K),
            (hkFEWeightedZeroAverage ψ (Irep E) +
              ∑ C : RayClassGroup m,
                hkFEIdealWeightNormalizedG (hkFEIdealRayClassPointWeight ψ C) (Irep E) t) := by
            unfold hkWeightedH
            apply Finset.sum_congr rfl
            intro E hE
            simpa [Irep] using hdecomp E
      _ = _ := by rw [Finset.sum_add_distrib, hdouble]
  rw [hH, hsumZero, zero_add, hRhsTail]
  change ∑ C : RayClassGroup m, (ψ C : ℂ) *
      (rayF m (R.ideal C) (R.coprime C) t : ℂ) =
    (rayCharacterFEPair R ψ).f t
  simp [rayCharacterFEPair, finiteFEPair, rayFEPair]

end ArtinPrimitiveRoots.Hecke
