import ArtinPrimitiveRoots.Hecke.Theta.RayMellinArithmetic

/-!
The ray restriction of the fundamental-cone ideal parametrization. Mathlib's
`integerSetEquiv` separates the torsion-unit factor; the ray kernel depends only on the
generated ideal, so the same torsion multiplicity survives the restriction.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem DedekindResidue
open scoped NumberField nonZeroDivisors ENNReal NNReal

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

/-- Fundamental-cone points selected by the ray-principal kernel. -/
def rayConePoints (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰) :=
  {a : idealSet K J // rayKernelWeight m (conePreimage K J a) = 1}

instance rayConePointsCountable (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰) :
    Countable (rayConePoints m J) := by
  unfold rayConePoints
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Ray-principal cone points are ray-principal multiples of J, with one torsion-unit factor. -/
def rayConeIdealEquiv [IsTotallyComplex K] (m : RayClassModulus K)
    (J : (Ideal (𝓞 K))⁰) :
    rayConePoints m J ≃
      {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
        ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1} ×
          torsion K := by
  classical
  calc
    rayConePoints m J ≃
        {a : {a : integerSet K //
          (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K))} //
          rayKernelWeight m (algebraMap (𝓞 K) K
            (preimageOfMemIntegerSet a.1 : 𝓞 K)) = 1} := by
      refine Equiv.subtypeEquiv (idealSetEquiv K J) (fun a => ?_)
      rfl
    _ ≃ {a : integerSet K //
        (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K)) ∧
        rayKernelWeight m (algebraMap (𝓞 K) K (preimageOfMemIntegerSet a : 𝓞 K)) = 1} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K)))
        (fun a : integerSet K => rayKernelWeight m
          (algebraMap (𝓞 K) K (preimageOfMemIntegerSet a : 𝓞 K)) = 1)
    _ ≃ {q : {P : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (P : Ideal (𝓞 K))} × torsion K //
        (J : Ideal (𝓞 K)) ∣ (q.1.1 : Ideal (𝓞 K)) ∧
        ∃ hP : IsCoprimeTo m (q.1.1 : Ideal (𝓞 K)),
          rayClass m (q.1.1 : Ideal (𝓞 K)) hP = 1} := by
      refine Equiv.subtypeEquiv (integerSetEquiv K) (fun a => ?_)
      rw [integerSetEquiv_apply_fst, Ideal.dvd_span_singleton]
      exact and_congr Iff.rfl (rayKernelWeight_eq_one_iff_rayClass_span m _
        (nonZeroDivisors.coe_ne_zero (preimageOfMemIntegerSet a)))
    _ ≃ {P : {P : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (P : Ideal (𝓞 K))} //
        (J : Ideal (𝓞 K)) ∣ (P.1 : Ideal (𝓞 K)) ∧
        ∃ hP : IsCoprimeTo m (P.1 : Ideal (𝓞 K)),
          rayClass m (P.1 : Ideal (𝓞 K)) hP = 1} × torsion K :=
      Equiv.prodSubtypeFstEquivSubtypeProd (p := fun P :
        {P : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (P : Ideal (𝓞 K))} =>
          (J : Ideal (𝓞 K)) ∣ (P.1 : Ideal (𝓞 K)) ∧
            ∃ hP : IsCoprimeTo m (P.1 : Ideal (𝓞 K)), rayClass m (P.1 : Ideal (𝓞 K)) hP = 1)
    _ ≃ {P : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (P : Ideal (𝓞 K)) ∧
        ((J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
          ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1)} ×
            torsion K :=
      Equiv.prodCongrLeft fun _ : torsion K => Equiv.subtypeSubtypeEquivSubtypeInter
        (fun P : (Ideal (𝓞 K))⁰ => Submodule.IsPrincipal (P : Ideal (𝓞 K)))
        (fun P : (Ideal (𝓞 K))⁰ => (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
          ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1)
    _ ≃ {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
        ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1} ×
          torsion K := by
      refine Equiv.prodCongrLeft (fun _ : torsion K =>
        Equiv.subtypeEquivRight (fun P : (Ideal (𝓞 K))⁰ => ?_))
      constructor
      · exact And.right
      · rintro ⟨hdiv, hP, hclass⟩
        exact ⟨isPrincipal_of_rayClass_eq_one m (P : Ideal (𝓞 K)) hP hclass,
          hdiv, hP, hclass⟩

@[simp] theorem rayConeIdealEquiv_fst [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰) (a : rayConePoints m J) :
    (((rayConeIdealEquiv m J a).1.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J a.1) : 𝓞 K)} := rfl

/-- The cone preimage norm is the absolute norm of its generated ray-principal ideal. -/
theorem rayConeIdealEquiv_norm [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰) (a : rayConePoints m J) :
    ((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ) =
      (Ideal.absNorm ((rayConeIdealEquiv m J a).1.1 : Ideal (𝓞 K)) : ℝ) := by
  rw [abs_norm_conePreimage, rayConeIdealEquiv_fst, Ideal.absNorm_span_singleton]
  rfl

/-- The norm sum on the selected cone has the same torsion multiplicity as the unweighted cone. -/
theorem tsum_rayCone_norm_rpow [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰) (σ : ℝ) :
    (∑' a : rayConePoints m J,
      ENNReal.ofReal (((((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ)) ^ 2) ^ (-σ))) =
    (torsionOrder K : ℝ≥0∞) *
      ∑' P : {P : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (P : Ideal (𝓞 K)) ∧
        ∃ hP : IsCoprimeTo m (P : Ideal (𝓞 K)), rayClass m (P : Ideal (𝓞 K)) hP = 1},
        ENNReal.ofReal (((Ideal.absNorm (P.1 : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ)) := by
  classical
  letI := Fintype.ofFinite (torsion K)
  simp_rw [rayConeIdealEquiv_norm m J]
  rw [Equiv.tsum_eq (rayConeIdealEquiv m J) (fun p =>
    ENNReal.ofReal (((Ideal.absNorm (p.1.1 : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ))),
    ENNReal.tsum_prod']
  simp only [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  simp only [Finset.card_univ]

end ArtinPrimitiveRoots.Hecke

end
