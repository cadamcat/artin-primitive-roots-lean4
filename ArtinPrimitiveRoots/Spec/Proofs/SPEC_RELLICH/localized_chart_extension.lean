import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Extend bounded test localizations over the closed energy graph and retain I compatibility.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:320. Uses localized_chart_H1_bound and
e.graph_eq. ExtendOfNorm on the dense graph gives the maps; test I identities extend
by continuity. This lemma contains only completion and linear-map algebra. -/
theorem localized_chart_extension
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (ψ : X F → ℝ) (c : RellichTestChart Γ ψ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : testSubmodule F Γ,
      ‖c.re f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ∧
      ‖c.im f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖)) :
    ∃ A B : E.V →L[ℝ] ↥(RellichEuclidean.h1On c.support c.compact.measurableSet),
      (∀ f, A (rellichTestVector e f) = c.re f) ∧
      (∀ f, B (rellichTestVector e f) = c.im f) ∧
      (∀ x, A (Complex.I • x) = -B x ∧ B (Complex.I • x) = A x) := by
  classical
  let L : testSubmodule F Γ →ₗ[ℝ] E.V := (rellichTestVector e).restrictScalars ℝ
  have hDense : DenseRange L := by
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hxgraph :
        ((x : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D)) ∈
          closure (Set.range (energyGraphMap e.toL2 e.gradL2)) := by
      have hsetEq :
          (E.V : Set (WithLp 2 (L2Space F D × GradientL2Space F D))) =
            (energyGraph e.toL2 e.gradL2 : Set (WithLp 2 (L2Space F D × GradientL2Space F D))) :=
        congrArg (fun V : Submodule ℂ (WithLp 2 (L2Space F D × GradientL2Space F D)) =>
          (V : Set (WithLp 2 (L2Space F D × GradientL2Space F D)))) e.graph_eq
      have hx :
          ((x : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D)) ∈
            (energyGraph e.toL2 e.gradL2 : Set (WithLp 2 (L2Space F D × GradientL2Space F D))) :=
        (Set.ext_iff.mp hsetEq ((x : E.V) : WithLp 2
          (L2Space F D × GradientL2Space F D))).mp x.property
      change ((x : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D)) ∈
        (energyGraphMap e.toL2 e.gradL2).range.topologicalClosure at hx
      exact hx
    obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp hxgraph) ε hε
    rcases hy with ⟨f, rfl⟩
    refine ⟨L f, Set.mem_range_self (f := L) f, ?_⟩
    change dist ((x : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D))
      (energyGraphMap e.toL2 e.gradL2 f) < ε
    exact hdist
  have hnormFst (f : testSubmodule F Γ) : ‖e.toL2 f‖ ≤ ‖L f‖ := by
    have h := WithLp.norm_fst_le (α := L2Space F D) (β := GradientL2Space F D)
      (x := ((rellichTestVector e f : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D)))
    simpa [L, rellichTestVector, energyGraphMap] using h
  have hnormSnd (f : testSubmodule F Γ) : ‖e.gradL2 f‖ ≤ ‖L f‖ := by
    have h := WithLp.norm_snd_le (α := L2Space F D) (β := GradientL2Space F D)
      (x := ((rellichTestVector e f : E.V) : WithLp 2 (L2Space F D × GradientL2Space F D)))
    simpa [L, rellichTestVector, energyGraphMap] using h
  have hReBound (f : testSubmodule F Γ) : ‖c.re f‖ ≤ (2 * C) * ‖L f‖ := by
    calc
      ‖c.re f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := (hbound f).1
      _ ≤ C * (‖L f‖ + ‖L f‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hnormFst f) (hnormSnd f)) hC
      _ = (2 * C) * ‖L f‖ := by ring
  have hImBound (f : testSubmodule F Γ) : ‖c.im f‖ ≤ (2 * C) * ‖L f‖ := by
    calc
      ‖c.im f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := (hbound f).2
      _ ≤ C * (‖L f‖ + ‖L f‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hnormFst f) (hnormSnd f)) hC
      _ = (2 * C) * ‖L f‖ := by ring
  letI : CompleteSpace ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) :=
    rellich_h1On_complete c.support c.compact.measurableSet
  letI : NormedSpace ℝ ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) := inferInstance
  letI : ContinuousAdd ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) := ⟨by
    apply Continuous.subtype_mk
    · exact (continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd)⟩
  letI : IsBoundedSMul ℝ ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) :=
    IsBoundedSMul.of_norm_smul_le (fun (r : ℝ)
      (x : ↥(RellichEuclidean.h1On c.support c.compact.measurableSet)) =>
      (inferInstance : NormedSpace ℝ
        (↥(RellichEuclidean.h1On c.support c.compact.measurableSet))).norm_smul_le r x)
  let A : E.V →L[ℝ] ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) :=
    LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := testSubmodule F Γ)
      (Eₗ := E.V) (F := ↥(RellichEuclidean.h1On c.support c.compact.measurableSet))
      (σ₁₂ := RingHom.id ℝ) c.re L
  let B : E.V →L[ℝ] ↥(RellichEuclidean.h1On c.support c.compact.measurableSet) :=
    LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := testSubmodule F Γ)
      (Eₗ := E.V) (F := ↥(RellichEuclidean.h1On c.support c.compact.measurableSet))
      (σ₁₂ := RingHom.id ℝ) c.im L
  have hA (f : testSubmodule F Γ) : A (rellichTestVector e f) = c.re f := by
    change c.re.extendOfNorm L (L f) = c.re f
    exact LinearMap.extendOfNorm_eq hDense ⟨2 * C, hReBound⟩ f
  have hB (f : testSubmodule F Γ) : B (rellichTestVector e f) = c.im f := by
    change c.im.extendOfNorm L (L f) = c.im f
    exact LinearMap.extendOfNorm_eq hDense ⟨2 * C, hImBound⟩ f
  have hA_L (f : testSubmodule F Γ) : A (L f) = c.re f := by
    simpa [L] using hA f
  have hB_L (f : testSubmodule F Γ) : B (L f) = c.im f := by
    simpa [L] using hB f
  have hLsmul (f : testSubmodule F Γ) :
      L (Complex.I • f) = Complex.I • L f := by
    change rellichTestVector e (Complex.I • f) = Complex.I • rellichTestVector e f
    exact map_smul (rellichTestVector e) Complex.I f
  have hIcont : Continuous (fun x : E.V => Complex.I • x) := continuous_const_smul _
  have hAonDense :
      (fun x : E.V => A (Complex.I • x) + B x) ∘ L = (fun _ => (0 : ↥(RellichEuclidean.h1On c.support c.compact.measurableSet))) ∘ L := by
    funext f
    change A (Complex.I • L f) + B (L f) = 0
    calc
      A (Complex.I • L f) + B (L f) = A (L (Complex.I • f)) + B (L f) := by
        rw [← hLsmul f]
      _ = c.re (Complex.I • f) + c.im f :=
        congrArg₂ (fun a b => a + b) (hA_L (Complex.I • f)) (hB_L f)
      _ = 0 := by rw [c.re_I f]; exact neg_add_cancel (c.im f)
  have hBonDense :
      (fun x : E.V => B (Complex.I • x)) ∘ L = (fun x => A x) ∘ L := by
    funext f
    change B (Complex.I • L f) = A (L f)
    calc
      B (Complex.I • L f) = B (L (Complex.I • f)) := by rw [← hLsmul f]
      _ = c.im (Complex.I • f) := hB_L (Complex.I • f)
      _ = c.re f := c.im_I f
      _ = A (L f) := (hA_L f).symm
  have hAplusEq : (fun x : E.V => A (Complex.I • x) + B x) = fun _ => (0 : ↥(RellichEuclidean.h1On c.support c.compact.measurableSet)) :=
    hDense.equalizer ((A.continuous.comp hIcont).add B.continuous) continuous_const hAonDense
  have hBeq : (fun x : E.V => B (Complex.I • x)) = fun x => A x :=
    hDense.equalizer (B.continuous.comp hIcont) A.continuous hBonDense
  refine ⟨A, B, hA, hB, ?_⟩
  intro x
  constructor
  · have hplus : A (Complex.I • x) + B x = 0 := congrFun hAplusEq x
    let a := A (Complex.I • x)
    let b := B x
    calc
      a = a + 0 := (add_zero a).symm
      _ = a + (b + -b) := congrArg (fun y => a + y) (add_neg_cancel b).symm
      _ = (a + b) + -b := (add_assoc a b (-b)).symm
      _ = 0 + -b := congrArg (fun y => y + -b) hplus
      _ = -b := zero_add _
  · exact congrFun hBeq x

end ArtinPrimitiveRoots.A1.Spec
