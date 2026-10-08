import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Recombine supported real H¹ maps into a compact complex-linear chart map.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:320. Uses only the prebuilt Euclidean
isCompactOperator_h1OnToL2 and Mathlib compact-operator composition/addition.
The I compatibility is furnished by localized_chart_extension. -/
theorem complex_chart_rellich_compact
    {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (C : Set (EuclideanSpace ℝ ι)) (hC : IsCompact C)
    (A B : V →L[ℝ] ↥(RellichEuclidean.h1On C hC.measurableSet))
    (hI : ∀ x, A (Complex.I • x) = -B x ∧ B (Complex.I • x) = A x) :
    ∃ L : V →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      IsCompactOperator L ∧
      L.restrictScalars ℝ = rellichRecombine C hC.measurableSet A B := by
  let J := RellichEuclidean.h1OnToL2 C hC.measurableSet
  let Q := rellichRealToComplex (volume : Measure (EuclideanSpace ℝ ι))
  let LA := Q.comp (J.comp A)
  let LB := Q.comp (J.comp B)
  let T : V →L[ℝ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
    LA + Complex.I • LB

  have hJ : IsCompactOperator J :=
    RellichEuclidean.isCompactOperator_h1OnToL2 hC hC.measurableSet
  have hLA : IsCompactOperator LA := by
    change IsCompactOperator (Q.comp (J.comp A))
    exact (hJ.comp_clm A).clm_comp Q
  have hLB : IsCompactOperator LB := by
    change IsCompactOperator (Q.comp (J.comp B))
    exact (hJ.comp_clm B).clm_comp Q
  have hTcompact : IsCompactOperator T := by
    change IsCompactOperator (LA + Complex.I • LB)
    exact hLA.add (hLB.smul Complex.I)

  have hLAI (x : V) : LA (Complex.I • x) = -LB x := by
    change Q (J (A (Complex.I • x))) = -Q (J (B x))
    rw [(hI x).1]
    change (Q.comp J) (-B x) = -(Q.comp J) (B x)
    exact map_neg (Q.comp J) (B x)
  have hLBI (x : V) : LB (Complex.I • x) = LA x := by
    change Q (J (B (Complex.I • x))) = Q (J (A x))
    rw [(hI x).2]
  have hTI (x : V) : T (Complex.I • x) = Complex.I • T x := by
    change LA (Complex.I • x) + Complex.I • LB (Complex.I • x) =
      Complex.I • (LA x + Complex.I • LB x)
    rw [hLAI x, hLBI x, smul_add]
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
    abel

  have hdecompV (y : V) (z : ℂ) :
      z • y = (z.re : ℝ) • y + (z.im : ℝ) • (Complex.I • y) := by
    have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    calc
      z • y = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • y :=
        congrArg (fun w : ℂ => w • y) hz
      _ = (z.re : ℝ) • y + (z.im : ℝ) • (Complex.I • y) := by
        rw [add_smul, ← smul_smul]
        congr 1
  have hdecompW (y : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (z : ℂ) :
      z • y = (z.re : ℝ) • y + (z.im : ℝ) • (Complex.I • y) := by
    have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    calc
      z • y = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • y :=
        congrArg (fun w : ℂ => w • y) hz
      _ = (z.re : ℝ) • y + (z.im : ℝ) • (Complex.I • y) := by
        rw [add_smul, ← smul_smul]
        congr 1

  let Tlin : V →ₗ[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro z x
        calc
          T (z • x) = T ((z.re : ℝ) • x + (z.im : ℝ) • (Complex.I • x)) := by
            rw [hdecompV x z]
          _ = (z.re : ℝ) • T x + (z.im : ℝ) • T (Complex.I • x) := by
            rw [T.map_add, T.map_smul, T.map_smul]
          _ = (z.re : ℝ) • T x + (z.im : ℝ) • (Complex.I • T x) := by
            rw [hTI x]
          _ = z • T x := (hdecompW (T x) z).symm }
  let L : V →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
    Tlin.mkContinuous ‖T‖ (fun x => T.le_opNorm x)

  refine ⟨L, ?_, ?_⟩
  · change IsCompactOperator T
    exact hTcompact
  · apply ContinuousLinearMap.ext
    intro x
    change T x = rellichRecombine C hC.measurableSet A B x
    rfl

end ArtinPrimitiveRoots.A1.Spec
