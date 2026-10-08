import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical MeasureTheory

private theorem circleDistance_eq_infDist (t : ℝ) :
    circleDistance t = Metric.infDist t (Set.range (fun z : ℤ => (z : ℝ))) := by
  let A := Set.range (fun z : ℤ => |t - (z : ℝ)|)
  have hImage : (fun u : ℝ => dist t u) '' Set.range (fun z : ℤ => (z : ℝ)) = A := by
    ext y
    constructor
    · rintro ⟨u, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, by simp only [Real.dist_eq]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z : ℝ), ⟨z, rfl⟩, by simp only [Real.dist_eq]⟩
  have hNE : A.Nonempty := Set.range_nonempty (fun z : ℤ => |t - (z : ℝ)|)
  have hBdd : BddBelow A := ⟨0, by rintro y ⟨z, rfl⟩; exact abs_nonneg _⟩
  have hSinf : IsGLB A (circleDistance t) := isGLB_csInf hNE hBdd
  have hInf := Metric.isGLB_infDist
    (Set.range_nonempty (fun z : ℤ => (z : ℝ))) (x := t)
  rw [hImage] at hInf
  exact hSinf.unique hInf

/-- Circle distance is continuous as distance to the integer lattice. -/
theorem circleDistance_continuous : Continuous circleDistance := by
  have hfun : circleDistance = fun t : ℝ => Metric.infDist t (Set.range (fun z : ℤ => (z : ℝ))) :=
    funext circleDistance_eq_infDist
  rw [hfun]
  exact Metric.continuous_infDist_pt _

private theorem measurableSet_const_predicate (P : Prop) : MeasurableSet {r : ℝ | P} := by
  by_cases h : P <;> simp [h]

private theorem measurableSet_const_imp (P : Prop) (Q : ℝ → Prop)
    (hQ : MeasurableSet {r : ℝ | Q r}) : MeasurableSet {r : ℝ | P → Q r} := by
  by_cases h : P
  · simpa only [h, true_implies] using hQ
  · simp [h]

/-- The deterministic first test is a countable intersection of measurable conditions. -/
theorem measurableSet_goodTestOne (x Y d₀ : ℝ) {K : ℕ} (p : PrimeLists x K) :
    MeasurableSet {r : ℝ | goodTestOne x Y d₀ p r} := by
  unfold goodTestOne
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro omitted
  apply MeasurableSet.iInter
  intro hlow
  apply MeasurableSet.iInter
  intro hhigh
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro hl
  apply MeasurableSet.iInter
  intro hlhigh
  have hCont : Continuous (fun r : ℝ => circleDistance ((l : ℝ) * (omissionProduct p omitted : ℝ) * r)) :=
    circleDistance_continuous.comp (by fun_prop)
  exact measurableSet_lt measurable_const hCont.measurable

/-- The weighted trial-failure series in the second test is measurable. -/
theorem measurable_goodTestTwo_series (x d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (I : Finset (Fin K)) (iStar : Fin K) :
    Measurable (fun r : ℝ =>
      ∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
            ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
              IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
              circleDistance (((n₁ : ℝ) - n₂) * r) ≤
                100 * Real.exp (-Real.rpow (Real.log x) (a iStar))
        then freshChoiceWeight x a I fresh else 0) := by
  apply Measurable.tsum
  intro fresh
  have hEvent : MeasurableSet {r : ℝ |
      IsFreshChoice x a I fresh ∧
        ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
          circleDistance (((n₁ : ℝ) - n₂) * r) ≤
            100 * Real.exp (-Real.rpow (Real.log x) (a iStar))} := by
    simp only [Set.setOf_and, Set.setOf_exists]
    apply (measurableSet_const_predicate _).inter
    apply MeasurableSet.iUnion
    intro n₁
    apply MeasurableSet.iUnion
    intro n₂
    apply (measurableSet_const_predicate _).inter
    apply (measurableSet_const_predicate _).inter
    apply (measurableSet_const_predicate _).inter
    have hCont : Continuous (fun r : ℝ => circleDistance (((n₁ : ℝ) - n₂) * r)) :=
      circleDistance_continuous.comp (by fun_prop)
    exact measurableSet_le hCont.measurable measurable_const
  exact Measurable.ite hEvent measurable_const measurable_const

/-- The probabilistic second test is a finite intersection of measurable series sublevel sets. -/
theorem measurableSet_goodTestTwo (x d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) : MeasurableSet {r : ℝ | goodTestTwo x d₀ K a p r} := by
  unfold goodTestTwo
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro I
  apply MeasurableSet.iInter
  intro hI
  exact measurableSet_le (measurable_goodTestTwo_series x d₀ K a p I (I.max' hI)) measurable_const

/-- The source and target goodness predicates are Borel. -/
theorem measurableSet_isGoodRatio (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) : MeasurableSet {r : ℝ | IsGoodRatio x Y d₀ K a p r} := by
  unfold IsGoodRatio
  rw [Set.setOf_and]
  exact (measurableSet_goodTestOne x Y d₀ p).inter (measurableSet_goodTestTwo x d₀ K a p)

/-- The indicator in the frozen good-state estimate is integrable on its ratio interval. -/
theorem badRatio_intervalIntegrable (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) :
    IntervalIntegrable (fun r : ℝ => if IsGoodRatio x Y d₀ K a p r then (0 : ℝ) else 1)
      volume 0 1 := by
  let f := fun r : ℝ => if IsGoodRatio x Y d₀ K a p r then (0 : ℝ) else 1
  have hm : Measurable f := Measurable.ite (measurableSet_isGoodRatio x Y d₀ K a p)
    measurable_const measurable_const
  have hi : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with r
    dsimp [f]
    split_ifs <;> norm_num
  refine ⟨hi, ?_⟩
  simp [Set.Ioc_eq_empty_of_le (by norm_num : (0 : ℝ) ≤ 1)]

end ArtinPrimitiveRoots.TypeII.PD
