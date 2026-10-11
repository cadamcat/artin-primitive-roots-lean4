import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_denominator_elements_with_embedding_bounds
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.cusp_stabilizer_form_without_freeness
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.cusp_representatives_transition_eq

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specProper_lowerHeight_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) : 0 < SiegelData.lowerHeight F d i := by
  let g : SL(2,F) := (d.σ i)⁻¹
  have hrow : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := g.2
    rw [Matrix.det_fin_two] at hd
    simp [h.1, h.2] at hd
  have hI : bottomRowFractionalIdeal F g ≠ 0 := by
    rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
    rcases hrow with h | h
    · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  have hnorm : FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) ≠ 0 := by
    intro hz
    exact hI (FractionalIdeal.absNorm_eq_zero_iff.mp hz)
  have hnormQ : 0 < FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnorm)
  have hnormR : 0 < ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) : ℚ) : ℝ) :=
    by exact_mod_cast hnormQ
  dsimp [SiegelData.lowerHeight]
  exact inv_pos.mpr (mul_pos hnormR d.C_M_pos)

private theorem specProper_normHeight_ptX' (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    normHeight F (ptX' F x y) = ∏ w : InfinitePlace F, y w := by
  change (∏ w : InfinitePlace F, height ((ptX' F x y) w)) = _
  apply Finset.prod_congr rfl
  intro w hw
  exact (G1_h3_basics (F := F)).1 (x w) (y w) (hy w)

private theorem specProper_balanced_unit_bound (B : ℝ)
    (y y' : InfinitePlace F → ℝ) (a : InfinitePlace F → ℂ)
    (hbal : IsBalancedHeights F B y) (hbal' : IsBalancedHeights F B y')
    (hscale : ∀ w, y' w = Complex.normSq (a w) * y w)
    (hprod : (∏ w : InfinitePlace F, y w) = ∏ w, y' w) :
    0 ≤ B ∧ ∀ w, ‖a w‖ ≤ Real.exp |B| ∧ (Real.exp |B|)⁻¹ ≤ ‖a w‖ := by
  have hB : 0 ≤ B := by
    let w₀ : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
    exact le_trans (abs_nonneg _) (hbal.2 w₀)
  have hlogs : (∑ w : InfinitePlace F, Real.log (y w)) =
      ∑ w, Real.log (y' w) := by
    have hlogY : Real.log (∏ w : InfinitePlace F, y w) =
        ∑ w, Real.log (y w) :=
      Real.log_prod (fun w hw => (hbal.1 w).ne')
    have hlogY' : Real.log (∏ w : InfinitePlace F, y' w) =
        ∑ w, Real.log (y' w) :=
      Real.log_prod (fun w hw => (hbal'.1 w).ne')
    rw [← hlogY, hprod, hlogY']
  let mean (v : InfinitePlace F → ℝ) : ℝ :=
    (placeCount F)⁻¹ * ∑ w : InfinitePlace F, Real.log (v w)
  have hmean : mean y = mean y' := by
    simp [mean, hlogs]
  refine ⟨hB, ?_⟩
  intro w
  have hnormSqPos : 0 < Complex.normSq (a w) := by
    have hy' := hbal'.1 w
    rw [hscale w] at hy'
    have hy := hbal.1 w
    nlinarith [Complex.normSq_nonneg (a w)]
  have hnormPos : 0 < ‖a w‖ := by
    rw [Complex.normSq_eq_norm_sq] at hnormSqPos
    nlinarith [norm_nonneg (a w)]
  have hlogScale : Real.log (y' w) - Real.log (y w) =
      2 * Real.log ‖a w‖ := by
    have hmul := Real.log_mul hnormSqPos.ne' (hbal.1 w).ne'
    have hlogSq : Real.log (Complex.normSq (a w)) = 2 * Real.log ‖a w‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.log_pow]
      norm_num
    rw [hscale w, hmul, hlogSq]
    ring
  have hdev :
      (Real.log (y' w) - mean y') - (Real.log (y w) - mean y) =
        2 * Real.log ‖a w‖ := by
    rw [hmean]
    linarith [hlogScale]
  have hdevBound :
      |(Real.log (y' w) - mean y') - (Real.log (y w) - mean y)| ≤ 2 * B := by
    calc
      _ ≤ |Real.log (y' w) - mean y'| + |mean y - Real.log (y w)| := by
        simpa using abs_sub_le (Real.log (y' w) - mean y') 0
          (Real.log (y w) - mean y)
      _ = |Real.log (y' w) - mean y'| + |Real.log (y w) - mean y| := by
        rw [abs_sub_comm (mean y) (Real.log (y w))]
      _ ≤ B + B := add_le_add (hbal'.2 w) (hbal.2 w)
      _ = 2 * B := by ring
  have hlogBound : |Real.log ‖a w‖| ≤ B := by
    rw [hdev] at hdevBound
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hdevBound
    nlinarith
  have hlogLo : -|B| ≤ Real.log ‖a w‖ := by
    have h := (abs_le.mp hlogBound).1
    simpa [abs_of_nonneg hB] using h
  have hlogHi : Real.log ‖a w‖ ≤ |B| := by
    have h := (abs_le.mp hlogBound).2
    simpa [abs_of_nonneg hB] using h
  have hnormExp : Real.exp (Real.log ‖a w‖) = ‖a w‖ := Real.exp_log hnormPos
  constructor
  · calc
      ‖a w‖ = Real.exp (Real.log ‖a w‖) := hnormExp.symm
      _ ≤ Real.exp |B| := Real.exp_le_exp.mpr hlogHi
  · calc
      (Real.exp |B|)⁻¹ = Real.exp (-|B|) := by rw [Real.exp_neg]
      _ ≤ Real.exp (Real.log ‖a w‖) := Real.exp_le_exp.mpr hlogLo
      _ = ‖a w‖ := hnormExp

/-- Above a common product-height threshold, the remaining Siegel overlaps are finite.
Uses R6_two_heights, G1_h3_basics, G2_x_action,
cusp_representatives_transition_eq, cusp_stabilizer_form_without_freeness,
finite_integral_elements_with_embedding_bounds and
finite_denominator_elements_with_embedding_bounds; feeds R9_proper. -/
theorem siegel_high_height_overlap_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∃ A : ℝ, 0 ≤ A ∧ (siegelHighOverlap Γ d A).Finite := by
  classical
  letI : Fintype d.ι := d.fintype
  let floor (i : d.ι) : ℝ := SiegelData.lowerHeight F d i
  have hfloor (i : d.ι) : 0 < floor i := specProper_lowerHeight_pos Γ d i
  let pairBound (i j : d.ι) := (R6_two_heights (F := F) Γ).2 (d.σ i) (d.σ j)
  let C (i j : d.ι) : ℝ := Classical.choose (pairBound i j)
  have hC i j : 0 < C i j ∧ ∀ γ : Γ, ∀ z : X F,
      ((d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) 1 0 ≠ 0 →
        normHeight F ((d.σ i)⁻¹ • z) *
          normHeight F ((d.σ j)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ C i j :=
    Classical.choose_spec (pairBound i j)
  let Q (i j : d.ι) : ℝ := C i j / floor i + C i j / floor j
  have hQnonneg (i j : d.ι) : 0 ≤ Q i j := by
    dsimp [Q]
    exact add_nonneg (div_nonneg (hC i j).1.le (hfloor i).le)
      (div_nonneg (hC i j).1.le (hfloor j).le)
  let A : ℝ := 1 + ∑ i : d.ι, ∑ j : d.ι, Q i j
  have hA : 0 ≤ A := by
    dsimp [A]
    apply add_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact hQnonneg i j
  have hQle : ∀ i j : d.ι, Q i j ≤ ∑ i' : d.ι, ∑ j' : d.ι, Q i' j' := by
    intro i j
    calc
      Q i j ≤ ∑ j' : d.ι, Q i j' :=
        Finset.single_le_sum (fun j' hj' => hQnonneg i j') (Finset.mem_univ j)
      _ ≤ ∑ i' : d.ι, ∑ j' : d.ι, Q i' j' :=
        Finset.single_le_sum
          (fun i' hi' => Finset.sum_nonneg fun j' hj' => hQnonneg i' j')
          (Finset.mem_univ i)
  have hQltA : ∀ i j : d.ι, Q i j < A := by
    intro i j
    dsimp [A]
    linarith [hQle i j]
  let unitDenominatorData (i : d.ι) :=
    cusp_stabilizer_form_without_freeness Γ (d.σ i)
  let D (i : d.ι) : ℕ := Classical.choose (unitDenominatorData i)
  have hD (i : d.ι) : 0 < D i ∧ ∀ γ : cuspStab F Γ (d.σ i),
      ∃ ε : (𝓞 F)ˣ, ∃ μ : F, HasDenominatorBound F (D i) μ ∧
        (d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i = cuspUnitMatrix F ε μ ∧
        ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
          (∀ w, 0 < y w) →
          (γ : SL(2,𝓞 F)) • (d.σ i • ptX' F x y) =
            d.σ i • ptX' F
              (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
                w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
              (fun w => Complex.normSq
                (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w) :=
    Classical.choose_spec (unitDenominatorData i)
  let radiusData (i : d.ι) : ∃ R : ℝ, 0 < R ∧
      d.P i ⊆ Metric.ball (0 : InfinitePlace F → ℂ) R :=
    (d.P_bounded i).subset_ball_lt 0 (0 : InfinitePlace F → ℂ)
  let R (i : d.ι) : ℝ := Classical.choose (radiusData i)
  have hR (i : d.ι) : 0 < R i ∧ d.P i ⊆ Metric.ball (0 : InfinitePlace F → ℂ) (R i) :=
    Classical.choose_spec (radiusData i)
  have hcoordBound (i : d.ι) (u : InfinitePlace F → ℂ) (hu : u ∈ d.P i)
      (w : InfinitePlace F) : ‖u w‖ ≤ R i := by
    have hball := (hR i).2 hu
    have hnorm : ‖u‖ < R i := by simpa [dist_zero_right] using hball
    exact (norm_le_pi_norm u w).trans hnorm.le
  let E (i : d.ι) : ℝ := Real.exp |2 * d.B i|
  let M (i : d.ι) : ℝ := E i * (R i + E i ^ 2 * R i)
  have hMnonneg (i : d.ι) : 0 ≤ M i := by
    have hEpos : 0 < E i := Real.exp_pos _
    have hRpos : 0 < R i := (hR i).1
    dsimp [M]
    positivity
  let unitSet (i : d.ι) : Set ((𝓞 F)ˣ) :=
    {ε | ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ ≤ E i}
  let denominatorSet (i : d.ι) : Set F :=
    {μ | HasDenominatorBound F (D i) μ ∧
      ∀ w : InfinitePlace F, ‖w.embedding μ‖ ≤ M i}
  let parameterSet (i : d.ι) : Set ((𝓞 F)ˣ × F) := unitSet i ×ˢ denominatorSet i
  have hunitSetFinite (i : d.ι) : (unitSet i).Finite := by
    let integralSet : Set (𝓞 F) :=
      {a | ∀ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ E i}
    have hIntegral : integralSet.Finite := by
      apply finite_integral_elements_with_embedding_bounds (F := F) (E i)
      exact (Real.exp_pos _).le
    have hImage : ((fun ε : (𝓞 F)ˣ => (ε : 𝓞 F)) '' unitSet i).Finite := by
      apply hIntegral.subset
      rintro a ⟨ε, hε, rfl⟩
      exact hε
    apply Set.Finite.of_finite_image (f := fun ε : (𝓞 F)ˣ => (ε : 𝓞 F)) hImage
    intro ε hε η hη he
    exact Units.ext he
  have hdenominatorSetFinite (i : d.ι) : (denominatorSet i).Finite := by
    apply finite_denominator_elements_with_embedding_bounds (F := F) (D i) (hD i).1 (M i)
    exact hMnonneg i
  have hparameterSetFinite (i : d.ι) : (parameterSet i).Finite := by
    exact Set.Finite.prod (hunitSetFinite i) (hdenominatorSetFinite i)
  let realizableSet (i : d.ι) : Set ((𝓞 F)ˣ × F) :=
    {p | p ∈ parameterSet i ∧ ∃ γ : Γ,
      (d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i = cuspUnitMatrix F p.1 p.2}
  have hrealizableSetFinite (i : d.ι) : (realizableSet i).Finite :=
    (hparameterSetFinite i).subset (by intro p hp; exact hp.1)
  let chosenGamma (i : d.ι) : {p // p ∈ realizableSet i} → Γ :=
    fun p => Classical.choose p.property.2
  have hchosenGamma (i : d.ι) (p : {p // p ∈ realizableSet i}) :
      (d.σ i)⁻¹ * toSLF F (chosenGamma i p : SL(2,𝓞 F)) * d.σ i =
        cuspUnitMatrix F p.1.1 p.1.2 := Classical.choose_spec p.property.2
  have hrangeFinite (i : d.ι) : (Set.range (chosenGamma i)).Finite := by
    letI : Finite {p // p ∈ realizableSet i} := (hrealizableSetFinite i).to_subtype
    exact Set.finite_range (chosenGamma i)
  have hfiniteUnion : (⋃ i : d.ι, Set.range (chosenGamma i)).Finite :=
    Set.finite_iUnion hrangeFinite
  refine ⟨A, hA, ?_⟩
  apply hfiniteUnion.subset
  intro γ hγ
  change ∃ i j z, z ∈ SiegelData.setAt F d i ∧
      siegelOverlapTransition Γ d i j γ z ∈ SiegelData.setAt F d j ∧
      (A < normHeight F z ∨
        A < normHeight F (siegelOverlapTransition Γ d i j γ z)) at hγ
  rcases hγ with ⟨i, j, z, hzSet, htransSet, hlarge⟩
  rcases hzSet with ⟨x, y, hz, hx, hbal, hfloorSource⟩
  rcases htransSet with ⟨x', y', htransPoint, hx', hbal', hfloorTarget⟩
  have hfloorSource' : floor i ≤ normHeight F z := by
    rw [hz]
    exact hfloorSource
  have hfloorTarget' : floor j ≤
      normHeight F (siegelOverlapTransition Γ d i j γ z) := by
    rw [htransPoint]
    exact hfloorTarget
  have hnonzero : ¬
      ((d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) 1 0 ≠ 0 := by
    intro hentry
    have htwoRaw := (hC i j).2 γ (d.σ i • z) hentry
    have htwo : normHeight F z *
        normHeight F (siegelOverlapTransition Γ d i j γ z) ≤ C i j := by
      simpa [siegelOverlapTransition, smul_smul] using htwoRaw
    have hratioTarget : C i j / floor j < A := by
      have hterm : C i j / floor j ≤ Q i j := by
        dsimp [Q]
        have hnonneg : 0 ≤ C i j / floor i := div_nonneg (hC i j).1.le (hfloor i).le
        linarith
      exact lt_of_le_of_lt hterm (hQltA i j)
    have hratioSource : C i j / floor i < A := by
      have hterm : C i j / floor i ≤ Q i j := by
        dsimp [Q]
        have hnonneg : 0 ≤ C i j / floor j := div_nonneg (hC i j).1.le (hfloor j).le
        linarith
      exact lt_of_le_of_lt hterm (hQltA i j)
    rcases hlarge with hlarge | hlarge
    · have hgt : C i j < normHeight F z * floor j :=
        (div_lt_iff₀ (hfloor j)).mp (lt_trans hratioTarget hlarge)
      have hzpos : 0 < normHeight F z := lt_of_lt_of_le (hfloor i) hfloorSource'
      have hprod : normHeight F z * floor j ≤
          normHeight F z * normHeight F (siegelOverlapTransition Γ d i j γ z) :=
        mul_le_mul_of_nonneg_left hfloorTarget' hzpos.le
      exact not_lt_of_ge htwo (lt_of_lt_of_le hgt hprod)
    · have hgt : C i j < normHeight F (siegelOverlapTransition Γ d i j γ z) * floor i :=
        (div_lt_iff₀ (hfloor i)).mp (lt_trans hratioSource hlarge)
      have htpos : 0 < normHeight F (siegelOverlapTransition Γ d i j γ z) :=
        lt_of_lt_of_le (hfloor j) hfloorTarget'
      have hprod : floor i * normHeight F (siegelOverlapTransition Γ d i j γ z) ≤
          normHeight F z * normHeight F (siegelOverlapTransition Γ d i j γ z) :=
        mul_le_mul_of_nonneg_right hfloorSource' htpos.le
      have hgt' : C i j < floor i *
          normHeight F (siegelOverlapTransition Γ d i j γ z) := by
        simpa [mul_comm] using hgt
      exact not_lt_of_ge htwo (lt_of_lt_of_le hgt' hprod)
  have hzero : ((d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) 1 0 = 0 := by
    by_contra h
    exact hnonzero h
  have htri : (d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i ∈ borelSL F := by
    change ((d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) 1 0 = 0
    exact hzero
  have hij := cusp_representatives_transition_eq Γ d i j γ htri
  subst j
  have hstab : γ ∈ cuspStab F Γ (d.σ i) := by
    simpa [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using htri
  obtain ⟨ε, μ, hden, hform, hact⟩ :=
    (hD i).2 ⟨γ, hstab⟩
  let a : InfinitePlace F → ℂ := fun w =>
    w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))
  let xf : InfinitePlace F → ℂ := fun w => a w ^ 2 * x w + a w * w.embedding μ
  let yf : InfinitePlace F → ℝ := fun w => Complex.normSq (a w) * y w
  let Mtrans : SL(2,F) :=
    (d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i
  have htriSame : Mtrans ∈ borelSL F := by
    change Mtrans 1 0 = 0
    change ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) 1 0 = 0
    exact hzero
  have hMform : Mtrans = cuspUnitMatrix F ε μ := by
    change (d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i = _
    exact hform
  have hpointForm : Mtrans • ptX' F x y = ptX' F xf yf := by
    calc
      Mtrans • ptX' F x y = cuspUnitMatrix F ε μ • ptX' F x y := by rw [hMform]
      _ = ptX' F xf yf := by
        simpa [a, xf, yf] using cuspUnitMatrix_smul_ptX' ε μ x y hbal.1
  have haNe (w : InfinitePlace F) : a w ≠ 0 := by
    apply (map_ne_zero_iff _ w.embedding.injective).mpr
    intro hmap
    have hzeroO : (ε : 𝓞 F) = 0 := by
      apply RingOfIntegers.coe_injective
      simpa using hmap
    exact (Units.ne_zero ε) hzeroO
  have hyfPos (w : InfinitePlace F) : 0 < yf w := by
    change 0 < Complex.normSq (a w) * y w
    rw [Complex.normSq_eq_norm_sq]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (haNe w))) (hbal.1 w)
  have htransitionAction :
      siegelOverlapTransition Γ d i i γ z = Mtrans • z := by
    change (d.σ i)⁻¹ •
      (toSLF F (γ : SL(2,𝓞 F)) • ((d.σ i) • z)) = Mtrans • z
    rw [smul_smul, smul_smul]
  have hpoint : ptX' F x' y' = ptX' F xf yf := by
    calc
      ptX' F x' y' = siegelOverlapTransition Γ d i i γ z := htransPoint.symm
      _ = Mtrans • z := htransitionAction
      _ = Mtrans • ptX' F x y := by rw [hz]
      _ = ptX' F xf yf := hpointForm
  have hyFormula (w : InfinitePlace F) : y' w = Complex.normSq (a w) * y w := by
    have h := congrArg height (congrFun hpoint w)
    change height (pt (x' w) (y' w)) = height (pt (xf w) (yf w)) at h
    rw [(G1_h3_basics (F := F)).1 (x' w) (y' w) (hbal'.1 w)] at h
    rw [(G1_h3_basics (F := F)).1 (xf w) (yf w) (hyfPos w)] at h
    simpa [yf] using h
  have hxFormula (w : InfinitePlace F) : x' w = xf w := by
    have h := congrArg horiz (congrFun hpoint w)
    change horiz (pt (x' w) (y' w)) = horiz (pt (xf w) (yf w)) at h
    rw [(G1_h3_basics (F := F)).2.1 (x' w) (y' w) (hbal'.1 w),
      (G1_h3_basics (F := F)).2.1 (xf w) (yf w) (hyfPos w)] at h
    exact h
  have hheightInv :
      normHeight F (Mtrans • ptX' F x y) = normHeight F (ptX' F x y) := by
    simpa [Mtrans] using
      ((G2_x_action (F := F)).2.2.1 (γ : SL(2,𝓞 F)) (d.σ i) htriSame).2
        (ptX' F x y)
  have hprod : (∏ w : InfinitePlace F, y w) = ∏ w, y' w := by
    calc
      ∏ w : InfinitePlace F, y w = normHeight F (ptX' F x y) :=
        (specProper_normHeight_ptX' x y hbal.1).symm
      _ = normHeight F (Mtrans • ptX' F x y) := hheightInv.symm
      _ = normHeight F (ptX' F xf yf) := by rw [hpointForm]
      _ = normHeight F (ptX' F x' y') := by rw [← hpoint]
      _ = ∏ w : InfinitePlace F, y' w :=
        specProper_normHeight_ptX' x' y' hbal'.1
  have hunitBounds := specProper_balanced_unit_bound (2 * d.B i) y y' a
    hbal hbal' hyFormula hprod
  have hεbound : ε ∈ unitSet i := by
    intro w
    simpa [unitSet, E, a] using (hunitBounds.2 w).1
  have hεlower (w : InfinitePlace F) : (E i)⁻¹ ≤ ‖a w‖ := by
    simpa [E] using (hunitBounds.2 w).2
  have hμbound (w : InfinitePlace F) : ‖w.embedding μ‖ ≤ M i := by
    have haff : x' w = a w ^ 2 * x w + a w * w.embedding μ := by
      simpa [xf] using hxFormula w
    have hmul : a w * w.embedding μ = x' w - a w ^ 2 * x w := by
      rw [haff]
      ring
    have hsq : ‖a w‖ ^ 2 ≤ (E i) ^ 2 := by
      have hupper := (hunitBounds.2 w).1
      nlinarith [mul_nonneg (sub_nonneg.mpr hupper) (norm_nonneg (a w))]
    have hnormProduct : ‖a w‖ * ‖w.embedding μ‖ ≤ R i + (E i) ^ 2 * R i := by
      calc
        ‖a w‖ * ‖w.embedding μ‖ = ‖a w * w.embedding μ‖ := by rw [norm_mul]
        _ = ‖x' w - a w ^ 2 * x w‖ := by rw [hmul]
        _ ≤ ‖x' w‖ + ‖a w ^ 2 * x w‖ := norm_sub_le _ _
        _ = ‖x' w‖ + ‖a w‖ ^ 2 * ‖x w‖ := by simp [norm_mul, norm_pow]
        _ ≤ R i + (E i) ^ 2 * R i := by
          apply add_le_add
          · exact hcoordBound i x' hx' w
          · exact mul_le_mul hsq (hcoordBound i x hx w) (norm_nonneg _) (sq_nonneg _)
    have hEpos : 0 < E i := Real.exp_pos _
    have hEa : 1 ≤ E i * ‖a w‖ := by
      calc
        1 = E i * (E i)⁻¹ := by simp [ne_of_gt hEpos]
        _ ≤ E i * ‖a w‖ := mul_le_mul_of_nonneg_left (hεlower w) hEpos.le
    calc
      ‖w.embedding μ‖ = 1 * ‖w.embedding μ‖ := by ring
      _ ≤ (E i * ‖a w‖) * ‖w.embedding μ‖ :=
        mul_le_mul_of_nonneg_right hEa (norm_nonneg _)
      _ = E i * (‖a w‖ * ‖w.embedding μ‖) := by ring
      _ ≤ E i * (R i + (E i) ^ 2 * R i) :=
        mul_le_mul_of_nonneg_left hnormProduct hEpos.le
      _ = M i := rfl
  have hparameters : (ε, μ) ∈ parameterSet i :=
    ⟨hεbound, hden, hμbound⟩
  have hrealizable : (ε, μ) ∈ realizableSet i := ⟨hparameters, ⟨γ, hform⟩⟩
  let q : {p // p ∈ realizableSet i} := ⟨(ε, μ), hrealizable⟩
  have hconj :
      (d.σ i)⁻¹ * toSLF F (chosenGamma i q : SL(2,𝓞 F)) * d.σ i =
        (d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i := by
    calc
      _ = cuspUnitMatrix F ε μ := by simpa [q] using hchosenGamma i q
      _ = _ := hform.symm
  have hmap : toSLF F (chosenGamma i q : SL(2,𝓞 F)) =
      toSLF F (γ : SL(2,𝓞 F)) := by
    calc
      _ = (d.σ i) *
          ((d.σ i)⁻¹ * toSLF F (chosenGamma i q : SL(2,𝓞 F)) * d.σ i) *
            (d.σ i)⁻¹ := by group
      _ = (d.σ i) *
          ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i) *
            (d.σ i)⁻¹ := by rw [hconj]
      _ = _ := by group
  have hgamma : chosenGamma i q = γ := by
    apply Subtype.ext
    exact toSLF_injective hmap
  change γ ∈ ⋃ k : d.ι, Set.range (chosenGamma k)
  rw [← hgamma]
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self q⟩
end ArtinPrimitiveRoots.A1.Spec
