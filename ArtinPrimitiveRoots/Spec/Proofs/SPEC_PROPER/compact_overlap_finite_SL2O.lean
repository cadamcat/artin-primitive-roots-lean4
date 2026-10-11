import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_integral_elements_with_embedding_bounds

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem compact_coordinate_bounds (C : Set (X F)) (hC : IsCompact C)
    (hCne : C.Nonempty) :
    ∃ m M R : ℝ, 0 < m ∧ 0 < M ∧ 0 ≤ R ∧
      ∀ z ∈ C, ∀ w : InfinitePlace F,
        m ≤ (coordsX F z w).2 ∧ (coordsX F z w).2 ≤ M ∧
          ‖(coordsX F z w).1‖ ≤ R := by
  classical
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  rcases hchart with ⟨e, _, heinv⟩
  have hcoord : Continuous (fun z : X F => (e.symm z).val) :=
    continuous_subtype_val.comp e.symm.continuous
  let Y : Set ℝ := ⋃ w : InfinitePlace F,
    (fun z : X F => ((e.symm z).val w).2) '' C
  have hYcompact : IsCompact Y := by
    change IsCompact (⋃ w : InfinitePlace F,
      (fun z : X F => ((e.symm z).val w).2) '' C)
    apply isCompact_iUnion
    intro w
    exact hC.image (continuous_snd.comp ((continuous_apply w).comp hcoord))
  obtain ⟨z₀, hz₀⟩ := hCne
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hYne : Y.Nonempty := by
    refine ⟨((e.symm z₀).val w₀).2, Set.mem_iUnion.mpr ⟨w₀, ?_⟩⟩
    exact Set.mem_image_of_mem _ hz₀
  have hYpos : ∀ y ∈ Y, 0 < y := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨w, hw⟩
    rcases hw with ⟨z, hz, rfl⟩
    have hp := (e.symm z).property
    simpa [posSet] using hp w
  obtain ⟨m, hmY, hmmin⟩ := hYcompact.exists_isMinOn hYne continuousOn_id
  obtain ⟨M, hMY, hMmax⟩ := hYcompact.exists_isMaxOn hYne continuousOn_id
  have hmpos : 0 < m := hYpos m hmY
  have hMpos : 0 < M := hYpos M hMY
  let Xnorm : Set ℝ := ⋃ w : InfinitePlace F,
    (fun z : X F => ‖((e.symm z).val w).1‖) '' C
  have hXcompact : IsCompact Xnorm := by
    change IsCompact (⋃ w : InfinitePlace F,
      (fun z : X F => ‖((e.symm z).val w).1‖) '' C)
    apply isCompact_iUnion
    intro w
    exact hC.image (continuous_norm.comp
      (continuous_fst.comp ((continuous_apply w).comp hcoord)))
  have hXne : Xnorm.Nonempty := by
    refine ⟨‖((e.symm z₀).val w₀).1‖, Set.mem_iUnion.mpr ⟨w₀, ?_⟩⟩
    exact Set.mem_image_of_mem _ hz₀
  obtain ⟨R₀, hR₀, hRmax⟩ := hXcompact.exists_isMaxOn hXne continuousOn_id
  have hR₀nonneg : 0 ≤ R₀ := by
    rcases Set.mem_iUnion.mp hR₀ with ⟨w, hw⟩
    rcases hw with ⟨z, hz, rfl⟩
    exact norm_nonneg _
  refine ⟨m, M, max R₀ 0, hmpos, hMpos, le_max_right _ _, ?_⟩
  intro z hz w
  have hyY : ((e.symm z).val w).2 ∈ Y :=
    Set.mem_iUnion.mpr ⟨w, Set.mem_image_of_mem _ hz⟩
  have hxY : ‖((e.symm z).val w).1‖ ∈ Xnorm :=
    Set.mem_iUnion.mpr ⟨w, Set.mem_image_of_mem _ hz⟩
  have hlo : m ≤ ((e.symm z).val w).2 := by
    exact (isMinOn_iff.mp hmmin) _ hyY
  have hhi : ((e.symm z).val w).2 ≤ M := by
    exact (isMaxOn_iff.mp hMmax) _ hyY
  have hxn : ‖((e.symm z).val w).1‖ ≤ R₀ := by
    exact (isMaxOn_iff.mp hRmax) _ hxY
  rw [← heinv z]
  exact ⟨hlo, hhi, hxn.trans (le_max_left _ _)⟩

private theorem compact_coord_height_action (g : SL(2,𝓞 F)) (z : X F)
    (w : InfinitePlace F) :
    (coordsX F (g • z) w).2 =
      (coordsX F z w).2 /
        (Complex.normSq ((toInf F (toSLF F g) w) 1 0 * (coordsX F z w).1 +
          (toInf F (toSLF F g) w) 1 1) +
          Complex.normSq ((toInf F (toSLF F g) w) 1 0) *
            (coordsX F z w).2 ^ 2) := by
  rcases G1_h3_basics (F := F) with ⟨_, _, hformula, _, _, _, _, _, _, _, _, _⟩
  let x := horiz (z w)
  let y := height (z w)
  have hy : 0 < y := by
    dsimp [y]
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : z w = pt x y := by
    dsimp [x, y]
    exact (pt_horiz_height (z w)).symm
  change height ((toInf F (toSLF F g) w) • z w) = _
  rw [hpt]
  simpa [x, y, coordsX] using hformula (toInf F (toSLF F g) w) x y hy

private theorem compact_row_entry_bounds (C : Set (X F))
    (m M R : ℝ)
    (hcoords : ∀ z ∈ C, ∀ w : InfinitePlace F,
      m ≤ (coordsX F z w).2 ∧ (coordsX F z w).2 ≤ M ∧
        ‖(coordsX F z w).1‖ ≤ R)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 ≤ R)
    (g : SL(2,𝓞 F)) (z : X F) (hz : z ∈ C) (hgz : (g : SL(2,𝓞 F)) • z ∈ C) :
    ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (g 1 0))‖ ≤ Real.sqrt (M / m ^ 3) ∧
      ‖w.embedding (algebraMap (𝓞 F) F (g 1 1))‖ ≤
        Real.sqrt (M / m) + R * Real.sqrt (M / m ^ 3) := by
  intro w
  let p := toInf F (toSLF F g) w
  let c := p 1 0
  let d := p 1 1
  let x := (coordsX F z w).1
  let y := (coordsX F z w).2
  let y' := (coordsX F ((g : SL(2,𝓞 F)) • z) w).2
  let q := Complex.normSq (c * x + d) + Complex.normSq c * y ^ 2
  have hsrc := hcoords z hz w
  have hdst := hcoords ((g : SL(2,𝓞 F)) • z) hgz w
  have hy : 0 < y := lt_of_lt_of_le hm hsrc.1
  have hy' : 0 < y' := lt_of_lt_of_le hm hdst.1
  have hform : y' = y / q := by
    simpa [p, c, d, x, y, y', q] using compact_coord_height_action (F := F) g z w
  have hqne : q ≠ 0 := by
    intro hq
    rw [hform, hq] at hy'
    norm_num at hy'
  have hqpos : 0 < q := by
    by_contra hnot
    have hqle : q ≤ 0 := le_of_not_gt hnot
    have hqneg : q < 0 := lt_of_le_of_ne hqle hqne
    have hneg : y / q < 0 := div_neg_of_pos_of_neg hy hqneg
    rw [← hform] at hneg
    exact (not_lt_of_ge (le_of_lt hy')) hneg
  have hqeq : q = y / y' := by
    have hmul : y' * q = y := by
      calc
        y' * q = (y / q) * q := by rw [hform]
        _ = y := div_mul_cancel₀ y hqne
    apply (eq_div_iff hy'.ne').2
    nlinarith [hmul]
  have hqmul : q * m ≤ M := by
    calc
      q * m ≤ q * y' := mul_le_mul_of_nonneg_left hdst.1 hqpos.le
      _ = y := by rw [hqeq]; field_simp [hy'.ne']
      _ ≤ M := hsrc.2.1
  have hqle : q ≤ M / m := (le_div_iff₀ hm).2 hqmul
  have hysq : m ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hm.le hy.le).2 hsrc.1
  have hcM2 : Complex.normSq c * m ^ 2 ≤ M / m := by
    calc
      Complex.normSq c * m ^ 2 ≤ Complex.normSq c * y ^ 2 :=
        mul_le_mul_of_nonneg_left hysq (Complex.normSq_nonneg _)
      _ ≤ q := le_add_of_nonneg_left (Complex.normSq_nonneg _)
      _ ≤ M / m := hqle
  have hcM3 : Complex.normSq c * m ^ 3 ≤ M := by
    calc
      Complex.normSq c * m ^ 3 = (Complex.normSq c * m ^ 2) * m := by ring
      _ ≤ (M / m) * m := mul_le_mul_of_nonneg_right hcM2 hm.le
      _ = M := div_mul_cancel₀ M hm.ne'
  have hcSq : Complex.normSq c ≤ M / m ^ 3 := (le_div_iff₀ (pow_pos hm 3)).2 hcM3
  have hcNorm : ‖c‖ ≤ Real.sqrt (M / m ^ 3) := by
    calc
      ‖c‖ = Real.sqrt (Complex.normSq c) := by
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (M / m ^ 3) := Real.sqrt_le_sqrt hcSq
  have hdSq : Complex.normSq (c * x + d) ≤ q :=
    le_add_of_nonneg_right (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg y))
  have hdM : Complex.normSq (c * x + d) ≤ M / m := hdSq.trans hqle
  have hdNorm : ‖c * x + d‖ ≤ Real.sqrt (M / m) := by
    calc
      ‖c * x + d‖ = Real.sqrt (Complex.normSq (c * x + d)) := by
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (M / m) := Real.sqrt_le_sqrt hdM
  have hcx : ‖c * x‖ ≤ Real.sqrt (M / m ^ 3) * R := by
    rw [norm_mul]
    calc
      ‖c‖ * ‖x‖ ≤ Real.sqrt (M / m ^ 3) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hcNorm (norm_nonneg _)
      _ ≤ Real.sqrt (M / m ^ 3) * R :=
        mul_le_mul_of_nonneg_left hsrc.2.2 (Real.sqrt_nonneg _)
  have hd : ‖d‖ ≤ Real.sqrt (M / m) + R * Real.sqrt (M / m ^ 3) := by
    calc
      ‖d‖ = ‖(c * x + d) - c * x‖ := by congr 1 <;> ring
      _ ≤ ‖c * x + d‖ + ‖c * x‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (M / m) + Real.sqrt (M / m ^ 3) * R := add_le_add hdNorm hcx
      _ = Real.sqrt (M / m) + R * Real.sqrt (M / m ^ 3) := by ring
  constructor
  · simpa [c, p, toInf, toSLF] using hcNorm
  · simpa [d, c, p, toInf, toSLF] using hd

/-- Only finitely many integral determinant-one matrices move one compact set to meet another.
Uses G1_h3_basics, G2_x_action and
finite_integral_elements_with_embedding_bounds; feeds R9_proper, low-height finiteness,
free_action_wandering_nbhd and local_finite_overlap. -/
theorem compact_overlap_finite_SL2O (K K' : Set (X F))
    (hK : IsCompact K) (hK' : IsCompact K') :
    {γ : SL(2,𝓞 F) | ∃ z ∈ K, γ • z ∈ K'}.Finite := by
  classical
  by_cases hKempty : K = ∅
  · simp [hKempty]
  by_cases hK'empty : K' = ∅
  · simp [hK'empty]
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  have hK'ne : K'.Nonempty := Set.nonempty_iff_ne_empty.mpr hK'empty
  let J : SL(2,𝓞 F) :=
    ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; norm_num⟩
  rcases G2_x_action (F := F) with ⟨_, _, _, hhomeo, _⟩
  obtain ⟨eJ, heJ, _⟩ := hhomeo (toInf F (toSLF F J))
  have heJact (z : X F) : eJ z = (toSLF F J) • z := by
    rw [heJ z]
    funext w
    rfl
  let KJ : Set (X F) := eJ '' K'
  have hKJ : IsCompact KJ := hK'.image eJ.continuous
  let C : Set (X F) := K ∪ K' ∪ KJ
  have hC : IsCompact C := hK.union hK' |>.union hKJ
  have hCne : C.Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    exact ⟨z, by simp [C, hz]⟩
  obtain ⟨m, M, R, hm, hM, hR, hcoords⟩ := compact_coordinate_bounds (F := F) C hC hCne
  let bc : ℝ := Real.sqrt (M / m ^ 3)
  let bd : ℝ := Real.sqrt (M / m) + R * bc
  let B : ℝ := max bc bd
  have hB : 0 ≤ B := by positivity
  let E : Set (𝓞 F) := {a | ∀ w : InfinitePlace F,
    ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ B}
  have hE : E.Finite := finite_integral_elements_with_embedding_bounds B hB
  let MS : Set (Matrix (Fin 2) (Fin 2) (𝓞 F)) :=
    {M | ∀ i j, M i j ∈ E}
  have hMS : MS.Finite := by
    change {M : Matrix (Fin 2) (Fin 2) (𝓞 F) | ∀ i j, M i j ∈ E}.Finite
    exact Set.Finite.pi' (fun _ : Fin 2 => Set.Finite.pi' (fun _ : Fin 2 => hE))
  let S : Set (SL(2,𝓞 F)) := {γ | ∀ i j, γ i j ∈ E}
  have hS : S.Finite := by
    apply Set.Finite.of_finite_image (f := fun γ : SL(2,𝓞 F) =>
      (γ : Matrix (Fin 2) (Fin 2) (𝓞 F)))
    · apply hMS.subset
      rintro M ⟨γ, hγ, rfl⟩
      exact hγ
    · exact Set.injOn_of_injective Subtype.val_injective
  apply hS.subset
  intro γ hγ
  change ∀ i j : Fin 2, γ i j ∈ E
  rcases hγ with ⟨z, hzK, hγzK'⟩
  have hzC : z ∈ C := by exact Set.mem_union_left KJ (Set.mem_union_left K' hzK)
  have hγzC : γ • z ∈ C := by
    exact Set.mem_union_left KJ (Set.mem_union_right K hγzK')
  have hrowγ := compact_row_entry_bounds (F := F) C m M R hcoords hm hM hR γ z
    hzC hγzC
  let δ : SL(2,𝓞 F) := J * γ
  have hδeq : (δ : SL(2,𝓞 F)) • z = eJ ((γ : SL(2,𝓞 F)) • z) := by
    calc
      (δ : SL(2,𝓞 F)) • z = (J : SL(2,𝓞 F)) • ((γ : SL(2,𝓞 F)) • z) :=
        (smul_smul J γ z).symm
      _ = eJ ((γ : SL(2,𝓞 F)) • z) := (heJact _).symm
  have hδz : (δ : SL(2,𝓞 F)) • z ∈ KJ := by
    rw [hδeq]
    exact Set.mem_image_of_mem eJ hγzK'
  have hδC : (δ : SL(2,𝓞 F)) • z ∈ C := by
    exact Set.mem_union_right (K ∪ K') hδz
  have hrowδ := compact_row_entry_bounds (F := F) C m M R hcoords hm hM hR δ z
    hzC hδC
  have hδmat : (δ : Matrix (Fin 2) (Fin 2) (𝓞 F)) =
      (J : Matrix (Fin 2) (Fin 2) (𝓞 F)) * (γ : Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    simp [δ]
  have hδ10 : δ 1 0 = γ 0 0 := by
    have h := congrFun (congrFun hδmat 1) 0
    simpa [J, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hδ11 : δ 1 1 = γ 0 1 := by
    have h := congrFun (congrFun hδmat 1) 1
    simpa [J, Matrix.mul_apply, Fin.sum_univ_two] using h
  have h00 : ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (γ 0 0))‖ ≤ B := by
    intro w
    have hh := (hrowδ w).1
    simpa [hδ10, bc, B] using hh.trans (le_max_left bc bd)
  have h01 : ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (γ 0 1))‖ ≤ B := by
    intro w
    have hh := (hrowδ w).2
    simpa [hδ11, bc, bd, B] using hh.trans (le_max_right bc bd)
  have h10 : ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (γ 1 0))‖ ≤ B := by
    intro w
    have hh := (hrowγ w).1
    simpa [bc, B] using hh.trans (le_max_left bc bd)
  have h11 : ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (γ 1 1))‖ ≤ B := by
    intro w
    have hh := (hrowγ w).2
    simpa [bd, B] using hh.trans (le_max_right bc bd)
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11
end ArtinPrimitiveRoots.A1.Spec
