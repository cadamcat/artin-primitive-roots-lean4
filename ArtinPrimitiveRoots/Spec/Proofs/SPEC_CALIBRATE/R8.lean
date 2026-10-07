import ArtinPrimitiveRoots.Spec.Stage1

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma r8_bottomRowIdeal_coe (g : SL(2,F)) :
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F) =
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
  rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_coe]
  have hrange : Set.range (fun i : Fin 2 =>
      if i = 0 then (bottomRow F g).1 else (bottomRow F g).2) = {g 1 0, g 1 1} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [bottomRow]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact ⟨0, by simp [bottomRow, h.symm]⟩
      · exact ⟨1, by simp [bottomRow, h.symm]⟩
  simp only [Finset.coe_univ, Set.image_univ, hrange]

private lemma r8_bottomRowIdeal_eq_span (a b : 𝓞 F) (g : SL(2,F))
    (h₀ : g 1 0 = algebraMap (𝓞 F) F a)
    (h₁ : g 1 1 = algebraMap (𝓞 F) F b) :
    bottomRowFractionalIdeal F g = (Ideal.span ({a, b} : Set (𝓞 F)) :
      FractionalIdeal (𝓞 F)⁰ F) := by
  apply FractionalIdeal.coeToSubmodule_inj.mp
  rw [r8_bottomRowIdeal_coe, FractionalIdeal.coe_coeIdeal,
    IsLocalization.coeSubmodule_span, h₀, h₁]
  congr 1
  ext x
  simp

private lemma r8_bottomRowIdeal_right_le (g : SL(2,F)) (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) ≤ bottomRowFractionalIdeal F g := by
  change (bottomRowFractionalIdeal F (g * toSLF F γ) : Submodule (𝓞 F) F) ≤
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [r8_bottomRowIdeal_coe, r8_bottomRowIdeal_coe]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hrow₀ : (g * toSLF F γ) 1 0 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 0) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hrow₁ : (g * toSLF F γ) 1 1 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 1) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hc : g 1 0 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hd : g 1 1 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hca (u : 𝓞 F) : g 1 0 * algebraMap (𝓞 F) F u ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) u hc)
  have hdb (u : 𝓞 F) : g 1 1 * algebraMap (𝓞 F) F u ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) u hd)
  rcases hx with hx | hx
  · rw [hx, hrow₀]
    exact Submodule.add_mem _ (hca _) (hdb _)
  · rw [hx, hrow₁]
    exact Submodule.add_mem _ (hca _) (hdb _)

private lemma r8_bottomRowIdeal_right (g : SL(2,F)) (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) = bottomRowFractionalIdeal F g := by
  apply le_antisymm (r8_bottomRowIdeal_right_le g γ)
  have hmul : (g * toSLF F γ) * toSLF F γ⁻¹ = g := by simp [mul_assoc]
  have h := r8_bottomRowIdeal_right_le (g * toSLF F γ) γ⁻¹
  rw [hmul] at h
  exact h

private lemma r8_bottomRowIdeal_left_borel (b : SL(2,F)) (hb : b ∈ borelSL F)
    (g : SL(2,F)) :
    b 1 1 ≠ 0 ∧ bottomRowFractionalIdeal F (b * g) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) * bottomRowFractionalIdeal F g := by
  have hb₀ : b 1 0 = 0 := hb
  have hu : b 1 1 ≠ 0 := by
    intro hzero
    have hdet : Matrix.det (b : Matrix (Fin 2) (Fin 2) F) = 1 := b.2
    rw [Matrix.det_fin_two, hb₀, hzero] at hdet
    norm_num at hdet
  have hrow₀ : (b * g) 1 0 = b 1 1 * g 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hb₀]
  have hrow₁ : (b * g) 1 1 = b 1 1 * g 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hb₀]
  refine ⟨hu, ?_⟩
  apply FractionalIdeal.coeToSubmodule_inj.mp
  rw [r8_bottomRowIdeal_coe, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, r8_bottomRowIdeal_coe,
    hrow₀, hrow₁, Submodule.span_mul_span]
  apply congrArg (Submodule.span (𝓞 F))
  ext x
  simp

private lemma r8_exists_matrix_with_bottomRow (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ g : SL(2,F), g 1 0 = a ∧ g 1 1 = b := by
  by_cases hb : b ≠ 0
  · refine ⟨⟨!![b⁻¹, 0; a, b], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [hb]
    · simp
    · simp
  · have ha : a ≠ 0 := h.resolve_right hb
    refine ⟨⟨!![0, -a⁻¹; a, 0], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [ha]
    · simp
    · simpa using (not_ne_iff.mp hb).symm

private lemma r8_rowHeightForm_scale (β : F) (v : F × F) (z : X F)
    (w : InfinitePlace F) :
    rowHeightForm F (β * v.1, β * v.2) z w =
      Complex.normSq (w.embedding β) * rowHeightForm F v z w := by
  unfold rowHeightForm
  simp only [map_mul]
  have hsum : w.embedding β * w.embedding v.1 * (coordsX F z w).1 +
      w.embedding β * w.embedding v.2 =
      w.embedding β * (w.embedding v.1 * (coordsX F z w).1 +
        w.embedding v.2) := by ring
  rw [hsum, Complex.normSq_mul]
  ring_nf

private lemma r8_normHeight_rowProduct (g : SL(2,F)) (z : X F) :
    normHeight F (g • z) =
      (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g) z w)⁻¹ := by
  let x : InfinitePlace F → ℂ := fun w => horiz (z w)
  let y : InfinitePlace F → ℝ := fun w => height (z w)
  have hy : ∀ w, 0 < y w := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hz : z = ptX' F x y := by
    funext w
    exact (pt_horiz_height (z w)).symm
  have hformula := (G2_x_action (F := F)).1 g x y hy
  rw [hz, hformula]
  have hden (w : InfinitePlace F) :
      Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
        Complex.normSq (w.embedding (g 1 0)) * y w ^ 2 ≠ 0 := by
    have hp : 0 < height ((g • ptX' F x y) w) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos ((g • ptX' F x y) w)
    have hloc := height_smul_ptX'_at g x y hy w
    rw [hloc] at hp
    intro hzero
    rw [hzero, div_zero] at hp
    exact (lt_irrefl 0) hp
  have hlocal (w : InfinitePlace F) :
      (rowHeightForm F (bottomRow F g) (ptX' F x y) w)⁻¹ =
        y w /
          (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
            Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
    simp only [rowHeightForm, coordsX, ptX', bottomRow]
    rw [horiz_pt (x w) (y w) (hy w), height_pt (x w) (y w) (hy w)]
    field_simp [hy w, hden w]
    <;> ring_nf
  calc
    (∏ w : InfinitePlace F,
        y w / (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
          Complex.normSq (w.embedding (g 1 0)) * y w ^ 2)) =
        ∏ w : InfinitePlace F,
          (rowHeightForm F (bottomRow F g) (ptX' F x y) w)⁻¹ := by
      apply Finset.prod_congr rfl
      intro w hw
      simpa [div_eq_mul_inv] using (hlocal w).symm
    _ = (∏ w : InfinitePlace F,
          rowHeightForm F (bottomRow F g) (ptX' F x y) w)⁻¹ := by
      rw [Finset.prod_inv_distrib]

private lemma r8_cuspUnitMatrix_mul (ε ε' : (𝓞 F)ˣ) (μ μ' : F) :
    cuspUnitMatrix F ε μ * cuspUnitMatrix F ε' μ' =
      cuspUnitMatrix F (ε * ε')
        (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ' +
          μ * (algebraMap (𝓞 F) F (ε' : 𝓞 F))⁻¹) := by
  let a : F := algebraMap (𝓞 F) F (ε : 𝓞 F)
  let a' : F := algebraMap (𝓞 F) F (ε' : 𝓞 F)
  have ha : a ≠ 0 := by
    intro hz
    apply ε.ne_zero
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa [a] using hz
  have ha' : a' ≠ 0 := by
    intro hz
    apply ε'.ne_zero
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa [a'] using hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspUnitMatrix, Matrix.mul_apply, Fin.sum_univ_two, map_mul,
      map_inv₀, a, a'] <;> field_simp [ha, ha'] <;> ring

private lemma r8_cuspUnitMatrix_inv (ε : (𝓞 F)ˣ) (μ : F) :
    (cuspUnitMatrix F ε μ)⁻¹ = cuspUnitMatrix F ε⁻¹ (-μ) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspUnitMatrix]

private def r8_cuspUnitSetSubgroup (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    Subgroup ((𝓞 F)ˣ) where
  carrier := cuspUnitSet F Γ σ
  one_mem' := by
    refine ⟨0, 1, ?_⟩
    have hmat : (1 : SL(2,F)) = cuspUnitMatrix F 1 0 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cuspUnitMatrix]
    simpa [cuspUnitSet] using hmat
  mul_mem' := by
    intro ε ε' hε hε'
    rcases hε with ⟨μ, γ, hγ⟩
    rcases hε' with ⟨μ', γ', hγ'⟩
    refine ⟨algebraMap (𝓞 F) F (ε : 𝓞 F) * μ' +
      μ * (algebraMap (𝓞 F) F (ε' : 𝓞 F))⁻¹, γ * γ', ?_⟩
    calc
      σ⁻¹ * toSLF F ((γ * γ' : Γ) : SL(2,𝓞 F)) * σ =
          (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) *
            (σ⁻¹ * toSLF F (γ' : SL(2,𝓞 F)) * σ) := by
        simp [map_mul]
        group
      _ = cuspUnitMatrix F ε μ * cuspUnitMatrix F ε' μ' := by rw [hγ, hγ']
      _ = cuspUnitMatrix F (ε * ε')
          (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ' +
            μ * (algebraMap (𝓞 F) F (ε' : 𝓞 F))⁻¹) :=
        r8_cuspUnitMatrix_mul ε ε' μ μ'
  inv_mem' := by
    intro ε hε
    rcases hε with ⟨μ, γ, hγ⟩
    refine ⟨-μ, γ⁻¹, ?_⟩
    calc
      σ⁻¹ * toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
          (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ)⁻¹ := by
        simp [map_inv, _root_.mul_inv_rev]
        group
      _ = (cuspUnitMatrix F ε μ)⁻¹ := by rw [hγ]
      _ = cuspUnitMatrix F ε⁻¹ (-μ) := r8_cuspUnitMatrix_inv ε μ

private lemma r8_cuspUnits_mem_iff_set (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (ε : (𝓞 F)ˣ) : ε ∈ cuspUnits F Γ σ ↔ ε ∈ cuspUnitSet F Γ σ := by
  have hclosure : cuspUnits F Γ σ = r8_cuspUnitSetSubgroup Γ σ := by
    change Subgroup.closure (cuspUnitSet F Γ σ) = r8_cuspUnitSetSubgroup Γ σ
    exact Subgroup.closure_eq (r8_cuspUnitSetSubgroup Γ σ)
  rw [hclosure]
  rfl

private lemma r8_rowProduct_scale (β : F) (v : F × F) (z : X F) :
    (∏ w : InfinitePlace F, rowHeightForm F (β * v.1, β * v.2) z w) =
      absFieldNorm F β * (∏ w : InfinitePlace F, rowHeightForm F v z w) := by
  calc
    _ = ∏ w : InfinitePlace F,
        Complex.normSq (w.embedding β) * rowHeightForm F v z w := by
      apply Finset.prod_congr rfl
      intro w hw
      exact r8_rowHeightForm_scale β v z w
    _ = (∏ w : InfinitePlace F, Complex.normSq (w.embedding β)) *
        (∏ w : InfinitePlace F, rowHeightForm F v z w) := Finset.prod_mul_distrib
    _ = absFieldNorm F β * (∏ w : InfinitePlace F, rowHeightForm F v z w) := by
      simp [absFieldNorm, Complex.normSq_eq_norm_sq]

private lemma r8_absNorm_spanSingleton_mul (β : F)
    (J : FractionalIdeal (𝓞 F)⁰ F) :
    FractionalIdeal.absNorm
        (FractionalIdeal.spanSingleton (𝓞 F)⁰ β * J) =
      |Algebra.norm ℚ β| * FractionalIdeal.absNorm J := by
  rw [map_mul, FractionalIdeal.absNorm_span_singleton]

private lemma r8_cuspLattice_realize (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (a : F) (ha : a ∈ cuspLattice F Γ σ) :
    ∃ γ : Γ, σ * upperHom F (Multiplicative.ofAdd a) * σ⁻¹ =
      toSLF F (γ : SL(2,𝓞 F)) := by
  have hmap :
      ((MulAut.conj σ).toMonoidHom.comp (upperHom F)) (Multiplicative.ofAdd a) ∈
        Γ.map (toSLF F) := by
    simpa [cuspLattice] using ha
  have hmap' := (Subgroup.mem_map.mp hmap)
  rcases hmap' with ⟨g, hg, hEq⟩
  refine ⟨⟨g, hg⟩, ?_⟩
  simpa [map_mul, map_inv] using hEq.symm

private lemma r8_absNorm_scale (β : F) (J : Ideal (𝓞 F))
    (I : FractionalIdeal (𝓞 F)⁰ F)
    (hI : I = FractionalIdeal.spanSingleton (𝓞 F)⁰ β *
      (J : FractionalIdeal (𝓞 F)⁰ F)) :
    absFieldNorm F β * ((Ideal.absNorm J : ℚ) : ℝ) =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have hnorm : FractionalIdeal.absNorm I =
      |Algebra.norm ℚ β| * (Ideal.absNorm J : ℚ) := by
    rw [hI, r8_absNorm_spanSingleton_mul, FractionalIdeal.coeIdeal_absNorm]
  have hnormR : ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      |Algebra.norm ℚ β| * (Ideal.absNorm J : ℝ) := by
    exact_mod_cast hnorm
  rw [absFieldNorm_eq_abs_norm]
  simpa using hnormR.symm

private lemma r8_integralIdeal_absNorm_ge_one (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (1 : ℕ) ≤ Ideal.absNorm J := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hzero
  exact hJ (Ideal.absNorm_eq_zero_iff.mp hzero)

private lemma r8_normHeight_pos (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private lemma r8_mixed_smul_assoc (g : SL(2,F)) (γ : SL(2,𝓞 F)) (z : X F) :
    g • (γ • z) = (g * toSLF F γ) • z := by
  funext w
  change (Matrix.SpecialLinearGroup.map w.embedding g) •
      ((Matrix.SpecialLinearGroup.map w.embedding (toSLF F γ)) • z w) =
    (Matrix.SpecialLinearGroup.map w.embedding (g * toSLF F γ)) • z w
  rw [smul_smul, map_mul]

private lemma r8_cuspUnit_height (ε : (𝓞 F)ˣ) (μ : F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) :
    height ((cuspUnitMatrix F ε μ • ptX' F x y) w) = unitHeightAction F ε y w := by
  rw [height_smul_ptX'_at (cuspUnitMatrix F ε μ) x y hy w]
  simp [cuspUnitMatrix, unitHeightAction, Complex.normSq_inv]
  ring_nf

private lemma r8_translation_pt (a : F) (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    upperHom F (Multiplicative.ofAdd a) • ptX' F x y =
      ptX' F (fun w => w.embedding a + x w) y := by
  funext w
  have hU : ((upperHom F (Multiplicative.ofAdd a) : SL(2,F)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := by
    change !![1, Multiplicative.toAdd (Multiplicative.ofAdd a); 0, 1] =
      !![1, a; 0, 1]
    simp
  have hUmap :
      ((Matrix.SpecialLinearGroup.map w.embedding
        (upperHom F (Multiplicative.ofAdd a)) : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![1, w.embedding a; 0, 1] := by
    change w.embedding.mapMatrix
      ((upperHom F (Multiplicative.ofAdd a) : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  have hmat :
      Matrix.SpecialLinearGroup.map w.embedding (upperHom F (Multiplicative.ofAdd a)) *
          ptMat (x w) (y w) (hy w) =
        ptMat (w.embedding a + x w) (y w) (hy w) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change ((Matrix.SpecialLinearGroup.map w.embedding
        (upperHom F (Multiplicative.ofAdd a)) : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
          (ptMat (x w) (y w) (hy w) : Matrix (Fin 2) (Fin 2) ℂ) =
      (ptMat (w.embedding a + x w) (y w) (hy w) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [hUmap]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
        (try field_simp [ne_of_gt (Real.sqrt_pos.mpr (hy w))]) <;> ring
  change (Matrix.SpecialLinearGroup.map w.embedding
      (upperHom F (Multiplicative.ofAdd a))) • pt (x w) (y w) =
    pt (w.embedding a + x w) (y w)
  simp only [pt, dif_pos (hy w)]
  change QuotientGroup.mk
      (Matrix.SpecialLinearGroup.map w.embedding (upperHom F (Multiplicative.ofAdd a)) *
        ptMat (x w) (y w) (hy w)) =
    QuotientGroup.mk (ptMat (w.embedding a + x w) (y w) (hy w))
  rw [hmat]

private lemma r8_balanced_unitAction (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (B : ℝ)
    (hB : ∀ w, |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ *
        Real.sqrt (y w)) -
      (placeCount F)⁻¹ *
        ∑ w' : InfinitePlace F, Real.log (Real.sqrt (y w'))| ≤ B) :
    IsBalancedHeights F (2 * B) (unitHeightAction F ε y) := by
  classical
  let t : InfinitePlace F → ℝ := fun w => Real.sqrt (y w)
  have ht : ∀ w, 0 < t w := fun w => Real.sqrt_pos.mpr (hy w)
  have hFunit : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 := by
    intro h
    apply ε.ne_zero
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h
  have hEmbed (w : InfinitePlace F) :
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) ≠ 0 := by
    intro h
    apply hFunit
    apply w.embedding.injective
    simpa using h
  have hnormpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ :=
    norm_pos_iff.mpr (hEmbed w)
  have hargpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w :=
    mul_pos (hnormpos w) (ht w)
  have hlog (w : InfinitePlace F) :
      Real.log (unitHeightAction F ε y w) =
        2 * Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by
    have hsq : unitHeightAction F ε y w =
        (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) ^ 2 := by
      change Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w = _
      rw [Complex.normSq_eq_norm_sq]
      have ht2 : t w ^ 2 = y w := by
        dsimp [t]
        exact Real.sq_sqrt (hy w).le
      rw [← ht2]
      ring
    rw [hsq, Real.log_pow]
    norm_num
  have hlogMul (w : InfinitePlace F) :
      Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) =
        Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ + Real.log (t w) :=
    Real.log_mul (hnormpos w).ne' (ht w).ne'
  have hfieldnorm : absFieldNorm F (algebraMap (𝓞 F) F (ε : 𝓞 F)) = 1 := by
    simpa [absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  have hprodSq : (∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖) ^ 2 = 1 := by
    calc
      _ = ∏ w : InfinitePlace F,
          ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ ^ 2 := by
        rw [Finset.prod_pow]
      _ = absFieldNorm F (algebraMap (𝓞 F) F (ε : 𝓞 F)) := by
        simp [absFieldNorm]
      _ = 1 := hfieldnorm
  have hprodPos : 0 < ∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := by
    apply Finset.prod_pos
    intro w hw
    exact hnormpos w
  have hprodOne : ∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 1 := by
    nlinarith [hprodSq]
  have hsumNorm : ∑ w : InfinitePlace F,
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
    calc
      _ = Real.log (∏ w : InfinitePlace F,
          ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖) := by
        symm
        apply Real.log_prod
        intro w hw
        exact (hnormpos w).ne'
      _ = 0 := by rw [hprodOne]; simp
  have hsum :
      (∑ w : InfinitePlace F, Real.log (unitHeightAction F ε y w)) =
        2 * ∑ w : InfinitePlace F, Real.log (t w) := by
    calc
      _ = ∑ w : InfinitePlace F,
          2 * Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hlog w
      _ = 2 * ∑ w : InfinitePlace F,
          Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by
        rw [← Finset.mul_sum]
      _ = 2 * (∑ w : InfinitePlace F,
          Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ +
            ∑ w : InfinitePlace F, Real.log (t w)) := by
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        exact hlogMul w
      _ = 2 * ∑ w : InfinitePlace F, Real.log (t w) := by
        rw [hsumNorm, zero_add]
  constructor
  · intro w
    unfold unitHeightAction
    exact mul_pos (Complex.normSq_pos.mpr (hEmbed w)) (hy w)
  · intro w
    change |Real.log (unitHeightAction F ε y w) -
      (placeCount F)⁻¹ * ∑ w' : InfinitePlace F,
        Real.log (unitHeightAction F ε y w')| ≤ 2 * B
    have hrewrite :
        Real.log (unitHeightAction F ε y w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F,
              Real.log (unitHeightAction F ε y w') =
          2 * (Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')) := by
      rw [hlog w, hsum]
      ring
    rw [hrewrite]
    calc
      |(2 : ℝ) * (Real.log
          (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w'))| =
        2 * |Real.log
          (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| := by
        simp
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left (hB w) (by norm_num)

private lemma r8_minkowski_reduction (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (z : X F) :
    ∃ (i : d.ι) (γ : Γ) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z) = ptX' F x y ∧
      (∀ w, 0 < y w) ∧
      SiegelData.lowerHeight F d i ≤
        normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) := by
  classical
  obtain ⟨v, hv, hmink⟩ := d.minkowski z
  let a : F := algebraMap (𝓞 F) F v.1
  let b : F := algebraMap (𝓞 F) F v.2
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    apply Prod.ext
    · apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      simpa [a] using hn.1
    · apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      simpa [b] using hn.2
  obtain ⟨g₀, hg₀a, hg₀b⟩ := r8_exists_matrix_with_bottomRow a b hab
  have hrow₀ : bottomRow F g₀ = (a, b) := Prod.ext hg₀a hg₀b
  have hPbound :
      (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w) ≤ d.C_M := by
    simpa [bottomRow, hg₀a, hg₀b, a, b] using hmink
  let f : (Σ j, CuspCosets F Γ (d.σ j)) →
      Quotient (QuotientGroup.rightRel (borelSL F)) := fun p =>
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      ((d.σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))
  obtain ⟨p, hp⟩ := d.reps_bijective.2
    (Quotient.mk (QuotientGroup.rightRel (borelSL F)) g₀)
  let i : d.ι := p.1
  let γ₀ : Γ := p.2.out
  let σi : SL(2,F) := d.σ i
  let gI : SL(2,F) := σi⁻¹
  let f₀ : SL(2,F) := gI * toSLF F (γ₀ : SL(2,𝓞 F))
  have hq : Quotient.mk (QuotientGroup.rightRel (borelSL F)) f₀ =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) g₀ := by
    simpa [f, i, γ₀, σi, gI, f₀] using hp
  have hrel : g₀ * f₀⁻¹ ∈ borelSL F :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  let bmat : SL(2,F) := f₀ * g₀⁻¹
  have hborel : bmat ∈ borelSL F := by
    have hinv := (borelSL F).inv_mem hrel
    simpa [bmat, _root_.mul_inv_rev] using hinv
  have hfactor : bmat * g₀ = f₀ := by
    dsimp [bmat]
    group
  let β : F := bmat 1 1
  have hβ : β ≠ 0 := (r8_bottomRowIdeal_left_borel bmat hborel g₀).1
  have hrowf : bottomRow F f₀ = (β * a, β * b) := by
    have hb10 : bmat 1 0 = 0 := hborel
    rw [← hfactor]
    apply Prod.ext
    · change (bmat * g₀) 1 0 = β * a
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp [β, hb10, hg₀a]
    · change (bmat * g₀) 1 1 = β * b
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp [β, hb10, hg₀b]
  have hIright : bottomRowFractionalIdeal F f₀ =
      bottomRowFractionalIdeal F gI := by
    dsimp [f₀, gI]
    exact r8_bottomRowIdeal_right _ (γ₀ : SL(2,𝓞 F))
  let J : Ideal (𝓞 F) := Ideal.span ({v.1, v.2} : Set (𝓞 F))
  have hJ : bottomRowFractionalIdeal F g₀ = (J : FractionalIdeal (𝓞 F)⁰ F) := by
    apply r8_bottomRowIdeal_eq_span v.1 v.2 g₀ hg₀a hg₀b
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hzero : bottomRowFractionalIdeal F g₀ = 0 := by
      rw [hJ, hbot]
      simp
    exact (R3_cusps_finite (F := F) Γ).2.1 g₀ hzero
  have hscaleB := (r8_bottomRowIdeal_left_borel bmat hborel g₀).2
  have hIscale : bottomRowFractionalIdeal F gI =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (J : FractionalIdeal (𝓞 F)⁰ F) := by
    calc
      _ = bottomRowFractionalIdeal F f₀ := hIright.symm
      _ = bottomRowFractionalIdeal F (bmat * g₀) := by rw [hfactor]
      _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ β * bottomRowFractionalIdeal F g₀ := by
        simpa [β] using hscaleB
      _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (J : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [hJ]
  have hcal := r8_absNorm_scale β J (bottomRowFractionalIdeal F gI) hIscale
  have hJnormN : (1 : ℕ) ≤ Ideal.absNorm J := r8_integralIdeal_absNorm_ge_one J hJne
  have hJnorm : (1 : ℝ) ≤ ((Ideal.absNorm J : ℚ) : ℝ) := by exact_mod_cast hJnormN
  have hβnonneg : 0 ≤ absFieldNorm F β := by
    unfold absFieldNorm
    positivity
  have hNi : 0 ≤ ((FractionalIdeal.absNorm
      (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) := by
    rw [← hcal]
    positivity
  have hβle : absFieldNorm F β ≤
      ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) := by
    calc
      absFieldNorm F β = absFieldNorm F β * 1 := by ring
      _ ≤ absFieldNorm F β * ((Ideal.absNorm J : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hJnorm hβnonneg
      _ = ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) := hcal
  have hPpos : 0 < ∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w := by
    have hN := r8_normHeight_pos (g₀ • z)
    rw [r8_normHeight_rowProduct] at hN
    exact inv_pos.mp hN
  have hdenle :
      absFieldNorm F β *
        (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w) ≤
      ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) * d.C_M := by
    calc
      _ ≤ ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) *
          (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w) :=
        mul_le_mul_of_nonneg_right hβle hPpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hPbound hNi
  have hrowprod :
      (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F f₀) z w) =
        absFieldNorm F β *
      (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w) := by
    rw [hrowf]
    calc
      _ = ∏ w : InfinitePlace F, rowHeightForm F (β * a, β * b) z w := rfl
      _ = absFieldNorm F β * (∏ w : InfinitePlace F,
          rowHeightForm F (a, b) z w) := r8_rowProduct_scale β (a, b) z
      _ = absFieldNorm F β * (∏ w : InfinitePlace F,
          rowHeightForm F (bottomRow F g₀) z w) := by rw [← hrow₀]
  have hNf : normHeight F (f₀ • z) =
      (absFieldNorm F β *
        (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w))⁻¹ := by
    rw [r8_normHeight_rowProduct, hrowprod]
  have hdenpos := inv_pos.mp (by rw [← hNf]; exact r8_normHeight_pos (f₀ • z))
  have htargetpos :
      0 < ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) * d.C_M :=
    lt_of_lt_of_le hdenpos hdenle
  have hheight :
      ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ)⁻¹ * d.C_M⁻¹ ≤
        normHeight F (f₀ • z) := by
    rw [hNf]
    have hrecip := one_div_le_one_div_of_le hdenpos hdenle
    calc
      _ = 1 / (((FractionalIdeal.absNorm (bottomRowFractionalIdeal F gI) : ℚ) : ℝ) * d.C_M) := by
        simp only [one_div, _root_.mul_inv_rev]
        ring
      _ ≤ 1 / (absFieldNorm F β *
          (∏ w : InfinitePlace F, rowHeightForm F (bottomRow F g₀) z w)) := hrecip
      _ = _ := by simpa [one_div] using hNf.symm
  let x : InfinitePlace F → ℂ := fun w => horiz ((f₀ • z) w)
  let y : InfinitePlace F → ℝ := fun w => height ((f₀ • z) w)
  have hy : ∀ w, 0 < y w := by
    intro w
    change 0 < height ((f₀ • z) w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos ((f₀ • z) w)
  have hzcoord : f₀ • z = ptX' F x y := by
    funext w
    exact (pt_horiz_height ((f₀ • z) w)).symm
  have hlower : SiegelData.lowerHeight F d i ≤ normHeight F (f₀ • z) := by
    simpa [SiegelData.lowerHeight, i, gI, σi, div_eq_mul_inv,
      _root_.mul_inv_rev, mul_comm] using hheight
  refine ⟨i, γ₀, x, y, ?_, hy, ?_⟩
  · calc
      (d.σ i)⁻¹ • ((γ₀ : SL(2,𝓞 F)) • z) =
          ((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z :=
        r8_mixed_smul_assoc _ _ _
      _ = f₀ • z := by simp [f₀, gI, σi]
      _ = ptX' F x y := hzcoord
  · calc
      SiegelData.lowerHeight F d i ≤ normHeight F (f₀ • z) := hlower
      _ = normHeight F ((d.σ i)⁻¹ • ((γ₀ : SL(2,𝓞 F)) • z)) := by
        rw [r8_mixed_smul_assoc]

theorem r8_siegel_cover_helper (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∀ z : X F, ∃ i : d.ι, ∃ γ : Γ,
      (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z) ∈ SiegelData.setAt F d i := by
  classical
  intro z
  obtain ⟨i, γ₀, x, y, hbase, hy, hlower⟩ := r8_minkowski_reduction Γ d z
  let σ : SL(2,F) := d.σ i
  let t : InfinitePlace F → ℝ := fun w => Real.sqrt (y w)
  have ht : ∀ w, 0 < t w := fun w => Real.sqrt_pos.mpr (hy w)
  obtain ⟨ε, hε, hbalance⟩ := d.balanced i t ht
  have hεset : ε ∈ cuspUnitSet F Γ σ :=
    (r8_cuspUnits_mem_iff_set Γ σ ε).mp hε
  rcases hεset with ⟨μu, γu, hU⟩
  let U : SL(2,F) := cuspUnitMatrix F ε μu
  have hUtri : σ⁻¹ * toSLF F (γu : SL(2,𝓞 F)) * σ ∈ borelSL F := by
    rw [hU]
    change U 1 0 = 0
    simp [U, cuspUnitMatrix, borelSL]
  let zUnit : X F := U • ptX' F x y
  let xUnit : InfinitePlace F → ℂ := fun w => horiz (zUnit w)
  let yUnit : InfinitePlace F → ℝ := fun w => height (zUnit w)
  have hUnitCoord : zUnit = ptX' F xUnit yUnit := by
    funext w
    exact (pt_horiz_height (zUnit w)).symm
  have hUnitHeight (w : InfinitePlace F) :
      yUnit w = unitHeightAction F ε y w := by
    exact r8_cuspUnit_height ε μu x y hy w
  have hUnitBalanced : IsBalancedHeights F (2 * d.B i) yUnit := by
    have hyEq : yUnit = unitHeightAction F ε y := funext hUnitHeight
    rw [hyEq]
    exact r8_balanced_unitAction ε y hy (d.B i) hbalance
  have hG2unit := (G2_x_action (F := F)).2.2.1
      (γu : SL(2,𝓞 F)) σ hUtri
  have hNormUnit : normHeight F zUnit = normHeight F (ptX' F x y) := by
    change normHeight F (cuspUnitMatrix F ε μu • ptX' F x y) = _
    calc
      _ = normHeight F ((σ⁻¹ * toSLF F (γu : SL(2,𝓞 F)) * σ) • ptX' F x y) := by
        rw [hU.symm]
      _ = normHeight F (ptX' F x y) := hG2unit.2 (ptX' F x y)
  have hLowerBase : SiegelData.lowerHeight F d i ≤ normHeight F (ptX' F x y) := by
    simpa [hbase] using hlower
  have hLowerUnit : SiegelData.lowerHeight F d i ≤ normHeight F zUnit := by
    calc
      SiegelData.lowerHeight F d i ≤ normHeight F (ptX' F x y) := hLowerBase
      _ = normHeight F zUnit := hNormUnit.symm
  obtain ⟨τ, hτ, hPτ⟩ := d.P_covers i xUnit
  have hτmap : τ ∈
      (cuspLattice F Γ σ).map (infEmb F).toAddMonoidHom := by exact hτ
  obtain ⟨aT, hTransMember, hEmb⟩ := AddSubgroup.mem_map.mp hτmap
  have hEmb' : (fun w => w.embedding aT) = τ := by
    funext w
    have h := congrFun hEmb w
    change (infEmb F).toAddMonoidHom aT w = τ w at h
    simpa [infEmb] using h
  obtain ⟨γt, hT⟩ := r8_cuspLattice_realize Γ σ aT hTransMember
  let N : SL(2,F) := upperHom F (Multiplicative.ofAdd aT)
  let xFinal : InfinitePlace F → ℂ := fun w => w.embedding aT + xUnit w
  have hPFinal : xFinal ∈ d.P i := by
    change (fun w => w.embedding aT + xUnit w) ∈ d.P i
    have hshift : (fun w => w.embedding aT + xUnit w) = τ + xUnit := by
      funext w
      rw [congrFun hEmb' w]
      rfl
    rw [hshift]
    exact hPτ
  have hTranslationPoint : N • zUnit = ptX' F xFinal yUnit := by
    calc
      N • zUnit = N • ptX' F xUnit yUnit := by rw [hUnitCoord]
      _ = ptX' F xFinal yUnit := r8_translation_pt aT xUnit yUnit hUnitBalanced.1
  have hNtri : N ∈ borelSL F := by
    change (upperHom F (Multiplicative.ofAdd aT)) 1 0 = 0
    rfl
  have hN00 : N 0 0 = 1 := by
    change (upperHom F (Multiplicative.ofAdd aT)) 0 0 = 1
    rfl
  have hG2translation := (G2_x_action (F := F)).2.1 N hNtri zUnit
  have hNtranslation : normHeight F (N • zUnit) = normHeight F zUnit := by
    simpa [hN00, absFieldNorm] using hG2translation
  have hLowerFinal : SiegelData.lowerHeight F d i ≤
      normHeight F (ptX' F xFinal yUnit) := by
    calc
      SiegelData.lowerHeight F d i ≤ normHeight F zUnit := hLowerUnit
      _ = normHeight F (N • zUnit) := hNtranslation.symm
      _ = normHeight F (ptX' F xFinal yUnit) := by rw [hTranslationPoint]
  have hγuConj : toSLF F (γu : SL(2,𝓞 F)) = σ * U * σ⁻¹ := by
    calc
      toSLF F (γu : SL(2,𝓞 F)) =
          σ * (σ⁻¹ * toSLF F (γu : SL(2,𝓞 F)) * σ) * σ⁻¹ := by group
      _ = σ * U * σ⁻¹ := by rw [hU]
  have hgroup : σ⁻¹ * toSLF F (γt : SL(2,𝓞 F)) *
        toSLF F (γu : SL(2,𝓞 F)) * toSLF F (γ₀ : SL(2,𝓞 F)) =
      N * U * ((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) := by
    calc
      _ = σ⁻¹ * (σ * N * σ⁻¹) * (σ * U * σ⁻¹) *
          toSLF F (γ₀ : SL(2,𝓞 F)) := by rw [← hT, hγuConj]
      _ = _ := by
        dsimp [σ]
        group
  have hbaseProd :
      ((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z = ptX' F x y := by
    calc
      _ = (d.σ i)⁻¹ • ((γ₀ : SL(2,𝓞 F)) • z) :=
        (r8_mixed_smul_assoc (d.σ i)⁻¹ (γ₀ : SL(2,𝓞 F)) z).symm
      _ = ptX' F x y := hbase
  let γFinal : Γ := γt * γu * γ₀
  have hFinalAction :
      σ⁻¹ • ((γFinal : SL(2,𝓞 F)) • z) =
        N • (U • (((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z)) := by
    calc
      _ = (σ⁻¹ * toSLF F (γFinal : SL(2,𝓞 F))) • z :=
        r8_mixed_smul_assoc σ⁻¹ (γFinal : SL(2,𝓞 F)) z
      _ = (σ⁻¹ * toSLF F (γt : SL(2,𝓞 F)) *
          toSLF F (γu : SL(2,𝓞 F)) * toSLF F (γ₀ : SL(2,𝓞 F))) • z := by
        simp [γFinal, map_mul, mul_assoc]
      _ = (N * U * ((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F)))) • z := by rw [hgroup]
      _ = N • (U • (((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z)) := by
        calc
          _ = (N * U) • (((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z) :=
            (smul_smul (N * U) _ z).symm
          _ = N • (U • (((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z)) :=
            (smul_smul N U _).symm
  have hFinalPoint :
      σ⁻¹ • ((γFinal : SL(2,𝓞 F)) • z) = ptX' F xFinal yUnit := by
    calc
      _ = N • (U • (((d.σ i)⁻¹ * toSLF F (γ₀ : SL(2,𝓞 F))) • z)) := hFinalAction
      _ = N • (U • ptX' F x y) := by rw [hbaseProd]
      _ = N • zUnit := by rfl
      _ = ptX' F xFinal yUnit := hTranslationPoint
  refine ⟨i, γFinal, ?_⟩
  rw [hFinalPoint]
  change ∃ x' y', ptX' F xFinal yUnit = ptX' F x' y' ∧
    x' ∈ d.P i ∧ IsBalancedHeights F (2 * d.B i) y' ∧
    SiegelData.lowerHeight F d i ≤ normHeight F (ptX' F x' y')
  exact ⟨xFinal, yUnit, rfl, hPFinal, hUnitBalanced, hLowerFinal⟩

end ArtinPrimitiveRoots.A1.Spec
