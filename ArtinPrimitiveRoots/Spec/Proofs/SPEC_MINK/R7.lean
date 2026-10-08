import ArtinPrimitiveRoots.Spec.Geometry
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

set_option autoImplicit false

open Module NumberField NumberField.InfinitePlace MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private abbrev specMinkMixed (F : Type) [Field F] [NumberField F] :=
  NumberField.mixedEmbedding.mixedSpace F

private instance specMinkNoRealPlaces : IsEmpty {w : InfinitePlace F // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

private abbrev specMinkCoordSpace (F : Type) [Field F] [NumberField F] :=
  (Fin 2 ⊕ Fin 2) × InfinitePlace F → ℝ

private def specMinkCoordEquiv :
    (specMinkMixed F × specMinkMixed F) ≃ₗ[ℝ] specMinkCoordSpace F where
  toFun v p :=
    let c : {w : InfinitePlace F // IsComplex w} := ⟨p.2, IsTotallyComplex.isComplex p.2⟩
    match p.1 with
    | Sum.inl i => if i = 0 then (v.1.2 c).re else (v.1.2 c).im
    | Sum.inr i => if i = 0 then (v.2.2 c).re else (v.2.2 c).im
  invFun f :=
    let a : specMinkMixed F :=
      (fun w => isEmptyElim w,
        fun w => ⟨f (Sum.inl 0, w.1), f (Sum.inl 1, w.1)⟩)
    let b : specMinkMixed F :=
      (fun w => isEmptyElim w,
        fun w => ⟨f (Sum.inr 0, w.1), f (Sum.inr 1, w.1)⟩)
    (a, b)
  left_inv v := by
    apply Prod.ext
    · apply Prod.ext
      · funext w
        exact isEmptyElim w
      · funext w
        rfl
    · apply Prod.ext
      · funext w
        exact isEmptyElim w
      · funext w
        rfl
  right_inv f := by
    funext p
    rcases p with ⟨i, w⟩
    rcases i with i | i <;> fin_cases i <;> simp
  map_add' a b := by
    funext p
    rcases p with ⟨i, w⟩
    rcases i with i | i <;> fin_cases i <;> simp [Complex.add_re, Complex.add_im]
  map_smul' r v := by
    funext p
    rcases p with ⟨i, w⟩
    rcases i with i | i <;> fin_cases i <;> simp [Complex.mul_re, Complex.mul_im]

private noncomputable def specMinkRowBasis :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ
      (specMinkMixed F × specMinkMixed F) :=
  (NumberField.mixedEmbedding.latticeBasis F).prod
    (NumberField.mixedEmbedding.latticeBasis F)

private noncomputable def specMinkCoordBasis :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ
      (specMinkCoordSpace F) :=
  (specMinkRowBasis).map (specMinkCoordEquiv (F := F))

private def specMinkRowZLattice : Submodule ℤ (specMinkMixed F × specMinkMixed F) :=
  Submodule.span ℤ (Set.range specMinkRowBasis)

private def specMinkCoordZLattice : Submodule ℤ (specMinkCoordSpace F) :=
  Submodule.span ℤ (Set.range specMinkCoordBasis)

private theorem specMinkCoordZLattice_eq_map :
    specMinkCoordZLattice = Submodule.map
      ((specMinkCoordEquiv (F := F)).toLinearMap.restrictScalars ℤ) specMinkRowZLattice := by
  have hrange : Set.range specMinkCoordBasis =
      (specMinkCoordEquiv (F := F)).toLinearMap '' Set.range specMinkRowBasis := by
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [specMinkCoordZLattice, specMinkRowZLattice, hrange]
  exact (Submodule.map_span
    ((specMinkCoordEquiv (F := F)).toLinearMap.restrictScalars ℤ)
    (Set.range specMinkRowBasis)).symm

private theorem specMinkRowZLattice_mem (a b : 𝓞 F) :
    (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
      NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b)) ∈ specMinkRowZLattice := by
  classical
  let q := NumberField.mixedEmbedding.latticeBasis F
  have hqspan : Submodule.span ℤ (Set.range q) =
      NumberField.mixedEmbedding.integerLattice F :=
    NumberField.mixedEmbedding.span_latticeBasis F
  have ha : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈
      NumberField.mixedEmbedding.integerLattice F := by
    change NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈
      LinearMap.range ((NumberField.mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
    exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  have hb : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) ∈
      NumberField.mixedEmbedding.integerLattice F := by
    change NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) ∈
      LinearMap.range ((NumberField.mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
    exact LinearMap.mem_range.mpr ⟨b, rfl⟩
  have haspan : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈
      Submodule.span ℤ (Set.range q) := by rw [hqspan]; exact ha
  have hbspan : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) ∈
      Submodule.span ℤ (Set.range q) := by rw [hqspan]; exact hb
  change (_, _) ∈ Submodule.span ℤ (Set.range (q.prod q))
  rw [(q.prod q).mem_span_iff_repr_mem ℤ]
  intro i
  cases i with
  | inl i => simpa only [Module.Basis.prod_repr_inl] using
      (q.mem_span_iff_repr_mem ℤ _).mp haspan i
  | inr i => simpa only [Module.Basis.prod_repr_inr] using
      (q.mem_span_iff_repr_mem ℤ _).mp hbspan i

private theorem specMinkRowZLattice_extract {x y : specMinkMixed F}
    (hxy : (x, y) ∈ specMinkRowZLattice) :
    ∃ a b : 𝓞 F,
      x = NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∧
      y = NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) := by
  classical
  let q := NumberField.mixedEmbedding.latticeBasis F
  have hqspan : Submodule.span ℤ (Set.range q) =
      NumberField.mixedEmbedding.integerLattice F :=
    NumberField.mixedEmbedding.span_latticeBasis F
  change (x, y) ∈ Submodule.span ℤ (Set.range (q.prod q)) at hxy
  rw [(q.prod q).mem_span_iff_repr_mem ℤ] at hxy
  have hxspan : x ∈ Submodule.span ℤ (Set.range q) := by
    rw [q.mem_span_iff_repr_mem ℤ]
    intro i
    simpa only [Module.Basis.prod_repr_inl] using hxy (Sum.inl i)
  have hyspan : y ∈ Submodule.span ℤ (Set.range q) := by
    rw [q.mem_span_iff_repr_mem ℤ]
    intro i
    simpa only [Module.Basis.prod_repr_inr] using hxy (Sum.inr i)
  have hxmem : x ∈ NumberField.mixedEmbedding.integerLattice F := by
    rw [← hqspan]
    exact hxspan
  have hymem : y ∈ NumberField.mixedEmbedding.integerLattice F := by
    rw [← hqspan]
    exact hyspan
  change x ∈ LinearMap.range
      ((NumberField.mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap at hxmem
  change y ∈ LinearMap.range
      ((NumberField.mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap at hymem
  rcases LinearMap.mem_range.mp hxmem with ⟨a, ha⟩
  rcases LinearMap.mem_range.mp hymem with ⟨b, hb⟩
  exact ⟨a, b, ha.symm, hb.symm⟩

private theorem specMinkCoordZLattice_mem (a b : 𝓞 F) :
    (specMinkCoordEquiv (F := F))
      (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
        NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b)) ∈ specMinkCoordZLattice := by
  rw [specMinkCoordZLattice_eq_map]
  apply Submodule.mem_map.mpr
  exact ⟨_, specMinkRowZLattice_mem a b, rfl⟩

private def specMinkLocalMatrix (x : ℂ) (y : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks
    !![Real.sqrt y, 0; 0, Real.sqrt y]
    0
    !![x.re / Real.sqrt y, -x.im / Real.sqrt y;
       x.im / Real.sqrt y, x.re / Real.sqrt y]
    !![(Real.sqrt y)⁻¹, 0; 0, (Real.sqrt y)⁻¹]

private theorem specMinkLocalMatrix_det (x : ℂ) {y : ℝ} (hy : 0 < y) :
    (specMinkLocalMatrix x y).det = 1 := by
  have hk : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  rw [specMinkLocalMatrix, Matrix.det_fromBlocks_zero₁₂]
  simp [Matrix.det_fin_two_of]
  field_simp

private def specMinkGlobalMatrix (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) :
    Matrix ((Fin 2 ⊕ Fin 2) × InfinitePlace F)
      ((Fin 2 ⊕ Fin 2) × InfinitePlace F) ℝ :=
  Matrix.blockDiagonal fun w => specMinkLocalMatrix (x w) (y w)

private theorem specMinkGlobalMatrix_det (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : (specMinkGlobalMatrix x y).det = 1 := by
  rw [specMinkGlobalMatrix, Matrix.det_blockDiagonal]
  simp [specMinkLocalMatrix_det, hy]

private noncomputable def specMinkTransform (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    specMinkCoordSpace F ≃ₗ[ℝ] specMinkCoordSpace F :=
  (specMinkGlobalMatrix x y).toLin'.equivOfDetNeZero (by
    rw [LinearMap.det_toLin', specMinkGlobalMatrix_det x y hy]
    norm_num)

private def specMinkRowCoords (a b : ℂ) : (Fin 2 ⊕ Fin 2) → ℝ := fun i =>
  match i with
  | Sum.inl j => if j = 0 then a.re else a.im
  | Sum.inr j => if j = 0 then b.re else b.im

private theorem specMinkCoordEquiv_integral_apply (a b : 𝓞 F) (w : InfinitePlace F)
    (i : Fin 2 ⊕ Fin 2) :
    specMinkCoordEquiv (F := F)
        (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
          NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b)) (i, w) =
      specMinkRowCoords (w.embedding (algebraMap (𝓞 F) F a))
        (w.embedding (algebraMap (𝓞 F) F b)) i := by
  rcases i with i | i <;> fin_cases i <;>
    simp [specMinkCoordEquiv, specMinkRowCoords]

private theorem specMinkLocalMatrix_toLin_apply (x : ℂ) {y : ℝ} (hy : 0 < y)
    (v : (Fin 2 ⊕ Fin 2) → ℝ) :
    (specMinkLocalMatrix x y).toLin' v =
      specMinkRowCoords
        (Real.sqrt y * Complex.mk (v (Sum.inl 0)) (v (Sum.inl 1)))
        ((Complex.mk (v (Sum.inl 0)) (v (Sum.inl 1)) * x +
          Complex.mk (v (Sum.inr 0)) (v (Sum.inr 1))) / Real.sqrt y) := by
  let a : ℂ := Complex.mk (v (Sum.inl 0)) (v (Sum.inl 1))
  let b : ℂ := Complex.mk (v (Sum.inr 0)) (v (Sum.inr 1))
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      specMinkLocalMatrix,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      specMinkRowCoords, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> field_simp <;> ring

private theorem specMinkGlobalMatrix_toLin_apply (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (v : specMinkCoordSpace F)
    (i : Fin 2 ⊕ Fin 2) (w : InfinitePlace F) :
    (specMinkGlobalMatrix x y).toLin' v (i, w) =
      (specMinkLocalMatrix (x w) (y w)).toLin' (fun j => v (j, w)) i := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, specMinkGlobalMatrix,
    Matrix.blockDiagonal_apply]

private def specMinkRowAt (v : specMinkCoordSpace F) (w : InfinitePlace F) : ℂ × ℂ :=
  (Complex.mk (v (Sum.inl 0, w)) (v (Sum.inl 1, w)),
    Complex.mk (v (Sum.inr 0, w)) (v (Sum.inr 1, w)))

private theorem specMinkGlobalMatrix_rowAt (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w)
    (v : specMinkCoordSpace F) (w : InfinitePlace F) :
    specMinkRowAt ((specMinkGlobalMatrix x y).toLin' v) w =
      (Real.sqrt (y w) * (specMinkRowAt v w).1,
        ((specMinkRowAt v w).1 * x w + (specMinkRowAt v w).2) / Real.sqrt (y w)) := by
  have hloc := specMinkLocalMatrix_toLin_apply (x w) (v := fun j => v (j, w)) (hy w)
  have hcoord (i : Fin 2 ⊕ Fin 2) :
      (specMinkGlobalMatrix x y).toLin' v (i, w) =
        (specMinkRowCoords
          (Real.sqrt (y w) * (specMinkRowAt v w).1)
          (((specMinkRowAt v w).1 * x w + (specMinkRowAt v w).2) /
            Real.sqrt (y w))) i := by
    calc
      (specMinkGlobalMatrix x y).toLin' v (i, w) =
          (specMinkLocalMatrix (x w) (y w)).toLin' (fun j => v (j, w)) i :=
        specMinkGlobalMatrix_toLin_apply x y v i w
      _ = specMinkRowCoords
          (Real.sqrt (y w) * (specMinkRowAt v w).1)
          (((specMinkRowAt v w).1 * x w + (specMinkRowAt v w).2) /
            Real.sqrt (y w)) i := congrFun hloc i
  apply Prod.ext
  · apply Complex.ext
    · simpa [specMinkRowAt, specMinkRowCoords] using hcoord (Sum.inl 0)
    · simpa [specMinkRowAt, specMinkRowCoords] using hcoord (Sum.inl 1)
  · apply Complex.ext
    · simpa [specMinkRowAt, specMinkRowCoords] using hcoord (Sum.inr 0)
    · simpa [specMinkRowAt, specMinkRowCoords] using hcoord (Sum.inr 1)

private theorem specMinkRowAt_integral (a b : 𝓞 F) (w : InfinitePlace F) :
    specMinkRowAt
        (specMinkCoordEquiv (F := F)
          (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
            NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b))) w =
      (w.embedding (algebraMap (𝓞 F) F a), w.embedding (algebraMap (𝓞 F) F b)) := by
  apply Prod.ext <;> apply Complex.ext
  · simpa [specMinkRowAt, specMinkRowCoords] using
      specMinkCoordEquiv_integral_apply a b w (Sum.inl 0)
  · simpa [specMinkRowAt, specMinkRowCoords] using
      specMinkCoordEquiv_integral_apply a b w (Sum.inl 1)
  · simpa [specMinkRowAt, specMinkRowCoords] using
      specMinkCoordEquiv_integral_apply a b w (Sum.inr 0)
  · simpa [specMinkRowAt, specMinkRowCoords] using
      specMinkCoordEquiv_integral_apply a b w (Sum.inr 1)

private theorem specMink_rowHeight_norm_identity (a b x : ℂ) {y : ℝ} (hy : 0 < y) :
    (Complex.normSq (a * x + b) + Complex.normSq a * y ^ 2) / y =
      Complex.normSq (Real.sqrt y * a) +
        Complex.normSq ((a * x + b) / Real.sqrt y) := by
  have hk : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hksq : Real.sqrt y * Real.sqrt y = y := by
    nlinarith [Real.sq_sqrt hy.le]
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_div,
    Complex.normSq_ofReal]
  rw [hksq]
  field_simp [hy.ne', hk]
  ring

private def specMinkCube (R : ℝ) : Set (specMinkCoordSpace F) :=
  Set.Icc (fun _ => -R) (fun _ => R)

private theorem specMink_row_product_bound (z : X F) (a b : 𝓞 F) (R : ℝ)
    (hR : 0 ≤ R)
    (hcube : (specMinkGlobalMatrix (fun w => horiz (z w)) (fun w => height (z w))).toLin'
        (specMinkCoordEquiv (F := F)
          (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
            NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b))) ∈ specMinkCube (F := F) R) :
    ∏ w : InfinitePlace F,
      rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w ≤
        (4 * R ^ 2) ^ Fintype.card (InfinitePlace F) := by
  let v := specMinkCoordEquiv (F := F)
    (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
      NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b))
  let tv := (specMinkGlobalMatrix (fun w => horiz (z w))
    (fun w => height (z w))).toLin' v
  have hcoords (i : Fin 2 ⊕ Fin 2) (w : InfinitePlace F) :
      -R ≤ tv (i, w) ∧ tv (i, w) ≤ R := by
    have h := Set.mem_Icc.mp hcube
    exact ⟨h.1 (i, w), h.2 (i, w)⟩
  have hsquare {t : ℝ} (ht : -R ≤ t) (ht' : t ≤ R) : t ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (t - R), sq_nonneg (t + R)]
  have hout (w : InfinitePlace F) :
      specMinkRowAt tv w =
        (Real.sqrt (height (z w)) * w.embedding (algebraMap (𝓞 F) F a),
          (w.embedding (algebraMap (𝓞 F) F a) * horiz (z w) +
            w.embedding (algebraMap (𝓞 F) F b)) / Real.sqrt (height (z w))) := by
    have hy : ∀ w, 0 < height (z w) := by
      intro w
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    calc
      specMinkRowAt tv w = specMinkRowAt
          ((specMinkGlobalMatrix (fun w => horiz (z w))
            (fun w => height (z w))).toLin' v) w := rfl
      _ = (Real.sqrt (height (z w)) * (specMinkRowAt v w).1,
          ((specMinkRowAt v w).1 * horiz (z w) + (specMinkRowAt v w).2) /
            Real.sqrt (height (z w))) :=
        specMinkGlobalMatrix_rowAt _ _ hy v w
      _ = (Real.sqrt (height (z w)) * w.embedding (algebraMap (𝓞 F) F a),
          (w.embedding (algebraMap (𝓞 F) F a) * horiz (z w) +
            w.embedding (algebraMap (𝓞 F) F b)) / Real.sqrt (height (z w))) := by
          rw [specMinkRowAt_integral]
  have hform (w : InfinitePlace F) :
      rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w =
        Complex.normSq (specMinkRowAt tv w).1 + Complex.normSq (specMinkRowAt tv w).2 := by
    have hy : 0 < height (z w) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    calc
      rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w =
          (Complex.normSq (w.embedding (algebraMap (𝓞 F) F a) * horiz (z w) +
            w.embedding (algebraMap (𝓞 F) F b)) +
            Complex.normSq (w.embedding (algebraMap (𝓞 F) F a)) * height (z w) ^ 2) /
              height (z w) := rfl
      _ = Complex.normSq (Real.sqrt (height (z w)) *
            w.embedding (algebraMap (𝓞 F) F a)) +
          Complex.normSq ((w.embedding (algebraMap (𝓞 F) F a) * horiz (z w) +
            w.embedding (algebraMap (𝓞 F) F b)) / Real.sqrt (height (z w))) :=
          specMink_rowHeight_norm_identity
            (w.embedding (algebraMap (𝓞 F) F a))
            (w.embedding (algebraMap (𝓞 F) F b)) (horiz (z w)) hy
      _ = Complex.normSq (specMinkRowAt tv w).1 + Complex.normSq (specMinkRowAt tv w).2 := by
          rw [hout w]
  have hnorm (c : ℂ) (w : InfinitePlace F)
      (h1 : -R ≤ c.re) (h2 : c.re ≤ R) (h3 : -R ≤ c.im) (h4 : c.im ≤ R) :
      Complex.normSq c ≤ 2 * R ^ 2 := by
    have hr := hsquare h1 h2
    have hi := hsquare h3 h4
    rw [Complex.normSq_apply]
    nlinarith
  have hlocal (w : InfinitePlace F) :
      rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w ≤ 4 * R ^ 2 := by
    rw [hform]
    calc
      _ ≤ 2 * R ^ 2 + 2 * R ^ 2 := add_le_add
        (hnorm (specMinkRowAt tv w).1 w
        (hcoords (Sum.inl 0) w).1 (hcoords (Sum.inl 0) w).2
        (hcoords (Sum.inl 1) w).1 (hcoords (Sum.inl 1) w).2)
        (hnorm (specMinkRowAt tv w).2 w
        (hcoords (Sum.inr 0) w).1 (hcoords (Sum.inr 0) w).2
        (hcoords (Sum.inr 1) w).1 (hcoords (Sum.inr 1) w).2)
      _ = 4 * R ^ 2 := by ring
  have hnonneg (w : InfinitePlace F) :
      0 ≤ rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w := by
    rw [hform]
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  calc
    ∏ w : InfinitePlace F,
        rowHeightForm F (algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b) z w ≤
        ∏ _ : InfinitePlace F, 4 * R ^ 2 :=
      Finset.prod_le_prod₀ (fun w hw => hnonneg w) (fun w hw => hlocal w)
    _ = (4 * R ^ 2) ^ Fintype.card (InfinitePlace F) := by simp

private theorem specMinkCube_convex (R : ℝ) : Convex ℝ (specMinkCube (F := F) R) := by
  intro u hu v hv a b ha hb hab
  apply Set.mem_Icc.mpr
  constructor
  · intro i
    have hu' := (Set.mem_Icc.mp hu).1 i
    have hv' := (Set.mem_Icc.mp hv).1 i
    have huR : 0 ≤ u i + R := by linarith
    have hvR : 0 ≤ v i + R := by linarith
    change -R ≤ a * u i + b * v i
    have hcomb : 0 ≤ a * (u i + R) + b * (v i + R) :=
      add_nonneg (mul_nonneg ha huR) (mul_nonneg hb hvR)
    have hsum : a * u i + b * v i + R = a * (u i + R) + b * (v i + R) := by
      calc
        a * u i + b * v i + R = a * u i + b * v i + (a + b) * R := by rw [hab]; ring
        _ = a * (u i + R) + b * (v i + R) := by ring
    rw [← hsum] at hcomb
    linarith
  · intro i
    have hu' := (Set.mem_Icc.mp hu).2 i
    have hv' := (Set.mem_Icc.mp hv).2 i
    have hRu : 0 ≤ R - u i := by linarith
    have hRv : 0 ≤ R - v i := by linarith
    change a * u i + b * v i ≤ R
    have hcomb : 0 ≤ a * (R - u i) + b * (R - v i) :=
      add_nonneg (mul_nonneg ha hRu) (mul_nonneg hb hRv)
    have hsum : R - (a * u i + b * v i) = a * (R - u i) + b * (R - v i) := by
      calc
        R - (a * u i + b * v i) = (a + b) * R - a * u i - b * v i := by rw [hab]; ring
        _ = a * (R - u i) + b * (R - v i) := by ring
    rw [← hsum] at hcomb
    linarith

private theorem specMinkCube_symmetric (R : ℝ) :
    ∀ u ∈ specMinkCube (F := F) R, -u ∈ specMinkCube (F := F) R := by
  intro u hu
  apply Set.mem_Icc.mpr
  constructor <;> intro i
  · have h := (Set.mem_Icc.mp hu).2 i
    simpa using neg_le_neg h
  · have h := (Set.mem_Icc.mp hu).1 i
    simpa using neg_le_neg h

private theorem specMinkCube_volume (R : ℝ) :
    volume (specMinkCube (F := F) R) =
      ENNReal.ofReal (2 * R) ^ Fintype.card ((Fin 2 ⊕ Fin 2) × InfinitePlace F) := by
  simp [specMinkCube, Real.volume_Icc_pi, sub_neg_eq_add, two_mul, Finset.prod_const]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem specMink_R7_minkowski :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ z : X F, ∃ v : 𝓞 F × 𝓞 F,
      v ≠ (0, 0) ∧
        ∏ w : InfinitePlace F,
          rowHeightForm F
            (algebraMap (𝓞 F) F v.1, algebraMap (𝓞 F) F v.2) z w ≤ C_M := by
  classical
  let d : ℕ := Fintype.card ((Fin 2 ⊕ Fin 2) × InfinitePlace F)
  have hW : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  have hd : 0 < d := by
    dsimp [d]
    have hs : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
    rw [Fintype.card_prod, hs]
    exact Nat.mul_pos (by omega) hW
  have hdim : Module.finrank ℝ (specMinkCoordSpace F) = d := by
    simp [d, specMinkCoordSpace, Module.finrank_fintype_fun_eq_card]
  letI : Finite (Free.ChooseBasisIndex ℤ (𝓞 F)) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis ℤ (𝓞 F))
  letI : Finite (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) := inferInstance
  let L : Submodule ℤ (specMinkCoordSpace F) := specMinkCoordZLattice (F := F)
  letI : DiscreteTopology L := by
    change DiscreteTopology
      (Submodule.span ℤ (Set.range (specMinkCoordBasis (F := F))))
    infer_instance
  letI : IsZLattice ℝ L := ⟨by
    change Submodule.span ℝ
      (Submodule.span ℤ (Set.range (specMinkCoordBasis (F := F))) :
        Set (specMinkCoordSpace F)) = ⊤
    exact ZSpan.span_top (specMinkCoordBasis (F := F))⟩
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  letI : Finite (Free.ChooseBasisIndex ℤ L) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis ℤ L)
  let bL : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  letI : Countable L.toAddSubgroup := by
    change Countable L
    infer_instance
  let fd : Set (specMinkCoordSpace F) := ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)
  have hfd : IsAddFundamentalDomain L.toAddSubgroup fd
      (volume : Measure (specMinkCoordSpace F)) := by
    exact ZLattice.isAddFundamentalDomain bL (volume : Measure (specMinkCoordSpace F))
  have hfdBound : Bornology.IsBounded fd := by
    dsimp [fd]
    exact ZSpan.fundamentalDomain_isBounded _
  have hVne : volume fd ≠ 0 :=
    hfd.measure_ne_zero (NeZero.ne (volume : Measure (specMinkCoordSpace F)))
  have hVtop : volume fd ≠ ⊤ :=
    ne_of_lt (Bornology.IsBounded.measure_lt_top
      (μ := (volume : Measure (specMinkCoordSpace F))) hfdBound)
  have hVreal : 0 < (volume fd).toReal := ENNReal.toReal_pos hVne hVtop
  let R : ℝ := (2 : ℝ) ^ d * (volume fd).toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hside : 1 ≤ 2 * R := by
    dsimp [R]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) d,
      (ENNReal.toReal_nonneg : 0 ≤ (volume fd).toReal)]
  have hbaseLt : (2 : ℝ) ^ d * (volume fd).toReal < 2 * R := by
    dsimp [R]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) d,
      (ENNReal.toReal_nonneg : 0 ≤ (volume fd).toReal)]
  have hd1 : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hde : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hsidePow : 2 * R ≤ (2 * R) ^ d := by
    exact le_self_pow₀ hside (Nat.ne_of_gt hd)
  have hvolReal : (2 : ℝ) ^ d * (volume fd).toReal < (2 * R) ^ d :=
    hbaseLt.trans_le hsidePow
  have hleft : volume fd * (2 : ENNReal) ^ d =
      ENNReal.ofReal ((volume fd).toReal * (2 : ℝ) ^ d) := by
    calc
      volume fd * (2 : ENNReal) ^ d =
          ENNReal.ofReal ((volume fd).toReal) * (2 : ENNReal) ^ d := by
        rw [ENNReal.ofReal_toReal hVtop]
      _ = ENNReal.ofReal ((volume fd).toReal) * ENNReal.ofReal (2 : ℝ) ^ d := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
      _ = ENNReal.ofReal ((volume fd).toReal * (2 : ℝ) ^ d) := by
        rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num) d]
        rw [← ENNReal.ofReal_mul
          (ENNReal.toReal_nonneg : 0 ≤ (volume fd).toReal)]
  have hcubeVol : volume (specMinkCube (F := F) R) = ENNReal.ofReal ((2 * R) ^ d) := by
    rw [specMinkCube_volume]
    simpa [d] using
      (ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 * R by positivity) d).symm
  have hvol : volume fd * (2 : ENNReal) ^ Module.finrank ℝ (specMinkCoordSpace F) <
      volume (specMinkCube (F := F) R) := by
    rw [hdim, hcubeVol, hleft]
    apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos (mul_pos (by norm_num) hR) d)).2
    nlinarith [hvolReal]
  refine ⟨(4 * R ^ 2) ^ Fintype.card (InfinitePlace F), by positivity, ?_⟩
  intro z
  let x : InfinitePlace F → ℂ := fun w => horiz (z w)
  let y : InfinitePlace F → ℝ := fun w => height (z w)
  have hy : ∀ w, 0 < y w := by
    intro w
    dsimp [y]
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  let T : specMinkCoordSpace F ≃ₗ[ℝ] specMinkCoordSpace F := specMinkTransform x y hy
  have hTco : (T : specMinkCoordSpace F →ₗ[ℝ] specMinkCoordSpace F) =
      (specMinkGlobalMatrix x y).toLin' := by
    ext u
    simp [T, specMinkTransform]
  have hTapp (u : specMinkCoordSpace F) :
      T u = (specMinkGlobalMatrix x y).toLin' u := by
    simpa only [LinearEquiv.coe_coe] using
      congrArg (fun f : specMinkCoordSpace F →ₗ[ℝ] specMinkCoordSpace F => f u) hTco
  have hdetT : LinearMap.det (T : specMinkCoordSpace F →ₗ[ℝ] specMinkCoordSpace F) = 1 := by
    rw [hTco, LinearMap.det_toLin', specMinkGlobalMatrix_det x y hy]
  have hdetTinv :
      LinearMap.det (T.symm : specMinkCoordSpace F →ₗ[ℝ] specMinkCoordSpace F) = 1 := by
    rw [LinearEquiv.det_coe_symm, hdetT]
    norm_num
  have hbodyVol : volume (T ⁻¹' specMinkCube (F := F) R) =
      volume (specMinkCube (F := F) R) := by
    rw [Measure.addHaar_preimage_linearEquiv]
    simp [hdetTinv]
  have hbodySymm : ∀ u ∈ T ⁻¹' specMinkCube (F := F) R,
      -u ∈ T ⁻¹' specMinkCube (F := F) R := by
    intro u hu
    have hu' : T u ∈ specMinkCube (F := F) R := hu
    change T (-u) ∈ specMinkCube (F := F) R
    rw [map_neg]
    exact specMinkCube_symmetric R (T u) hu'
  have hbodyConvex : Convex ℝ (T ⁻¹' specMinkCube (F := F) R) := by
    intro u hu v hv a b ha hb hab
    have hu' : T u ∈ specMinkCube (F := F) R := hu
    have hv' : T v ∈ specMinkCube (F := F) R := hv
    have h := (specMinkCube_convex R) hu' hv' (a := a) (b := b) ha hb hab
    change T (a • u + b • v) ∈ specMinkCube (F := F) R
    simpa only [map_add, map_smul] using h
  have hstrict : volume fd * (2 : ENNReal) ^ Module.finrank ℝ (specMinkCoordSpace F) <
      volume (T ⁻¹' specMinkCube (F := F) R) := by
    rw [hbodyVol]
    exact hvol
  obtain ⟨p, hp0, hpBody⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      hfd hbodySymm hbodyConvex hstrict
  have hpCube : T (p : specMinkCoordSpace F) ∈ specMinkCube (F := F) R := by
    change T (p : specMinkCoordSpace F) ∈ specMinkCube (F := F) R at hpBody
    exact hpBody
  have hpMatrix : (specMinkGlobalMatrix x y).toLin' (p : specMinkCoordSpace F) ∈
      specMinkCube (F := F) R := by
    rw [← hTapp (p : specMinkCoordSpace F)]
    exact hpCube
  have hpCoord : (p : specMinkCoordSpace F) ∈ specMinkCoordZLattice := by
    change (p : specMinkCoordSpace F) ∈ L
    exact p.property
  rw [specMinkCoordZLattice_eq_map] at hpCoord
  rcases Submodule.mem_map.mp hpCoord with ⟨u, hu, hφu⟩
  obtain ⟨a, b, hua, hub⟩ := specMinkRowZLattice_extract hu
  have hu0 : (a, b) ≠ (0, 0) := by
    intro hab
    have ha0 : a = 0 := congrArg Prod.fst hab
    have hb0 : b = 0 := congrArg Prod.snd hab
    have huEq : u = (0, 0) := by
      apply Prod.ext
      · rw [hua, ha0]
        simp
      · rw [hub, hb0]
        simp
    have hpVec : (p : specMinkCoordSpace F) = 0 := by
      rw [← hφu, huEq]
      simp
    apply hp0
    exact Subtype.ext hpVec
  have hrowCoord :
      (specMinkCoordEquiv (F := F)
        (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
          NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b))) =
        (p : specMinkCoordSpace F) := by
    calc
      _ = (specMinkCoordEquiv (F := F) u) := by rw [← hua, ← hub]
      _ = (p : specMinkCoordSpace F) := hφu
  have hrowCube :
      (specMinkGlobalMatrix x y).toLin'
        (specMinkCoordEquiv (F := F)
          (NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a),
            NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b))) ∈
          specMinkCube (F := F) R := by
    simpa only [hrowCoord] using hpMatrix
  have hbound := specMink_row_product_bound z a b R (le_of_lt hR) hrowCube
  exact ⟨(a, b), hu0, hbound⟩

end ArtinPrimitiveRoots.A1.Spec
