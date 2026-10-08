import ArtinPrimitiveRoots.Spec.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.OpenPos
import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
import OAI.NumberTheory.DirichletL.Eisenstein.VariationalLaplacian
import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents

attribute [-instance] OAI.CubicEisenstein.complexSLTopology

/-! Geometry nodes G1--G6. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

theorem H3_eq_OAI : H3 = OAI.CubicEisenstein.HyperbolicSpace := by
  rfl

theorem height_eq_hyperbolicHeight : height = OAI.CubicEisenstein.hyperbolicHeight := by
  funext z
  induction z using Quotient.inductionOn with
  | _ g =>
      change ((((g : Matrix (Fin 2) (Fin 2) ℂ) *
        star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1).re)⁻¹ =
        OAI.CubicEisenstein.hyperbolicHeight
          (g : OAI.CubicEisenstein.HyperbolicSpace)
      rw [OAI.CubicEisenstein.hyperbolicHeight_mk]
      simp [OAI.CubicEisenstein.liftedHeight, OAI.CubicEisenstein.complexBottomRow,
        OAI.CubicEisenstein.rowEnergy, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_apply]
      rw [← Complex.normSq_eq_norm_sq (g 1 0),
        ← Complex.normSq_eq_norm_sq (g 1 1), Complex.normSq_apply, Complex.normSq_apply]

theorem pt_eq_upperPoint (x : ℂ) (y : ℝ) (hy : 0 < y) :
    pt x y = OAI.CubicEisenstein.upperPoint x y hy := by
  simp only [pt, dif_pos hy, OAI.CubicEisenstein.upperPoint]
  apply congrArg (fun a : SL(2,ℂ) => (a : H3))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptMat, OAI.CubicEisenstein.upperSection]

theorem herm_eq_hyperbolicGram : herm = OAI.CubicEisenstein.hyperbolicGram := by
  rfl

theorem herm_diag_im_zero (z : H3) : (herm z 1 1).im = 0 := by
  induction z using Quotient.inductionOn with
  | _ g =>
      simp [herm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Complex.mul_conj]

theorem horiz_eq_hyperbolicHorizontal : horiz = OAI.CubicEisenstein.hyperbolicHorizontal := by
  funext z
  have hreal : herm z 1 1 = (herm z 1 1).re := by
    apply Complex.ext <;> simp [herm_diag_im_zero]
  have hherm := congrFun herm_eq_hyperbolicGram z
  have hheight := congrFun height_eq_hyperbolicHeight z
  have hrealgram : OAI.CubicEisenstein.hyperbolicGram z 1 1 =
      (OAI.CubicEisenstein.hyperbolicGram z 1 1).re := by
    rw [← hherm]
    exact hreal
  have hheightpos : 0 < height z := by
    rw [hheight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  have hB : (OAI.CubicEisenstein.hyperbolicGram z 1 1).re ≠ 0 := by
    rw [← hherm]
    exact (inv_pos.mp (by simpa only [height] using hheightpos)).ne'
  have hh : OAI.CubicEisenstein.hyperbolicHorizontal z =
      OAI.CubicEisenstein.hyperbolicGram z 0 1 *
        (OAI.CubicEisenstein.hyperbolicHeight z : ℂ) := rfl
  rw [horiz, hh]
  rw [hherm, ← hheight, hrealgram, height, hherm, hrealgram, Complex.ofReal_inv]
  field_simp [hB]

theorem height_smul_ptX'_at (g : SL(2,F)) (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) (w : InfinitePlace F) :
    height ((g • ptX' F x y) w) = y w /
      (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
        Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
  change height ((Matrix.SpecialLinearGroup.map w.embedding g) • pt (x w) (y w)) = _
  rw [height_eq_hyperbolicHeight, pt_eq_upperPoint (x w) (y w) (hy w)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact OAI.CubicEisenstein.hyperbolicHeight_action_upperPoint
    (Matrix.SpecialLinearGroup.map w.embedding g) (x w) (y w) (hy w)

theorem pt_horiz_height (z : H3) : pt (horiz z) (height z) = z := by
  have hp : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  rw [pt_eq_upperPoint (horiz z) (height z) hp]
  have hpoint := OAI.CubicEisenstein.upperPoint_congr hp
    (OAI.CubicEisenstein.hyperbolicHeight_pos z)
    (congrFun horiz_eq_hyperbolicHorizontal z)
    (congrFun height_eq_hyperbolicHeight z)
  rw [hpoint]
  exact OAI.CubicEisenstein.upperCoordinates_right_inverse z

/-- G1 `spec:h3-basics` — P-SPEC.md:208, 258–260. Coordinate formulas, the action on height,
recovery of a point from its Hermitian matrix, and the positive-coordinate chart. -/
theorem G1_h3_basics :
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y, height (pt x y) = y) ∧
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y, horiz (pt x y) = x) ∧
    (∀ g : SL(2,ℂ), ∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y,
      height (g • pt x y) = y /
        (Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2)) ∧
    (∀ g : SL(2,ℂ), ∀ z : H3,
      herm (g • z) = (g : Matrix (Fin 2) (Fin 2) ℂ) * herm z *
        star (g : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    Function.Injective herm ∧
    (∀ z : H3, pt (horiz z) (height z) = z) ∧
    (∀ p : Coord F, p ∈ posSet F → coordsX F (ptX F p) = p) ∧
    (∀ z : X F, ptX F (coordsX F z) = z) ∧
    H3 = OAI.CubicEisenstein.HyperbolicSpace ∧
    height = OAI.CubicEisenstein.hyperbolicHeight ∧
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y,
      pt x y = OAI.CubicEisenstein.upperPoint x y hy) ∧
    ∃ e : {p : Coord F // p ∈ posSet F} ≃ₜ X F,
      (∀ p, e p = ptX F p.1) ∧ (∀ z, (e.symm z).1 = coordsX F z) := by
  constructor
  · exact height_pt
  constructor
  · exact horiz_pt
  constructor
  · intro g x y hy
    rw [height_eq_hyperbolicHeight, pt_eq_upperPoint x y hy]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact OAI.CubicEisenstein.hyperbolicHeight_action_upperPoint g x y hy
  constructor
  · intro g z
    induction z using Quotient.inductionOn with
    | _ h =>
        change (((g * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
            star ((g * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) =
          (g : Matrix (Fin 2) (Fin 2) ℂ) *
            ((h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ)) *
              star (g : Matrix (Fin 2) (Fin 2) ℂ)
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.star_mul]
        noncomm_ring
  constructor
  · intro z z' hz
    apply OAI.CubicEisenstein.hyperbolicGram_injective
    simpa only [← herm_eq_hyperbolicGram] using hz
  constructor
  · exact pt_horiz_height
  constructor
  · intro p hp
    have hp' : ∀ w, 0 < (p w).2 := by simpa [posSet] using hp
    funext w
    simp [coordsX, ptX, horiz_pt, height_pt, hp' w]
  constructor
  · intro z
    funext w
    exact pt_horiz_height (z w)
  constructor
  · exact H3_eq_OAI
  constructor
  · exact height_eq_hyperbolicHeight
  constructor
  · exact pt_eq_upperPoint
  · let c : {p : Coord F // p ∈ posSet F} ≃ₜ
        (InfinitePlace F → OAI.CubicEisenstein.UpperCoordinates) :=
      { toFun := fun p w => ⟨p.1 w, p.2 w⟩
        invFun := fun q => ⟨fun w => q w, fun w => (q w).2⟩
        left_inv := by
          intro p
          apply Subtype.ext
          funext w
          rfl
        right_inv := by
          intro q
          funext w
          apply Subtype.ext
          rfl
        continuous_toFun := by
          apply continuous_pi
          intro w
          apply Continuous.subtype_mk
          exact (continuous_apply w).comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          apply continuous_pi
          intro w
          exact continuous_subtype_val.comp (continuous_apply w) }
    let d : (InfinitePlace F → OAI.CubicEisenstein.UpperCoordinates) ≃ₜ X F :=
      { toFun := fun q w => OAI.CubicEisenstein.upperCoordinatesHomeomorph (q w)
        invFun := fun z w => OAI.CubicEisenstein.upperCoordinatesHomeomorph.symm (z w)
        left_inv := by
          intro q
          funext w
          exact OAI.CubicEisenstein.upperCoordinatesHomeomorph.left_inv (q w)
        right_inv := by
          intro z
          funext w
          exact OAI.CubicEisenstein.upperCoordinatesHomeomorph.right_inv (z w)
        continuous_toFun := by
          apply continuous_pi
          intro w
          exact OAI.CubicEisenstein.upperCoordinatesHomeomorph.continuous_toFun.comp
            (continuous_apply w)
        continuous_invFun := by
          apply continuous_pi
          intro w
          exact OAI.CubicEisenstein.upperCoordinatesHomeomorph.continuous_invFun.comp
            (continuous_apply w) }
    refine ⟨c.trans d, ?_, ?_⟩
    · intro p
      funext w
      change OAI.CubicEisenstein.upperPoint (p.1 w).1 (p.1 w).2 _ =
        pt (p.1 w).1 (p.1 w).2
      exact (pt_eq_upperPoint (p.1 w).1 (p.1 w).2 (p.2 w)).symm
    · intro z
      funext w
      change (OAI.CubicEisenstein.hyperbolicCoordinates (z w)).1 =
        (coordsX F z) w
      dsimp [OAI.CubicEisenstein.hyperbolicCoordinates, coordsX]
      exact Prod.ext (congrFun horiz_eq_hyperbolicHorizontal (z w)).symm
        (congrFun height_eq_hyperbolicHeight (z w)).symm

theorem absFieldNorm_eq_abs_norm (a : F) :
    absFieldNorm F a = |Algebra.norm ℚ a| := by
  unfold absFieldNorm
  rw [← InfinitePlace.prod_eq_abs_norm (K := F) a]
  apply Finset.prod_congr rfl
  intro w hw
  rw [IsTotallyComplex.mult_eq, ← InfinitePlace.norm_embedding_eq]

open Polynomial in
theorem conjugate_borel_diagonal_is_unit (γ : SL(2,𝓞 F)) (σ : SL(2,F))
    (htri : σ⁻¹ * toSLF F γ * σ ∈ borelSL F) :
    ∃ ε : (𝓞 F)ˣ,
      algebraMap (𝓞 F) F (ε : 𝓞 F) = (σ⁻¹ * toSLF F γ * σ) 0 0 ∧
        absUnitNorm F ε = 1 := by
  classical
  let τ : 𝓞 F := γ 0 0 + γ 1 1
  let a : F := (σ⁻¹ * toSLF F γ * σ) 0 0
  let d : F := (σ⁻¹ * toSLF F γ * σ) 1 1
  let b : SL(2,F) := σ⁻¹ * toSLF F γ * σ
  have hb10 : b 1 0 = 0 := by
    change σ⁻¹ * toSLF F γ * σ ∈ borelSL F at htri
    change b 1 0 = 0
    simpa [borelSL, b] using htri
  have hdet : a * d = 1 := by
    have h := b.property
    rw [Matrix.det_fin_two, hb10] at h
    simpa [a, d, b] using h
  have htraceA : Matrix.trace (toSLF F γ : Matrix (Fin 2) (Fin 2) F) =
      algebraMap (𝓞 F) F τ := by
    simp [τ, toSLF, Matrix.trace, Fin.sum_univ_two]
  have htraceB : Matrix.trace (b : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (toSLF F γ : Matrix (Fin 2) (Fin 2) F) := by
    have hσ : ((σ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) *
        (((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)) = 1 :=
      congrArg (fun g : SL(2,F) => (g : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel σ)
    change Matrix.trace
        (((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) *
          (toSLF F γ : Matrix (Fin 2) (Fin 2) F) *
          (σ : Matrix (Fin 2) (Fin 2) F)) = _
    rw [Matrix.trace_mul_comm]
    calc
      Matrix.trace ((σ : Matrix (Fin 2) (Fin 2) F) *
          (((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) *
            (toSLF F γ : Matrix (Fin 2) (Fin 2) F))) =
          Matrix.trace (((σ : Matrix (Fin 2) (Fin 2) F) *
            ((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)) *
              (toSLF F γ : Matrix (Fin 2) (Fin 2) F)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (toSLF F γ : Matrix (Fin 2) (Fin 2) F) := by rw [hσ]; simp
  have htrace : algebraMap (𝓞 F) F τ = a + d := by
    calc
      algebraMap (𝓞 F) F τ = Matrix.trace (toSLF F γ : Matrix (Fin 2) (Fin 2) F) :=
        htraceA.symm
      _ = Matrix.trace (b : Matrix (Fin 2) (Fin 2) F) := htraceB.symm
      _ = a + d := by simp [Matrix.trace, Fin.sum_univ_two, a, d, b, hb10]
  have ha_root : a ^ 2 - algebraMap (𝓞 F) F τ * a + 1 = 0 := by
    rw [htrace]
    calc
      a ^ 2 - (a + d) * a + 1 = 1 - a * d := by ring
      _ = 0 := by rw [hdet]; ring
  have hd_root : d ^ 2 - algebraMap (𝓞 F) F τ * d + 1 = 0 := by
    rw [htrace]
    calc
      d ^ 2 - (a + d) * d + 1 = 1 - a * d := by ring
      _ = 0 := by rw [hdet]; ring
  let q : Polynomial (𝓞 F) :=
    Polynomial.X ^ 2 +
      (-(Polynomial.C τ * Polynomial.X) + Polynomial.C 1)
  have hqdeg : Polynomial.degree
      (-(Polynomial.C τ * Polynomial.X) + Polynomial.C 1 : Polynomial (𝓞 F)) <
        (2 : WithBot ℕ) := by
    have hle : Polynomial.degree
        (-(Polynomial.C τ * Polynomial.X) + Polynomial.C 1 : Polynomial (𝓞 F)) ≤ 1 := by
      calc
        _ ≤ max (Polynomial.degree (-(Polynomial.C τ * Polynomial.X)))
            (Polynomial.degree (Polynomial.C 1)) := Polynomial.degree_add_le _ _
        _ ≤ 1 := by
          apply max_le
          · rw [Polynomial.degree_neg]
            calc
              Polynomial.degree (Polynomial.C τ * Polynomial.X) ≤
                  Polynomial.degree (Polynomial.C τ) + Polynomial.degree Polynomial.X :=
                Polynomial.degree_mul_le _ _
              _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le (by simp)
              _ = 1 := by simp
          · simp
    exact lt_of_le_of_lt hle (by norm_num)
  have hqmonic : q.Monic := by
    dsimp [q]
    exact Polynomial.monic_X_pow_add hqdeg
  have ha_integral_O : IsIntegral (𝓞 F) a := by
    refine ⟨q, hqmonic, ?_⟩
    have hroot' : a ^ 2 + (-(algebraMap (𝓞 F) F τ * a) + 1) = 0 := by
      calc
        a ^ 2 + (-(algebraMap (𝓞 F) F τ * a) + 1) =
            a ^ 2 - algebraMap (𝓞 F) F τ * a + 1 := by ring
        _ = 0 := ha_root
    simpa [q, Polynomial.aeval_def, map_add, map_neg] using hroot'
  have hd_integral_O : IsIntegral (𝓞 F) d := by
    refine ⟨q, hqmonic, ?_⟩
    have hroot' : d ^ 2 + (-(algebraMap (𝓞 F) F τ * d) + 1) = 0 := by
      calc
        d ^ 2 + (-(algebraMap (𝓞 F) F τ * d) + 1) =
            d ^ 2 - algebraMap (𝓞 F) F τ * d + 1 := by ring
        _ = 0 := hd_root
    simpa [q, Polynomial.aeval_def, map_add, map_neg] using hroot'
  have ha_integral_Z : IsIntegral ℤ a :=
    isIntegral_trans (R := ℤ) (A := 𝓞 F) a ha_integral_O
  have hd_integral_Z : IsIntegral ℤ d :=
    isIntegral_trans (R := ℤ) (A := 𝓞 F) d hd_integral_O
  obtain ⟨aO, haO⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).mp ha_integral_Z
  obtain ⟨dO, hdO⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).mp hd_integral_Z
  have hmul : aO * dO = 1 := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 F) F aO * algebraMap (𝓞 F) F dO = 1
    rw [haO, hdO, hdet]
  have hmul' : dO * aO = 1 := by simpa [mul_comm] using hmul
  let ε : (𝓞 F)ˣ := ⟨aO, dO, hmul, hmul'⟩
  have hε : algebraMap (𝓞 F) F (ε : 𝓞 F) = a := haO
  have hnorm : absUnitNorm F ε = 1 := by
    simpa [absUnitNorm, absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  exact ⟨ε, hε, hnorm⟩

/-- G2 `spec:x-action` — P-SPEC.md:209, 271–275. Product height formula, triangular norm
scaling, unit diagonal norm preservation, and continuity of the product action. -/
theorem G2_x_action :
    (∀ g : SL(2,F), ∀ x : InfinitePlace F → ℂ, ∀ y : InfinitePlace F → ℝ,
      (∀ w, 0 < y w) →
      normHeight F (g • ptX' F x y) =
        ∏ w, y w / (Complex.normSq (w.embedding (g 1 0) * x w +
          w.embedding (g 1 1)) + Complex.normSq (w.embedding (g 1 0)) * y w ^ 2)) ∧
    (∀ b : SL(2,F), b ∈ borelSL F → ∀ z : X F,
      normHeight F (b • z) = absFieldNorm F (b 0 0) * normHeight F z) ∧
    (∀ γ : SL(2,𝓞 F), ∀ σ : SL(2,F),
      σ⁻¹ * toSLF F γ * σ ∈ borelSL F →
      (∃ ε : (𝓞 F)ˣ,
        algebraMap (𝓞 F) F (ε : 𝓞 F) = (σ⁻¹ * toSLF F γ * σ) 0 0 ∧
        absUnitNorm F ε = 1) ∧
      ∀ z : X F, normHeight F ((σ⁻¹ * toSLF F γ * σ) • z) = normHeight F z) ∧
    (∀ g : InfinitePlace F → SL(2,ℂ),
      ∃ e : X F ≃ₜ X F,
        (∀ z, e z = actAtPlaces F g z) ∧
        (∀ z, e.symm z = actAtPlaces F (fun w => (g w)⁻¹) z)) ∧
      ∀ z : X F, Continuous (fun h : InfinitePlace F → SL(2,ℂ) => actAtPlaces F h z) := by
  have hFormula : ∀ (g : SL(2,F)) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (∀ w, 0 < y w) →
      normHeight F (g • ptX' F x y) =
        ∏ w, y w / (Complex.normSq (w.embedding (g 1 0) * x w +
          w.embedding (g 1 1)) + Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
    intro g x y hy
    change (∏ w, height ((g • ptX' F x y) w)) = _
    apply Finset.prod_congr rfl
    intro w hw
    exact height_smul_ptX'_at g x y hy w
  have hRecovery (z : X F) :
      z = ptX' F (fun w => horiz (z w)) (fun w => height (z w)) := by
    funext w
    exact (pt_horiz_height (z w)).symm
  have hBorel : ∀ (b : SL(2,F)), b ∈ borelSL F → ∀ z : X F,
      normHeight F (b • z) = absFieldNorm F (b 0 0) * normHeight F z := by
    intro b hb z
    have hb10 : b 1 0 = 0 := by
      change b 1 0 = 0 at hb
      exact hb
    have hdet : b 0 0 * b 1 1 = 1 := by
      have h := b.property
      rw [Matrix.det_fin_two] at h
      rw [hb10] at h
      simpa using h
    have hb00 : b 0 0 ≠ 0 := by
      intro hzero
      simp [hzero] at hdet
    have hb11 : b 1 1 = (b 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    have hpos : ∀ w, 0 < height (z w) := by
      intro w
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    calc
      normHeight F (b • z) = normHeight F
          (b • ptX' F (fun w => horiz (z w)) (fun w => height (z w))) := by
        exact congrArg (fun q : X F => normHeight F (b • q)) (hRecovery z)
      _ = ∏ w, height (z w) /
          (Complex.normSq (w.embedding (b 1 0) * horiz (z w) +
            w.embedding (b 1 1)) + Complex.normSq (w.embedding (b 1 0)) *
              height (z w) ^ 2) := hFormula b _ _ hpos
      _ = absFieldNorm F (b 0 0) * normHeight F z := by
        have hlocal (w : InfinitePlace F) :
            height (z w) /
              (Complex.normSq (w.embedding (b 1 0) * horiz (z w) +
                w.embedding (b 1 1)) + Complex.normSq (w.embedding (b 1 0)) *
                  height (z w) ^ 2) =
              Complex.normSq (w.embedding (b 0 0)) * height (z w) := by
          have h10w : w.embedding (b 1 0) = 0 := by rw [hb10]; simp
          have h11w : w.embedding (b 1 1) = (w.embedding (b 0 0))⁻¹ := by
            rw [hb11, map_inv₀]
          rw [h10w, h11w]
          simp only [zero_mul, zero_add, Complex.normSq_zero, mul_zero, add_zero]
          rw [Complex.normSq_inv]
          simp [div_eq_mul_inv]
          ring
        have hprod :
            (∏ w, height (z w) /
              (Complex.normSq (w.embedding (b 1 0) * horiz (z w) +
                w.embedding (b 1 1)) + Complex.normSq (w.embedding (b 1 0)) *
                  height (z w) ^ 2)) =
            ∏ w, Complex.normSq (w.embedding (b 0 0)) * height (z w) := by
          apply Finset.prod_congr rfl
          intro w hw
          exact hlocal w
        rw [hprod, Finset.prod_mul_distrib]
        unfold absFieldNorm normHeight
        simp_rw [Complex.normSq_eq_norm_sq]
  refine ⟨hFormula, hBorel, ?_, ?_, ?_⟩
  · intro γ σ htri
    let b : SL(2,F) := σ⁻¹ * toSLF F γ * σ
    have hb : b ∈ borelSL F := by simpa [b] using htri
    obtain ⟨ε, hε, hnorm⟩ := conjugate_borel_diagonal_is_unit γ σ htri
    refine ⟨⟨ε, hε, hnorm⟩, ?_⟩
    intro z
    have hnormB : absFieldNorm F (b 0 0) = 1 := by
      calc
        absFieldNorm F (b 0 0) = absFieldNorm F (algebraMap (𝓞 F) F (ε : 𝓞 F)) := by
          rw [← hε]
        _ = absUnitNorm F ε := rfl
        _ = 1 := hnorm
    rw [hBorel b hb z, hnormB, one_mul]
  · intro g
    let e : X F ≃ₜ X F :=
      { toFun := actAtPlaces F g
        invFun := actAtPlaces F (fun w => (g w)⁻¹)
        left_inv := by
          intro z
          funext w
          simp [actAtPlaces]
        right_inv := by
          intro z
          funext w
          simp [actAtPlaces]
        continuous_toFun := by
          apply continuous_pi
          intro w
          exact (OAI.CubicEisenstein.continuous_hyperbolic_action (g w)).comp
            (continuous_apply w)
        continuous_invFun := by
          apply continuous_pi
          intro w
          exact (OAI.CubicEisenstein.continuous_hyperbolic_action ((g w)⁻¹)).comp
            (continuous_apply w) }
    refine ⟨e, ?_, ?_⟩
    · intro z
      rfl
    · intro z
      rfl
  · intro z
    classical
    apply continuous_pi
    intro w
    obtain ⟨u, hu⟩ := Quotient.mk_surjective (z w)
    change Continuous (fun h : InfinitePlace F → SL(2,ℂ) => h w • z w)
    rw [← hu]
    change Continuous (fun h : InfinitePlace F → SL(2,ℂ) =>
      ((h w * u : SL(2,ℂ)) : OAI.CubicEisenstein.HyperbolicSpace))
    apply OAI.CubicEisenstein.continuous_hyperbolicProjection.comp
    apply Continuous.subtype_mk
    change Continuous (fun h : InfinitePlace F → SL(2,ℂ) =>
      (h w : Matrix (Fin 2) (Fin 2) ℂ) * (u : Matrix (Fin 2) (Fin 2) ℂ))
    exact (continuous_subtype_val.comp (continuous_apply w)).mul continuous_const

private theorem herm_pt_matrix (x : ℂ) (y : ℝ) (hy : 0 < y) :
    herm (pt x y) = !![((Complex.normSq x + y ^ 2 : ℝ) : ℂ) / (y : ℂ),
      x / (y : ℂ); star x / (y : ℂ), (1 : ℂ) / (y : ℂ)] := by
  rw [pt, dif_pos hy]
  change (ptMat x y hy : Matrix (Fin 2) (Fin 2) ℂ) *
      star (ptMat x y hy : Matrix (Fin 2) (Fin 2) ℂ) = _
  have hs : (Real.sqrt y : ℂ) ^ 2 = y := by exact_mod_cast Real.sq_sqrt hy.le
  have hs0 : (Real.sqrt y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hsi : (Real.sqrt y : ℂ)⁻¹ ^ 2 = (y : ℂ)⁻¹ := by rw [inv_pow, hs]
  have hs4 : (Real.sqrt y : ℂ) ^ 4 = (y : ℂ) ^ 2 := by
    calc
      (Real.sqrt y : ℂ) ^ 4 = ((Real.sqrt y : ℂ) ^ 2) ^ 2 := by ring
      _ = (y : ℂ) ^ 2 := by rw [hs]
  have hnorm : x * (starRingEnd ℂ) x = (Complex.normSq x : ℂ) :=
    Complex.mul_conj x
  ext i j
  fin_cases i <;> fin_cases j
  · simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_ofReal]
    field_simp [hs0, hy.ne']
    rw [hs4, hnorm]
    rw [hs]
    ring
  · simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_ofReal]
    field_simp [hs0, hy.ne']
    rw [hs]
  · simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_ofReal]
    field_simp [hs0, hy.ne']
    rw [hs]
    ring
  · simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_ofReal]
    simpa [pow_two] using hsi

private def gramPair (z z' : H3) : ℝ :=
  ((Matrix.trace ((herm z).adjugate * herm z')).re) / 2

private theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.adjugate = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_apply, Matrix.updateRow, Matrix.det_fin_two,
      Fin.sum_univ_two, Function.update, Pi.single_apply]

private theorem ppi_eq_gramPair (z z' : H3) : ppi z z' = gramPair z z' := by
  have hy : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  have hy' : 0 < height z' := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z'
  rw [← pt_horiz_height z, ← pt_horiz_height z']
  rw [ppi, height_pt _ _ hy, height_pt _ _ hy', horiz_pt _ _ hy, horiz_pt _ _ hy']
  rw [gramPair, herm_pt_matrix _ _ hy, herm_pt_matrix _ _ hy', adjugate_fin_two]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_sub,
    Complex.normSq_apply]
  field_simp [hy.ne', hy'.ne']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  ring

private theorem herm_mk (g : SL(2,ℂ)) :
    herm (QuotientGroup.mk g : H3) = (g : Matrix (Fin 2) (Fin 2) ℂ) *
      star (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

private theorem adjugate_sl (g : SL(2,ℂ)) :
    Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) ℂ) =
      ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa using (Matrix.SpecialLinearGroup.coe_inv (A := g)).symm

private theorem adjugate_star_sl (g : SL(2,ℂ)) :
    Matrix.adjugate (star (g : Matrix (Fin 2) (Fin 2) ℂ)) =
      star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  calc
    Matrix.adjugate (star (g : Matrix (Fin 2) (Fin 2) ℂ)) =
        star (Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
          rw [Matrix.star_eq_conjTranspose, ← Matrix.adjugate_conjTranspose,
            Matrix.star_eq_conjTranspose]
    _ = star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by rw [adjugate_sl]

private theorem herm_smul (g : SL(2,ℂ)) (z : H3) :
    herm (g • z) = (g : Matrix (Fin 2) (Fin 2) ℂ) * herm z *
      star (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction z using Quotient.inductionOn with
  | _ h =>
      change (((g * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
          star ((g * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) *
          ((h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ)) *
            star (g : Matrix (Fin 2) (Fin 2) ℂ)
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.star_mul]
      noncomm_ring

private theorem trace_conjugatePair (g : SL(2,ℂ))
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * A *
      ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * B * star (g : Matrix (Fin 2) (Fin 2) ℂ))) =
      Matrix.trace (A * B) := by
  let G : Matrix (Fin 2) (Fin 2) ℂ := g
  let Gi : Matrix (Fin 2) (Fin 2) ℂ := (g⁻¹ : SL(2,ℂ))
  let K : Matrix (Fin 2) (Fin 2) ℂ := star G
  let Ki : Matrix (Fin 2) (Fin 2) ℂ := star Gi
  have hleft : Gi * G = 1 := by
    dsimp [Gi, G]
    simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.det_coe] using
      (Matrix.adjugate_mul (g : Matrix (Fin 2) (Fin 2) ℂ))
  have hstar : K * Ki = 1 := by
    dsimp [K, Ki, G, Gi]
    simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.det_coe,
      Matrix.star_mul] using congrArg star
        (Matrix.adjugate_mul (g : Matrix (Fin 2) (Fin 2) ℂ))
  change Matrix.trace (Ki * A * Gi * (G * B * K)) = Matrix.trace (A * B)
  have hcancel : Ki * A * Gi * (G * B * K) = Ki * A * B * K := by
    calc
      Ki * A * Gi * (G * B * K) = Ki * A * (Gi * (G * (B * K))) := by
        simp only [Matrix.mul_assoc]
      _ = Ki * A * ((Gi * G) * (B * K)) := by
        congr 1
        rw [← Matrix.mul_assoc Gi G (B * K)]
      _ = Ki * A * (B * K) := by rw [hleft]; simp
      _ = Ki * A * B * K := by simp only [Matrix.mul_assoc]
  calc
    Matrix.trace (Ki * A * Gi * (G * B * K)) =
        Matrix.trace (Ki * A * B * K) := congrArg Matrix.trace hcancel
    _ = Matrix.trace (A * B) := by
      calc
        Matrix.trace (Ki * A * B * K) = Matrix.trace ((A * (B * K)) * Ki) := by
          simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Ki (A * (B * K))
        _ = Matrix.trace (A * B) := by
          congr 1
          calc
            (A * (B * K)) * Ki = A * (B * (K * Ki)) := by simp only [Matrix.mul_assoc]
            _ = A * B := by rw [hstar]; simp

private theorem gramPair_smul (g : SL(2,ℂ)) (z z' : H3) :
    gramPair (g • z) (g • z') = gramPair z z' := by
  rw [gramPair, gramPair, herm_smul, herm_smul, Matrix.adjugate_mul_distrib,
    Matrix.adjugate_mul_distrib, adjugate_star_sl, adjugate_sl]
  exact congrArg (fun t : ℂ => t.re / 2) (by
    simpa only [Matrix.mul_assoc] using
      trace_conjugatePair g (herm z).adjugate (herm z'))

private theorem trace_mul_star_eq_normSq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (M * star M) =
      (∑ i : Fin 2, ∑ j : Fin 2, (Complex.normSq (M i j) : ℂ)) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

private noncomputable def complexSpatialEquiv : (ℂ × ℝ) ≃ᵐ
    OAI.CubicEisenstein.EuclideanSpatial :=
  (MeasurableEquiv.prodCongr Complex.measurableEquivPi (MeasurableEquiv.refl ℝ)).trans <|
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (MeasurableEquiv.refl ℝ)).trans <|
      (MeasurableEquiv.prodAssoc.trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm).trans <|
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.trans
            (MeasurableEquiv.toLp 2 _))

private theorem complexSpatialEquiv_measurePreserving :
    MeasurePreserving complexSpatialEquiv volume volume := by
  have h₁ : MeasurePreserving
      (MeasurableEquiv.prodCongr Complex.measurableEquivPi (MeasurableEquiv.refl ℝ))
    (volume : Measure (ℂ × ℝ)) (volume : Measure ((Fin 2 → ℝ) × ℝ)) := by
    simpa [MeasurableEquiv.prodCongr, Measure.volume_eq_prod] using
      (Complex.volume_preserving_equiv_pi.prod (MeasurePreserving.id (volume : Measure ℝ)))
  have h₂ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
        (MeasurableEquiv.refl ℝ))
      (volume : Measure ((Fin 2 → ℝ) × ℝ)) (volume : Measure ((ℝ × ℝ) × ℝ)) := by
    simpa [MeasurableEquiv.prodCongr, Measure.volume_eq_prod] using
      (MeasurePreserving.prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
        (MeasurePreserving.id (volume : Measure ℝ)))
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × ℝ × ℝ)) volume volume := by
    exact volume_preserving_prodAssoc
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm)
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure (ℝ × (Fin 2 → ℝ))) := by
    simpa [MeasurableEquiv.prodCongr, Measure.volume_eq_prod] using
      (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
        (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm)
  have h₅ : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
      (volume : Measure (ℝ × (Fin 2 → ℝ))) (volume : Measure (Fin 3 → ℝ)) := by
    simpa only [Measure.volume_eq_prod] using
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have h₆ : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure OAI.CubicEisenstein.EuclideanSpatial) := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm
  exact h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))

private theorem complexSpatialEquiv_apply (q : ℂ × ℝ) (i : Fin 3) :
    complexSpatialEquiv q i = ![q.1.re, q.1.im, q.2] i := by
  fin_cases i <;> simp [complexSpatialEquiv, MeasurableEquiv.prodCongr,
    Complex.measurableEquivPi_apply,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.piFinTwo, MeasurableEquiv.piFinSuccAbove]

private theorem complexSpatialEquiv_height (q : ℂ × ℝ) :
    complexSpatialEquiv q 2 = q.2 := by
  simpa using complexSpatialEquiv_apply q 2

private theorem complexSpatialEquiv_horizontal (q : ℂ × ℝ) :
    (complexSpatialEquiv q 0 : ℂ) + Complex.I * (complexSpatialEquiv q 1 : ℂ) = q.1 := by
  apply Complex.ext <;> simp [complexSpatialEquiv_apply]

private theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β) (hμν : Measure.map e μ = ν)
    (f : β → ENNReal) :
    Measure.map e (μ.withDensity (fun x => f (e x))) = ν.withDensity f := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage e.measurable) (fun x => f (e x)),
    ← lintegral_indicator hs f]
  rw [← hμν, MeasureTheory.lintegral_map_equiv]
  congr 1

private theorem volH3_eq_OAI :
    volH3 = OAI.CubicEisenstein.hyperbolicVolume := by
  let S : Set (ℂ × ℝ) := {q | 0 < q.2}
  let T : Set OAI.CubicEisenstein.EuclideanSpatial := OAI.CubicEisenstein.euclideanUpperHalf
  let μ : Measure (ℂ × ℝ) := (volume.restrict S).withDensity
    (fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹))
  let ν : Measure OAI.CubicEisenstein.EuclideanSpatial :=
    (volume.restrict T).withDensity OAI.CubicEisenstein.hyperbolicDensity
  have hpre : complexSpatialEquiv ⁻¹' T = S := by
    ext q
    simp [T, S, OAI.CubicEisenstein.euclideanUpperHalf, complexSpatialEquiv_height]
  have hrestrict : MeasurePreserving complexSpatialEquiv (volume.restrict S)
      (volume.restrict T) := by
    rw [← hpre]
    exact complexSpatialEquiv_measurePreserving.restrict_preimage
      (OAI.CubicEisenstein.euclideanUpperHalf_measurable)
  have hden : (fun q : ℂ × ℝ => OAI.CubicEisenstein.hyperbolicDensity
      (complexSpatialEquiv q)) = fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹) := by
    funext q
    simp [OAI.CubicEisenstein.hyperbolicDensity, complexSpatialEquiv_height]
  have hmapD : Measure.map complexSpatialEquiv μ = ν := by
    dsimp [μ, ν]
    rw [← hden]
    exact map_withDensity_equiv complexSpatialEquiv (volume.restrict S) (volume.restrict T)
      hrestrict.map_eq OAI.CubicEisenstein.hyperbolicDensity
  have hpos : ∀ᵐ q ∂μ, 0 < q.2 := by
    dsimp [μ]
    exact (ae_restrict_mem (show MeasurableSet S from
      measurableSet_lt measurable_const (by fun_prop))).filter_mono
      ((withDensity_absolutelyContinuous (volume.restrict S)
        (fun q : ℂ × ℝ => ENNReal.ofReal ((q.2 ^ 3)⁻¹))).ae_le)
  have hpoint : ∀ q : ℂ × ℝ, 0 < q.2 →
      OAI.CubicEisenstein.euclideanToHyperbolic (complexSpatialEquiv q) = pt q.1 q.2 := by
    intro q hq
    rw [OAI.CubicEisenstein.euclideanToHyperbolic_positive _
      (by rw [complexSpatialEquiv_height]; exact hq), complexSpatialEquiv_horizontal]
    exact (pt_eq_upperPoint q.1 q.2 hq).symm
  unfold volH3 OAI.CubicEisenstein.hyperbolicVolume
  change Measure.map (fun q : ℂ × ℝ => pt q.1 q.2) μ =
    Measure.map OAI.CubicEisenstein.euclideanToHyperbolic ν
  calc
    _ = Measure.map (OAI.CubicEisenstein.euclideanToHyperbolic ∘ complexSpatialEquiv) μ := by
      apply Measure.map_congr
      filter_upwards [hpos] with q hq
      exact (hpoint q hq).symm
    _ = Measure.map OAI.CubicEisenstein.euclideanToHyperbolic
        (Measure.map complexSpatialEquiv μ) := by
      rw [Measure.map_map OAI.CubicEisenstein.euclideanToHyperbolic_measurable
        complexSpatialEquiv.measurable]
    _ = Measure.map OAI.CubicEisenstein.euclideanToHyperbolic ν := by rw [hmapD]

private theorem pi_withDensity_prod_fin {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (d : α → ENNReal) (hd : Measurable d)
    [SigmaFinite μ] [SigmaFinite (μ.withDensity d)] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).withDensity (fun p => ∏ i, d (p i)) =
      Measure.pi (fun _ : Fin n => μ.withDensity d) := by
  induction n with
  | zero =>
      haveI : IsEmpty (Fin 0) := inferInstance
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      let μR : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ)
      let dR : (Fin n → α) → ENNReal := fun x => ∏ i, d (x i)
      let νR : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ.withDensity d)
      have hμe : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => μ))
          (μ.prod μR) := by
        simpa [e, μR] using
          measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
      have hνe : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => μ.withDensity d))
          ((μ.withDensity d).prod νR) := by
        simpa [e, νR] using
          measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ.withDensity d) 0
      have heval (x : Fin (n + 1) → α) :
          (∏ i : Fin (n + 1), d (x i)) = d (e x).1 * dR (e x).2 := by
        simp [e, dR, Fin.prod_univ_succ, Fin.tail]
      have hdR : Measurable dR := by
        dsimp [dR]
        fun_prop
      have hmapLeft :
          Measure.map e ((Measure.pi (fun _ : Fin (n + 1) => μ)).withDensity
            (fun p => ∏ i, d (p i))) = (μ.withDensity d).prod (μR.withDensity dR) := by
        have hden : (fun p : Fin (n + 1) → α => ∏ i, d (p i)) =
            fun p => d (e p).1 * dR (e p).2 := funext heval
        rw [hden]
        calc
          _ = (μ.prod μR).withDensity (fun z => d z.1 * dR z.2) :=
            map_withDensity_equiv e _ _ hμe.map_eq (fun z => d z.1 * dR z.2)
          _ = (μ.withDensity d).prod (μR.withDensity dR) := by
            symm
            exact prod_withDensity hd hdR
      have hmapEq : Measure.map e
          ((Measure.pi (fun _ : Fin (n + 1) => μ)).withDensity
            (fun p => ∏ i, d (p i))) =
          Measure.map e (Measure.pi (fun _ : Fin (n + 1) => μ.withDensity d)) := by
        calc
          _ = (μ.withDensity d).prod νR := by
            rw [hmapLeft]
            simpa [μR, dR, νR] using
              congrArg (fun m : Measure (Fin n → α) => (μ.withDensity d).prod m) ih
          _ = _ := hνe.map_eq.symm
      exact e.measurableEmbedding.map_injective hmapEq

private theorem pi_withDensity_prod {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (d : α → ENNReal) (hd : Measurable d)
    [SigmaFinite μ] [SigmaFinite (μ.withDensity d)] :
    (Measure.pi (fun _ : ι => μ)).withDensity (fun p => ∏ i, d (p i)) =
      Measure.pi (fun _ : ι => μ.withDensity d) := by
  let eI : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let eP : (Fin (Fintype.card ι) → α) ≃ᵐ (ι → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => α) eI
  let μFin : Measure (Fin (Fintype.card ι) → α) :=
    Measure.pi (fun _ : Fin (Fintype.card ι) => μ)
  let νFin : Measure (Fin (Fintype.card ι) → α) :=
    Measure.pi (fun _ : Fin (Fintype.card ι) => μ.withDensity d)
  have hμe : MeasurePreserving eP μFin (Measure.pi (fun _ : ι => μ)) := by
    simpa [eP, μFin] using measurePreserving_piCongrLeft (fun _ : ι => μ) eI
  have hνe : MeasurePreserving eP νFin (Measure.pi (fun _ : ι => μ.withDensity d)) := by
    simpa [eP, νFin] using measurePreserving_piCongrLeft (fun _ : ι => μ.withDensity d) eI
  have heval (x : Fin (Fintype.card ι) → α) :
      (∏ i : Fin (Fintype.card ι), d (x i)) = ∏ i : ι, d (eP x i) := by
    simp [eP, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    exact (Equiv.prod_comp eI.symm (fun j : Fin (Fintype.card ι) => d (x j))).symm
  have hmapLeft : Measure.map eP (μFin.withDensity (fun x => ∏ i, d (x i))) =
      (Measure.pi (fun _ : ι => μ)).withDensity (fun x => ∏ i, d (x i)) := by
    have hden : (fun x : Fin (Fintype.card ι) → α => ∏ i, d (x i)) =
        fun x => ∏ i, d (eP x i) := funext heval
    rw [hden]
    exact map_withDensity_equiv eP μFin (Measure.pi (fun _ : ι => μ)) hμe.map_eq
      (fun x => ∏ i, d (x i))
  have hmapEq : Measure.map eP (μFin.withDensity (fun x => ∏ i, d (x i))) =
      Measure.map eP νFin := by
    rw [pi_withDensity_prod_fin μ d hd (Fintype.card ι)]
  calc
    (Measure.pi (fun _ : ι => μ)).withDensity (fun x => ∏ i, d (x i)) =
        Measure.map eP (μFin.withDensity (fun x => ∏ i, d (x i))) := hmapLeft.symm
    _ = Measure.map eP νFin := hmapEq
    _ = Measure.pi (fun _ : ι => μ.withDensity d) := hνe.map_eq

private theorem ennreal_ofReal_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his, Finset.prod_insert his,
        ENNReal.ofReal_mul (hf i (Finset.mem_insert_self i s))]
      apply congrArg (fun x : ENNReal => ENNReal.ofReal (f i) * x)
      exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem oai_hyperbolicVolume_sigmaFinite :
    SigmaFinite OAI.CubicEisenstein.hyperbolicVolume := by
  letI : TopologicalSpace (SL(2,ℂ)) := OAI.CubicEisenstein.complexSLTopology
  letI : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace := by infer_instance
  letI : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicMeasurableSpace
  letI : BorelSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicBorelSpace
  letI : IsFiniteMeasureOnCompacts OAI.CubicEisenstein.hyperbolicVolume :=
    OAI.CubicEisenstein.hyperbolicVolume_finiteOnCompacts
  infer_instance

private theorem oai_hyperbolicVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts OAI.CubicEisenstein.hyperbolicVolume := by
  letI : TopologicalSpace (SL(2,ℂ)) := OAI.CubicEisenstein.complexSLTopology
  letI : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace := by infer_instance
  letI : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicMeasurableSpace
  letI : BorelSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicBorelSpace
  exact OAI.CubicEisenstein.hyperbolicVolume_finiteOnCompacts

private def positiveCoordSet : Set (ℂ × ℝ) := {q | 0 < q.2}

private def positiveCoordMeasure : Measure (ℂ × ℝ) :=
  (volume.restrict positiveCoordSet).withDensity
    (fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹))

private def factorChart : ℂ × ℝ → H3 := fun q => pt q.1 q.2

private theorem volH3_eq_factorChartMeasure :
    volH3 = Measure.map factorChart positiveCoordMeasure := rfl

private theorem factorChart_aemeasurable :
    AEMeasurable factorChart positiveCoordMeasure := by
  have hS : MeasurableSet positiveCoordSet := by
    exact measurableSet_lt measurable_const (by fun_prop)
  have hpos : ∀ᵐ q ∂positiveCoordMeasure, q ∈ positiveCoordSet := by
    dsimp [positiveCoordMeasure]
    exact (ae_restrict_mem hS).filter_mono
      ((withDensity_absolutelyContinuous (volume.restrict positiveCoordSet)
        (fun q : ℂ × ℝ => ENNReal.ofReal ((q.2 ^ 3)⁻¹))).ae_le)
  have hf : Measurable (fun q : ℂ × ℝ =>
      OAI.CubicEisenstein.euclideanToHyperbolic (complexSpatialEquiv q)) :=
    OAI.CubicEisenstein.euclideanToHyperbolic_measurable.comp complexSpatialEquiv.measurable
  have hEq : (fun q : ℂ × ℝ =>
      OAI.CubicEisenstein.euclideanToHyperbolic (complexSpatialEquiv q)) =ᵐ[
        positiveCoordMeasure] factorChart := by
    filter_upwards [hpos] with q hq
    have hy : 0 < q.2 := hq
    rw [OAI.CubicEisenstein.euclideanToHyperbolic_positive _
      (by rw [complexSpatialEquiv_height]; exact hy), complexSpatialEquiv_horizontal]
    exact (pt_eq_upperPoint q.1 q.2 hy).symm
  exact hf.aemeasurable.congr hEq

private theorem volH3_finiteOnCompacts : IsFiniteMeasureOnCompacts volH3 := by
  letI : TopologicalSpace (SL(2,ℂ)) := OAI.CubicEisenstein.complexSLTopology
  letI : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace := by infer_instance
  letI : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicMeasurableSpace
  letI : BorelSpace OAI.CubicEisenstein.HyperbolicSpace :=
    OAI.CubicEisenstein.hyperbolicBorelSpace
  rw [volH3_eq_OAI]
  exact OAI.CubicEisenstein.hyperbolicVolume_finiteOnCompacts

private theorem volH3_sigmaFinite : SigmaFinite volH3 := by
  rw [volH3_eq_OAI]
  exact oai_hyperbolicVolume_sigmaFinite

private def coordDensity (p : Coord F) : ENNReal :=
  ENNReal.ofReal (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹)

private theorem positiveCoordMeasure_pi_eq :
    (volume.restrict (posSet F)).withDensity coordDensity =
      Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure) := by
  let S : Set (ℂ × ℝ) := positiveCoordSet
  let μ : Measure (ℂ × ℝ) := volume.restrict S
  let d : ℂ × ℝ → ENNReal := fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹)
  have hSetPos : posSet F = Set.univ.pi (fun _ : InfinitePlace F => S) := by
    ext p
    simp [posSet, S, positiveCoordSet]
  have hS : MeasurableSet S := by
    exact measurableSet_lt measurable_const (by fun_prop)
  have hPosMeas : MeasurableSet (posSet F) := by
    rw [hSetPos]
    exact MeasurableSet.univ_pi fun _ => hS
  have hvol : (volume : Measure (Coord F)) =
      Measure.pi (fun _ : InfinitePlace F => (volume : Measure (ℂ × ℝ))) := by
    simpa [Coord] using (MeasureTheory.volume_pi (α := fun _ : InfinitePlace F => ℂ × ℝ))
  have hRestr : volume.restrict (posSet F) =
      Measure.pi (fun _ : InfinitePlace F => μ) := by
    rw [hSetPos, hvol, Measure.restrict_pi_pi]
  have hd : Measurable d := by
    dsimp [d]
    fun_prop
  have hDen : coordDensity =ᵐ[
        Measure.pi (fun _ : InfinitePlace F => μ)] fun p =>
        ∏ w : InfinitePlace F, d (p w) := by
    have hpos : ∀ᵐ p ∂(Measure.pi (fun _ : InfinitePlace F => μ)), p ∈ posSet F := by
      rw [← hRestr]
      exact ae_restrict_mem hPosMeas
    filter_upwards [hpos] with p hp
    dsimp [coordDensity, d]
    apply ennreal_ofReal_prod
    intro w hw
    have h := hp w
    positivity
  rw [hRestr, withDensity_congr_ae hDen]
  simpa [S, μ, positiveCoordMeasure, d] using
    (pi_withDensity_prod μ d hd :
      (Measure.pi (fun _ : InfinitePlace F => μ)).withDensity
          (fun p => ∏ w : InfinitePlace F, d (p w)) =
        Measure.pi (fun _ : InfinitePlace F => μ.withDensity d))

private theorem volX_eq_pi_volH3 :
    volX F = Measure.pi (fun _ : InfinitePlace F => volH3) := by
  letI : SigmaFinite (Measure.map factorChart positiveCoordMeasure) := by
    rw [← volH3_eq_factorChartMeasure]
    exact volH3_sigmaFinite
  calc
    volX F = Measure.map (fun p : Coord F => fun w : InfinitePlace F => factorChart (p w))
        (Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure)) := by
      unfold volX
      change Measure.map (ptX F)
        ((volume.restrict (posSet F)).withDensity coordDensity) = _
      rw [positiveCoordMeasure_pi_eq]
      rfl
    _ = Measure.pi (fun _ : InfinitePlace F => Measure.map factorChart positiveCoordMeasure) := by
      exact Measure.pi_map_pi (fun _ => factorChart_aemeasurable)
    _ = Measure.pi (fun _ : InfinitePlace F => volH3) := by
      rw [volH3_eq_factorChartMeasure]

private theorem volH3_isOpenPosMeasure : Measure.IsOpenPosMeasure volH3 := by
  constructor
  intro U hU hne
  let chart : OAI.CubicEisenstein.UpperCoordinates → H3 :=
    fun p => pt p.1.1 p.1.2
  let W : Set OAI.CubicEisenstein.UpperCoordinates := chart ⁻¹' U
  have hchart : Continuous chart := by
    change Continuous (fun p : OAI.CubicEisenstein.UpperCoordinates => pt p.1.1 p.1.2)
    exact OAI.CubicEisenstein.continuous_upperCoordinates.congr fun p =>
      (pt_eq_upperPoint p.1.1 p.1.2 p.2).symm
  have hWopen : IsOpen W := hU.preimage hchart
  obtain ⟨z, hz⟩ := hne
  have hy : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  let p : OAI.CubicEisenstein.UpperCoordinates := ⟨(horiz z, height z), hy⟩
  have hpW : p ∈ W := by
    change chart p ∈ U
    change pt (horiz z) (height z) ∈ U
    rw [pt_horiz_height]
    exact hz
  have hWne : W.Nonempty := ⟨p, hpW⟩
  obtain ⟨V, hV, hpre⟩ :=
    (isOpen_induced_iff (f := (Subtype.val :
      OAI.CubicEisenstein.UpperCoordinates → ℂ × ℝ))).mp hWopen
  let A : Set (ℂ × ℝ) := V ∩ positiveCoordSet
  have hSopen : IsOpen positiveCoordSet := by
    change IsOpen {q : ℂ × ℝ | 0 < q.2}
    exact isOpen_lt continuous_const continuous_snd
  have hAopen : IsOpen A := by
    exact hV.inter hSopen
  have hAne : A.Nonempty := by
    obtain ⟨p, hp⟩ := hWne
    have hpV : (p : ℂ × ℝ) ∈ V := by
      have hp' : p ∈ Subtype.val ⁻¹' V := by
        rw [hpre]
        exact hp
      exact hp'
    exact ⟨p, hpV, p.2⟩
  have hAsub : A ⊆ positiveCoordSet := Set.inter_subset_right
  have hApre : A ⊆ factorChart ⁻¹' U := by
    rintro q ⟨hqV, hqpos⟩
    let p : OAI.CubicEisenstein.UpperCoordinates := ⟨q, hqpos⟩
    have hp' : p ∈ Subtype.val ⁻¹' V := by
      simpa using hqV
    have hpW : p ∈ W := by
      rw [← hpre]
      exact hp'
    simpa [W, chart, factorChart, p] using hpW
  have hd : Measurable (fun q : ℂ × ℝ => ENNReal.ofReal ((q.2 ^ 3)⁻¹)) := by
    fun_prop
  have hfactorA : positiveCoordMeasure A ≠ 0 := by
    change (volume.restrict positiveCoordSet).withDensity
      (fun q : ℂ × ℝ => ENNReal.ofReal ((q.2 ^ 3)⁻¹)) A ≠ 0
    intro hzero
    have hzero' := (withDensity_apply_eq_zero hd).mp hzero
    have hnonzero :
        {q : ℂ × ℝ | ENNReal.ofReal ((q.2 ^ 3)⁻¹) ≠ 0} ∩ A = A := by
      ext q
      constructor
      · exact fun h => h.2
      · intro hq
        refine ⟨?_, hq⟩
        have hyq : 0 < q.2 := hAsub hq
        exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < (q.2 ^ 3)⁻¹)).ne'
    have hRestrA : (volume.restrict positiveCoordSet) A = volume A := by
      rw [Measure.restrict_apply hAopen.measurableSet]
      simp [Set.inter_eq_left.mpr hAsub]
    have hvolZero : volume A = 0 := by
      calc
        volume A = (volume.restrict positiveCoordSet) A := hRestrA.symm
        _ = (volume.restrict positiveCoordSet)
            ({q : ℂ × ℝ | ENNReal.ofReal ((q.2 ^ 3)⁻¹) ≠ 0} ∩ A) := by
              rw [hnonzero]
        _ = 0 := hzero'
    exact (ne_of_gt (hAopen.measure_pos volume hAne)) hvolZero
  have hmap : volH3 U = positiveCoordMeasure (factorChart ⁻¹' U) := by
    rw [volH3_eq_factorChartMeasure]
    exact Measure.map_apply_of_aemeasurable factorChart_aemeasurable hU.measurableSet
  have hprepos : 0 < positiveCoordMeasure (factorChart ⁻¹' U) :=
    lt_of_lt_of_le hfactorA.bot_lt (measure_mono hApre)
  rw [hmap]
  exact hprepos.ne'

private theorem ppi_mk_eq_frobenius (g h : SL(2,ℂ)) :
    ppi (QuotientGroup.mk g : H3) (QuotientGroup.mk h : H3) =
      (∑ i : Fin 2, ∑ j : Fin 2,
        Complex.normSq ((g⁻¹ * h : SL(2,ℂ)) i j)) / 2 := by
  rw [ppi_eq_gramPair, gramPair, herm_mk, herm_mk, Matrix.adjugate_mul_distrib,
    adjugate_star_sl, adjugate_sl]
  have htrace :
      Matrix.trace (star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ))) =
      Matrix.trace (((g⁻¹ * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((g⁻¹ * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    calc
      _ = Matrix.trace ((((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
          (h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ)) *
          star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) := by
            simpa only [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm
                (star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ))
                (((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
                  ((h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ))))
      _ = Matrix.trace ((((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
          (h : Matrix (Fin 2) (Fin 2) ℂ)) *
          (star (h : Matrix (Fin 2) (Fin 2) ℂ) *
            star ((g⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ))) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.star_mul]
  rw [htrace]
  rw [trace_mul_star_eq_normSq]
  simp [Complex.ofReal_re]

/-- G3 `spec:volume` — P-SPEC.md:210. Invariance, the coordinate density, local finiteness and
positivity, and the product measure formula for hyperbolic volume. -/
theorem G3_volume :
    (∀ g : InfinitePlace F → SL(2,ℂ),
      Measure.map (fun z : X F => actAtPlaces F g z) (volX F) = volX F) ∧
    (∀ f : X F → ℝ, Integrable f (volX F) →
      ∫ z, f z ∂(volX F) =
        ∫ p, f (ptX F p) * (∏ w, ((p w).2 ^ 3)⁻¹)
          ∂(volume.restrict (posSet F))) ∧
    (∀ K : Set (X F), IsCompact K → volX F K < ⊤) ∧
    (∀ U : Set (X F), IsOpen U → U.Nonempty → volX F U ≠ 0) ∧
    volX F = Measure.pi (fun _ : InfinitePlace F => volH3) := by
  have hpi : volX F = Measure.pi (fun _ : InfinitePlace F => volH3) :=
    volX_eq_pi_volH3
  letI : SigmaFinite positiveCoordMeasure := by
    dsimp [positiveCoordMeasure]
    infer_instance
  letI : SigmaFinite volH3 := volH3_sigmaFinite
  refine ⟨?_, ?_, ?_, ?_, hpi⟩
  · intro g
    rw [hpi]
    have hpres : ∀ w : InfinitePlace F,
        Measure.map (fun z : H3 => g w • z) volH3 = volH3 := by
      intro w
      rw [volH3_eq_OAI]
      exact OAI.CubicEisenstein.hyperbolicVolume_invariant (g w)
    letI : ∀ w : InfinitePlace F,
        SigmaFinite (Measure.map (fun z : H3 => g w • z) volH3) := by
      intro w
      rw [hpres w]
      infer_instance
    have hmap := Measure.pi_map_pi
      (μ := fun _ : InfinitePlace F => volH3)
      (f := fun (w : InfinitePlace F) (z : H3) => g w • z)
      (fun w => (OAI.CubicEisenstein.continuous_hyperbolic_action (g w)).measurable.aemeasurable)
    calc
      Measure.map (fun z : X F => actAtPlaces F g z)
          (Measure.pi (fun _ : InfinitePlace F => volH3)) =
          Measure.map (fun x w => g w • x w)
            (Measure.pi (fun _ : InfinitePlace F => volH3)) := by rfl
      _ = Measure.pi (fun w => Measure.map (fun z : H3 => g w • z) volH3) := hmap
      _ = Measure.pi (fun _ : InfinitePlace F => volH3) := by
        congr 1
        funext w
        exact hpres w
  · intro f hf
    have hptX : AEMeasurable (ptX F)
        (Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure)) := by
      apply AEMeasurable.of_eval
      intro w
      change AEMeasurable (fun p : Coord F => factorChart (p w)) _
      exact factorChart_aemeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval
          (fun _ : InfinitePlace F => positiveCoordMeasure) w)
    have hvolMap : volX F =
        Measure.map (ptX F) (Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure)) := by
      calc
        volX F = Measure.map (ptX F)
            ((volume.restrict (posSet F)).withDensity coordDensity) := by rfl
        _ = _ := by rw [positiveCoordMeasure_pi_eq]
    have hfMap : AEStronglyMeasurable f
        (Measure.map (ptX F) (Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure))) := by
      rw [← hvolMap]
      exact hf.aestronglyMeasurable
    have hdensityMeas : Measurable (coordDensity (F := F)) := by
      change Measurable (fun p : Coord F =>
        ENNReal.ofReal (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹))
      fun_prop
    have hdensityTop : ∀ᵐ p ∂(volume.restrict (posSet F)),
        coordDensity p < ⊤ := by
      filter_upwards [] with p
      exact ENNReal.ofReal_lt_top
    calc
      ∫ z, f z ∂(volX F) =
          ∫ z, f z ∂Measure.map (ptX F)
            (Measure.pi (fun _ : InfinitePlace F => positiveCoordMeasure)) := by
              rw [hvolMap]
      _ = ∫ p, f (ptX F p) ∂(Measure.pi
          (fun _ : InfinitePlace F => positiveCoordMeasure)) :=
            MeasureTheory.integral_map hptX hfMap
      _ = ∫ p, f (ptX F p) ∂((volume.restrict (posSet F)).withDensity coordDensity) := by
            rw [← positiveCoordMeasure_pi_eq]
      _ = ∫ p, (coordDensity p).toReal • f (ptX F p)
            ∂(volume.restrict (posSet F)) := by
              rw [integral_withDensity_eq_integral_toReal_smul hdensityMeas hdensityTop]
      _ = ∫ p, f (ptX F p) * (∏ w, ((p w).2 ^ 3)⁻¹)
            ∂(volume.restrict (posSet F)) := by
              apply integral_congr_ae
              have hPosMeas : MeasurableSet (posSet F) := by
                have hSetPos : posSet F = Set.univ.pi
                    (fun _ : InfinitePlace F => positiveCoordSet) := by
                  ext p
                  simp [posSet, positiveCoordSet]
                rw [hSetPos]
                exact MeasurableSet.univ_pi fun _ => by
                  exact measurableSet_lt measurable_const (by fun_prop)
              filter_upwards [ae_restrict_mem hPosMeas] with p hp
              have hweight : 0 ≤ ∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹ := by
                apply Finset.prod_nonneg
                intro w hw
                have hy : 0 < (p w).2 := hp w
                exact inv_nonneg.mpr (by positivity)
              have hreal : (coordDensity p).toReal =
                  ∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹ := by
                rw [coordDensity, ENNReal.toReal_ofReal hweight]
              rw [smul_eq_mul, hreal, mul_comm]
  · intro K hK
    letI : IsFiniteMeasureOnCompacts volH3 := volH3_finiteOnCompacts
    rw [hpi]
    exact hK.measure_lt_top
  · intro U hU hne
    letI : Measure.IsOpenPosMeasure volH3 := volH3_isOpenPosMeasure
    rw [hpi]
    exact hU.measure_ne_zero (Measure.pi (fun _ : InfinitePlace F => volH3)) hne

/-- G6 `spec:ppi` — P-SPEC.md:213, 267–270. The point-pair invariant is isometry-invariant,
separates points, controls the coordinates in a small ball, and is smooth in positive coordinates. -/
theorem G6_ppi :
    (∀ g : SL(2,ℂ), ∀ z z' : H3,
      ppi (g • z) (g • z') = ppi z z') ∧
    (∀ g h : SL(2,ℂ),
      ppi (QuotientGroup.mk g : H3) (QuotientGroup.mk h : H3) =
        (∑ i : Fin 2, ∑ j : Fin 2,
          Complex.normSq ((g⁻¹ * h : SL(2,ℂ)) i j)) / 2) ∧
    (∀ z z' : H3, 1 ≤ ppi z z' ∧ (ppi z z' = 1 ↔ z = z')) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ z : H3,
      ppi (pt 0 1) z ≤ 1 + ρ →
        |Real.log (height z)| ≤ Real.arcosh (1 + ρ) ∧
          ‖horiz z‖ ≤ Real.sqrt (2 * ρ + ρ ^ 2)) ∧
    ∀ w : InfinitePlace F,
      ContDiffOn ℝ ∞ (fun pq : Coord F × Coord F => ppiCoordAt F w pq)
        {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g z z'
    rw [ppi_eq_gramPair, ppi_eq_gramPair, gramPair_smul]
  · exact ppi_mk_eq_frobenius
  · intro z z'
    have hy : 0 < height z := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos z
    have hy' : 0 < height z' := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos z'
    have hden : 0 < 2 * height z * height z' := by positivity
    constructor
    · dsimp [ppi]
      rw [le_div_iff₀ hden]
      nlinarith [Complex.normSq_nonneg (horiz z - horiz z'),
        sq_nonneg (height z - height z')]
    · constructor
      · intro heq
        dsimp [ppi] at heq
        have hnum :
            Complex.normSq (horiz z - horiz z') + height z ^ 2 + height z' ^ 2 =
              2 * height z * height z' := by
          field_simp [hden.ne'] at heq
          linarith
        have hnorm : Complex.normSq (horiz z - horiz z') = 0 := by
          nlinarith [Complex.normSq_nonneg (horiz z - horiz z'),
            sq_nonneg (height z - height z')]
        have hyEq : height z = height z' := by nlinarith [hnum, hnorm]
        have hxEq : horiz z = horiz z' := by
          exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hnorm)
        calc
          z = pt (horiz z) (height z) := (pt_horiz_height z).symm
          _ = pt (horiz z') (height z') := by rw [hxEq, hyEq]
          _ = z' := pt_horiz_height z'
      · intro hz
        subst z'
        dsimp [ppi]
        field_simp [hy.ne']
        simp [Complex.normSq_zero]
        ring
  · intro ρ hρ z hball
    have hy : 0 < height z := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos z
    let y := height z
    let x := horiz z
    have hcenter : ppi (pt 0 1) z =
        (Complex.normSq x + 1 + y ^ 2) / (2 * y) := by
      rw [ppi, horiz_pt 0 1 (by norm_num), height_pt 0 1 (by norm_num)]
      simp [x, y]
    have hnum : Complex.normSq x + 1 + y ^ 2 ≤ 2 * y * (1 + ρ) := by
      rw [hcenter] at hball
      have hden : 0 < 2 * y := by positivity
      have htmp := (div_le_iff₀ hden).mp hball
      nlinarith [htmp]
    have hsum : 1 + y ^ 2 ≤ 2 * y * (1 + ρ) := by
      nlinarith [hnum, Complex.normSq_nonneg x]
    have hhalf : (y + y⁻¹) / 2 ≤ 1 + ρ := by
      have hmul : y * (y + y⁻¹) ≤ y * (2 * (1 + ρ)) := by
        have hleft : y * (y + y⁻¹) = 1 + y ^ 2 := by
          rw [mul_add, mul_inv_cancel₀ hy.ne']
          ring
        rw [hleft]
        nlinarith [hsum]
      have hquot : y + y⁻¹ ≤ 2 * (1 + ρ) := le_of_mul_le_mul_left hmul hy
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hquot])
    have hcosh : Real.cosh (Real.log y) ≤ 1 + ρ := by
      rw [Real.cosh_log hy]
      exact hhalf
    have hcoshAbs : Real.cosh |Real.log y| ≤ 1 + ρ := by
      simpa only [Real.cosh_abs] using hcosh
    have harcosh : Real.arcosh (Real.cosh |Real.log y|) ≤ Real.arcosh (1 + ρ) :=
      (Real.arcosh_le_arcosh (Real.cosh_pos _) (by linarith)).2 hcoshAbs
    have hlog : |Real.log y| ≤ Real.arcosh (1 + ρ) := by
      calc
        |Real.log y| = Real.arcosh (Real.cosh |Real.log y|) :=
          (Real.arcosh_cosh (abs_nonneg _)).symm
        _ ≤ Real.arcosh (1 + ρ) := harcosh
    have hbox : Complex.normSq x + (y - (1 + ρ)) ^ 2 ≤ 2 * ρ + ρ ^ 2 := by
      nlinarith [hnum, sq_nonneg (y - (1 + ρ))]
    have hnormSq : Complex.normSq x ≤ 2 * ρ + ρ ^ 2 := by
      nlinarith [hbox, sq_nonneg (y - (1 + ρ))]
    have hnormSq' : ‖x‖ ^ 2 ≤ 2 * ρ + ρ ^ 2 := by
      simpa only [Complex.normSq_eq_norm_sq] using hnormSq
    have hnorm : ‖x‖ ≤ Real.sqrt (2 * ρ + ρ ^ 2) := by
      calc
        ‖x‖ = Real.sqrt (‖x‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
        _ ≤ Real.sqrt (2 * ρ + ρ ^ 2) := Real.sqrt_le_sqrt hnormSq'
    exact ⟨hlog, hnorm⟩
  · intro w pq hpq
    letI : NormedSpace ℝ ℝ := RCLike.toInnerProductSpaceReal.toNormedSpace
    let u : Coord F × Coord F → ℂ := fun q => (q.1 w).1 - (q.2 w).1
    let y₁ : Coord F × Coord F → ℝ := fun q => (q.1 w).2
    let y₂ : Coord F × Coord F → ℝ := fun q => (q.2 w).2
    let num : Coord F × Coord F → ℝ := fun q =>
      (u q).re ^ 2 + (u q).im ^ 2 + y₁ q ^ 2 + y₂ q ^ 2
    let den : Coord F × Coord F → ℝ := fun q => 2 * y₁ q * y₂ q
    have hu : ContDiff ℝ ∞ u := by dsimp [u]; fun_prop
    have hy₁ : ContDiff ℝ ∞ y₁ := by dsimp [y₁]; fun_prop
    have hy₂ : ContDiff ℝ ∞ y₂ := by dsimp [y₂]; fun_prop
    have hRe : ContDiff ℝ ∞ (fun q => (u q).re) := by
      have hr := Complex.reCLM.contDiff.comp hu
      convert hr using 1
      funext q
      exact (Complex.reCLM_apply (u q)).symm
    have hIm : ContDiff ℝ ∞ (fun q => (u q).im) := by
      have hi := Complex.imCLM.contDiff.comp hu
      convert hi using 1
      funext q
      exact (Complex.imCLM_apply (u q)).symm
    have hnum : ContDiff ℝ ∞ num := by dsimp [num]; fun_prop
    have hden : ContDiff ℝ ∞ den := by dsimp [den]; fun_prop
    have hy₁pos : 0 < y₁ pq := by exact hpq.1 w
    have hy₂pos : 0 < y₂ pq := by exact hpq.2 w
    have hden_ne : den pq ≠ 0 := by
      dsimp [den, y₁, y₂]
      positivity
    dsimp [ppiCoordAt]
    simp_rw [Complex.normSq_apply]
    have hAtDiv : ContDiffWithinAt ℝ ∞
        ((fun q => num q) / (fun q => den q))
        {q | q.1 ∈ posSet F ∧ q.2 ∈ posSet F} pq :=
      (hnum.contDiffAt.div hden.contDiffAt hden_ne).contDiffWithinAt
    have hAtFun : ContDiffWithinAt ℝ ∞ (fun q => num q / den q)
        {q | q.1 ∈ posSet F ∧ q.2 ∈ posSet F} pq :=
      hAtDiv.congr (by intro q hq; rfl) rfl
    simpa [num, den, u, y₁, y₂, pow_two] using hAtFun

end ArtinPrimitiveRoots.A1.Spec
