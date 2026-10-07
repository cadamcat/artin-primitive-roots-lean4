import ArtinPrimitiveRoots.Spec.Defs
import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
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
  sorry

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
  sorry

end ArtinPrimitiveRoots.A1.Spec
