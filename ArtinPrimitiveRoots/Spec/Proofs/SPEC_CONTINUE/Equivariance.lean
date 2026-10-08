import ArtinPrimitiveRoots.Spec.Geometry
import Mathlib.MeasureTheory.Integral.Pi
import Lean

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups
open Lean Elab Term

noncomputable section

open ArtinPrimitiveRoots.A1.Spec

namespace ArtinPrimitiveRoots.Proofs.spec_continue_p

elab "volH3_sigmaFiniteExact" : term => do
  let n := Name.num (Name.str (Name.str (Name.str `_private "ArtinPrimitiveRoots")
      "Spec") "Geometry") 0
  let n := n.str "ArtinPrimitiveRoots" |>.str "A1" |>.str "Spec" |>.str "volH3_sigmaFinite"
  return mkConst n

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem cpow_finset_prod {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i) (a : ℂ) :
    ((∏ i ∈ s, y i : ℝ) : ℂ) ^ a = ∏ i ∈ s, (y i : ℂ) ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hy i (by simp)) (by
          apply Finset.prod_nonneg
          intro j hj
          exact hy j (Finset.mem_insert_of_mem hj)) a, ih (by
            intro j hj
            exact hy j (Finset.mem_insert_of_mem hj))]

private theorem cpow_mul_positive {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (a : ℂ) :
    ((x * y : ℝ) : ℂ) ^ a = (x : ℂ) ^ a * (y : ℂ) ^ a := by
  simpa only [Complex.ofReal_mul] using Complex.mul_cpow_ofReal_nonneg hx hy a

/-- The product-space transform at the common basepoint is the product of the one-place transforms. -/
theorem smoothing_radial_power_at_base (k₀ : ℝ → ℝ) (a : ℂ) :
    smoothingOperator F k₀
      (fun w => ((normHeight F w : ℝ) : ℂ) ^ a)
      (fun _ => pt 0 1) = radialTransform F k₀ a := by
  letI : SigmaFinite volH3 := volH3_sigmaFiniteExact
  have hpow (w : X F) :
      ((normHeight F w : ℝ) : ℂ) ^ a =
        ∏ v : InfinitePlace F, (height (w v) : ℂ) ^ a := by
    unfold normHeight
    rw [cpow_finset_prod Finset.univ (fun v : InfinitePlace F => height (w v))
      (by
        intro v hv
        have hvpos : 0 < height (w v) := by
          rw [height_eq_hyperbolicHeight]
          exact OAI.CubicEisenstein.hyperbolicHeight_pos (w v)
        exact hvpos.le) a]
  have hfactor (w : X F) :
      radialKernel F k₀ (fun _ => pt 0 1) w * ((normHeight F w : ℝ) : ℂ) ^ a =
        ∏ v : InfinitePlace F,
          ((k₀ (ppi (pt 0 1) (w v)) : ℂ) * (height (w v) : ℂ) ^ a) := by
    rw [radialKernel, hpow, ← Finset.prod_mul_distrib]
  rw [smoothingOperator]
  simp_rw [hfactor]
  rw [(G3_volume (F := F)).2.2.2.2]
  change (∫ w : InfinitePlace F → H3,
    ∏ v : InfinitePlace F,
      ((k₀ (ppi (pt 0 1) (w v)) : ℝ) : ℂ) * (height (w v) : ℂ) ^ a
      ∂Measure.pi (fun _ : InfinitePlace F => volH3)) = _
  calc
    _ = ∏ v : InfinitePlace F,
        ∫ q : H3, ((k₀ (ppi (pt 0 1) q) : ℝ) : ℂ) * (height q : ℂ) ^ a ∂volH3 := by
      exact MeasureTheory.integral_fintype_prod_eq_prod
        (fun v q => ((k₀ (ppi (pt 0 1) q) : ℝ) : ℂ) * (height q : ℂ) ^ a)
    _ = radialTransform F k₀ a := by
      simp [radialTransform, radialTransform₀]


/-- Changing variables by a product isometry commutes with radial smoothing. -/
theorem smoothing_isometry_equivariant_of_Geometry (k₀ : ℝ → ℝ)
    (g : InfinitePlace F → SL(2, ℂ)) (f : X F → ℂ) (z : X F) :
    smoothingOperator F k₀ (fun x => f (actAtPlaces F g x)) z =
      smoothingOperator F k₀ f (actAtPlaces F g z) := by
  letI : TopologicalSpace (SL(2, ℂ)) := OAI.CubicEisenstein.complexSLTopology
  letI : TopologicalSpace H3 := by infer_instance
  letI : MeasurableSpace H3 := OAI.CubicEisenstein.hyperbolicMeasurableSpace
  letI : BorelSpace H3 := OAI.CubicEisenstein.hyperbolicBorelSpace
  letI : OpensMeasurableSpace H3 := BorelSpace.opensMeasurable
  let hppi := G6_ppi (F := F)
  let hvol := G3_volume (F := F)
  let gi : InfinitePlace F → SL(2, ℂ) := fun w => (g w)⁻¹
  have hgMeas : Measurable (actAtPlaces F g) := by
    rw [measurable_pi_iff]
    intro w
    change Measurable (fun x : X F => (g w) • x w)
    exact (OAI.CubicEisenstein.continuous_hyperbolic_action (g w)).measurable.comp
      (measurable_pi_apply w)
  have hgiMeas : Measurable (actAtPlaces F gi) := by
    rw [measurable_pi_iff]
    intro w
    change Measurable (fun x : X F => (gi w) • x w)
    exact (OAI.CubicEisenstein.continuous_hyperbolic_action (gi w)).measurable.comp
      (measurable_pi_apply w)
  have hcomp (x : X F) : actAtPlaces F gi (actAtPlaces F g x) = x := by
    funext w
    simp [actAtPlaces, gi]
  have hcomp' (x : X F) : actAtPlaces F g (actAtPlaces F gi x) = x := by
    funext w
    simp [actAtPlaces, gi]
  have hgEmb : MeasurableEmbedding (actAtPlaces F g) := by
    refine ⟨?_, hgMeas, ?_⟩
    · intro x y hxy
      funext w
      have hw : g w • x w = g w • y w := by
        simpa [actAtPlaces] using congrFun hxy w
      calc
        x w = (g w)⁻¹ • (g w • x w) := by simp
        _ = (g w)⁻¹ • (g w • y w) := by rw [hw]
        _ = y w := by simp
    · intro s hs
      have himage : actAtPlaces F g '' s = (actAtPlaces F gi) ⁻¹' s := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          change actAtPlaces F gi (actAtPlaces F g y) ∈ s
          rw [hcomp y]
          exact hy
        · intro hx
          refine ⟨actAtPlaces F gi x, hx, ?_⟩
          exact hcomp' x
      rw [himage]
      exact hgiMeas hs
  have hmap : Measure.map (actAtPlaces F g) (volX F) = volX F := hvol.1 g
  have hker (x : X F) :
      radialKernel F k₀ z (actAtPlaces F gi x) =
        radialKernel F k₀ (actAtPlaces F g z) x := by
    unfold radialKernel actAtPlaces
    apply Finset.prod_congr rfl
    intro w hw
    rw [← hppi.1 (g w) (z w) ((gi w) • x w)]
    simp [gi]
  let H : X F → ℂ := fun x => radialKernel F k₀ z (actAtPlaces F gi x) * f x
  have hchange :
      (∫ x, radialKernel F k₀ z x * f (actAtPlaces F g x) ∂volX F) =
        ∫ x, H x ∂volX F := by
    calc
      _ = ∫ x, H (actAtPlaces F g x) ∂volX F := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [H]
        rw [hcomp x]
      _ = ∫ x, H x ∂Measure.map (actAtPlaces F g) (volX F) :=
        (hgEmb.integral_map H).symm
      _ = ∫ x, H x ∂volX F := by rw [hmap]; rfl
  unfold smoothingOperator
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [] with x
  change radialKernel F k₀ z (actAtPlaces F gi x) * f x =
    radialKernel F k₀ (actAtPlaces F g z) x * f x
  rw [hker]

noncomputable def verticalScaleMatrix (x : ℂ) (y : ℝ) (hy : 0 < y) : SL(2, ℂ) :=
  OAI.CubicEisenstein.complexTranslation x *
    OAI.CubicEisenstein.complexDiagonal (Real.sqrt y : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne')

theorem verticalScale_pt (x : ℂ) (y : ℝ) (hy : 0 < y)
    (u : ℂ) (v : ℝ) (hv : 0 < v) :
    verticalScaleMatrix x y hy • pt u v = pt (x + y * u) (y * v) := by
  let d : ℂ := (Real.sqrt y : ℝ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hsq : d ^ 2 = (y : ℂ) := by
    dsimp [d]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hnorm : Complex.normSq d = y := by
    dsimp [d]
    simp [Complex.normSq_eq_norm_sq, Real.norm_of_nonneg (Real.sqrt_nonneg y),
      Real.sq_sqrt hy.le]
  rw [pt_eq_upperPoint u v hv,
    pt_eq_upperPoint (x + y * u) (y * v) (mul_pos hy hv)]
  change (OAI.CubicEisenstein.complexTranslation x *
      OAI.CubicEisenstein.complexDiagonal d hd) •
        OAI.CubicEisenstein.upperPoint u v hv = _
  rw [mul_smul, OAI.CubicEisenstein.complexDiagonal_action,
    OAI.CubicEisenstein.complexTranslation_action, hsq]
  apply OAI.CubicEisenstein.upperPoint_congr
  · ring
  · calc
      Complex.normSq d * v = y * v := by rw [hnorm]

private theorem verticalScale_height (x : ℂ) (y : ℝ) (hy : 0 < y)
    (z : H3) :
    height (verticalScaleMatrix x y hy • z) = y * height z := by
  have hz : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  rw [← pt_horiz_height z,
    verticalScale_pt x y hy (horiz z) (height z) hz]
  rw [height_pt _ _ (mul_pos hy hz), height_pt _ _ hz]

private theorem normHeight_pos (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

/-- Radial powers are eigenfunctions of smoothing, first at the basepoint and then by isometry covariance. -/
theorem smoothing_radial_power (k₀ : ℝ → ℝ) (a : ℂ) (z : X F) :
    smoothingOperator F k₀ (fun w => ((normHeight F w : ℝ) : ℂ) ^ a) z =
      radialTransform F k₀ a * ((normHeight F z : ℝ) : ℂ) ^ a := by
  let o : X F := fun _ => pt 0 1
  let b : InfinitePlace F → SL(2, ℂ) := fun w =>
    verticalScaleMatrix (horiz (z w)) (height (z w))
      (by
        rw [height_eq_hyperbolicHeight]
        exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w))
  have hact : actAtPlaces F b o = z := by
    funext w
    dsimp [actAtPlaces, b, o]
    have hy : 0 < height (z w) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    rw [verticalScale_pt (horiz (z w)) (height (z w)) hy 0 1 (by norm_num)]
    simpa using (pt_horiz_height (z w))
  have hheight (w : X F) :
      normHeight F (actAtPlaces F b w) = normHeight F z * normHeight F w := by
    change (∏ v : InfinitePlace F, height (b v • w v)) =
      (∏ v : InfinitePlace F, height (z v)) * ∏ v : InfinitePlace F, height (w v)
    calc
      _ = ∏ v : InfinitePlace F, height (z v) * height (w v) := by
        apply Finset.prod_congr rfl
        intro v hv
        dsimp [b]
        exact verticalScale_height (horiz (z v)) (height (z v))
          (by
            rw [height_eq_hyperbolicHeight]
            exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)) (w v)
      _ = _ := Finset.prod_mul_distrib
  let f : X F → ℂ := fun w => ((normHeight F w : ℝ) : ℂ) ^ a
  have hcov := smoothing_isometry_equivariant_of_Geometry k₀ b f o
  have hscale (w : X F) :
      f (actAtPlaces F b w) = ((normHeight F z : ℝ) : ℂ) ^ a * f w := by
    dsimp [f]
    rw [hheight]
    exact cpow_mul_positive (normHeight_pos z).le (normHeight_pos w).le a
  have hsm : smoothingOperator F k₀ (fun w => f (actAtPlaces F b w)) o =
      ((normHeight F z : ℝ) : ℂ) ^ a * smoothingOperator F k₀ f o := by
    unfold smoothingOperator
    calc
      (∫ w, radialKernel F k₀ o w * f (actAtPlaces F b w) ∂volX F) =
          ∫ w, ((normHeight F z : ℝ) : ℂ) ^ a *
            (radialKernel F k₀ o w * f w) ∂volX F := by
        apply integral_congr_ae
        filter_upwards [] with w
        rw [hscale]
        ring
      _ = ((normHeight F z : ℝ) : ℂ) ^ a *
          ∫ w, radialKernel F k₀ o w * f w ∂volX F := by
        rw [integral_const_mul]
  calc
    smoothingOperator F k₀ f z = smoothingOperator F k₀ f (actAtPlaces F b o) := by
      rw [hact]
    _ = smoothingOperator F k₀ (fun w => f (actAtPlaces F b w)) o := hcov.symm
    _ = ((normHeight F z : ℝ) : ℂ) ^ a * smoothingOperator F k₀ f o := hsm
    _ = radialTransform F k₀ a * ((normHeight F z : ℝ) : ℂ) ^ a := by
      rw [smoothing_radial_power_at_base]
      ring

end ArtinPrimitiveRoots.Proofs.spec_continue_p
