import ArtinPrimitiveRoots.Spec.Geometry
import ArtinPrimitiveRoots.Spec.EisensteinExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.All
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.Equivariance
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Lean

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology
open Lean Elab Term

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

elab "volH3FiniteOnCompactsExact" : term => do
  let n := Name.num (Name.str (Name.str (Name.str `_private "ArtinPrimitiveRoots")
      "Spec") "Geometry") 0
  let n := n.str "ArtinPrimitiveRoots" |>.str "A1" |>.str "Spec" |>.str "volH3_finiteOnCompacts"
  return mkConst n

elab "volH3OpenPosMeasureExact" : term => do
  let n := Name.num (Name.str (Name.str (Name.str `_private "ArtinPrimitiveRoots")
      "Spec") "Geometry") 0
  let n := n.str "ArtinPrimitiveRoots" |>.str "A1" |>.str "Spec" |>.str "volH3_isOpenPosMeasure"
  return mkConst n

local instance : TopologicalSpace (SL(2, ℂ)) := OAI.CubicEisenstein.complexSLTopology
local instance : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace :=
  QuotientGroup.instTopologicalSpace OAI.CubicEisenstein.compactSubgroup
local instance : TopologicalSpace H3 := H3_eq_OAI.symm ▸ inferInstance
local instance : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
  borel OAI.CubicEisenstein.HyperbolicSpace
local instance : BorelSpace OAI.CubicEisenstein.HyperbolicSpace := ⟨rfl⟩
private theorem opensMeasurableH3Exact :
    OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := by
  exact BorelSpace.opensMeasurable
local instance : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace :=
  opensMeasurableH3Exact
local instance : T2Space OAI.CubicEisenstein.UpperCoordinates := inferInstance
local instance : T2Space OAI.CubicEisenstein.HyperbolicSpace :=
  OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
local instance : IsFiniteMeasureOnCompacts volH3 := volH3FiniteOnCompactsExact
local instance : Measure.IsOpenPosMeasure volH3 := volH3OpenPosMeasureExact

open OAI.CubicEisenstein

private def h3OAIHomeomorph : H3 ≃ₜ OAI.CubicEisenstein.HyperbolicSpace where
  toEquiv := Equiv.cast H3_eq_OAI
  continuous_toFun := by
    cases H3_eq_OAI
    exact continuous_id
  continuous_invFun := by
    cases H3_eq_OAI
    exact continuous_id

private theorem ppi_h3OAI (z z' : H3) :
    ppi (h3OAIHomeomorph z) (h3OAIHomeomorph z') = ppi z z' := by
  cases H3_eq_OAI
  rfl

private theorem ppi_h3OAI_base (z : H3) :
    ppi (pt 0 1) (h3OAIHomeomorph z) = ppi (pt 0 1) z := by
  cases H3_eq_OAI
  rfl

theorem ppi_small_sublevel_compact (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] :
    ∃ W : Set OAI.CubicEisenstein.HyperbolicSpace, IsCompact W ∧
      ∀ z : OAI.CubicEisenstein.HyperbolicSpace,
        ppi (pt 0 1) z ≤ 1 + 1 / 100 → z ∈ W := by
  let ρ : ℝ := 1 / 100
  let R : ℝ := Real.arcosh (1 + ρ)
  let L : ℝ := Real.sqrt (2 * ρ + ρ ^ 2)
  let ylo : ℝ := Real.exp (-R)
  let yhi : ℝ := Real.exp R
  let box : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (-L) L ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc ylo yhi)
  let φ : ℝ × (ℝ × ℝ) → ℂ × ℝ :=
    fun q => ((q.1 : ℂ) + Complex.I * (q.2.1 : ℂ), q.2.2)
  let B : Set (ℂ × ℝ) := φ '' box
  let C : Set UpperCoordinates := {q | q.1 ∈ B}
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  have hR : 0 ≤ R := Real.arcosh_nonneg (by norm_num [ρ])
  have hylo : 0 < ylo := Real.exp_pos _
  have hbox : IsCompact box := by
    dsimp [box]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hφ : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hB : IsCompact B := by
    dsimp [B]
    exact hbox.image hφ
  have hBpos : B ⊆ {q : ℂ × ℝ | 0 < q.2} := by
    rintro q ⟨r, hr, rfl⟩
    have hy : ylo ≤ r.2.2 := hr.2.2.1
    exact lt_of_lt_of_le hylo hy
  have hImage : (Subtype.val '' C : Set (ℂ × ℝ)) = B := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      exact ⟨⟨q, hBpos hq⟩, hq, rfl⟩
  have hC : IsCompact C := by
    rw [Subtype.isCompact_iff, hImage]
    exact hB
  let W : Set OAI.CubicEisenstein.HyperbolicSpace := upperCoordinatesHomeomorph '' C
  have hW : IsCompact W := hC.image upperCoordinatesHomeomorph.continuous
  refine ⟨W, hW, ?_⟩
  intro z hz
  have hbounds := (G6_ppi (F := F)).2.2.2.1 ρ hρ z hz
  rcases hbounds with ⟨hlog, hhor⟩
  have hypos : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_pos z
  have hlog' := abs_le.mp hlog
  have hylo' : ylo ≤ height z := by
    dsimp [ylo]
    calc
      Real.exp (-R) ≤ Real.exp (Real.log (height z)) := Real.exp_le_exp.mpr hlog'.1
      _ = height z := Real.exp_log hypos
  have hyhi' : height z ≤ yhi := by
    dsimp [yhi]
    calc
      height z = Real.exp (Real.log (height z)) := (Real.exp_log hypos).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog'.2
  have hre : |(horiz z).re| ≤ L := (Complex.abs_re_le_norm _).trans hhor
  have him : |(horiz z).im| ≤ L := (Complex.abs_im_le_norm _).trans hhor
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  let q : UpperCoordinates := hyperbolicCoordinates z
  have hq1 : q.1.1 = horiz z := by
    change hyperbolicHorizontal z = horiz z
    exact (congrFun horiz_eq_hyperbolicHorizontal z).symm
  have hq2 : q.1.2 = height z := by
    change hyperbolicHeight z = height z
    exact (congrFun height_eq_hyperbolicHeight z).symm
  have hqval : (q : ℂ × ℝ) = (horiz z, height z) := Prod.ext hq1 hq2
  have hqB : q.1 ∈ B := by
    change (q : ℂ × ℝ) ∈ φ '' box
    rw [hqval]
    refine ⟨((horiz z).re, ((horiz z).im, height z)), ?_, ?_⟩
    · change (-L ≤ (horiz z).re ∧ (horiz z).re ≤ L) ∧
        ((-L ≤ (horiz z).im ∧ (horiz z).im ≤ L) ∧
          (ylo ≤ height z ∧ height z ≤ yhi))
      exact ⟨⟨by dsimp [L]; linarith [hre'.1], by dsimp [L]; linarith [hre'.2]⟩,
        ⟨⟨by dsimp [L]; linarith [him'.1], by dsimp [L]; linarith [him'.2]⟩,
          ⟨hylo', hyhi'⟩⟩⟩
    · apply Prod.ext
      · change ((horiz z).re : ℂ) + Complex.I * ((horiz z).im : ℂ) = horiz z
        apply Complex.ext <;> simp
      · rfl
  have hqC : q ∈ C := hqB
  have hzq : upperCoordinatesHomeomorph q = z := by
    change upperCoordinatesHomeomorph (hyperbolicCoordinates z) = z
    exact upperCoordinates_right_inverse z
  exact ⟨q, hqC, hzq⟩

private theorem h3OAI_pt (x : ℂ) (y : ℝ) (hy : 0 < y) :
    h3OAIHomeomorph (pt x y) = OAI.CubicEisenstein.upperPoint x y hy := by
  cases H3_eq_OAI
  exact pt_eq_upperPoint x y hy

private theorem h3OAI_action (g : SL(2, ℂ)) (z : H3) :
    h3OAIHomeomorph (g • z) = g • h3OAIHomeomorph z := by
  cases H3_eq_OAI
  rfl

private theorem continuous_hyperbolic_action_H3 (g : SL(2, ℂ)) :
    Continuous (fun z : H3 => g • z) := by
  have hfun : (fun z : H3 => g • z) =
      fun z => h3OAIHomeomorph.symm (g • h3OAIHomeomorph z) := by
    funext z
    rw [← h3OAI_action g z]
    simp
  rw [hfun]
  exact h3OAIHomeomorph.continuous_invFun.comp
    ((OAI.CubicEisenstein.continuous_hyperbolic_action g).comp
      h3OAIHomeomorph.continuous_toFun)

private theorem ppi_small_sublevel_compact_H3 (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] :
    ∃ W : Set H3, IsCompact W ∧
      ∀ z : H3, ppi (pt 0 1) z ≤ 1 + 1 / 100 → z ∈ W := by
  obtain ⟨W₀, hW₀c, hW₀⟩ := ppi_small_sublevel_compact F
  let W : Set H3 := h3OAIHomeomorph.symm '' W₀
  have hWc : IsCompact W := hW₀c.image h3OAIHomeomorph.continuous_invFun
  refine ⟨W, hWc, ?_⟩
  intro z hz
  have hbase : ppi (pt 0 1) (h3OAIHomeomorph z) = ppi (pt 0 1) z :=
    ppi_h3OAI_base z
  refine ⟨h3OAIHomeomorph z, hW₀ (h3OAIHomeomorph z) ?_, ?_⟩
  · rw [hbase]
    exact hz
  · simp

theorem ppi_small_sublevel_compact_at (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (p : H3) :
    ∃ W : Set H3, IsCompact W ∧
      ∀ z : H3, ppi p z ≤ 1 + 1 / 100 → z ∈ W := by
  obtain ⟨W₀, hW₀c, hW₀⟩ := ppi_small_sublevel_compact_H3 F
  have hp : 0 < height p := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos p
  let g : SL(2, ℂ) := verticalScaleMatrix (horiz p) (height p) hp
  have hgp : g • pt 0 1 = p := by
    calc
      g • pt 0 1 = pt (horiz p) (height p) := by
        simpa [g] using verticalScale_pt (horiz p) (height p) hp 0 1 (by norm_num)
      _ = p := pt_horiz_height p
  let W : Set H3 := (fun z : H3 => g • z) '' W₀
  refine ⟨W, hW₀c.image (continuous_hyperbolic_action_H3 g), ?_⟩
  intro z hz
  have hbase : ppi (pt 0 1) (g⁻¹ • z) = ppi p z := by
    have h := (G6_ppi (F := F)).1 g (pt 0 1) (g⁻¹ • z)
    have hinv : g • (g⁻¹ • z) = z := by
      calc
        g • (g⁻¹ • z) = (g * g⁻¹) • z := (mul_smul g g⁻¹ z).symm
        _ = z := by simp
    have h' : ppi (g • pt 0 1) z = ppi (pt 0 1) (g⁻¹ • z) := by
      simpa [hinv] using h
    have h'gp : ppi (g • pt 0 1) z = ppi p z := congrArg (fun q => ppi q z) hgp
    exact h'.symm.trans h'gp
  refine ⟨g⁻¹ • z, hW₀ (g⁻¹ • z) ?_, ?_⟩
  · rw [hbase]
    exact hz
  · calc
      g • (g⁻¹ • z) = (g * g⁻¹) • z := (mul_smul g g⁻¹ z).symm
      _ = z := by simp

theorem radialKernel_support_compact (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (k₀ : ℝ → ℝ)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100)) (z : X F) :
    ∃ K : Set (X F), IsCompact K ∧
      z ∈ K ∧
      ∀ w, radialKernel F k₀ z w ≠ 0 → w ∈ K := by
  classical
  have hballs (v : InfinitePlace F) : ∃ W : Set H3, IsCompact W ∧
      ∀ q, ppi (z v) q ≤ 1 + 1 / 100 → q ∈ W :=
    ppi_small_sublevel_compact_at F (z v)
  choose W hWcompact hWcontains using hballs
  let K : Set (X F) := Set.pi Set.univ W
  refine ⟨K, ?_, ?_, ?_⟩
  · exact isCompact_univ_pi hWcompact
  · change ∀ v ∈ (Set.univ : Set (InfinitePlace F)), z v ∈ W v
    intro v hv
    apply hWcontains v
    have hself : ppi (z v) (z v) = 1 :=
      ((G6_ppi (F := F)).2.2.1 (z v) (z v)).2.mpr rfl
    rw [hself]
    norm_num
  · intro w hw
    change ∀ v ∈ (Set.univ : Set (InfinitePlace F)), w v ∈ W v
    intro v hv
    have hk : k₀ (ppi (z v) (w v)) ≠ 0 := by
      intro hk0
      have hfactor : (k₀ (ppi (z v) (w v)) : ℂ) = 0 := by exact_mod_cast hk0
      apply hw
      simpa [radialKernel] using
        (Finset.prod_eq_zero_iff.mpr ⟨v, Finset.mem_univ v, hfactor⟩)
    apply hWcontains v
    exact (hkSupport hk).2

def radialTransformIntegrand (k₀ : ℝ → ℝ) (a : ℂ) (z : OAI.CubicEisenstein.HyperbolicSpace) : ℂ :=
  (k₀ (ppi (pt 0 1) z) : ℂ) * (height z : ℂ) ^ a

theorem radialTransformIntegrand_continuous (k₀ : ℝ → ℝ)
    [NormedAddCommGroup ℂ]
    (hkSmooth : ContDiff ℝ ∞ k₀) (a : ℂ) :
    Continuous (radialTransformIntegrand k₀ a) := by
  have hh : Continuous height := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_continuous
  have hx : Continuous horiz := by
    rw [horiz_eq_hyperbolicHorizontal]
    exact hyperbolicHorizontal_continuous
  have hpos (z : OAI.CubicEisenstein.HyperbolicSpace) : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_pos z
  have hppi : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => ppi (pt 0 1) z) := by
    have hformula (z : OAI.CubicEisenstein.HyperbolicSpace) : ppi (pt 0 1) z =
        (Complex.normSq (horiz z) + 1 + height z ^ 2) / (2 * height z) := by
      simp only [ppi, horiz_pt 0 1 (by norm_num), height_pt 0 1 (by norm_num)]
      simp
    have hn : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => Complex.normSq (horiz z) + 1 + height z ^ 2) := by
      fun_prop
    have hd : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => 2 * height z) := by fun_prop
    have hq : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace =>
        (Complex.normSq (horiz z) + 1 + height z ^ 2) / (2 * height z)) :=
      hn.div hd (fun z => by have := hpos z; positivity)
    exact hq.congr fun z => (hformula z).symm
  have hk : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => (k₀ (ppi (pt 0 1) z) : ℂ)) :=
    Complex.continuous_ofReal.comp (hkSmooth.continuous.comp hppi)
  have hy : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => (height z : ℂ)) :=
    Complex.continuous_ofReal.comp hh
  have hcpow : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => (height z : ℂ) ^ a) := by
    apply hy.cpow continuous_const
    intro z
    exact Complex.ofReal_mem_slitPlane.mpr (hpos z)
  change Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace =>
    (k₀ (ppi (pt 0 1) z) : ℂ) * (height z : ℂ) ^ a)
  exact hk.mul hcpow

private theorem radialTransformIntegrand_zero_outside {k₀ : ℝ → ℝ}
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (a : ℂ) {W : Set OAI.CubicEisenstein.HyperbolicSpace}
    (hW : ∀ z, ppi (pt 0 1) z ≤ 1 + 1 / 100 → z ∈ W)
    {z : OAI.CubicEisenstein.HyperbolicSpace} (hz : z ∉ W) : radialTransformIntegrand k₀ a z = 0 := by
  have hp : 1 + 1 / 100 < ppi (pt 0 1) z := by
    by_contra h
    exact hz (hW z (le_of_not_gt h))
  have hk : k₀ (ppi (pt 0 1) z) = 0 := by
    by_contra hne
    have hs := hkSupport hne
    exact (not_lt_of_ge hs.2) hp
  simp [radialTransformIntegrand, hk]

private theorem radialKernel_positive_interior (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (hkNonneg : ∀ t, 0 ≤ k₀ t)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (hkNonzero : ∃ t, k₀ t ≠ 0) :
    ∃ t, 1 < t ∧ t < 1 + 1 / 100 ∧ 0 < k₀ t := by
  obtain ⟨t, ht⟩ := hkNonzero
  have hkt : 0 < k₀ t := by
    rcases lt_or_eq_of_le (hkNonneg t) with hpos | hzero
    · exact hpos
    · exact (ht hzero.symm).elim
  have hsupport := hkSupport ht
  have hmem : k₀ ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 t :=
    (isOpen_Ioi.preimage hkSmooth.continuous).mem_nhds hkt
  rcases Metric.mem_nhds_iff.mp hmem with ⟨δ, hδ, hball⟩
  have hlow : 1 < t := by
    by_contra hnot
    have htEq : t = 1 := le_antisymm (le_of_not_gt hnot) hsupport.1
    subst t
    let u : ℝ := 1 - δ / 2
    have hdist : dist u 1 < δ := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      dsimp [u]
      rw [abs_of_nonpos (by linarith : 1 - δ / 2 - 1 ≤ 0)]
      linarith
    have hu := hball (Metric.mem_ball.mpr hdist)
    have huSupport := hkSupport (ne_of_gt hu)
    dsimp [u] at huSupport
    have hδ2 : 0 < δ / 2 := by positivity
    have hlt : 1 - δ / 2 < 1 := by linarith
    exact (not_le_of_gt hlt) huSupport.1
  have hupp : t < 1 + 1 / 100 := by
    by_contra hnot
    have htEq : t = 1 + 1 / 100 := le_antisymm hsupport.2 (le_of_not_gt hnot)
    subst t
    let u : ℝ := (1 + 1 / 100) + δ / 2
    have hdist : dist u (1 + 1 / 100) < δ := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      dsimp [u]
      rw [abs_of_nonneg (by nlinarith [hδ])]
      linarith
    have hu := hball (Metric.mem_ball.mpr hdist)
    have huSupport := hkSupport (ne_of_gt hu)
    dsimp [u] at huSupport
    have hδ2 : 0 < δ / 2 := by positivity
    have hgt : 1 + 1 / 100 < 1 + 1 / 100 + δ / 2 := by linarith
    exact (not_le_of_gt hgt) huSupport.2
  exact ⟨t, hlow, hupp, hkt⟩

private theorem arcosh_101_lt_one_seven : Real.arcosh (1 + 1 / 100) < 1 / 7 := by
  have hsinh : (1 / 14 : ℝ) ≤ Real.sinh (1 / 14) :=
    Real.self_le_sinh_iff.mpr (by norm_num)
  have hsinhSq : (1 / 14 : ℝ) ^ 2 ≤ Real.sinh (1 / 14) ^ 2 := by
    nlinarith [sq_nonneg (Real.sinh (1 / 14) - (1 / 14 : ℝ))]
  have hcosh : 1 + 1 / 98 ≤ Real.cosh (1 / 7) := by
    rw [show (1 / 7 : ℝ) = 2 * (1 / 14 : ℝ) by norm_num,
      Real.cosh_two_mul, Real.cosh_sq']
    nlinarith [hsinhSq]
  have hnum : 1 + 1 / 100 < Real.cosh (1 / 7) := by
    calc
      1 + 1 / 100 < 1 + 1 / 98 := by norm_num
      _ ≤ Real.cosh (1 / 7) := hcosh
  rw [← Real.arcosh_cosh (by norm_num : 0 ≤ (1 / 7 : ℝ))]
  exact (Real.arcosh_lt_arcosh (by norm_num) (Real.cosh_pos _)).2 hnum

private theorem cpow_real_part_of_pos {y : ℝ} (hy : 0 < y) (a : ℂ) :
    ((y : ℂ) ^ a).re = Real.exp (a.re * Real.log y) * Real.cos (a.im * Real.log y) := by
  have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_def_of_ne_zero hyne, ← Complex.ofReal_log hy.le]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_comm]


theorem radialTransformIntegrand_integrable (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (a : ℂ) : Integrable (radialTransformIntegrand k₀ a) volH3 := by
  letI : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := opensMeasurableH3Exact
  obtain ⟨W, hWc, hW⟩ := ppi_small_sublevel_compact F
  have hWmeas : MeasurableSet W := by
    letI : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := opensMeasurableH3Exact
    exact hWc.measurableSet
  have hOn : IntegrableOn (radialTransformIntegrand k₀ a) W volH3 := by
    letI : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := opensMeasurableH3Exact
    exact @ContinuousOn.integrableOn_compact' OAI.CubicEisenstein.HyperbolicSpace ℂ
      (inferInstance : MeasurableSpace OAI.CubicEisenstein.HyperbolicSpace)
      (inferInstance : TopologicalSpace OAI.CubicEisenstein.HyperbolicSpace)
      (inferInstance : NormedAddCommGroup ℂ)
      volH3 opensMeasurableH3Exact W (radialTransformIntegrand k₀ a)
      (inferInstance : IsFiniteMeasureOnCompacts volH3)
      hWc hWmeas (radialTransformIntegrand_continuous k₀ hkSmooth a).continuousOn
  have hOn' : Integrable (Set.indicator W (radialTransformIntegrand k₀ a)) volH3 :=
    (integrable_indicator_iff hWmeas).2 hOn
  have hEq : Set.indicator W (radialTransformIntegrand k₀ a) =
      radialTransformIntegrand k₀ a := by
    funext z
    by_cases hz : z ∈ W
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz,
        radialTransformIntegrand_zero_outside hkSupport a hW hz]
  rw [← hEq]
  exact hOn'

theorem radialTransform₀_realPart_pos (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (hkNonneg : ∀ t, 0 ≤ k₀ t)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (hkNonzero : ∃ t, k₀ t ≠ 0) (s : ℂ) (hs : ‖s‖ ≤ 5) :
    0 < (radialTransform₀ k₀ (1 + 2 * s)).re := by
  let a : ℂ := 1 + 2 * s
  have hρ : 0 ≤ (1 / 100 : ℝ) := by norm_num
  have hR : Real.arcosh (1 + 1 / 100) < 1 / 7 := arcosh_101_lt_one_seven
  have hima : |a.im| ≤ 10 := by
    have him : |s.im| ≤ 5 := (Complex.abs_im_le_norm s).trans hs
    calc
      |a.im| = 2 * |s.im| := by simp [a, Complex.add_im, Complex.mul_im, abs_mul]
      _ ≤ 10 := by nlinarith
  have hInt : Integrable (radialTransformIntegrand k₀ a) volH3 := by
    exact radialTransformIntegrand_integrable F k₀ hkSmooth hkSupport a
  let reKernel : OAI.CubicEisenstein.HyperbolicSpace → ℝ :=
    fun z => (radialTransformIntegrand k₀ a z).re
  have hReCont : Continuous reKernel := by
    dsimp [reKernel]
    exact Complex.continuous_re.comp (radialTransformIntegrand_continuous k₀ hkSmooth a)
  have hReInt : Integrable reKernel volH3 := by
    dsimp [reKernel]
    exact Complex.reCLM.integrable_comp hInt
  have hReNonneg : 0 ≤ reKernel := by
    intro z
    dsimp [reKernel, a]
    by_cases hk : k₀ (ppi (pt 0 1) z) = 0
    · simp [radialTransformIntegrand, hk]
    · have hsupport := hkSupport hk
      have hzpos : 0 < height z := by
        rw [height_eq_hyperbolicHeight]
        exact OAI.CubicEisenstein.hyperbolicHeight_pos z
      have hBounds := (G6_ppi (F := F)).2.2.2.1 (1 / 100) hρ z hsupport.2
      have hphase : |(1 + 2 * (s:ℂ)).im * Real.log (height z)| < Real.pi / 2 := by
        calc
          |(1 + 2 * (s:ℂ)).im * Real.log (height z)| =
              |(1 + 2 * s).im| * |Real.log (height z)| := abs_mul _ _
          _ ≤ 10 * Real.arcosh (1 + 1 / 100) := by
            calc
              |(1 + 2 * s).im| * |Real.log (height z)| ≤
                  10 * |Real.log (height z)| :=
                mul_le_mul_of_nonneg_right hima (abs_nonneg _)
              _ ≤ 10 * Real.arcosh (1 + 1 / 100) :=
                mul_le_mul_of_nonneg_left hBounds.1 (by norm_num)
          _ < 10 / 7 := by nlinarith
          _ < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
      have hcos : 0 < Real.cos ((1 + 2 * (s:ℂ)).im * Real.log (height z)) := by
        have h := abs_lt.mp hphase
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hpow := cpow_real_part_of_pos hzpos (1 + 2 * s)
      rw [radialTransformIntegrand, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add]
      rw [hpow]
      simpa using mul_nonneg (hkNonneg _) (mul_nonneg (Real.exp_pos _).le hcos.le)
  obtain ⟨t, htlo, htup, hkt⟩ :=
    radialKernel_positive_interior k₀ hkSmooth hkNonneg hkSupport hkNonzero
  let x : ℂ := ((Real.sqrt (2 * (t - 1)) : ℝ) : ℂ)
  let z₀ : OAI.CubicEisenstein.HyperbolicSpace := pt x 1
  have hxarg : 0 ≤ 2 * (t - 1) := by nlinarith
  have htm1 : 0 ≤ t - 1 := by linarith
  have hxnorm : Complex.normSq x = 2 * (t - 1) := by
    rw [Complex.normSq_ofReal]
    simpa only [pow_two] using Real.sq_sqrt hxarg
  have hppi : ppi (pt 0 1) z₀ = t := by
    dsimp [z₀]
    have hform : ppi (pt 0 1) (pt x 1) = (Complex.normSq x + 2) / 2 := by
      simp only [ppi, horiz_pt 0 1 (by norm_num), horiz_pt x 1 (by norm_num),
        height_pt 0 1 (by norm_num), height_pt x 1 (by norm_num)]
      have hneg : Complex.normSq (-x) = Complex.normSq x := by simp
      simp [hneg]
      ring
    rw [hform, hxnorm]
    ring
  have hAt : reKernel z₀ > 0 := by
    dsimp [reKernel, radialTransformIntegrand, z₀]
    rw [hppi, height_pt x 1 (by norm_num)]
    simp
    exact hkt
  have hIntegralPos : 0 < ∫ z, reKernel z ∂volH3 :=
    integral_pos_of_integrable_nonneg_nonzero hReCont hReInt hReNonneg hAt.ne'
  have hReEq : (radialTransform₀ k₀ (1 + 2 * s)).re =
      ∫ z, reKernel z ∂volH3 := by
    cases H3_eq_OAI
    unfold radialTransform₀ reKernel
    convert (Complex.reCLM.integral_comp_comm hInt).symm using 1
    all_goals first | rfl | simp [radialTransformIntegrand, Complex.reCLM_apply]
  rw [hReEq]
  exact hIntegralPos

def radialTransformDerivativeIntegrand (k₀ : ℝ → ℝ) (a : ℂ) (z : OAI.CubicEisenstein.HyperbolicSpace) : ℂ :=
  (k₀ (ppi (pt 0 1) z) : ℂ) *
    ((height z : ℂ) ^ a * Complex.log (height z : ℂ))

theorem radialTransformIntegrand_hasDerivAt
    (k₀ : ℝ → ℝ) (z : OAI.CubicEisenstein.HyperbolicSpace) (a : ℂ) :
    HasDerivAt (fun w => radialTransformIntegrand k₀ w z)
      (radialTransformDerivativeIntegrand k₀ a z) a := by
  have hy : 0 < height z := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_pos z
  have hbase : (height z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpow :=
    (Complex.hasStrictDerivAt_const_cpow (x := (height z : ℂ)) (y := a) (Or.inl hbase)).hasDerivAt
  simpa [radialTransformIntegrand, radialTransformDerivativeIntegrand] using
    hpow.const_mul (k₀ (ppi (pt 0 1) z) : ℂ)

theorem radialTransformDerivativeIntegrand_continuous (k₀ : ℝ → ℝ)
    [NormedAddCommGroup ℂ]
    (hkSmooth : ContDiff ℝ ∞ k₀) (a : ℂ) :
    Continuous (radialTransformDerivativeIntegrand k₀ a) := by
  have hbase := radialTransformIntegrand_continuous k₀ hkSmooth a
  have hh : Continuous height := by
    rw [height_eq_hyperbolicHeight]
    exact hyperbolicHeight_continuous
  have hy : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => (height z : ℂ)) := Complex.continuous_ofReal.comp hh
  have hpos (z : OAI.CubicEisenstein.HyperbolicSpace) : (height z : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (by
      rw [height_eq_hyperbolicHeight]
      exact hyperbolicHeight_pos z)
  have hlog : Continuous (fun z : OAI.CubicEisenstein.HyperbolicSpace => Complex.log (height z : ℂ)) := hy.clog hpos
  have hEq : radialTransformDerivativeIntegrand k₀ a =
      fun z => radialTransformIntegrand k₀ a z * Complex.log (height z : ℂ) := by
    funext z
    simp [radialTransformDerivativeIntegrand, radialTransformIntegrand, mul_assoc]
  exact hEq ▸ hbase.mul hlog

theorem radialTransform₀_differentiableAt (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (a₀ : ℂ) : DifferentiableAt ℂ (radialTransform₀ k₀) a₀ := by
  letI semiringModule : Module ℂ ℂ := Semiring.toModule
  letI semiringNormedSpace : NormedSpace ℂ ℂ := NormedSpace.mk (fun a b => by
    simpa [Semiring.toModule] using (norm_mul_le a b : ‖a * b‖ ≤ ‖a‖ * ‖b‖))
  letI : OpensMeasurableSpace OAI.CubicEisenstein.HyperbolicSpace := opensMeasurableH3Exact
  let ρ : ℝ := 1 / 100
  let R : ℝ := Real.arcosh (1 + ρ)
  let E : ℝ := Real.exp ((|a₀.re| + 1) * R)
  let C : ℝ := E * R
  let bound : OAI.CubicEisenstein.HyperbolicSpace → ℝ := fun z => C * ‖radialTransformIntegrand k₀ 0 z‖
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  have hR : 0 ≤ R := Real.arcosh_nonneg (by norm_num [ρ])
  have hbaseInt : Integrable (radialTransformIntegrand k₀ 0) volH3 :=
    radialTransformIntegrand_integrable F k₀ hkSmooth hkSupport 0
  have hboundInt : Integrable bound volH3 := by
    dsimp [bound]
    simpa [mul_comm] using hbaseInt.norm.const_mul C
  have hFmeas : ∀ᶠ s in 𝓝 a₀,
      AEStronglyMeasurable (radialTransformIntegrand k₀ s) volH3 := by
    filter_upwards [] with s
    exact (radialTransformIntegrand_continuous k₀ hkSmooth s).aestronglyMeasurable
  have hFint : Integrable (radialTransformIntegrand k₀ a₀) volH3 :=
    radialTransformIntegrand_integrable F k₀ hkSmooth hkSupport a₀
  have hFprimeMeas : AEStronglyMeasurable
      (radialTransformDerivativeIntegrand k₀ a₀) volH3 :=
    (radialTransformDerivativeIntegrand_continuous k₀ hkSmooth a₀).aestronglyMeasurable
  have hBound : ∀ᵐ z ∂volH3, ∀ s ∈ Metric.ball a₀ 1,
      ‖radialTransformDerivativeIntegrand k₀ s z‖ ≤ bound z := by
    filter_upwards [] with z
    intro s hs
    by_cases hk : k₀ (ppi (pt 0 1) z) = 0
    · simp [radialTransformDerivativeIntegrand, radialTransformIntegrand, bound, hk]
    · have hsupport := hkSupport hk
      have hparam : |s.re| ≤ |a₀.re| + 1 := by
        have hdist : ‖s - a₀‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hs
        have hre : s.re = a₀.re + (s - a₀).re := by simp
        rw [hre]
        calc
          |a₀.re + (s - a₀).re| ≤ |a₀.re| + |(s - a₀).re| := abs_add_le _ _
          _ ≤ |a₀.re| + ‖s - a₀‖ := by gcongr; exact Complex.abs_re_le_norm _
          _ ≤ |a₀.re| + 1 := by linarith
      have hypos : 0 < height z := by
        rw [height_eq_hyperbolicHeight]
        exact OAI.CubicEisenstein.hyperbolicHeight_pos z
      have hBounds := (G6_ppi (F := F)).2.2.2.1 ρ hρ z hsupport.2
      have hlog : |Real.log (height z)| ≤ R := hBounds.1
      have hpow : ‖(height z : ℂ) ^ s‖ ≤ E := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos,
          Real.rpow_def_of_pos hypos]
        apply Real.exp_le_exp.mpr
        calc
          Real.log (height z) * s.re ≤ |Real.log (height z) * s.re| := le_abs_self _
          _ = |Real.log (height z)| * |s.re| := abs_mul _ _
          _ = |s.re| * |Real.log (height z)| := by ring
          _ ≤ (|a₀.re| + 1) * R := by
            calc
              |s.re| * |Real.log (height z)| ≤
                  (|a₀.re| + 1) * |Real.log (height z)| :=
                mul_le_mul_of_nonneg_right hparam (abs_nonneg _)
              _ ≤ (|a₀.re| + 1) * R :=
                mul_le_mul_of_nonneg_left hlog (by positivity)
      have hlognorm : ‖Complex.log (height z : ℂ)‖ ≤ R := by
        rw [← Complex.ofReal_log hypos.le, Complex.norm_real]
        exact hlog
      have hkernel : ‖(k₀ (ppi (pt 0 1) z) : ℂ)‖ =
          ‖radialTransformIntegrand k₀ 0 z‖ := by
        simp [radialTransformIntegrand]
      have hderivNorm :
          ‖radialTransformDerivativeIntegrand k₀ s z‖ =
            ‖(k₀ (ppi (pt 0 1) z) : ℂ)‖ * ‖(height z : ℂ) ^ s‖ *
              ‖Complex.log (height z : ℂ)‖ := by
        simp [radialTransformDerivativeIntegrand, mul_assoc]
      rw [hderivNorm, hkernel]
      calc
        ‖radialTransformIntegrand k₀ 0 z‖ * ‖(height z : ℂ) ^ s‖ *
            ‖Complex.log (height z : ℂ)‖ ≤
          ‖radialTransformIntegrand k₀ 0 z‖ * E * R := by gcongr
        _ ≤ C * ‖radialTransformIntegrand k₀ 0 z‖ := by
          dsimp [C]
          exact le_of_eq (by ring)
  let Ffun : ℂ → OAI.CubicEisenstein.HyperbolicSpace → ℂ := fun s z => radialTransformIntegrand k₀ s z
  let Fprime : ℂ → OAI.CubicEisenstein.HyperbolicSpace → ℂ := fun s z => radialTransformDerivativeIntegrand k₀ s z
  have hDiff : ∀ᵐ z ∂volH3, ∀ s ∈ Metric.ball a₀ 1,
      HasDerivAt (Ffun · z) (Fprime s z) s := by
    filter_upwards [] with z
    intro s hs
    exact radialTransformIntegrand_hasDerivAt k₀ z s
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Ffun) (x₀ := a₀) (s := Metric.ball a₀ 1)
    (Metric.ball_mem_nhds a₀ (by norm_num)) hFmeas hFint
    (F' := Fprime) hFprimeMeas hBound hboundInt hDiff
  have hradial : HasDerivAt (fun s => radialTransform₀ k₀ s)
      (∫ z, Fprime a₀ z ∂volH3) a₀ := by
    cases H3_eq_OAI
    convert hderiv.2 using 1
    all_goals first | rfl | simp [radialTransform₀, Ffun, radialTransformIntegrand]
  exact hradial.differentiableAt

end ArtinPrimitiveRoots.A1.Spec
