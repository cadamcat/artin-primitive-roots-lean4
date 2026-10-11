import ArtinPrimitiveRoots.A2.Interface
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.SheetFinite
import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».NORM

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open Filter
open scoped Classical Pointwise
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- Translate the actual fundamental set. Definitionally equal to omegaAt R l for G=R.sheets.
Uses SheetGeometry, without importing its consumers. -/
def bridgeOmegaAt (G : SheetGeometry D S μ v0) (l : ℝ) : Set S.FS :=
  {y | ∃ x ∈ G.omega, y = (G.ellU l : S.FS) * x}

/-- Exact representative condition; definitionally equal to IsFundamentalAt in Reflection/Missing.
Uses Gamma and the actual diagonal action. -/
def bridgeFundamentalAt (S : SData F CE condη) (O : Set S.FS) (l : ℝ) : Prop :=
  MeasurableSet O ∧ (∀ y ∈ O, IsUnit y ∧ S.absS y = l) ∧
  ∀ y : S.FSˣ, S.absS (y : S.FS) = l →
    ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ O

/-- The actual sheet integral; definitionally equal to sheetIntegral R for G=R.sheets.
Uses Interface.onUnits. -/
def bridgeSheetIntegral (G : SheetGeometry D S μ v0) (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y, onUnits f y ∂(G.sheet l)

/-- Fundamental-set integral; definitionally equal to omegaInt R for G=R.sheets.
Uses bridgeOmegaAt and Interface.onUnits. -/
def bridgeOmegaInt (G : SheetGeometry D S μ v0) (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y in bridgeOmegaAt G l, onUnits f y ∂(G.sheet l)

variable (G : SheetGeometry D S μ v0)

private theorem bridgeAbsS_continuous : Continuous (S.absS) := by
  unfold SData.absS
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    have habs : Continuous (absFin v.1) := by
      convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
      ext x
      exact A1.Theta.absFin_eq_norm v.1 x
    exact habs.comp ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    exact Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)

private theorem bridgeFS_unit_iff_coords (y : S.FS) : IsUnit y ↔
    (∀ v : S.Sf, y.1 v ≠ 0) ∧ (∀ w : InfinitePlace F, y.2 w ≠ 0) := by
  simp [Prod.isUnit_iff, Pi.isUnit_iff]

private theorem bridgeAbsS_one_isUnit (y : S.FS) (hy : S.absS y = 1) : IsUnit y := by
  have hfin (v : S.Sf) : absFin v.1 (y.1 v) ≠ 0 := by
    intro hv
    have hprod : (∏ v' : S.Sf, absFin v'.1 (y.1 v')) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hv
    have hzero : S.absS y = 0 := by
      unfold SData.absS
      rw [hprod]
      simp
    rw [hy] at hzero
    norm_num at hzero
  have harch (w : InfinitePlace F) : Complex.normSq (y.2 w) ≠ 0 := by
    intro hw
    have hprod : (∏ w' : InfinitePlace F, Complex.normSq (y.2 w')) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) hw
    have hzero : S.absS y = 0 := by
      unfold SData.absS
      rw [hprod]
      simp
    rw [hy] at hzero
    norm_num at hzero
  rw [bridgeFS_unit_iff_coords]
  constructor
  · intro v hz
    have hzabs : absFin v.1 (y.1 v) = 0 := by
      rw [hz, A1.Theta.absFin_eq_norm]
      simp
    exact (hfin v) hzabs
  · intro w hz
    have hq : Complex.normSq (y.2 w) = 0 := by simp [hz]
    exact harch w hq

private theorem bridgeSheetCutoff_exists (K : Set S.FS) (hK : IsCompact K) :
    ∃ N : ∀ v : S.Sf, ℕ, ∀ v y, y ∈ K →
      absFin v.1 (y.1 v) < (Ideal.absNorm v.1.asIdeal : ℝ) ^ (N v) := by
  classical
  have hExist : ∀ v : S.Sf, ∃ n : ℕ, ∀ y, y ∈ K →
      absFin v.1 (y.1 v) < (Ideal.absNorm v.1.asIdeal : ℝ) ^ n := by
    intro v
    have habs : Continuous (fun y : S.FS => absFin v.1 (y.1 v)) := by
      have hAbs : Continuous (absFin v.1) := by
        convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
        ext x
        exact A1.Theta.absFin_eq_norm v.1 x
      exact hAbs.comp ((continuous_apply v).comp continuous_fst)
    obtain ⟨B, hB⟩ := hK.bddAbove_image habs.continuousOn
    have hq : 1 < (Ideal.absNorm v.1.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    have hpow : Tendsto
        (fun n : ℕ => (Ideal.absNorm v.1.asIdeal : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq
    obtain ⟨n, hn⟩ := (hpow.eventually_gt_atTop (max B 1)).exists
    refine ⟨n, ?_⟩
    intro y hy
    have hyB : absFin v.1 (y.1 v) ≤ B := hB ⟨y, hy, rfl⟩
    exact hyB.trans_lt ((le_max_left B 1).trans_lt hn)
  choose N hN using hExist
  refine ⟨N, ?_⟩
  intro v y hy
  exact hN v y hy

private theorem bridgeSheetMajorant_continuousOn
    (δ : ℝ) (hδ : 0 < δ) (N : ∀ v : S.Sf, ℕ) (E : Set S.FS)
    (hcut : ∀ y ∈ E, ∀ v : S.Sf,
      absFin v.1 (y.1 v) < (Ideal.absNorm v.1.asIdeal : ℝ) ^ (N v))
    (hunit : ∀ y ∈ E, IsUnit y) :
    ContinuousOn (bridgeSheetGlobalMajorant (S := S) δ N) E := by
  have hfin (v : S.Sf) : ContinuousOn
      (fun y : S.FS => bridgeFinMajorant v.1 δ (N v) (y.1 v)) E := by
    have habs : Continuous (fun y : S.FS => absFin v.1 (y.1 v)) := by
      have hAbs : Continuous (absFin v.1) := by
        convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
        ext x
        exact A1.Theta.absFin_eq_norm v.1 x
      exact hAbs.comp ((continuous_apply v).comp continuous_fst)
    have hpow : Continuous (fun y : S.FS => (absFin v.1 (y.1 v)) ^ δ) :=
      (Real.continuous_rpow_const hδ.le).comp habs
    apply hpow.continuousOn.congr
    intro y hy
    simp [bridgeFinMajorant, (hcut y hy v).le]
  have harch (w : InfinitePlace F) : ContinuousOn
      (fun y : S.FS => bridgeComplexMajorant δ (y.2 w)) E := by
    have hq : Continuous (fun y : S.FS => Complex.normSq (y.2 w)) :=
      Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)
    have hnum : Continuous (fun y : S.FS => Complex.normSq (y.2 w) ^ δ) :=
      (Real.continuous_rpow_const hδ.le).comp hq
    have hp : 0 < δ + 3 := by linarith
    have hden : Continuous (fun y : S.FS =>
        (1 + Complex.normSq (y.2 w)) ^ (δ + 3)) := by
      apply (Real.continuous_rpow_const hp.le).comp
      exact continuous_const.add hq
    have hformula : Continuous (fun y : S.FS =>
        Complex.normSq (y.2 w) ^ δ /
          (1 + Complex.normSq (y.2 w)) ^ (δ + 3)) := by
      apply hnum.div hden
      intro y
      have hbase : 0 < 1 + Complex.normSq (y.2 w) := by
        have hq := Complex.normSq_nonneg (y.2 w)
        linarith
      exact ne_of_gt (Real.rpow_pos_of_pos hbase (δ + 3))
    apply hformula.continuousOn.congr
    intro y hy
    have hcoord : y.2 w ≠ 0 := ((bridgeFS_unit_iff_coords y).mp (hunit y hy)).2 w
    simp [bridgeComplexMajorant, hcoord]
  unfold bridgeSheetGlobalMajorant
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd Finset.univ
    intro v hv
    exact hfin v
  · apply continuousOn_finsetProd Finset.univ
    intro w hw
    exact harch w

private theorem bridgeFS_measurable_leftMul (a : S.FS) :
    Measurable (fun y : S.FS => a * y) := by
  apply Measurable.prod
  · apply measurable_pi_iff.mpr
    intro v
    exact (measurable_const_mul (a.1 v)).comp
      ((measurable_pi_apply v).comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    exact (measurable_const_mul (a.2 w)).comp
      ((measurable_pi_apply w).comp measurable_snd)

private def bridgeMulUnitEquiv (a : S.FSˣ) : S.FS ≃ᵐ S.FS where
  toEquiv := {
    toFun := fun y => (a : S.FS) * y
    invFun := fun y => (a⁻¹ : S.FS) * y
    left_inv := by intro y; simp [mul_assoc]
    right_inv := by intro y; simp [mul_assoc] }
  measurable_toFun := bridgeFS_measurable_leftMul (a : S.FS)
  measurable_invFun := bridgeFS_measurable_leftMul (a⁻¹ : S.FS)

private def bridgeGammaDiag : Gamma S →* S.FSˣ :=
  S.diagU.comp (S.US.subtype.comp (Gamma S).subtype)

private theorem bridgeGammaDiag_eq (γ : Gamma S) :
    bridgeGammaDiag (S := S) γ = S.diagU (γ.1 : Fˣ) := rfl

private theorem bridge_onUnits_mul (a : S.FSˣ) (f : S.FSˣ → ℂ) :
    onUnits (fun y => f (a * y)) = fun y : S.FS => onUnits f ((a : S.FS) * y) := by
  funext y
  by_cases hy : IsUnit y
  · have hmul : IsUnit ((a : S.FS) * y) := (a.isUnit_units_mul y).2 hy
    have hmulval : hmul.unit = a * hy.unit := by
      apply Units.ext
      simp [hy.unit_spec]
    rw [onUnits, dif_pos hy, onUnits, dif_pos hmul, hmulval]
  · have hmul : ¬ IsUnit ((a : S.FS) * y) := fun h => hy ((a.isUnit_units_mul y).mp h)
    simp [onUnits, hy, hmul]

private theorem bridgeFS_measurable_inv : Measurable (fun z : S.FS => z⁻¹) := by
  apply Measurable.prod
  · apply measurable_pi_iff.mpr
    intro v
    exact measurable_inv.comp ((measurable_pi_apply v).comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    exact measurable_inv.comp ((measurable_pi_apply w).comp measurable_snd)

private theorem bridgeFS_isUnit_measurable : MeasurableSet {y : S.FS | IsUnit y} := by
  have hcoord (y : S.FS) : IsUnit y ↔
      (∀ v : S.Sf, y.1 v ≠ 0) ∧ (∀ w : InfinitePlace F, y.2 w ≠ 0) := by
    simp [Prod.isUnit_iff, Pi.isUnit_iff]
  rw [show {y : S.FS | IsUnit y} =
      (⋂ v : S.Sf, {y : S.FS | y.1 v ≠ 0}) ∩
        ⋂ w : InfinitePlace F, {y : S.FS | y.2 w ≠ 0} by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact hcoord y]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro v
    exact (measurableSet_singleton (0 : v.1.adicCompletion F)).compl.preimage
      ((measurable_pi_apply v).comp measurable_fst)
  · apply MeasurableSet.iInter
    intro w
    exact (measurableSet_singleton (0 : ℂ)).compl.preimage
      ((measurable_pi_apply w).comp measurable_snd)

private theorem bridgeFS_measurable_ringInverse :
    Measurable (fun y : S.FS => Ring.inverse y) := by
  have hpiece : Measurable (fun y : S.FS => if IsUnit y then y⁻¹ else 0) :=
    Measurable.ite bridgeFS_isUnit_measurable bridgeFS_measurable_inv measurable_const
  convert hpiece using 1
  funext y
  by_cases hy : IsUnit y
  · simp [Ring.inverse, hy]
  · simp [Ring.inverse, hy]

private theorem bridge_onUnits_ringInverse (f : S.FSˣ → ℂ) :
    onUnits (fun y => f y⁻¹) = fun y : S.FS => onUnits f (Ring.inverse y) := by
  funext y
  by_cases hy : IsUnit y
  · have hval : Ring.inverse y = ((hy.unit⁻¹ : S.FSˣ) : S.FS) := by
      rw [Ring.inverse_of_isUnit hy]
    have hunit : IsUnit (Ring.inverse y) := by rw [hval]; exact (hy.unit⁻¹).isUnit
    simp only [onUnits, dif_pos hy, dif_pos hunit]
    congr 1
    apply Units.ext
    simp [hval]
  · have hzero : Ring.inverse y = 0 := Ring.inverse_non_unit y hy
    simp [onUnits, hy, hzero]

private theorem bridgeOmega_finite_sheetMass (l : ℝ) (hl : 0 < l) :
    G.sheet l (bridgeOmegaAt G l) < ⊤ := by
  classical
  by_cases hOmega : G.omega.Nonempty
  · obtain ⟨K, hKcompact, hOmegaK⟩ := G.omega_bounded
    obtain ⟨N, hN⟩ := bridgeSheetCutoff_exists (S := S) K hKcompact
    obtain ⟨t, ht, hMajorantInt⟩ :=
      bridgeSheetGlobalMajorant_exists_sheet (G := G) (δ := 1) one_pos N
    let K1 : Set S.FS := K ∩ {y | S.absS y = 1}
    have hAbsCont : Continuous (S.absS) := bridgeAbsS_continuous (S := S)
    have hK1compact : IsCompact K1 := by
      apply hKcompact.inter_right
      exact isClosed_singleton.preimage hAbsCont
    have hOmegaK1 : G.omega ⊆ K1 := by
      intro y hy
      exact ⟨hOmegaK hy, (G.omega_norm y hy).2⟩
    have hK1nonempty : K1.Nonempty := by
      rcases hOmega with ⟨y, hy⟩
      exact ⟨y, hOmegaK1 hy⟩
    let u := G.ellU t
    let Z : Set S.FS := (fun y : S.FS => (u : S.FS) * y) '' K1
    have hMulCont : Continuous (fun y : S.FS => (u : S.FS) * y) := by
      change Continuous (fun y : S.FS =>
        ((fun v : S.Sf => ((u : S.FS).1 v) * y.1 v),
          fun w : InfinitePlace F => ((u : S.FS).2 w) * y.2 w))
      have hf : Continuous (fun y : S.FS =>
          fun v : S.Sf => ((u : S.FS).1 v) * y.1 v) := by
        apply continuous_pi_iff.mpr
        intro v
        exact continuous_const.mul ((continuous_apply v).comp continuous_fst)
      have hg : Continuous (fun y : S.FS =>
          fun w : InfinitePlace F => ((u : S.FS).2 w) * y.2 w) := by
        apply continuous_pi_iff.mpr
        intro w
        exact continuous_const.mul ((continuous_apply w).comp continuous_snd)
      exact hf.prodMk hg
    have hZcompact : IsCompact Z := hK1compact.image hMulCont
    have hZnonempty : Z.Nonempty := by
      rcases hK1nonempty with ⟨y, hy⟩
      exact ⟨(u : S.FS) * y, ⟨y, hy, rfl⟩⟩
    have hZunit : ∀ z ∈ Z, IsUnit z := by
      rintro z ⟨y, hy, rfl⟩
      exact u.isUnit.mul (bridgeAbsS_one_isUnit (S := S) y hy.2)
    have hZcut : ∀ z ∈ Z, ∀ v : S.Sf,
        absFin v.1 (z.1 v) < (Ideal.absNorm v.1.asIdeal : ℝ) ^ (N v) := by
      rintro z ⟨y, hy, rfl⟩ v
      have hcoord : ((u : S.FS) * y).1 v = y.1 v := by
        rw [G.ellU_val t ht]
        simp [SData.ell]
      rw [hcoord]
      exact hN v y hy.1
    have hMcont : ContinuousOn (bridgeSheetGlobalMajorant (S := S) 1 N) Z :=
      bridgeSheetMajorant_continuousOn (S := S) 1 one_pos N Z hZcut hZunit
    have hMpos : ∀ z ∈ Z, 0 < bridgeSheetGlobalMajorant (S := S) 1 N z := by
      intro z hz
      unfold bridgeSheetGlobalMajorant
      apply mul_pos
      · apply Finset.prod_pos
        intro v hv
        have hcut := hZcut z hz v
        rw [bridgeFinMajorant, if_pos hcut.le]
        have hvunit := (bridgeFS_unit_iff_coords z).mp (hZunit z hz)
        have hcoord0 : z.1 v ≠ 0 := hvunit.1 v
        have hpos : 0 < absFin v.1 (z.1 v) := by
          rw [A1.Theta.absFin_eq_norm]
          exact norm_pos_iff.mpr hcoord0
        exact Real.rpow_pos_of_pos hpos 1
      · apply Finset.prod_pos
        intro w hw
        have hwunit := (bridgeFS_unit_iff_coords z).mp (hZunit z hz)
        exact bridgeComplexMajorant_pos 1 one_pos (z.2 w) (hwunit.2 w)
    obtain ⟨z0, hz0, hmin⟩ := hZcompact.exists_isMinOn hZnonempty hMcont
    let c : ℝ := bridgeSheetGlobalMajorant (S := S) 1 N z0
    have hc : 0 < c := hMpos z0 hz0
    have hMlower : ∀ z ∈ Z, c ≤ bridgeSheetGlobalMajorant (S := S) 1 N z := by
      simpa [IsMinOn, IsMinFilter, c] using hmin
    let E := bridgeOmegaAt G t
    let et := bridgeMulUnitEquiv (S := S) u
    have hOeqt : E = et '' G.omega := by
      ext y
      simp only [E, bridgeOmegaAt, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, hxy.symm⟩
    have hEmeas : MeasurableSet E := by
      rw [hOeqt]
      exact et.measurableSet_image.mpr G.omega_measurable
    have hEsubZ : E ⊆ Z := by
      rw [hOeqt]
      rintro z ⟨y, hy, rfl⟩
      exact ⟨y, hOmegaK1 hy, rfl⟩
    have hMlowerE : ∀ y ∈ E, c ≤ bridgeSheetGlobalMajorant (S := S) 1 N y :=
      fun y hy => hMlower y (hEsubZ hy)
    have hscaledInt : Integrable
        (fun y => bridgeSheetGlobalMajorant (S := S) 1 N y / c) (G.sheet t) :=
      hMajorantInt.div_const c
    have hIndicatorMeas : AEStronglyMeasurable
        (Set.indicator E (fun _ : S.FS => (1 : ℝ))) (G.sheet t) :=
      (measurable_const.indicator hEmeas).aestronglyMeasurable
    have hIndicatorBound : ∀ᵐ y ∂G.sheet t,
        ‖Set.indicator E (fun _ : S.FS => (1 : ℝ)) y‖ ≤
          bridgeSheetGlobalMajorant (S := S) 1 N y / c := by
      filter_upwards with y
      by_cases hy : y ∈ E
      · have hquot : 1 ≤ bridgeSheetGlobalMajorant (S := S) 1 N y / c :=
          (one_le_div hc).2 (hMlowerE y hy)
        simpa [Set.indicator_of_mem, hy] using hquot
      · have hnonneg : 0 ≤ bridgeSheetGlobalMajorant (S := S) 1 N y / c :=
          div_nonneg (bridgeSheetGlobalMajorant_nonneg (S := S) 1 N y) hc.le
        simpa [Set.indicator_of_notMem, hy] using hnonneg
    have hIndicatorInt : Integrable
        (Set.indicator E (fun _ : S.FS => (1 : ℝ))) (G.sheet t) :=
      hscaledInt.mono' hIndicatorMeas hIndicatorBound
    have hOneOn : IntegrableOn (fun _ : S.FS => (1 : ℝ)) E (G.sheet t) :=
      (integrable_indicator_iff hEmeas).mp hIndicatorInt
    have hEtFinite : G.sheet t E < ⊤ := by
      have hfin := (integrableOn_const_iff (C := (1 : ℝ))).mp hOneOn
      exact hfin.resolve_left (by norm_num)
    let a : S.FSˣ := G.ellU l / G.ellU t
    let el := bridgeMulUnitEquiv (S := S) (G.ellU l)
    have hOeqL : bridgeOmegaAt G l = el '' G.omega := by
      ext y
      simp only [bridgeOmegaAt, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, hxy.symm⟩
    have hOmeasL : MeasurableSet (bridgeOmegaAt G l) := by
      rw [hOeqL]
      exact el.measurableSet_image.mpr G.omega_measurable
    rcases a2_bridge_NORM D S with ⟨_, _, _, _, hdiv, _⟩
    have haNorm : S.absS (a : S.FS) = l / t := by
      simpa [a, G.ellU_norm l hl, G.ellU_norm t ht] using hdiv (G.ellU l) (G.ellU t)
    have hratio : S.absS (a : S.FS) * t = l := by
      rw [haNorm]
      exact div_mul_cancel₀ l ht.ne'
    have htrans := G.sheet_translate a t ht
    rw [hratio] at htrans
    let φ : S.FS → S.FS := fun y => (a : S.FS) * y
    have hφ : Measurable φ := by
      change Measurable (fun y : S.FS => (a : S.FS) * y)
      exact bridgeFS_measurable_leftMul (a : S.FS)
    have hpre : φ ⁻¹' bridgeOmegaAt G l = E := by
      ext y
      simp only [Set.mem_preimage, bridgeOmegaAt, Set.mem_setOf_eq, E]
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        have haell : a * u = G.ellU l := by
          dsimp [a, u]
          exact div_mul_cancel _ _
        have hval : (a : S.FS) * (u : S.FS) = (G.ellU l : S.FS) :=
          congrArg (fun b : S.FSˣ => (b : S.FS)) haell
        change (a : S.FS) * y = (G.ellU l : S.FS) * x at hxy
        have hcancel : y = (u : S.FS) * x := by
          calc
            y = (a⁻¹ : S.FS) * ((a : S.FS) * y) := by simp
            _ = (a⁻¹ : S.FS) * ((G.ellU l : S.FS) * x) := by rw [hxy]
            _ = (u : S.FS) * x := by rw [← hval]; simp [mul_assoc]
        exact hcancel
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        have haell : a * u = G.ellU l := by
          dsimp [a, u]
          exact div_mul_cancel _ _
        have hval : (a : S.FS) * (u : S.FS) = (G.ellU l : S.FS) :=
          congrArg (fun b : S.FSˣ => (b : S.FS)) haell
        change y = (u : S.FS) * x at hxy
        calc
          (a : S.FS) * y = (a : S.FS) * ((u : S.FS) * x) := by rw [hxy]
          _ = ((a : S.FS) * (u : S.FS)) * x := by ac_rfl
          _ = (G.ellU l : S.FS) * x := by rw [hval]
    have hmass : G.sheet l (bridgeOmegaAt G l) = G.sheet t E := by
      calc
        G.sheet l (bridgeOmegaAt G l) = Measure.map φ (G.sheet t) (bridgeOmegaAt G l) := by
          rw [← htrans]
        _ = G.sheet t (φ ⁻¹' bridgeOmegaAt G l) := by
          rw [Measure.map_apply hφ hOmeasL]
        _ = G.sheet t E := by rw [hpre]
    rw [hmass]
    exact hEtFinite
  · have hEmpty : G.omega = ∅ := Set.not_nonempty_iff_eq_empty.mp hOmega
    simp [bridgeOmegaAt, hEmpty]

/-- Measurability, exact fundamental-domain condition, and finite restricted mass.
Uses NORM and SheetGeometry fields. -/
theorem a2_bridge_SHEET (l : ℝ) (hl : 0 < l) :
    bridgeFundamentalAt S (bridgeOmegaAt G l) l ∧
    G.sheet l (bridgeOmegaAt G l) < ⊤ ∧ Countable (Gamma S) := by
  let u := G.ellU l
  let e := bridgeMulUnitEquiv (S := S) u
  have hOeq : bridgeOmegaAt G l = e '' G.omega := by
    ext y
    simp only [bridgeOmegaAt, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy.symm⟩
  have hOmeas : MeasurableSet (bridgeOmegaAt G l) := by
    rw [hOeq]
    exact e.measurableSet_image.mpr G.omega_measurable
  have hnormMul := (a2_bridge_NORM D S).2.1
  have hnormO : ∀ y ∈ bridgeOmegaAt G l, IsUnit y ∧ S.absS y = l := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨u.isUnit.mul (G.omega_norm x hx).1, ?_⟩
    calc
      S.absS ((u : S.FS) * x) = S.absS (u : S.FS) * S.absS x := hnormMul _ _
      _ = l * 1 := by rw [G.ellU_norm l hl, (G.omega_norm x hx).2]
      _ = l := by ring
  have huniq : ∀ y : S.FSˣ, S.absS (y : S.FS) = l →
      ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈
        bridgeOmegaAt G l := by
    intro y hy
    let y0 : S.FSˣ := u⁻¹ * y
    have hnormDiv := (a2_bridge_NORM D S).2.2.2.2.1
    have hnorm0 : S.absS (y0 : S.FS) = 1 := by
      calc
        S.absS (y0 : S.FS) = S.absS ((y : S.FSˣ) / u : S.FSˣ).val := by
          congr 1
          change (y0 : S.FS) = ((y : S.FSˣ) / u : S.FSˣ)
          simp [y0, div_eq_mul_inv, mul_comm]
        _ = S.absS (y : S.FS) / S.absS (u : S.FS) := hnormDiv y u
        _ = l / l := by rw [hy, G.ellU_norm l hl]
        _ = 1 := div_self hl.ne'
    have hshift (z : S.FSˣ) :
        (z : S.FS) ∈ bridgeOmegaAt G l ↔ ((u⁻¹ * z : S.FSˣ) : S.FS) ∈ G.omega := by
      constructor
      · rintro ⟨x, hx, hz⟩
        have hval : ((u⁻¹ * z : S.FSˣ) : S.FS) = x := by
          calc
            ((u⁻¹ * z : S.FSˣ) : S.FS) = (u⁻¹ : S.FS) * (z : S.FS) := by simp
            _ = (u⁻¹ : S.FS) * ((u : S.FS) * x) := by rw [hz]
            _ = x := by simp [mul_assoc]
        simpa [hval] using hx
      · intro hz
        refine ⟨((u⁻¹ * z : S.FSˣ) : S.FS), hz, ?_⟩
        change (z : S.FS) = (u : S.FS) * ((u⁻¹ * z : S.FSˣ) : S.FS)
        simp [mul_assoc]
    rcases G.omega_partition y0 hnorm0 with ⟨γ, hγ, hγuniq⟩
    refine ⟨γ, ?_, ?_⟩
    · apply (hshift ((S.diagU (γ.1 : Fˣ))⁻¹ * y)).2
      simpa [y0, mul_assoc, mul_left_comm, mul_comm] using hγ
    · intro γ' hγ'
      apply hγuniq γ'
      have hh := (hshift ((S.diagU (γ'.1 : Fˣ))⁻¹ * y)).1 hγ'
      simpa [y0, mul_assoc, mul_left_comm, mul_comm] using hh
  have hcount : Countable (Gamma S) := by
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
    letI : Countable Fˣ := Units.val_injective.countable
    letI : Countable S.US := Subtype.val_injective.countable
    exact Subtype.countable
  refine ⟨⟨hOmeas, ⟨hnormO, huniq⟩⟩, ⟨?_, hcount⟩⟩
  exact bridgeOmega_finite_sheetMass (G := G) l hl

/-- Multiplication transport of integrable unit functions.
Uses NORM and SheetGeometry.sheet_translate. -/
theorem a2_bridge_SHEET_transport (l : ℝ) (hl : 0 < l) (a : S.FSˣ)
    (f : S.FSˣ → ℂ) (hf : Integrable (onUnits f) (G.sheet (S.absS (a : S.FS) * l))) :
    Integrable (onUnits (fun y => f (a * y))) (G.sheet l) ∧
    bridgeSheetIntegral G l (fun y => f (a * y)) =
      bridgeSheetIntegral G (S.absS (a : S.FS) * l) f := by
  let e := bridgeMulUnitEquiv (S := S) a
  have hpos : 0 < S.absS (a : S.FS) := (a2_bridge_NORM D S).2.2.1 a
  have hmp : MeasurePreserving (e : S.FS → S.FS)
      (G.sheet l) (G.sheet (S.absS (a : S.FS) * l)) := by
    exact ⟨e.measurable, G.sheet_translate a l hl⟩
  have hcomp : Integrable ((onUnits f) ∘ fun y : S.FS => (a : S.FS) * y) (G.sheet l) := by
    exact (hmp.integrable_comp_emb e.measurableEmbedding).2 hf
  have hfun := bridge_onUnits_mul (S := S) a f
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hfun] using hcomp
  · change (∫ y, onUnits (fun y => f (a * y)) y ∂G.sheet l) =
      ∫ y, onUnits f y ∂G.sheet (S.absS (a : S.FS) * l)
    rw [hfun]
    exact MeasurePreserving.integral_comp' (f := e) hmp (onUnits f)

/-- Integrable unfolding on the actual diagonal Γ and positive norm sheet.
Uses SHEET and NORM.
The integrability premise is supplied by ANALYSIS before application. -/
theorem a2_bridge_SHEET_unfold (l : ℝ) (hl : 0 < l) (f : S.FSˣ → ℂ)
    (hf : Integrable (onUnits f) (G.sheet l)) :
    (∀ γ : Gamma S, IntegrableOn (onUnits (fun y => f (S.diagU (γ.1 : Fˣ) * y)))
      (bridgeOmegaAt G l) (G.sheet l)) ∧
    Summable (fun γ : Gamma S => bridgeOmegaInt G l (fun y => f (S.diagU (γ.1 : Fˣ) * y))) ∧
    (∑' γ : Gamma S, bridgeOmegaInt G l (fun y => f (S.diagU (γ.1 : Fˣ) * y))) =
      bridgeSheetIntegral G l f := by
  letI : SMul (Gamma S) S.FS := ⟨fun γ y =>
    ((bridgeGammaDiag (S := S) γ : S.FSˣ) : S.FS) * y⟩
  letI : MulAction (Gamma S) S.FS := {
    one_smul := by
      intro y
      change ((bridgeGammaDiag (S := S) 1 : S.FSˣ) : S.FS) * y = y
      simp
    mul_smul := by
      intro γ γ' y
      change ((bridgeGammaDiag (S := S) (γ * γ') : S.FSˣ) : S.FS) * y =
        ((bridgeGammaDiag (S := S) γ : S.FSˣ) : S.FS) *
          (((bridgeGammaDiag (S := S) γ' : S.FSˣ) : S.FS) * y)
      rw [map_mul]
      simp [mul_assoc] }
  letI : MeasurableConstSMul (Gamma S) S.FS := ⟨fun γ => by
    change Measurable (fun y : S.FS => ((bridgeGammaDiag (S := S) γ : S.FSˣ) : S.FS) * y)
    exact bridgeFS_measurable_leftMul _⟩
  have hmain := a2_bridge_SHEET (G := G) l hl
  letI : Countable (Gamma S) := hmain.2.2
  have hfund := hmain.1
  have hgammaNorm (γ : Gamma S) : S.absS (S.diagU (γ.1 : Fˣ) : S.FS) = 1 :=
    (a2_bridge_NORM D S).2.2.2.1 (γ.1 : S.US)
  have hact (γ : Gamma S) : (fun y : S.FS => γ • y) =
      fun y => (S.diagU (γ.1 : Fˣ) : S.FS) * y := by
    funext y
    change ((bridgeGammaDiag (S := S) γ : S.FSˣ) : S.FS) * y = _
    rw [bridgeGammaDiag_eq]
  have hactInv (γ : Gamma S) : (fun y : S.FS => γ⁻¹ • y) =
      fun y => ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * y := by
    funext y
    change ((bridgeGammaDiag (S := S) γ⁻¹ : S.FSˣ) : S.FS) * y = _
    rw [map_inv, bridgeGammaDiag_eq]
    congr 1
    exact Units.val_inv_eq_inv_val _
  have hpres (γ : Gamma S) : MeasurePreserving (fun y : S.FS => γ • y)
      (G.sheet l) (G.sheet l) := by
    refine ⟨measurable_const_smul γ, ?_⟩
    change Measure.map (fun y : S.FS =>
      ((bridgeGammaDiag (S := S) γ : S.FSˣ) : S.FS) * y) (G.sheet l) = G.sheet l
    rw [bridgeGammaDiag_eq]
    simpa [hgammaNorm γ] using G.sheet_translate (S.diagU (γ.1 : Fˣ)) l hl
  letI : SMulInvariantMeasure (Gamma S) S.FS (G.sheet l) := ⟨fun γ t ht => by
    calc
      G.sheet l ((fun y : S.FS => γ • y) ⁻¹' t) =
          Measure.map (fun y : S.FS => γ • y) (G.sheet l) t :=
        (Measure.map_apply (measurable_const_smul γ) ht).symm
      _ = G.sheet l t := by rw [(hpres γ).map_eq]⟩
  have hqmp (γ : Gamma S) : Measure.QuasiMeasurePreserving (fun y : S.FS => γ • y)
      (G.sheet l) (G.sheet l) := (hpres γ).quasiMeasurePreserving
  have hcover : ∀ᵐ y ∂G.sheet l, ∃ γ : Gamma S, γ • y ∈ bridgeOmegaAt G l := by
    filter_upwards [G.sheet_support l hl] with y hy
    rcases hy with ⟨hyunit, hynorm⟩
    let yu : S.FSˣ := hyunit.unit
    obtain ⟨γ, hγ, -⟩ := hfund.2.2 yu hynorm
    refine ⟨γ⁻¹, ?_⟩
    rw [congrFun (hactInv γ) y]
    simpa [yu, hyunit.unit_spec] using hγ
  have hdis : ∀ γ : Gamma S, γ ≠ 1 →
      AEDisjoint (G.sheet l) (γ • bridgeOmegaAt G l) (bridgeOmegaAt G l) := by
    intro γ hγ
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro y hγy hy
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hγy
    have hleft : γ⁻¹ • y ∈ bridgeOmegaAt G l := hγy
    obtain ⟨hyunit, hynorm⟩ := hfund.2.1 y hy
    let yu : S.FSˣ := hyunit.unit
    obtain ⟨δ, hδ, hδuniq⟩ := hfund.2.2 yu hynorm
    have hone : ((S.diagU ((1 : Gamma S).1 : Fˣ))⁻¹ * yu : S.FSˣ).val ∈
        bridgeOmegaAt G l := by simpa [yu, hyunit.unit_spec] using hy
    have hgamma : ((S.diagU (γ.1 : Fˣ))⁻¹ * yu : S.FSˣ).val ∈
        bridgeOmegaAt G l := by
      have hleft' : ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * y ∈ bridgeOmegaAt G l := by
        rw [← congrFun (hactInv γ) y]
        exact hleft
      simpa [yu, hyunit.unit_spec] using hleft'
    have hγδ := hδuniq γ hgamma
    have h1δ := hδuniq 1 hone
    exact hγ (hγδ.trans h1δ.symm)
  have hdom : MeasureTheory.IsFundamentalDomain (Gamma S) (bridgeOmegaAt G l) (G.sheet l) :=
    MeasureTheory.IsFundamentalDomain.mk'' hfund.1.nullMeasurableSet hcover hdis hqmp
  have htransIntegrable (γ : Gamma S) :
      Integrable (onUnits (fun y => f (S.diagU (γ.1 : Fˣ) * y))) (G.sheet l) := by
    have hcomp : Integrable ((onUnits f) ∘ fun y : S.FS => γ • y) (G.sheet l) :=
      (hpres γ).integrable_comp hf.aestronglyMeasurable |>.mpr hf
    have hfun := bridge_onUnits_mul (S := S) (S.diagU (γ.1 : Fˣ)) f
    rw [hfun]
    simpa only [Function.comp_def, hact γ] using hcomp
  have htransOn (γ : Gamma S) :
      IntegrableOn (onUnits (fun y => f (S.diagU (γ.1 : Fˣ) * y)))
        (bridgeOmegaAt G l) (G.sheet l) :=
    (htransIntegrable γ).integrableOn
  have hsumNorm : Summable (fun γ : Gamma S =>
      ∫ y in bridgeOmegaAt G l,
        ‖onUnits f ((S.diagU (γ.1 : Fˣ) : S.FS) * y)‖ ∂G.sheet l) := by
    have hfsum : Integrable (onUnits f)
        (Measure.sum fun γ : Gamma S => (G.sheet l).restrict (γ • bridgeOmegaAt G l)) := by
      rw [hdom.sum_restrict]
      exact hf
    have hbase := hfsum.summable_integral
    apply hbase.congr
    intro γ
    let e := bridgeMulUnitEquiv (S := S) (S.diagU (γ.1 : Fˣ))
    have hset : γ • bridgeOmegaAt G l = e '' bridgeOmegaAt G l := by
      change (fun y : S.FS => γ • y) '' bridgeOmegaAt G l =
        (fun y : S.FS => (S.diagU (γ.1 : Fˣ) : S.FS) * y) '' bridgeOmegaAt G l
      rw [hact γ]
    change (∫ y in γ • bridgeOmegaAt G l, ‖onUnits f y‖ ∂G.sheet l) =
      ∫ y in bridgeOmegaAt G l, ‖onUnits f ((S.diagU (γ.1 : Fˣ) : S.FS) * y)‖ ∂G.sheet l
    rw [hset]
    exact (hpres γ).setIntegral_image_emb e.measurableEmbedding
      (fun y => ‖onUnits f y‖) (bridgeOmegaAt G l)
  have htermNorm : Summable (fun γ : Gamma S =>
      bridgeOmegaInt G l (fun y => f (S.diagU (γ.1 : Fˣ) * y))) :=
    hsumNorm.of_norm_bounded fun γ => by
      simp only [bridgeOmegaInt]
      rw [bridge_onUnits_mul (S := S) (S.diagU (γ.1 : Fˣ)) f]
      exact norm_integral_le_integral_norm _
  refine ⟨htransOn, htermNorm, ?_⟩
  calc
    (∑' γ : Gamma S, bridgeOmegaInt G l
        (fun y => f (S.diagU (γ.1 : Fˣ) * y))) =
        ∑' γ : Gamma S, ∫ y in bridgeOmegaAt G l, onUnits f (γ • y) ∂G.sheet l := by
      apply tsum_congr
      intro γ
      have hfun := bridge_onUnits_mul (S := S) (S.diagU (γ.1 : Fˣ)) f
      rw [bridgeOmegaInt, hfun]
      simpa only [hact γ]
    _ = ∫ y, onUnits f y ∂G.sheet l := (hdom.integral_eq_tsum''
      (onUnits f) hf).symm

/-- Integrable inversion between reciprocal positive sheets.
Uses NORM and SheetGeometry.sheet_inversion. -/
theorem a2_bridge_SHEET_inversion (l : ℝ) (hl : 0 < l) (f : S.FSˣ → ℂ)
    (hf : Integrable (onUnits f) (G.sheet l⁻¹)) :
    Integrable (onUnits (fun y => f y⁻¹)) (G.sheet l) ∧
    bridgeSheetIntegral G l (fun y => f y⁻¹) = bridgeSheetIntegral G l⁻¹ f := by
  have hmp : MeasurePreserving (fun y : S.FS => Ring.inverse y)
      (G.sheet l) (G.sheet l⁻¹) :=
    ⟨bridgeFS_measurable_ringInverse, G.sheet_inversion l hl⟩
  have hfun := bridge_onUnits_ringInverse (S := S) f
  have hcomp : Integrable ((onUnits f) ∘ fun y : S.FS => Ring.inverse y) (G.sheet l) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).mpr hf
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hfun] using hcomp
  · change (∫ y, onUnits (fun y => f y⁻¹) y ∂G.sheet l) =
      ∫ y, onUnits f y ∂G.sheet l⁻¹
    rw [hfun]
    have hgm : AEStronglyMeasurable (onUnits f)
        (Measure.map (fun y : S.FS => Ring.inverse y) (G.sheet l)) := by
      rw [hmp.map_eq]
      exact hf.aestronglyMeasurable
    rw [← hmp.map_eq]
    exact (MeasureTheory.integral_map bridgeFS_measurable_ringInverse.aemeasurable hgm).symm

end ArtinPrimitiveRoots.A2
