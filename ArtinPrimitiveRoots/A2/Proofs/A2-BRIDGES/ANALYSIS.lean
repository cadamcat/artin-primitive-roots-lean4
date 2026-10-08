import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SHEET
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.LocalRadial
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.FiniteRadial

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- Absolute tensor sum on units; definitionally equal to rotatedAbs with projected R.rotated data.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses the actual finite and complex factors. -/
def bridgeRotatedAbs (S : SData F CE condη) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (y : S.FSˣ) : ℝ :=
  ∑ ℓ : Fin J, (∏ v : S.Sf, ‖ff ℓ v ((y : S.FS).1 v)‖) *
    ∏ w : InfinitePlace F, ‖fc ℓ w ((y : S.FS).2 w)‖

private def bridgeRotatedAbsAll (S : SData F CE condη) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (y : S.FS) : ℝ :=
  ∑ ℓ : Fin J, (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) *
    ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖

private theorem bridgeRotatedAbsAll_measurable (δ : ℝ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    Measurable (bridgeRotatedAbsAll S J ff fc) := by
  classical
  unfold bridgeRotatedAbsAll
  apply Finset.univ.measurable_fun_sum
  intro ℓ hℓ
  apply Measurable.mul
  · apply Finset.univ.measurable_fun_prod
    intro v hv
    have hf := bridgeSheetHypFin_measurable v.1 δ (ff ℓ v) (hff ℓ v)
    exact (continuous_norm.measurable.comp hf).comp
      ((measurable_pi_apply v).comp measurable_fst)
  · apply Finset.univ.measurable_fun_prod
    intro w hw
    have hf := bridgeSheetHypC_measurable δ (fc ℓ w) (hfc ℓ w)
    exact (continuous_norm.measurable.comp hf).comp
      ((measurable_pi_apply w).comp measurable_snd)

/-- Absolute sheet profile, definitionally equal to profileAbs on the consumer's projected data.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses bridgeRotatedAbs and bridgeSheetIntegral. -/
def bridgeProfileAbs (G : SheetGeometry D S μ v0) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (x : ℝ) : ℝ :=
  (bridgeSheetIntegral G x (fun y => (bridgeRotatedAbs S J ff fc y : ℂ))).re

/-- One profile tensor with its actual bounded multiplier. No ReflectionSetup import is needed.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses bridgeSheetIntegral. -/
def bridgeProfileH (G : SheetGeometry D S μ v0) (m : S.FSˣ → ℂ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (ℓ : Fin J) (x : ℝ) : ℂ :=
  bridgeSheetIntegral G x (fun y => m y *
    (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
    ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))

variable (G : SheetGeometry D S μ v0)

private theorem bridgeFS_properSpace : ProperSpace S.FS := by
  letI : ∀ v : S.Sf, ProperSpace (v.1.adicCompletion F) := fun v => bridgeFin_properSpace v.1
  letI : ProperSpace (∀ v : S.Sf, v.1.adicCompletion F) := inferInstance
  letI : ProperSpace (∀ w : InfinitePlace F, ℂ) := inferInstance
  infer_instance

private theorem bridgeFS_sixthPower_range_closed :
    IsClosed (Set.range (fun y : S.FS => y ^ 6)) := by
  classical
  let UF : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    ⋂ v : S.Sf, (fun z : ∀ v : S.Sf, v.1.adicCompletion F => z v) ⁻¹'
      Set.range (fun z : v.1.adicCompletion F => z ^ 6)
  let UC : Set (InfinitePlace F → ℂ) :=
    ⋂ w : InfinitePlace F, (fun z : InfinitePlace F → ℂ => z w) ⁻¹'
      Set.range (fun z : ℂ => z ^ 6)
  have hUF : IsClosed UF := by
    apply isClosed_iInter
    intro v
    exact IsClosed.preimage (continuous_apply v) (bridgeFin_sixthPower_range_closed v.1)
  have hUC : IsClosed UC := by
    apply isClosed_iInter
    intro w
    exact IsClosed.preimage (continuous_apply w) bridgeComplex_sixthPower_range_closed
  have hRange : Set.range (fun y : S.FS => y ^ 6) = UF ×ˢ UC := by
    ext y
    simp only [Set.mem_range, Set.mem_prod, UF, UC, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz⟩
      constructor
      · intro v
        refine ⟨z.1 v, ?_⟩
        have h := congrArg (fun p : S.FS => p.1 v) hz
        simpa using h
      · intro w
        refine ⟨z.2 w, ?_⟩
        have h := congrArg (fun p : S.FS => p.2 w) hz
        simpa using h
    · intro hy
      have hfin : ∀ v : S.Sf, ∃ z : v.1.adicCompletion F, z ^ 6 = y.1 v :=
        fun v => hy.1 v
      have harch : ∀ w : InfinitePlace F, ∃ z : ℂ, z ^ 6 = y.2 w :=
        fun w => hy.2 w
      let z : S.FS := (fun v => Classical.choose (hfin v), fun w => Classical.choose (harch w))
      refine ⟨z, ?_⟩
      apply Prod.ext
      · funext v
        exact Classical.choose_spec (hfin v)
      · funext w
        exact Classical.choose_spec (harch w)
  rw [hRange]
  exact hUF.prod hUC

private theorem bridgeUnits_sixthPower_range_eq_preimage :
    Set.range (fun y : S.FSˣ => y ^ 6) =
      (Units.val : S.FSˣ → S.FS) ⁻¹' Set.range (fun y : S.FS => y ^ 6) := by
  ext u
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : S.FS), ?_⟩
    exact congrArg Units.val hv
  · rintro ⟨z, hz⟩
    change z ^ 6 = (u : S.FS) at hz
    have hunitpow : IsUnit (z ^ 6) := by rw [hz]; exact u.isUnit
    rcases isUnit_iff_exists.mp hunitpow with ⟨q, hq₁, hq₂⟩
    have hzunit : IsUnit z := by
      rw [isUnit_iff_exists]
      refine ⟨z ^ 5 * q, ?_, ?_⟩
      · calc
          z * (z ^ 5 * q) = z ^ 6 * q := by ring
          _ = 1 := hq₁
      · calc
          (z ^ 5 * q) * z = q * z ^ 6 := by ring
          _ = 1 := hq₂
    let v : S.FSˣ := hzunit.unit
    have hv : (v : S.FS) = z := hzunit.unit_spec
    refine ⟨v, ?_⟩
    apply Units.ext
    calc
      ((v ^ 6 : S.FSˣ) : S.FS) = (v : S.FS) ^ 6 := by simp
      _ = z ^ 6 := by rw [hv]
      _ = (u : S.FS) := hz

private theorem bridgeUnits_sixthPower_range_closed :
    IsClosed ((powMonoidHom 6 : S.FSˣ →* S.FSˣ).range : Set S.FSˣ) := by
  change IsClosed (Set.range (fun y : S.FSˣ => y ^ 6))
  rw [bridgeUnits_sixthPower_range_eq_preimage]
  exact bridgeFS_sixthPower_range_closed.preimage Units.continuous_val

private theorem bridgeFS_measurable_div_const (u : S.FS) :
    Measurable (fun y : S.FS => y / u) := by
  apply Measurable.prod
  · apply measurable_pi_iff.mpr
    intro v
    exact (measurable_div_const (u.1 v)).comp
      ((measurable_pi_apply v).comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    exact (measurable_div_const (u.2 w)).comp
      ((measurable_pi_apply w).comp measurable_snd)

private theorem bridgeFS_measurable_inv : Measurable (fun z : S.FS => z⁻¹) := by
  apply Measurable.prod
  · apply measurable_pi_iff.mpr
    intro v
    exact measurable_inv.comp ((measurable_pi_apply v).comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    exact measurable_inv.comp ((measurable_pi_apply w).comp measurable_snd)

private theorem bridgeFS_units_opensMeasurable : OpensMeasurableSpace S.FSˣ := by
  letI : MeasurableSpace S.FSˣ := Units.instMeasurableSpace
  letI : OpensMeasurableSpace S.FS := inferInstance
  letI : SecondCountableTopology S.FS := inferInstance
  letI : SecondCountableTopology S.FSᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : S.FS ≃ₜ S.FSᵐᵒᵖ).symm.secondCountableTopology
  letI : OpensMeasurableSpace S.FSᵐᵒᵖ :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr fun U hU => by
    have hpre : IsOpen ((MulOpposite.op : S.FS → S.FSᵐᵒᵖ) ⁻¹' U) :=
      (MulOpposite.opHomeomorph : S.FS ≃ₜ S.FSᵐᵒᵖ).isOpen_preimage.mpr hU
    change MeasurableSet[(MeasurableSpace.map (MulOpposite.op : S.FS → S.FSᵐᵒᵖ)
      (inferInstance : MeasurableSpace S.FS))] U
    exact hpre.measurableSet
  letI : OpensMeasurableSpace (S.FS × S.FSᵐᵒᵖ) := inferInstance
  have hval : Measurable (Units.val : S.FSˣ → S.FS) := comap_measurable Units.val
  have hinv : Measurable (fun u : S.FSˣ => ((u⁻¹ : S.FSˣ) : S.FS)) := by
    convert bridgeFS_measurable_inv.comp hval using 1
    funext u
    simp
  have hEmbed : Measurable (Units.embedProduct S.FS) := by
    exact hval.prodMk (measurable_mul_op.comp hinv)
  exact opensMeasurableSpace_iff_forall_measurableSet.mpr fun U hU => by
    change @IsOpen S.FSˣ (TopologicalSpace.induced (Units.embedProduct S.FS) inferInstance) U at hU
    obtain ⟨V, hV, hpre⟩ := isOpen_induced_iff.mp hU
    rw [← hpre]
    exact hEmbed hV.measurableSet

private theorem bridgeV_measurableSingleton (G : SheetGeometry D S μ v0) :
    MeasurableSingletonClass S.V := by
  classical
  letI : Fintype S.V := G.classFinite
  letI : OpensMeasurableSpace S.FS := inferInstance
  letI : MeasurableSpace S.FSˣ := Units.instMeasurableSpace
  letI : OpensMeasurableSpace S.FSˣ := bridgeFS_units_opensMeasurable
  letI : T1Space S.V := QuotientGroup.t1Space_iff.mpr bridgeUnits_sixthPower_range_closed
  refine ⟨?_⟩
  intro q
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q
  let H : Subgroup S.FSˣ := (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  have hpre : (QuotientGroup.mk : S.FSˣ → S.V) ⁻¹' {q} =
      (fun y : S.FSˣ => y / u) ⁻¹' (H : Set S.FSˣ) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hu]
    exact QuotientGroup.eq_iff_div_mem
  rw [measurableSet_quotient]
  rw [hpre]
  have hH : (H : Set S.FSˣ) =
      (Units.val : S.FSˣ → S.FS) ⁻¹' Set.range (fun z : S.FS => z ^ 6) := by
    change Set.range (fun y : S.FSˣ => y ^ 6) = _
    exact bridgeUnits_sixthPower_range_eq_preimage
  have hmap : Measurable (fun y : S.FSˣ => ((y / u : S.FSˣ) : S.FS)) := by
    convert (bridgeFS_measurable_div_const (u : S.FS)).comp
      (comap_measurable (Units.val : S.FSˣ → S.FS)) using 1
    funext y
    simp
  rw [hH]
  exact bridgeFS_sixthPower_range_closed.measurableSet.preimage hmap

private theorem bridgeClassFun_measurable (G : SheetGeometry D S μ v0) (b : S.V → ℂ) :
    Measurable b := by
  letI : Fintype S.V := G.classFinite
  letI : MeasurableSingletonClass S.V := bridgeV_measurableSingleton G
  exact measurable_of_finite b

private theorem bridgeFS_units_range_open : IsOpen (Set.range (Units.val : S.FSˣ → S.FS)) := by
  classical
  let UF : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    ⋂ v : S.Sf, (fun z : ∀ v : S.Sf, v.1.adicCompletion F => z v) ⁻¹' ({0}ᶜ)
  let UC : Set (InfinitePlace F → ℂ) :=
    ⋂ w : InfinitePlace F, (fun z : InfinitePlace F → ℂ => z w) ⁻¹' ({0}ᶜ)
  have hUF : IsOpen UF := by
    apply isOpen_iInter_of_finite
    intro v
    exact (continuous_apply v).isOpen_preimage ({0}ᶜ) isClosed_singleton.isOpen_compl
  have hUC : IsOpen UC := by
    apply isOpen_iInter_of_finite
    intro w
    exact (continuous_apply w).isOpen_preimage ({0}ᶜ) isClosed_singleton.isOpen_compl
  have hunit : {y : S.FS | IsUnit y} = UF ×ˢ UC := by
    ext y
    simp [UF, UC, Prod.isUnit_iff, Pi.isUnit_iff, isUnit_iff_ne_zero]
  have hrange : Set.range (Units.val : S.FSˣ → S.FS) = {y | IsUnit y} := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact u.isUnit
    · intro hy
      exact ⟨hy.unit, hy.unit_spec⟩
  rw [hrange, hunit]
  exact hUF.prod hUC

private theorem bridgeFS_units_val_measurableEmbedding :
    MeasurableEmbedding (Units.val : S.FSˣ → S.FS) := by
  letI : OpensMeasurableSpace S.FS := inferInstance
  letI : MeasurableSpace S.FSˣ := Units.instMeasurableSpace
  refine ⟨Units.val_injective, comap_measurable Units.val, ?_⟩
  intro t ht
  rcases MeasurableSpace.measurableSet_comap.mp ht with ⟨s, hs, hpre⟩
  have himage : Units.val '' t = s ∩ Set.range Units.val := by
    rw [← hpre, Set.image_preimage_eq_inter_range]
  rw [himage]
  exact hs.inter bridgeFS_units_range_open.measurableSet

private theorem bridgeSheetMultiplier_measurable (G : SheetGeometry D S μ v0)
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) : Measurable m := by
  letI : OpensMeasurableSpace S.FSˣ := bridgeFS_units_opensMeasurable
  rcases hm with ⟨L, k, b, hb, hrep⟩
  have hchar : Measurable (fun y : S.FSˣ => ((L.L y : ℂˣ) : ℂ)) := L.cont.measurable
  have hclass : Measurable (fun y : S.FSˣ => b (QuotientGroup.mk y)) :=
    (bridgeClassFun_measurable G b).comp QuotientGroup.measurable_coe
  have hpow : Measurable (fun y : S.FSˣ => ((L.L y : ℂˣ) : ℂ) ^ k) := by
    cases k with
    | ofNat n => exact hchar.pow_const n
    | negSucc n =>
      have hpos : Measurable (fun y : S.FSˣ => ((L.L y : ℂˣ) : ℂ) ^ (n + 1)) :=
        hchar.pow_const (n + 1)
      have hinv : Measurable (fun y : S.FSˣ => (((L.L y : ℂˣ) : ℂ) ^ (n + 1))⁻¹) :=
        measurable_inv.comp hpos
      have hEq : (fun y : S.FSˣ => ((L.L y : ℂˣ) : ℂ) ^ Int.negSucc n) =
          fun y => (((L.L y : ℂˣ) : ℂ) ^ (n + 1))⁻¹ := by
        funext y
        exact zpow_negSucc ((L.L y : ℂˣ) : ℂ) n
      rw [hEq]
      exact hinv
  have hformula : Measurable (fun y : S.FSˣ =>
      ((L.L y : ℂˣ) : ℂ) ^ k * b (QuotientGroup.mk y)) := hpow.mul hclass
  have hEq : m = fun y : S.FSˣ =>
      ((L.L y : ℂˣ) : ℂ) ^ k * b (QuotientGroup.mk y) := by
    funext y
    have h := hrep y
    simpa [onUnits] using h
  rw [hEq]
  exact hformula

private theorem bridgeOnUnits_measurable (G : SheetGeometry D S μ v0)
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) : Measurable (onUnits m) := by
  have hmMeas : Measurable m := bridgeSheetMultiplier_measurable G m hm
  have hUnitsEmb : MeasurableEmbedding (Units.val : S.FSˣ → S.FS) :=
    bridgeFS_units_val_measurableEmbedding
  have hExtMeas : Measurable (Function.extend Units.val m (fun _ => (0 : ℂ))) :=
    hUnitsEmb.measurable_extend hmMeas measurable_const
  have hEq : onUnits m = Function.extend Units.val m (fun _ => (0 : ℂ)) := by
    funext y
    by_cases hy : IsUnit y
    · have hleft : onUnits m y = m hy.unit := by simp [onUnits, hy]
      rw [hleft]
      have hval : (hy.unit : S.FS) = y := hy.unit_spec
      calc
        m hy.unit = Function.extend Units.val m (fun _ => 0) (hy.unit : S.FS) :=
          (Units.val_injective.extend_apply m (fun _ => 0) hy.unit).symm
        _ = Function.extend Units.val m (fun _ => 0) y := by rw [hval]
    · have hnot : ¬∃ u : S.FSˣ, (u : S.FS) = y := by
        rintro ⟨u, rfl⟩
        exact hy u.isUnit
      simp [onUnits, hy, Function.extend_apply', hnot]
  rw [hEq]
  exact hExtMeas

private theorem bridgeSheetMultiplier_bound (m : S.FSˣ → ℂ)
    (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖m y‖ ≤ C := by
  rcases hm with ⟨L, k, b, hBound, hm⟩
  rcases hBound with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y
  have hmy : m y = ((L.L y : ℂˣ) : ℂ) ^ k * b (QuotientGroup.mk y) := by
    have h := hm y
    simpa [onUnits] using h
  have hpow : ‖((L.L y : ℂˣ) : ℂ) ^ k‖ = 1 := by
    rw [norm_zpow, L.unitary]
    simp
  calc
    ‖m y‖ = ‖((L.L y : ℂˣ) : ℂ) ^ k‖ * ‖b (QuotientGroup.mk y)‖ := by rw [hmy, norm_mul]
    _ ≤ 1 * C := by rw [hpow]; simpa using hC (QuotientGroup.mk y)
    _ = C := one_mul C
    _ ≤ max C 0 := le_max_left _ _

/-- Product of the local radial majorants used in ANALYSIS. -/
def bridgeGlobalMajorant (δ : ℝ) (N : ∀ v : S.Sf, ℕ) (y : S.FS) : ℝ :=
  (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) ((y : S.FS).1 v)) *
    ∏ w : InfinitePlace F, bridgeComplexMajorant δ ((y : S.FS).2 w)

private theorem bridgeGlobalMajorant_measurable (δ : ℝ) (N : ∀ v : S.Sf, ℕ) :
    Measurable (bridgeGlobalMajorant δ N) := by
  have hfin : Measurable (fun y : S.FS =>
      ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) := by
    apply Finset.univ.measurable_fun_prod
    intro v hv
    exact (bridgeFinMajorant_measurable v.1 δ (N v)).comp
      ((measurable_pi_apply v).comp measurable_fst)
  have harch : Measurable (fun y : S.FS =>
      ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w)) := by
    apply Finset.univ.measurable_fun_prod
    intro w hw
    exact (bridgeComplexMajorant_measurable δ).comp
      ((measurable_pi_apply w).comp measurable_snd)
  change Measurable (fun y : S.FS =>
    (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) *
      ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w))
  exact hfin.mul harch

private theorem bridgeGlobalMajorant_scale_oneFin (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) (a : S.FSˣ)
    (ha : ∀ v : S.Sf, ((a : S.FS).1 v) = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : S.FS,
      bridgeGlobalMajorant δ N ((a : S.FS) * y) ≤ C * bridgeGlobalMajorant δ N y := by
  classical
  let hscale : ∀ w : InfinitePlace F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, bridgeComplexMajorant δ (((a : S.FS).2 w) * z) ≤
        C * bridgeComplexMajorant δ z := by
    intro w
    apply bridgeComplexMajorant_scale δ hδ
    change ((S.compC w a : ℂˣ) : ℂ) ≠ 0
    exact Units.ne_zero (S.compC w a)
  let Cw : InfinitePlace F → ℝ := fun w => Classical.choose (hscale w)
  have hCw : ∀ w, 0 ≤ Cw w ∧
      ∀ z : ℂ, bridgeComplexMajorant δ (((a : S.FS).2 w) * z) ≤
        Cw w * bridgeComplexMajorant δ z := by
    intro w
    exact Classical.choose_spec (hscale w)
  let C : ℝ := ∏ w : InfinitePlace F, Cw w
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.prod_nonneg
    intro w hw
    exact (hCw w).1
  refine ⟨C, hC, ?_⟩
  intro y
  have hfin_eq :
      (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (((a : S.FS) * y).1 v)) =
        ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v) := by
    congr 1
    funext v
    simp [ha v]
  have hfin_nonneg : 0 ≤ ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v) := by
    apply Finset.prod_nonneg
    intro v hv
    exact bridgeFinMajorant_nonneg v.1 δ (N v) (y.1 v)
  have harch_le :
      (∏ w : InfinitePlace F, bridgeComplexMajorant δ (((a : S.FS) * y).2 w)) ≤
        ∏ w : InfinitePlace F, Cw w * bridgeComplexMajorant δ (y.2 w) := by
    apply Finset.prod_le_prod₀
    · intro w hw
      exact bridgeComplexMajorant_nonneg δ (((a : S.FS) * y).2 w)
    · intro w hw
      simpa [Pi.mul_apply] using (hCw w).2 (y.2 w)
  have hprod_eq :
      (∏ w : InfinitePlace F, Cw w * bridgeComplexMajorant δ (y.2 w)) =
        C * (∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w)) := by
    simp [C, Finset.prod_mul_distrib]
  calc
    bridgeGlobalMajorant δ N ((a : S.FS) * y) =
        (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (((a : S.FS) * y).1 v)) *
          ∏ w : InfinitePlace F, bridgeComplexMajorant δ (((a : S.FS) * y).2 w) := rfl
    _ = (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) *
          ∏ w : InfinitePlace F, bridgeComplexMajorant δ (((a : S.FS) * y).2 w) := by
      rw [hfin_eq]
    _ ≤ (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) *
          ∏ w : InfinitePlace F, Cw w * bridgeComplexMajorant δ (y.2 w) :=
      mul_le_mul_of_nonneg_left harch_le hfin_nonneg
    _ = C * bridgeGlobalMajorant δ N y := by
      rw [hprod_eq, bridgeGlobalMajorant]
      ring

private theorem bridgeGlobalMajorant_integrable (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) : Integrable (bridgeGlobalMajorant δ N) (Theta.mulHaarS S μ) := by
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    haveI : SigmaFinite (μ v.1).μ := inferInstance
    change SigmaFinite ((μ v.1).μ.withDensity fun y => ENNReal.ofReal (absFin v.1 y)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SigmaFinite Theta.mulHaarC := by
    change SigmaFinite (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hfin : Integrable
      (fun y : ∀ v : S.Sf, v.1.adicCompletion F =>
        ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y v))
      (Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)) := by
    apply MeasureTheory.Integrable.fintype_prod_dep
    intro v
    exact bridgeFinMajorant_integrable v.1 (μ v.1) δ hδ (N v)
  have harch : Integrable
      (fun z : InfinitePlace F → ℂ =>
        ∏ w : InfinitePlace F, bridgeComplexMajorant δ (z w))
      (Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC) := by
    apply MeasureTheory.Integrable.fintype_prod_dep
    intro w
    exact bridgeComplexMajorant_integrable δ hδ
  change Integrable
    (fun y : (∀ v : S.Sf, v.1.adicCompletion F) × (InfinitePlace F → ℂ) =>
      (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) *
        ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w))
    ((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC))
  exact hfin.mul_prod harch

private theorem bridgeGlobalHaar_openPos :
    Measure.IsOpenPosMeasure (Theta.mulHaarS S μ) := by
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    haveI : SigmaFinite (μ v.1).μ := inferInstance
    change SigmaFinite ((μ v.1).μ.withDensity fun y => ENNReal.ofReal (absFin v.1 y)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SigmaFinite Theta.mulHaarC := by
    change SigmaFinite (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : ∀ v : S.Sf, Measure.IsOpenPosMeasure (Theta.mulHaarFin (μ v.1)) :=
    fun v => bridgeFin_mulHaar_openPos v.1 (μ v.1)
  letI : Measure.IsOpenPosMeasure Theta.mulHaarC := bridgeComplex_mulHaar_openPos
  change Measure.IsOpenPosMeasure
    ((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC))
  infer_instance

private theorem bridgeGlobalMajorant_pos_on_open (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    ∃ U : Set S.FS, IsOpen U ∧ U.Nonempty ∧
      ∀ y ∈ U, bridgeGlobalMajorant δ N y ≠ 0 := by
  let Uf : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    ⋂ v : S.Sf, {y : (∀ v : S.Sf, v.1.adicCompletion F) |
      dist (y v) (1 : v.1.adicCompletion F) < 1}
  let Uc : Set (InfinitePlace F → ℂ) :=
    ⋂ w : InfinitePlace F, {z : InfinitePlace F → ℂ | z w ≠ 0}
  let U : Set S.FS := Uf ×ˢ Uc
  have hUf : IsOpen Uf := by
    apply isOpen_iInter_of_finite
    intro v
    exact (continuous_apply v).isOpen_preimage (Metric.ball 1 1) Metric.isOpen_ball
  have hUc : IsOpen Uc := by
    apply isOpen_iInter_of_finite
    intro w
    change IsOpen ((fun z : InfinitePlace F → ℂ => z w) ⁻¹' ({0}ᶜ))
    exact (continuous_apply w).isOpen_preimage ({0}ᶜ) isClosed_singleton.isOpen_compl
  have hU : IsOpen U := hUf.prod hUc
  have hUne : U.Nonempty := by
    refine ⟨(fun _ => (1 : _), fun _ => (1 : ℂ)), ?_⟩
    simp [U, Uf, Uc]
  refine ⟨U, hU, hUne, ?_⟩
  intro y hy
  have hyf : y.1 ∈ Uf := hy.1
  have hyc : y.2 ∈ Uc := hy.2
  have habs : ∀ v : S.Sf, absFin v.1 (y.1 v) = 1 := by
    intro v
    let K := v.1.adicCompletion F
    have hd : dist (y.1 v) (1 : K) < 1 := Set.mem_iInter.mp hyf v
    have hdnorm : ‖y.1 v - 1‖ < 1 := by simpa [dist_eq_norm] using hd
    have hupper : ‖y.1 v‖ ≤ 1 := by
      calc
        ‖y.1 v‖ = ‖(y.1 v - 1) + 1‖ := by congr 1 <;> ring
        _ ≤ max ‖y.1 v - 1‖ 1 := IsUltrametricDist.norm_add_one_le_max_norm_one _
        _ = 1 := max_eq_right hdnorm.le
    have hnot : ¬ ‖y.1 v‖ < 1 := by
      intro hlt
      have hsum : (1 : K) = y.1 v + (1 - y.1 v) := by ring
      have hsumBound : 1 ≤ max ‖y.1 v‖ ‖1 - y.1 v‖ := by
        calc
          (1 : ℝ) = ‖(1 : K)‖ := by simp
          _ = ‖y.1 v + (1 - y.1 v)‖ := congrArg norm hsum
          _ ≤ max ‖y.1 v‖ ‖1 - y.1 v‖ := IsUltrametricDist.norm_add_le_max _ _
      have hrev : ‖1 - y.1 v‖ = ‖y.1 v - 1‖ := by
        rw [show (1 : K) - y.1 v = -(y.1 v - 1) by ring, norm_neg]
      have hmax : max ‖y.1 v‖ ‖1 - y.1 v‖ < 1 := by
        rw [hrev]
        exact max_lt hlt hdnorm
      linarith
    have hnorm : ‖y.1 v‖ = 1 := le_antisymm hupper (le_of_not_gt hnot)
    rw [A1.Theta.absFin_eq_norm]
    exact hnorm
  have hfinite : 0 < ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v) := by
    apply Finset.prod_pos
    intro v hv
    have hq : 1 ≤ (Ideal.absNorm v.1.asIdeal : ℝ) := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.1).le
    have hqpow : 1 ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ (N v) := one_le_pow₀ hq
    have hvmajor : bridgeFinMajorant v.1 δ (N v) (y.1 v) = 1 := by
      simp [bridgeFinMajorant, habs v, hqpow]
    rw [hvmajor]
    norm_num
  have harch : 0 < ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w) := by
    apply Finset.prod_pos
    intro w hw
    exact bridgeComplexMajorant_pos δ hδ (y.2 w) (Set.mem_iInter.mp hyc w)
  unfold bridgeGlobalMajorant
  exact (mul_pos hfinite harch).ne'

private theorem bridgeGlobalMajorant_nonneg (δ : ℝ) (N : ∀ v : S.Sf, ℕ) (y : S.FS) :
    0 ≤ bridgeGlobalMajorant δ N y := by
  unfold bridgeGlobalMajorant
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro v hv
    have hq : 0 ≤ absFin v.1 (y.1 v) := by
      rw [A1.Theta.absFin_eq_norm]
      exact norm_nonneg _
    unfold bridgeFinMajorant
    split_ifs <;> positivity
  · apply Finset.prod_nonneg
    intro w hw
    have hq : 0 ≤ Complex.normSq (y.2 w) := Complex.normSq_nonneg _
    unfold bridgeComplexMajorant
    split_ifs <;> positivity

private theorem bridgeGlobalMajorant_integral_pos (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    0 < ∫ y, bridgeGlobalMajorant δ N y ∂(Theta.mulHaarS S μ) := by
  letI : Measure.IsOpenPosMeasure (Theta.mulHaarS S μ) := bridgeGlobalHaar_openPos
  have hInt := bridgeGlobalMajorant_integrable (S := S) (μ := μ) δ hδ N
  have hnonneg : ∀ y, 0 ≤ bridgeGlobalMajorant δ N y :=
    fun y => bridgeGlobalMajorant_nonneg δ N y
  obtain ⟨U, hUopen, hUne, hUpos⟩ :=
    bridgeGlobalMajorant_pos_on_open (S := S) δ hδ N
  have hsubset : U ⊆ Function.support (bridgeGlobalMajorant δ N) := by
    intro y hy
    exact hUpos y hy
  have hsupp : 0 < (Theta.mulHaarS S μ) (Function.support (bridgeGlobalMajorant δ N)) :=
    lt_of_lt_of_le (hUopen.measure_pos _ hUne) (measure_mono hsubset)
  exact (integral_pos_iff_support_of_nonneg hnonneg hInt).2 hsupp

private theorem bridgeGlobalMajorant_exists_sheet (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    ∃ x : ℝ, 0 < x ∧ Integrable (bridgeGlobalMajorant δ N) (G.sheet x) := by
  have hGlobalReal : Integrable (bridgeGlobalMajorant δ N) (Theta.mulHaarS S μ) :=
    bridgeGlobalMajorant_integrable (S := S) (μ := μ) δ hδ N
  have hGlobalComplex : Integrable (fun y => (bridgeGlobalMajorant δ N y : ℂ)) G.mul := by
    rw [G.mul_eq]
    exact (hGlobalReal.ofReal).smul_measure <| by
      apply ENNReal.inv_ne_top.mpr
      exact ENNReal.ofReal_ne_zero_iff.mpr Real.pi_pos
  have hbasePos := bridgeGlobalMajorant_integral_pos (S := S) (μ := μ) δ hδ N
  have hbaseIntComplex : Integrable (fun y => (bridgeGlobalMajorant δ N y : ℂ))
      (Theta.mulHaarS S μ) := hGlobalReal.ofReal
  have hbaseRe :
      (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂(Theta.mulHaarS S μ)).re =
        ∫ y, bridgeGlobalMajorant δ N y ∂(Theta.mulHaarS S μ) := by
    calc
      (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂(Theta.mulHaarS S μ)).re =
          ∫ y, Complex.re (bridgeGlobalMajorant δ N y : ℂ) ∂(Theta.mulHaarS S μ) :=
        (integral_re hbaseIntComplex).symm
      _ = ∫ y, bridgeGlobalMajorant δ N y ∂(Theta.mulHaarS S μ) := by simp
  have hbaseNe : (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂(Theta.mulHaarS S μ)) ≠ 0 := by
    intro hzero
    have hRe := congrArg Complex.re hzero
    rw [hbaseRe] at hRe
    exact hbasePos.ne' hRe
  have hc : ((ENNReal.ofReal Real.pi)⁻¹).toReal ≠ 0 := by
    have hpi0 : ENNReal.ofReal Real.pi ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr Real.pi_pos
    have hci0 : (ENNReal.ofReal Real.pi)⁻¹ ≠ 0 := by simp [hpi0]
    have hcitop : (ENNReal.ofReal Real.pi)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hpi0
    exact (ENNReal.toReal_pos hci0 hcitop).ne'
  have hscaled :
      (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂G.mul) =
        ((ENNReal.ofReal Real.pi)⁻¹).toReal •
          ∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂(Theta.mulHaarS S μ) := by
    rw [G.mul_eq, integral_smul_measure]
  have hGlobalNe :
      (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂G.mul) ≠ 0 := by
    rw [hscaled]
    simpa [smul_eq_mul] using
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) hbaseNe
  have hdis := G.disintegrate (fun y => (bridgeGlobalMajorant δ N y : ℂ)) hGlobalComplex
  rw [hdis] at hGlobalNe
  obtain ⟨x, hx, houter⟩ := exists_ne_zero_of_setIntegral_ne_zero hGlobalNe
  have hxpos : 0 < x := hx
  have hden : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hinner : (∫ y, (bridgeGlobalMajorant δ N y : ℂ) ∂G.sheet x) ≠ 0 :=
    (div_ne_zero_iff.mp houter).1
  have hComplexInt : Integrable (fun y => (bridgeGlobalMajorant δ N y : ℂ)) (G.sheet x) :=
    Integrable.of_integral_ne_zero hinner
  have hRealInt : Integrable (bridgeGlobalMajorant δ N) (G.sheet x) := by
    have hnorm := hComplexInt.norm
    have hEq : (fun y => ‖(bridgeGlobalMajorant δ N y : ℂ)‖) = bridgeGlobalMajorant δ N := by
      funext y
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact bridgeGlobalMajorant_nonneg δ N y
    rw [hEq] at hnorm
    exact hnorm
  exact ⟨x, hxpos, hRealInt⟩

private theorem bridgeGlobalMajorant_integrable_all (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    ∀ x : ℝ, 0 < x → Integrable (bridgeGlobalMajorant δ N) (G.sheet x) := by
  obtain ⟨t, ht, hbase⟩ := bridgeGlobalMajorant_exists_sheet (G := G) δ hδ N
  intro x hx
  let a : S.FSˣ := G.ellU x / G.ellU t
  have haFin : ∀ v : S.Sf, ((a : S.FS).1 v) = 1 := by
    intro v
    simp [a, G.ellU_val x hx, G.ellU_val t ht, SData.ell]
  obtain ⟨C, hC, hScale⟩ := bridgeGlobalMajorant_scale_oneFin δ hδ N a haFin
  have hcompInt : Integrable (fun y : S.FS => bridgeGlobalMajorant δ N ((a : S.FS) * y))
      (G.sheet t) := by
    apply (hbase.const_mul C).mono'
    · have hcompMeas : Measurable
          (fun y : S.FS => bridgeGlobalMajorant δ N ((a : S.FS) * y)) :=
        (bridgeGlobalMajorant_measurable δ N).comp (by fun_prop)
      exact hcompMeas.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (bridgeGlobalMajorant_nonneg δ N ((a : S.FS) * y))]
      exact hScale y
  rcases a2_bridge_NORM D S with ⟨_, _, _, _, hdiv, _⟩
  have haNorm : S.absS (a : S.FS) = x / t := by
    simpa [a, G.ellU_norm x hx, G.ellU_norm t ht] using hdiv (G.ellU x) (G.ellU t)
  have hratio : S.absS (a : S.FS) * t = x := by
    rw [haNorm]
    exact div_mul_cancel₀ x ht.ne'
  have htrans := G.sheet_translate a t ht
  rw [hratio] at htrans
  let φ : S.FS → S.FS := fun y => (a : S.FS) * y
  have hφ : Measurable φ := by fun_prop
  have hMMap : AEStronglyMeasurable (bridgeGlobalMajorant δ N)
      (Measure.map φ (G.sheet t)) :=
    (bridgeGlobalMajorant_measurable δ N).aestronglyMeasurable
  have hmapInt : Integrable (bridgeGlobalMajorant δ N) (Measure.map φ (G.sheet t)) :=
    (integrable_map_measure hMMap hφ.aemeasurable).2 hcompInt
  have htrans' : Measure.map φ (G.sheet t) = G.sheet x := by simpa [φ] using htrans
  rw [htrans'] at hmapInt
  exact hmapInt

private theorem bridgeRotatedAbs_bound_by_global (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    ∃ N : ∀ v : S.Sf, ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : S.FS, IsUnit y →
      bridgeRotatedAbsAll S J ff fc y ≤ C * bridgeGlobalMajorant δ N y := by
  classical
  have hfinExists : ∀ ℓ v, ∃ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ z, z ≠ 0 → ‖ff ℓ v z‖ ≤ c * bridgeFinMajorant v.1 δ n z := by
    intro ℓ v
    rcases bridgeFin_sheetHyp_radial_bound v.1 δ hδ (ff ℓ v) (hff ℓ v) with
      ⟨n, c, hc, hbound⟩
    exact ⟨n, c, hc, hbound⟩
  choose Nlv Clv hClv hflv using hfinExists
  have harchExists : ∀ ℓ w, ∃ c : ℝ, 0 ≤ c ∧
      ∀ z, z ≠ 0 → ‖fc ℓ w z‖ ≤ c * bridgeComplexMajorant δ z := by
    intro ℓ w
    exact bridgeSheetHypC_radial_bound δ hδ (fc ℓ w) (hfc ℓ w)
  choose Carch hCarch hfarch using harchExists
  let N : ∀ v : S.Sf, ℕ := fun v => Finset.univ.sup fun ℓ : Fin J => Nlv ℓ v
  let Bfin : Fin J → ℝ := fun ℓ => ∏ v : S.Sf, Clv ℓ v
  let Barch : Fin J → ℝ := fun ℓ => ∏ w : InfinitePlace F, Carch ℓ w
  let B : Fin J → ℝ := fun ℓ => Bfin ℓ * Barch ℓ
  let C : ℝ := ∑ ℓ : Fin J, B ℓ
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro ℓ hℓ
    apply mul_nonneg
    · dsimp [Bfin]
      apply Finset.prod_nonneg
      intro v hv
      exact hClv ℓ v
    · dsimp [Barch]
      apply Finset.prod_nonneg
      intro w hw
      exact hCarch ℓ w
  refine ⟨N, C, hCnonneg, ?_⟩
  intro y hy
  have hycoord : (∀ v : S.Sf, y.1 v ≠ 0) ∧ (∀ w : InfinitePlace F, y.2 w ≠ 0) := by
    simpa [Prod.isUnit_iff, Pi.isUnit_iff, isUnit_iff_ne_zero] using hy
  have hterm : ∀ ℓ : Fin J,
      (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) *
          ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖ ≤ B ℓ * bridgeGlobalMajorant δ N y := by
    intro ℓ
    let Qfin : ℝ := ∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)
    let Qarch : ℝ := ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w)
    have hQfin : 0 ≤ Qfin := by
      dsimp [Qfin]
      apply Finset.prod_nonneg
      intro v hv
      exact bridgeFinMajorant_nonneg v.1 δ (N v) (y.1 v)
    have hQarch : 0 ≤ Qarch := by
      dsimp [Qarch]
      apply Finset.prod_nonneg
      intro w hw
      exact bridgeComplexMajorant_nonneg δ (y.2 w)
    have hfin_le :
        (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) ≤ Bfin ℓ * Qfin := by
      calc
        (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) ≤
            ∏ v : S.Sf, Clv ℓ v * bridgeFinMajorant v.1 δ (N v) (y.1 v) := by
          apply Finset.prod_le_prod₀ (s := Finset.univ)
          · intro v hv
            exact norm_nonneg _
          · intro v hv
            have hN : Nlv ℓ v ≤ N v := by
              dsimp [N]
              exact Finset.le_sup (f := fun ℓ' : Fin J => Nlv ℓ' v)
                (Finset.mem_univ ℓ)
            have hlocal := hflv ℓ v (y.1 v) (hycoord.1 v)
            have hmono := bridgeFinMajorant_mono v.1 δ hN (y.1 v)
            exact hlocal.trans (mul_le_mul_of_nonneg_left hmono (hClv ℓ v))
        _ = Bfin ℓ * Qfin := by simp [Bfin, Qfin, Finset.prod_mul_distrib]
    have harch_le :
        (∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖) ≤ Barch ℓ * Qarch := by
      calc
        (∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖) ≤
            ∏ w : InfinitePlace F, Carch ℓ w * bridgeComplexMajorant δ (y.2 w) := by
          apply Finset.prod_le_prod₀ (s := Finset.univ)
          · intro w hw
            exact norm_nonneg _
          · intro w hw
            exact hfarch ℓ w (y.2 w) (hycoord.2 w)
        _ = Barch ℓ * Qarch := by simp [Barch, Qarch, Finset.prod_mul_distrib]
    have hA : 0 ≤ Bfin ℓ * Qfin := mul_nonneg (by
      dsimp [Bfin]
      apply Finset.prod_nonneg
      intro v hv
      exact hClv ℓ v) hQfin
    have hB : 0 ≤ ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖ := by positivity
    calc
      (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) *
        ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖ ≤
        (Bfin ℓ * Qfin) * (Barch ℓ * Qarch) :=
          mul_le_mul hfin_le harch_le hB hA
      _ = B ℓ * bridgeGlobalMajorant δ N y := by
        simp [B, Bfin, Barch, Qfin, Qarch, bridgeGlobalMajorant]
        ring
  calc
    bridgeRotatedAbsAll S J ff fc y =
        ∑ ℓ : Fin J,
          (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖ := rfl
    _ ≤ ∑ ℓ : Fin J, B ℓ * bridgeGlobalMajorant δ N y :=
      Finset.sum_le_sum fun ℓ hℓ => hterm ℓ
    _ = C * bridgeGlobalMajorant δ N y := by
      simp [C, Finset.sum_mul]

private theorem bridgeRotatedAbs_nonneg (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (y : S.FSˣ) :
    0 ≤ bridgeRotatedAbs S J ff fc y := by
  unfold bridgeRotatedAbs
  apply Finset.sum_nonneg
  intro ℓ hℓ
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro v hv
    exact norm_nonneg _
  · apply Finset.prod_nonneg
    intro w hw
    exact norm_nonneg _

/-- Absolute tensors are integrable on each positive sheet.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses local hypotheses and the sheet parametrization. -/
theorem a2_bridge_ANALYSIS (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    ∀ x : ℝ, 0 < x →
      Integrable (onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ))) (G.sheet x) := by
  classical
  intro x hx
  obtain ⟨N, C, hC, hbound⟩ := bridgeRotatedAbs_bound_by_global δ hδ J ff fc hff hfc
  have hrad : Integrable (bridgeGlobalMajorant δ N) (G.sheet x) :=
    bridgeGlobalMajorant_integrable_all (G := G) δ hδ N x hx
  have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
    (G.sheet_support x hx).mono fun _ hy => hy.1
  have hmeasReal : Measurable (bridgeRotatedAbsAll S J ff fc) :=
    bridgeRotatedAbsAll_measurable δ J ff fc hff hfc
  have hmeas : Measurable (fun y : S.FS => (bridgeRotatedAbsAll S J ff fc y : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hmeasReal
  have hAE :
      onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
        fun y : S.FS => (bridgeRotatedAbsAll S J ff fc y : ℂ) := by
    filter_upwards [hunit] with y hy
    simp [onUnits, bridgeRotatedAbs, bridgeRotatedAbsAll, hy]
  have htargetAEStrong :
      AEStronglyMeasurable
        (onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ))) (G.sheet x) :=
    hmeas.aestronglyMeasurable.congr hAE.symm
  have hdom : ∀ᵐ y ∂(G.sheet x),
      ‖onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y‖ ≤
        C * bridgeGlobalMajorant δ N y := by
    filter_upwards [hunit] with y hy
    have hpoint := hbound y hy
    have hnonneg := bridgeRotatedAbs_nonneg J ff fc hy.unit
    have hval : bridgeRotatedAbs S J ff fc hy.unit = bridgeRotatedAbsAll S J ff fc y := by
      simp [bridgeRotatedAbs, bridgeRotatedAbsAll, hy.unit_spec]
    rw [show onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y =
      (bridgeRotatedAbs S J ff fc hy.unit : ℂ) by simp [onUnits, hy]]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, hval]
    exact hpoint
  exact (hrad.const_mul C).mono' htargetAEStrong hdom

/-- Each tensor multiplied by an admissible bounded S-character/class multiplier is integrable.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses ANALYSIS and Theta.SheetMultiplier. -/
theorem a2_bridge_ANALYSIS_tensor (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∀ (ℓ : Fin J) (x : ℝ), 0 < x →
      Integrable (onUnits (fun y => m y *
        (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
        ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))) (G.sheet x) := by
  classical
  intro ℓ x hx
  obtain ⟨C, hC, hmbound⟩ := bridgeSheetMultiplier_bound m hm
  have habs := a2_bridge_ANALYSIS (G := G) δ hδ J ff fc hff hfc x hx
  have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
    (G.sheet_support x hx).mono fun _ hy => hy.1
  let factors : S.FSˣ → ℂ := fun y =>
    (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
      ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)
  have hfactors : Measurable factors := by
    dsimp [factors]
    apply Measurable.mul
    · apply Finset.univ.measurable_fun_prod
      intro v hv
      have hlocal := bridgeSheetHypFin_measurable v.1 δ (ff ℓ v) (hff ℓ v)
      exact hlocal.comp ((measurable_pi_apply v).comp
        (measurable_fst.comp (comap_measurable Units.val)))
    · apply Finset.univ.measurable_fun_prod
      intro w hw
      have hlocal := bridgeSheetHypC_measurable δ (fc ℓ w) (hfc ℓ w)
      exact hlocal.comp ((measurable_pi_apply w).comp
        (measurable_snd.comp (comap_measurable Units.val)))
  let f : S.FSˣ → ℂ := fun y => m y * factors y
  have hf : Measurable f := by
    dsimp [f]
    exact (bridgeSheetMultiplier_measurable G m hm).mul hfactors
  have hUnitsEmb : MeasurableEmbedding (Units.val : S.FSˣ → S.FS) :=
    bridgeFS_units_val_measurableEmbedding
  have hExtMeas : Measurable (Function.extend Units.val f (fun _ => (0 : ℂ))) :=
    hUnitsEmb.measurable_extend hf measurable_const
  have hEq : onUnits f = Function.extend Units.val f (fun _ => (0 : ℂ)) := by
    funext y
    by_cases hy : IsUnit y
    · have hleft : onUnits f y = f hy.unit := by simp [onUnits, hy]
      rw [hleft]
      have hval : (hy.unit : S.FS) = y := hy.unit_spec
      calc
        f hy.unit = Function.extend Units.val f (fun _ => 0) (hy.unit : S.FS) :=
          (Units.val_injective.extend_apply f (fun _ => 0) hy.unit).symm
        _ = Function.extend Units.val f (fun _ => 0) y := by rw [hval]
    · have hnot : ¬∃ u : S.FSˣ, (u : S.FS) = y := by
        rintro ⟨u, rfl⟩
        exact hy u.isUnit
      simp [onUnits, hy, Function.extend_apply', hnot]
  have htargetMeas : Measurable (onUnits f) := by rw [hEq]; exact hExtMeas
  have htarget' : AEStronglyMeasurable (onUnits f) (G.sheet x) :=
    htargetMeas.aestronglyMeasurable
  have hTargetEq : onUnits (fun y : S.FSˣ =>
      (m y * (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v))) *
        ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)) = onUnits f := by
    funext y
    by_cases hy : IsUnit (y : S.FS)
    · simp [onUnits, hy, f, factors, mul_assoc]
    · simp [onUnits, hy]
  have htarget : AEStronglyMeasurable
      (onUnits (fun y : S.FSˣ =>
        (m y * (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v))) *
          ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))) (G.sheet x) := by
    rw [hTargetEq]
    exact htarget'
  have hpoint (u : S.FSˣ) :
      ‖m u * (∏ v : S.Sf, ff ℓ v ((u : S.FS).1 v)) *
          ∏ w : InfinitePlace F, fc ℓ w ((u : S.FS).2 w)‖ ≤
        C * bridgeRotatedAbs S J ff fc u := by
    have hterm :
        ‖(∏ v : S.Sf, ff ℓ v ((u : S.FS).1 v)) *
            ∏ w : InfinitePlace F, fc ℓ w ((u : S.FS).2 w)‖ =
          (∏ v : S.Sf, ‖ff ℓ v ((u : S.FS).1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w ((u : S.FS).2 w)‖ := by
      simp only [norm_mul, norm_prod]
    have hsum :
        (∏ v : S.Sf, ‖ff ℓ v ((u : S.FS).1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w ((u : S.FS).2 w)‖ ≤
          bridgeRotatedAbs S J ff fc u := by
      unfold bridgeRotatedAbs
      exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin J =>
        (∏ v : S.Sf, ‖ff i v ((u : S.FS).1 v)‖) *
          ∏ w : InfinitePlace F, ‖fc i w ((u : S.FS).2 w)‖)
        (by intro i hi; positivity) (Finset.mem_univ ℓ)
    calc
      _ = ‖m u‖ * ‖(∏ v : S.Sf, ff ℓ v ((u : S.FS).1 v)) *
            ∏ w : InfinitePlace F, fc ℓ w ((u : S.FS).2 w)‖ := by
        simp only [norm_mul, norm_prod]
        ring
      _ ≤ C * ((∏ v : S.Sf, ‖ff ℓ v ((u : S.FS).1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w ((u : S.FS).2 w)‖) := by
        rw [hterm]
        exact mul_le_mul_of_nonneg_right (hmbound u) (by positivity)
      _ ≤ C * bridgeRotatedAbs S J ff fc u :=
        mul_le_mul_of_nonneg_left hsum hC
  have hdom : ∀ᵐ y ∂(G.sheet x), ‖onUnits f y‖ ≤
      C * ‖onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y‖ := by
    filter_upwards [hunit] with y hy
    rw [show onUnits f y = f hy.unit by simp [onUnits, hy, f, factors]]
    rw [show onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y =
      (bridgeRotatedAbs S J ff fc hy.unit : ℂ) by simp [onUnits, hy]]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (bridgeRotatedAbs_nonneg J ff fc hy.unit)]
    simpa [f, factors, mul_assoc] using hpoint hy.unit
  have hdom' : ∀ᵐ y ∂(G.sheet x),
      ‖onUnits (fun y : S.FSˣ =>
        (m y * (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v))) *
          ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)) y‖ ≤
        C * ‖onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y‖ :=
    hdom.mono fun y hy => by simpa only [hTargetEq] using hy
  exact ((habs.norm).const_mul C).mono' htarget hdom'

private theorem bridgeSheetPoint_measurable :
    Measurable (fun z : (Set.Ioi (0 : ℝ) ×
        ((∀ v : S.Sf, v.1.adicCompletion F) ×
          ({w : InfinitePlace F // w ≠ v0} → ℂ))) × ℝ =>
      Theta.sheetPoint S v0 z.1.1 z.1.2 z.2) := by
  classical
  let P0 := (∀ v : S.Sf, v.1.adicCompletion F) ×
    ({w : InfinitePlace F // w ≠ v0} → ℂ)
  let A := (Set.Ioi (0 : ℝ) × P0) × ℝ
  let den : A → ℝ := fun z =>
    (∏ v : S.Sf, absFin v.1 (z.1.2.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (z.1.2.2 w)
  have hfinite : Measurable (fun z : A => z.1.2.1) := by
    apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply v).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have harch : Measurable (fun z : A => z.1.2.2) := by
    apply measurable_pi_iff.mpr
    intro w
    exact (measurable_pi_apply w).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hden : Measurable den := by
    dsimp [den]
    apply Measurable.mul
    · apply Finset.univ.measurable_fun_prod
      intro v hv
      have hcoord : Measurable (fun z : A => z.1.2.1 v) :=
        (measurable_pi_apply v).comp hfinite
      have hn : Measurable (fun z : A => ‖z.1.2.1 v‖) :=
        continuous_norm.measurable.comp hcoord
      convert hn using 1
      funext z
      rw [A1.Theta.absFin_eq_norm]
    · apply Finset.univ.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp harch)
  have hx : Measurable (fun z : A => (z.1.1 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  have hquot : Measurable (fun z : A => (z.1.1 : ℝ) / den z) := by
    have hmul := hx.mul (measurable_inv.comp hden)
    convert hmul using 1
    funext z
    simp [div_eq_mul_inv]
  have hroot : Measurable (fun z : A => (Real.sqrt ((z.1.1 : ℝ) / den z) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp hquot)
  have hθ : Measurable (fun z : A => (z.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_snd
  have hphase : Measurable (fun z : A => (2 * Real.pi * Complex.I) * (z.2 : ℂ)) :=
    measurable_const.mul hθ
  have hexp : Measurable (fun z : A => Complex.exp ((2 * Real.pi * Complex.I) * (z.2 : ℂ))) :=
    Complex.continuous_exp.measurable.comp hphase
  have hfinite' : Measurable (fun z : A =>
      (fun v : S.Sf => z.1.2.1 v)) := by
    exact hfinite
  have harch' : Measurable (fun z : A => fun w : InfinitePlace F =>
      if hw : w = v0 then
        (Real.sqrt ((z.1.1 : ℝ) / den z) : ℂ) *
          Complex.exp ((2 * Real.pi * Complex.I) * (z.2 : ℂ))
      else z.1.2.2 ⟨w, hw⟩) := by
    apply measurable_pi_iff.mpr
    intro w
    by_cases hw : w = v0
    · subst w
      convert hroot.mul hexp using 1
      funext z
      simp
    · convert (measurable_pi_apply (⟨w, hw⟩ : {w : InfinitePlace F // w ≠ v0})).comp harch using 1
      funext z
      simp [hw]
  have hprod : Measurable (fun z : A =>
      ((fun v : S.Sf => z.1.2.1 v), fun w : InfinitePlace F =>
        if hw : w = v0 then
          (Real.sqrt ((z.1.1 : ℝ) / den z) : ℂ) *
            Complex.exp ((2 * Real.pi * Complex.I) * (z.2 : ℂ))
        else z.1.2.2 ⟨w, hw⟩)) := hfinite'.prodMk harch'
  have hEq (z : A) :
      ((fun v : S.Sf => z.1.2.1 v), fun w : InfinitePlace F =>
        if hw : w = v0 then
          (Real.sqrt ((z.1.1 : ℝ) / den z) : ℂ) *
            Complex.exp ((2 * Real.pi * Complex.I) * (z.2 : ℂ))
        else z.1.2.2 ⟨w, hw⟩) = Theta.sheetPoint S v0 z.1.1 z.1.2 z.2 := by
    rfl
  convert hprod using 1
  funext z
  exact (hEq z).symm

private theorem bridgeProfileAbs_measurable (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    Measurable (fun x : Set.Ioi (0 : ℝ) => bridgeProfileAbs G J ff fc x) := by
  classical
  let P := (∀ v : S.Sf, v.1.adicCompletion F) ×
    ({w : InfinitePlace F // w ≠ v0} → ℂ)
  let ν : Measure P :=
    (Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)
  let νθ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let joint : ((Set.Ioi (0 : ℝ) × P) × ℝ) → ℂ := fun z =>
    (bridgeRotatedAbsAll S J ff fc
      (Theta.sheetPoint S v0 z.1.1 z.1.2 z.2) : ℂ)
  haveI (v : S.Sf) : SigmaCompactSpace (v.1.adicCompletion F) := inferInstance
  haveI (v : S.Sf) : SigmaFinite (μ v.1).μ := inferInstance
  haveI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) := by
    intro v
    dsimp [Theta.mulHaarFin]
    infer_instance
  haveI : ∀ w : {w : InfinitePlace F // w ≠ v0}, SigmaFinite Theta.mulHaarC := by
    intro w
    dsimp [Theta.mulHaarC]
    infer_instance
  have hjoint : Measurable joint := by
    dsimp [joint]
    exact Complex.continuous_ofReal.measurable.comp
      ((bridgeRotatedAbsAll_measurable δ J ff fc hff hfc).comp
        bridgeSheetPoint_measurable)
  haveI : SigmaFinite ν := by dsimp [ν]; infer_instance
  haveI : SFinite ν := inferInstance
  haveI : SigmaFinite νθ := by dsimp [νθ]; infer_instance
  haveI : SFinite νθ := inferInstance
  have hJointSM : StronglyMeasurable joint := hjoint.stronglyMeasurable
  have hInnerSM : StronglyMeasurable
      (fun z : Set.Ioi (0 : ℝ) × P => ∫ θ, joint (z, θ) ∂νθ) :=
    hJointSM.integral_prod_right'
  have hOuterSM : StronglyMeasurable
      (fun x : Set.Ioi (0 : ℝ) => ∫ p, ∫ θ, joint ((x, p), θ) ∂νθ ∂ν) :=
    hInnerSM.integral_prod_right'
  let raw : S.FS → ℂ := fun y => (bridgeRotatedAbsAll S J ff fc y : ℂ)
  have hProfileEq (x : Set.Ioi (0 : ℝ)) :
      bridgeProfileAbs G J ff fc x =
        (∫ p, ∫ θ, joint ((x, p), θ) ∂νθ ∂ν).re := by
    have habs := a2_bridge_ANALYSIS (G := G) δ hδ J ff fc hff hfc x.val x.property
    have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
      (G.sheet_support x x.property).mono fun _ hy => hy.1
    have hAE : onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
        raw := by
      filter_upwards [hunit] with y hy
      simp [onUnits, bridgeRotatedAbs, bridgeRotatedAbsAll, raw, hy]
    have hraw : Integrable raw (G.sheet x) := habs.congr hAE
    have hInt :
        (∫ y, onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y ∂G.sheet x) =
          ∫ y, raw y ∂G.sheet x := integral_congr_ae hAE
    have hSheet := G.sheetInt_eq x x.property raw hraw
    rw [bridgeProfileAbs, bridgeSheetIntegral, hInt, hSheet]
    simp only [Theta.sheetInt, joint, raw, ν, νθ]
    rfl
  have hMeas : Measurable (fun x : Set.Ioi (0 : ℝ) =>
      (∫ p, ∫ θ, joint ((x, p), θ) ∂νθ ∂ν).re) := by
    exact Complex.continuous_re.measurable.comp hOuterSM.measurable
  have heq : (fun x : Set.Ioi (0 : ℝ) => bridgeProfileAbs G J ff fc x) =
      fun x => (∫ p, ∫ θ, joint ((x, p), θ) ∂νθ ∂ν).re := funext hProfileEq
  rw [heq]
  exact hMeas

private theorem bridgeProfileAbs_eq_absProfile (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) (x : ℝ) (hx : 0 < x) :
    bridgeProfileAbs G J ff fc x = A1.Theta.absProfile S μ v0 J ff fc 0 x := by
  classical
  let term : Fin J → S.FS → ℝ := fun ℓ y =>
    (∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖) *
      ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖
  let raw : S.FS → ℂ := fun y => (∑ ℓ : Fin J, term ℓ y : ℂ)
  have haggMeas : Measurable (bridgeRotatedAbsAll S J ff fc) :=
    bridgeRotatedAbsAll_measurable δ J ff fc hff hfc
  have htermMeas (ℓ : Fin J) : Measurable (term ℓ) := by
    dsimp [term]
    apply Measurable.mul
    · apply Finset.univ.measurable_fun_prod
      intro v hv
      exact (continuous_norm.measurable.comp
        ((bridgeSheetHypFin_measurable v.1 δ (ff ℓ v) (hff ℓ v)).comp
          ((measurable_pi_apply v).comp measurable_fst)))
    · apply Finset.univ.measurable_fun_prod
      intro w hw
      exact (continuous_norm.measurable.comp
        ((bridgeSheetHypC_measurable δ (fc ℓ w) (hfc ℓ w)).comp
          ((measurable_pi_apply w).comp measurable_snd)))
  have haggEq : bridgeRotatedAbsAll S J ff fc = fun y => ∑ ℓ : Fin J, term ℓ y := by
    funext y
    rfl
  have hAE : onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
      raw := by
    have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
      (G.sheet_support x hx).mono fun _ hy => hy.1
    filter_upwards [hunit] with y hy
    simp [onUnits, bridgeRotatedAbs, bridgeRotatedAbsAll, raw, term, hy]
  have haggInt : Integrable raw (G.sheet x) := by
    have h := a2_bridge_ANALYSIS (G := G) δ hδ J ff fc hff hfc x hx
    have hAEagg : onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
        fun y => (bridgeRotatedAbsAll S J ff fc y : ℂ) := by
      simpa [raw, haggEq] using hAE
    have h' : Integrable (fun y => (bridgeRotatedAbsAll S J ff fc y : ℂ)) (G.sheet x) :=
      h.congr hAEagg
    simpa [raw, haggEq] using h'
  have htermInt (ℓ : Fin J) : Integrable (fun y => (term ℓ y : ℂ)) (G.sheet x) := by
    have hsum : ∀ y, term ℓ y ≤ bridgeRotatedAbsAll S J ff fc y := by
      intro y
      rw [haggEq]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun i => term i y)
        (by
          intro i hi
          dsimp [term]
          positivity) (Finset.mem_univ ℓ)
    have hdom : ∀ y, ‖(term ℓ y : ℂ)‖ ≤ ‖raw y‖ := by
      intro y
      have hterm_nonneg : 0 ≤ term ℓ y := by positivity
      have hsum_nonneg : 0 ≤ ∑ i : Fin J, term i y :=
        Finset.sum_nonneg fun i hi => by dsimp [term]; positivity
      calc
        ‖(term ℓ y : ℂ)‖ = term ℓ y := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
        _ ≤ ∑ i : Fin J, term i y := by simpa [haggEq] using hsum y
        _ = ‖raw y‖ := by
          have hcast : (∑ i : Fin J, (term i y : ℂ)) =
              (∑ i : Fin J, term i y : ℝ) := by push_cast; rfl
          change (∑ i : Fin J, term i y) =
            ‖(∑ i : Fin J, (term i y : ℂ))‖
          rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    have ht : AEStronglyMeasurable (fun y => (term ℓ y : ℂ)) (G.sheet x) :=
      (Complex.continuous_ofReal.measurable.comp (htermMeas ℓ)).aestronglyMeasurable
    exact haggInt.norm.mono' ht (Filter.Eventually.of_forall hdom)
  have hsumInt :
      (∫ y, raw y ∂G.sheet x) =
        ∑ ℓ : Fin J, ∫ y, (term ℓ y : ℂ) ∂G.sheet x := by
    change (∫ y, (∑ ℓ : Fin J, (term ℓ y : ℂ)) ∂G.sheet x) = _
    exact integral_finsetSum Finset.univ (by intro ℓ hℓ; exact htermInt ℓ)
  have htermSheet (ℓ : Fin J) :
      (∫ y, (term ℓ y : ℂ) ∂G.sheet x) =
        A1.Theta.sheetInt S μ v0 (fun y => (term ℓ y : ℂ)) x :=
    G.sheetInt_eq x hx (fun y => (term ℓ y : ℂ)) (htermInt ℓ)
  have hBridge : bridgeProfileAbs G J ff fc x =
      (∫ y, raw y ∂G.sheet x).re := by
    unfold bridgeProfileAbs bridgeSheetIntegral
    rw [integral_congr_ae hAE]
  have hTermEq (ℓ : Fin J) (y : S.FS) :
      term ℓ y =
        (‖A1.normDeriv 0 (fc ℓ v0) (y.2 v0)‖ *
            ∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖) *
          ∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖ := by
    dsimp [term]
    have hp :
        ‖fc ℓ v0 (y.2 v0)‖ *
            ∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖ =
          ∏ w : InfinitePlace F, ‖fc ℓ w (y.2 w)‖ :=
      Finset.mul_prod_erase Finset.univ (fun w => ‖fc ℓ w (y.2 w)‖) (Finset.mem_univ v0)
    rw [← hp]
    simp [A1.normDeriv]
    ring
  have hMain : bridgeProfileAbs G J ff fc x =
      ∑ ℓ : Fin J,
        (A1.Theta.sheetInt S μ v0 (fun y => (term ℓ y : ℂ)) x).re := by
    rw [hBridge]
    calc
      (∫ y, raw y ∂G.sheet x).re =
          (∑ ℓ : Fin J, ∫ y, (term ℓ y : ℂ) ∂G.sheet x).re :=
        congrArg Complex.re hsumInt
      _ = ∑ ℓ : Fin J, (∫ y, (term ℓ y : ℂ) ∂G.sheet x).re := by
        rw [Complex.re_sum]
      _ = ∑ ℓ : Fin J,
          (A1.Theta.sheetInt S μ v0 (fun y => (term ℓ y : ℂ)) x).re := by
        simp_rw [htermSheet]
  rw [hMain]
  simp [A1.Theta.absProfile, hTermEq, Complex.ofReal_re]

private theorem bridgeProfileAbs_eq_integral (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) (x : ℝ) (hx : 0 < x) :
    bridgeProfileAbs G J ff fc x =
      ∫ y, bridgeRotatedAbsAll S J ff fc y ∂G.sheet x := by
  classical
  let raw : S.FS → ℂ := fun y => (bridgeRotatedAbsAll S J ff fc y : ℂ)
  have habs := a2_bridge_ANALYSIS (G := G) δ hδ J ff fc hff hfc x hx
  have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
    (G.sheet_support x hx).mono fun _ hy => hy.1
  have hAE : onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
      raw := by
    filter_upwards [hunit] with y hy
    simp [onUnits, bridgeRotatedAbs, bridgeRotatedAbsAll, raw, hy]
  have hraw : Integrable raw (G.sheet x) := habs.congr hAE
  unfold bridgeProfileAbs bridgeSheetIntegral
  calc
    (∫ y, onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) y ∂G.sheet x).re =
        (∫ y, raw y ∂G.sheet x).re := by congr 1; exact integral_congr_ae hAE
    _ = ∫ y, (raw y).re ∂G.sheet x := (integral_re hraw).symm
    _ = ∫ y, bridgeRotatedAbsAll S J ff fc y ∂G.sheet x := by simp [raw]

private theorem bridgeProfileH_measurable (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) (ℓ : Fin J) :
    Measurable (fun x : Set.Ioi (0 : ℝ) => bridgeProfileH G m J ff fc ℓ x) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let ff1 : Fin 1 → (v : S.Sf) → v.1.adicCompletion F → ℂ := fun _ => ff ℓ
  let fc1 : Fin 1 → InfinitePlace F → ℂ → ℂ := fun _ => fc ℓ
  have hff1 : ∀ i v, SheetHypFin v.1 δ (ff1 i v) := by
    intro i v
    exact hff ℓ v
  have hfc1 : ∀ i w, SheetHypC δ (fc1 i w) := by
    intro i w
    exact hfc ℓ w
  let Hf : ℝ → ℂ := A1.Theta.sheetInt S μ v0
    (fun y => onUnits m y * A1.Theta.sumProd S 1 ff1 fc1 y)
  have htheta := A1.Theta.sheet_profile S μ v0 δ hδ 1 ff1 fc1 hff1 hfc1
    (onUnits m) hm
  have hcont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hf (Set.Ioi 0) := by
    simpa [Hf] using htheta.1
  have hEq (x : Set.Ioi (0 : ℝ)) : bridgeProfileH G m J ff fc ℓ x = Hf x := by
    have hTensor := a2_bridge_ANALYSIS_tensor (G := G) δ hδ J ff fc hff hfc m hm ℓ x x.property
    have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
      (G.sheet_support x x.property).mono fun _ hy => hy.1
    let fUnit : S.FSˣ → ℂ := fun y => m y *
      (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
      ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)
    let fAll : S.FS → ℂ := fun y => onUnits m y * A1.Theta.sumProd S 1 ff1 fc1 y
    have hAE : onUnits fUnit =ᵐ[G.sheet x] fAll := by
      filter_upwards [hunit] with y hy
      simp [fUnit, fAll, onUnits, hy, A1.Theta.sumProd, ff1, fc1, mul_assoc]
    have hIntegrable : Integrable fAll (G.sheet x) := hTensor.congr hAE
    have hInt : (∫ y, onUnits fUnit y ∂G.sheet x) = ∫ y, fAll y ∂G.sheet x :=
      integral_congr_ae hAE
    unfold bridgeProfileH bridgeSheetIntegral Hf
    rw [hInt]
    exact G.sheetInt_eq x x.property fAll hIntegrable
  have heq : (fun x : Set.Ioi (0 : ℝ) => bridgeProfileH G m J ff fc ℓ x) =
      fun x : Set.Ioi (0 : ℝ) => Hf x := funext hEq
  rw [heq]
  exact hcont.continuousOn.restrict.measurable

private theorem bridgeProfileH_norm_bound (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : Fin J) (x : ℝ), 0 < x →
        ‖bridgeProfileH G m J ff fc ℓ x‖ ≤ C * bridgeProfileAbs G J ff fc x := by
  classical
  obtain ⟨C, hC, hmbound⟩ := bridgeSheetMultiplier_bound m hm
  refine ⟨C, hC, ?_⟩
  intro ℓ x hx
  let fUnit : S.FSˣ → ℂ := fun y => m y *
    (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
    ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)
  let raw : S.FS → ℂ := fun y => (bridgeRotatedAbsAll S J ff fc y : ℂ)
  have hTensor : Integrable (onUnits fUnit) (G.sheet x) := by
    exact a2_bridge_ANALYSIS_tensor (G := G) δ hδ J ff fc hff hfc m hm ℓ x hx
  have hunit : ∀ᵐ y ∂(G.sheet x), IsUnit y :=
    (G.sheet_support x hx).mono fun _ hy => hy.1
  have hRad := a2_bridge_ANALYSIS (G := G) δ hδ J ff fc hff hfc x hx
  have hAE : onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ)) =ᵐ[G.sheet x]
      raw := by
    filter_upwards [hunit] with y hy
    simp [onUnits, bridgeRotatedAbs, bridgeRotatedAbsAll, raw, hy]
  have hraw : Integrable raw (G.sheet x) := hRad.congr hAE
  have hAgg : Integrable (bridgeRotatedAbsAll S J ff fc) (G.sheet x) := by
    simpa [raw] using hraw.re
  have hdom : ∀ᵐ y ∂(G.sheet x),
      ‖onUnits fUnit y‖ ≤ C * bridgeRotatedAbsAll S J ff fc y := by
    filter_upwards [hunit] with y hy
    have hterm :
        (∏ v : S.Sf, ‖ff ℓ v ((hy.unit : S.FS).1 v)‖) *
          ∏ w : InfinitePlace F, ‖fc ℓ w ((hy.unit : S.FS).2 w)‖ ≤
        bridgeRotatedAbs S J ff fc hy.unit := by
      unfold bridgeRotatedAbs
      exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin J =>
        (∏ v : S.Sf, ‖ff i v ((hy.unit : S.FS).1 v)‖) *
          ∏ w : InfinitePlace F, ‖fc i w ((hy.unit : S.FS).2 w)‖)
        (by intro i hi; positivity) (Finset.mem_univ ℓ)
    have hval : bridgeRotatedAbs S J ff fc hy.unit = bridgeRotatedAbsAll S J ff fc y := by
      simp [bridgeRotatedAbs, bridgeRotatedAbsAll, hy.unit_spec]
    have hnorm : ‖fUnit hy.unit‖ = ‖m hy.unit‖ *
        ((∏ v : S.Sf, ‖ff ℓ v ((hy.unit : S.FS).1 v)‖) *
          ∏ w : InfinitePlace F, ‖fc ℓ w ((hy.unit : S.FS).2 w)‖) := by
      dsimp [fUnit]
      simp only [norm_mul, norm_prod]
      ring
    rw [show onUnits fUnit y = fUnit hy.unit by simp [onUnits, hy], hnorm]
    calc
      ‖m hy.unit‖ *
          ((∏ v : S.Sf, ‖ff ℓ v ((hy.unit : S.FS).1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w ((hy.unit : S.FS).2 w)‖) ≤
        C * ((∏ v : S.Sf, ‖ff ℓ v ((hy.unit : S.FS).1 v)‖) *
            ∏ w : InfinitePlace F, ‖fc ℓ w ((hy.unit : S.FS).2 w)‖) :=
          mul_le_mul_of_nonneg_right (hmbound hy.unit) (by positivity)
      _ ≤ C * bridgeRotatedAbs S J ff fc hy.unit :=
          mul_le_mul_of_nonneg_left hterm hC
      _ = C * bridgeRotatedAbsAll S J ff fc y := by rw [hval]
  have hmono :
      (∫ y, ‖onUnits fUnit y‖ ∂G.sheet x) ≤
        ∫ y, C * bridgeRotatedAbsAll S J ff fc y ∂G.sheet x :=
    integral_mono_ae hTensor.norm (hAgg.const_mul C) hdom
  have hProfileEq := bridgeProfileAbs_eq_integral G δ hδ J ff fc hff hfc x hx
  calc
    ‖bridgeProfileH G m J ff fc ℓ x‖ =
        ‖∫ y, onUnits fUnit y ∂G.sheet x‖ := rfl
    _ ≤ ∫ y, ‖onUnits fUnit y‖ ∂G.sheet x :=
      norm_integral_le_integral_norm (onUnits fUnit)
    _ ≤ ∫ y, C * bridgeRotatedAbsAll S J ff fc y ∂G.sheet x := hmono
    _ = C * bridgeProfileAbs G J ff fc x := by
      rw [integral_const_mul, ← hProfileEq]

/-- Convolution majorants exist as integrable functions before bounds on their integrals.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses ANALYSIS, ANALYSIS_tensor and all kernel moments. -/
theorem a2_bridge_ANALYSIS_convolution (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (K : ℝ → ℂ) (hKmeas : AEStronglyMeasurable K (volume.restrict (Set.Ioi (0 : ℝ))))
    (hK : ∀ β : ℝ, IntegrableOn (fun T : ℝ => ‖K T‖ * T ^ β / T) (Set.Ioi 0))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∀ x : ℝ, 0 < x →
      IntegrableOn (fun T : ℝ => ‖K T‖ * bridgeProfileAbs G J ff fc (x / T) / T) (Set.Ioi 0) ∧
      IntegrableOn (fun T : ℝ => ‖K T‖ * bridgeProfileAbs G J ff fc (x * T) / T) (Set.Ioi 0) ∧
      (∀ ℓ : Fin J,
          IntegrableOn (fun T : ℝ => K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ))
          (Set.Ioi 0)) := by
  classical
  intro x hx
  letI : IsTotallyComplex F := D.isTotallyComplex
  have htheta := A1.Theta.sheet_profile S μ v0 δ hδ J ff fc hff hfc (onUnits m) hm
  rcases htheta with ⟨_, htail⟩
  rcases htail with ⟨hfirst, _⟩
  rcases hfirst with ⟨Cm, hCm, hBounds⟩
  obtain ⟨Cprof, hGrowth⟩ := hBounds 0 0 (by linarith)
  have hProfileLe (u : ℝ) (hu : 0 < u) :
      bridgeProfileAbs G J ff fc u ≤ Cprof := by
    rw [bridgeProfileAbs_eq_absProfile G δ hδ J ff fc hff hfc u hu]
    have h := (hGrowth u hu).2
    simpa using h
  have hProfileNonneg (u : ℝ) (hu : 0 < u) :
      0 ≤ bridgeProfileAbs G J ff fc u := by
    rw [bridgeProfileAbs_eq_integral G δ hδ J ff fc hff hfc u hu]
    apply integral_nonneg
    intro y
    unfold bridgeRotatedAbsAll
    positivity
  have hCprof : 0 ≤ Cprof := (hProfileNonneg 1 one_pos).trans (hProfileLe 1 one_pos)
  let psub : Set.Ioi (0 : ℝ) → ℝ := fun u => bridgeProfileAbs G J ff fc u
  let pext : ℝ → ℝ := Function.extend (fun u : Set.Ioi (0 : ℝ) => (u : ℝ))
    psub (fun _ => 0)
  have hSubtypeEmb : MeasurableEmbedding (fun u : Set.Ioi (0 : ℝ) => (u : ℝ)) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hPsub : Measurable psub := by
    exact bridgeProfileAbs_measurable G δ hδ J ff fc hff hfc
  have hPext : Measurable pext := hSubtypeEmb.measurable_extend hPsub measurable_const
  have hPextAt (u : ℝ) (hu : 0 < u) : pext u = bridgeProfileAbs G J ff fc u := by
    have h := Subtype.val_injective.extend_apply psub (fun _ => 0) ⟨u, hu⟩
    simpa [pext, psub] using h
  have hDiv : Measurable (fun T : ℝ => x / T) := by
    have hconst : Measurable (fun _ : ℝ => x) := measurable_const
    have h := hconst.mul (measurable_inv : Measurable fun T : ℝ => T⁻¹)
    convert h using 1
    funext T
    simp [div_eq_mul_inv]
  have hMul : Measurable (fun T : ℝ => x * T) :=
    (measurable_const : Measurable fun _ : ℝ => x).mul measurable_id
  have hFactorInv : Measurable (fun T : ℝ => pext (x / T) / T) := by
    have h := (hPext.comp hDiv).mul (measurable_inv : Measurable fun T : ℝ => T⁻¹)
    convert h using 1
    funext T
    simp [div_eq_mul_inv]
  have hFactorFwd : Measurable (fun T : ℝ => pext (x * T) / T) := by
    have h := (hPext.comp hMul).mul (measurable_inv : Measurable fun T : ℝ => T⁻¹)
    convert h using 1
    funext T
    simp [div_eq_mul_inv]
  have hKzero : Integrable (fun T : ℝ => ‖K T‖ / T)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := hK 0
    change Integrable (fun T : ℝ => ‖K T‖ * T ^ (0 : ℝ) / T)
      (volume.restrict (Set.Ioi (0 : ℝ))) at h
    simpa using h
  let fInv : ℝ → ℝ := fun T => ‖K T‖ * bridgeProfileAbs G J ff fc (x / T) / T
  let fFwd : ℝ → ℝ := fun T => ‖K T‖ * bridgeProfileAbs G J ff fc (x * T) / T
  have hInvEq : fInv =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun T => ‖K T‖ * (pext (x / T) / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    rw [hPextAt (x / T) (div_pos hx hT)]
    dsimp [fInv]
    ring
  have hFwdEq : fFwd =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun T => ‖K T‖ * (pext (x * T) / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    rw [hPextAt (x * T) (mul_pos hx hT)]
    dsimp [fFwd]
    ring
  have hInvAESM : AEStronglyMeasurable fInv (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hKmeas.norm.mul hFactorInv.aestronglyMeasurable).congr hInvEq.symm
  have hFwdAESM : AEStronglyMeasurable fFwd (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hKmeas.norm.mul hFactorFwd.aestronglyMeasurable).congr hFwdEq.symm
  have hInvDom : ∀ᵐ T ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖fInv T‖ ≤ Cprof * (‖K T‖ / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTpos : 0 < T := hT
    have hu : 0 < x / T := div_pos hx hTpos
    have hp0 := hProfileNonneg (x / T) hu
    have hpC := hProfileLe (x / T) hu
    have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
    have hf0 : 0 ≤ fInv T := by dsimp [fInv]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    dsimp [fInv]
    rw [div_eq_mul_inv]
    calc
      ‖K T‖ * bridgeProfileAbs G J ff fc (x / T) * T⁻¹ ≤
          ‖K T‖ * Cprof * T⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpC (norm_nonneg _)) hTi
      _ = Cprof * (‖K T‖ / T) := by rw [div_eq_mul_inv]; ring
  have hFwdDom : ∀ᵐ T ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖fFwd T‖ ≤ Cprof * (‖K T‖ / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTpos : 0 < T := hT
    have hu : 0 < x * T := mul_pos hx hTpos
    have hp0 := hProfileNonneg (x * T) hu
    have hpC := hProfileLe (x * T) hu
    have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
    have hf0 : 0 ≤ fFwd T := by dsimp [fFwd]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    dsimp [fFwd]
    rw [div_eq_mul_inv]
    calc
      ‖K T‖ * bridgeProfileAbs G J ff fc (x * T) * T⁻¹ ≤
          ‖K T‖ * Cprof * T⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpC (norm_nonneg _)) hTi
      _ = Cprof * (‖K T‖ / T) := by rw [div_eq_mul_inv]; ring
  have hInv : IntegrableOn fInv (Set.Ioi (0 : ℝ)) := by
    change Integrable fInv (volume.restrict (Set.Ioi (0 : ℝ)))
    exact (hKzero.const_mul Cprof).mono' hInvAESM hInvDom
  have hFwd : IntegrableOn fFwd (Set.Ioi (0 : ℝ)) := by
    change Integrable fFwd (volume.restrict (Set.Ioi (0 : ℝ)))
    exact (hKzero.const_mul Cprof).mono' hFwdAESM hFwdDom
  refine ⟨hInv, hFwd, ?_⟩
  intro ℓ
  obtain ⟨Cb, hCb, hHbound⟩ :=
    bridgeProfileH_norm_bound G δ hδ J ff fc hff hfc m hm
  let Hsub : Set.Ioi (0 : ℝ) → ℂ := fun u => bridgeProfileH G m J ff fc ℓ u
  let Hext : ℝ → ℂ := Function.extend (fun u : Set.Ioi (0 : ℝ) => (u : ℝ))
    Hsub (fun _ => 0)
  have hHsub : Measurable Hsub := by
    exact bridgeProfileH_measurable G δ hδ J ff fc hff hfc m hm ℓ
  have hHext : Measurable Hext := hSubtypeEmb.measurable_extend hHsub measurable_const
  have hHextAt (u : ℝ) (hu : 0 < u) : Hext u = bridgeProfileH G m J ff fc ℓ u := by
    have h := Subtype.val_injective.extend_apply Hsub (fun _ => 0) ⟨u, hu⟩
    simpa [Hext, Hsub] using h
  have hDenom : Measurable (fun T : ℝ => (T : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_id
  have hHfactor : Measurable (fun T : ℝ => Hext (x / T) / (T : ℂ)) := by
    have h := (hHext.comp hDiv).mul (measurable_inv.comp hDenom)
    convert h using 1
    funext T
    simp [div_eq_mul_inv]
  have hHEq :
      (fun T : ℝ => K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ)) =ᵐ[
        volume.restrict (Set.Ioi (0 : ℝ))]
      fun T => K T * (Hext (x / T) / (T : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    rw [hHextAt (x / T) (div_pos hx hT)]
    ring
  have hComplexAESM : AEStronglyMeasurable
      (fun T : ℝ => K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hKmeas.mul hHfactor.aestronglyMeasurable).congr hHEq.symm
  have hComplexDom :
      ∀ᵐ T ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ)‖ ≤
          (Cb * Cprof) * (‖K T‖ / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTpos : 0 < T := hT
    have hu : 0 < x / T := div_pos hx hTpos
    have hHpoint : ‖bridgeProfileH G m J ff fc ℓ (x / T)‖ ≤
        Cb * bridgeProfileAbs G J ff fc (x / T) := hHbound ℓ (x / T) hu
    have hHconst : ‖bridgeProfileH G m J ff fc ℓ (x / T)‖ ≤ Cb * Cprof := by
      calc
        ‖bridgeProfileH G m J ff fc ℓ (x / T)‖ ≤
            Cb * bridgeProfileAbs G J ff fc (x / T) := hHpoint
        _ ≤ Cb * Cprof := mul_le_mul_of_nonneg_left (hProfileLe (x / T) hu) hCb
    have hTnorm : ‖(T : ℂ)‖ = T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    calc
      ‖K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ)‖ =
          ‖K T‖ * ‖bridgeProfileH G m J ff fc ℓ (x / T)‖ / T := by
        rw [norm_div, norm_mul, hTnorm]
      _ ≤ ‖K T‖ * (Cb * Cprof) / T := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hHconst (norm_nonneg _)
        · exact hTpos.le
      _ = (Cb * Cprof) * (‖K T‖ / T) := by ring
  change Integrable (fun T : ℝ =>
      K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  exact (hKzero.const_mul (Cb * Cprof)).mono' hComplexAESM hComplexDom

end ArtinPrimitiveRoots.A2
