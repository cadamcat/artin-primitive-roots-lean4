import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.FiniteRadial
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.LocalRadial

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Pointwise
noncomputable section

namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

def bridgeSheetGlobalMajorant (δ : ℝ) (N : ∀ v : S.Sf, ℕ) (y : S.FS) : ℝ :=
  (∏ v : S.Sf, bridgeFinMajorant v.1 δ (N v) (y.1 v)) *
    ∏ w : InfinitePlace F, bridgeComplexMajorant δ (y.2 w)

theorem bridgeSheetGlobalMajorant_nonneg (δ : ℝ) (N : ∀ v : S.Sf, ℕ)
    (y : S.FS) : 0 ≤ bridgeSheetGlobalMajorant (S := S) δ N y := by
  unfold bridgeSheetGlobalMajorant
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro v hv
    exact bridgeFinMajorant_nonneg v.1 δ (N v) (y.1 v)
  · apply Finset.prod_nonneg
    intro w hw
    exact bridgeComplexMajorant_nonneg δ (y.2 w)

private theorem bridgeSheetGlobalMajorant_measurable (δ : ℝ) (N : ∀ v : S.Sf, ℕ) :
    Measurable (bridgeSheetGlobalMajorant (S := S) δ N) := by
  unfold bridgeSheetGlobalMajorant
  apply Measurable.mul
  · apply Finset.univ.measurable_fun_prod
    intro v hv
    exact (bridgeFinMajorant_measurable v.1 δ (N v)).comp
      ((measurable_pi_apply v).comp measurable_fst)
  · apply Finset.univ.measurable_fun_prod
    intro w hw
    exact (bridgeComplexMajorant_measurable δ).comp
      ((measurable_pi_apply w).comp measurable_snd)

private theorem bridgeSheetGlobalHaar_openPos :
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

private theorem bridgeSheetGlobalMajorant_pos_on_open (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    ∃ U : Set S.FS, IsOpen U ∧ U.Nonempty ∧
      ∀ y ∈ U, bridgeSheetGlobalMajorant (S := S) δ N y ≠ 0 := by
  let Uf : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    ⋂ v : S.Sf, {y | dist (y v) (1 : v.1.adicCompletion F) < 1}
  let Uc : Set (InfinitePlace F → ℂ) :=
    ⋂ w : InfinitePlace F, {z | z w ≠ 0}
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
  unfold bridgeSheetGlobalMajorant
  exact (mul_pos hfinite harch).ne'

private theorem bridgeSheetGlobalMajorant_integrable (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    Integrable (bridgeSheetGlobalMajorant (S := S) δ N) (Theta.mulHaarS S μ) := by
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

private theorem bridgeSheetGlobalMajorant_integral_pos (δ : ℝ) (hδ : 0 < δ)
    (N : ∀ v : S.Sf, ℕ) :
    0 < ∫ y, bridgeSheetGlobalMajorant (S := S) δ N y ∂(Theta.mulHaarS S μ) := by
  letI : Measure.IsOpenPosMeasure (Theta.mulHaarS S μ) := bridgeSheetGlobalHaar_openPos
  have hInt := bridgeSheetGlobalMajorant_integrable (S := S) (μ := μ) δ hδ N
  have hnonneg : ∀ y, 0 ≤ bridgeSheetGlobalMajorant (S := S) δ N y :=
    fun y => bridgeSheetGlobalMajorant_nonneg (S := S) δ N y
  obtain ⟨U, hUopen, hUne, hUpos⟩ :=
    bridgeSheetGlobalMajorant_pos_on_open (S := S) δ hδ N
  have hsubset : U ⊆ Function.support (bridgeSheetGlobalMajorant (S := S) δ N) := by
    intro y hy
    exact hUpos y hy
  have hsupp : 0 < (Theta.mulHaarS S μ)
      (Function.support (bridgeSheetGlobalMajorant (S := S) δ N)) :=
    lt_of_lt_of_le (hUopen.measure_pos _ hUne) (measure_mono hsubset)
  exact (integral_pos_iff_support_of_nonneg hnonneg hInt).2 hsupp

theorem bridgeSheetGlobalMajorant_exists_sheet (G : SheetGeometry D S μ v0)
    (δ : ℝ) (hδ : 0 < δ) (N : ∀ v : S.Sf, ℕ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (bridgeSheetGlobalMajorant (S := S) δ N) (G.sheet t) := by
  have hGlobalReal : Integrable (bridgeSheetGlobalMajorant (S := S) δ N)
      (Theta.mulHaarS S μ) := bridgeSheetGlobalMajorant_integrable (S := S) (μ := μ) δ hδ N
  have hGlobalComplex : Integrable
      (fun y => (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)) G.mul := by
    rw [G.mul_eq]
    exact (hGlobalReal.ofReal).smul_measure <| by
      apply ENNReal.inv_ne_top.mpr
      exact ENNReal.ofReal_ne_zero_iff.mpr Real.pi_pos
  have hbasePos := bridgeSheetGlobalMajorant_integral_pos (S := S) (μ := μ) δ hδ N
  have hbaseIntComplex : Integrable
      (fun y => (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)) (Theta.mulHaarS S μ) :=
    hGlobalReal.ofReal
  have hbaseRe :
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂(Theta.mulHaarS S μ)).re =
        ∫ y, bridgeSheetGlobalMajorant (S := S) δ N y ∂(Theta.mulHaarS S μ) := by
    calc
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂(Theta.mulHaarS S μ)).re =
          ∫ y, Complex.re (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)
            ∂(Theta.mulHaarS S μ) := (integral_re hbaseIntComplex).symm
      _ = ∫ y, bridgeSheetGlobalMajorant (S := S) δ N y ∂(Theta.mulHaarS S μ) := by simp
  have hbaseNe :
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂(Theta.mulHaarS S μ)) ≠ 0 := by
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
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂G.mul) =
        ((ENNReal.ofReal Real.pi)⁻¹).toReal •
          ∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂(Theta.mulHaarS S μ) := by
    rw [G.mul_eq, integral_smul_measure]
  have hGlobalNe :
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂G.mul) ≠ 0 := by
    rw [hscaled]
    simpa [smul_eq_mul] using
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) hbaseNe
  have hdis := G.disintegrate
    (fun y => (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)) hGlobalComplex
  rw [hdis] at hGlobalNe
  obtain ⟨t, ht, houter⟩ := exists_ne_zero_of_setIntegral_ne_zero hGlobalNe
  have htpos : 0 < t := ht
  have hinner :
      (∫ y, (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ) ∂G.sheet t) ≠ 0 :=
    (div_ne_zero_iff.mp houter).1
  have hComplexInt : Integrable
      (fun y => (bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)) (G.sheet t) :=
    Integrable.of_integral_ne_zero hinner
  have hRealInt : Integrable (bridgeSheetGlobalMajorant (S := S) δ N) (G.sheet t) := by
    have hnorm := hComplexInt.norm
    have hEq : (fun y => ‖(bridgeSheetGlobalMajorant (S := S) δ N y : ℂ)‖) =
        bridgeSheetGlobalMajorant (S := S) δ N := by
      funext y
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact bridgeSheetGlobalMajorant_nonneg (S := S) δ N y
    rw [hEq] at hnorm
    exact hnorm
  exact ⟨t, htpos, hRealInt⟩

end ArtinPrimitiveRoots.A2
