import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.SelfDualMeasure
import ArtinPrimitiveRoots.A2.Reflection.Missing
import Mathlib.MeasureTheory.Measure.Haar.Unique

open NumberField IsDedekindDomain MeasureTheory
open Filter
open ArtinPrimitiveRoots A1 A2
open LineDeriv
open scoped FourierTransform RealInnerProductSpace
open scoped Topology
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_weights_p

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v}
variable {A : AddCharData F}

private noncomputable local instance instMeasurableFS (S : SData F CE condη) :
    MeasurableSpace S.FS := borel S.FS

private local instance instBorelFS (S : SData F CE condη) : BorelSpace S.FS := ⟨rfl⟩

private instance adicCompletion_separableSpace (v : FinPlace F) :
    TopologicalSpace.SeparableSpace (v.adicCompletion F) := by
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap (K := F))

private instance adicCompletion_secondCountable (v : FinPlace F) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable (v.adicCompletion F)

@[instance_reducible] private noncomputable def fsProductMeas (S : SData F CE condη) :
    MeasurableSpace S.FS := Prod.instMeasurableSpace

private theorem fsProductMeas_eq_borel (S : SData F CE condη) :
    fsProductMeas S = borel S.FS := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq

private noncomputable def fsULiftProductMeas (S : SData F CE condη) :
    MeasurableSpace (ULift.{0} S.FS) := @ULift.instMeasurableSpace S.FS (fsProductMeas S)

private noncomputable def fsUpAddEquiv (S : SData F CE condη) : S.FS ≃+ ULift.{0} S.FS where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl

private noncomputable def fsDownAddEquiv (S : SData F CE condη) : ULift.{0} S.FS ≃+ S.FS :=
  (fsUpAddEquiv S).symm

private theorem fsUpMeasurableProd (S : SData F CE condη) :
    @Measurable S.FS (ULift.{0} S.FS) (fsProductMeas S) (fsULiftProductMeas S) ULift.up := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  exact measurable_up

private theorem fsDownMeasurableProd (S : SData F CE condη) :
    @Measurable (ULift.{0} S.FS) S.FS (fsULiftProductMeas S) (fsProductMeas S) ULift.down := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  exact measurable_down

private noncomputable def fsUpProdMeasEquiv (S : SData F CE condη) :
    @MeasurableEquiv S.FS (ULift.{0} S.FS) (fsProductMeas S) (fsULiftProductMeas S) := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  exact @MeasurableEquiv.mk S.FS (ULift.{0} S.FS) (fsProductMeas S) (fsULiftProductMeas S)
    (fsUpAddEquiv S).toEquiv (fsUpMeasurableProd S) (fsDownMeasurableProd S)

private noncomputable def fsDownBorelMeasEquiv (S : SData F CE condη) :
    @MeasurableEquiv (ULift.{0} S.FS) S.FS (fsULiftProductMeas S) (borel S.FS) := by
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  letI : MeasurableSpace S.FS := borel S.FS
  have hEq := fsProductMeas_eq_borel S
  have hdown : @Measurable (ULift.{0} S.FS) S.FS (fsULiftProductMeas S)
      (borel S.FS) ULift.down := by
    apply Measurable.of_le_map
    change borel S.FS ≤ (fsULiftProductMeas S).map ULift.down
    calc
      _ = fsProductMeas S := hEq.symm
      _ ≤ _ := (fsDownMeasurableProd S).le_map
  have hup : @Measurable S.FS (ULift.{0} S.FS) (borel S.FS)
      (fsULiftProductMeas S) ULift.up := by
    apply Measurable.of_le_map
    change fsULiftProductMeas S ≤ (borel S.FS).map ULift.up
    calc
      _ ≤ (fsProductMeas S).map ULift.up := (fsUpMeasurableProd S).le_map
      _ = _ := congrArg (fun m => m.map ULift.up) hEq
  exact @MeasurableEquiv.mk (ULift.{0} S.FS) S.FS (fsULiftProductMeas S) (borel S.FS)
    (fsDownAddEquiv S).toEquiv hdown hup

private noncomputable def referenceAddHaarProd
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure S.FS (fsProductMeas S) :=
  (Measure.pi fun v : S.Sf => (μ v.1).μ).prod
    (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F))

private theorem referenceAddHaarProd_isHaar
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure.IsAddHaarMeasure S.FS inferInstance inferInstance (fsProductMeas S)
      (referenceAddHaarProd S μ) := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : BorelSpace S.FS := inferInstance
  letI : ∀ v : S.Sf, SigmaFinite ((μ v.1).μ) := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    letI : SigmaCompactSpace (v.1.adicCompletion F) := inferInstance
    infer_instance
  have hfin : Measure.IsAddHaarMeasure (Measure.pi fun v : S.Sf => (μ v.1).μ) :=
    inferInstance
  have harch : Measure.IsAddHaarMeasure
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : Measure.IsAddHaarMeasure (Measure.pi fun v : S.Sf => (μ v.1).μ) := hfin
  letI : Measure.IsAddHaarMeasure
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) := harch
  letI : SFinite (Measure.pi fun v : S.Sf => (μ v.1).μ) := inferInstance
  letI : SFinite
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) := by
    letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
    infer_instance
  exact Measure.prod.instIsAddHaarMeasure _ _

private noncomputable def fsProductBorelEquiv (S : SData F CE condη) :
    @MeasurableEquiv S.FS S.FS (fsProductMeas S) (borel S.FS) := by
  let hEq := fsProductMeas_eq_borel S
  have h₁ : @Measurable S.FS S.FS (fsProductMeas S) (borel S.FS) id := by
    apply Measurable.of_le_map
    change borel S.FS ≤ (fsProductMeas S).map id
    simpa only [MeasurableSpace.map_id] using hEq.symm.le
  have h₂ : @Measurable S.FS S.FS (borel S.FS) (fsProductMeas S) id := by
    apply Measurable.of_le_map
    change fsProductMeas S ≤ (borel S.FS).map id
    simpa only [MeasurableSpace.map_id] using hEq.le
  exact @MeasurableEquiv.mk S.FS S.FS (fsProductMeas S) (borel S.FS)
    (Equiv.refl S.FS) h₁ h₂

private noncomputable def referenceAddHaarUp
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure (ULift.{0} S.FS) (fsULiftProductMeas S) :=
  @Measure.map S.FS (ULift.{0} S.FS) (fsProductMeas S) (fsULiftProductMeas S)
    (fsUpProdMeasEquiv S) (referenceAddHaarProd S μ)

private noncomputable def referenceAddHaar
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure S.FS (borel S.FS) :=
  @Measure.map (ULift.{0} S.FS) S.FS (fsULiftProductMeas S) (borel S.FS)
    (fsDownBorelMeasEquiv S) (referenceAddHaarUp S μ)

private theorem referenceAddHaarUp_isHaar
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure.IsAddHaarMeasure (ULift.{0} S.FS) inferInstance inferInstance
      (fsULiftProductMeas S) (referenceAddHaarUp S μ) := by
  letI : MeasurableSpace S.FS := fsProductMeas S
  letI : BorelSpace S.FS := ⟨fsProductMeas_eq_borel S⟩
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  letI : BorelSpace (ULift.{0} S.FS) := ULift.instBorelSpace
  letI : Measure.IsAddHaarMeasure (referenceAddHaarProd S μ) :=
    referenceAddHaarProd_isHaar S μ
  have h := (fsUpAddEquiv S).isAddHaarMeasure_map (referenceAddHaarProd S μ)
    (by change Continuous (fun x : S.FS => ULift.up x); fun_prop)
    (by change Continuous (fun x : ULift.{0} S.FS => ULift.down x); fun_prop)
  simpa [referenceAddHaarUp, fsUpProdMeasEquiv, fsUpAddEquiv] using h

private theorem referenceAddHaar_isHaar
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v) :
    @Measure.IsAddHaarMeasure S.FS inferInstance inferInstance (borel S.FS)
      (referenceAddHaar S μ) := by
  letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
  letI : BorelSpace (ULift.{0} S.FS) := by
    letI : MeasurableSpace S.FS := fsProductMeas S
    letI : BorelSpace S.FS := ⟨fsProductMeas_eq_borel S⟩
    exact ULift.instBorelSpace
  letI : Measure.IsAddHaarMeasure (referenceAddHaarUp S μ) :=
    referenceAddHaarUp_isHaar S μ
  have h := (fsDownAddEquiv S).isAddHaarMeasure_map
    (referenceAddHaarUp S μ)
    (by change Continuous (fun x : ULift.{0} S.FS => ULift.down x); fun_prop)
    (by change Continuous (fun x : S.FS => ULift.up x); fun_prop)
  simpa [referenceAddHaar, fsDownBorelMeasEquiv, fsDownAddEquiv] using h

private theorem integral_addHaarScalarFactor_complex
    {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasurableSpace E] [BorelSpace E] [LocallyCompactSpace E]
    (μ' μ : Measure E) [μ'.IsAddHaarMeasure] [μ.IsAddHaarMeasure]
    (f : E → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ x, f x ∂μ' =
      ((Measure.addHaarScalarFactor μ' μ).toReal : ℂ) * ∫ x, f x ∂μ := by
  let c : ℝ := (Measure.addHaarScalarFactor μ' μ : ℝ)
  have hfRe : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf
  have hfIm : Continuous (fun x => (f x).im) := Complex.continuous_im.comp hf
  have hfcRe : HasCompactSupport (fun x => (f x).re) := by
    apply hfc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal
    · intro x hx
      have hfx : f x ≠ 0 := by
        intro hzero
        exact (Function.mem_support.mp hx) (by simp [hzero])
      exact subset_closure (Function.mem_support.mpr hfx)
    · exact isClosed_tsupport _
  have hfcIm : HasCompactSupport (fun x => (f x).im) := by
    apply hfc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal
    · intro x hx
      have hfx : f x ≠ 0 := by
        intro hzero
        exact (Function.mem_support.mp hx) (by simp [hzero])
      exact subset_closure (Function.mem_support.mpr hfx)
    · exact isClosed_tsupport _
  have hRe0 := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
    μ' μ hfRe hfcRe
  rw [MeasureTheory.integral_smul_nnreal_measure] at hRe0
  have hRe :
      (∫ x, (f x).re ∂μ') = c * ∫ x, (f x).re ∂μ := by
    simpa [c, smul_eq_mul, NNReal.smul_def] using hRe0
  have hIm0 := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
    μ' μ hfIm hfcIm
  rw [MeasureTheory.integral_smul_nnreal_measure] at hIm0
  have hIm :
      (∫ x, (f x).im ∂μ') = c * ∫ x, (f x).im ∂μ := by
    simpa [c, smul_eq_mul, NNReal.smul_def] using hIm0
  have hInt' : Integrable f μ' := hf.integrable_of_hasCompactSupport hfc
  have hInt : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  have hReComm' := Complex.reCLM.integral_comp_comm hInt'
  have hReComm := Complex.reCLM.integral_comp_comm hInt
  have hImComm' := Complex.imCLM.integral_comp_comm hInt'
  have hImComm := Complex.imCLM.integral_comp_comm hInt
  have hReT : (∫ x, f x ∂μ').re = c * (∫ x, f x ∂μ).re := by
    calc
      (∫ x, f x ∂μ').re = ∫ x, (f x).re ∂μ' := by
        simpa only [Complex.reCLM_apply] using hReComm'.symm
      _ = c * ∫ x, (f x).re ∂μ := hRe
      _ = c * (∫ x, f x ∂μ).re := by
        simpa only [Complex.reCLM_apply] using congrArg (fun r : ℝ => c * r) hReComm
  have hImT : (∫ x, f x ∂μ').im = c * (∫ x, f x ∂μ).im := by
    calc
      (∫ x, f x ∂μ').im = ∫ x, (f x).im ∂μ' := by
        simpa only [Complex.imCLM_apply] using hImComm'.symm
      _ = c * ∫ x, (f x).im ∂μ := hIm
      _ = c * (∫ x, f x ∂μ).im := by
        simpa only [Complex.imCLM_apply] using congrArg (fun r : ℝ => c * r) hImComm
  apply Complex.ext
  · simpa [c, Complex.mul_re] using hReT
  · simpa [c, Complex.mul_im] using hImT

private theorem finitePsi_isLocallyConstant (v : FinPlace F) (A : AddCharData F) :
    IsLocallyConstant (A.ψ v) := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  have hOopen : IsOpen O := by
    change IsOpen (v.adicCompletionIntegers F : Set K)
    exact Valued.isOpen_valuationSubring K
  apply (IsLocallyConstant.iff_exists_open (A.ψ v)).2
  intro x
  let U : Set K := {y | y - x ∈ O}
  have hUopen : IsOpen U := by
    apply hOopen.preimage
    fun_prop
  refine ⟨U, hUopen, ?_, ?_⟩
  · change x - x ∈ O
    simp [O, HeightOneSpectrum.mem_adicCompletionIntegers]
  · intro y hy
    have hψ := A.integral v (y - x) hy
    calc
      A.ψ v y = A.ψ v (x + (y - x)) := by congr 1 <;> abel
      _ = A.ψ v x * A.ψ v (y - x) := AddChar.map_add_eq_mul (A.ψ v) x (y - x)
      _ = A.ψ v x := by rw [hψ]; simp

private theorem finiteCharacterIntegrable
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (y : v.adicCompletion F) :
    Integrable (fun x => f x * A.ψ v (-(x * y))) μ.μ := by
  let g : v.adicCompletion F → ℂ := fun x => f x * A.ψ v (-(x * y))
  have hχ : Continuous (fun x : v.adicCompletion F => A.ψ v (-(x * y))) := by
    exact (finitePsi_isLocallyConstant v A).continuous.comp (by fun_prop)
  have hg : Continuous g := hf.mul hχ
  have hsupport : Function.support g ⊆ tsupport f := by
    intro x hx
    by_contra hnot
    have hfzero : f x = 0 := by
      by_contra hne
      exact hnot (subset_closure (Function.mem_support.mpr hne))
    exact (Function.mem_support.mp hx) (by simp [g, hfzero])
  have htsupport : tsupport g ⊆ tsupport f :=
    closure_minimal hsupport (isClosed_tsupport f)
  have hcompact : IsCompact (tsupport g) := hfc.of_isClosed_subset
    (isClosed_tsupport g) htsupport
  exact hg.integrable_of_hasCompactSupport hcompact

private theorem tensorFunction_continuous
    (arch : SData.ArchSchwartz F) (finite : ∀ v : S.Sf, S.FiniteTest v) :
    Continuous (S.tensorFunction arch finite) := by
  change Continuous (fun x : S.FS => arch x.2 * ∏ v : S.Sf, (finite v).1 (x.1 v))
  apply Continuous.mul
  · exact arch.continuous.comp continuous_snd
  · apply continuous_finsetProd Finset.univ
    intro v hv
    exact (finite v).2.1.comp ((continuous_apply v).comp continuous_fst)

private theorem globalAddChar_continuous (S : SData F CE condη) (A : AddCharData F) :
    Continuous (S.e A) := by
  unfold SData.e
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    exact (finitePsi_isLocallyConstant v.1 A).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    have hψ : Continuous (A1.psiC) := by unfold A1.psiC; fun_prop
    exact hψ.comp ((continuous_apply w).comp continuous_snd)

private theorem globalKernel_continuous (S : SData F CE condη) (A : AddCharData F)
    (y : S.FS) : Continuous (fun x : S.FS => S.e A (-(x * y))) := by
  apply (globalAddChar_continuous S A).comp
  exact continuous_neg.comp (continuous_id.mul continuous_const)

private theorem psiC_norm_one (z : ℂ) : ‖A1.psiC z‖ = 1 := by
  unfold A1.psiC
  rw [Complex.norm_exp]
  have hre : (-(4 * Real.pi * Complex.I * (z.re : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero]

private theorem tensorFourier_reference
    (arch : SData.ArchSchwartz F) (finite : ∀ v : S.Sf, S.FiniteTest v) (y : S.FS) :
    S.fourier A (referenceAddHaar S μ) (S.tensorFunction arch finite) y =
      (∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
        v.1 A (μ v.1) (finite v).1 (y.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
          (arch : (InfinitePlace F → ℂ) → ℂ) y.2 := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => (μ v.1).μ
  let μArch : Measure (InfinitePlace F → ℂ) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
  let finTerm : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun z =>
    ∏ v : S.Sf, (finite v).1 (z v) * A.ψ v.1 (-(y.1 v * z v))
  let archTerm : (InfinitePlace F → ℂ) → ℂ := fun z =>
    arch z * ∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z w))
  letI : ∀ v : S.Sf, SigmaFinite ((μ v.1).μ) := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    letI : SigmaCompactSpace (v.1.adicCompletion F) := inferInstance
    infer_instance
  have hcoord (v : S.Sf) :
      Integrable (fun z => (finite v).1 z * A.ψ v.1 (-(y.1 v * z))) (μ v.1).μ := by
    simpa [mul_comm] using finiteCharacterIntegrable v.1 A (μ v.1) (finite v).1
      (finite v).2.1 (finite v).2.2.1 (y.1 v)
  have hfin : Integrable finTerm μFin := by
    dsimp [finTerm, μFin]
    exact Integrable.fintype_prod_dep hcoord
  letI : Measure.IsAddHaarMeasure μArch :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
  letI : Measure.HasTemperateGrowth μArch := inferInstance
  letI : SFinite μArch := inferInstance
  have hArchBase : Integrable (arch : (InfinitePlace F → ℂ) → ℂ) μArch := arch.integrable
  have hArchCharCont : Continuous
      (fun z : InfinitePlace F → ℂ => ∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z w))) := by
    apply continuous_finsetProd Finset.univ
    intro w hw
    have hψ : Continuous (A1.psiC) := by unfold A1.psiC; fun_prop
    exact hψ.comp (by fun_prop)
  have hArchCharNorm (z : InfinitePlace F → ℂ) :
      ‖∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z w))‖ = 1 := by
    rw [norm_prod]
    simp [psiC_norm_one]
  have harch : Integrable archTerm μArch := by
    dsimp [archTerm]
    exact hArchBase.mul_bdd hArchCharCont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => le_of_eq (hArchCharNorm z))
  letI : SFinite μFin := inferInstance
  have hprod : Integrable (fun z => finTerm z.1 * archTerm z.2) (μFin.prod μArch) :=
    hfin.mul_prod harch
  have hglobal :
      ∫ x, S.tensorFunction arch finite x * S.e A (-(x * y)) ∂referenceAddHaar S μ =
        ∫ z, finTerm z.1 * archTerm z.2 ∂(μFin.prod μArch) := by
    letI : MeasurableSpace (ULift.{0} S.FS) := fsULiftProductMeas S
    letI : BorelSpace (ULift.{0} S.FS) := by
      letI : MeasurableSpace S.FS := fsProductMeas S
      letI : BorelSpace S.FS := ⟨fsProductMeas_eq_borel S⟩
      exact ULift.instBorelSpace
    unfold referenceAddHaar referenceAddHaarUp
    rw [MeasureTheory.integral_map_equiv (fsDownBorelMeasEquiv S)]
    rw [MeasureTheory.integral_map_equiv (fsUpProdMeasEquiv S)]
    apply integral_congr_ae
    filter_upwards with z
    change arch z.2 * (∏ v : S.Sf, (finite v).1 (z.1 v)) *
        ((∏ v : S.Sf, A.ψ v.1 (-(z.1 v * y.1 v))) *
          ∏ w : InfinitePlace F, A1.psiC (-(z.2 w * y.2 w))) = _
    let hFinChar :
        (∏ v : S.Sf, A.ψ v.1 (-(z.1 v * y.1 v))) =
          ∏ v : S.Sf, A.ψ v.1 (-(y.1 v * z.1 v)) := by
      apply Finset.prod_congr rfl
      intro v hv
      congr 1
      congr 1
      rw [mul_comm]
    let hArchChar :
        (∏ w : InfinitePlace F, A1.psiC (-(z.2 w * y.2 w))) =
          ∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z.2 w)) := by
      apply Finset.prod_congr rfl
      intro w hw
      congr 1
      congr 1
      rw [mul_comm]
    have hProd :
        (∏ v ∈ S.Sf.attach, (finite v).1 (z.1 v)) *
          (∏ v ∈ S.Sf.attach, A.ψ v.1 (-(y.1 v * z.1 v))) =
        ∏ v ∈ S.Sf.attach, (finite v).1 (z.1 v) * A.ψ v.1 (-(y.1 v * z.1 v)) := by
      rw [← Finset.prod_mul_distrib]
    rw [hFinChar, hArchChar]
    dsimp [finTerm, archTerm]
    calc
      _ = (arch z.2 * ∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z.2 w))) *
          ((∏ v ∈ S.Sf.attach, (finite v).1 (z.1 v)) *
            ∏ v ∈ S.Sf.attach, A.ψ v.1 (-(y.1 v * z.1 v))) := by ring
      _ = (arch z.2 * ∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z.2 w))) *
          ∏ v ∈ S.Sf.attach, (finite v).1 (z.1 v) * A.ψ v.1 (-(y.1 v * z.1 v)) := by
            rw [hProd]
      _ = _ := by ring
  calc
    S.fourier A (referenceAddHaar S μ) (S.tensorFunction arch finite) y =
        ∫ x, S.tensorFunction arch finite x * S.e A (-(x * y)) ∂referenceAddHaar S μ := rfl
    _ = ∫ z, finTerm z.1 * archTerm z.2 ∂(μFin.prod μArch) := hglobal
    _ = (∫ z, finTerm z ∂μFin) * ∫ z, archTerm z ∂μArch :=
          MeasureTheory.integral_prod_mul finTerm archTerm
    _ = (∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
          v.1 A (μ v.1) (finite v).1 (y.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
          (arch : (InfinitePlace F → ℂ) → ℂ) y.2 := by
      have hfinProd := MeasureTheory.integral_fintype_prod_eq_prod
        (μ := fun v : S.Sf => (μ v.1).μ)
        (fun v z => (finite v).1 z * A.ψ v.1 (-(y.1 v * z)))
      have harchEq : ∫ z, archTerm z ∂μArch =
          ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
            (arch : (InfinitePlace F → ℂ) → ℂ) y.2 := by
        unfold ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
        dsimp [archTerm]
        apply integral_congr_ae
        filter_upwards with z
        change arch z * (∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z w))) =
          (∏ w : InfinitePlace F, A1.psiC (-(y.2 w * z w))) * arch z
        ring
      have hfiniteEq : ∫ z, finTerm z ∂μFin =
          ∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
            v.1 A (μ v.1) (finite v).1 (y.1 v) := by
        dsimp [μFin, finTerm]
        simpa [ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier, mul_comm] using hfinProd
      calc
        (∫ z, finTerm z ∂μFin) * ∫ z, archTerm z ∂μArch =
            (∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
              v.1 A (μ v.1) (finite v).1 (y.1 v)) * ∫ z, archTerm z ∂μArch := by
                rw [hfiniteEq]
        _ = _ := by rw [harchEq]

private noncomputable def referenceFourierScale
    (sd : S.SelfDualMeasure A) : ℂ := by
  letI : Measure.IsAddHaarMeasure (sd.measure) := sd.isHaar
  letI : Measure.IsAddHaarMeasure (referenceAddHaar S μ) := referenceAddHaar_isHaar S μ
  exact ((Measure.addHaarScalarFactor sd.measure (referenceAddHaar S μ)).toReal : ℂ)

private theorem tensorFourier_actual
    (sd : S.SelfDualMeasure A) (arch : SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v)
    (hcompact : HasCompactSupport (S.tensorFunction arch finite)) (y : S.FS) :
    S.fourier A sd.measure (S.tensorFunction arch finite) y =
      referenceFourierScale (μ := μ) sd *
        ((∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
          v.1 A (μ v.1) (finite v).1 (y.1 v)) *
          ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
            (arch : (InfinitePlace F → ℂ) → ℂ) y.2) := by
  let g : S.FS → ℂ := fun x => S.tensorFunction arch finite x * S.e A (-(x * y))
  letI : Measure.IsAddHaarMeasure (sd.measure) := sd.isHaar
  letI : Measure.IsAddHaarMeasure (referenceAddHaar S μ) := referenceAddHaar_isHaar S μ
  have hgcont : Continuous g := by
    exact (tensorFunction_continuous arch finite).mul (globalKernel_continuous S A y)
  have hgsupport : Function.support g ⊆ tsupport (S.tensorFunction arch finite) := by
    intro x hx
    by_contra hnot
    have hzero : S.tensorFunction arch finite x = 0 := by
      by_contra hne
      exact hnot (subset_closure (Function.mem_support.mpr hne))
    exact (Function.mem_support.mp hx) (by simp [g, hzero])
  have hgt : tsupport g ⊆ tsupport (S.tensorFunction arch finite) :=
    closure_minimal hgsupport (isClosed_tsupport _)
  have hgcompact : HasCompactSupport g := hcompact.of_isClosed_subset
    (isClosed_tsupport g) hgt
  have hscale := integral_addHaarScalarFactor_complex sd.measure
    (referenceAddHaar S μ) g hgcont hgcompact
  have hreference := tensorFourier_reference (S := S) (μ := μ) (A := A)
    arch finite y
  unfold SData.fourier
  change (∫ x, g x ∂sd.measure) = _
  calc
    _ = referenceFourierScale (μ := μ) sd *
        ∫ x, g x ∂referenceAddHaar S μ := hscale
    _ = _ := congrArg (fun z : ℂ => referenceFourierScale (μ := μ) sd * z) hreference

private def pArchProduct (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (z : InfinitePlace F → ℂ) : ℂ :=
  ∏ w : InfinitePlace F, arch w (z w)

private theorem pArchSlice_schwartz (W0 : S.FS → ℂ)
    (hW0 : W0 ∈ S.BruhatSchwartz)
    (x : ∀ v : S.Sf, v.1.adicCompletion F) :
    ∃ g : SchwartzMap (InfinitePlace F → ℂ) ℂ, ∀ z, g z = W0 (x, z) := by
  classical
  change W0 ∈ Submodule.span ℂ (Set.range fun p :
    SData.ArchSchwartz F × (∀ v : S.Sf, S.FiniteTest v) => S.tensorFunction p.1 p.2)
    at hW0
  refine Submodule.span_induction
    (p := fun f _ => ∃ g : SchwartzMap (InfinitePlace F → ℂ) ℂ,
      ∀ z, g z = f (x, z)) ?_ ?_ ?_ ?_ hW0
  · rintro f ⟨p, rfl⟩
    rcases p with ⟨a, fin⟩
    refine ⟨(∏ v : S.Sf, (fin v).1 (x v)) • a, ?_⟩
    intro z
    simp [SData.tensorFunction, mul_comm, mul_left_comm, mul_assoc]
  · refine ⟨0, ?_⟩
    intro z
    simp
  · intro f g hf hg hfp hgp
    rcases hfp with ⟨f', hf'⟩
    rcases hgp with ⟨g', hg'⟩
    refine ⟨f' + g', ?_⟩
    intro z
    simp [hf', hg']
  · intro c f hf hfp
    rcases hfp with ⟨f', hf'⟩
    refine ⟨c • f', ?_⟩
    intro z
    simp [hf']

private theorem pArchProduct_schwartz_of_bruhat
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hW0 : W0 ∈ S.BruhatSchwartz)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct arch y.2)
    (hW0ne : ∃ y, W0 y ≠ 0) :
    ∃ g : SchwartzMap (InfinitePlace F → ℂ) ℂ, ∀ z, g z = pArchProduct arch z := by
  classical
  obtain ⟨y, hy⟩ := hW0ne
  let c : ℂ := ∏ v : S.Sf, (finite v).1 (y.1 v)
  have hc : c ≠ 0 := by
    have hprod : c * pArchProduct arch y.2 ≠ 0 := by
      simpa [c, hTensor] using hy
    exact left_ne_zero_of_mul hprod
  obtain ⟨g, hg⟩ := pArchSlice_schwartz (S := S) W0 hW0 y.1
  refine ⟨c⁻¹ • g, ?_⟩
  intro z
  have hslice : W0 (y.1, z) = c * pArchProduct arch z := by
    simpa [c] using hTensor (y.1, z)
  change c⁻¹ * g z = pArchProduct arch z
  rw [hg z, hslice]
  field_simp [hc]

private theorem pArchProduct_hasCompactSupport
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct arch y.2)
    (hcompact : HasCompactSupport W0) (hW0ne : ∃ y, W0 y ≠ 0) :
    HasCompactSupport (pArchProduct arch) := by
  classical
  obtain ⟨y, hy⟩ := hW0ne
  let c : ℂ := ∏ v : S.Sf, (finite v).1 (y.1 v)
  have hc : c ≠ 0 := by
    have hprod : c * pArchProduct arch y.2 ≠ 0 := by
      simpa [c, hTensor] using hy
    exact left_ne_zero_of_mul hprod
  let K : Set S.FS := tsupport W0
  let P : Set (InfinitePlace F → ℂ) := (fun z : S.FS => z.2) '' K
  have hP : IsCompact P := hcompact.image (by fun_prop)
  have hsupport : Function.support (pArchProduct arch) ⊆ P := by
    intro z hz
    have harch : pArchProduct arch z ≠ 0 := Function.mem_support.mp hz
    have hW : W0 (y.1, z) ≠ 0 := by
      rw [hTensor]
      simpa [c] using mul_ne_zero hc harch
    have hmem : (y.1, z) ∈ K := subset_closure (Function.mem_support.mpr hW)
    exact ⟨(y.1, z), hmem, rfl⟩
  have hts : tsupport (pArchProduct arch) ⊆ P :=
    closure_minimal hsupport hP.isClosed
  exact hP.of_isClosed_subset (isClosed_tsupport _) hts

private theorem pArchProduct_schwartz_of_compactTensor
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct arch y.2)
    (hcompact : HasCompactSupport W0) (hW0ne : ∃ y, W0 y ≠ 0) :
    ∃ g : SchwartzMap (InfinitePlace F → ℂ) ℂ, ∀ z, g z = pArchProduct arch z := by
  have hgcomp : HasCompactSupport (pArchProduct arch) :=
    pArchProduct_hasCompactSupport arch finite W0 hTensor hcompact hW0ne
  have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pArchProduct arch) := by
    unfold pArchProduct
    fun_prop
  refine ⟨hgcomp.toSchwartzMap hgsmooth, ?_⟩
  intro z
  rfl

private noncomputable def pArchVolumeMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi fun _ : ι => (volume : Measure ℂ)

private theorem pArchVolumeMeasure_isHaar (ι : Type*) [Fintype ι] :
    Measure.IsAddHaarMeasure (pArchVolumeMeasure ι) := by
  letI : ∀ w : ι, Measure.IsAddHaarMeasure (volume : Measure ℂ) :=
    fun _ => inferInstance
  letI : ∀ w : ι, SigmaFinite (volume : Measure ℂ) := fun _ => inferInstance
  change Measure.IsAddHaarMeasure
    (Measure.pi fun _ : ι => (volume : Measure ℂ))
  infer_instance

noncomputable def pArchFourierScale (ι : Type*) [Fintype ι] : ℂ := by
  letI : LocallyCompactSpace (ι → ℂ) := inferInstance
  letI : Measure.IsAddHaarMeasure
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar ι) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : Measure.IsAddHaarMeasure (pArchVolumeMeasure ι) := pArchVolumeMeasure_isHaar ι
  exact ((Measure.addHaarScalarFactor
    (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar ι)
    (pArchVolumeMeasure ι)).toReal : ℂ)

private theorem pComplexPiFourier_product
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (g : SchwartzMap (InfinitePlace F → ℂ) ℂ)
    (hg : ∀ z, g z = pArchProduct arch z)
    (hcompact : HasCompactSupport g) (x : InfinitePlace F → ℂ) :
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier g x =
      pArchFourierScale (InfinitePlace F) * ∏ w : InfinitePlace F,
        ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w) (x w) := by
  classical
  let ν : Measure (InfinitePlace F → ℂ) := pArchVolumeMeasure (InfinitePlace F)
  let f : (InfinitePlace F → ℂ) → ℂ := fun z =>
    (∏ w : InfinitePlace F, A1.psiC (-(x w * z w))) * g z
  let fcoord : ∀ w : InfinitePlace F, ℂ → ℂ := fun w z =>
    A1.psiC (-(x w * z)) * arch w z
  let μcoord : ∀ w : InfinitePlace F, Measure ℂ := fun _ => volume
  letI : ∀ w : InfinitePlace F, SigmaFinite (μcoord w) := fun _ => inferInstance
  letI : SigmaFinite ν := by
    dsimp [ν, pArchVolumeMeasure]
    infer_instance
  letI : SFinite ν := inferInstance
  have hcoordInt (w : InfinitePlace F) : Integrable (fcoord w) (μcoord w) := by
    have hcharCont : Continuous (fun z : ℂ => A1.psiC (-(x w * z))) := by
      have hψ : Continuous A1.psiC := by unfold A1.psiC; fun_prop
      exact hψ.comp (by fun_prop)
    have hcharNorm (z : ℂ) : ‖A1.psiC (-(x w * z))‖ = 1 := psiC_norm_one _
    have hbase : Integrable (arch w) (μcoord w) := (arch w).integrable
    have hmul := hbase.mul_bdd hcharCont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => le_of_eq (hcharNorm z))
    dsimp [fcoord, μcoord]
    simpa [mul_comm] using hmul
  have hprodInt : Integrable
      (fun z : InfinitePlace F → ℂ => ∏ w : InfinitePlace F, fcoord w (z w)) ν := by
    dsimp [ν, pArchVolumeMeasure]
    exact Integrable.fintype_prod_dep hcoordInt
  have hintegrand (z : InfinitePlace F → ℂ) :
      f z = ∏ w : InfinitePlace F, fcoord w (z w) := by
    dsimp [f, fcoord]
    rw [hg z, pArchProduct, ← Finset.prod_mul_distrib]
  have hfactor := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := μcoord) (fun w z => fcoord w z)
  have hreference :
      ∫ z, f z ∂ν =
        ∏ w : InfinitePlace F,
          ∫ z : ℂ, fcoord w z ∂(μcoord w) := by
    calc
      _ = ∫ z, ∏ w : InfinitePlace F, fcoord w (z w) ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        exact hintegrand z
      _ = _ := by simpa [ν, μcoord, pArchVolumeMeasure] using hfactor
  have hloc (w : InfinitePlace F) :
      ∫ z : ℂ, fcoord w z ∂(μcoord w) =
        ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w) (x w) := by
    dsimp [fcoord, μcoord]
    rw [ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz_eq_integral]
    apply integral_congr_ae
    filter_upwards with z
    ring
  letI : Measure.IsAddHaarMeasure
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : Measure.IsAddHaarMeasure ν := pArchVolumeMeasure_isHaar (InfinitePlace F)
  have hscale := integral_addHaarScalarFactor_complex
    (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) ν f
    (by
      have hcharCont : Continuous
          (fun z : InfinitePlace F → ℂ =>
            ∏ w : InfinitePlace F, A1.psiC (-(x w * z w))) := by
        apply continuous_finsetProd Finset.univ
        intro w hw
        have hψ : Continuous A1.psiC := by unfold A1.psiC; fun_prop
        exact hψ.comp (by fun_prop)
      exact hcharCont.mul g.continuous)
    (by
      have hsupport : Function.support f ⊆ tsupport g := by
        intro z hz
        by_contra hnot
        have hzero : g z = 0 := by
          by_contra hne
          exact hnot (subset_closure (Function.mem_support.mpr hne))
        exact (Function.mem_support.mp hz) (by simp [f, hzero])
      have hts : tsupport f ⊆ tsupport g :=
        closure_minimal hsupport (isClosed_tsupport _)
      exact hcompact.of_isClosed_subset (isClosed_tsupport _) hts)
  have hfourier : ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier g x =
      ∫ z, f z ∂(ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar
        (InfinitePlace F)) := by
    unfold ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier f
    rfl
  calc
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier g x =
        ∫ z, f z ∂(ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar
          (InfinitePlace F)) := hfourier
    _ = pArchFourierScale (InfinitePlace F) * ∫ z, f z ∂ν := by
      simpa [pArchFourierScale] using hscale
    _ = pArchFourierScale (InfinitePlace F) *
        ∏ w : InfinitePlace F,
          ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w) (x w) := by
      rw [hreference]
      simp_rw [hloc]

private theorem pWeightFourier_actual
    (sd : S.SelfDualMeasure A)
    (archLocal : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct archLocal y.2)
    (hBruhat : W0 ∈ S.BruhatSchwartz)
    (hcompact : HasCompactSupport W0) (hW0ne : ∃ y, W0 y ≠ 0) (y : S.FS) :
    ∃ arch : SData.ArchSchwartz F,
      S.fourier A sd.measure W0 y =
        referenceFourierScale (S := S) (μ := μ) sd *
          ((∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
            v.1 A (μ v.1) (finite v).1 (y.1 v)) *
            ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier arch y.2) := by
  classical
  let arch : SData.ArchSchwartz F := Classical.choose
    (pArchProduct_schwartz_of_bruhat (S := S) archLocal finite W0 hBruhat hTensor hW0ne)
  have harch : ∀ z, arch z = pArchProduct archLocal z :=
    Classical.choose_spec
      (pArchProduct_schwartz_of_bruhat (S := S) archLocal finite W0 hBruhat hTensor hW0ne)
  have hEq : W0 = S.tensorFunction arch finite := by
    funext x
    rw [hTensor x]
    simp [SData.tensorFunction, pArchProduct, harch]
    ring
  have hcompact' : HasCompactSupport (S.tensorFunction arch finite) := by
    simpa [hEq] using hcompact
  have hFourier := tensorFourier_actual (S := S) (μ := μ) (A := A)
    sd arch finite hcompact' y
  refine ⟨arch, ?_⟩
  rw [hEq]
  simpa [arch] using hFourier

noncomputable def pWeightFourierScale (sd : S.SelfDualMeasure A)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) : ℂ :=
  referenceFourierScale (S := S) (μ := μ) sd * pArchFourierScale (InfinitePlace F)

private theorem pWeightFourier_local_actual
    (sd : S.SelfDualMeasure A)
    (archLocal : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct archLocal y.2)
    (hcompact : HasCompactSupport W0) (hW0ne : ∃ y, W0 y ≠ 0) (y : S.FS) :
    S.fourier A sd.measure W0 y = pWeightFourierScale (S := S) sd μ *
      ((∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
        v.1 A (μ v.1) (finite v).1 (y.1 v)) *
        ∏ w : InfinitePlace F,
          ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
            (archLocal w) (y.2 w)) := by
  classical
  obtain ⟨arch, harch⟩ := pArchProduct_schwartz_of_compactTensor
    archLocal finite W0 hTensor hcompact hW0ne
  have hGcompact : HasCompactSupport (pArchProduct archLocal) :=
    pArchProduct_hasCompactSupport archLocal finite W0 hTensor hcompact hW0ne
  have hArchEq : (arch : (InfinitePlace F → ℂ) → ℂ) = pArchProduct archLocal :=
    funext harch
  have hArchCompact : HasCompactSupport arch := by
    simpa [hArchEq] using hGcompact
  have hEq : W0 = S.tensorFunction arch finite := by
    funext x
    rw [hTensor x]
    simp [SData.tensorFunction, pArchProduct, harch]
    ring
  have hcompact' : HasCompactSupport (S.tensorFunction arch finite) := by
    simpa [hEq] using hcompact
  have hFourier := tensorFourier_actual (S := S) (μ := μ) (A := A)
    sd arch finite hcompact' y
  have hArchFourier := pComplexPiFourier_product archLocal arch harch hArchCompact y.2
  calc
    S.fourier A sd.measure W0 y =
        referenceFourierScale (S := S) (μ := μ) sd *
          ((∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
            v.1 A (μ v.1) (finite v).1 (y.1 v)) *
            ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier arch y.2) := by
              rw [hEq]
              exact hFourier
    _ = referenceFourierScale (S := S) (μ := μ) sd *
        ((∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
          v.1 A (μ v.1) (finite v).1 (y.1 v)) *
          (pArchFourierScale (InfinitePlace F) * ∏ w : InfinitePlace F,
            ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
              (archLocal w) (y.2 w))) := by rw [hArchFourier]
    _ = _ := by
      simp [pWeightFourierScale]
      ring

private theorem mulHaarC_integral_comp_smul (a : ℝ) (ha : 0 < a) (f : ℂ → ℂ) :
    ∫ z, f ((a : ℂ) • z) ∂A1.Theta.mulHaarC = ∫ z, f z ∂A1.Theta.mulHaarC := by
  let q : ℂ → ℝ := Complex.normSq
  have hqscale (z : ℂ) : q ((a : ℂ) • z) = a ^ 2 * q z := by
    change Complex.normSq ((a : ℂ) * z) = a ^ 2 * Complex.normSq z
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    ring
  have hdensity : Measurable (fun z : ℂ => ENNReal.ofReal (q z)⁻¹) := by
    fun_prop
  have htop : ∀ᵐ z : ℂ ∂(volume : Measure ℂ), ENNReal.ofReal (q z)⁻¹ < ⊤ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  have htoReal (z : ℂ) : (ENNReal.ofReal (q z)⁻¹).toReal = (q z)⁻¹ := by
    by_cases hz : z = 0
    · subst z
      simp [q]
    · have hqpos : 0 < q z := Complex.normSq_pos.mpr hz
      rw [ENNReal.ofReal_inv_of_pos hqpos, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hqpos.le]
  unfold A1.Theta.mulHaarC
  rw [integral_withDensity_eq_integral_toReal_smul hdensity htop,
    integral_withDensity_eq_integral_toReal_smul hdensity htop]
  simp_rw [htoReal]
  have hqInv (z : ℂ) : (q z)⁻¹ = a ^ 2 * (q ((a : ℂ) • z))⁻¹ := by
    rw [hqscale]
    calc
      (q z)⁻¹ = (a ^ 2 * (a ^ 2)⁻¹) * (q z)⁻¹ := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul]
      _ = a ^ 2 * ((q z)⁻¹ * (a ^ 2)⁻¹) := by ring
      _ = a ^ 2 * (a ^ 2 * q z)⁻¹ := by rw [mul_inv_rev]
  calc
    (∫ z, (q z)⁻¹ • f ((a : ℂ) • z) ∂(volume : Measure ℂ)) =
        a ^ 2 • ∫ z, (q ((a : ℂ) • z))⁻¹ • f ((a : ℂ) • z)
          ∂(volume : Measure ℂ) := by
            rw [← integral_smul (a ^ 2)
              (fun z : ℂ => (q ((a : ℂ) • z))⁻¹ • f ((a : ℂ) • z))]
            apply integral_congr_ae
            filter_upwards with z
            rw [hqInv z]
            simp only [Complex.real_smul]
            rw [Complex.ofReal_mul]
            ac_rfl
    _ = a ^ 2 • ((a ^ 2)⁻¹ • ∫ z, (q z)⁻¹ • f z ∂(volume : Measure ℂ)) := by
          congr 1
          have hchange := Measure.integral_comp_smul (volume : Measure ℂ)
            (fun z => (q z)⁻¹ • f z) a
          simpa [Complex.finrank_real_complex,
            abs_of_pos (inv_pos.mpr (pow_pos ha 2)), smul_eq_mul] using hchange
    _ = ∫ z, (q z)⁻¹ • f z ∂(volume : Measure ℂ) := by
          have ha2 : (a ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 ha.ne'
          have hcancel : ((a ^ 2 : ℝ) : ℂ) * (((a ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
            rw [← Complex.ofReal_mul]
            simp [ha2]
          simp only [Complex.real_smul]
          rw [← mul_assoc, hcancel, one_mul]

private theorem pReCoeff_temperate :
    (fun z : ℂ => (z.re : ℂ)).HasTemperateGrowth := by
  fun_prop

private theorem pImCoeff_temperate :
    (fun z : ℂ => (z.im : ℂ)).HasTemperateGrowth := by
  fun_prop

private def pEulerSchwartz (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℂ) •
    (SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.re : ℂ)) (∂_{(1 : ℂ)} f) +
      SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.im : ℂ)) (∂_{Complex.I} f))

private theorem pEulerSchwartz_apply (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    pEulerSchwartz f z = (1 / 2 : ℂ) * fderiv ℝ f z z := by
  have hz : (z.re : ℝ) • (1 : ℂ) + z.im • Complex.I = z := by
    apply Complex.ext <;> simp
  change (1 / 2 : ℂ) *
      (SchwartzMap.smulLeftCLM ℂ (fun z => (z.re : ℂ)) (∂_{(1 : ℂ)} f) z +
        SchwartzMap.smulLeftCLM ℂ (fun z => (z.im : ℂ)) (∂_{Complex.I} f) z) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply pReCoeff_temperate,
    SchwartzMap.smulLeftCLM_apply_apply pImCoeff_temperate,
    SchwartzMap.lineDerivOp_apply_eq_fderiv (1 : ℂ) f z,
    SchwartzMap.lineDerivOp_apply_eq_fderiv Complex.I f z]
  have hlin : fderiv ℝ f z z =
      z.re • fderiv ℝ f z 1 + z.im • fderiv ℝ f z Complex.I := by
    calc
      fderiv ℝ f z z =
          fderiv ℝ f z ((z.re : ℝ) • (1 : ℂ) + z.im • Complex.I) := by rw [hz]
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [hlin]
  change (1 / 2 : ℂ) * ((z.re : ℂ) * fderiv ℝ f z 1 +
      (z.im : ℂ) * fderiv ℝ f z Complex.I) = _
  rw [Complex.real_smul, Complex.real_smul]

private def pRadialIter : ℕ → SchwartzMap ℂ ℂ → SchwartzMap ℂ ℂ
  | 0, f => f
  | n + 1, f => pEulerSchwartz (pRadialIter n f)

private theorem pHasDeriv_expHalf (t : ℝ) :
    HasDerivAt (fun u : ℝ => (Real.exp (u / 2) : ℂ))
      ((Real.exp (t / 2) / 2 : ℝ) : ℂ) t := by
  have hdiv : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t := by
    convert (hasDerivAt_id t).div_const 2 using 1 <;> simp
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) / 2) t := by
    convert (Real.hasDerivAt_exp (t / 2)).comp t hdiv using 1
    · funext u
      simp only [Function.comp_apply]
    · ring
  exact hexp.ofReal_comp

private theorem pEulerChain (f : SchwartzMap ℂ ℂ) (z : ℂ) (t : ℝ) :
    deriv (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      pEulerSchwartz f ((Real.exp (t / 2) : ℂ) * z) := by
  let y : ℂ := (Real.exp (t / 2) : ℂ) * z
  have hφ := (pHasDeriv_expHalf t).mul_const z
  have hf : HasFDerivAt (fun w : ℂ => f w) (fderiv ℝ f y) y :=
    f.differentiableAt.hasFDerivAt
  have hcomp := hf.comp t hφ.hasFDerivAt
  have hchain : deriv (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      fderiv ℝ f y (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) := by
    simpa [y, Function.comp_def] using hcomp.hasDerivAt.deriv
  rw [hchain, pEulerSchwartz_apply]
  have hdir : (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) = (1 / 2 : ℝ) • y := by
    dsimp [y]
    push_cast
    ring
  rw [hdir, map_smul]
  change ((1 / 2 : ℝ) : ℂ) * fderiv ℝ f y y =
      (1 / 2 : ℂ) * fderiv ℝ f y y
  push_cast
  ring

private theorem pIteratedDerivRadial (f : SchwartzMap ℂ ℂ) (n : ℕ) (z : ℂ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      pRadialIter n f ((Real.exp (t / 2) : ℂ) * z) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) =
          fun u => pRadialIter n f ((Real.exp (u / 2) : ℂ) * z) := by
        funext u
        exact ih u
      rw [hfun]
      simpa [pRadialIter] using pEulerChain (pRadialIter n f) z t

private theorem pNormDerivEqRadialIter (f : SchwartzMap ℂ ℂ) (n : ℕ) (z : ℂ) :
    A1.normDeriv n f z = pRadialIter n f z := by
  unfold A1.normDeriv
  have h := pIteratedDerivRadial f n z 0
  simpa [Complex.exp_zero] using h

private theorem pRadialSchwartzWeightBound (g : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖g z‖ * Complex.normSq z ^ σ ≤ C * bridgeComplexMajorant σ z := by
  obtain ⟨n, hn⟩ := exists_nat_gt (σ + 3)
  let C0 : ℝ := max ((SchwartzMap.seminorm ℂ 0 0) g) 0
  let Cn : ℝ := max ((SchwartzMap.seminorm ℂ (2 * n) 0) g) 0
  let p : ℝ := σ + 3
  let C : ℝ := max C0 Cn * 2 ^ p
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCn : 0 ≤ Cn := le_max_right _ _
  have hp : 0 < p := by dsimp [p]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    simp [bridgeComplexMajorant, hσ.ne']
  · have hqpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hqnonneg : 0 ≤ Complex.normSq z := le_of_lt hqpos
    have hnorm : ‖g z‖ ≤ C0 := by
      have h := SchwartzMap.norm_le_seminorm ℂ g z
      exact h.trans (le_max_left _ _)
    have hpow : Complex.normSq z ^ n = ‖z‖ ^ (2 * n) := by
      rw [Complex.normSq_eq_norm_sq, ← pow_mul]
    have hjet : Complex.normSq z ^ n * ‖g z‖ ≤ Cn := by
      rw [hpow]
      simpa only [norm_iteratedFDeriv_zero] using
        (SchwartzMap.le_seminorm ℂ (2 * n) 0 g z).trans (le_max_left _ _)
    let q : ℝ := Complex.normSq z
    have hqpos' : 0 < q := hqpos
    have hqnonneg' : 0 ≤ q := hqnonneg
    have htail : ‖g z‖ ≤ Cn * q ^ (-(n : ℝ)) := by
      have hqpow : 0 < q ^ n := pow_pos hqpos' n
      have hdiv : ‖g z‖ ≤ Cn / q ^ n := by
        apply (le_div_iff₀ hqpow).2
        simpa [q, mul_comm] using hjet
      calc
        ‖g z‖ ≤ Cn / q ^ n := hdiv
        _ = Cn * q ^ (-(n : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg hqpos'.le]
    have hmajorant_pos : 0 < (1 + q) ^ p := Real.rpow_pos_of_pos (by positivity) p
    have hsmall (hq : q ≤ 1) :
        ‖g z‖ * q ^ σ ≤ C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
      have hden : (1 + q) ^ p ≤ 2 ^ p := by
        apply Real.rpow_le_rpow (by positivity) (by linarith) hp.le
      have hpow : q ^ σ ≤ 2 ^ p * q ^ σ / (1 + q) ^ p := by
        apply (le_div_iff₀ hmajorant_pos).2
        calc
          q ^ σ * (1 + q) ^ p ≤ q ^ σ * 2 ^ p :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hqnonneg' σ)
          _ = 2 ^ p * q ^ σ := by ring
      have hpow' : q ^ σ ≤ 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
        simpa [mul_div_assoc] using hpow
      calc
        ‖g z‖ * q ^ σ ≤ C0 * q ^ σ :=
          mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hqnonneg' σ)
        _ ≤ C0 * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
          mul_le_mul_of_nonneg_left hpow' hC0
        _ = C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    have hlarge (hq : 1 ≤ q) :
        ‖g z‖ * q ^ σ ≤ Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
      have hden : (1 + q) ^ p ≤ 2 ^ p * q ^ p := by
        calc
          (1 + q) ^ p ≤ (2 * q) ^ p :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) hp.le
          _ = 2 ^ p * q ^ p := Real.mul_rpow (by norm_num) hqnonneg'
      have hfactor : q ^ (-3 : ℝ) ≤ 2 ^ p * q ^ σ / (1 + q) ^ p := by
        apply (le_div_iff₀ hmajorant_pos).2
        calc
          q ^ (-3 : ℝ) * (1 + q) ^ p ≤ q ^ (-3 : ℝ) * (2 ^ p * q ^ p) :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hqnonneg' _)
          _ = 2 ^ p * (q ^ (-3 : ℝ) * q ^ p) := by ring
          _ = 2 ^ p * q ^ (p - 3) := by
            rw [← Real.rpow_add hqpos']
            congr 2 <;> ring
          _ = 2 ^ p * q ^ σ := by dsimp [p]; ring
      have hfactor' : q ^ (-3 : ℝ) ≤ 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
        simpa [mul_div_assoc] using hfactor
      have hqexp : q ^ (σ - (n : ℝ)) ≤ q ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq (by linarith)
      have htail' : ‖g z‖ * q ^ σ ≤ Cn * q ^ (-3 : ℝ) := by
        calc
          ‖g z‖ * q ^ σ ≤ (Cn * q ^ (-(n : ℝ))) * q ^ σ :=
            mul_le_mul_of_nonneg_right htail (Real.rpow_nonneg hqnonneg' σ)
          _ = Cn * q ^ (σ - (n : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hqpos']
            congr 1
            ring
          _ ≤ Cn * q ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left hqexp hCn
      calc
        ‖g z‖ * q ^ σ ≤ Cn * q ^ (-3 : ℝ) := htail'
        _ ≤ Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
          mul_le_mul_of_nonneg_left hfactor' hCn
        _ = Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    have hbound : ‖g z‖ * q ^ σ ≤ C * (q ^ σ / (1 + q) ^ p) := by
      dsimp [C]
      have hratio : 0 ≤ 2 ^ p * (q ^ σ / (1 + q) ^ p) := by positivity
      by_cases hq : q ≤ 1
      · calc
          ‖g z‖ * q ^ σ ≤ C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := hsmall hq
          _ = C0 * (2 ^ p * (q ^ σ / (1 + q) ^ p)) := by ring
          _ ≤ max C0 Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hratio
          _ = max C0 Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
      · calc
          ‖g z‖ * q ^ σ ≤ Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) :=
            hlarge (le_of_not_ge hq)
          _ = Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) := by ring
          _ ≤ max C0 Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hratio
          _ = max C0 Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    simpa [bridgeComplexMajorant, q, p, hz] using hbound

private theorem pRadialSchwartzWeightBound_uniformScale
    (g : SchwartzMap ℂ ℂ) (σ δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ → ∀ z : ℂ,
      ‖g ((Real.exp (t / 2) : ℂ) * z)‖ * Complex.normSq z ^ σ ≤
        C * bridgeComplexMajorant σ z := by
  obtain ⟨C₀, hC₀, hbase⟩ := pRadialSchwartzWeightBound g σ hσ
  let b : ℝ := Real.exp (-δ / 2)
  let c : ℝ := min 1 (b ^ 2)
  let p : ℝ := σ + 3
  let C : ℝ := C₀ * c ^ (-p)
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := lt_min zero_lt_one (sq_pos_of_pos hb)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcb : c ≤ b ^ 2 := min_le_right _ _
  have hp : 0 < p := by dsimp [p]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht z
  let a : ℝ := Real.exp (t / 2)
  have ha : 0 < a := Real.exp_pos _
  have hta : b ≤ a := by
    dsimp [a, b]
    apply Real.exp_le_exp.mpr
    linarith [neg_abs_le t, ht]
  have hqa : Complex.normSq ((a : ℂ) * z) = a ^ 2 * Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    ring
  by_cases hz : z = 0
  · subst z
    simp [bridgeComplexMajorant, hσ.ne']
  · have hq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hqa_pos : 0 < Complex.normSq ((a : ℂ) * z) := by
      rw [hqa]
      positivity
    have hden : 0 < (1 + Complex.normSq ((a : ℂ) * z)) ^ p :=
      Real.rpow_pos_of_pos (by positivity) p
    have hqpow : 0 < Complex.normSq ((a : ℂ) * z) ^ σ :=
      Real.rpow_pos_of_pos hqa_pos σ
    have hpoint := hbase ((a : ℂ) * z)
    have hnorm : ‖g ((a : ℂ) * z)‖ ≤ C₀ /
        (1 + Complex.normSq ((a : ℂ) * z)) ^ p := by
      have haz : (a : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hz
      have hmul :
          Complex.normSq ((a : ℂ) * z) ^ σ *
            (‖g ((a : ℂ) * z)‖ *
              (1 + Complex.normSq ((a : ℂ) * z)) ^ p) ≤
            Complex.normSq ((a : ℂ) * z) ^ σ * C₀ := by
        have hpoint' :
            ‖g ((a : ℂ) * z)‖ * Complex.normSq ((a : ℂ) * z) ^ σ ≤
              C₀ * (Complex.normSq ((a : ℂ) * z) ^ σ /
                (1 + Complex.normSq ((a : ℂ) * z)) ^ p) := by
          simpa [bridgeComplexMajorant, p, haz] using hpoint
        calc
          _ = (‖g ((a : ℂ) * z)‖ * Complex.normSq ((a : ℂ) * z) ^ σ) *
                (1 + Complex.normSq ((a : ℂ) * z)) ^ p := by ring
          _ ≤ (C₀ * (Complex.normSq ((a : ℂ) * z) ^ σ /
                (1 + Complex.normSq ((a : ℂ) * z)) ^ p)) *
                (1 + Complex.normSq ((a : ℂ) * z)) ^ p :=
                  mul_le_mul_of_nonneg_right hpoint' (Real.rpow_nonneg (by positivity) p)
          _ = _ := by field_simp [hden.ne'] <;> ring
      have hnormden : ‖g ((a : ℂ) * z)‖ *
          (1 + Complex.normSq ((a : ℂ) * z)) ^ p ≤ C₀ :=
        le_of_mul_le_mul_left hmul hqpow
      exact (le_div_iff₀ hden).2 hnormden
    have hcscale : c * (1 + Complex.normSq z) ≤
        1 + Complex.normSq ((a : ℂ) * z) := by
      rw [hqa]
      have hca : c ≤ a ^ 2 := le_trans hcb (pow_le_pow_left₀ (by linarith) hta 2)
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (Complex.normSq_nonneg z),
        mul_nonneg (sub_nonneg.mpr hca) (Complex.normSq_nonneg z)]
    have hdenCompare :
        (1 + Complex.normSq ((a : ℂ) * z)) ^ p ≥
          c ^ p * (1 + Complex.normSq z) ^ p := by
      calc
        _ = (1 + Complex.normSq ((a : ℂ) * z)) ^ p := rfl
        _ ≥ (c * (1 + Complex.normSq z)) ^ p :=
          Real.rpow_le_rpow (by positivity) hcscale hp.le
        _ = _ := by rw [Real.mul_rpow hc.le (by positivity)]
    have hratio :
        (‖g ((a : ℂ) * z)‖ * Complex.normSq z ^ σ) ≤
          C₀ * c ^ (-p) *
            (Complex.normSq z ^ σ / (1 + Complex.normSq z) ^ p) := by
      calc
        _ ≤ (C₀ / (1 + Complex.normSq ((a : ℂ) * z)) ^ p) *
              Complex.normSq z ^ σ :=
                mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (by positivity) σ)
        _ ≤ (C₀ / (c ^ p * (1 + Complex.normSq z) ^ p)) *
              Complex.normSq z ^ σ := by
                exact mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_left hC₀
                    (mul_pos (Real.rpow_pos_of_pos hc p)
                      (Real.rpow_pos_of_pos (by positivity) p)) hdenCompare)
                  (Real.rpow_nonneg (by positivity) σ)
        _ = _ := by
          rw [Real.rpow_neg hc.le]
          field_simp [hc.ne', (Real.rpow_pos_of_pos hc p).ne',
            (Real.rpow_pos_of_pos (by positivity) p).ne']
    simpa [a, bridgeComplexMajorant, C, p, hz] using hratio

private theorem pComplexCpow_norm (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    ‖(Complex.normSq z : ℂ) ^ s‖ = Complex.normSq z ^ s.re := by
  by_cases hz : z = 0
  · subst z
    simpa only [Complex.normSq_zero, Complex.ofReal_zero] using
      (Complex.norm_cpow_eq_rpow_re_of_nonneg (x := 0) (y := s) (by norm_num)
        (ne_of_gt hs))
  · exact Complex.norm_cpow_eq_rpow_re_of_pos (Complex.normSq_pos.mpr hz) s

private theorem pComplexCpow_integrable (g : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs : 0 < s.re) :
    Integrable (fun z : ℂ => g z * (Complex.normSq z : ℂ) ^ s) A1.Theta.mulHaarC := by
  have hpowCont : Continuous (fun z : ℂ => (Complex.normSq z : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.2
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const (Complex.normSq z) s (Or.inl hs)).comp
      Complex.continuous_normSq.continuousAt
  have hmeas : AEStronglyMeasurable
      (fun z : ℂ => g z * (Complex.normSq z : ℂ) ^ s) A1.Theta.mulHaarC :=
    (g.continuous.mul hpowCont).aestronglyMeasurable
  have hnorm (z : ℂ) :
      ‖g z * (Complex.normSq z : ℂ) ^ s‖ =
        ‖g z‖ * Complex.normSq z ^ s.re := by
    rw [norm_mul, pComplexCpow_norm s hs z]
  have hreal := ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable
    g s.re hs
  have hnormInt : Integrable
      (fun z : ℂ => ‖g z * (Complex.normSq z : ℂ) ^ s‖) A1.Theta.mulHaarC :=
    hreal.congr (Filter.Eventually.of_forall fun z => (hnorm z).symm)
  exact (integrable_norm_iff hmeas).1 hnormInt

private theorem pFiniteCpow_norm {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (s : ℂ) (hs : 0 < s.re) (y : v.adicCompletion F) :
    ‖(absFin v y : ℂ) ^ s‖ = absFin v y ^ s.re := by
  have hy0 : 0 ≤ absFin v y := by
    rw [Theta.absFin_eq_norm]
    exact norm_nonneg _
  by_cases hy : absFin v y = 0
  · rw [hy]
    change ‖(0 : ℂ) ^ s‖ = (0 : ℝ) ^ s.re
    exact Complex.norm_cpow_eq_rpow_re_of_nonneg (x := 0) (y := s) (by norm_num)
      (ne_of_gt hs)
  · exact Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_le_of_ne hy0 (Ne.symm hy)) s

private theorem pFiniteCpow_integrable {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y => f y * (absFin v y : ℂ) ^ s) (Theta.mulHaarFin μ) := by
  have hAbsCont : Continuous (absFin v) := by
    have hEq : absFin v = fun y : v.adicCompletion F => ‖y‖ := by
      funext y
      exact Theta.absFin_eq_norm v y
    rw [hEq]
    exact continuous_norm
  have hpowCont : Continuous (fun y => (absFin v y : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.2
    intro y
    exact (Complex.continuousAt_ofReal_cpow_const (absFin v y) s (Or.inl hs)).comp
      hAbsCont.continuousAt
  have hmeas : AEStronglyMeasurable
      (fun y => f y * (absFin v y : ℂ) ^ s) (Theta.mulHaarFin μ) :=
    (hf.mul hpowCont).aestronglyMeasurable
  have hreal := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc s.re hs
  have hnorm (y : v.adicCompletion F) :
      ‖f y * (absFin v y : ℂ) ^ s‖ = ‖f y‖ * absFin v y ^ s.re := by
    rw [norm_mul, pFiniteCpow_norm v s hs y]
  have hnormInt : Integrable
      (fun y => ‖f y * (absFin v y : ℂ) ^ s‖) (Theta.mulHaarFin μ) :=
    hreal.congr (Filter.Eventually.of_forall fun y => (hnorm y).symm)
  exact (integrable_norm_iff hmeas).1 hnormInt

private theorem pMulHaarS_integral_prod
    (fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fArch : ∀ w : InfinitePlace F, ℂ → ℂ)
    (hFin : ∀ v : S.Sf, Integrable (fFin v) (Theta.mulHaarFin (μ v.1)))
    (hArch : ∀ w : InfinitePlace F, Integrable (fArch w) Theta.mulHaarC) :
    ∫ y : S.FS, (∏ v : S.Sf, fFin v (y.1 v)) *
      ∏ w : InfinitePlace F, fArch w (y.2 w) ∂Theta.mulHaarS S μ =
    (∏ v : S.Sf, ∫ z, fFin v z ∂Theta.mulHaarFin (μ v.1)) *
      ∏ w : InfinitePlace F, ∫ z, fArch w z ∂Theta.mulHaarC := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let μArch : Measure (InfinitePlace F → ℂ) :=
    Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC
  let fFinPi : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun y =>
    ∏ v : S.Sf, fFin v (y v)
  let fArchPi : (InfinitePlace F → ℂ) → ℂ := fun y =>
    ∏ w : InfinitePlace F, fArch w (y w)
  letI : ∀ v : S.Sf, SigmaFinite (μ v.1).μ := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    exact inferInstance
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) := fun v => by
    change SigmaFinite ((μ v.1).μ.withDensity fun z => ENNReal.ofReal (absFin v.1 z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SigmaFinite Theta.mulHaarC := by
    change SigmaFinite (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SFinite μFin := by
    dsimp [μFin]
    infer_instance
  letI : SFinite μArch := by
    dsimp [μArch]
    infer_instance
  have hFinPi : Integrable fFinPi μFin := by
    dsimp [fFinPi, μFin]
    exact Integrable.fintype_prod_dep hFin
  have hArchPi : Integrable fArchPi μArch := by
    dsimp [fArchPi, μArch]
    exact Integrable.fintype_prod_dep hArch
  have hprod := MeasureTheory.integral_prod_mul (μ := μFin) (ν := μArch)
    fFinPi fArchPi
  have hfinFactor := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun v : S.Sf => Theta.mulHaarFin (μ v.1)) (fun v z => fFin v z)
  have harchFactor := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun w : InfinitePlace F => Theta.mulHaarC) (fun w z => fArch w z)
  change (∫ p : (∀ v : S.Sf, v.1.adicCompletion F) ×
      (InfinitePlace F → ℂ), fFinPi p.1 * fArchPi p.2 ∂(μFin.prod μArch)) = _
  calc
    _ = (∫ z, fFinPi z ∂μFin) * ∫ z, fArchPi z ∂μArch := hprod
    _ = _ := by
      simp only [fFinPi, fArchPi, μFin, μArch]
      rw [hfinFactor, harchFactor]

private theorem pMulHaarS_integrable_prod
    (fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fArch : ∀ w : InfinitePlace F, ℂ → ℂ)
    (hFin : ∀ v : S.Sf, Integrable (fFin v) (Theta.mulHaarFin (μ v.1)))
    (hArch : ∀ w : InfinitePlace F, Integrable (fArch w) Theta.mulHaarC) :
    Integrable (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) *
      ∏ w : InfinitePlace F, fArch w (y.2 w)) (Theta.mulHaarS S μ) := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let μArch : Measure (InfinitePlace F → ℂ) :=
    Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC
  let fFinPi : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun y =>
    ∏ v : S.Sf, fFin v (y v)
  let fArchPi : (InfinitePlace F → ℂ) → ℂ := fun y =>
    ∏ w : InfinitePlace F, fArch w (y w)
  letI : ∀ v : S.Sf, SigmaFinite (μ v.1).μ := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    exact inferInstance
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) := fun v => by
    change SigmaFinite ((μ v.1).μ.withDensity fun z => ENNReal.ofReal (absFin v.1 z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SigmaFinite Theta.mulHaarC := by
    change SigmaFinite (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹)
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  letI : SFinite μFin := by dsimp [μFin]; infer_instance
  letI : SFinite μArch := by dsimp [μArch]; infer_instance
  have hFinPi : Integrable fFinPi μFin := by
    dsimp [fFinPi, μFin]
    exact Integrable.fintype_prod_dep hFin
  have hArchPi : Integrable fArchPi μArch := by
    dsimp [fArchPi, μArch]
    exact Integrable.fintype_prod_dep hArch
  have hprod := hFinPi.mul_prod hArchPi
  change Integrable (fun p : (∀ v : S.Sf, v.1.adicCompletion F) ×
      (InfinitePlace F → ℂ) => fFinPi p.1 * fArchPi p.2) (μFin.prod μArch)
  exact hprod

noncomputable def pSheetMulScale : ℂ :=
  ((ENNReal.ofReal Real.pi)⁻¹).toReal

private theorem pCpow_mul_nonneg_aux (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (s : ℂ) (hs : 0 < s.re) :
    ((x * y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s * (y : ℂ) ^ s := by
  by_cases hx0 : x = 0
  · subst x
    have hsne : s ≠ 0 := by
      intro h
      subst s
      simp at hs
    simp [hsne]
  by_cases hy0 : y = 0
  · subst y
    have hsne : s ≠ 0 := by
      intro h
      subst s
      simp at hs
    simp [hsne]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hprod : 0 < x * y := mul_pos hxpos hypos
  have hlogProd : Complex.log ((x * y : ℝ) : ℂ) =
      ((Real.log x + Real.log y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hprod.le, Real.log_mul hxpos.ne' hypos.ne']
  have hlogX : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hxpos.le).symm
  have hlogY : Complex.log (y : ℂ) = (Real.log y : ℂ) :=
    (Complex.ofReal_log hypos.le).symm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hprod.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxpos.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hypos.ne'), hlogProd,
    hlogX, hlogY, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem pCpow_finset_prod_aux {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (z : ℂ) (hz : 0 < z.re) :
    ((∏ i ∈ s, q i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (q i : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hqS : ∀ j ∈ s, 0 ≤ q j := fun j hj => hq j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      rw [pCpow_mul_nonneg_aux (q i) (∏ j ∈ s, q j)
        (hq i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun j hj => hqS j hj) z hz]
      rw [ih hqS]

theorem pWeightM_factorization
    {H : HilbertData F} {Bd : BData S H} {ϑ : HeckeChar F}
    {bc : BalancedChoices D S H Bd} {v0 : InfinitePlace F}
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (W0 : S.FS → ℂ)
    (hTensor : ∀ y, W0 y =
      (∏ v : S.Sf, (finite v).1 (y.1 v)) * pArchProduct arch y.2)
    (hcompact : HasCompactSupport W0) (hW0ne : ∃ y, W0 y ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y : S.FS => S.fourier A sd.measure W0 y *
      (S.absS y : ℂ) ^ s) (R.sheets.mul) ∧
    (∫ y : S.FS, S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s ∂(R.sheets.mul)) =
      pSheetMulScale * pWeightFourierScale sd μ *
        ((∏ v : S.Sf, ∫ z : v.1.adicCompletion F,
          ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1) (finite v).1 z *
            (absFin v.1 z : ℂ) ^ s ∂Theta.mulHaarFin (μ v.1)) *
          ∏ w : InfinitePlace F, ∫ z : ℂ,
            ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w) z *
              (Complex.normSq z : ℂ) ^ s ∂Theta.mulHaarC) := by
  classical
  let fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ := fun v z =>
    ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
      v.1 A (μ v.1) (finite v).1 z * (absFin v.1 z : ℂ) ^ s
  let fArch : ∀ w : InfinitePlace F, ℂ → ℂ := fun w z =>
    ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w) z *
      (Complex.normSq z : ℂ) ^ s
  have hFinInt : ∀ v : S.Sf, Integrable (fFin v) (Theta.mulHaarFin (μ v.1)) := by
    intro v
    let f : v.1.adicCompletion F → ℂ := (finite v).1
    let ft : v.1.adicCompletion F → ℂ :=
      ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1) f
    obtain ⟨k, hperiod⟩ := ArtinPrimitiveRoots.Proofs.a2_weights.finiteTest_exists_period_ball
      v.1 f (finite v).2.2.2 (finite v).2.2.1
    have hftCompact : HasCompactSupport ft :=
      ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier_hasCompactSupport_of_period
        v.1 A (μ v.1) f k hperiod
    have hftCont : Continuous ft :=
      (ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier_isLocallyConstant
        v.1 A (μ v.1) f (finite v).2.2.1).continuous
    simpa [fFin, ft, f] using
      pFiniteCpow_integrable v.1 (μ v.1) ft hftCont hftCompact s hs
  have hArchInt : ∀ w : InfinitePlace F, Integrable (fArch w) Theta.mulHaarC := by
    intro w
    dsimp [fArch]
    exact pComplexCpow_integrable
      (ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (arch w)) s hs
  have hProductInt := pMulHaarS_integrable_prod fFin fArch hFinInt hArchInt
  have hProductIntegral := pMulHaarS_integral_prod fFin fArch hFinInt hArchInt
  have hPoint (y : S.FS) :
      S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s =
        pWeightFourierScale sd μ *
          ((∏ v : S.Sf, fFin v (y.1 v)) * ∏ w : InfinitePlace F, fArch w (y.2 w)) := by
    have hFourier := pWeightFourier_local_actual (S := S) (μ := μ) (A := A)
      sd arch finite W0 hTensor hcompact hW0ne y
    have hFinCombine :
        (∏ v : S.Sf,
          ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
            v.1 A (μ v.1) (finite v).1 (y.1 v) *
              (absFin v.1 (y.1 v) : ℂ) ^ s) =
          (∏ v : S.Sf, ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
            v.1 A (μ v.1) (finite v).1 (y.1 v)) *
            ∏ v : S.Sf, (absFin v.1 (y.1 v) : ℂ) ^ s := by
      simp only [Finset.prod_mul_distrib]
    have hArchCombine :
        (∏ w : InfinitePlace F,
          ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
            (arch w) (y.2 w) * (Complex.normSq (y.2 w) : ℂ) ^ s) =
          (∏ w : InfinitePlace F,
            ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
              (arch w) (y.2 w)) *
            ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s := by
      simp only [Finset.prod_mul_distrib]
    have hfinNonneg (v : S.Sf) : 0 ≤ absFin v.1 (y.1 v) := by
      rw [Theta.absFin_eq_norm]
      exact norm_nonneg _
    have harchNonneg (w : InfinitePlace F) : 0 ≤ Complex.normSq (y.2 w) :=
      Complex.normSq_nonneg _
    have hfinBase : 0 ≤ ∏ v : S.Sf, absFin v.1 (y.1 v) := by
      apply Finset.prod_nonneg
      intro v hv
      exact hfinNonneg v
    have harchBase : 0 ≤ ∏ w : InfinitePlace F, Complex.normSq (y.2 w) := by
      apply Finset.prod_nonneg
      intro w hw
      exact harchNonneg w
    have hSabs : S.absS y =
        (∏ v : S.Sf, absFin v.1 (y.1 v)) * ∏ w : InfinitePlace F, Complex.normSq (y.2 w) := rfl
    have hfinPow :
        ((∏ v : S.Sf, absFin v.1 (y.1 v) : ℝ) : ℂ) ^ s =
          ∏ v : S.Sf, (absFin v.1 (y.1 v) : ℂ) ^ s := by
      simpa using pCpow_finset_prod_aux (Finset.univ : Finset S.Sf)
        (fun v : S.Sf => absFin v.1 (y.1 v)) (by intro v hv; exact hfinNonneg v) s hs
    have harchPow :
        ((∏ w : InfinitePlace F, Complex.normSq (y.2 w) : ℝ) : ℂ) ^ s =
          ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s := by
      simpa using pCpow_finset_prod_aux (Finset.univ : Finset (InfinitePlace F))
        (fun w : InfinitePlace F => Complex.normSq (y.2 w))
        (by intro w hw; exact harchNonneg w) s hs
    have hSabsPow : (S.absS y : ℂ) ^ s =
        (∏ v : S.Sf, (absFin v.1 (y.1 v) : ℂ) ^ s) *
          ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s := by
      rw [hSabs, pCpow_mul_nonneg_aux _ _ hfinBase harchBase s hs, hfinPow, harchPow]
    rw [hFourier, hSabsPow]
    calc
      _ = pWeightFourierScale sd μ *
          ((∏ v : S.Sf,
            ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
              v.1 A (μ v.1) (finite v).1 (y.1 v)) *
            ∏ w : InfinitePlace F,
              ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
                (arch w) (y.2 w)) *
          ((∏ v : S.Sf, (absFin v.1 (y.1 v) : ℂ) ^ s) *
            ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s) := by ring
      _ = pWeightFourierScale sd μ *
          ((∏ v : S.Sf,
            ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier
              v.1 A (μ v.1) (finite v).1 (y.1 v) * (absFin v.1 (y.1 v) : ℂ) ^ s) *
            ∏ w : InfinitePlace F,
              ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz
          (arch w) (y.2 w) * (Complex.normSq (y.2 w) : ℂ) ^ s) := by
            rw [hFinCombine, hArchCombine]
            ring
      _ = _ := by
        rfl
  have hGlobalInt : Integrable
      (fun y : S.FS => S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s)
      (Theta.mulHaarS S μ) := by
    have heq : (fun y : S.FS => S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s) =
        fun y => pWeightFourierScale sd μ *
          ((∏ v : S.Sf, fFin v (y.1 v)) * ∏ w : InfinitePlace F, fArch w (y.2 w)) :=
      funext hPoint
    rw [heq]
    simpa [mul_comm] using hProductInt.const_mul (pWeightFourierScale sd μ)
  have hIntegralTheta :
      ∫ y : S.FS, S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s
        ∂Theta.mulHaarS S μ =
        pWeightFourierScale sd μ *
          ((∏ v : S.Sf, ∫ z, fFin v z ∂Theta.mulHaarFin (μ v.1)) *
            ∏ w : InfinitePlace F, ∫ z, fArch w z ∂Theta.mulHaarC) := by
    calc
      _ = ∫ y : S.FS, pWeightFourierScale sd μ *
          ((∏ v : S.Sf, fFin v (y.1 v)) * ∏ w : InfinitePlace F, fArch w (y.2 w))
          ∂Theta.mulHaarS S μ := by
            apply integral_congr_ae
            filter_upwards with y
            exact hPoint y
      _ = pWeightFourierScale sd μ *
          ∫ y : S.FS, (∏ v : S.Sf, fFin v (y.1 v)) * ∏ w : InfinitePlace F, fArch w (y.2 w)
            ∂Theta.mulHaarS S μ := by rw [integral_const_mul]
      _ = _ := by rw [hProductIntegral]
  have hIntR : Integrable
      (fun y : S.FS => S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s) R.sheets.mul := by
    rw [R.sheets.mul_eq]
    have hpi0 : ENNReal.ofReal Real.pi ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
    have hpiTop : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
    apply (integrable_smul_measure
      (ENNReal.inv_ne_zero.mpr hpiTop)
      (ENNReal.inv_ne_top.mpr hpi0)).2
    exact hGlobalInt
  have hScaleR :
      ∫ y : S.FS, S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s ∂(R.sheets.mul) =
        pSheetMulScale *
          ∫ y : S.FS, S.fourier A sd.measure W0 y * (S.absS y : ℂ) ^ s
            ∂Theta.mulHaarS S μ := by
    rw [R.sheets.mul_eq, integral_smul_measure]
    simp [pSheetMulScale, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul]
  constructor
  · exact hIntR
  · rw [hScaleR, hIntegralTheta]
    simp [fFin, fArch]
    ring

private theorem pExpMul_cpow (t q : ℝ) (hq : 0 < q) (s : ℂ) :
    ((Real.exp t * q : ℝ) : ℂ) ^ s =
      Complex.exp ((t : ℂ) * s) * (q : ℂ) ^ s := by
  have he : 0 < Real.exp t := Real.exp_pos _
  have hprod : 0 < Real.exp t * q := mul_pos he hq
  have hlogProd : Complex.log ((Real.exp t * q : ℝ) : ℂ) =
      ((t + Real.log q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hprod.le, Real.log_mul he.ne' hq.ne', Real.log_exp]
  have hlogQ : Complex.log (q : ℂ) = (Real.log q : ℂ) :=
    (Complex.ofReal_log hq.le).symm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hprod.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'), hlogProd, hlogQ,
    Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem pCpow_mul_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (s : ℂ) (hs : 0 < s.re) :
    ((x * y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s * (y : ℂ) ^ s := by
  by_cases hx0 : x = 0
  · subst x
    have hsne : s ≠ 0 := by
      intro h
      subst s
      simp at hs
    simp [hsne]
  by_cases hy0 : y = 0
  · subst y
    have hsne : s ≠ 0 := by
      intro h
      subst s
      simp at hs
    simp [hsne]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hprod : 0 < x * y := mul_pos hxpos hypos
  have hlogProd : Complex.log ((x * y : ℝ) : ℂ) =
      ((Real.log x + Real.log y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hprod.le, Real.log_mul hxpos.ne' hypos.ne']
  have hlogX : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hxpos.le).symm
  have hlogY : Complex.log (y : ℂ) = (Real.log y : ℂ) :=
    (Complex.ofReal_log hypos.le).symm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hprod.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxpos.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hypos.ne'), hlogProd,
    hlogX, hlogY, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem pCpow_finset_prod {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (z : ℂ) (hz : 0 < z.re) :
    ((∏ i ∈ s, q i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (q i : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hqS : ∀ j ∈ s, 0 ≤ q j := fun j hj =>
        hq j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      rw [pCpow_mul_nonneg (q i) (∏ j ∈ s, q j) (hq i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun j hj => hqS j hj) z hz]
      rw [ih hqS]

private theorem pComplexMellin_euler (g : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs : 0 < s.re) :
    (∫ z : ℂ, pEulerSchwartz g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC) =
      -s * ∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC := by
  let q : ℂ → ℝ := Complex.normSq
  let μ : Measure ℂ := A1.Theta.mulHaarC
  let F : ℝ → ℂ → ℂ := fun t z =>
    g ((Real.exp (t / 2) : ℂ) * z) * (q z : ℂ) ^ s
  let F' : ℝ → ℂ → ℂ := fun t z =>
    pEulerSchwartz g ((Real.exp (t / 2) : ℂ) * z) * (q z : ℂ) ^ s
  have hpowCont : Continuous (fun z : ℂ => (q z : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.2
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const (q z) s (Or.inl hs)).comp
      Complex.continuous_normSq.continuousAt
  have hF_meas (t : ℝ) : AEStronglyMeasurable (F t) μ := by
    apply ((g.continuous.comp ?_).mul hpowCont).aestronglyMeasurable
    fun_prop
  have hF_int : Integrable (F 0) μ := by
    convert pComplexCpow_integrable g s hs using 1 <;> ext z <;> simp [F, q]
  have hF'_meas : AEStronglyMeasurable (F' 0) μ := by
    apply ((pEulerSchwartz g).continuous.comp ?_ |>.mul hpowCont).aestronglyMeasurable
    fun_prop
  obtain ⟨C, hC, hscale⟩ := pRadialSchwartzWeightBound_uniformScale
    (pEulerSchwartz g) s.re 1 hs (by norm_num)
  let B : ℂ → ℝ := fun z => C * bridgeComplexMajorant s.re z
  have hB : Integrable B μ := by
    dsimp [B]
    exact (bridgeComplexMajorant_integrable s.re hs).const_mul C
  have hbound : ∀ᵐ z ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t z‖ ≤ B z := by
    filter_upwards with z
    intro t ht
    have ht' : |t| ≤ 1 := by
      have ht'' : dist t 0 < 1 := by simpa [Metric.mem_ball] using ht
      simpa [Real.dist_eq] using ht''.le
    have h := hscale t ht' z
    simpa [F', B, q, Complex.norm_mul, pComplexCpow_norm s hs z] using h
  have hdiff : ∀ᵐ z ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (F · z) (F' t z) t := by
    filter_upwards with z
    intro t ht
    have hdiffAt : DifferentiableAt ℝ
        (fun u : ℝ => g ((Real.exp (u / 2) : ℂ) * z)) t := by
      fun_prop
    have hchain : HasDerivAt
        (fun u : ℝ => g ((Real.exp (u / 2) : ℂ) * z))
        (pEulerSchwartz g ((Real.exp (t / 2) : ℂ) * z)) t := by
      convert hdiffAt.hasDerivAt using 1
      exact (pEulerChain g z t).symm
    simpa [F, F'] using hchain.mul_const ((q z : ℂ) ^ s)
  have hUnder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas hbound hB hdiff
  have hF_scalar (t : ℝ) : ∫ z, F t z ∂μ =
      Complex.exp (-((t : ℂ) * s)) * ∫ z, g z * (q z : ℂ) ^ s ∂μ := by
    let a : ℝ := Real.exp (t / 2)
    have ha : 0 < a := Real.exp_pos _
    have hqscale (z : ℂ) : q ((a : ℂ) * z) = a ^ 2 * q z := by
      change Complex.normSq ((a : ℂ) * z) = a ^ 2 * Complex.normSq z
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      ring
    have ha2 : a ^ 2 = Real.exp t := by
      dsimp [a]
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    have hpow (z : ℂ) : (q z : ℂ) ^ s =
        Complex.exp (-((t : ℂ) * s)) * (q ((a : ℂ) * z) : ℂ) ^ s := by
      by_cases hz : z = 0
      · subst z
        have hsne : s ≠ 0 := by
          intro h
          subst s
          simp at hs
        simp [q, hsne]
      · have hqpos : 0 < q z := Complex.normSq_pos.mpr hz
        rw [hqscale, ha2]
        have hmul := pExpMul_cpow t (q z) hqpos s
        calc
          (q z : ℂ) ^ s =
              (Complex.exp (-((t : ℂ) * s)) * Complex.exp ((t : ℂ) * s)) *
                (q z : ℂ) ^ s := by
                  rw [← Complex.exp_add]
                  simp
          _ = Complex.exp (-((t : ℂ) * s)) *
                ((Real.exp t * q z : ℝ) : ℂ) ^ s := by
                  rw [hmul]
                  ring
    have hpoint (z : ℂ) : F t z =
        Complex.exp (-((t : ℂ) * s)) *
          (g ((a : ℂ) * z) * (q ((a : ℂ) * z) : ℂ) ^ s) := by
      simp only [F, q, a]
      rw [hpow]
      ring
    calc
      _ = ∫ z, Complex.exp (-((t : ℂ) * s)) *
          (g ((a : ℂ) * z) * (q ((a : ℂ) * z) : ℂ) ^ s) ∂μ := by
            apply integral_congr_ae
            filter_upwards with z
            exact hpoint z
      _ = Complex.exp (-((t : ℂ) * s)) *
          ∫ z, g ((a : ℂ) * z) * (q ((a : ℂ) * z) : ℂ) ^ s ∂μ := by
            rw [integral_const_mul]
      _ = _ := by
            rw [← mulHaarC_integral_comp_smul a ha
              (fun z : ℂ => g z * (q z : ℂ) ^ s)]
            simp [μ]
  have hFfun : (fun t : ℝ => ∫ z, F t z ∂μ) =
      fun t : ℝ => Complex.exp (-((t : ℂ) * s)) *
        ∫ z, g z * (q z : ℂ) ^ s ∂μ := funext hF_scalar
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * s))) (-s) 0 := by
    convert hasDerivAt_exp_smul_const (𝕂 := ℝ) (-s) (0 : ℝ) using 1
    · ext t
      rw [← Complex.exp_eq_exp_ℂ]
      congr 1
      change -((t : ℂ) * s) = (t : ℂ) * (-s)
      ring
    · simp
  have hscalar := hexp.mul_const (∫ z, g z * (q z : ℂ) ^ s ∂μ)
  rw [hFfun] at hUnder
  have hderivEq := hUnder.2.unique hscalar
  simpa [F', q, μ] using hderivEq

private theorem pComplexMellin_radialIter (n : ℕ) (g : SchwartzMap ℂ ℂ)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ z : ℂ, pRadialIter n g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC) =
      (-s) ^ n * ∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC := by
  induction n with
  | zero => simp [pRadialIter]
  | succ n ih =>
      simp only [pRadialIter]
      rw [pComplexMellin_euler (pRadialIter n g) s hs, ih]
      ring

theorem pComplexWeighted_integral_strip_le (g : SchwartzMap ℂ ℂ)
    (l r σ : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hσl : l ≤ σ) (hσr : σ ≤ r) :
    (∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ σ ∂A1.Theta.mulHaarC) ≤
      (∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ l ∂A1.Theta.mulHaarC) +
        ∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ r ∂A1.Theta.mulHaarC := by
  have hσ : 0 < σ := lt_of_lt_of_le hl hσl
  have hL := ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable g l hl
  have hR := ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable g r
    (lt_of_lt_of_le hl hlr)
  have hS := ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable g σ hσ
  have hsum : Integrable (fun z : ℂ =>
      ‖g z‖ * Complex.normSq z ^ l + ‖g z‖ * Complex.normSq z ^ r)
      A1.Theta.mulHaarC := hL.add hR
  have hpoint (z : ℂ) :
      ‖g z‖ * Complex.normSq z ^ σ ≤
        ‖g z‖ * Complex.normSq z ^ l + ‖g z‖ * Complex.normSq z ^ r := by
    have hq : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
    by_cases hq0 : Complex.normSq z = 0
    · simp [hq0, hσ.ne', hl.ne', (lt_of_lt_of_le hl hlr).ne']
    · have hqpos : 0 < Complex.normSq z := lt_of_le_of_ne hq (Ne.symm hq0)
      by_cases hq1 : Complex.normSq z ≤ 1
      · have hp := Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hσl
        calc
          ‖g z‖ * Complex.normSq z ^ σ ≤ ‖g z‖ * Complex.normSq z ^ l :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_right
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq r))
      · have hqge : 1 ≤ Complex.normSq z := le_of_not_ge hq1
        have hp := Real.rpow_le_rpow_of_exponent_le hqge hσr
        calc
          ‖g z‖ * Complex.normSq z ^ σ ≤ ‖g z‖ * Complex.normSq z ^ r :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_of_le
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq l)) le_rfl
  exact (integral_mono_ae hS hsum (Filter.Eventually.of_forall hpoint)).trans_eq
    (integral_add hL hR)

theorem pComplexMellin_norm_bound (g : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs : 0 < s.re) :
    ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤
      ∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ s.re ∂A1.Theta.mulHaarC := by
  have hInt := pComplexCpow_integrable g s hs
  calc
    _ ≤ ∫ z : ℂ, ‖g z * (Complex.normSq z : ℂ) ^ s‖ ∂A1.Theta.mulHaarC :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [norm_mul, pComplexCpow_norm s hs z]

theorem pComplexMellin_vertical_decay
    (g : SchwartzMap ℂ ℂ) (l r A0 : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, l ≤ σ → σ ≤ r →
      ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^
        ((σ : ℂ) + (τ : ℂ) * Complex.I) ∂A1.Theta.mulHaarC‖ ≤
          C * (1 + |τ|) ^ (-A0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt A0
  let gn : SchwartzMap ℂ ℂ := pRadialIter n g
  let I0 : ℝ := ∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ l ∂A1.Theta.mulHaarC
  let I1 : ℝ := ∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ r ∂A1.Theta.mulHaarC
  let J0 : ℝ := ∫ z : ℂ, ‖gn z‖ * Complex.normSq z ^ l ∂A1.Theta.mulHaarC
  let J1 : ℝ := ∫ z : ℂ, ‖gn z‖ * Complex.normSq z ^ r ∂A1.Theta.mulHaarC
  have hI0 : 0 ≤ I0 := by
    dsimp [I0]
    exact integral_nonneg fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  have hI1 : 0 ≤ I1 := by
    dsimp [I1]
    exact integral_nonneg fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  have hJ0 : 0 ≤ J0 := by
    dsimp [J0]
    exact integral_nonneg fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  have hJ1 : 0 ≤ J1 := by
    dsimp [J1]
    exact integral_nonneg fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  let C : ℝ := 2 ^ n * (I0 + I1 + J0 + J1 + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro σ τ hσl hσr
  let s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  have hs : 0 < s.re := by dsimp [s]; simp; exact lt_of_lt_of_le hl hσl
  have hsRe : s.re = σ := by simp [s]
  have hsIm : s.im = τ := by simp [s]
  have hsExpr : ((σ : ℂ) + (τ : ℂ) * Complex.I) = s := by simp [s]
  rw [hsExpr]
  have hM : ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤ I0 + I1 := by
    calc
      _ ≤ ∫ z : ℂ, ‖g z‖ * Complex.normSq z ^ σ ∂A1.Theta.mulHaarC := by
        simpa [hsRe] using pComplexMellin_norm_bound g s hs
      _ ≤ _ := by
        simpa [I0, I1] using pComplexWeighted_integral_strip_le g l r σ hl hlr hσl hσr
  have hN : ‖∫ z : ℂ, gn z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤ J0 + J1 := by
    calc
      _ ≤ ∫ z : ℂ, ‖gn z‖ * Complex.normSq z ^ σ ∂A1.Theta.mulHaarC := by
        simpa [hsRe] using pComplexMellin_norm_bound gn s hs
      _ ≤ _ := by
        simpa [J0, J1] using pComplexWeighted_integral_strip_le gn l r σ hl hlr hσl hσr
  have hIter := pComplexMellin_radialIter n g s hs
  change (∫ z : ℂ, gn z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC) = _ at hIter
  have hIterNorm :
      ‖∫ z : ℂ, gn z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ =
        ‖s‖ ^ n * ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ := by
    rw [hIter, norm_mul, norm_pow, norm_neg]
  have hτ : |τ| ≤ ‖s‖ := by rw [← hsIm]; exact Complex.abs_im_le_norm s
  let t : ℝ := |τ|
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hMsmall : ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤ I0 + I1 := hM
  by_cases hlarge : 1 ≤ t
  · have htpos : 0 < t := lt_of_lt_of_le zero_lt_one hlarge
    have hpowNorm : t ^ n ≤ ‖s‖ ^ n :=
      pow_le_pow_left₀ ht0 hτ n
    have hprod : t ^ n *
        ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤ J0 + J1 := by
      calc
        _ ≤ ‖s‖ ^ n *
            ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ :=
              mul_le_mul_of_nonneg_right hpowNorm (norm_nonneg _)
        _ = ‖∫ z : ℂ, gn z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ := hIterNorm.symm
        _ ≤ J0 + J1 := hN
    have hdiv :
        ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤
          (J0 + J1) / t ^ n := by
            apply (le_div_iff₀ (pow_pos htpos n)).2
            simpa [mul_comm] using hprod
    have hpower : (1 + t) ^ A0 ≤ 2 ^ n * t ^ n := by
      calc
        (1 + t) ^ A0 ≤ (2 * t) ^ A0 :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) hA0.le
        _ = 2 ^ A0 * t ^ A0 := Real.mul_rpow (by norm_num) (le_of_lt htpos)
        _ ≤ 2 ^ n * t ^ n := by
          apply mul_le_mul
          · simpa only [Real.rpow_natCast] using
              (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn.le)
          · simpa only [Real.rpow_natCast] using
              (Real.rpow_le_rpow_of_exponent_le hlarge hn.le)
          · positivity
          · positivity
    have hfactor : 1 / t ^ n ≤ 2 ^ n / (1 + t) ^ A0 := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) A0)).2
      calc
        (1 / t ^ n) * (1 + t) ^ A0 ≤ (1 / t ^ n) * (2 ^ n * t ^ n) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = 2 ^ n := by field_simp [pow_ne_zero n htpos.ne']
    have hbound : ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤
        (J0 + J1) * (2 ^ n / (1 + t) ^ A0) := by
      calc
        _ ≤ (J0 + J1) / t ^ n := hdiv
        _ ≤ (J0 + J1) * (2 ^ n / (1 + t) ^ A0) :=
          by
            calc
              _ = (J0 + J1) * (1 / t ^ n) := by rw [div_eq_mul_inv, one_div]
              _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hCbound :
        (J0 + J1) * (2 ^ n / (1 + t) ^ A0) ≤ C / (1 + t) ^ A0 := by
      have hbase : J0 + J1 ≤ I0 + I1 + J0 + J1 + 1 := by nlinarith [hI0, hI1]
      have hnum : (J0 + J1) * 2 ^ n ≤ C := by
        calc
          (J0 + J1) * 2 ^ n ≤ (I0 + I1 + J0 + J1 + 1) * 2 ^ n :=
            mul_le_mul_of_nonneg_right hbase (pow_nonneg (by norm_num) n)
          _ = C := by dsimp [C]; ring
      calc
        _ = ((J0 + J1) * 2 ^ n) / (1 + t) ^ A0 := by ring
        _ ≤ C / (1 + t) ^ A0 :=
          div_le_div_of_nonneg_right hnum (Real.rpow_pos_of_pos (by positivity) A0).le
    have hcalc :
        ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤ C / (1 + t) ^ A0 := by
      calc
        ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤
            (J0 + J1) * (2 ^ n / (1 + t) ^ A0) := hbound
        _ ≤ C / (1 + t) ^ A0 := hCbound
    rw [Real.rpow_neg (by positivity)]
    simpa [t, div_eq_mul_inv] using hcalc
  · have htlt : t < 1 := lt_of_not_ge hlarge
    have hpowSmall : (1 + t) ^ A0 ≤ 2 ^ n := by
      calc
        (1 + t) ^ A0 ≤ 2 ^ A0 :=
          Real.rpow_le_rpow (by positivity) (by linarith) hA0.le
        _ ≤ 2 ^ n := by
          simpa only [Real.rpow_natCast] using
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn.le)
    have hfactor : 1 ≤ 2 ^ n / (1 + t) ^ A0 :=
      (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) A0)).2 (by simpa using hpowSmall)
    have hbound : ‖∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC‖ ≤
        C / (1 + t) ^ A0 := by
      calc
        _ ≤ I0 + I1 := hMsmall
        _ ≤ (I0 + I1 + J0 + J1 + 1) * (2 ^ n / (1 + t) ^ A0) := by
          have hCbase : I0 + I1 ≤ I0 + I1 + J0 + J1 + 1 := by nlinarith [hJ0, hJ1]
          calc
            I0 + I1 ≤ I0 + I1 + J0 + J1 + 1 := hCbase
            _ = (I0 + I1 + J0 + J1 + 1) * 1 := by ring
            _ ≤ (I0 + I1 + J0 + J1 + 1) * (2 ^ n / (1 + t) ^ A0) :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = C / (1 + t) ^ A0 := by
          dsimp [C]
          ring
    rw [Real.rpow_neg (by positivity)]
    simpa [t, div_eq_mul_inv] using hbound

private theorem pRealRpowLog_bound (q ε σ : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    q ^ σ * |Real.log q| ≤ (1 / ε) * (q ^ (σ - ε) + q ^ (σ + ε)) := by
  by_cases hq1 : 1 ≤ q
  · have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
    have hlogpow : Real.log (q ^ ε) = ε * Real.log q := Real.log_rpow hq ε
    have hlogBound : |Real.log q| ≤ q ^ ε / ε := by
      apply (le_div_iff₀ hε).2
      rw [abs_of_nonneg hlog]
      calc
        Real.log q * ε = ε * Real.log q := by ring
        _ = Real.log (q ^ ε) := by rw [hlogpow]
        _ ≤ q ^ ε - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq ε)
        _ ≤ q ^ ε := by linarith
    have hmain : q ^ σ * |Real.log q| ≤ (1 / ε) * q ^ (σ + ε) := by
      calc
        q ^ σ * |Real.log q| ≤ q ^ σ * (q ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlogBound (Real.rpow_nonneg hq.le σ)
        _ = (1 / ε) * (q ^ σ * q ^ ε) := by ring
        _ = (1 / ε) * q ^ (σ + ε) := by rw [← Real.rpow_add hq]
    calc
      q ^ σ * |Real.log q| ≤ (1 / ε) * q ^ (σ + ε) := hmain
      _ ≤ (1 / ε) * (q ^ (σ - ε) + q ^ (σ + ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_add_of_nonneg_left (Real.rpow_nonneg hq.le _)
  · have hq1' : q ≤ 1 := le_of_not_ge hq1
    have hlog : Real.log q ≤ 0 := by
      calc
        Real.log q ≤ Real.log 1 := Real.log_le_log hq hq1'
        _ = 0 := Real.log_one
    have hlogpow : Real.log (q ^ (-ε)) = -ε * Real.log q := Real.log_rpow hq (-ε)
    have hlogBound : |Real.log q| ≤ q ^ (-ε) / ε := by
      apply (le_div_iff₀ hε).2
      rw [abs_of_nonpos hlog]
      calc
        (-Real.log q) * ε = ε * (-Real.log q) := by ring
        _ = Real.log (q ^ (-ε)) := by rw [hlogpow]; ring
        _ ≤ q ^ (-ε) - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq (-ε))
        _ ≤ q ^ (-ε) := by linarith
    have hmain : q ^ σ * |Real.log q| ≤ (1 / ε) * q ^ (σ - ε) := by
      calc
        q ^ σ * |Real.log q| ≤ q ^ σ * (q ^ (-ε) / ε) :=
          mul_le_mul_of_nonneg_left hlogBound (Real.rpow_nonneg hq.le σ)
        _ = (1 / ε) * (q ^ σ * q ^ (-ε)) := by ring
        _ = (1 / ε) * q ^ (σ - ε) := by
          rw [← Real.rpow_add hq]
          rw [show σ + -ε = σ - ε by ring]
    calc
      q ^ σ * |Real.log q| ≤ (1 / ε) * q ^ (σ - ε) := hmain
      _ ≤ (1 / ε) * (q ^ (σ - ε) + q ^ (σ + ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_add_of_nonneg_right (Real.rpow_nonneg hq.le _)

private theorem pComplex_re_close (w s : ℂ) (ε : ℝ) (h : dist w s < ε) :
    |w.re - s.re| < ε := by
  have hnorm : ‖w - s‖ < ε := by simpa [dist_eq_norm] using h
  have h' := Complex.abs_re_le_norm (w - s)
  have hsub : (w - s).re = w.re - s.re := by simp
  rw [hsub] at h'
  exact h'.trans_lt hnorm

theorem pComplexMellin_differentiableAt (g : SchwartzMap ℂ ℂ) (s₀ : ℂ)
    (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ
      (fun s => ∫ z : ℂ, g z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC) s₀ := by
  let q : ℂ → ℝ := Complex.normSq
  let ε : ℝ := s₀.re / 4
  let α : ℝ := s₀.re / 2
  let β : ℝ := 2 * s₀.re
  let B : ℂ → ℝ := fun z => (2 / ε) *
    (‖g z‖ * q z ^ α + ‖g z‖ * q z ^ β)
  let μ : Measure ℂ := A1.Theta.mulHaarC
  let F : ℂ → ℂ → ℂ := fun w z => g z * (q z : ℂ) ^ w
  let F' : ℂ → ℂ → ℂ := fun w z => g z * (q z : ℂ) ^ w * (Real.log (q z) : ℂ)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hαInt : Integrable (fun z : ℂ => ‖g z‖ * q z ^ α) μ := by
    simpa [μ, q, α] using
      ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable g α hα
  have hβInt : Integrable (fun z : ℂ => ‖g z‖ * q z ^ β) μ := by
    simpa [μ, q, β] using
      ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable g β hβ
  have hBInt : Integrable B μ := by
    dsimp [B]
    simpa [mul_comm] using (hαInt.add hβInt).const_mul (2 / ε)
  have hFint : Integrable (F s₀) μ := by
    simpa [F, q, μ] using pComplexCpow_integrable g s₀ hs₀
  have hlogMeas : Measurable (fun z : ℂ => (Real.log (q z) : ℂ)) := by fun_prop
  have hFprimeMeas : AEStronglyMeasurable (F' s₀) μ := by
    have hpowCont : Continuous (fun z : ℂ => (q z : ℂ) ^ s₀) := by
      apply continuous_iff_continuousAt.2
      intro z
      exact (Complex.continuousAt_ofReal_cpow_const (q z) s₀ (Or.inl hs₀)).comp
        Complex.continuous_normSq.continuousAt
    have hMeas : Measurable (F' s₀) := by
      dsimp [F']
      exact (g.continuous.measurable.mul hpowCont.measurable).mul hlogMeas
    exact hMeas.aestronglyMeasurable
  have hFmeas : ∀ᶠ w : ℂ in 𝓝 s₀, AEStronglyMeasurable (F w) μ := by
    filter_upwards [Metric.ball_mem_nhds s₀ hε] with w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    have hpowCont : Continuous (fun z : ℂ => (q z : ℂ) ^ w) := by
      apply continuous_iff_continuousAt.2
      intro z
      exact (Complex.continuousAt_ofReal_cpow_const (q z) w (Or.inl hwRe)).comp
        Complex.continuous_normSq.continuousAt
    exact (g.continuous.mul hpowCont).aestronglyMeasurable
  have hbound : ∀ᵐ z : ℂ ∂μ, ∀ w ∈ Metric.ball s₀ ε, ‖F' w z‖ ≤ B z := by
    filter_upwards with z
    intro w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    have hσlower : α ≤ w.re - ε := by dsimp [α, ε] at *; linarith
    have hσupper : w.re + ε ≤ β := by dsimp [β, ε] at *; linarith
    by_cases hq0 : q z = 0
    · have hwne : w ≠ 0 := by
        intro h
        subst w
        simp at hwRe
      have hzero : F' w z = 0 := by simp [F', q, hq0, hwne]
      rw [hzero]
      simp [B, q, hq0, Real.zero_rpow (ne_of_gt hα), Real.zero_rpow (ne_of_gt hβ)]
    · have hqpos : 0 < q z := lt_of_le_of_ne (Complex.normSq_nonneg z) (Ne.symm hq0)
      have hlogBound := pRealRpowLog_bound (q z) ε w.re hqpos hε
      have hsumPow : q z ^ (w.re - ε) + q z ^ (w.re + ε) ≤
          2 * (q z ^ α + q z ^ β) := by
        by_cases hq1 : q z ≤ 1
        · have hlow : q z ^ (w.re - ε) ≤ q z ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hσlower
          have hhigh : q z ^ (w.re + ε) ≤ q z ^ α := by
            apply Real.rpow_le_rpow_of_exponent_ge hqpos hq1
            dsimp [α, ε]
            linarith [hclose'.1]
          calc
            _ ≤ q z ^ α + q z ^ α := add_le_add hlow hhigh
            _ ≤ 2 * (q z ^ α + q z ^ β) := by
              have hαpow : 0 ≤ q z ^ α := Real.rpow_nonneg (Complex.normSq_nonneg z) _
              have hβpow : 0 ≤ q z ^ β := Real.rpow_nonneg (Complex.normSq_nonneg z) _
              nlinarith
        · have hqge : 1 ≤ q z := le_of_not_ge hq1
          have hlow : q z ^ (w.re - ε) ≤ q z ^ β := by
            apply Real.rpow_le_rpow_of_exponent_le hqge
            dsimp [β, ε]
            linarith [hclose'.2]
          have hhigh : q z ^ (w.re + ε) ≤ q z ^ β :=
            Real.rpow_le_rpow_of_exponent_le hqge hσupper
          calc
            _ ≤ q z ^ β + q z ^ β := add_le_add hlow hhigh
            _ ≤ 2 * (q z ^ α + q z ^ β) := by
              have hαpow : 0 ≤ q z ^ α := Real.rpow_nonneg (Complex.normSq_nonneg z) _
              have hβpow : 0 ≤ q z ^ β := Real.rpow_nonneg (Complex.normSq_nonneg z) _
              nlinarith
      have hpowBound : q z ^ w.re * |Real.log (q z)| ≤
          (2 / ε) * (q z ^ α + q z ^ β) := by
        calc
          _ ≤ (1 / ε) * (q z ^ (w.re - ε) + q z ^ (w.re + ε)) := hlogBound
          _ ≤ (1 / ε) * (2 * (q z ^ α + q z ^ β)) :=
            mul_le_mul_of_nonneg_left hsumPow (by positivity)
          _ = _ := by ring
      calc
        ‖F' w z‖ = ‖g z‖ * (q z ^ w.re * |Real.log (q z)|) := by
          dsimp [F']
          rw [norm_mul, norm_mul, pComplexCpow_norm w hwRe z, Complex.norm_real,
            Real.norm_eq_abs]
          ring
        _ ≤ B z := by
          calc
            _ ≤ ‖g z‖ * ((2 / ε) * (q z ^ α + q z ^ β)) :=
              mul_le_mul_of_nonneg_left hpowBound (norm_nonneg _)
            _ = B z := by dsimp [B]; ring
  have hdiff : ∀ᵐ z : ℂ ∂μ, ∀ w ∈ Metric.ball s₀ ε,
      HasDerivAt (F · z) (F' w z) w := by
    filter_upwards with z
    intro w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    by_cases hq0 : q z = 0
    · have hne (u : ℂ) (hu : 0 < u.re) : u ≠ 0 := by
        intro heq
        subst u
        simp at hu
      have hposOpen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
      have hEq : (fun u : ℂ => F u z) =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [hposOpen.mem_nhds hwRe] with u hu
        have hune : u ≠ 0 := hne u hu
        simp [F, q, hq0, hune]
      have hzero := hEq.hasDerivAt_iff.mpr (hasDerivAt_const w (0 : ℂ))
      have hwne : w ≠ 0 := hne w hwRe
      have hF'zero : F' w z = 0 := by simp [F', q, hq0, hwne]
      simpa [hF'zero] using hzero
    · have hqpos : 0 < q z := lt_of_le_of_ne (Complex.normSq_nonneg z) (Ne.symm hq0)
      have hbase : HasDerivAt (fun u : ℂ => (q z : ℂ) ^ u)
          ((q z : ℂ) ^ w * Complex.log (q z : ℂ)) w := by
        convert (hasDerivAt_id' w).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hqpos.ne')) using 1
        simp
      have hmul := hbase.const_mul (g z)
      simpa [F, F', q, Complex.ofReal_log hqpos.le, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hUnder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hε) hFmeas hFint hFprimeMeas hbound hBInt hdiff
  exact hUnder.2.differentiableAt

theorem pFiniteMellin_differentiableAt {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (s₀ : ℂ) (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ
      (fun s => ∫ y, f y * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ) s₀ := by
  let q : v.adicCompletion F → ℝ := absFin v
  let ε : ℝ := s₀.re / 4
  let α : ℝ := s₀.re / 2
  let β : ℝ := 2 * s₀.re
  let B : v.adicCompletion F → ℝ := fun y => (2 / ε) *
    (‖f y‖ * q y ^ α + ‖f y‖ * q y ^ β)
  let μv : Measure (v.adicCompletion F) := Theta.mulHaarFin μ
  let Fm : ℂ → (v.adicCompletion F) → ℂ := fun w y => f y * (q y : ℂ) ^ w
  let Fm' : ℂ → (v.adicCompletion F) → ℂ := fun w y =>
    f y * (q y : ℂ) ^ w * (Real.log (q y) : ℂ)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hAbsCont : Continuous q := by
    have heq : absFin v = fun y : v.adicCompletion F => ‖y‖ := by
      funext y
      exact Theta.absFin_eq_norm v y
    simpa [q, heq] using continuous_norm
  have hαInt : Integrable (fun y : v.adicCompletion F => ‖f y‖ * q y ^ α) μv := by
    simpa [q, μv] using
      ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
        v μ f hf hfc α hα
  have hβInt : Integrable (fun y : v.adicCompletion F => ‖f y‖ * q y ^ β) μv := by
    simpa [q, μv] using
      ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
        v μ f hf hfc β hβ
  have hBInt : Integrable B μv := by
    dsimp [B]
    simpa [mul_comm] using (hαInt.add hβInt).const_mul (2 / ε)
  have hFint : Integrable (Fm s₀) μv := by
    simpa [Fm, q, μv] using pFiniteCpow_integrable v μ f hf hfc s₀ hs₀
  have hlogMeas : Measurable (fun y : v.adicCompletion F => (Real.log (q y) : ℂ)) := by
    fun_prop
  have hFprimeMeas : AEStronglyMeasurable (Fm' s₀) μv := by
    have hpowCont : Continuous (fun y : v.adicCompletion F => (q y : ℂ) ^ s₀) := by
      apply continuous_iff_continuousAt.2
      intro y
      exact (Complex.continuousAt_ofReal_cpow_const (q y) s₀ (Or.inl hs₀)).comp
        hAbsCont.continuousAt
    have hMeas : Measurable (Fm' s₀) := by
      dsimp [Fm']
      exact (hf.measurable.mul hpowCont.measurable).mul hlogMeas
    exact hMeas.aestronglyMeasurable
  have hFmeas : ∀ᶠ w : ℂ in 𝓝 s₀, AEStronglyMeasurable (Fm w) μv := by
    filter_upwards [Metric.ball_mem_nhds s₀ hε] with w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    have hpowCont : Continuous (fun y : v.adicCompletion F => (q y : ℂ) ^ w) := by
      apply continuous_iff_continuousAt.2
      intro y
      exact (Complex.continuousAt_ofReal_cpow_const (q y) w (Or.inl hwRe)).comp
        hAbsCont.continuousAt
    exact (hf.mul hpowCont).aestronglyMeasurable
  have hbound : ∀ᵐ y : v.adicCompletion F ∂μv, ∀ w ∈ Metric.ball s₀ ε,
      ‖Fm' w y‖ ≤ B y := by
    filter_upwards with y
    intro w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    have hσlower : α ≤ w.re - ε := by dsimp [α, ε] at *; linarith
    have hσupper : w.re + ε ≤ β := by dsimp [β, ε] at *; linarith
    have hqnonneg : 0 ≤ q y := by
      change 0 ≤ absFin v y
      rw [Theta.absFin_eq_norm]
      exact norm_nonneg _
    by_cases hq0 : q y = 0
    · have hwne : w ≠ 0 := by
        intro h
        subst w
        simp at hwRe
      have hzero : Fm' w y = 0 := by simp [Fm', q, hq0, hwne]
      rw [hzero]
      simp [B, q, hq0, Real.zero_rpow (ne_of_gt hα), Real.zero_rpow (ne_of_gt hβ)]
    · have hqpos : 0 < q y := lt_of_le_of_ne hqnonneg (Ne.symm hq0)
      have hlogBound := pRealRpowLog_bound (q y) ε w.re hqpos hε
      have hsumPow : q y ^ (w.re - ε) + q y ^ (w.re + ε) ≤
          2 * (q y ^ α + q y ^ β) := by
        by_cases hq1 : q y ≤ 1
        · have hlow : q y ^ (w.re - ε) ≤ q y ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hσlower
          have hhigh : q y ^ (w.re + ε) ≤ q y ^ α := by
            apply Real.rpow_le_rpow_of_exponent_ge hqpos hq1
            dsimp [α, ε]
            linarith [hclose'.1]
          calc
            _ ≤ q y ^ α + q y ^ α := add_le_add hlow hhigh
            _ ≤ 2 * (q y ^ α + q y ^ β) := by
              have hαpow : 0 ≤ q y ^ α := Real.rpow_nonneg hqnonneg _
              have hβpow : 0 ≤ q y ^ β := Real.rpow_nonneg hqnonneg _
              nlinarith
        · have hqge : 1 ≤ q y := le_of_not_ge hq1
          have hlow : q y ^ (w.re - ε) ≤ q y ^ β := by
            apply Real.rpow_le_rpow_of_exponent_le hqge
            dsimp [β, ε]
            linarith [hclose'.2]
          have hhigh : q y ^ (w.re + ε) ≤ q y ^ β :=
            Real.rpow_le_rpow_of_exponent_le hqge hσupper
          calc
            _ ≤ q y ^ β + q y ^ β := add_le_add hlow hhigh
            _ ≤ 2 * (q y ^ α + q y ^ β) := by
              have hαpow : 0 ≤ q y ^ α := Real.rpow_nonneg hqnonneg _
              have hβpow : 0 ≤ q y ^ β := Real.rpow_nonneg hqnonneg _
              nlinarith
      have hpowBound : q y ^ w.re * |Real.log (q y)| ≤
          (2 / ε) * (q y ^ α + q y ^ β) := by
        calc
          _ ≤ (1 / ε) * (q y ^ (w.re - ε) + q y ^ (w.re + ε)) := hlogBound
          _ ≤ (1 / ε) * (2 * (q y ^ α + q y ^ β)) :=
            mul_le_mul_of_nonneg_left hsumPow (by positivity)
          _ = _ := by ring
      calc
        ‖Fm' w y‖ = ‖f y‖ * (q y ^ w.re * |Real.log (q y)|) := by
          dsimp [Fm']
          rw [norm_mul, norm_mul, pFiniteCpow_norm v w hwRe y, Complex.norm_real, Real.norm_eq_abs]
          ring
        _ ≤ B y := by
          calc
            _ ≤ ‖f y‖ * ((2 / ε) * (q y ^ α + q y ^ β)) :=
              mul_le_mul_of_nonneg_left hpowBound (norm_nonneg _)
            _ = B y := by dsimp [B]; ring
  have hdiff : ∀ᵐ y : v.adicCompletion F ∂μv, ∀ w ∈ Metric.ball s₀ ε,
      HasDerivAt (Fm · y) (Fm' w y) w := by
    filter_upwards with y
    intro w hw
    have hclose := pComplex_re_close w s₀ ε (Metric.mem_ball.mp hw)
    have hclose' := abs_lt.mp hclose
    have hwRe : 0 < w.re := by dsimp [ε] at hclose'; linarith
    by_cases hq0 : q y = 0
    · have hne (u : ℂ) (hu : 0 < u.re) : u ≠ 0 := by
        intro heq
        subst u
        simp at hu
      have hposOpen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
      have hEq : (fun u : ℂ => Fm u y) =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [hposOpen.mem_nhds hwRe] with u hu
        have hune : u ≠ 0 := hne u hu
        simp [Fm, q, hq0, hune]
      have hzero := hEq.hasDerivAt_iff.mpr (hasDerivAt_const w (0 : ℂ))
      have hwne : w ≠ 0 := hne w hwRe
      have hF'zero : Fm' w y = 0 := by simp [Fm', q, hq0, hwne]
      simpa [hF'zero] using hzero
    · have hqnonneg : 0 ≤ q y := by
        change 0 ≤ absFin v y
        rw [Theta.absFin_eq_norm]
        exact norm_nonneg _
      have hqpos : 0 < q y := lt_of_le_of_ne hqnonneg (Ne.symm hq0)
      have hbase : HasDerivAt (fun u : ℂ => (q y : ℂ) ^ u)
          ((q y : ℂ) ^ w * Complex.log (q y : ℂ)) w := by
        convert (hasDerivAt_id' w).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hqpos.ne')) using 1
        simp
      have hmul := hbase.const_mul (f y)
      have hlog : Complex.log (q y : ℂ) = (Real.log (q y) : ℂ) :=
        (Complex.ofReal_log hqpos.le).symm
      simpa [Fm, Fm', q, hlog, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hUnder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hε) hFmeas hFint hFprimeMeas hbound hBInt hdiff
  exact hUnder.2.differentiableAt

theorem pFiniteWeighted_integral_strip_le {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (l r σ : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hσl : l ≤ σ) (hσr : σ ≤ r) :
    (∫ y, ‖f y‖ * absFin v y ^ σ ∂Theta.mulHaarFin μ) ≤
      (∫ y, ‖f y‖ * absFin v y ^ l ∂Theta.mulHaarFin μ) +
        ∫ y, ‖f y‖ * absFin v y ^ r ∂Theta.mulHaarFin μ := by
  have hσ : 0 < σ := lt_of_lt_of_le hl hσl
  have hL := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc l hl
  have hR := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc r (lt_of_lt_of_le hl hlr)
  have hS := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc σ hσ
  have hsum : Integrable (fun y => ‖f y‖ * absFin v y ^ l + ‖f y‖ * absFin v y ^ r)
      (Theta.mulHaarFin μ) := hL.add hR
  have hpoint (y : v.adicCompletion F) :
      ‖f y‖ * absFin v y ^ σ ≤
        ‖f y‖ * absFin v y ^ l + ‖f y‖ * absFin v y ^ r := by
    have hq : 0 ≤ absFin v y := by rw [Theta.absFin_eq_norm]; positivity
    by_cases hq0 : absFin v y = 0
    · simp [hq0, hσ.ne', hl.ne', (lt_of_lt_of_le hl hlr).ne']
    · have hqpos : 0 < absFin v y := lt_of_le_of_ne hq (Ne.symm hq0)
      by_cases hq1 : absFin v y ≤ 1
      · have hp := Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hσl
        calc
          ‖f y‖ * absFin v y ^ σ ≤ ‖f y‖ * absFin v y ^ l :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_right
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq r))
      · have hqge : 1 ≤ absFin v y := le_of_not_ge hq1
        have hp := Real.rpow_le_rpow_of_exponent_le hqge hσr
        calc
          ‖f y‖ * absFin v y ^ σ ≤ ‖f y‖ * absFin v y ^ r :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_of_le
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq l)) le_rfl
  exact (integral_mono_ae hS hsum (Filter.Eventually.of_forall hpoint)).trans_eq
    (integral_add hL hR)

theorem pFiniteMellin_norm_bound {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (s : ℂ) (hs : 0 < s.re) :
    ‖∫ y, f y * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ‖ ≤
      ∫ y, ‖f y‖ * absFin v y ^ s.re ∂Theta.mulHaarFin μ := by
  have hInt := pFiniteCpow_integrable v μ f hf hfc s hs
  calc
    _ ≤ ∫ y, ‖f y * (absFin v y : ℂ) ^ s‖ ∂Theta.mulHaarFin μ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_mul, pFiniteCpow_norm v s hs y]

private theorem pFiniteWeighted_integral_strip_le_aux {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (l r σ : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hσl : l ≤ σ) (hσr : σ ≤ r) :
    (∫ y, ‖f y‖ * absFin v y ^ σ ∂Theta.mulHaarFin μ) ≤
      (∫ y, ‖f y‖ * absFin v y ^ l ∂Theta.mulHaarFin μ) +
        ∫ y, ‖f y‖ * absFin v y ^ r ∂Theta.mulHaarFin μ := by
  have hσ : 0 < σ := lt_of_lt_of_le hl hσl
  have hL := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc l hl
  have hR := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc r (lt_of_lt_of_le hl hlr)
  have hS := ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
    v μ f hf hfc σ hσ
  have hsum : Integrable (fun y => ‖f y‖ * absFin v y ^ l + ‖f y‖ * absFin v y ^ r)
      (Theta.mulHaarFin μ) := hL.add hR
  have hpoint (y : v.adicCompletion F) :
      ‖f y‖ * absFin v y ^ σ ≤
        ‖f y‖ * absFin v y ^ l + ‖f y‖ * absFin v y ^ r := by
    have hq : 0 ≤ absFin v y := by rw [Theta.absFin_eq_norm]; positivity
    by_cases hq0 : absFin v y = 0
    · simp [hq0, hσ.ne', hl.ne', (lt_of_lt_of_le hl hlr).ne']
    · have hqpos : 0 < absFin v y := lt_of_le_of_ne hq (Ne.symm hq0)
      by_cases hq1 : absFin v y ≤ 1
      · have hp := Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hσl
        calc
          ‖f y‖ * absFin v y ^ σ ≤ ‖f y‖ * absFin v y ^ l :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_right
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq r))
      · have hqge : 1 ≤ absFin v y := le_of_not_ge hq1
        have hp := Real.rpow_le_rpow_of_exponent_le hqge hσr
        calc
          ‖f y‖ * absFin v y ^ σ ≤ ‖f y‖ * absFin v y ^ r :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_of_le
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq l)) le_rfl
  exact (integral_mono_ae hS hsum (Filter.Eventually.of_forall hpoint)).trans_eq
    (integral_add hL hR)

end ArtinPrimitiveRoots.Proofs.a2_weights_p
