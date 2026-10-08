import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».NORM
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Theta.AnalysisS
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Group.Prod
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import ArtinPrimitiveRoots.Vendor.TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import ArtinPrimitiveRoots.Vendor.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2_PRODUCERS

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem sheet_absFin_one (v : FinPlace F) : A1.absFin v 1 = 1 := by
  have hv : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  simp [A1.absFin, hv]

theorem sheet_absS_ell (D : FieldData F) (S : SData F CE condη)
    (x : ℝ) (hx : 0 < x) : S.absS (S.ell D x hx) = x := by
  simp only [SData.absS, SData.ell]
  simp_rw [sheet_absFin_one]
  simp only [Finset.prod_const_one, one_mul, Complex.normSq_ofReal, Finset.prod_const,
    Finset.card_univ]
  rw [show A1.numComplex F = Fintype.card (InfinitePlace F) by rfl]
  have hc : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F))).ne'
  rw [← Real.rpow_add hx]
  rw [← Real.rpow_natCast (x ^ (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
    1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)))) (Fintype.card (InfinitePlace F))]
  have hrpow := Real.rpow_mul (le_of_lt hx)
    (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
      1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)))
    (Fintype.card (InfinitePlace F) : ℝ)
  rw [hrpow.symm]
  have he : (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
      1 / (2 * (Fintype.card (InfinitePlace F) : ℝ))) *
      (Fintype.card (InfinitePlace F) : ℝ) = 1 := by
    field_simp [hc]
    norm_num
  rw [he, Real.rpow_one]

def sheetEllUnit (D : FieldData F) (S : SData F CE condη)
    (x : ℝ) (hx : 0 < x) : S.FSˣ where
  val := S.ell D x hx
  inv := S.ell D x⁻¹ (inv_pos.mpr hx)
  val_inv := by
    ext v
    · simp [SData.ell]
    · simp [SData.ell, Real.inv_rpow (le_of_lt hx)]
      field_simp [Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne']
  inv_val := by
    ext v
    · simp [SData.ell]
    · simp [SData.ell, Real.inv_rpow (le_of_lt hx)]
      field_simp [Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne']

abbrev SheetFree (S : SData F CE condη) (v0 : InfinitePlace F) :=
  (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ)

def sheetParameterMeasure (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) :
    Measure (SheetFree S v0 × ℝ) :=
  ((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) 1))

def sheetParameterMap (S : SData F CE condη) (v0 : InfinitePlace F) (T : ℝ) :
    SheetFree S v0 × ℝ → S.FS :=
  fun q => Theta.sheetPoint S v0 T q.1 q.2

def sheetMeasure (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
    (v0 : InfinitePlace F) (T : ℝ) : Measure S.FS :=
  Measure.map (sheetParameterMap S v0 T) (sheetParameterMeasure S μ v0)

theorem sheetParameter_nonzero_ae (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) :
    ∀ᵐ q ∂sheetParameterMeasure S μ v0,
      (∀ v : S.Sf, q.1.1 v ≠ 0) ∧
        (∀ w : {w : InfinitePlace F // w ≠ v0}, q.1.2 w ≠ 0) := by
  classical
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let νf : Measure Xf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC
  let ν : Measure (Xf × Xc) := νf.prod νc
  let θμ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => hlocal.1 v.1 |>.2.2.2.2
  letI : SigmaFinite Theta.mulHaarC := hlocal.2.2
  letI : SFinite νf := by infer_instance
  letI : SFinite νc := by infer_instance
  letI : SFinite ν := by infer_instance
  letI : SFinite θμ := by infer_instance
  letI : ∀ v : S.Sf, NullSingletonClass (Theta.mulHaarFin (μ v.1)) := fun v => by
    have hv : NullSingletonClass (μ v.1).μ := (hlocal.1 v.1).2.2.1
    dsimp [Theta.mulHaarFin]
    infer_instance
  letI : NullSingletonClass Theta.mulHaarC := hlocal.2.1
  have hfn : ∀ᵐ y : Xf ∂νf, ∀ v : S.Sf, y v ≠ 0 := by
    apply ae_all_iff.mpr
    intro v
    exact Measure.ae_eval_ne (fun v : S.Sf => Theta.mulHaarFin (μ v.1)) v 0
  have hcn : ∀ᵐ y : Xc ∂νc,
      ∀ w : {w : InfinitePlace F // w ≠ v0}, y w ≠ 0 := by
    apply ae_all_iff.mpr
    intro w
    exact Measure.ae_eval_ne
      (fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC) w 0
  have hfn' : ∀ᵐ p : Xf × Xc ∂ν, ∀ v : S.Sf, p.1 v ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := νf) (ν := νc)).ae hfn
  have hcn' : ∀ᵐ p : Xf × Xc ∂ν,
      ∀ w : {w : InfinitePlace F // w ≠ v0}, p.2 w ≠ 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := νf) (ν := νc)).ae hcn
  have hfn'' : ∀ᵐ q : (Xf × Xc) × ℝ ∂(ν.prod θμ), ∀ v : S.Sf, q.1.1 v ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := θμ)).ae hfn'
  have hcn'' : ∀ᵐ q : (Xf × Xc) × ℝ ∂(ν.prod θμ),
      ∀ w : {w : InfinitePlace F // w ≠ v0}, q.1.2 w ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := θμ)).ae hcn'
  change ∀ᵐ q : (Xf × Xc) × ℝ ∂(ν.prod θμ),
    (∀ v : S.Sf, q.1.1 v ≠ 0) ∧
      (∀ w : {w : InfinitePlace F // w ≠ v0}, q.1.2 w ≠ 0)
  filter_upwards [hfn'', hcn''] with q hqf hqc
  exact ⟨hqf, hqc⟩

theorem sheetParameterMap_measurable (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) (T : ℝ) :
    Measurable (sheetParameterMap S v0 T) := by
  classical
  unfold sheetParameterMap
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  let B : SheetFree S v0 → ℝ := fun p =>
    (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  have hB : Measurable B := by
    dsimp [B]
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (hlocal.1 v.1).1.comp
        ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply v).comp (measurable_fst.comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    by_cases hw : w = v0
    · subst w
      simp only [dif_pos rfl]
      change Measurable (fun q : SheetFree S v0 × ℝ =>
        ((Real.sqrt (T / B q.1) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (q.2 : ℂ)))
      fun_prop
    · have w' : {w : InfinitePlace F // w ≠ v0} := ⟨w, hw⟩
      simp only [Theta.sheetPoint, dif_neg hw]
      change Measurable (fun q : SheetFree S v0 × ℝ =>
        q.1.2 (⟨w, hw⟩ : {w : InfinitePlace F // w ≠ v0}))
      exact (measurable_pi_apply (⟨w, hw⟩ : {w : InfinitePlace F // w ≠ v0})).comp
        (measurable_snd.comp measurable_fst)

theorem integral_sheetMeasure_eq_sheetInt (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) (T : ℝ)
    (f : S.FS → ℂ) (hf : Integrable f (sheetMeasure S μ v0 T)) :
    ∫ y, f y ∂sheetMeasure S μ v0 T = Theta.sheetInt S μ v0 f T := by
  let g := sheetParameterMap S v0 T
  let ν := sheetParameterMeasure S μ v0
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let νf : Measure Xf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => hlocal.1 v.1 |>.2.2.2.2
  letI : SigmaFinite Theta.mulHaarC := hlocal.2.2
  letI : SFinite νf := by infer_instance
  letI : SFinite νc := by infer_instance
  letI : SFinite (νf.prod νc) := by infer_instance
  letI : SFinite ν := by
    dsimp [ν, sheetParameterMeasure, Xf, Xc, νf, νc, Theta.mulHaarFin, Theta.mulHaarC]
    infer_instance
  have hg : Measurable g := by
    simpa [g] using sheetParameterMap_measurable S μ v0 T
  have hmp : MeasurePreserving g ν (Measure.map g ν) := ⟨hg, rfl⟩
  have hcomp : Integrable (fun q => f (g q)) ν := hmp.integrable_comp_of_integrable hf
  calc
    _ = ∫ q, f (g q) ∂ν := by
      change ∫ y, f y ∂Measure.map g ν = _
      exact integral_map hg.aemeasurable hf.aestronglyMeasurable
    _ = ∫ p, ∫ θ, f (Theta.sheetPoint S v0 T p θ) ∂volume.restrict
          (Set.Ioc (0 : ℝ) 1) ∂((Measure.pi fun v : S.Sf =>
            Theta.mulHaarFin (μ v.1)).prod
            (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)) := by
      dsimp [g, ν, sheetParameterMeasure, sheetParameterMap]
      exact integral_prod (fun q => f (g q)) hcomp
    _ = Theta.sheetInt S μ v0 f T := by
      rfl

theorem sheetParameterMap_absS (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (T : ℝ) (hT : 0 < T) (p : SheetFree S v0) (θ : ℝ)
    (hp : ∀ v : S.Sf, p.1 v ≠ 0)
    (hc : ∀ w : {w : InfinitePlace F // w ≠ v0}, p.2 w ≠ 0) :
    IsUnit (Theta.sheetPoint S v0 T p θ) ∧
      S.absS (Theta.sheetPoint S v0 T p θ) = T := by
  classical
  let B : ℝ := (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
    ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have hB : 0 < B := by
    dsimp [B]
    apply mul_pos
    · exact Finset.prod_pos fun v _ => hlocal.1 v.1 |>.2.1 _ (hp v)
    · apply Finset.prod_pos
      intro w _
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hc w))
  have hfin : 0 < ∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v) :=
    Finset.prod_pos fun v _ => hlocal.1 v.1 |>.2.1 _ (hp v)
  have hother : 0 < ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
    apply Finset.prod_pos
    intro w _
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hc w))
  have hfin0 :
      (∏ v ∈ S.Sf.attach, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact ne_of_gt ((hlocal.1 v.1).2.1 (p.1 v) (hp v))
  let z : ℂ := ((Real.sqrt (T / B) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (div_pos hT hB))))
      (Complex.exp_ne_zero _)
  have hz_norm : Complex.normSq z = T / B := by
    dsimp [z]
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (θ : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg hT.le hB.le)]
  have hunit : IsUnit (Theta.sheetPoint S v0 T p θ) := by
    change IsUnit (p.1, fun w : InfinitePlace F =>
      if h : w = v0 then z else p.2 ⟨w, h⟩)
    rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
    constructor
    · intro v
      exact (isUnit_iff_ne_zero).2 (hp v)
    · intro w
      by_cases hw : w = v0
      · subst w
        simp only [dif_pos rfl]
        exact (isUnit_iff_ne_zero).2 hz
      · simp only [dif_neg hw]
        exact (isUnit_iff_ne_zero).2 (hc ⟨w, hw⟩)
  have hcoord (w : InfinitePlace F) :
      Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 w) =
        if h : w = v0 then T / B else Complex.normSq (p.2 ⟨w, h⟩) := by
    by_cases hw : w = v0
    · subst w
      simpa [Theta.sheetPoint, B, z] using hz_norm
    · simp [Theta.sheetPoint, hw, B, z]
  have hprod : ∏ w : InfinitePlace F,
      Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 w) =
        (T / B) * ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun w : InfinitePlace F => Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 w)) v0]
    have hv0 : Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 v0) = T / B := by
      simpa using hcoord v0
    have hsub (w : {w : InfinitePlace F // w ≠ v0}) :
        Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 w.1) = Complex.normSq (p.2 w) := by
      simpa [w.property] using hcoord w.1
    simp_rw [hv0, hsub]
  have hnorm : S.absS (Theta.sheetPoint S v0 T p θ) = T := by
    rw [SData.absS]
    change (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
      ∏ w : InfinitePlace F, Complex.normSq ((Theta.sheetPoint S v0 T p θ).2 w) = T
    rw [hprod]
    dsimp [B]
    field_simp [hfin0, ne_of_gt hother]
  exact ⟨hunit, hnorm⟩

theorem sheetMeasure_support (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ y ∂sheetMeasure S μ v0 T, IsUnit y ∧ S.absS y = T := by
  classical
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have hunit_set : MeasurableSet {y : S.FS | IsUnit y} := by
    have heq : {y : S.FS | IsUnit y} =
        (⋂ v : S.Sf, {y : S.FS | y.1 v ≠ 0}) ∩
          ⋂ w : InfinitePlace F, {y : S.FS | y.2 w ≠ 0} := by
      ext y
      change IsUnit (y.1, y.2) ↔ _
      rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
      simp [isUnit_iff_ne_zero]
    rw [heq]
    apply MeasurableSet.inter
    · apply MeasurableSet.iInter
      intro v
      exact (isClosed_singleton.measurableSet.compl).preimage
        ((measurable_pi_apply v).comp measurable_fst)
    · apply MeasurableSet.iInter
      intro w
      exact (isClosed_singleton.measurableSet.compl).preimage
        ((measurable_pi_apply w).comp measurable_snd)
  have hnorm_meas : Measurable S.absS := by
    unfold SData.absS
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (hlocal.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  have hnorm_set : MeasurableSet {y : S.FS | S.absS y = T} := by
    exact (measurableSet_singleton T).preimage hnorm_meas
  have hgood : MeasurableSet {y : S.FS | IsUnit y ∧ S.absS y = T} :=
    hunit_set.inter hnorm_set
  rw [sheetMeasure, ae_map_iff
    (sheetParameterMap_measurable S μ v0 T).aemeasurable hgood]
  filter_upwards [sheetParameter_nonzero_ae S μ v0] with q hq
  exact sheetParameterMap_absS S μ v0 T hT q.1 q.2 hq.1 hq.2

theorem sheetUnitNorm_measurable (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (T : ℝ) :
    MeasurableSet {y : S.FS | IsUnit y ∧ S.absS y = T} := by
  classical
  have hunit_set : MeasurableSet {y : S.FS | IsUnit y} := by
    have heq : {y : S.FS | IsUnit y} =
        (⋂ v : S.Sf, {y : S.FS | y.1 v ≠ 0}) ∩
          ⋂ w : InfinitePlace F, {y : S.FS | y.2 w ≠ 0} := by
      ext y
      change IsUnit (y.1, y.2) ↔ _
      rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
      simp [isUnit_iff_ne_zero]
    rw [heq]
    apply MeasurableSet.inter
    · apply MeasurableSet.iInter
      intro v
      exact (isClosed_singleton.measurableSet.compl).preimage
        ((measurable_pi_apply v).comp measurable_fst)
    · apply MeasurableSet.iInter
      intro w
      exact (isClosed_singleton.measurableSet.compl).preimage
        ((measurable_pi_apply w).comp measurable_snd)
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have hnorm_meas : Measurable S.absS := by
    unfold SData.absS
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (hlocal.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  have hnorm_set : MeasurableSet {y : S.FS | S.absS y = T} :=
    (measurableSet_singleton T).preimage hnorm_meas
  exact hunit_set.inter hnorm_set

theorem sheetCoordinates (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) :
    ∃ e : (SheetFree S v0 × ℂ) ≃ᵐ S.FS,
      MeasurePreserving e
        (((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
          (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)).prod
            Theta.mulHaarC) (Theta.mulHaarS S μ) ∧
      (∀ u p θ, e (p, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
          (u / ((∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
            ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)), θ)) =
        Theta.sheetPoint S v0 u p θ) ∧
      Measurable (fun p : SheetFree S v0 =>
        (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
          ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)) ∧
      ∀ᵐ p ∂((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
        (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)),
        0 < (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
          ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
  classical
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let νf : Measure Xf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => hlocal.1 v.1 |>.2.2.2.2
  have : SigmaFinite Theta.mulHaarC := hlocal.2.2
  letI : SFinite νf := by infer_instance
  letI : SFinite νc := by infer_instance
  letI : SFinite (νf.prod νc) := by infer_instance
  have : ∀ v : S.Sf, NullSingletonClass (Theta.mulHaarFin (μ v.1)) := fun v => by
    have hv : NullSingletonClass (μ v.1).μ := (hlocal.1 v.1).2.2.1
    dsimp [Theta.mulHaarFin]
    infer_instance
  have : NullSingletonClass Theta.mulHaarC := hlocal.2.1
  let E := {w : InfinitePlace F // w = v0}
  letI : Unique E := {
    default := ⟨v0, rfl⟩
    uniq := fun w => Subtype.ext w.property }
  letI : Fintype E := Subtype.fintype (fun w : InfinitePlace F => w = v0)
  let split : (InfinitePlace F → ℂ) ≃ᵐ ((E → ℂ) × Xc) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℂ) (fun w => w = v0)
  let collapse : ((E → ℂ) × Xc) ≃ᵐ (ℂ × Xc) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique fun _ : E => ℂ)
      (MeasurableEquiv.refl Xc)
  let ec : (InfinitePlace F → ℂ) ≃ᵐ (Xc × ℂ) :=
    (split.trans collapse).trans (MeasurableEquiv.prodComm : ℂ × Xc ≃ᵐ Xc × ℂ)
  have hsplit : MeasurePreserving split (Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC)
      ((Measure.pi fun _ : E => Theta.mulHaarC).prod νc) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace F => Theta.mulHaarC)
      (fun w => w = v0)
  have hcollapse : MeasurePreserving collapse
      ((Measure.pi fun _ : E => Theta.mulHaarC).prod νc) (Theta.mulHaarC.prod νc) :=
    (measurePreserving_piUnique (fun _ : E => Theta.mulHaarC)).prod
      (MeasurePreserving.id νc)
  have hec : MeasurePreserving ec (Measure.pi fun _ : InfinitePlace F => Theta.mulHaarC)
      (νc.prod Theta.mulHaarC) :=
    (Measure.measurePreserving_swap (μ := Theta.mulHaarC) (ν := νc)).comp
      (hcollapse.comp hsplit)
  let ef : S.FS ≃ᵐ ((Xf × Xc) × ℂ) :=
    ((MeasurableEquiv.refl Xf).prodCongr ec).trans MeasurableEquiv.prodAssoc.symm
  have hef : MeasurePreserving ef (Theta.mulHaarS S μ) ((νf.prod νc).prod Theta.mulHaarC) :=
    (measurePreserving_prodAssoc νf νc Theta.mulHaarC).symm.comp
      ((MeasurePreserving.id νf).prod hec)
  let B : SheetFree S v0 → ℝ := fun p =>
    (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  have hef_apply (y : S.FS) : ef y = ((y.1, fun w => y.2 w.1), y.2 v0) := by rfl
  have hpoint (u : ℝ) (p : SheetFree S v0) (θ : ℝ) :
      ef.symm (p, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
        (u / B p, θ)) = Theta.sheetPoint S v0 u p θ := by
    apply ef.injective
    rw [ef.apply_symm_apply, hef_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext w
        simp [Theta.sheetPoint, w.property]
    · have hBp : B p =
          (∏ v ∈ S.Sf.attach, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
            ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
        simp [B]
      simp [Theta.sheetPoint, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint,
        hBp]
  have hB : Measurable B := by
    dsimp [B]
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (hlocal.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  have hfn : ∀ᵐ yf : Xf ∂νf, ∀ v : S.Sf, yf v ≠ 0 := by
    have : ∀ᵐ yf : Xf ∂νf, ∀ v : S.Sf, yf v ≠ 0 := by
      apply ae_all_iff.mpr
      intro v
      exact Measure.ae_eval_ne (fun v : S.Sf => Theta.mulHaarFin (μ v.1)) v 0
    exact this
  have hcn : ∀ᵐ yc : Xc ∂νc, ∀ w : {w : InfinitePlace F // w ≠ v0}, yc w ≠ 0 := by
    apply ae_all_iff.mpr
    intro w
    exact Measure.ae_eval_ne
      (fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC) w 0
  have hfn' : ∀ᵐ p : Xf × Xc ∂(νf.prod νc), ∀ v : S.Sf, p.1 v ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := νf) (ν := νc)).ae hfn
  have hcn' : ∀ᵐ p : Xf × Xc ∂(νf.prod νc),
      ∀ w : {w : InfinitePlace F // w ≠ v0}, p.2 w ≠ 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := νf) (ν := νc)).ae hcn
  have hpos : ∀ᵐ p : Xf × Xc ∂(νf.prod νc), 0 < B p := by
    filter_upwards [hfn', hcn'] with p hp hc
    dsimp [B]
    apply mul_pos
    · exact Finset.prod_pos fun v _ => (hlocal.1 v.1).2.1 (p.1 v) (hp v)
    · apply Finset.prod_pos
      intro w _
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hc w))
  refine ⟨ef.symm, hef.symm, ?_, hB, hpos⟩
  intro u p θ
  simpa [B] using hpoint u p θ

theorem sheetParameter_integrable_ae (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (f : S.FS → ℂ) (hf : Integrable f (Theta.mulHaarS S μ)) :
    ∀ᵐ u ∂ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure,
      Integrable (fun q : SheetFree S v0 × ℝ =>
        f (Theta.sheetPoint S v0 u q.1 q.2))
        (((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
          (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)).prod
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  classical
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let P := SheetFree S v0
  let νf : Measure Xf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC
  let ν : Measure P := νf.prod νc
  let rad : Measure ℝ := ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure
  let θμ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => hlocal.1 v.1 |>.2.2.2.2
  letI : SigmaFinite Theta.mulHaarC := hlocal.2.2
  letI : SigmaFinite ν := by infer_instance
  letI : SigmaFinite rad := by
    dsimp [rad, ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure]
    infer_instance
  letI : SigmaFinite θμ := by infer_instance
  letI : SFinite ν := by infer_instance
  letI : SFinite rad := by infer_instance
  letI : SFinite θμ := by infer_instance
  obtain ⟨e, he, hpoint, hBmeas, hBpos⟩ := sheetCoordinates S μ v0
  let B : P → ℝ := fun p =>
    (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  let θmap : ((P × ℝ) × ℝ) → P × ℂ := fun q =>
    (q.1.1, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
      (q.1.2 / B q.1.1, q.2))
  have hscale :=
    (ArtinPrimitiveRoots.Proofs.thsol_sheets.radial_product_scaling ν B hBmeas hBpos).prod
      (MeasurePreserving.id θμ)
  have hassoc := measurePreserving_prodAssoc ν rad θμ
  have hpolar : MeasurePreserving
      (fun q : P × (ℝ × ℝ) =>
        (q.1, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint q.2))
      (ENNReal.ofReal Real.pi • ν.prod (rad.prod θμ)) (ν.prod Theta.mulHaarC) := by
    simpa only [rad, θμ, Theta.mulHaarC, Measure.prod_smul_right, Prod.map_def, id_eq] using
      (MeasurePreserving.id ν).prod
        ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_polar_measurePreserving
  have hθmap : MeasurePreserving θmap
      (ENNReal.ofReal Real.pi • ((ν.prod rad).prod θμ)) (ν.prod Theta.mulHaarC) := by
    exact hpolar.comp ((hassoc.smul_measure (ENNReal.ofReal Real.pi)).comp
      (hscale.smul_measure (ENNReal.ofReal Real.pi)))
  let fullMap : ((P × ℝ) × ℝ) → S.FS := fun q => e (θmap q)
  have hfull : MeasurePreserving fullMap
      (ENNReal.ofReal Real.pi • ((ν.prod rad).prod θμ)) (Theta.mulHaarS S μ) :=
    he.comp hθmap
  let H : ((P × ℝ) × ℝ) → ℂ := fun q =>
    f (Theta.sheetPoint S v0 q.1.2 q.1.1 q.2)
  have hcomp : Integrable (fun q => f (fullMap q))
      (ENNReal.ofReal Real.pi • ((ν.prod rad).prod θμ)) :=
    hfull.integrable_comp_of_integrable hf
  have hsource₀ : Integrable (fun q => f (fullMap q)) ((ν.prod rad).prod θμ) :=
    (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mp hcomp
  have hsource : Integrable H ((ν.prod rad).prod θμ) := by
    apply hsource₀.congr
    filter_upwards with q
    simp only [H, fullMap, θmap]
    rw [hpoint q.1.2 q.1.1 q.2]
  let perm : ((P × ℝ) × ℝ) ≃ᵐ ℝ × (P × ℝ) := {
    toFun := fun q => (q.1.2, (q.1.1, q.2))
    invFun := fun q => ((q.2.1, q.1), q.2.2)
    left_inv := by intro q; rcases q with ⟨⟨p, u⟩, θ⟩; rfl
    right_inv := by intro q; rcases q with ⟨u, ⟨p, θ⟩⟩; rfl
    measurable_toFun := by
      apply Measurable.prodMk
      · exact measurable_snd.comp measurable_fst
      · apply Measurable.prodMk
        · exact measurable_fst.comp measurable_fst
        · exact measurable_snd
    measurable_invFun := by
      apply Measurable.prodMk
      · apply Measurable.prodMk
        · exact measurable_fst.comp measurable_snd
        · exact measurable_fst
      · exact measurable_snd.comp measurable_snd }
  have hperm : MeasurePreserving perm ((ν.prod rad).prod θμ) (rad.prod (ν.prod θμ)) := by
    have hp1 := measurePreserving_prodAssoc ν rad θμ
    have hp2 := Measure.measurePreserving_swap (μ := ν) (ν := rad.prod θμ)
    have hp3 := measurePreserving_prodAssoc rad θμ ν
    have hp4 := (MeasurePreserving.id rad).prod
      (Measure.measurePreserving_swap (μ := θμ) (ν := ν))
    convert hp4.comp (hp3.comp (hp2.comp hp1)) using 1 <;> rfl
  let H' : ℝ × (P × ℝ) → ℂ := H ∘ perm.symm
  have hH' : AEStronglyMeasurable H' (rad.prod (ν.prod θμ)) :=
    hsource.aestronglyMeasurable.comp_measurePreserving hperm.symm
  have htarget : Integrable H' (rad.prod (ν.prod θμ)) := by
    have hcomp' : Integrable (fun q => H' (perm q)) ((ν.prod rad).prod θμ) := by
      have hEq : (fun q => H' (perm q)) = H := by
        funext q
        change H (perm.symm (perm q)) = H q
        rw [perm.symm_apply_apply]
      rw [hEq]
      exact hsource
    exact (hperm.integrable_comp hH').mp hcomp'
  have hslice := htarget.prod_right_ae
  change ∀ᵐ u ∂rad, Integrable
    (fun q : P × ℝ => H' (u, q)) (ν.prod θμ) at hslice
  filter_upwards [hslice] with u hu
  have hperm_symm (p : P) (θ : ℝ) : perm.symm (u, (p, θ)) = ((p, u), θ) := by
    rfl
  apply hu.congr
  filter_upwards with q
  simp [H', H, hperm_symm]

private theorem complexPolarPoint_injOn :
    Set.InjOn ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) 1) := by
  classical
  let D : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) 1
  let squarePolarChart := ArtinPrimitiveRoots.Proofs.thsol_sheets.squarePolarChart
  let complexPolarPoint := ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
  have hrot (p : ℝ × ℝ) : squarePolarChart p =
      -polarCoord.symm (Real.sqrt p.1, 2 * Real.pi * p.2 - Real.pi) := by
    ext <;> simp [squarePolarChart,
      ArtinPrimitiveRoots.Proofs.thsol_sheets.squarePolarChart,
      polarCoord_symm_apply, Real.cos_sub, Real.sin_sub]
  have htarget (p : ℝ × ℝ) (hp : p ∈ D) :
      (Real.sqrt p.1, 2 * Real.pi * p.2 - Real.pi) ∈ polarCoord.target := by
    change 0 < Real.sqrt p.1 ∧ -Real.pi < 2 * Real.pi * p.2 - Real.pi ∧
      2 * Real.pi * p.2 - Real.pi < Real.pi
    refine ⟨Real.sqrt_pos.mpr hp.1, ?_, ?_⟩ <;>
      nlinarith [Real.pi_pos, hp.2.1, hp.2.2]
  have hinj : Set.InjOn squarePolarChart D := by
    intro p hp q hq heq
    rw [hrot p, hrot q, neg_inj] at heq
    have h := polarCoord.symm.injOn (htarget p hp) (htarget q hq) heq
    have hr := congrArg Prod.fst h
    have hθ := congrArg Prod.snd h
    dsimp only at hr hθ
    apply Prod.ext
    · calc
        p.1 = Real.sqrt p.1 ^ 2 := (Real.sq_sqrt hp.1.le).symm
        _ = Real.sqrt q.1 ^ 2 := by rw [hr]
        _ = q.1 := Real.sq_sqrt hq.1.le
    · nlinarith [hθ, Real.pi_pos]
  have hC (p : ℝ × ℝ) :
      Complex.measurableEquivRealProd.symm (squarePolarChart p) = complexPolarPoint p := by
    have ha : (2 * Real.pi * Complex.I * (p.2 : ℂ)) =
        ((2 * Real.pi * p.2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    change Complex.equivRealProd.symm (squarePolarChart p) = _
    rw [Complex.equivRealProd_symm_apply]
    dsimp only [squarePolarChart, ArtinPrimitiveRoots.Proofs.thsol_sheets.squarePolarChart,
      Prod.fst, Prod.snd, complexPolarPoint,
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
    rw [ha, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  intro p hp q hq heq
  have hpC : squarePolarChart p =
      Complex.measurableEquivRealProd (complexPolarPoint p) := by
    simpa using congrArg Complex.measurableEquivRealProd (hC p)
  have hqC : squarePolarChart q =
      Complex.measurableEquivRealProd (complexPolarPoint q) := by
    simpa using congrArg Complex.measurableEquivRealProd (hC q)
  apply hinj hp hq
  rw [hpC, hqC]
  exact congrArg Complex.measurableEquivRealProd heq

theorem integrable_sheetMeasure_of_parameter (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) (T : ℝ)
    (hT : 0 < T) (f : S.FS → ℂ)
    (hf : Integrable (fun q : SheetFree S v0 × ℝ =>
      f (sheetParameterMap S v0 T q)) (sheetParameterMeasure S μ v0)) :
    Integrable f (sheetMeasure S μ v0 T) := by
  classical
  let P := SheetFree S v0
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let νf : Measure Xf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC
  let ν : Measure P := νf.prod νc
  let θμ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let μpar : Measure (P × ℝ) := ν.prod θμ
  let B : P → ℝ := fun p =>
    (∏ v : S.Sf, ArtinPrimitiveRoots.A1.absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  let Good : Set (P × ℝ) :=
    {q | 0 < B q.1 ∧ q.2 ∈ Set.Ioo (0 : ℝ) 1}
  have hμpar : μpar = sheetParameterMeasure S μ v0 := rfl
  obtain ⟨e, _, hpoint, hBmeas, hBpos⟩ := sheetCoordinates S μ v0
  have hBmeas' : Measurable B := by simpa [B] using hBmeas
  have hpoint' (u : ℝ) (p : P) (θ : ℝ) :
      e (p, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (u / B p, θ)) =
        sheetParameterMap S v0 u (p, θ) := by
    simpa [B, sheetParameterMap] using hpoint u p θ
  have hGoodMeas : MeasurableSet Good := by
    dsimp [Good]
    exact (measurableSet_Ioi.preimage (hBmeas'.comp measurable_fst)).inter
      (measurableSet_Ioo.preimage measurable_snd)
  have htheta : ∀ᵐ θ ∂θμ, θ ∈ Set.Ioo (0 : ℝ) 1 := by
    change ∀ᵐ θ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      θ ∈ Set.Ioo (0 : ℝ) 1
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with θ hθ
    intro hIoc
    have hlt : θ < 1 := by
      by_contra h
      exact hθ (le_antisymm hIoc.2 (le_of_not_gt h))
    exact ⟨hIoc.1, hlt⟩
  have hBpos' : ∀ᵐ p : P ∂ν, 0 < B p := by
    simpa [ν, B] using hBpos
  have hBpos'' : ∀ᵐ q : P × ℝ ∂μpar, 0 < B q.1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := θμ)).ae hBpos'
  have htheta' : ∀ᵐ q : P × ℝ ∂μpar, q.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    exact (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := θμ)).ae htheta
  have hGoodAE : ∀ᵐ q : P × ℝ ∂μpar, q ∈ Good := by
    filter_upwards [hBpos'', htheta'] with q hqB hqθ
    exact ⟨hqB, hqθ⟩
  have hInj : Set.InjOn (sheetParameterMap S v0 T) Good := by
    intro q hq r hr hEq
    have hcoord :
        e (q.1, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
          (T / B q.1, q.2)) =
        e (r.1, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
          (T / B r.1, r.2)) := by
      calc
        _ = sheetParameterMap S v0 T q := hpoint' T q.1 q.2
        _ = sheetParameterMap S v0 T r := hEq
        _ = _ := (hpoint' T r.1 r.2).symm
    have hpolar := e.injective hcoord
    have hpolar' := complexPolarPoint_injOn
      ⟨show T / B q.1 ∈ Set.Ioi (0 : ℝ) from div_pos hT hq.1, hq.2⟩
      ⟨show T / B r.1 ∈ Set.Ioi (0 : ℝ) from div_pos hT hr.1, hr.2⟩
      (congrArg Prod.snd hpolar)
    have hfree : q.1 = r.1 := congrArg (fun z : P × ℂ => z.1) hpolar
    have hangle : q.2 = r.2 := congrArg (fun z : ℝ × ℝ => z.2) hpolar'
    rcases q with ⟨qp, qθ⟩
    rcases r with ⟨rp, rθ⟩
    change qp = rp at hfree
    change qθ = rθ at hangle
    cases hfree
    cases hangle
    rfl
  letI : StandardBorelSpace (P × ℝ) := inferInstance
  letI : StandardBorelSpace Good := hGoodMeas.standardBorel
  letI : MeasurableSpace.CountablySeparated S.FS := inferInstance
  have hEmb : MeasurableEmbedding (Good.domRestrict (sheetParameterMap S v0 T)) :=
    Measurable.measurableEmbedding
      ((sheetParameterMap_measurable S μ v0 T).comp measurable_subtype_coe)
      (Set.injOn_iff_injective.1 hInj)
  let μGood : Measure Good := Measure.comap
    (Subtype.val : Good → P × ℝ) μpar
  have hμGoodMap : Measure.map (Subtype.val : Good → P × ℝ) μGood =
      μpar.restrict Good := map_comap_subtype_coe hGoodMeas μpar
  have hfRestr : Integrable (fun q : P × ℝ =>
      f (sheetParameterMap S v0 T q)) (μpar.restrict Good) :=
    hf.mono_measure Measure.restrict_le_self
  have hfGood : Integrable (fun q : Good =>
      f (sheetParameterMap S v0 T (q : P × ℝ))) μGood := by
    rw [← hμGoodMap] at hfRestr
    exact (MeasurableEmbedding.subtype_coe hGoodMeas).integrable_map_iff.mp hfRestr
  have hmap : Measure.map (Good.domRestrict (sheetParameterMap S v0 T)) μGood =
      sheetMeasure S μ v0 T := by
    change Measure.map (sheetParameterMap S v0 T ∘ Subtype.val) μGood = _
    rw [← Measure.map_map (sheetParameterMap_measurable S μ v0 T)
      measurable_subtype_coe, hμGoodMap,
      Measure.restrict_eq_self_of_ae_mem hGoodAE]
    rfl
  have hfMap : Integrable f
      (Measure.map (Good.domRestrict (sheetParameterMap S v0 T)) μGood) :=
    hEmb.integrable_map_iff.mpr hfGood
  rw [hmap] at hfMap
  exact hfMap

theorem unitSixFinite (D : FieldData F) (S : SData F CE condη) : Finite (UnitSix S) := by
  classical
  have hUSnorm (u : S.US) : S.absS (S.diagU (u : Fˣ) : S.FS) = 1 :=
    (ArtinPrimitiveRoots.A2.a2_bridge_NORM D S).2.2.2.1 u
  obtain ⟨K, hKcompact, hKrep⟩ := S.FSOne_quotient_compact D
  let Λ : AddSubgroup S.FS :=
    (S.diag.toAddMonoidHom.comp S.R.val.toAddMonoidHom).range
  have hdiagR : (Λ : Set S.FS) = S.diagR := rfl
  have hdiscR : IsDiscrete (S.diagR : Set S.FS) :=
    (S.diagR_discrete_cocompact D).1
  have hdiscΛ : IsDiscrete (Λ : Set S.FS) := by
    simpa [hdiagR] using hdiscR
  letI : DiscreteTopology Λ := (isDiscrete_iff_discreteTopology).mp hdiscΛ
  have hΛclosed : IsClosed (Λ : Set S.FS) := by
    exact AddSubgroup.isClosed_of_discreteTopology
  have hKΛcompact : IsCompact (K ∩ (Λ : Set S.FS)) :=
    hKcompact.inter_right hΛclosed
  have hKΛdiscrete : IsDiscrete (K ∩ (Λ : Set S.FS)) := by
    apply IsDiscrete.of_nhdsWithin
    intro x hx
    exact (nhdsWithin_mono x Set.inter_subset_right).trans (hdiscΛ.nhdsWithin x hx.2).le
  have hKΛfinite : (K ∩ (Λ : Set S.FS)).Finite := hKΛcompact.finite hKΛdiscrete
  let U_K : Set S.US := {u | S.diag ((u : Fˣ) : F) ∈ K}
  have hU_K_finite : U_K.Finite := by
    apply Set.Finite.of_injOn (f := fun u : S.US => S.diag ((u : Fˣ) : F))
      (s := U_K) (t := K ∩ (Λ : Set S.FS) ) ?_ ?_ hKΛfinite
    · intro u hu
      constructor
      · exact hu
      · change ∃ x : S.R, S.diag (x : F) = S.diag ((u : Fˣ) : F)
        let ru : (S.R)ˣ :=
          (Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F) u
        refine ⟨ru.1, ?_⟩
        rfl
    · intro u hu v hv huv
      apply Subtype.ext
      apply Units.ext
      exact (by
        have hinj : Function.Injective (S.diag : F →+* S.FS) := by
          intro a b hab
          obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
          have h := congrArg (fun z : S.FS => z.2 w) hab
          exact w.embedding.injective h
        exact hinj huv)
  let U_K' := {u : S.US // u ∈ U_K}
  letI : Fintype U_K' := hU_K_finite.fintype
  have hsurj : Function.Surjective (fun u : U_K' => unitSixClass S u.1) := by
    intro c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    let x : S.FSOne := ⟨S.diagU (u : Fˣ), hUSnorm u⟩
    obtain ⟨z, hzK, hrel⟩ := hKrep x
    rcases hrel with ⟨v, hv⟩
    let t : S.US := (v : S.US) ^ (-6 : ℤ) * u
    have hvpow : (v : S.US) ^ (-6 : ℤ) ∈ Gamma S := by
      change (v : S.US) ^ (-6 : ℤ) ∈ (sixthPowerOnUS S).range
      refine ⟨v⁻¹, ?_⟩
      simp [sixthPowerOnUS]
    have hv' : S.diagU (u : Fˣ) = (S.diagU (v : Fˣ)) ^ 6 * z.1 := by
      simpa using hv
    have hdiagT : S.diagU (t : Fˣ) = z.1 := by
      calc
        S.diagU (t : Fˣ) = (S.diagU (v : Fˣ)) ^ (-6 : ℤ) * S.diagU (u : Fˣ) := by
          simp [t, map_mul, map_zpow]
        _ = z.1 := by rw [hv']; group
    have ht : t ∈ U_K := by
      change S.diag ((t : Fˣ) : F) ∈ K
      rw [show S.diag ((t : Fˣ) : F) = S.diagU (t : Fˣ) by rfl, hdiagT]
      exact hzK
    have hclass : unitSixClass S t = unitSixClass S u := by
      rw [unitSixClass, unitSixClass, QuotientGroup.eq_iff_div_mem]
      change t / u ∈ Gamma S
      have htdiv : t / u = (v : S.US) ^ (-6 : ℤ) := by
        change ((v : S.US) ^ (-6 : ℤ) * u) / u = _
        rw [mul_div_cancel_right]
      rw [htdiv]
      exact hvpow
    refine ⟨⟨t, ht⟩, ?_⟩
    exact hclass
  exact Finite.of_surjective (fun u : U_K' => unitSixClass S u.1) hsurj

private theorem complexSixthPower_surjective (z : ℂˣ) :
    ∃ w : ℂˣ, w ^ 6 = z := by
  let p : Polynomial ℂ := Polynomial.X ^ 6 - Polynomial.C (z : ℂ)
  have hCX : (Polynomial.C (z : ℂ) : Polynomial ℂ).degree <
      (Polynomial.X ^ 6 : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    by_cases hz : (z : ℂ) = 0
    · simpa [hz] using (WithBot.bot_lt_coe (6 : ℕ))
    · simp [hz]
  have hp : 0 < p.degree := by
    dsimp [p]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hCX, Polynomial.degree_X_pow]
    norm_num
  obtain ⟨w, hw⟩ := Complex.exists_root hp
  have hwpow : w ^ 6 = (z : ℂ) := by
    change Polynomial.eval w p = 0 at hw
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hw
    exact sub_eq_zero.mp hw
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    have hz : (z : ℂ) = 0 := by simpa [p] using hw
    exact Units.ne_zero z hz
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply Units.ext
  exact hwpow

theorem classVFinite (S : SData F CE condη) : Finite S.V := by
  classical
  let LocalPow (v : S.Sf) : Subgroup (v.1.adicCompletion F)ˣ :=
    (powMonoidHom 6 : (v.1.adicCompletion F)ˣ →* (v.1.adicCompletion F)ˣ).range
  let LocalQ (v : S.Sf) := (v.1.adicCompletion F)ˣ ⧸ LocalPow v
  have hLocalFinite (v : S.Sf) : Finite (LocalQ v) := by
    letI : (LocalPow v).FiniteIndex :=
      TauCeti.finiteIndex_range_powMonoidHom (by norm_num : (6 : v.1.adicCompletion F) ≠ 0)
    infer_instance
  letI : ∀ v : S.Sf, Fintype (LocalQ v) := fun v => by
    letI : Finite (LocalQ v) := hLocalFinite v
    exact Fintype.ofFinite (LocalQ v)
  let Q := ∀ v : S.Sf, LocalQ v
  letI : MulOneClass S.FSˣ :=
    (inferInstance : Group S.FSˣ).toDivInvMonoid.toMulOneClass
  letI : Group Q := inferInstance
  letI : MulOneClass Q := (inferInstance : Group Q).toDivInvMonoid.toMulOneClass
  let φ : S.FSˣ →* Q := MonoidHom.pi fun v =>
    (QuotientGroup.mk' (LocalPow v)).comp (S.compU v)
  let eFin : (∀ v : S.Sf, v.1.adicCompletion F)ˣ ≃* (∀ v : S.Sf, (v.1.adicCompletion F)ˣ) :=
    MulEquiv.piUnits
  let eArch : (InfinitePlace F → ℂ)ˣ ≃* (InfinitePlace F → ℂˣ) := MulEquiv.piUnits
  let e : S.FSˣ ≃* ((∀ v : S.Sf, (v.1.adicCompletion F)ˣ) × (InfinitePlace F → ℂˣ)) :=
    MulEquiv.prodUnits.trans (eFin.prodCongr eArch)
  have heval (x : S.FSˣ) :
      e x = ((fun v : S.Sf => S.compU v x), fun w : InfinitePlace F => S.compC w x) := by
    apply Prod.ext
    · funext v
      change (eFin (Units.map (MonoidHom.fst _ _) x)) v = S.compU v x
      rfl
    · funext w
      change (eArch (Units.map (MonoidHom.snd _ _) x)) w = S.compC w x
      rfl
  have hker : φ.ker = (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range := by
    apply le_antisymm
    · intro x hx
      have hxφ : φ x = 1 := MonoidHom.mem_ker.mp hx
      have hroot (v : S.Sf) : ∃ y : (v.1.adicCompletion F)ˣ,
          S.compU v x = y ^ 6 := by
        have hmem : S.compU v x ∈ LocalPow v := by
          have hxv := congrFun hxφ v
          change QuotientGroup.mk' (LocalPow v) (S.compU v x) =
            (1 : LocalQ v) at hxv
          exact (QuotientGroup.eq_one_iff _).mp hxv
        obtain ⟨y, hy⟩ := hmem
        exact ⟨y, hy.symm⟩
      have hrootC (w : InfinitePlace F) : ∃ y : ℂˣ,
          S.compC w x = y ^ 6 := by
        obtain ⟨y, hy⟩ := complexSixthPower_surjective (S.compC w x)
        exact ⟨y, hy.symm⟩
      let yFin : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ := fun v => Classical.choose (hroot v)
      let yArch : InfinitePlace F → ℂˣ := fun w => Classical.choose (hrootC w)
      have hyFin (v : S.Sf) : S.compU v x = yFin v ^ 6 :=
        Classical.choose_spec (hroot v)
      have hyArch (w : InfinitePlace F) : S.compC w x = yArch w ^ 6 :=
        Classical.choose_spec (hrootC w)
      let y : S.FSˣ := e.symm (yFin, yArch)
      have hy : y ^ 6 = x := by
        apply e.injective
        rw [map_pow]
        rw [show e y = (yFin, yArch) by simp [y], heval x]
        apply Prod.ext
        · funext v
          exact (hyFin v).symm
        · funext w
          exact (hyArch w).symm
      exact ⟨y, hy⟩
    · rintro x ⟨y, rfl⟩
      apply MonoidHom.mem_ker.mpr
      funext v
      dsimp [φ]
      change QuotientGroup.mk' (LocalPow v) (S.compU v (y ^ 6)) = 1
      have hpow : S.compU v (y ^ 6) = (S.compU v y) ^ 6 :=
        map_pow (S.compU v) y 6
      rw [hpow]
      exact (QuotientGroup.eq_one_iff _).2 ⟨S.compU v y, rfl⟩
  letI : Finite Q := by infer_instance
  have hRange : Finite (MonoidHom.range φ) := by
    exact Finite.of_injective (f := fun q : MonoidHom.range φ => (q.1 : Q))
      Subtype.val_injective
  letI : Finite (MonoidHom.range φ) := hRange
  let eQuot : S.V ≃* MonoidHom.range φ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  exact Finite.of_equiv (MonoidHom.range φ) eQuot.symm

def sheetGammaAction (S : SData F CE condη) (γ : Gamma S) (z : S.FS) : S.FS :=
  ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * z

private theorem sheetGammaAction_mul (S : SData F CE condη) (γ δ : Gamma S) (z : S.FS) :
    sheetGammaAction S γ (sheetGammaAction S δ z) =
      sheetGammaAction S (γ * δ) z := by
  simp [sheetGammaAction, map_mul, map_inv, mul_assoc, mul_comm, mul_left_comm]

private theorem sheet_absS_continuous (S : SData F CE condη) : Continuous S.absS := by
  unfold SData.absS
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    have habs : Continuous (A1.absFin v.1) := by
      convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
      ext x
      exact A1.Theta.absFin_eq_norm v.1 x
    exact habs.comp ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    exact Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)

private theorem sheet_absS_one_isUnit (S : SData F CE condη) {z : S.FS}
    (hz : S.absS z = 1) : IsUnit z := by
  classical
  let AF : ℝ := ∏ v : S.Sf, A1.absFin v.1 (z.1 v)
  let AC : ℝ := ∏ w : InfinitePlace F, Complex.normSq (z.2 w)
  have hprod : AF * AC = 1 := by simpa [AF, AC, SData.absS] using hz
  have hAF : AF ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hAC : AC ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact zero_ne_one hprod
  have hFin (v : S.Sf) : z.1 v ≠ 0 := by
    have hAFprod : (∏ v : S.Sf, A1.absFin v.1 (z.1 v)) ≠ 0 := by
      simpa [AF] using hAF
    have hv := (Finset.prod_ne_zero_iff.mp hAFprod) v (Finset.mem_univ v)
    intro hzv
    apply hv
    simp [A1.absFin, hzv]
  have hInf (w : InfinitePlace F) : z.2 w ≠ 0 := by
    have hACprod : (∏ w : InfinitePlace F, Complex.normSq (z.2 w)) ≠ 0 := by
      simpa [AC] using hAC
    have hw := (Finset.prod_ne_zero_iff.mp hACprod) w (Finset.mem_univ w)
    intro hzw
    apply hw
    simp [hzw]
  let u : S.FSˣ := {
    val := z
    inv := (fun v => (z.1 v)⁻¹, fun w => (z.2 w)⁻¹)
    val_inv := by
      ext v
      · simp [hFin v]
      · simp [hInf v]
    inv_val := by
      ext v
      · simp [hFin v]
      · simp [hInf v] }
  exact u.isUnit

private theorem sheet_diagU_injective (S : SData F CE condη) :
    Function.Injective S.diagU := by
  intro u v huv
  apply Units.ext
  have hval : S.diag ((u : Fˣ) : F) = S.diag ((v : Fˣ) : F) :=
    congrArg (fun x : S.FSˣ => (x : S.FS)) huv
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact w.embedding.injective (congrArg (fun x : S.FS => x.2 w) hval)

private theorem map_withDensity_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α)
    (d : α → ENNReal) :
    Measure.map e (μ.withDensity d) =
      (Measure.map e μ).withDensity (fun y => d (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply d (e.measurable hs),
    withDensity_apply (fun y => d (e.symm y)) hs]
  calc
    ∫⁻ x in e ⁻¹' s, d x ∂μ =
        ∫⁻ x, (e ⁻¹' s).indicator d x ∂μ := by
      rw [lintegral_indicator (e.measurable hs) d]
    _ = ∫⁻ x, s.indicator (fun y => d (e.symm y)) (e x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      simp [Set.indicator]
    _ = ∫⁻ y, s.indicator (fun y => d (e.symm y)) y ∂Measure.map e μ :=
      (MeasureTheory.lintegral_map_equiv
        (s.indicator (fun y => d (e.symm y))) e).symm
    _ = ∫⁻ y in s, d (e.symm y) ∂Measure.map e μ := by
      rw [lintegral_indicator hs]

private theorem sheet_locHaar_map_mul {v : FinPlace F} (μ : Theta.LocHaar v)
    (y : (v.adicCompletion F)ˣ) :
    Measure.map (fun x : v.adicCompletion F => (y : v.adicCompletion F) * x) μ.μ =
      ENNReal.ofReal (A1.absFin v y)⁻¹ • μ.μ := by
  classical
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  letI : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  letI : ProperSpace K := hproper
  letI : SecondCountableTopology K := inferInstance
  let e : K ≃ₜ+ K := (ContinuousLinearEquiv.smulLeft (R₁ := K) y).toContinuousAddEquiv
  let eMeas : K ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  have he (x : K) : eMeas x = (y : K) * x := by
    change e x = (y : K) * x
    change (y : K) • x = _
    rfl
  let ν : Measure K := Measure.map eMeas μ.μ
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ.μ
  haveI : IsFiniteMeasureOnCompacts μ.μ := inferInstance
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hpre : IsCompact (e.symm '' C) := hC.image e.symm.continuous
    have hEq : e ⁻¹' C = e.symm '' C := by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    change (Measure.map eMeas μ.μ) C < ⊤
    rw [Measure.map_apply eMeas.measurable hC.measurableSet]
    have hEqMeas : eMeas ⁻¹' C = eMeas.symm '' C := by
      ext x
      constructor
      · intro hx
        exact ⟨eMeas x, hx, by simp⟩
      · rintro ⟨w, hw, hwx⟩
        have hwe : w = eMeas x := by simpa using congrArg eMeas hwx
        rw [hwe] at hw
        exact hw
    rw [hEqMeas]
    exact hpre.measure_lt_top
  have hscale : ν = Measure.addHaarScalarFactor ν μ.μ • μ.μ :=
    Measure.isAddLeftInvariant_eq_smul ν μ.μ
  let O : Set K := v.adicCompletionIntegers F
  have hOmeas : MeasurableSet O := Valued.isOpen_valuationSubring K |>.measurableSet
  let f : K → ℝ := O.indicator fun _ => 1
  have hIntOne : ∫ x, f x ∂μ.μ = 1 := by
    calc
      ∫ x, f x ∂μ.μ = μ.μ.real O := integral_indicator_one hOmeas
      _ = 1 := by
        change (μ.μ (v.adicCompletionIntegers F : Set K)).toReal = 1
        rw [μ.norm_O]
        simp
  have hcomp : ∫ x, f (eMeas x) ∂μ.μ = (A1.absFin v y)⁻¹ := by
    calc
      ∫ x, f (eMeas x) ∂μ.μ = ∫ x, f ((y : K) * x) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [he]
      _ = (A1.absFin v y)⁻¹ • ∫ x, f x ∂μ.μ :=
        Theta.LocHaar.integral_comp_mul μ y f
      _ = (A1.absFin v y)⁻¹ := by
        rw [hIntOne]
        simp [smul_eq_mul]
  have hmapInt : ∫ x, f x ∂ν = (A1.absFin v y)⁻¹ :=
    (integral_map_equiv eMeas f).trans hcomp
  have hmReal : ν.real O = (A1.absFin v y)⁻¹ := by
    calc
      ν.real O = ∫ x, f x ∂ν := (integral_indicator_one hOmeas).symm
      _ = (A1.absFin v y)⁻¹ := hmapInt
  have hOscale : ν O = (Measure.addHaarScalarFactor ν μ.μ : ENNReal) := by
    have h := congrArg (fun ρ : Measure K => ρ O) hscale
    simpa [O, μ.norm_O, Measure.smul_apply, smul_eq_mul] using h
  have hcReal : ((Measure.addHaarScalarFactor ν μ.μ : ENNReal).toReal) =
      (A1.absFin v y)⁻¹ := by
    calc
      ((Measure.addHaarScalarFactor ν μ.μ : ENNReal).toReal) = (ν O).toReal := by
        rw [hOscale]
      _ = ν.real O := rfl
      _ = (A1.absFin v y)⁻¹ := hmReal
  have hcTop : (Measure.addHaarScalarFactor ν μ.μ : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hc : (Measure.addHaarScalarFactor ν μ.μ : ENNReal) =
      ENNReal.ofReal (A1.absFin v y)⁻¹ := by
    calc
      (Measure.addHaarScalarFactor ν μ.μ : ENNReal) =
          ENNReal.ofReal ((Measure.addHaarScalarFactor ν μ.μ : ENNReal).toReal) :=
        (ENNReal.ofReal_toReal hcTop).symm
      _ = ENNReal.ofReal (A1.absFin v y)⁻¹ := by rw [hcReal]
  have hAbsPos : 0 < A1.absFin v (y : K) := by
    rw [A1.Theta.absFin_eq_norm]
    exact norm_pos_iff.mpr (Units.ne_zero y)
  have hcNN : Measure.addHaarScalarFactor ν μ.μ =
      Real.toNNReal ((A1.absFin v y)⁻¹) := by
    apply Subtype.ext
    calc
      (Measure.addHaarScalarFactor ν μ.μ : ℝ) = (A1.absFin v y)⁻¹ := by
        simpa using hcReal
      _ = (Real.toNNReal ((A1.absFin v y)⁻¹) : ℝ) :=
        (Real.coe_toNNReal _ (inv_nonneg.mpr hAbsPos.le)).symm
  have hscaleNN : ν = (Real.toNNReal ((A1.absFin v y)⁻¹)) • μ.μ := by
    rw [hcNN] at hscale
    exact hscale
  have hcoe : (Real.toNNReal ((A1.absFin v y)⁻¹) : ENNReal) =
      ENNReal.ofReal ((A1.absFin v y)⁻¹) := by
    exact ENNReal.ofNNReal_toNNReal _
  have hscaleENN : ν = ENNReal.ofReal ((A1.absFin v y)⁻¹) • μ.μ := by
    calc
      ν = (Real.toNNReal ((A1.absFin v y)⁻¹)) • μ.μ := hscaleNN
      _ = (Real.toNNReal ((A1.absFin v y)⁻¹) : ENNReal) • μ.μ := by
        rw [ENNReal.smul_def]
      _ = ENNReal.ofReal ((A1.absFin v y)⁻¹) • μ.μ := by rw [hcoe]
  have hmapEq : Measure.map eMeas μ.μ =
      Measure.map (fun x : K => (y : K) * x) μ.μ := by
    apply Measure.map_congr
    filter_upwards with x
    exact (he x).symm
  calc
    Measure.map (fun x : K => (y : K) * x) μ.μ = Measure.map eMeas μ.μ := hmapEq.symm
    _ = ENNReal.ofReal (A1.absFin v y)⁻¹ • μ.μ := hscaleENN

private theorem sheet_mulHaarFin_mul {v : FinPlace F} (μ : Theta.LocHaar v)
    (y : (v.adicCompletion F)ˣ) :
    Measure.map (fun x : v.adicCompletion F => (y : v.adicCompletion F) * x)
      (Theta.mulHaarFin μ) = Theta.mulHaarFin μ := by
  classical
  let K := v.adicCompletion F
  let x : ℝ := A1.absFin v y
  let c : ENNReal := ENNReal.ofReal x
  let d : K → ENNReal := fun z => ENNReal.ofReal ((A1.absFin v z)⁻¹)
  let e : K ≃ₜ+ K := (ContinuousLinearEquiv.smulLeft (R₁ := K) y).toContinuousAddEquiv
  let eMeas : K ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  have hx : 0 < x := by
    dsimp [x]
    rw [A1.Theta.absFin_eq_norm]
    exact norm_pos_iff.mpr (Units.ne_zero y)
  have he (z : K) : eMeas z = (y : K) * z := by
    change e z = (y : K) * z
    change (y : K) • z = _
    rfl
  have heSymm (z : K) : eMeas.symm z = ((y⁻¹ : Kˣ) : K) * z := by
    change e.symm z = _
    apply e.injective
    simp [e, Units.smul_def, smul_eq_mul, mul_assoc]
  have hAbs (z : K) : A1.absFin v (eMeas.symm z) = x⁻¹ * A1.absFin v z := by
    calc
      A1.absFin v (eMeas.symm z) =
          A1.absFin v (((y⁻¹ : Kˣ) : K) * z) := by rw [heSymm]
      _ = ‖((y⁻¹ : Kˣ) : K) * z‖ := A1.Theta.absFin_eq_norm v _
      _ = ‖((y⁻¹ : Kˣ) : K)‖ * ‖z‖ := norm_mul _ _
      _ = ‖(y : K)‖⁻¹ * ‖z‖ := by rw [Units.val_inv_eq_inv_val, norm_inv]
      _ = x⁻¹ * A1.absFin v z := by
        rw [← A1.Theta.absFin_eq_norm v (y : K), ← A1.Theta.absFin_eq_norm v z]
  have hzNonneg (z : K) : 0 ≤ A1.absFin v z := by
    rw [A1.Theta.absFin_eq_norm]
    exact norm_nonneg _
  have hWeight (z : K) : d (eMeas.symm z) = c * d z := by
    dsimp [d, c, x]
    rw [hAbs]
    have hrecip (t : ℝ) : (x⁻¹ * t)⁻¹ = x * t⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hrecip, ENNReal.ofReal_mul (le_of_lt hx)]
  have hscale := sheet_locHaar_map_mul μ y
  have hmapEqAdd : Measure.map eMeas μ.μ =
      Measure.map (fun z : K => (y : K) * z) μ.μ := by
    apply Measure.map_congr
    filter_upwards with z
    exact (he z).symm
  have hscaleMeas : Measure.map eMeas μ.μ = c⁻¹ • μ.μ := by
    calc
      Measure.map eMeas μ.μ = Measure.map (fun z : K => (y : K) * z) μ.μ := hmapEqAdd
      _ = c⁻¹ • μ.μ := by
        rw [ENNReal.ofReal_inv_of_pos hx] at hscale
        simpa [c, x] using hscale
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hx).ne'
  have hmulDensity :
      Measure.map eMeas (μ.μ.withDensity d) = μ.μ.withDensity d := by
    calc
      Measure.map eMeas (μ.μ.withDensity d) =
          (Measure.map eMeas μ.μ).withDensity (fun z => d (eMeas.symm z)) :=
        map_withDensity_measurableEquiv eMeas μ.μ d
      _ = (c⁻¹ • μ.μ).withDensity (c • d) := by
        rw [hscaleMeas]
        congr 1
        funext z
        simpa only [Pi.smul_apply, smul_eq_mul] using hWeight z
      _ = c⁻¹ • (μ.μ.withDensity (c • d)) :=
        MeasureTheory.withDensity_smul_measure c⁻¹ (c • d)
      _ = c⁻¹ • (c • μ.μ.withDensity d) := by
        rw [MeasureTheory.withDensity_smul' c d ENNReal.ofReal_ne_top]
      _ = μ.μ.withDensity d := by
        have hcTop : c ≠ ⊤ := by simp [c]
        rw [smul_smul, ENNReal.inv_mul_cancel hc0 hcTop, one_smul]
  have hmapEq : Measure.map eMeas (Theta.mulHaarFin μ) =
      Measure.map (fun z : K => (y : K) * z) (Theta.mulHaarFin μ) := by
    apply Measure.map_congr
    filter_upwards with z
    exact (he z).symm
  have hmapEq' : Measure.map eMeas (μ.μ.withDensity d) =
      Measure.map (fun z : K => (y : K) * z) (μ.μ.withDensity d) := by
    simpa [Theta.mulHaarFin, d] using hmapEq
  rw [Theta.mulHaarFin]
  calc
    Measure.map (fun z : K => (y : K) * z) (μ.μ.withDensity d) =
        Measure.map eMeas (μ.μ.withDensity d) := hmapEq'.symm
    _ = μ.μ.withDensity d := hmulDensity
    _ = Theta.mulHaarFin μ := rfl

private theorem sheet_complexVolume_map_mul (a : ℂˣ) :
    Measure.map (fun z : ℂ => (a : ℂ) * z) volume =
      ENNReal.ofReal (Complex.normSq (a : ℂ))⁻¹ • volume := by
  classical
  let r : ℝ := ‖(a : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr (Units.ne_zero a)
  let u : Circle := ⟨(a : ℂ) / r, by
    change dist ((a : ℂ) / r) (0 : ℂ) = 1
    rw [dist_eq_norm]
    rw [sub_zero]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    change ‖(a : ℂ)‖ / r = 1
    dsimp [r]
    exact div_self (ne_of_gt hr)⟩
  have hdecomp : (a : ℂ) = (r : ℂ) * u := by
    dsimp [u, r]
    field_simp [ne_of_gt hr]
  have hcomp : (fun z : ℂ => (a : ℂ) * z) = fun z => r • rotation u z := by
    funext z
    rw [hdecomp, rotation_apply, Complex.real_smul]
    push_cast
    ring
  have hrot : MeasurePreserving (rotation u) (volume : Measure ℂ) volume :=
    LinearIsometryEquiv.measurePreserving (rotation u)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hnormsq : Complex.normSq (a : ℂ) = r ^ 2 := by
    simp [Complex.normSq_eq_norm_sq, r]
  have hcoeff : ENNReal.ofReal |(r ^ (Module.finrank ℝ ℂ))⁻¹| =
      ENNReal.ofReal (Complex.normSq (a : ℂ))⁻¹ := by
    rw [Complex.finrank_real_complex, hnormsq,
      abs_of_pos (inv_pos.mpr hr2), ENNReal.ofReal_inv_of_pos hr2]
  calc
    Measure.map (fun z : ℂ => (a : ℂ) * z) volume =
    Measure.map (fun z : ℂ => r • rotation u z) volume := by rw [hcomp]
    _ = Measure.map (fun z : ℂ => r • z) (Measure.map (rotation u) volume) := by
      have hcomp' : (fun z : ℂ => r • rotation u z) =
          (fun z : ℂ => r • z) ∘ rotation u := rfl
      rw [hcomp']
      exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = Measure.map (fun z : ℂ => r • z) volume := by rw [hrot.map_eq]
    _ = ENNReal.ofReal (Complex.normSq (a : ℂ))⁻¹ • volume := by
      rw [Measure.map_addHaar_smul volume hr.ne', hcoeff]

private theorem sheet_mulHaarC_mul (a : ℂˣ) :
    Measure.map (fun z : ℂ => (a : ℂ) * z) Theta.mulHaarC = Theta.mulHaarC := by
  classical
  let c : ENNReal := ENNReal.ofReal (Complex.normSq (a : ℂ))
  let d : ℂ → ENNReal := fun z => ENNReal.ofReal ((Complex.normSq z)⁻¹)
  let e : ℂ ≃ₜ+ ℂ := (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) a).toContinuousAddEquiv
  let eMeas : ℂ ≃ᵐ ℂ := e.toHomeomorph.toMeasurableEquiv
  have hnormPos : 0 < Complex.normSq (a : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero a))
  have he (z : ℂ) : eMeas z = (a : ℂ) * z := by
    change e z = (a : ℂ) * z
    change (a : ℂ) • z = _
    rfl
  have heSymm (z : ℂ) : eMeas.symm z = ((a⁻¹ : ℂˣ) : ℂ) * z := by
    change e.symm z = _
    apply e.injective
    simp [e, Units.smul_def, smul_eq_mul, mul_assoc]
  have hInv : Complex.normSq ((a : ℂ)⁻¹) = (Complex.normSq (a : ℂ))⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, norm_inv, Complex.normSq_eq_norm_sq]
    ring
  have hnormMul (z : ℂ) :
      Complex.normSq (eMeas.symm z) = (Complex.normSq (a : ℂ))⁻¹ * Complex.normSq z := by
    rw [heSymm, Complex.normSq_mul, Units.val_inv_eq_inv_val, hInv]
  have hWeight (z : ℂ) : d (eMeas.symm z) = c * d z := by
    dsimp [d, c]
    rw [hnormMul]
    have hrecip (t : ℝ) : ((Complex.normSq (a : ℂ))⁻¹ * t)⁻¹ =
        Complex.normSq (a : ℂ) * t⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hrecip, ENNReal.ofReal_mul (le_of_lt hnormPos)]
  have hscale : Measure.map eMeas volume = c⁻¹ • volume := by
    have hmapEq : Measure.map eMeas volume =
        Measure.map (fun z : ℂ => (a : ℂ) * z) volume := by
      apply Measure.map_congr
      filter_upwards with z
      exact (he z).symm
    calc
      Measure.map eMeas volume =
          Measure.map (fun z : ℂ => (a : ℂ) * z) volume := hmapEq
      _ = c⁻¹ • volume := by simpa [c] using sheet_complexVolume_map_mul a
  have hmulDensity : Measure.map eMeas (volume.withDensity d) = volume.withDensity d := by
    calc
      Measure.map eMeas (volume.withDensity d) =
          (Measure.map eMeas volume).withDensity (fun z => d (eMeas.symm z)) :=
        map_withDensity_measurableEquiv eMeas volume d
      _ = (c⁻¹ • volume).withDensity (c • d) := by
        rw [hscale]
        congr 1
        funext z
        simpa only [Pi.smul_apply, smul_eq_mul] using hWeight z
      _ = c⁻¹ • (volume.withDensity (c • d)) :=
        MeasureTheory.withDensity_smul_measure c⁻¹ (c • d)
      _ = c⁻¹ • (c • volume.withDensity d) := by
        rw [MeasureTheory.withDensity_smul' c d ENNReal.ofReal_ne_top]
      _ = volume.withDensity d := by
        have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hnormPos).ne'
        have hcTop : c ≠ ⊤ := by simp [c]
        rw [smul_smul, ENNReal.inv_mul_cancel hc0 hcTop, one_smul]
  have hmapEq : Measure.map eMeas (Theta.mulHaarC) =
      Measure.map (fun z : ℂ => (a : ℂ) * z) Theta.mulHaarC := by
    apply Measure.map_congr
    filter_upwards with z
    exact (he z).symm
  have hmapEq' : Measure.map eMeas (volume.withDensity d) =
      Measure.map (fun z : ℂ => (a : ℂ) * z) (volume.withDensity d) := by
    simpa [Theta.mulHaarC, d] using hmapEq
  rw [Theta.mulHaarC]
  calc
    Measure.map (fun z : ℂ => (a : ℂ) * z) (volume.withDensity d) =
        Measure.map eMeas (volume.withDensity d) := hmapEq'.symm
    _ = volume.withDensity d := hmulDensity
    _ = Theta.mulHaarC := rfl

private theorem a2_prod_sol_sheetFree_mul_preserving
    (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
    (v0 : InfinitePlace F) (a : S.FSˣ) :
    MeasurePreserving
      (fun p : SheetFree S v0 =>
        (fun v => (a : S.FS).1 v * p.1 v,
         fun w => (a : S.FS).2 w.1 * p.2 w))
      ((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
        (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC))
      ((Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)).prod
        (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)) := by
  classical
  have hlocal := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  letI : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => (hlocal.1 v.1).2.2.2.2
  letI : SigmaFinite Theta.mulHaarC := hlocal.2.2
  have hf : MeasurePreserving
      (fun p : ∀ v : S.Sf, v.1.adicCompletion F => fun v => (a : S.FS).1 v * p v)
      (Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1))
      (Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)) := by
    apply measurePreserving_pi
    intro v
    let av : (v.1.adicCompletion F)ˣ := {
      val := (a : S.FS).1 v
      inv := a.inv.1 v
      val_inv := by
        simpa only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] using
          congrArg (fun z : S.FS => z.1 v) a.val_inv
      inv_val := by
        simpa only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] using
          congrArg (fun z : S.FS => z.1 v) a.inv_val }
    exact ⟨(continuous_const.mul continuous_id).measurable,
      sheet_mulHaarFin_mul (μ v.1) av⟩
  have hc : MeasurePreserving
      (fun p : {w : InfinitePlace F // w ≠ v0} → ℂ =>
        fun w => (a : S.FS).2 w.1 * p w)
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC)
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => Theta.mulHaarC) := by
    apply measurePreserving_pi
    intro w
    let aw : ℂˣ := {
      val := (a : S.FS).2 w.1
      inv := a.inv.2 w.1
      val_inv := by
        simpa only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] using
          congrArg (fun z : S.FS => z.2 w.1) a.val_inv
      inv_val := by
        simpa only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] using
          congrArg (fun z : S.FS => z.2 w.1) a.inv_val }
    exact ⟨(continuous_const.mul continuous_id).measurable, sheet_mulHaarC_mul aw⟩
  simpa only [Prod.map_def] using hf.prod hc

private theorem a2_prod_sol_sheetPoint_mul
    (S : SData F CE condη) (v0 : InfinitePlace F)
    (a : S.FSˣ) (T : ℝ) (hT : 0 < T)
    (p : SheetFree S v0) (θ : ℝ)
    (hf : ∀ v, p.1 v ≠ 0) (hc : ∀ w, p.2 w ≠ 0) :
    (a : S.FS) * Theta.sheetPoint S v0 T p θ =
    Theta.sheetPoint S v0 (S.absS (a : S.FS) * T)
      (fun v => (a : S.FS).1 v * p.1 v,
       fun w => (a : S.FS).2 w.1 * p.2 w)
      (θ + Complex.arg ((a : S.FS).2 v0) / (2 * Real.pi)) := by
  classical
  let A : ℝ := (∏ v : S.Sf, A1.absFin v.1 ((a : S.FS).1 v)) *
    ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq ((a : S.FS).2 w.1)
  let B : ℝ := (∏ v : S.Sf, A1.absFin v.1 (p.1 v)) *
    ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  let c : ℂ := (a : S.FS).2 v0
  have ha : (∀ v : S.Sf, IsUnit ((a : S.FS).1 v)) ∧
      ∀ w : InfinitePlace F, IsUnit ((a : S.FS).2 w) := by
    simpa only [Prod.isUnit_iff, Pi.isUnit_iff] using a.isUnit
  have hA : 0 < A := by
    dsimp [A]
    apply mul_pos
    · apply Finset.prod_pos
      intro v _
      rw [A1.Theta.absFin_eq_norm]
      exact norm_pos_iff.mpr (ha.1 v).ne_zero
    · apply Finset.prod_pos
      intro w _
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (ha.2 w.1).ne_zero)
  have hB : 0 < B := by
    dsimp [B]
    apply mul_pos
    · apply Finset.prod_pos
      intro v _
      rw [A1.Theta.absFin_eq_norm]
      exact norm_pos_iff.mpr (hf v)
    · apply Finset.prod_pos
      intro w _
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hc w))
  have hAbs : S.absS (a : S.FS) = A * Complex.normSq c := by
    rw [SData.absS, Fintype.prod_eq_mul_prod_subtype_ne
      (fun w : InfinitePlace F => Complex.normSq ((a : S.FS).2 w)) v0]
    dsimp [A, c]
    ring
  have hfree :
      (∏ v : S.Sf, A1.absFin v.1 ((a : S.FS).1 v * p.1 v)) *
        ∏ w : {w : InfinitePlace F // w ≠ v0},
          Complex.normSq ((a : S.FS).2 w.1 * p.2 w) = A * B := by
    simp_rw [A1.Theta.absFin_eq_norm, norm_mul, Complex.normSq_mul,
      Finset.prod_mul_distrib]
    dsimp [A, B]
    simp_rw [A1.Theta.absFin_eq_norm]
    ring
  have hratio : (S.absS (a : S.FS) * T) / (A * B) =
      Complex.normSq c * (T / B) := by
    rw [hAbs]
    field_simp [hA.ne', hB.ne']
    <;> ring
  have hradius : Real.sqrt ((S.absS (a : S.FS) * T) / (A * B)) =
      ‖c‖ * Real.sqrt (T / B) := by
    rw [hratio, Complex.normSq_eq_norm_sq, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
  have hangle : (2 * Real.pi : ℝ) *
      (θ + Complex.arg c / (2 * Real.pi)) =
      2 * Real.pi * θ + Complex.arg c := by
    field_simp [Real.pi_ne_zero]
  have hexp :
      Complex.exp (2 * Real.pi * Complex.I *
        ((θ + Complex.arg c / (2 * Real.pi) : ℝ) : ℂ)) =
      Complex.exp ((Complex.arg c : ℂ) * Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) := by
    have he : 2 * Real.pi * Complex.I *
        ((θ + Complex.arg c / (2 * Real.pi) : ℝ) : ℂ) =
        (Complex.arg c : ℂ) * Complex.I +
          2 * Real.pi * Complex.I * (θ : ℂ) := by
      calc
        _ = (((2 * Real.pi : ℝ) *
            (θ + Complex.arg c / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        _ = _ := by
          rw [hangle]
          push_cast
          ring
    rw [he, Complex.exp_add]
  apply Prod.ext
  · rfl
  · funext w
    by_cases hw : w = v0
    · subst w
      simp only [Prod.snd_mul, Pi.mul_apply, Theta.sheetPoint, dif_pos rfl]
      change c * (((Real.sqrt (T / B) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) =
        ((Real.sqrt ((S.absS (a : S.FS) * T) /
          ((∏ v : S.Sf, A1.absFin v.1 ((a : S.FS).1 v * p.1 v)) *
            ∏ w : {w : InfinitePlace F // w ≠ v0},
              Complex.normSq ((a : S.FS).2 w.1 * p.2 w))) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((θ + Complex.arg c / (2 * Real.pi) : ℝ) : ℂ))
      rw [hfree, hradius, hexp, Complex.ofReal_mul]
      calc
        _ = (((‖c‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg c : ℂ) * Complex.I)) *
            (((Real.sqrt (T / B) : ℝ) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
        _ = _ := by ring
    · simp only [Prod.snd_mul, Pi.mul_apply, Theta.sheetPoint, dif_neg hw]

private theorem sheet_integral_Ioc_periodic_translate (g : ℝ → ℂ)
    (hg : Function.Periodic g 1) (c : ℝ) :
    ∫ θ in Set.Ioc (0 : ℝ) 1, g (θ + c) ∂volume =
      ∫ θ in Set.Ioc (0 : ℝ) 1, g θ ∂volume := by
  calc
    ∫ θ in Set.Ioc (0 : ℝ) 1, g (θ + c) ∂volume =
        ∫ θ in (0 : ℝ)..1, g (θ + c) := by
          rw [← intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ θ in c..c + 1, g θ := by
      simpa only [zero_add, add_comm 1 c] using
        intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (1 : ℝ)) g c
    _ = ∫ θ in (0 : ℝ)..1, g θ := by
      simpa only [zero_add] using hg.intervalIntegral_add_eq c 0
    _ = ∫ θ in Set.Ioc (0 : ℝ) 1, g θ ∂volume :=
      intervalIntegral.integral_of_le (by norm_num)

theorem sheetOmega_exists (D : FieldData F) (S : SData F CE condη) :
    ∃ Ω K : Set S.FS, MeasurableSet Ω ∧ IsCompact K ∧ Ω ⊆ K ∧
      (∀ y ∈ Ω, IsUnit y ∧ S.absS y = 1) ∧
      (∀ y : S.FSˣ, S.absS (y : S.FS) = 1 →
        ∃! γ : Gamma S, sheetGammaAction S γ (y : S.FS) ∈ Ω) := by
  classical
  obtain ⟨K, hKcompact, hKrep⟩ := S.FSOne_quotient_compact D
  have hAbsCont : Continuous S.absS := sheet_absS_continuous S
  let K1 : Set S.FS := K ∩ {z | S.absS z = 1}
  have hK1compact : IsCompact K1 := by
    apply hKcompact.inter_right
    exact isClosed_singleton.preimage hAbsCont
  have hK1meas : MeasurableSet K1 := hK1compact.isClosed.measurableSet
  let Λ : AddSubgroup S.FS :=
    (S.diag.toAddMonoidHom.comp S.R.val.toAddMonoidHom).range
  have hdiagR : (Λ : Set S.FS) = S.diagR := rfl
  have hdiscR : IsDiscrete (S.diagR : Set S.FS) :=
    (S.diagR_discrete_cocompact D).1
  have hdiscΛ : IsDiscrete (Λ : Set S.FS) := by
    simpa [hdiagR] using hdiscR
  letI : DiscreteTopology Λ := (isDiscrete_iff_discreteTopology).mp hdiscΛ
  have hΛclosed : IsClosed (Λ : Set S.FS) := AddSubgroup.isClosed_of_discreteTopology
  have hcompactDiscreteFinite (C : Set S.FS) (hC : IsCompact C) :
      (C ∩ (Λ : Set S.FS)).Finite := by
    have hCΛcompact : IsCompact (C ∩ (Λ : Set S.FS)) := hC.inter_right hΛclosed
    have hCΛdiscrete : IsDiscrete (C ∩ (Λ : Set S.FS)) := by
      apply IsDiscrete.of_nhdsWithin
      intro x hx
      exact (nhdsWithin_mono x Set.inter_subset_right).trans
        (hdiscΛ.nhdsWithin x hx.2).le
    exact hCΛcompact.finite hCΛdiscrete
  have hdiagUS (u : S.US) :
      (S.diagU (u : Fˣ) : S.FS) ∈ (Λ : Set S.FS) := by
    change ∃ x : S.R, S.diag (x : F) = S.diag ((u : Fˣ) : F)
    let ru : (S.R)ˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F u
    exact ⟨ru.1, rfl⟩
  have hUSnorm (u : S.US) : S.absS (S.diagU (u : Fˣ) : S.FS) = 1 :=
    (ArtinPrimitiveRoots.A2.a2_bridge_NORM D S).2.2.2.1 u
  let good := fun (y : S.FSˣ) =>
    {γ : Gamma S | sheetGammaAction S γ (y : S.FS) ∈ K1}
  have hgoodFinite (y : S.FSˣ) : (good y).Finite := by
    let Kshift : Set S.FS :=
      (fun z : S.FS => z * ((y : S.FS)⁻¹)) '' K1
    have hKshift : IsCompact Kshift := by
      dsimp [Kshift]
      exact hK1compact.image (continuous_id.mul continuous_const)
    apply Set.Finite.of_injOn
      (f := fun γ : Gamma S => (((S.diagU (γ.1 : Fˣ))⁻¹ : S.FSˣ) : S.FS))
      (s := good y) (t := Kshift ∩ (Λ : Set S.FS)) ?_ ?_
      (hcompactDiscreteFinite Kshift hKshift)
    · intro γ hγ
      constructor
      · refine ⟨sheetGammaAction S γ (y : S.FS), hγ, ?_⟩
        simp [Kshift, sheetGammaAction, mul_assoc]
      · have h := hdiagUS ((γ.1 : S.US)⁻¹)
        have hmap : S.diagU (((γ.1 : S.US)⁻¹ : S.US) : Fˣ) =
            (S.diagU (γ.1 : Fˣ))⁻¹ := by simp [map_inv]
        rw [hmap] at h
        change (((S.diagU (γ.1 : Fˣ))⁻¹ : S.FSˣ) : S.FS) ∈ (Λ : Set S.FS)
        simpa only [Units.val_inv_eq_inv_val] using h
    · intro γ hγ δ hδ hEq
      have hEqUnits :
          ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FSˣ) = (S.diagU (δ.1 : Fˣ))⁻¹ := by
        apply Units.ext
        simpa only [Units.val_inv_eq_inv_val] using hEq
      have hDiag : S.diagU (γ.1 : Fˣ) = S.diagU (δ.1 : Fˣ) := inv_injective hEqUnits
      have hF : (γ.1 : Fˣ) = (δ.1 : Fˣ) := sheet_diagU_injective S hDiag
      exact Subtype.ext (Subtype.ext hF)
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Fˣ) := Units.val_injective.countable
  letI : Countable (S.US) := Subtype.val_injective.countable
  letI : Countable (Gamma S) := Subtype.val_injective.countable
  let codeExists := MeasureTheory.exists_measurableEmbedding_real S.FS
  let code : S.FS → ℝ := Classical.choose codeExists
  have hcode : MeasurableEmbedding code := Classical.choose_spec codeExists
  let Ω : Set S.FS :=
    {z | z ∈ K1 ∧ ∀ γ : Gamma S,
      sheetGammaAction S γ z ∈ K1 → code z ≤ code (sheetGammaAction S γ z)}
  have hcondition (γ : Gamma S) : MeasurableSet
    {z : S.FS | sheetGammaAction S γ z ∈ K1 →
        code z ≤ code (sheetGammaAction S γ z)} := by
    have hact : Measurable (sheetGammaAction S γ) := by
      exact measurable_const.mul measurable_id
    have hpre : MeasurableSet {z : S.FS | sheetGammaAction S γ z ∈ K1} :=
      hK1meas.preimage hact
    have hle : MeasurableSet {z : S.FS | code z ≤ code (sheetGammaAction S γ z)} :=
      measurableSet_le hcode.measurable (hcode.measurable.comp hact)
    have hset : {z : S.FS | sheetGammaAction S γ z ∈ K1 →
        code z ≤ code (sheetGammaAction S γ z)} =
        {z | sheetGammaAction S γ z ∈ K1}ᶜ ∪
          {z | code z ≤ code (sheetGammaAction S γ z)} := by
      ext z
      by_cases hz : sheetGammaAction S γ z ∈ K1 <;> simp [hz]
    rw [hset]
    exact hpre.compl.union hle
  have hΩeq : Ω = K1 ∩ ⋂ γ : Gamma S,
      {z : S.FS | sheetGammaAction S γ z ∈ K1 →
        code z ≤ code (sheetGammaAction S γ z)} := by
    ext z
    simp [Ω]
  have hΩmeas : MeasurableSet Ω := by
    rw [hΩeq]
    exact hK1meas.inter (MeasurableSet.iInter hcondition)
  have hΩK : Ω ⊆ K := by
    intro z hz
    exact hz.1.1
  have hΩnorm : ∀ z ∈ Ω, IsUnit z ∧ S.absS z = 1 := by
    intro z hz
    exact ⟨sheet_absS_one_isUnit S hz.1.2, hz.1.2⟩
  have hΩrep : ∀ y : S.FSˣ, S.absS (y : S.FS) = 1 →
      ∃! γ : Gamma S, sheetGammaAction S γ (y : S.FS) ∈ Ω := by
    intro y hy
    let x : S.FSOne := ⟨y, hy⟩
    obtain ⟨z, hzK, hrel⟩ := hKrep x
    rcases hrel with ⟨u, hu⟩
    let γ₀ : Gamma S := ⟨u ^ 6, by
      change u ^ 6 ∈ (sixthPowerOnUS S).range
      exact ⟨u, rfl⟩⟩
    have hdiag : S.diagU (γ₀.1 : Fˣ) = (S.diagU (u : Fˣ)) ^ 6 := by
      change S.diagU ((u : Fˣ) ^ 6) = _
      exact map_pow (S.diagU) (u : Fˣ) 6
    have hyunit : y = (S.diagU (u : Fˣ)) ^ 6 * z.1 := by
      simpa [x] using hu
    have hrepr : sheetGammaAction S γ₀ (y : S.FS) = z.1 := by
      have hreprUnit : (S.diagU (γ₀.1 : Fˣ))⁻¹ * y = z.1 := by
        rw [hdiag, hyunit]
        group
      simpa [sheetGammaAction] using
        congrArg (fun q : S.FSˣ => (q : S.FS)) hreprUnit
    have hzK1 : (z.1 : S.FS) ∈ K1 := ⟨hzK, z.2⟩
    have hγ₀good : γ₀ ∈ good y := by
      change sheetGammaAction S γ₀ (y : S.FS) ∈ K1
      rw [hrepr]
      exact hzK1
    obtain ⟨γmin, hγmin, hmin⟩ :=
      Set.exists_min_image (good y) (fun γ => code (sheetGammaAction S γ (y : S.FS)))
        (hgoodFinite y) ⟨γ₀, hγ₀good⟩
    let zmin := sheetGammaAction S γmin (y : S.FS)
    have hzminOmega : zmin ∈ Ω := by
      refine ⟨hγmin, ?_⟩
      intro δ hδ
      have hcomp : sheetGammaAction S δ zmin =
          sheetGammaAction S (δ * γmin) (y : S.FS) := by
        simpa [zmin] using sheetGammaAction_mul S δ γmin (y : S.FS)
      have hδgood : δ * γmin ∈ good y := by
        change sheetGammaAction S (δ * γmin) (y : S.FS) ∈ K1
        rw [← hcomp]
        exact hδ
      calc
        code zmin = code (sheetGammaAction S γmin (y : S.FS)) := rfl
        _ ≤ code (sheetGammaAction S (δ * γmin) (y : S.FS)) :=
          hmin (δ * γmin) hδgood
        _ = code (sheetGammaAction S δ zmin) := by rw [← hcomp]
    refine ⟨γmin, hzminOmega, ?_⟩
    intro γ hγΩ
    have hγgood : γ ∈ good y := hγΩ.1
    have hminLe : code zmin ≤ code (sheetGammaAction S γ (y : S.FS)) :=
      hmin γ hγgood
    have hreverse : code (sheetGammaAction S γ (y : S.FS)) ≤ code zmin := by
      let δ := γmin * γ⁻¹
      have htrans : sheetGammaAction S δ (sheetGammaAction S γ (y : S.FS)) = zmin := by
        calc
          sheetGammaAction S δ (sheetGammaAction S γ (y : S.FS)) =
              sheetGammaAction S (δ * γ) (y : S.FS) := sheetGammaAction_mul S δ γ _
          _ = zmin := by
            simp [zmin, δ]
      have hz : sheetGammaAction S δ (sheetGammaAction S γ (y : S.FS)) ∈ K1 := by
        rw [htrans]
        exact hγmin
      have hbound := hγΩ.2 δ hz
      rw [htrans] at hbound
      exact hbound
    have hcodeEq : code zmin = code (sheetGammaAction S γ (y : S.FS)) :=
      le_antisymm hminLe hreverse
    have hactEq : sheetGammaAction S γmin (y : S.FS) =
        sheetGammaAction S γ (y : S.FS) := hcode.injective hcodeEq
    have hInvValEq : ((S.diagU (γmin.1 : Fˣ))⁻¹ : S.FS) =
        ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) := by
      have h := congrArg (fun v : S.FS => v * ((y : S.FS)⁻¹)) hactEq
      simpa [sheetGammaAction, mul_assoc] using h
    have hInvEq : (S.diagU (γmin.1 : Fˣ))⁻¹ =
        (S.diagU (γ.1 : Fˣ))⁻¹ := by
      apply Units.ext
      simpa only [Units.val_inv_eq_inv_val] using hInvValEq
    have hDiag : S.diagU (γmin.1 : Fˣ) = S.diagU (γ.1 : Fˣ) :=
      inv_injective hInvEq
    have hF : (γmin.1 : Fˣ) = (γ.1 : Fˣ) := sheet_diagU_injective S hDiag
    exact Subtype.ext (Subtype.ext hF.symm)
  exact ⟨Ω, K, hΩmeas, hKcompact, hΩK, hΩnorm, hΩrep⟩

theorem sheet_mul_disintegrate (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (f : S.FS → ℂ)
    (hf : Integrable f ((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ)) :
    ∫ y, f y ∂((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ) =
      ∫ T in Set.Ioi (0 : ℝ), (Theta.sheetInt S μ v0 f T) / (T : ℂ) := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hpi0 : ENNReal.ofReal Real.pi ≠ 0 :=
    (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
  have hc0 : (ENNReal.ofReal Real.pi)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hctop : (ENNReal.ofReal Real.pi)⁻¹ ≠ ⊤ := by
    intro h
    exact hpi0 (ENNReal.inv_eq_top.mp h)
  have hbase : Integrable f (Theta.mulHaarS S μ) :=
    (integrable_smul_measure hc0 hctop).mp hf
  have hdis := Theta.sheet_disintegration S μ v0 f hbase
  have hscale : (((ENNReal.ofReal Real.pi)⁻¹).toReal : ℝ) = Real.pi⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal Real.pi_pos.le]
  calc
    ∫ y, f y ∂((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ) =
        (((ENNReal.ofReal Real.pi)⁻¹).toReal : ℂ) *
          ∫ y, f y ∂Theta.mulHaarS S μ := by
      rw [integral_smul_measure, Complex.real_smul]
    _ = ∫ T in Set.Ioi (0 : ℝ), (Theta.sheetInt S μ v0 f T) / (T : ℂ) := by
      rw [hdis, hscale]
      push_cast
      field_simp [Real.pi_ne_zero]

theorem sheet_measure_disintegrate (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (f : S.FS → ℂ)
    (hf : Integrable f ((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ)) :
    ∫ y, f y ∂((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ) =
      ∫ T in Set.Ioi (0 : ℝ),
        (∫ y, f y ∂sheetMeasure S μ v0 T) / (T : ℂ) := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hpi0 : ENNReal.ofReal Real.pi ≠ 0 :=
    (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
  have hc0 : (ENNReal.ofReal Real.pi)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hctop : (ENNReal.ofReal Real.pi)⁻¹ ≠ ⊤ := by
    intro h
    exact hpi0 (ENNReal.inv_eq_top.mp h)
  have hbase : Integrable f (Theta.mulHaarS S μ) :=
    (integrable_smul_measure hc0 hctop).mp hf
  have hslice := sheetParameter_integrable_ae S μ v0 f hbase
  have hden : Measurable (fun T : ℝ => ENNReal.ofReal T⁻¹) := by fun_prop
  have hTpos : ∀ᵐ T ∂ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure,
      0 < T := by
    rw [ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure,
      ae_withDensity_iff hden]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    intro _
    exact hT
  have hsliceRad : ∀ᵐ T ∂ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure,
      Integrable f (sheetMeasure S μ v0 T) := by
    filter_upwards [hslice, hTpos] with T hparam hT
    apply integrable_sheetMeasure_of_parameter S μ v0 T hT f
    simpa [sheetParameterMap, sheetParameterMeasure] using hparam
  have hsliceVol : ∀ᵐ T ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Integrable f (sheetMeasure S μ v0 T) := by
    have h := hsliceRad
    rw [ArtinPrimitiveRoots.Proofs.thsol_sheets.polarRadialMeasure,
      ae_withDensity_iff hden] at h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with T hT hI
    exact hT (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hI))
  have hEq : ∀ᵐ T ∂volume.restrict (Set.Ioi (0 : ℝ)),
      (∫ y, f y ∂sheetMeasure S μ v0 T) = Theta.sheetInt S μ v0 f T := by
    filter_upwards [hsliceVol] with T hT
    exact integral_sheetMeasure_eq_sheetInt S μ v0 T f hT
  calc
    ∫ y, f y ∂((ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ) =
        ∫ T in Set.Ioi (0 : ℝ), (Theta.sheetInt S μ v0 f T) / (T : ℂ) :=
      sheet_mul_disintegrate D S μ v0 f hf
    _ = ∫ T in Set.Ioi (0 : ℝ),
        (∫ y, f y ∂sheetMeasure S μ v0 T) / (T : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hEq] with T hT
      rw [← hT]

end ArtinPrimitiveRoots.Proofs.A2_PRODUCERS
