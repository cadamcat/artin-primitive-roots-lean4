import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.TensorSheetIntegrable
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
import ArtinPrimitiveRoots.Theta.AnalysisS

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

set_option maxHeartbeats 2000000 in
/-- The full absolute tensor sheet integral decays quadratically, with one
dependent Schwartz supremum and positive weighted moments at free places. -/
theorem tensor_sheet_norm_decay_two
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (G : A2.SheetGeometry D S μ v0)
    (ff : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fc : InfinitePlace F → SchwartzMap ℂ ℂ)
    (hffcont : ∀ v, Continuous (ff v))
    (hffcompact : ∀ v, HasCompactSupport (ff v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      (∫ y, ‖(∏ v : S.Sf, ff v (y.1 v)) *
        ∏ w : InfinitePlace F, fc w (y.2 w)‖ ∂G.sheet T) ≤ C / T ^ 2 := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hsub := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (Theta.mulHaarFin (μ v.1)) :=
    fun v => (hsub.1 v.1).2.2.2.2
  have : SigmaFinite Theta.mulHaarC := hsub.2.2
  have : ∀ v : S.Sf, NullSingletonClass (Theta.mulHaarFin (μ v.1)) := fun v => by
    have : NullSingletonClass (μ v.1).μ := (hsub.1 v.1).2.2.1
    dsimp [Theta.mulHaarFin]
    infer_instance
  have : NullSingletonClass Theta.mulHaarC := hsub.2.1
  let W := {w : InfinitePlace F // w ≠ v0}
  let P := (∀ v : S.Sf, v.1.adicCompletion F) × (W → ℂ)
  let νf := Measure.pi fun v : S.Sf => Theta.mulHaarFin (μ v.1)
  let νc := Measure.pi fun _ : W => Theta.mulHaarC
  let ν : Measure P := νf.prod νc
  let η : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Q := P × ℝ
  let ρ : Measure Q := ν.prod η
  let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
    ∏ w : W, Complex.normSq (p.2 w)
  have hB : Measurable B := by
    apply Measurable.mul
    · exact Finset.measurable_fun_prod Finset.univ fun v hv =>
        (hsub.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · exact Finset.measurable_fun_prod Finset.univ fun w hw =>
        Complex.continuous_normSq.measurable.comp
          ((measurable_pi_apply w).comp measurable_snd)
  have hpos : ∀ᵐ p ∂ν, 0 < B p := by
    have hfn : ∀ᵐ yf ∂νf, ∀ v : S.Sf, yf v ≠ 0 :=
      ae_all_iff.mpr fun v =>
        Measure.ae_eval_ne (fun v : S.Sf => Theta.mulHaarFin (μ v.1)) v 0
    have hcn : ∀ᵐ yc ∂νc, ∀ w : W, yc w ≠ 0 :=
      ae_all_iff.mpr fun w => Measure.ae_eval_ne (fun _ : W => Theta.mulHaarC) w 0
    have hfn' := (Measure.quasiMeasurePreserving_fst (μ := νf) (ν := νc)).ae hfn
    have hcn' := (Measure.quasiMeasurePreserving_snd (μ := νf) (ν := νc)).ae hcn
    filter_upwards [hfn', hcn'] with p hf hc
    apply mul_pos
    · exact Finset.prod_pos fun v hv => (hsub.1 v.1).2.1 (p.1 v) (hf v)
    · exact Finset.prod_pos fun w hw => Complex.normSq_pos.mpr (hc w)
  have hp : ∀ᵐ q ∂ρ, 0 < B q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).ae hpos
  let z : ℝ → Q → ℂ := fun T q =>
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (T / B q.1, q.2)
  let Y : ℝ → Q → S.FS := fun T q => Theta.sheetPoint S v0 T q.1 q.2
  have hzmeas (T : ℝ) : Measurable (z T) :=
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_polar_measurePreserving.measurable.comp
      ((measurable_const.div (hB.comp measurable_fst)).prodMk measurable_snd)
  have hYdep (T : ℝ) (q : Q) : (Y T q).2 v0 = z T q := by
    simp only [Y, Theta.sheetPoint, z, dite_true, B,
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
    rfl
  have hznorm (T : ℝ) (hT : 0 < T) (q : Q) (hq : 0 < B q.1) :
      Complex.normSq (z T q) = T / B q.1 := by
    unfold z ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (q.2 : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_pos hT hq).le]
  have hfree (g : InfinitePlace F → ℂ → ℂ) (T : ℝ) (p : P) (θ : ℝ) :
      (∏ w ∈ Finset.univ.erase v0, g w ((Theta.sheetPoint S v0 T p θ).2 w)) =
        ∏ w : W, g w.1 (p.2 w) := by
    rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w ≠ v0)
      (Finset.univ.erase v0) (by simp [ne_comm])]
    apply Finset.prod_congr rfl
    intro w hw
    simp only [Theta.sheetPoint, dite_eq_right w.property]
  let A : P → ℂ := fun p =>
    (∏ v : S.Sf, ff v (p.1 v)) * ∏ w : W, fc w.1 (p.2 w)
  let H : P → ℝ := fun p =>
    (∏ v : S.Sf, ‖ff v (p.1 v)‖ * absFin v.1 (p.1 v) ^ 2) *
      ∏ w : W, ‖fc w.1 (p.2 w)‖ * Complex.normSq (p.2 w) ^ 2
  have hAmeas : Measurable A := by
    apply Measurable.mul
    · exact Finset.measurable_fun_prod Finset.univ fun v hv =>
        (hffcont v).measurable.comp ((measurable_pi_apply v).comp measurable_fst)
    · exact Finset.measurable_fun_prod Finset.univ fun w hw =>
        (fc w.1).continuous.measurable.comp
          ((measurable_pi_apply w).comp measurable_snd)
  have hHval (p : P) : H p = ‖A p‖ * B p ^ 2 := by
    simp only [H, A, B, norm_mul, norm_prod, Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  have hHnonneg (p : P) : 0 ≤ H p := by
    rw [hHval]
    positivity
  have hHi : Integrable H ν := by
    have hfI (v : S.Sf) : Integrable
        (fun x => ‖ff v x‖ * absFin v.1 x ^ 2) (Theta.mulHaarFin (μ v.1)) := by
      simpa only [Real.rpow_two] using
        ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
          v.1 (μ v.1) (ff v) (hffcont v) (hffcompact v) 2 (by norm_num)
    have hcI (w : W) : Integrable
        (fun x : ℂ => ‖fc w.1 x‖ * Complex.normSq x ^ 2) Theta.mulHaarC := by
      simpa only [Real.rpow_two] using
        ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable
          (fc w.1) 2 (by norm_num)
    exact (Integrable.fintype_prod_dep hfI).mul_prod (Integrable.fintype_prod hcI)
  let C0 : ℝ := SchwartzMap.seminorm ℂ 4 0 (fc v0)
  have hC0 : 0 ≤ C0 := apply_nonneg _ _
  have hsup (y : ℂ) : ‖fc v0 y‖ * Complex.normSq y ^ 2 ≤ C0 := by
    have hh := SchwartzMap.norm_pow_mul_le_seminorm ℂ (fc v0) 4 y
    convert hh using 1
    rw [Complex.normSq_eq_norm_sq]
    ring
  let tensor : S.FS → ℂ := fun y =>
    (∏ v : S.Sf, ff v (y.1 v)) * ∏ w : InfinitePlace F, fc w (y.2 w)
  have hpoint (T : ℝ) (q : Q) : tensor (Y T q) = A q.1 * fc v0 (z T q) := by
    dsimp only [tensor]
    rw [← Finset.mul_prod_erase Finset.univ (fun w => fc w ((Y T q).2 w))
      (Finset.mem_univ v0), hYdep]
    have hf := hfree (fun w y => fc w y) T q.1 q.2
    change (∏ v : S.Sf, ff v (q.1.1 v)) *
      (fc v0 (z T q) * ∏ w ∈ Finset.univ.erase v0, fc w ((Y T q).2 w)) = _
    rw [hf]
    dsimp only [A]
    ring
  let E : ℝ → Q → ℝ := fun T q => ‖A q.1 * fc v0 (z T q)‖
  have hEmeas (T : ℝ) : AEStronglyMeasurable (E T) ρ :=
    ((hAmeas.comp measurable_fst).mul
      ((fc v0).continuous.measurable.comp (hzmeas T))).norm.aestronglyMeasurable
  have hbound (T : ℝ) (hT : 0 < T) :
      ∀ᵐ q ∂ρ, E T q ≤ (C0 / T ^ 2) * H q.1 := by
    filter_upwards [hp] with q hq
    have hh := hsup (z T q)
    rw [hznorm T hT q hq] at hh
    have hweighted : ‖fc v0 (z T q)‖ * T ^ 2 ≤ C0 * B q.1 ^ 2 := by
      calc
        _ = (‖fc v0 (z T q)‖ * (T / B q.1) ^ 2) * B q.1 ^ 2 := by
          field_simp [hq.ne']
          <;> ring
        _ ≤ C0 * B q.1 ^ 2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    have hd : ‖fc v0 (z T q)‖ ≤ C0 * B q.1 ^ 2 / T ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hT)).2 hweighted
    dsimp only [E]
    rw [norm_mul]
    calc
      _ ≤ ‖A q.1‖ * (C0 * B q.1 ^ 2 / T ^ 2) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = (C0 / T ^ 2) * H q.1 := by rw [hHval]; ring
  have hdom (T : ℝ) : Integrable (fun q : Q => (C0 / T ^ 2) * H q.1) ρ :=
    (hHi.comp_fst η).const_mul (C0 / T ^ 2)
  have hEi (T : ℝ) (hT : 0 < T) : Integrable (E T) ρ := by
    apply (hdom T).mono' (hEmeas T)
    filter_upwards [hbound T hT] with q hq
    simpa only [E, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hq
  have hHmean : (∫ q : Q, H q.1 ∂ρ) = ∫ p, H p ∂ν := by
    rw [integral_prod _ (hHi.comp_fst η)]
    simp [η, Measure.real, Real.volume_Ioc]
  have hHintegral : 0 ≤ ∫ p, H p ∂ν := integral_nonneg hHnonneg
  let C1 : ℝ := C0 * ∫ p, H p ∂ν
  have hC1 : 0 ≤ C1 := mul_nonneg hC0 hHintegral
  refine ⟨C1 + 1, by positivity, ?_⟩
  intro T hT
  have hactual : Integrable tensor (G.sheet T) :=
    tensor_sheet_integrable D S μ v0 G ff fc hffcont hffcompact T hT
  have hparam : Integrable
      (fun q : Q => (‖tensor (Theta.sheetPoint S v0 T q.1 q.2)‖ : ℂ)) ρ := by
    apply ((hEi T hT).ofReal).congr
    filter_upwards with q
    change (E T q : ℂ) = (‖tensor (Y T q)‖ : ℂ)
    rw [hpoint]
  have hsheet := G.sheetInt_eq T hT (fun y => (‖tensor y‖ : ℂ)) hactual.norm.ofReal
  change (∫ y, (‖tensor y‖ : ℂ) ∂G.sheet T) =
    ∫ p, ∫ θ, (‖tensor (Theta.sheetPoint S v0 T p θ)‖ : ℂ) ∂η ∂ν at hsheet
  rw [← integral_prod _ hparam] at hsheet
  have hparamEq : (∫ q : Q, (‖tensor (Theta.sheetPoint S v0 T q.1 q.2)‖ : ℂ) ∂ρ) =
      (((∫ q, E T q ∂ρ) : ℝ) : ℂ) := by
    calc
      _ = ∫ q, (E T q : ℂ) ∂ρ := by
        apply integral_congr_ae
        filter_upwards with q
        change (‖tensor (Y T q)‖ : ℂ) = (E T q : ℂ)
        rw [hpoint]
      _ = _ := integral_complex_ofReal
  rw [integral_complex_ofReal, hparamEq] at hsheet
  have hactualEq : (∫ y, ‖tensor y‖ ∂G.sheet T) = ∫ q, E T q ∂ρ :=
    Complex.ofReal_injective hsheet
  change (∫ y, ‖tensor y‖ ∂G.sheet T) ≤ (C1 + 1) / T ^ 2
  rw [hactualEq]
  calc
    _ ≤ ∫ q : Q, (C0 / T ^ 2) * H q.1 ∂ρ :=
      integral_mono_ae (hEi T hT) (hdom T) (hbound T hT)
    _ = C1 / T ^ 2 := by rw [integral_const_mul, hHmean]; dsimp only [C1]; ring
    _ ≤ (C1 + 1) / T ^ 2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg T)

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
