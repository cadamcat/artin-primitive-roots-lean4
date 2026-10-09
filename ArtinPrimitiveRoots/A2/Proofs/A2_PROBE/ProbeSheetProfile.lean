import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.LocalRadialIntegral
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.SchwartzRadial
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
import ArtinPrimitiveRoots.Theta.AnalysisS

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

set_option maxHeartbeats 2000000 in
/-- Positive sheet profiles of compact finite factors and complex Schwartz factors
are smooth, using weighted moments rather than local vanishing at zero. -/
theorem probe_sheet_profile_smooth
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (ff : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fc : InfinitePlace F → SchwartzMap ℂ ℂ)
    (hffcont : ∀ v, Continuous (ff v))
    (hffcompact : ∀ v, HasCompactSupport (ff v)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Theta.sheetInt S μ v0 (fun y : S.FS =>
        (∏ v : S.Sf, ff v (y.1 v)) * ∏ w : InfinitePlace F, fc w (y.2 w)))
      (Set.Ioi 0) := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  let Hf : ℝ → ℂ := Theta.sheetInt S μ v0 (fun y : S.FS =>
    (∏ v : S.Sf, ff v (y.1 v)) * ∏ w : InfinitePlace F, fc w (y.2 w))
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
  let z0 : Q → ℂ := fun q =>
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (1 / B q.1, q.2)
  let z : ℝ → Q → ℂ := fun t q => (Real.exp (t / 2) : ℂ) * z0 q
  let Y : ℝ → Q → S.FS := fun t q => Theta.sheetPoint S v0 (Real.exp t) q.1 q.2
  have hz0meas : Measurable z0 :=
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_polar_measurePreserving.measurable.comp
      ((measurable_const.div (hB.comp measurable_fst)).prodMk measurable_snd)
  have hzmeas (t : ℝ) : Measurable (z t) := measurable_const.mul hz0meas
  have hamp (t b : ℝ) : Real.sqrt (Real.exp t / b) =
      Real.exp (t / 2) * Real.sqrt (1 / b) := by
    have hexp : Real.exp t = Real.exp (t / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hs : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [hexp, Real.sqrt_sq (Real.exp_pos _).le]
    rw [div_eq_mul_inv, Real.sqrt_mul (Real.exp_pos t).le, hs, one_div]
  have hYdep (t : ℝ) (q : Q) : (Y t q).2 v0 = z t q := by
    simp only [Y, Theta.sheetPoint, z, z0,
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
    change (Real.sqrt (Real.exp t / B q.1) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * q.2) =
      (Real.exp (t / 2) : ℂ) * ((Real.sqrt (1 / B q.1) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * q.2))
    rw [hamp]
    push_cast
    ring
  have hz0norm (q : Q) (hq : 0 < B q.1) : Complex.normSq (z0 q) = 1 / B q.1 := by
    unfold z0 ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (q.2 : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (one_div_pos.mpr hq).le]
  have hz0ne (q : Q) (hq : 0 < B q.1) : z0 q ≠ 0 := by
    apply Complex.normSq_pos.mp
    rw [hz0norm q hq]
    exact one_div_pos.mpr hq
  have hznorm (t : ℝ) (q : Q) (hq : 0 < B q.1) :
      Complex.normSq (z t q) = Real.exp t / B q.1 := by
    dsimp only [z]
    rw [map_mul, hz0norm q hq]
    simp only [Complex.normSq_ofReal]
    rw [← Real.exp_add]
    have he : t / 2 + t / 2 = t := by ring
    rw [he]
    ring
  have hfree (g : InfinitePlace F → ℂ → ℂ) (u : ℝ) (p : P) (θ : ℝ) :
      (∏ w ∈ Finset.univ.erase v0, g w ((Theta.sheetPoint S v0 u p θ).2 w)) =
        ∏ w : W, g w.1 (p.2 w) := by
    rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w ≠ v0)
      (Finset.univ.erase v0) (by simp [ne_comm])]
    apply Finset.prod_congr rfl
    intro w hw
    simp only [Theta.sheetPoint, dite_eq_right w.property]
  let A : P → ℂ := fun p =>
    (∏ v : S.Sf, ff v (p.1 v)) * ∏ w : W, fc w.1 (p.2 w)
  let G : P → ℝ := fun p =>
    (∏ v : S.Sf, ‖ff v (p.1 v)‖ * absFin v.1 (p.1 v)) *
      ∏ w : W, ‖fc w.1 (p.2 w)‖ * Complex.normSq (p.2 w)
  have hAmeas : Measurable A := by
    apply Measurable.mul
    · exact Finset.measurable_fun_prod Finset.univ fun v hv =>
        (hffcont v).measurable.comp ((measurable_pi_apply v).comp measurable_fst)
    · exact Finset.measurable_fun_prod Finset.univ fun w hw =>
        ((fc w.1).smooth ⊤).continuous.measurable.comp
          ((measurable_pi_apply w).comp measurable_snd)
  have hGval (p : P) : G p = ‖A p‖ * B p := by
    simp only [G, A, B, norm_mul, norm_prod, Finset.prod_mul_distrib]
    ring
  have hGi : Integrable G ν := by
    have hfI (v : S.Sf) : Integrable
        (fun x => ‖ff v x‖ * absFin v.1 x) (Theta.mulHaarFin (μ v.1)) := by
      simpa only [Real.rpow_one] using
        ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
          v.1 (μ v.1) (ff v) (hffcont v) (hffcompact v) 1 (by norm_num)
    have hcI (w : W) : Integrable
        (fun x : ℂ => ‖fc w.1 x‖ * Complex.normSq x) Theta.mulHaarC := by
      simpa only [Real.rpow_one] using
        ArtinPrimitiveRoots.Proofs.a2_weights.complexSchwartz_weighted_integrable
          (fc w.1) 1 (by norm_num)
    exact (Integrable.fintype_prod_dep hfI).mul_prod (Integrable.fintype_prod hcI)
  choose gj hgj using fun j : ℕ => normDeriv_schwartz (fc v0) j
  have hcmeas (j : ℕ) : Measurable (normDeriv j (fc v0)) := by
    have heq : normDeriv j (fc v0) = fun z => gj j z := funext (hgj j)
    rw [heq]
    exact ((gj j).smooth ⊤).continuous.measurable
  let C : ℕ → ℝ := fun j => (SchwartzMap.seminorm ℂ 2 0) (gj j)
  have hjet (j : ℕ) (y : ℂ) : ‖normDeriv j (fc v0) y‖ * Complex.normSq y ≤ C j := by
    rw [hgj j, Complex.normSq_eq_norm_sq, mul_comm]
    simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ 2 0 (gj j) y
  let E (j : ℕ) (t : ℝ) (q : Q) : ℂ := A q.1 * normDeriv j (fc v0) (z t q)
  have hEmeas (j : ℕ) (t : ℝ) : AEStronglyMeasurable (E j t) ρ :=
    ((hAmeas.comp measurable_fst).mul ((hcmeas j).comp (hzmeas t))).aestronglyMeasurable
  have hEder (j : ℕ) : ∀ᵐ q ∂ρ, ∀ t,
      HasDerivAt (fun s : ℝ => E j s q) (E (j + 1) t q) t := by
    filter_upwards [hp] with q hq
    intro t
    exact (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_normDeriv_hasDerivAt
      (fc v0) ((fc v0).smooth ⊤).contDiffOn j (z0 q) (hz0ne q hq) t).const_mul (A q.1)
  have hEbound (j : ℕ) (a b : ℝ) (hab : a ≤ b) :
      ∃ g : Q → ℝ, Integrable g ρ ∧
        ∀ᵐ q ∂ρ, ∀ t ∈ Set.Icc a b, ‖E j t q‖ ≤ g q := by
    refine ⟨fun q => (C j / Real.exp a) * G q.1,
      (hGi.comp_fst η).const_mul (C j / Real.exp a), ?_⟩
    filter_upwards [hp] with q hq
    intro t ht
    have hjet' : ‖normDeriv j (fc v0) (z t q)‖ * Real.exp t ≤ C j * B q.1 := by
      have h := hjet j (z t q)
      rw [hznorm t q hq] at h
      have hm := mul_le_mul_of_nonneg_right h hq.le
      field_simp at hm
      simpa only [mul_assoc, mul_comm] using hm
    have hjetA : ‖normDeriv j (fc v0) (z t q)‖ * Real.exp a ≤ C j * B q.1 := by
      calc
        _ ≤ ‖normDeriv j (fc v0) (z t q)‖ * Real.exp t :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.1) (norm_nonneg _)
        _ ≤ _ := hjet'
    have hd : ‖normDeriv j (fc v0) (z t q)‖ ≤ C j * B q.1 / Real.exp a :=
      (le_div_iff₀ (Real.exp_pos a)).mpr hjetA
    dsimp only [E]
    rw [norm_mul]
    calc
      _ ≤ ‖A q.1‖ * (C j * B q.1 / Real.exp a) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = (C j / Real.exp a) * G q.1 := by rw [hGval]; ring
  obtain ⟨hEi, hEsmooth, _⟩ := local_radial_integral_smooth ρ E hEmeas hEder hEbound
  have hEzero (t : ℝ) (q : Q) : E 0 t q =
      (∏ v : S.Sf, ff v ((Y t q).1 v)) * ∏ w : InfinitePlace F, fc w ((Y t q).2 w) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun w => fc w ((Y t q).2 w))
      (Finset.mem_univ v0)]
    rw [hYdep]
    have hf := hfree (fun w y => fc w y) (Real.exp t) q.1 q.2
    change E 0 t q = (∏ v : S.Sf, ff v (q.1.1 v)) *
      (fc v0 (z t q) * ∏ w ∈ Finset.univ.erase v0, fc w ((Y t q).2 w))
    rw [hf]
    simp only [E, A, normDeriv, iteratedDeriv_zero, zero_div, Real.exp_zero,
      Complex.ofReal_one, one_mul]
    ring
  have hH (t : ℝ) : Hf (Real.exp t) = ∫ q, E 0 t q ∂ρ := by
    have hi : Integrable (fun q =>
        (∏ v : S.Sf, ff v ((Y t q).1 v)) * ∏ w : InfinitePlace F, fc w ((Y t q).2 w)) ρ :=
      (hEi 0 t).congr (Eventually.of_forall (hEzero t))
    change (∫ p, ∫ θ,
      (∏ v : S.Sf, ff v ((Theta.sheetPoint S v0 (Real.exp t) p θ).1 v)) *
        ∏ w : InfinitePlace F, fc w ((Theta.sheetPoint S v0 (Real.exp t) p θ).2 w) ∂η ∂ν) = _
    rw [← integral_prod _ hi]
    exact integral_congr_ae (Eventually.of_forall fun q => (hEzero t q).symm)
  have hHfun : (fun t : ℝ => Hf (Real.exp t)) = fun t : ℝ => ∫ q, E 0 t q ∂ρ := funext hH
  have hHs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => Hf (Real.exp t)) := by
    rw [hHfun]
    exact hEsmooth
  have hlog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono fun u hu => by simpa using hu.ne'
  have hc := hHs.comp_contDiffOn hlog
  apply hc.congr
  intro u hu
  exact congrArg Hf (Real.exp_log hu).symm

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
