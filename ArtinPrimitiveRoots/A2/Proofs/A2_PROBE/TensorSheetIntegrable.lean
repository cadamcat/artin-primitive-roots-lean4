import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.SheetFinite
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

set_option maxHeartbeats 2000000 in
/-- Compact finite tensors and complex Schwartz tensors are integrable on every
positive norm sheet, by a transported radial majorant. -/
theorem tensor_sheet_integrable
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (G : A2.SheetGeometry D S μ v0)
    (ff : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fc : InfinitePlace F → SchwartzMap ℂ ℂ)
    (hffcont : ∀ v, Continuous (ff v))
    (hffcompact : ∀ v, HasCompactSupport (ff v)) :
    ∀ T : ℝ, 0 < T → Integrable
      (fun y : S.FS => (∏ v : S.Sf, ff v (y.1 v)) *
        ∏ w : InfinitePlace F, fc w (y.2 w)) (G.sheet T) := by
  have hfin (v : S.Sf) : ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖ff v x‖ * absFin v.1 x ≤ C * bridgeFinMajorant v.1 1 N x := by
    obtain ⟨B, hB⟩ := (hffcompact v).isCompact.isBounded.exists_norm_le
    have hq : 1 < (Ideal.absNorm v.1.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    obtain ⟨N0, _, hN0⟩ := exists_nat_pow_near (le_max_left 1 B) hq
    let N := N0 + 1
    have hN : B < (Ideal.absNorm v.1.asIdeal : ℝ) ^ N :=
      (le_max_right 1 B).trans_lt hN0
    obtain ⟨C, hC⟩ := (hffcompact v).exists_bound_of_continuous (hffcont v)
    refine ⟨N, max 0 C, le_max_left _ _, ?_⟩
    intro x
    by_cases hx : absFin v.1 x ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ N
    · simp only [bridgeFinMajorant, if_pos hx, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right ((hC x).trans (le_max_right _ _))
        (by rw [Theta.absFin_eq_norm]; exact norm_nonneg _)
    · have hzero : ff v x = 0 := by
        by_contra hne
        have hmem : x ∈ tsupport (ff v) := subset_closure (Function.mem_support.mpr hne)
        have hnorm := (hB x hmem).trans hN.le
        exact hx (by simpa only [Theta.absFin_eq_norm] using hnorm)
      simp [hzero, bridgeFinMajorant, hx]
  choose N Cf hCf hfinBound using hfin
  have harch (w : InfinitePlace F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖fc w z‖ * Complex.normSq z ≤ C * bridgeComplexMajorant 1 z := by
    let s0 : ℝ := SchwartzMap.seminorm ℂ 0 0 (fc w)
    let s8 : ℝ := SchwartzMap.seminorm ℂ 8 0 (fc w)
    have hs0 : 0 ≤ s0 := apply_nonneg _ _
    have hs8 : 0 ≤ s8 := apply_nonneg _ _
    let C : ℝ := 16 * (s0 + s8)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C, hC, ?_⟩
    intro z
    by_cases hz : z = 0
    · simp [hz, bridgeComplexMajorant]
    let q : ℝ := Complex.normSq z
    have hq : 0 ≤ q := Complex.normSq_nonneg z
    have hden : 0 < (1 + q) ^ 4 := by positivity
    have hbase : ‖fc w z‖ * (1 + q) ^ 4 ≤ C := by
      by_cases hsmall : q ≤ 1
      · have hpow : (1 + q) ^ 4 ≤ 16 := by
          calc
            (1 + q) ^ 4 ≤ (2 : ℝ) ^ 4 :=
              pow_le_pow_left₀ (by positivity) (by linarith) 4
            _ = 16 := by norm_num
        have hnorm : ‖fc w z‖ ≤ s0 := SchwartzMap.norm_le_seminorm ℂ (fc w) z
        calc
          ‖fc w z‖ * (1 + q) ^ 4 ≤ s0 * 16 := mul_le_mul hnorm hpow (by positivity) hs0
          _ ≤ C := by dsimp [C]; nlinarith
      · have hlarge : 1 ≤ q := le_of_not_ge hsmall
        have hpow : (1 + q) ^ 4 ≤ 16 * q ^ 4 := by
          calc
            (1 + q) ^ 4 ≤ (2 * q) ^ 4 :=
              pow_le_pow_left₀ (by positivity) (by linarith) 4
            _ = 16 * q ^ 4 := by ring
        have hnorm : q ^ 4 * ‖fc w z‖ ≤ s8 := by
          have hh := SchwartzMap.norm_pow_mul_le_seminorm ℂ (fc w) 8 z
          convert hh using 1
          dsimp [q]
          rw [Complex.normSq_eq_norm_sq]
          ring
        calc
          ‖fc w z‖ * (1 + q) ^ 4 ≤ ‖fc w z‖ * (16 * q ^ 4) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ = 16 * (q ^ 4 * ‖fc w z‖) := by ring
          _ ≤ 16 * s8 := mul_le_mul_of_nonneg_left hnorm (by norm_num)
          _ ≤ C := by dsimp [C]; nlinarith
    have hquot : ‖fc w z‖ ≤ C / (1 + q) ^ 4 := (le_div_iff₀ hden).2 hbase
    calc
      ‖fc w z‖ * Complex.normSq z ≤ (C / (1 + q) ^ 4) * q :=
        mul_le_mul_of_nonneg_right hquot hq
      _ = C * bridgeComplexMajorant 1 z := by
        norm_num [bridgeComplexMajorant, hz, q, Real.rpow_natCast]
        ring
  choose Cc hCc harchBound using harch
  let M : S.FS → ℝ := bridgeSheetGlobalMajorant (S := S) 1 N
  have hMnonneg (y : S.FS) : 0 ≤ M y := bridgeSheetGlobalMajorant_nonneg 1 N y
  have hMmeas : Measurable M := by
    apply Measurable.mul
    · exact Finset.univ.measurable_fun_prod fun v hv =>
        (bridgeFinMajorant_measurable v.1 1 (N v)).comp
          ((measurable_pi_apply v).comp measurable_fst)
    · exact Finset.univ.measurable_fun_prod fun w hw =>
        (bridgeComplexMajorant_measurable 1).comp
          ((measurable_pi_apply w).comp measurable_snd)
  let f : S.FS → ℂ := fun y => (∏ v : S.Sf, ff v (y.1 v)) *
    ∏ w : InfinitePlace F, fc w (y.2 w)
  have hfcont : Continuous f := by
    apply Continuous.mul
    · exact continuous_finsetProd _ fun v hv =>
        (hffcont v).comp ((continuous_apply v).comp continuous_fst)
    · exact continuous_finsetProd _ fun w hw =>
        (fc w).continuous.comp ((continuous_apply w).comp continuous_snd)
  let C : ℝ := (∏ v : S.Sf, Cf v) * ∏ w : InfinitePlace F, Cc w
  have hC : 0 ≤ C := mul_nonneg (Finset.prod_nonneg fun v hv => hCf v)
    (Finset.prod_nonneg fun w hw => hCc w)
  have hbound (y : S.FS) : ‖f y‖ * S.absS y ≤ C * M y := by
    have hfprod : (∏ v : S.Sf, ‖ff v (y.1 v)‖ * absFin v.1 (y.1 v)) ≤
        (∏ v : S.Sf, Cf v * bridgeFinMajorant v.1 1 (N v) (y.1 v)) := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact mul_nonneg (norm_nonneg _)
          (by rw [Theta.absFin_eq_norm]; exact norm_nonneg _)
      · intro v hv
        exact hfinBound v (y.1 v)
    have hcprod : (∏ w : InfinitePlace F, ‖fc w (y.2 w)‖ * Complex.normSq (y.2 w)) ≤
        (∏ w : InfinitePlace F, Cc w * bridgeComplexMajorant 1 (y.2 w)) := by
      apply Finset.prod_le_prod₀
      · intro w hw
        exact mul_nonneg (norm_nonneg _) (Complex.normSq_nonneg _)
      · intro w hw
        exact harchBound w (y.2 w)
    have hh := mul_le_mul hfprod hcprod
      (Finset.prod_nonneg fun w hw => mul_nonneg (norm_nonneg _) (Complex.normSq_nonneg _))
      (Finset.prod_nonneg fun v hv => mul_nonneg (hCf v) (bridgeFinMajorant_nonneg _ _ _ _))
    simpa only [f, C, M, bridgeSheetGlobalMajorant, SData.absS, norm_mul,
      norm_prod, Finset.prod_mul_distrib, mul_mul_mul_comm] using hh
  obtain ⟨t0, ht0, hInt0⟩ := bridgeSheetGlobalMajorant_exists_sheet G 1 one_pos N
  intro T hT
  let a : S.FSˣ := G.ellU (t0 / T)
  have hratio : 0 < t0 / T := div_pos ht0 hT
  have hanorm : S.absS (a : S.FS) * T = t0 := by
    rw [G.ellU_norm _ hratio]
    exact div_mul_cancel₀ t0 hT.ne'
  have hafin (v : S.Sf) : (a : S.FS).1 v = 1 := by
    rw [G.ellU_val _ hratio]
    rfl
  have hleftmeas (b : S.FS) : Measurable (fun y : S.FS => b * y) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro v
      exact measurable_const.mul ((measurable_pi_apply v).comp measurable_fst)
    · apply measurable_pi_iff.mpr
      intro w
      exact measurable_const.mul ((measurable_pi_apply w).comp measurable_snd)
  let e : S.FS ≃ᵐ S.FS := {
    toEquiv := {
      toFun := fun y => (a : S.FS) * y
      invFun := fun y => ((a⁻¹ : S.FSˣ) : S.FS) * y
      left_inv := by intro y; simp [mul_assoc]
      right_inv := by intro y; simp [mul_assoc] }
    measurable_toFun := hleftmeas (a : S.FS)
    measurable_invFun := hleftmeas ((a⁻¹ : S.FSˣ) : S.FS) }
  have hmp : MeasurePreserving e (G.sheet T) (G.sheet t0) := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map (fun y : S.FS => (a : S.FS) * y) (G.sheet T) = G.sheet t0
    rw [G.sheet_translate a T hT, hanorm]
  have htranslated : Integrable (fun y : S.FS => M ((a : S.FS) * y)) (G.sheet T) :=
    (hmp.integrable_comp_emb e.measurableEmbedding).2 hInt0
  have hinvnonzero (w : InfinitePlace F) : ((a⁻¹ : S.FSˣ) : S.FS).2 w ≠ 0 := by
    have hh := congrArg (fun y : S.FS => y.2 w) (Units.inv_mul a)
    change ((a⁻¹ : S.FSˣ) : S.FS).2 w * (a : S.FS).2 w = 1 at hh
    exact left_ne_zero_of_mul_eq_one hh
  have hscale (w : InfinitePlace F) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z,
      bridgeComplexMajorant 1 z ≤ K * bridgeComplexMajorant 1 ((a : S.FS).2 w * z) := by
    obtain ⟨K, hK, hh⟩ := bridgeComplexMajorant_scale 1 one_pos
      (((a⁻¹ : S.FSˣ) : S.FS).2 w) (hinvnonzero w)
    refine ⟨K, hK, ?_⟩
    intro z
    have hz := hh ((a : S.FS).2 w * z)
    have hinv := congrArg (fun y : S.FS => y.2 w) (Units.inv_mul a)
    change ((a⁻¹ : S.FSˣ) : S.FS).2 w * (a : S.FS).2 w = 1 at hinv
    simpa only [← mul_assoc, hinv, one_mul] using hz
  choose K hK hscaleBound using hscale
  let K0 : ℝ := ∏ w : InfinitePlace F, K w
  have hK0 : 0 ≤ K0 := Finset.prod_nonneg fun w hw => hK w
  have hMscale (y : S.FS) : M y ≤ K0 * M ((a : S.FS) * y) := by
    have hh : (∏ w : InfinitePlace F, bridgeComplexMajorant 1 (y.2 w)) ≤
        ∏ w : InfinitePlace F, K w * bridgeComplexMajorant 1 ((a : S.FS).2 w * y.2 w) := by
      exact Finset.prod_le_prod₀ (fun w hw => bridgeComplexMajorant_nonneg 1 _)
        (fun w hw => hscaleBound w _)
    have hfnonneg : 0 ≤ ∏ v : S.Sf, bridgeFinMajorant v.1 1 (N v) (y.1 v) :=
      Finset.prod_nonneg fun v hv => bridgeFinMajorant_nonneg _ _ _ _
    have hh' := mul_le_mul_of_nonneg_left hh hfnonneg
    simpa only [M, bridgeSheetGlobalMajorant, K0, Finset.prod_mul_distrib,
      Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, hafin, one_mul, mul_left_comm] using hh'
  have hMint : Integrable M (G.sheet T) := by
    apply (htranslated.const_mul K0).mono' hMmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hMnonneg y)]
      exact hMscale y
  apply (hMint.const_mul (C / T)).mono' hfcont.aestronglyMeasurable
  filter_upwards [G.sheet_support T hT] with y hy
  have hh := hbound y
  rw [hy.2] at hh
  calc
    ‖f y‖ ≤ (C * M y) / T := (le_div_iff₀ hT).2 hh
    _ = (C / T) * M y := by ring

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
