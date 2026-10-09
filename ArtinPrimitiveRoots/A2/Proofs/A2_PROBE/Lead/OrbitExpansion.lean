import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitEquiv
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.PeriodicPoisson
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitAbs
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitSheet
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

/-- The outer `W₁` cutoff has finite ideal support. -/
private theorem lead_W1_support_finite (Y : ℝ) (hY : 0 < Y) :
    (Function.support (fun s : S.ExtIdeal => W.W1 (qI s.1 / Y))).Finite := by
  have hcompact : IsCompact (tsupport W.W1) := W.W1_compact
  obtain ⟨B, hB⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcompact.isBounded
  let cutoff : ℝ := Y * max B 1
  have hcutoff : 0 ≤ cutoff := by
    dsimp [cutoff]
    positivity
  have hfinite := a2_bridge_COUNT_finite S cutoff hcutoff
  apply hfinite.1.subset
  intro I hI
  have hts : qI I.1 / Y ∈ tsupport W.W1 := by
    apply subset_closure
    exact Function.mem_support.mpr hI
  have hball := hB hts
  have hdist : dist (qI I.1 / Y) 0 ≤ B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball
  have hfrac : qI I.1 / Y ≤ max B 1 := by
    calc
      qI I.1 / Y ≤ |qI I.1 / Y| := le_abs_self _
      _ = dist (qI I.1 / Y) 0 := by
        simpa only [sub_zero] using (Real.dist_eq (qI I.1 / Y) 0).symm
      _ ≤ B := hdist
      _ ≤ max B 1 := le_max_left _ _
  have hq : qI I.1 ≤ cutoff := by
    dsimp [cutoff]
    calc
      qI I.1 ≤ max B 1 * Y := (div_le_iff₀ hY).mp hfrac
      _ = Y * max B 1 := by ring
  simpa [qI, idealNorm] using hq

/-- For a fixed row ideal, one finite set of lattice points serves all of `Ω₁`. -/
private theorem lead_rows_finite (X : ℝ) (s : S.ExtIdeal) :
    {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
      W.W0 (S.diag (m : F) *
        ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}.Finite := by
  classical
  have hdiagFinite (K : Set S.FS) (hK : IsCompact K) :
      (K ∩ S.diagR).Finite := by
    let Hring : Subring S.FS := (S.diag.comp S.R.val.toRingHom).range
    let H : AddSubgroup S.FS := Hring.toAddSubgroup
    have hH : (H : Set S.FS) = S.diagR := by
      change Set.range (fun x : S.R => S.diag (x : F)) = _
      rfl
    have hdiscrete : IsDiscrete (H : Set S.FS) := by
      simpa only [hH] using (S.diagR_discrete_cocompact D).1
    have hclosed : IsClosed (H : Set S.FS) := H.isClosed_of_isDiscrete hdiscrete
    have hcompact : IsCompact (K ∩ (H : Set S.FS)) := hK.inter_right hclosed
    have hdiscrete' : IsDiscrete (K ∩ (H : Set S.FS)) :=
      hdiscrete.mono Set.inter_subset_right
    have hfinite := hcompact.finite hdiscrete'
    simpa only [hH] using hfinite
  classical
  obtain ⟨K, hK, hOmega⟩ := R.sheets.omega_bounded
  let a0 : S.FSˣ := R.sheets.ellU 1
  let a1 : S.FSˣ := R.sheets.ellU (qI s.1 * X)
  let Kunit : Set S.FS := (fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K
  have hWcompact : IsCompact (tsupport W.W0) := W.W0_compact
  have hKunit : IsCompact Kunit := by
    change IsCompact ((fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K)
    exact hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  let Ktotal : Set S.FS :=
    (fun p : S.FS × S.FS => p.1 * p.2) '' (tsupport W.W0 ×ˢ Kunit)
  have hKtotal : IsCompact Ktotal := by
    change IsCompact ((fun p : S.FS × S.FS => p.1 * p.2) ''
      (tsupport W.W0 ×ˢ Kunit))
    exact (hWcompact.prod hKunit).image (continuous_fst.mul continuous_snd)
  have hfinite := hdiagFinite Ktotal hKtotal
  have hdiag : Function.Injective (fun m : S.R => S.diag (m : F)) := by
    intro m n hmn
    apply Subtype.ext
    apply v0.embedding.injective
    change (S.diag (m : F)).2 v0 = (S.diag (n : F)).2 v0
    exact congrArg (fun y : S.FS => y.2 v0) hmn
  apply Set.Finite.of_injOn (f := fun m : S.R => S.diag (m : F))
    (s := {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
      W.W0 (S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val) ≠ 0})
    (t := Ktotal ∩ S.diagR) ?_ ?_ hfinite
  · intro m hm
    obtain ⟨t, ht, hW⟩ := hm
    let y : S.FS :=
      S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val
    have hy : y ∈ tsupport W.W0 := by
      apply subset_closure
      exact Function.mem_support.mpr hW
    rcases ht with ⟨x, hx, htx⟩
    have hta : (t : S.FS) * (a1 : S.FS) ∈ Kunit := by
      refine ⟨x, hOmega hx, ?_⟩
      dsimp [Kunit]
      rw [htx]
    constructor
    · refine ⟨(y, (t : S.FS) * (a1 : S.FS)), ⟨hy, hta⟩, ?_⟩
      dsimp [y]
      simp [mul_assoc]
    · exact ⟨m, rfl⟩
  · intro m hm n hn hmn
    exact hdiag hmn

private theorem lead_W0_continuous : Continuous W.W0 := by
  have hEq : W.W0 = fun y : S.FS =>
      (∏ v : S.Sf, (W.finite v).1 (y.1 v)) *
        ∏ w : InfinitePlace F, W.arch w (y.2 w) := funext W.W0_tensor
  rw [hEq]
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    exact (W.finite v).2.1.comp ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    exact (W.arch w).continuous.comp ((continuous_apply w).comp continuous_snd)

private theorem lead_isGen_mul (I J : Ideal (𝓞 F)) (a b : Fˣ)
    (ha : S.IsGen (a : F) I) (hb : S.IsGen (b : F) J) :
    S.IsGen ((a * b : Fˣ) : F) (I * J) := by
  have hExt : S.IsExterior (I * J) := by
    constructor
    · exact mul_ne_zero ha.1.1 hb.1.1
    · intro v hvS hsub
      have hdiv := v.isPrime.mul_le.mp hsub
      rcases hdiv with hI | hJ
      · exact ha.1.2 v hvS hI
      · exact hb.1.2 v hvS hJ
  have hI0 : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using ha.1.1
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using hb.1.1
  have hcoe : ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.coeIdeal_mul I J
  refine ⟨hExt, mul_ne_zero a.ne_zero b.ne_zero, ?_⟩
  intro v hvS
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a : F) * (b : F))) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) :=
      FractionalIdeal.count_mul F v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr b.ne_zero)
    _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [ha.2.2 v hvS, hb.2.2 v hvS]
    _ = FractionalIdeal.count F v
        ((I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
          (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :=
      (FractionalIdeal.count_mul F v hI0 hJ0).symm
    _ = FractionalIdeal.count F v
        ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      exact congrArg (FractionalIdeal.count F v) hcoe.symm

private theorem lead_Agen_isGen (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    S.IsGen (Agen R c n : F) (Aideal R c n).1 := by
  have hc := (bc.gen_spec (R.exterior.ofSqf c)).1
  have hn := (bc.gen_spec n).1
  have hn2 : S.IsGen ((bc.gen n * bc.gen n : Fˣ) : F) (n.1 * n.1) :=
    lead_isGen_mul n.1 n.1 (bc.gen n) (bc.gen n) hn hn
  have hn3 : S.IsGen ((bc.gen n ^ 3 : Fˣ) : F) (n.1 ^ 3) := by
    have h := lead_isGen_mul (n.1 * n.1) n.1 (bc.gen n * bc.gen n) (bc.gen n) hn2 hn
    simpa [pow_succ, pow_two, mul_assoc] using h
  have h := lead_isGen_mul (R.exterior.ofSqf c).1 (n.1 ^ 3)
    (bc.gen (R.exterior.ofSqf c)) (bc.gen n ^ 3) hc hn3
  simpa [Agen, Aideal, R.exterior.mul_val, R.exterior.ofSqf_val,
    R.exterior.pow_val, mul_assoc] using h

private theorem lead_Agen_allowed (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    Bd.Allowed (Agen R c n) := by
  have hc := (bc.gen_spec (R.exterior.ofSqf c)).2
  have hn := (bc.gen_spec n).2
  change (QuotientGroup.mk (S.diagU (bc.gen (R.exterior.ofSqf c) * bc.gen n ^ 3)) : S.V) ∈ Bd.B
  rw [map_mul, map_pow, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  exact Bd.B.mul_mem hc (Bd.B.pow_mem hn 3)

private theorem lead_Aideal_val (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    (Aideal R c n).1 = c.1 * n.1 ^ 3 := by
  simp [Aideal, R.exterior.mul_val, R.exterior.ofSqf_val, R.exterior.pow_val]

private theorem lead_qI_pos (I : S.ExtIdeal) : 0 < qI I.1 := by
  have h0 : I.1 ≠ ⊥ := I.2.1
  unfold qI
  exact_mod_cast Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h))

/-- One summand of the original `Bm` series. -/
private def leadBmTerm (Z : ℝ) (p : S.SqfExtIdeal × S.ExtIdeal) (m : F) : ℂ :=
  gamma D S A 2 p.1.1 (cgen R p.1) *
    ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
    ϑ.idealValue (p.1.1 * p.2.1 ^ 3) * chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
    (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)

/-- The `m`-independent part of a `Bm` summand. -/
private def leadBmCoeff (Z : ℝ) (p : S.SqfExtIdeal × S.ExtIdeal) : ℂ :=
  gamma D S A 2 p.1.1 (cgen R p.1) * ((qI p.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.1 : ℝ) : ℂ) *
    ϑ.idealValue (Aideal R p.1 p.2).1 * (PG (qI (Aideal R p.1 p.2).1 / Z) : ℂ)

private theorem lead_Bm_eq (m : F) (Z : ℝ) :
    Bm D S A ϑ (cgen R) m Z = ∑' p, leadBmTerm R Z p m := rfl

private theorem lead_BmTerm_eq (Z : ℝ) (p : S.SqfExtIdeal × S.ExtIdeal) (m : F) :
    leadBmTerm R Z p m = leadBmCoeff R Z p * chiIdealPow D (Aideal R p.1 p.2).1 m 1 := by
  simp only [leadBmTerm, leadBmCoeff, lead_Aideal_val, qI, div_eq_mul_inv]
  ring

private theorem lead_BmTerm_summable (Z : ℝ) (hZ : 0 < Z) (m : F) :
    Summable (fun p => ‖leadBmTerm R Z p m‖) :=
  Bm_summable D S A H Bd ϑ R.vartheta_unitary (cgen R) (cgen_valid R) m Z hZ

/-- The lattice coefficient of one probe row. -/
private def leadRowCoeff (X : ℝ) (s : S.ExtIdeal) (m : S.R) (t : S.FSˣ) : ℂ :=
  (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
    W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val)

/-- The probe row of the ideal `s` against one `Bm` summand. -/
private def leadRow (X Z : ℝ) (s : S.ExtIdeal) (p : S.SqfExtIdeal × S.ExtIdeal)
    (t : S.FSˣ) : ℂ :=
  ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑' m : S.R, leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)

private theorem lead_rowCoeff_eq_zero (X : ℝ) (s : S.ExtIdeal) (m : S.R) (t : S.FSˣ)
    (ht : (t : S.FS) ∈ omegaAt R 1)
    (hm : m ∉ (lead_rows_finite R W X s).toFinset) : leadRowCoeff R W X s m t = 0 := by
  have hW : W.W0 (S.diag (m : F) *
      ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) = 0 := by
    by_contra h
    apply hm
    rw [Set.Finite.mem_toFinset]
    exact ⟨t, ht, h⟩
  simp only [leadRowCoeff, hW, mul_zero]

private theorem lead_row_finite (X Z : ℝ) (s : S.ExtIdeal) (p : S.SqfExtIdeal × S.ExtIdeal)
    (t : S.FSˣ) (ht : (t : S.FS) ∈ omegaAt R 1) :
    leadRow R W X Z s p t = ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
      ∑ m ∈ (lead_rows_finite R W X s).toFinset,
        leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F) := by
  unfold leadRow
  congr 1
  apply tsum_eq_sum
  intro m hm
  rw [lead_rowCoeff_eq_zero R W X s m t ht hm, zero_mul]

private theorem lead_row_norm_le (hfinite : LeadFiniteContract R) (X Z : ℝ) (hX : 0 < X)
    (s : S.ExtIdeal) (p : S.SqfExtIdeal × S.ExtIdeal) (B0 : ℝ) (hB0 : ∀ y, ‖W.W0 y‖ ≤ B0)
    (t : S.FSˣ) (ht : (t : S.FS) ∈ omegaAt R 1) :
    ‖leadRow R W X Z s p t‖ ≤ (qI s.1 * X) ^ (-(1 / 2 : ℝ)) *
      ∑ m ∈ (lead_rows_finite R W X s).toFinset,
        qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0 * ‖leadBmTerm R Z p (m : F)‖ := by
  have hq := lead_qI_pos s
  have hc : 0 ≤ (qI s.1 * X) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (mul_pos hq hX).le _
  have hc' : 0 ≤ qI s.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hq.le _
  rw [lead_row_finite R W X Z s p t ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => ?_)) hc
  have hG : ‖leadFiniteGauss R s (-(m : F))‖ ≤ qI s.1 := by
    simpa using hfinite.2 s (-m)
  simp only [leadRowCoeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc']
  have hb := norm_nonneg (leadBmTerm R Z p (m : F))
  have hw := hB0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val)
  have hg0 := norm_nonneg (leadFiniteGauss R s (-(m : F)))
  have hw0 := norm_nonneg (W.W0 (S.diag (m : F) *
    ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val))
  have h1 : qI s.1 ^ (-(1 / 2 : ℝ)) * ‖leadFiniteGauss R s (-(m : F))‖ ≤
      qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 := mul_le_mul_of_nonneg_left hG hc'
  have h2 := mul_le_mul h1 hw hw0 (mul_nonneg hc' hq.le)
  exact mul_le_mul_of_nonneg_right h2 hb

/-- Scaled periodic Poisson summation on one row, for a point of `Ω₁`. -/
private theorem lead_row_poisson (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (X Z : ℝ) (hX : 0 < X) (s : S.ExtIdeal)
    (p : S.SqfExtIdeal × S.ExtIdeal) (t : S.FSˣ) (ht : (t : S.FS) ∈ omegaAt R 1) :
    leadRow R W X Z s p t = leadBmCoeff R Z p *
      ((X ^ (1 / 2 : ℝ) / qI (Aideal R p.1 p.2).1 : ℝ) : ℂ) *
      ∑' h : S.R, leadFiniteFactor R s (Aideal R p.1 p.2) (Agen R p.1 p.2) (h : F) *
        leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
          S.diag ((h : F) / ((bc.gen s : F) * (Agen R p.1 p.2 : F)))) := by
  have hq := lead_qI_pos s
  have hqX : 0 < qI s.1 * X := mul_pos hq hX
  have hP := (periodic_poisson (R := R) (sd := sd) (W := W) hcoset hfinite s
    (Aideal R p.1 p.2) (Agen R p.1 p.2) (lead_Agen_isGen R p.1 p.2)
    (lead_Agen_allowed R p.1 p.2) (t * R.sheets.ellU (qI s.1 * X))).2.2
  have habs : S.absS (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ)) : S.FS) = qI s.1 * X := by
    have hSheet := a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) 1 one_pos
    have ht1 : S.absS (t : S.FS) = 1 := (hSheet.1.2.1 (t : S.FS) ht).2
    have hnormMul := (a2_bridge_NORM D S).2.1
    rw [Units.val_mul, hnormMul, ht1, R.sheets.ellU_norm _ hqX, one_mul]
  have hrow : (∑' m : S.R, leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)) =
      leadBmCoeff R Z p * ∑' m : S.R,
        (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
          chiIdealPow D (Aideal R p.1 p.2).1 (m : F) 1 *
            W.W0 (S.diag (m : F) *
              ((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ)⁻¹ : S.FSˣ).val) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [lead_BmTerm_eq]
    simp only [leadRowCoeff]
    ring
  have hreal : (qI s.1 * X) ^ (-(1 / 2 : ℝ)) *
      (S.absS (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ)) : S.FS) /
        (qI s.1 ^ (1 / 2 : ℝ) * qI (Aideal R p.1 p.2).1)) =
      X ^ (1 / 2 : ℝ) / qI (Aideal R p.1 p.2).1 := by
    rw [habs]
    have hQ := lead_qI_pos (Aideal R p.1 p.2)
    have hsq : 0 < qI s.1 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
    have hxq : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
    have hneg : (qI s.1 * X) ^ (-(1 / 2 : ℝ)) =
        (qI s.1 ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg hqX.le, Real.mul_rpow hq.le hX.le]
    have hsq2 : qI s.1 * X = (qI s.1 ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq.le,
        ← Real.rpow_mul hX.le]
      norm_num
    rw [hneg, hsq2]
    field_simp
  unfold leadRow
  rw [hrow, hP, ← hreal, Complex.ofReal_mul]
  ring

/-- Integrability and integral of one row over `Ω₁`, from the worker orbit-sheet part. -/
private theorem lead_row_integral (hspec : LeadWeightSpec R sd W)
    (hcoset : LeadCosetContract sd W) (hfinite : LeadFiniteContract R)
    (hsheets : LeadSheetsContract R sd W) (hequiv : LeadEquivContract (bc := bc) η U)
    (X Z : ℝ) (hX : 0 < X) (s : S.ExtIdeal) (p : S.SqfExtIdeal × S.ExtIdeal) :
    IntegrableOn (onUnits (leadRow R W X Z s p)) (omegaAt R 1) (R.sheets.sheet 1) ∧
    omegaInt R 1 (leadRow R W X Z s p) = leadBmCoeff R Z p *
      ((X ^ (1 / 2 : ℝ) / qI (Aideal R p.1 p.2).1 : ℝ) : ℂ) *
      ∑' ur : U.U × S.ExtIdeal,
        leadFiniteFactor R s (Aideal R p.1 p.2) (Agen R p.1 p.2)
            ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
          leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI (Aideal R p.1 p.2).1) := by
  have hO := orbit_sheet_sum (R := R) (sd := sd) (W := W) (η := η) (U := U) hspec.1 hcoset
    hfinite hsheets hequiv s (Aideal R p.1 p.2) (Agen R p.1 p.2)
    (lead_Agen_isGen R p.1 p.2) (lead_Agen_allowed R p.1 p.2) X hX
  have hSheet := a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) 1 one_pos
  have hmeas : MeasurableSet (omegaAt R 1) := hSheet.1.1
  have heq : Set.EqOn (onUnits (leadRow R W X Z s p))
      (fun y => (leadBmCoeff R Z p *
        ((X ^ (1 / 2 : ℝ) / qI (Aideal R p.1 p.2).1 : ℝ) : ℂ)) *
        onUnits (fun t : S.FSˣ =>
          ∑' h : S.R, leadFiniteFactor R s (Aideal R p.1 p.2) (Agen R p.1 p.2) (h : F) *
            leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
              S.diag ((h : F) / ((bc.gen s : F) * (Agen R p.1 p.2 : F))))) y)
      (omegaAt R 1) := by
    intro y hy
    have hunit : IsUnit y := (hSheet.1.2.1 y hy).1
    simp only [onUnits, dif_pos hunit]
    exact lead_row_poisson R sd W hcoset hfinite X Z hX s p hunit.unit (by simpa using hy)
  refine ⟨IntegrableOn.congr_fun (Integrable.const_mul hO.2.1 _) heq.symm hmeas, ?_⟩
  have h2 := hO.2.2
  unfold omegaInt at h2 ⊢
  rw [setIntegral_congr_fun hmeas heq, integral_const_mul, h2]

set_option maxHeartbeats 800000 in
/-- Pointwise expansion of the probe integrand into rows and `Bm` summands on `Ω₁`. -/
private theorem lead_integrand_expand (X Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (t : S.FSˣ)
    (ht : (t : S.FS) ∈ omegaAt R 1) :
    leadProbeIntegrand R W X Y Z t =
      ∑' p : S.SqfExtIdeal × S.ExtIdeal, ∑ s ∈ (lead_W1_support_finite W Y hY).toFinset,
        (Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y) * leadRow R W X Z s p t := by
  have hrowSumm (s : S.ExtIdeal) :
      Summable (fun p : S.SqfExtIdeal × S.ExtIdeal => leadRow R W X Z s p t) := by
    have hm (m : S.R) : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)) :=
      ((lead_BmTerm_summable R Z hZ (m : F)).of_norm).mul_left _
    have hf : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        ∑ m ∈ (lead_rows_finite R W X s).toFinset,
          leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)) :=
      summable_sum fun m _ => hm m
    have hs : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        (((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ m ∈ (lead_rows_finite R W X s).toFinset,
            leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)) := hf.mul_left _
    exact hs.congr fun p => (lead_row_finite R W X Z s p t ht).symm
  have hrow (s : S.ExtIdeal) :
      (((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : S.R, (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
          W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
            Bm D S A ϑ (cgen R) (m : F) Z =
      ∑' p, leadRow R W X Z s p t := by
    have hsum : ∀ m ∈ (lead_rows_finite R W X s).toFinset,
        Summable (fun p => leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F)) :=
      fun m _ => ((lead_BmTerm_summable R Z hZ (m : F)).of_norm).mul_left _
    have h1 : (∑' m : S.R, (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
          W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
            Bm D S A ϑ (cgen R) (m : F) Z) =
        ∑' p, ∑ m ∈ (lead_rows_finite R W X s).toFinset,
          leadRowCoeff R W X s m t * leadBmTerm R Z p (m : F) := by
      rw [Summable.tsum_finsetSum hsum]
      rw [tsum_eq_sum (s := (lead_rows_finite R W X s).toFinset)]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [lead_Bm_eq, ← tsum_mul_left]
        rfl
      · intro m hm
        have h0 := lead_rowCoeff_eq_zero R W X s m t ht hm
        simp only [leadRowCoeff] at h0
        rw [h0, zero_mul]
    rw [h1, ← tsum_mul_left]
    exact tsum_congr fun p => (lead_row_finite R W X Z s p t ht).symm
  unfold leadProbeIntegrand
  rw [tsum_eq_sum (s := (lead_W1_support_finite W Y hY).toFinset)]
  · rw [Summable.tsum_finsetSum fun s _ => (hrowSumm s).mul_left _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_assoc (W.W1 _), hrow s, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun p => by ring
  · intro s hs
    have hW : W.W1 (qI s.1 / Y) = 0 := by
      by_contra h
      apply hs
      rw [Set.Finite.mem_toFinset]
      exact h
    rw [hW, zero_mul, zero_mul]

private theorem lead_ideal_countable : Countable (Ideal (𝓞 F)) := by
  have hcover : (Set.univ : Set (Ideal (𝓞 F))) =
      ⋃ n : ℕ, {I | Ideal.absNorm I ≤ n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  have hcount : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [hcover]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOfPred_absNorm_le n).countable)
  exact Set.countable_univ_iff.mp hcount

set_option maxHeartbeats 800000 in
/-- LEAD: integrate the expanded Bm rows using the independent worker parts. -/
theorem orbit_expansion
    (hspec : LeadWeightSpec R sd W) (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    LeadExpansionContract R sd W η U := by
  have hequiv : LeadEquivContract (bc := bc) η U :=
    orbit_equiv (η := η) (U := U) hclass hratio
  intro X Y Z hX hY hZ
  have habs := orbit_abs_summable (R := R) (sd := sd) (W := W) (η := η) (U := U)
    hfinite hsheets hequiv X Y Z hX hY hZ
  refine ⟨habs, ?_⟩
  classical
  letI : Countable (Ideal (𝓞 F)) := lead_ideal_countable
  letI : Countable S.ExtIdeal :=
    Function.Injective.countable (f := fun I : S.ExtIdeal => I.1) Subtype.val_injective
  letI : Countable S.SqfExtIdeal :=
    Function.Injective.countable (f := fun I : S.SqfExtIdeal => I.1) Subtype.val_injective
  have hSheet := a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) 1 one_pos
  have hmeas : MeasurableSet (omegaAt R 1) := hSheet.1.1
  haveI : IsFiniteMeasure ((R.sheets.sheet 1).restrict (omegaAt R 1)) :=
    isFiniteMeasure_restrict.mpr hSheet.2.1.ne
  obtain ⟨B0, hB0⟩ := (lead_W0_continuous W).bounded_above_of_compact_support W.W0_compact
  have rowI (s : S.ExtIdeal) (p : S.SqfExtIdeal × S.ExtIdeal) :=
    lead_row_integral R sd W η U hspec hcoset hfinite hsheets hequiv X Z hX s p
  let SW := (lead_W1_support_finite W Y hY).toFinset
  let fp : S.SqfExtIdeal × S.ExtIdeal → S.FS → ℂ := fun p y =>
    ∑ s ∈ SW, (Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y) * onUnits (leadRow R W X Z s p) y
  have hint : ∀ p, Integrable (fp p) ((R.sheets.sheet 1).restrict (omegaAt R 1)) :=
    fun p => integrable_finsetSum SW fun s _ => Integrable.const_mul (rowI s p).1 _
  let g : S.SqfExtIdeal × S.ExtIdeal → ℝ := fun p =>
    ∑ s ∈ SW, ‖(Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y)‖ * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) *
      ∑ m ∈ (lead_rows_finite R W X s).toFinset,
        qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0 * ‖leadBmTerm R Z p (m : F)‖)
  have hgm (s : S.ExtIdeal) (m : S.R) :
      Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        (qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0) * ‖leadBmTerm R Z p (m : F)‖) :=
    (lead_BmTerm_summable R Z hZ (m : F)).mul_left _
  have hgs (s : S.ExtIdeal) :
      Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        ‖(Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y)‖ * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) *
          ∑ m ∈ (lead_rows_finite R W X s).toFinset,
            qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0 * ‖leadBmTerm R Z p (m : F)‖)) := by
    have hf : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        ∑ m ∈ (lead_rows_finite R W X s).toFinset,
          qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0 * ‖leadBmTerm R Z p (m : F)‖) :=
      summable_sum fun m _ => hgm s m
    have hs : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
        (qI s.1 * X) ^ (-(1 / 2 : ℝ)) *
          ∑ m ∈ (lead_rows_finite R W X s).toFinset,
            qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 * B0 * ‖leadBmTerm R Z p (m : F)‖) :=
      hf.mul_left _
    exact hs.mul_left _
  have hg : Summable g := summable_sum fun s _ => hgs s
  have hfpBound : ∀ p, ∀ y ∈ omegaAt R 1, ‖fp p y‖ ≤ g p := by
    intro p y hy
    have hunit : IsUnit y := (hSheet.1.2.1 y hy).1
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    simp only [onUnits, dif_pos hunit, norm_mul]
    rw [← norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lead_row_norm_le R W hfinite X Z hX s p B0 hB0 hunit.unit (by simpa using hy))
      (norm_nonneg _)
  have hnorm : Summable (fun p =>
      ∫ y, ‖fp p y‖ ∂((R.sheets.sheet 1).restrict (omegaAt R 1))) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun y => norm_nonneg _)
      (fun p => ?_)
      (hg.mul_right (((R.sheets.sheet 1).restrict (omegaAt R 1)).real Set.univ))
    have h := norm_integral_le_of_norm_le_const
      (μ := (R.sheets.sheet 1).restrict (omegaAt R 1)) (f := fun y => ‖fp p y‖) (C := g p)
      (ae_restrict_of_forall_mem hmeas fun y hy => by
        simpa only [norm_norm] using hfpBound p y hy)
    exact (Real.le_norm_self _).trans h
  have hEqOn : Set.EqOn (onUnits (leadProbeIntegrand R W X Y Z))
      (fun y => ∑' p, fp p y) (omegaAt R 1) := by
    intro y hy
    have hunit : IsUnit y := (hSheet.1.2.1 y hy).1
    simp only [fp, SW, onUnits, dif_pos hunit]
    exact lead_integrand_expand R W X Y Z hY hZ hunit.unit (by simpa using hy)
  have hfpInt : ∀ p, ∫ y, fp p y ∂((R.sheets.sheet 1).restrict (omegaAt R 1)) =
      ∑ s ∈ SW, (Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y) * omegaInt R 1 (leadRow R W X Z s p) := by
    intro p
    simp only [fp]
    rw [integral_finsetSum _ fun s _ => Integrable.const_mul (rowI s p).1 _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_const_mul]
    rfl
  have hLHS : leadProbe R W X Y Z =
      ∑' p, ∑ s ∈ SW, (Y : ℂ)⁻¹ * W.W1 (qI s.1 / Y) * omegaInt R 1 (leadRow R W X Z s p) :=
    calc
      leadProbe R W X Y Z = ∫ y in omegaAt R 1, (∑' p, fp p y) ∂(R.sheets.sheet 1) :=
        setIntegral_congr_fun hmeas hEqOn
      _ = ∑' p, ∫ y in omegaAt R 1, fp p y ∂(R.sheets.sheet 1) :=
        (integral_tsum_of_summable_integral_norm hint hnorm).symm
      _ = _ := tsum_congr hfpInt
  have hs5 : Summable (leadOrbitTerm R sd W η U X Y Z) := habs.of_norm
  let e := Equiv.prodAssoc S.SqfExtIdeal S.ExtIdeal (S.ExtIdeal × (U.U × S.ExtIdeal))
  have hs' : Summable (fun q => leadOrbitTerm R sd W η U X Y Z (e q)) :=
    e.summable_iff.mpr hs5
  have hRHS : ∑' q, leadOrbitTerm R sd W η U X Y Z q =
      ∑' p : S.SqfExtIdeal × S.ExtIdeal, ∑ s ∈ SW,
        ∑' ur : U.U × S.ExtIdeal,
          leadOrbitTerm R sd W η U X Y Z (p.1, p.2, s, ur.1, ur.2) := by
    rw [← e.tsum_eq, hs'.tsum_prod]
    refine tsum_congr fun p => ?_
    rw [(hs'.prod_factor p).tsum_prod, tsum_eq_sum (s := SW)]
    · rfl
    · intro s hs
      have hW : W.W1 (qI s.1 / Y) = 0 := by
        by_contra h
        apply hs
        simp only [SW]
        rw [Set.Finite.mem_toFinset]
        exact h
      refine (tsum_congr fun ur => ?_).trans tsum_zero
      show leadOrbitTerm R sd W η U X Y Z (p.1, p.2, s, ur.1, ur.2) = 0
      simp only [leadOrbitTerm, hW, mul_zero, zero_mul]
  rw [hLHS, hRHS, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [(rowI s p).2]
  have hterm : ∀ ur : U.U × S.ExtIdeal,
      leadOrbitTerm R sd W η U X Y Z (p.1, p.2, s, ur.1, ur.2) =
        (gamma D S A 2 p.1.1 (cgen R p.1) * ϑ.idealValue (Aideal R p.1 p.2).1 *
          ((qI p.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.1 / qI (Aideal R p.1 p.2).1 : ℝ) : ℂ) *
          (PG (qI (Aideal R p.1 p.2).1 / Z) : ℂ) * W.W1 (qI s.1 / Y)) *
        (leadFiniteFactor R s (Aideal R p.1 p.2) (Agen R p.1 p.2)
            ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
          leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI (Aideal R p.1 p.2).1)) := by
    intro ur
    simp only [leadOrbitTerm]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  simp only [leadBmCoeff, Complex.ofReal_div]
  ring

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
