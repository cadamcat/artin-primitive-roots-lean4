import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
set_option maxHeartbeats 800000
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

private def prD_frequencyShell (k : ℕ) : Set U.U :=
  {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧ U.q u < ((2 ^ (k + 1) : ℕ) : ℝ)}

private theorem prD_frequencyShell_partition :
    ∀ u : U.U, ∃! k : ℕ, u ∈ prD_frequencyShell η U k := by
  intro u
  have hq := U.q_ge_one u
  let n : ℕ := Nat.floor (U.q u)
  have hn : n ≠ 0 := by
    intro hn
    have hfloorLt : U.q u < (n + 1 : ℕ) := by
      exact_mod_cast (Nat.lt_floor_add_one (U.q u))
    rw [hn] at hfloorLt
    norm_num at hfloorLt
    linarith [hq]
  let k : ℕ := Nat.log 2 n
  have hloNat : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn
  have hhiNat : n < 2 ^ (k + 1) := by
    simpa [k, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hlo : ((2 ^ k : ℕ) : ℝ) ≤ U.q u := by
    calc
      _ ≤ (n : ℝ) := by exact_mod_cast hloNat
      _ ≤ U.q u := Nat.floor_le (by linarith)
  have hfloorLt : U.q u < (n + 1 : ℕ) := by
    exact_mod_cast (Nat.lt_floor_add_one (U.q u))
  have hsuccNat : n + 1 ≤ 2 ^ (k + 1) := Nat.succ_le_iff.mpr hhiNat
  have hhi : U.q u < ((2 ^ (k + 1) : ℕ) : ℝ) :=
    hfloorLt.trans_le (by exact_mod_cast hsuccNat)
  refine ⟨k, ⟨hlo, hhi⟩, ?_⟩
  intro j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hjk)
    have hpowR : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast hpow
    linarith [hj.2, hlo]
  · have hpow : 2 ^ (k + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hkj)
    have hpowR : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
      exact_mod_cast hpow
    linarith [hj.1, hhi]

private theorem prD_frequency_q_inv_sq_summable :
    Summable (fun u : U.U => U.q u ^ (-2 : ℝ)) := by
  classical
  obtain ⟨Cdyad, hCdyad, hdyad⟩ := U.dyadic_count
  obtain ⟨Clow, hClow, hlowFinite, hlowBound⟩ := U.low_shell_bound
  let C : ℝ := max Cdyad Clow
  have hC : 0 < C := lt_of_lt_of_le hCdyad (le_max_left _ _)
  have hShellFinite (k : ℕ) : (prD_frequencyShell η U k).Finite := by
    by_cases hk : k = 0
    · subst k
      apply hlowFinite.subset
      intro u hu
      constructor
      · simpa using hu.1
      · exact lt_trans hu.2 (by norm_num)
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast this
      obtain ⟨hfin, _⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      refine hfin.subset ?_
      intro u hu
      exact ⟨hu.1, hu.2.trans_eq (by
        rw [pow_succ]
        push_cast
        ring)⟩
  have hCount (k : ℕ) :
      (prD_frequencyShell η U k).ncard ≤ C * ((2 ^ k : ℕ) : ℝ) := by
    by_cases hk : k = 0
    · subst k
      have hsub : prD_frequencyShell η U 0 ⊆
          {u | 1 ≤ U.q u ∧ U.q u < 4} := by
        intro u hu
        exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
      have hcard := Set.ncard_le_ncard hsub hlowFinite
      calc
        (prD_frequencyShell η U 0).ncard ≤
            ({u | 1 ≤ U.q u ∧ U.q u < 4}.ncard : ℝ) := by exact_mod_cast hcard
        _ ≤ Clow := hlowBound
        _ ≤ C := le_max_right _ _
        _ = C * ((2 ^ 0 : ℕ) : ℝ) := by simp [C]
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast this
      obtain ⟨hfin, hbound⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      have hsub : prD_frequencyShell η U k ⊆
          {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧
            U.q u < 2 * ((2 ^ k : ℕ) : ℝ)} := by
        intro u hu
        exact ⟨hu.1, hu.2.trans_eq (by
          rw [pow_succ]
          push_cast
          ring)⟩
      have hcard := Set.ncard_le_ncard hsub hfin
      calc
        (prD_frequencyShell η U k).ncard ≤
            ({u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧
              U.q u < 2 * ((2 ^ k : ℕ) : ℝ)}.ncard : ℝ) := by exact_mod_cast hcard
        _ ≤ Cdyad * ((2 ^ k : ℕ) : ℝ) := hbound
        _ ≤ C * ((2 ^ k : ℕ) : ℝ) := by
          dsimp [C]
          gcongr
          exact le_max_left _ _
  have hInner (k : ℕ) :
      Summable (fun u : prD_frequencyShell η U k => U.q u.1 ^ (-2 : ℝ)) := by
    letI := (hShellFinite k).fintype
    exact Summable.of_finite
  have hMass (k : ℕ) :
      (∑' u : prD_frequencyShell η U k, U.q u.1 ^ (-2 : ℝ)) ≤
        C * (1 / 2 : ℝ) ^ k := by
    let X : ℝ := ((2 ^ k : ℕ) : ℝ)
    have hX : 0 < X := by positivity
    have hterm (u : prD_frequencyShell η U k) :
        U.q u.1 ^ (-2 : ℝ) ≤ X ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX (by simpa [X] using u.2.1) (by norm_num)
    letI := (hShellFinite k).fintype
    calc
      _ ≤ ∑' u : prD_frequencyShell η U k, X ^ (-2 : ℝ) :=
        (hInner k).tsum_le_tsum (fun u => hterm u) (by
          letI := (hShellFinite k).fintype
          exact Summable.of_finite)
      _ = (Fintype.card (prD_frequencyShell η U k) : ℝ) * X ^ (-2 : ℝ) := by simp
      _ = ((prD_frequencyShell η U k).ncard : ℝ) * X ^ (-2 : ℝ) := by simp
      _ ≤ (C * X) * X ^ (-2 : ℝ) := by
        gcongr
        exact hCount k
      _ = C * (1 / 2 : ℝ) ^ k := by
        have hXcast : X = (2 : ℝ) ^ k := by
          dsimp [X]
          norm_cast
        rw [hXcast, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ k) 2,
          Real.rpow_two]
        simp only [one_div_pow, one_pow]
        field_simp
  have hOuter : Summable
      (fun k : ℕ => ∑' u : prD_frequencyShell η U k, U.q u.1 ^ (-2 : ℝ)) := by
    have hgeom : Summable (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun u => ?_) hMass hgeom
    exact Real.rpow_nonneg (U.q_pos u.1).le _
  have hf0 : ∀ u : U.U, 0 ≤ U.q u ^ (-2 : ℝ) :=
    fun u => Real.rpow_nonneg (U.q_pos u).le _
  exact (summable_partition hf0 (prD_frequencyShell_partition η U)).2
    ⟨hInner, hOuter⟩

private theorem prD_sheet_onUnits_integrable (T : ℝ) (hT : 0 < T)
    (hf : Integrable (leadFourier sd W) (R.sheets.sheet T)) :
    Integrable (onUnits (fun y : S.FSˣ => leadFourier sd W (y : S.FS)))
      (R.sheets.sheet T) := by
  have hEq : onUnits (fun y : S.FSˣ => leadFourier sd W (y : S.FS)) =ᵐ[R.sheets.sheet T]
      leadFourier sd W := by
    filter_upwards [R.sheets.sheet_support T hT] with y hy
    simp [onUnits, hy.1]
  exact hf.congr hEq.symm

private theorem prD_sheet_norm_onUnits_integrable (T : ℝ) (hT : 0 < T)
    (hf : Integrable (leadFourier sd W) (R.sheets.sheet T)) :
    Integrable (onUnits (fun y : S.FSˣ =>
      (‖leadFourier sd W (y : S.FS)‖ : ℂ))) (R.sheets.sheet T) ∧
    (∫ y, onUnits (fun y : S.FSˣ =>
      (‖leadFourier sd W (y : S.FS)‖ : ℂ)) y ∂(R.sheets.sheet T)) =
      ((∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet T) : ℝ) : ℂ) := by
  have hEq : onUnits (fun y : S.FSˣ =>
      (‖leadFourier sd W (y : S.FS)‖ : ℂ)) =ᵐ[R.sheets.sheet T]
      fun y => (‖leadFourier sd W y‖ : ℂ) := by
    filter_upwards [R.sheets.sheet_support T hT] with y hy
    simp [onUnits, hy.1]
  have hRaw : Integrable (fun y => (‖leadFourier sd W y‖ : ℂ))
      (R.sheets.sheet T) := hf.norm.ofReal
  refine ⟨hRaw.congr hEq.symm, ?_⟩
  calc
    _ = ∫ y, (‖leadFourier sd W y‖ : ℂ) ∂(R.sheets.sheet T) :=
      integral_congr_ae hEq
    _ = ((∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet T) : ℝ) : ℂ) :=
      integral_ofReal

private theorem prD_integrable_tsum_of_summable_integral_norm
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    {f : ι → α → ℂ} (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hf i).1), ?_⟩
  show ∫⁻ x, ‖∑' i, f i x‖ₑ ∂μ < ⊤
  have h0 (i : ι) :
      ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hf i),
      Real.enorm_eq_ofReal (integral_nonneg (fun x => norm_nonneg (f i x)))]
  calc
    ∫⁻ x, ‖∑' i, f i x‖ₑ ∂μ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ := lintegral_tsum (fun i => (hf i).1.enorm)
    _ = ∑' i, ‖∫ x, ‖f i x‖ ∂μ‖ₑ := tsum_congr h0
    _ = ∑' i, ENNReal.ofReal (∫ x, ‖f i x‖ ∂μ) := by
      apply tsum_congr
      intro i
      exact Real.enorm_eq_ofReal (integral_nonneg (fun x => norm_nonneg (f i x)))
    _ = ENNReal.ofReal (∑' i, ∫ x, ‖f i x‖ ∂μ) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun i => integral_nonneg (fun x => norm_nonneg (f i x))) hs]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- IMPL: exact nonzero-frequency regrouping and its full absolute unfolding. -/
theorem orbit_sheet_sum
    (hzero : leadFourier sd W 0 = 0)
    (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hequiv : LeadEquivContract (bc := bc) η U)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) (X : ℝ) (hX : 0 < X) :
    Summable (fun ur : U.U × S.ExtIdeal =>
      ‖leadFiniteFactor R s I a ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
        leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI I.1)‖) ∧
    IntegrableOn (fun y : S.FS =>
      onUnits (fun t : S.FSˣ =>
        ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
          leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
            S.diag ((h : F) / ((bc.gen s : F) * (a : F))))) y)
      (omegaAt R 1) (R.sheets.sheet 1) ∧
    omegaInt R 1 (fun t : S.FSˣ =>
      ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
        leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
          S.diag ((h : F) / ((bc.gen s : F) * (a : F))))) =
      ∑' ur : U.U × S.ExtIdeal,
        leadFiniteFactor R s I a ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
          leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI I.1) := by
  classical
  obtain ⟨e, heval⟩ := hequiv
  rcases hfinite with ⟨hfiniteRows, hgaussBound⟩
  rcases hsheets.2 with ⟨C, hC, hSheetBound⟩
  let denom : Fˣ := bc.gen s * a
  let baseR : U.U × S.ExtIdeal → S.R := fun ur =>
    U.repr ur.1 * (R.exterior.genR ur.2) ^ 6
  have hbase0 (ur : U.U × S.ExtIdeal) : (baseR ur : F) ≠ 0 := by
    have hrepr := U.repr_nonzero ur.1
    have hgen : (R.exterior.genR ur.2 : F) ≠ 0 := by
      rw [R.exterior.genR_val]
      exact Units.ne_zero (bc.gen ur.2)
    change (U.repr ur.1 : F) * (R.exterior.genR ur.2 : F) ^ 6 ≠ 0
    exact mul_ne_zero hrepr (pow_ne_zero _ hgen)
  let baseUnit : U.U × S.ExtIdeal → Fˣ := fun ur =>
    Units.mk0 (baseR ur : F) (hbase0 ur)
  let reprUnit : U.U × S.ExtIdeal → Fˣ := fun ur =>
    Units.mk0 (U.repr ur.1 : F) (U.repr_nonzero ur.1)
  have hbaseUnitVal (ur : U.U × S.ExtIdeal) :
      ((baseUnit ur : Fˣ) : F) = (baseR ur : F) := rfl
  have hbaseUnitFactor (ur : U.U × S.ExtIdeal) :
      baseUnit ur = reprUnit ur * (bc.gen ur.2) ^ 6 := by
    apply Units.ext
    simp [baseUnit, reprUnit, baseR, R.exterior.genR_val]
  let orbitT : U.U × S.ExtIdeal → ℝ := fun ur =>
    X * U.q ur.1 * qI ur.2.1 ^ 6 / qI I.1
  let orbitK : U.U × S.ExtIdeal → S.FSˣ := fun ur =>
    R.sheets.ellU (qI s.1 * X) * S.diagU (baseUnit ur / denom)
  let orbitC : ℝ := C * qI s.1 * qI I.1 ^ 3 / X ^ 2
  have hqExt (J : S.ExtIdeal) : 0 < qI J.1 := by
    have h := (a2_bridge_NORM D S).1 J
    simpa [qI, idealNorm] using h.1
  have hqS : 0 < qI s.1 := hqExt s
  have hqI : 0 < qI I.1 := hqExt I
  have hnormRepr (ur : U.U × S.ExtIdeal) :
      S.absS (S.diagU (reprUnit ur) : S.FS) = U.q ur.1 := by
    simpa [reprUnit, SData.diagU] using (U.q_eq_absS ur.1).symm
  have hnormGen (J : S.ExtIdeal) :
      S.absS (S.diagU (bc.gen J) : S.FS) = qI J.1 := by
    simpa [qI, idealNorm] using a2_bridge_NORM_gen D S H Bd bc J
  have hnormA : S.absS (S.diagU a : S.FS) = qI I.1 := by
    change S.absS (S.diag (a : F)) = qI I.1
    simpa [qI, idealNorm] using
      S.absS_diag_eq_norm_ofFieldData D (a : F) I.1 ha.1 ha
  have hpowGen (J : S.ExtIdeal) :
      S.absS (((S.diagU (bc.gen J)) ^ 6 : S.FSˣ) : S.FS) = qI J.1 ^ 6 := by
    have hp := (a2_bridge_NORM D S).2.2.2.2.2
      (S.diagU (bc.gen J)) (6 : ℤ)
    simpa [hnormGen J] using hp
  have hnormBase (ur : U.U × S.ExtIdeal) :
      S.absS (S.diagU (baseUnit ur) : S.FS) =
        U.q ur.1 * qI ur.2.1 ^ 6 := by
    calc
      S.absS (S.diagU (baseUnit ur) : S.FS) =
          S.absS ((S.diagU (reprUnit ur) : S.FSˣ) : S.FS) *
            S.absS (((S.diagU (bc.gen ur.2)) ^ 6 : S.FSˣ) : S.FS) := by
        rw [hbaseUnitFactor, map_mul, map_pow]
        exact (a2_bridge_NORM D S).2.1 _ _
      _ = U.q ur.1 * qI ur.2.1 ^ 6 := by
        rw [hnormRepr ur, hpowGen ur.2]
  have hnormDenom : S.absS (S.diagU denom : S.FS) = qI s.1 * qI I.1 := by
    change S.absS (S.diagU (bc.gen s * a) : S.FS) = qI s.1 * qI I.1
    calc
      S.absS (S.diagU (bc.gen s * a) : S.FS) =
          S.absS (S.diagU (bc.gen s) : S.FS) *
            S.absS (S.diagU a : S.FS) := by
        rw [map_mul]
        exact (a2_bridge_NORM D S).2.1 _ _
      _ = qI s.1 * qI I.1 := by rw [hnormGen s, hnormA]
  have hnormRatio (ur : U.U × S.ExtIdeal) :
      S.absS (S.diagU (baseUnit ur / denom) : S.FS) =
        U.q ur.1 * qI ur.2.1 ^ 6 / (qI s.1 * qI I.1) := by
    have hdiv := (a2_bridge_NORM D S).2.2.2.2.1
      (S.diagU (baseUnit ur)) (S.diagU denom)
    simpa [map_div, hnormBase ur, hnormDenom] using hdiv
  have hOrbitKNorm (ur : U.U × S.ExtIdeal) :
      S.absS (orbitK ur : S.FS) = orbitT ur := by
    calc
      S.absS (orbitK ur : S.FS) =
          S.absS (R.sheets.ellU (qI s.1 * X) : S.FS) *
            S.absS (S.diagU (baseUnit ur / denom) : S.FS) := by
        exact (a2_bridge_NORM D S).2.1 _ _
      _ = orbitT ur := by
        rw [R.sheets.ellU_norm _ (mul_pos hqS hX), hnormRatio ur]
        dsimp [orbitT]
        field_simp [ne_of_gt hqS, ne_of_gt hqI]
  have hFreqWeights : Summable (fun u : U.U => U.q u ^ (-2 : ℝ)) :=
    prD_frequency_q_inv_sq_summable η U
  have hIdealWeights : Summable (fun r : S.ExtIdeal => qI r.1 ^ (-12 : ℝ)) := by
    simpa [qI, idealNorm] using a2_bridge_COUNT_summable S 12 (by norm_num)
  have hWeights : Summable (fun ur : U.U × S.ExtIdeal =>
      U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ)) :=
    hFreqWeights.mul_of_nonneg hIdealWeights
      (fun u => Real.rpow_nonneg (U.q_pos u).le _)
      (fun r => Real.rpow_nonneg (hqExt r).le _)
  have hMajorant : Summable (fun ur : U.U × S.ExtIdeal =>
      orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ)) :=
    by simpa [mul_assoc] using hWeights.mul_left orbitC
  have hOrbitTpos (ur : U.U × S.ExtIdeal) : 0 < orbitT ur := by
    dsimp [orbitT]
    apply div_pos
    · exact mul_pos (mul_pos hX (U.q_pos ur.1)) (pow_pos (hqExt ur.2) 6)
    · exact hqI
  have hFactorNorm (ur : U.U × S.ExtIdeal) :
      ‖leadFiniteFactor R s I a
        ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6)‖ ≤ qI s.1 * qI I.1 := by
    let bR : S.R := U.repr ur.1 * (R.exterior.genR ur.2) ^ 6
    have hb := (hfiniteRows s I a ha hallowed bR).2.1
    simpa [bR, R.exterior.genR_val] using hb
  have hOrbitAlgebra (ur : U.U × S.ExtIdeal) :
      qI s.1 * qI I.1 * (C / (orbitT ur) ^ 2) =
        orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) := by
    have hqU := U.q_pos ur.1
    have hqR := hqExt ur.2
    have hpowU : U.q ur.1 ^ (-2 : ℝ) = (U.q ur.1 ^ 2)⁻¹ := by
      rw [Real.rpow_neg hqU.le]
      exact congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (U.q ur.1) 2)
    have hpowR : qI ur.2.1 ^ (-12 : ℝ) = (qI ur.2.1 ^ 12)⁻¹ := by
      rw [Real.rpow_neg hqR.le]
      exact congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (qI ur.2.1) 12)
    rw [hpowU, hpowR]
    dsimp [orbitC, orbitT]
    field_simp [ne_of_gt hX, ne_of_gt hqS, ne_of_gt hqI,
      ne_of_gt hqU, ne_of_gt hqR]
    <;> ring
  have hOrbitAbsBound (ur : U.U × S.ExtIdeal) :
      ‖leadFiniteFactor R s I a
          ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6)‖ *
        (∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur))) ≤
      orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) := by
    calc
      _ ≤ (qI s.1 * qI I.1) *
          (C / (orbitT ur) ^ 2) := by
        exact mul_le_mul (hFactorNorm ur)
          (hSheetBound (orbitT ur) (hOrbitTpos ur))
          (integral_nonneg (fun y => norm_nonneg (leadFourier sd W y)))
          (mul_nonneg hqS.le hqI.le)
      _ = orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) :=
        hOrbitAlgebra ur
  have hV0Norm (ur : U.U × S.ExtIdeal) :
      ‖leadV0 R sd W (orbitT ur)‖ ≤
        ∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur)) := by
    unfold leadV0
    exact norm_integral_le_integral_norm _
  have hOrbitTermBound (ur : U.U × S.ExtIdeal) :
      ‖leadFiniteFactor R s I a
          ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
        leadV0 R sd W (orbitT ur)‖ ≤
      orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) := by
    calc
      _ = ‖leadFiniteFactor R s I a
            ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6)‖ *
          ‖leadV0 R sd W (orbitT ur)‖ := norm_mul _ _
      _ ≤ ‖leadFiniteFactor R s I a
              ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6)‖ *
            (∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur))) :=
          mul_le_mul_of_nonneg_left (hV0Norm ur) (norm_nonneg _)
      _ ≤ orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) :=
          hOrbitAbsBound ur
  have hFirst : Summable (fun ur : U.U × S.ExtIdeal =>
      ‖leadFiniteFactor R s I a
          ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
        leadV0 R sd W (orbitT ur)‖) := by
    apply hMajorant.of_norm_bounded
    intro ur
    simpa using hOrbitTermBound ur
  let orbitCoeff : U.U × S.ExtIdeal → ℂ := fun ur =>
    leadFiniteFactor R s I a ((baseR ur : F))
  let orbitFourier : U.U × S.ExtIdeal → Gamma S → S.FSˣ → ℂ :=
    fun ur γ t => leadFourier sd W
      (((orbitK ur * S.diagU (γ.1 : Fˣ) * t : S.FSˣ) : S.FS))
  let rowTerm : S.R → S.FSˣ → ℂ := fun h t =>
    leadFiniteFactor R s I a (h : F) * leadFourier sd W
      (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
        S.diag ((h : F) / (denom : F)))
  let fullTerm : S.R → S.FS → ℂ := fun h => onUnits (rowTerm h)
  let omegaMeasure : Measure S.FS := (R.sheets.sheet 1).restrict (omegaAt R 1)
  let termNorm (h : S.R) : ℝ := ∫ y, ‖fullTerm h y‖ ∂omegaMeasure
  let orbitNorm (ur : U.U × S.ExtIdeal) (γ : Gamma S) : ℝ :=
    ∫ y, ‖onUnits (orbitFourier ur γ) y‖ ∂omegaMeasure
  have hRowFactor (p : (U.U × S.ExtIdeal) × Gamma S) :
      leadFiniteFactor R s I a ((e p : {x : S.R // (x : F) ≠ 0}).1 : F) =
        orbitCoeff p.1 := by
    have hInv := (hfiniteRows s I a ha hallowed (baseR p.1)).2.2 p.2
    have hvalue : ((e p : {x : S.R // (x : F) ≠ 0}).1 : F) =
        ((p.2.1 : Fˣ) : F) * (baseR p.1 : F) := by
      calc
        _ = ((p.2.1 : Fˣ) : F) * (U.repr p.1.1 : F) *
            (bc.gen p.1.2 : F) ^ 6 := heval p
        _ = ((p.2.1 : Fˣ) : F) * (baseR p.1 : F) := by
          simp [baseR, R.exterior.genR_val, mul_assoc]
    rw [hvalue]
    exact hInv
  have hRowArgument (p : (U.U × S.ExtIdeal) × Gamma S) (t : S.FSˣ) :
      (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
        S.diag (((e p : {x : S.R // (x : F) ≠ 0}).1 : F) / (denom : F))) =
      (((orbitK p.1 * S.diagU (p.2.1 : Fˣ) * t : S.FSˣ) : S.FS)) := by
    have hnum :
        (((p.2.1 : Fˣ) * baseUnit p.1 / denom : Fˣ) : F) =
          ((e p : {x : S.R // (x : F) ≠ 0}).1 : F) / (denom : F) := by
      rw [heval p]
      simp [baseUnit, baseR, R.exterior.genR_val, div_eq_mul_inv, mul_assoc]
    have hdiag : S.diag
        (((e p : {x : S.R // (x : F) ≠ 0}).1 : F) / (denom : F)) =
        (S.diagU ((p.2.1 : Fˣ) * baseUnit p.1 / denom) : S.FS) := by
      rw [← hnum]
      rfl
    have hmap : S.diagU ((p.2.1 : Fˣ) * baseUnit p.1 / denom) =
        S.diagU (p.2.1 : Fˣ) * S.diagU (baseUnit p.1 / denom) := by
      simp only [map_div, map_mul]
      exact mul_div_assoc _ _ _
    have hunit :
        (t * R.sheets.ellU (qI s.1 * X)) *
            S.diagU ((p.2.1 : Fˣ) * baseUnit p.1 / denom) =
          orbitK p.1 * S.diagU (p.2.1 : Fˣ) * t := by
      rw [hmap]
      change (t * R.sheets.ellU (qI s.1 * X)) *
          (S.diagU (p.2.1 : Fˣ) * S.diagU (baseUnit p.1 / denom)) =
        (R.sheets.ellU (qI s.1 * X) * S.diagU (baseUnit p.1 / denom)) *
          S.diagU (p.2.1 : Fˣ) * t
      ac_rfl
    calc
      _ = (((t * R.sheets.ellU (qI s.1 * X)) *
          S.diagU ((p.2.1 : Fˣ) * baseUnit p.1 / denom) : S.FSˣ) : S.FS) := by
            rw [hdiag]
            simp
      _ = _ := congrArg (fun z : S.FSˣ => (z : S.FS)) hunit
  have hRowOrbit (p : (U.U × S.ExtIdeal) × Gamma S) :
      rowTerm ((e p : {x : S.R // (x : F) ≠ 0}).1) =
        fun t => orbitCoeff p.1 * orbitFourier p.1 p.2 t := by
    funext t
    change leadFiniteFactor R s I a
        ((e p : {x : S.R // (x : F) ≠ 0}).1 : F) *
        leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
          S.diag (((e p : {x : S.R // (x : F) ≠ 0}).1 : F) / (denom : F))) =
      orbitCoeff p.1 * leadFourier sd W
        (((orbitK p.1 * S.diagU (p.2.1 : Fˣ) * t : S.FSˣ) : S.FS))
    rw [hRowFactor p, hRowArgument p t]
  have hFullOrbit (p : (U.U × S.ExtIdeal) × Gamma S) :
      fullTerm ((e p : {x : S.R // (x : F) ≠ 0}).1) =
        fun y => orbitCoeff p.1 * onUnits (orbitFourier p.1 p.2) y := by
    funext y
    by_cases hy : IsUnit y
    · simp [fullTerm, onUnits, hy, hRowOrbit p]
    · simp [fullTerm, onUnits, hy]
  have hOrbitFourierInt (ur : U.U × S.ExtIdeal) :
      Integrable (onUnits (fun y : S.FSˣ =>
        leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))))
        (R.sheets.sheet 1) := by
    let fU : S.FSˣ → ℂ := fun y => leadFourier sd W (y : S.FS)
    have hTInt := hsheets.1 (orbitT ur) (hOrbitTpos ur)
    have hUnitInt := prD_sheet_onUnits_integrable (R := R) (sd := sd) (W := W)
      (orbitT ur) (hOrbitTpos ur) hTInt
    have hinput : Integrable (onUnits fU)
        (R.sheets.sheet (S.absS (orbitK ur : S.FS) * 1)) := by
      simpa [fU, hOrbitKNorm ur] using hUnitInt
    exact (a2_bridge_SHEET_transport (G := R.sheets) 1 (by norm_num)
      (orbitK ur) fU hinput).1
  have hOrbitFourierIntegral (ur : U.U × S.ExtIdeal) :
      (∫ y, onUnits (fun y : S.FSˣ =>
        leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))) y
          ∂(R.sheets.sheet 1)) = leadV0 R sd W (orbitT ur) := by
    let fU : S.FSˣ → ℂ := fun y => leadFourier sd W (y : S.FS)
    have hTInt := hsheets.1 (orbitT ur) (hOrbitTpos ur)
    have hUnitInt := prD_sheet_onUnits_integrable (R := R) (sd := sd) (W := W)
      (orbitT ur) (hOrbitTpos ur) hTInt
    have hinput : Integrable (onUnits fU)
        (R.sheets.sheet (S.absS (orbitK ur : S.FS) * 1)) := by
      simpa [fU, hOrbitKNorm ur] using hUnitInt
    have htrans := a2_bridge_SHEET_transport (G := R.sheets) 1 (by norm_num)
      (orbitK ur) fU hinput
    have hAE : onUnits fU =ᵐ[R.sheets.sheet (orbitT ur)]
        leadFourier sd W := by
      filter_upwards [R.sheets.sheet_support (orbitT ur) (hOrbitTpos ur)] with y hy
      simp [fU, onUnits, hy.1]
    have hscale : S.absS (orbitK ur : S.FS) * 1 = orbitT ur := by
      rw [hOrbitKNorm ur]
      simp
    calc
      _ = bridgeSheetIntegral R.sheets 1
          (fun y => fU (orbitK ur * y)) := by
        simp only [bridgeSheetIntegral, fU]
      _ = bridgeSheetIntegral R.sheets (S.absS (orbitK ur : S.FS) * 1)
          fU := htrans.2
      _ = ∫ y, onUnits fU y ∂(R.sheets.sheet (orbitT ur)) := by
        rw [hscale]
        rfl
      _ = ∫ y, leadFourier sd W y ∂(R.sheets.sheet (orbitT ur)) :=
        integral_congr_ae hAE
      _ = leadV0 R sd W (orbitT ur) := rfl
  have hOrbitNormInt (ur : U.U × S.ExtIdeal) :
      Integrable (onUnits (fun y : S.FSˣ =>
        (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ)))
        (R.sheets.sheet 1) := by
    have hTInt := hsheets.1 (orbitT ur) (hOrbitTpos ur)
    have hUnitInt := (prD_sheet_norm_onUnits_integrable (R := R) (sd := sd)
      (W := W) (orbitT ur) (hOrbitTpos ur) hTInt).1
    have hinput : Integrable (onUnits (fun y : S.FSˣ =>
        (‖leadFourier sd W (y : S.FS)‖ : ℂ)))
        (R.sheets.sheet (S.absS (orbitK ur : S.FS) * 1)) := by
      simpa [hOrbitKNorm ur] using hUnitInt
    exact (a2_bridge_SHEET_transport (G := R.sheets) 1 (by norm_num)
      (orbitK ur) (fun y : S.FSˣ => (‖leadFourier sd W (y : S.FS)‖ : ℂ))
      hinput).1
  have hOrbitNormIntegral (ur : U.U × S.ExtIdeal) :
      (∫ y, onUnits (fun y : S.FSˣ =>
        (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ)) y
          ∂(R.sheets.sheet 1)) =
        ((∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur)) : ℝ) : ℂ) := by
    have hTInt := hsheets.1 (orbitT ur) (hOrbitTpos ur)
    have hNormData := prD_sheet_norm_onUnits_integrable (R := R) (sd := sd)
      (W := W) (orbitT ur) (hOrbitTpos ur) hTInt
    have hinput : Integrable (onUnits (fun y : S.FSˣ =>
        (‖leadFourier sd W (y : S.FS)‖ : ℂ)))
        (R.sheets.sheet (S.absS (orbitK ur : S.FS) * 1)) := by
      simpa [hOrbitKNorm ur] using hNormData.1
    have htrans := a2_bridge_SHEET_transport (G := R.sheets) 1 (by norm_num)
      (orbitK ur) (fun y : S.FSˣ => (‖leadFourier sd W (y : S.FS)‖ : ℂ)) hinput
    have hscale : S.absS (orbitK ur : S.FS) * 1 = orbitT ur := by
      rw [hOrbitKNorm ur]
      simp
    calc
      _ = bridgeSheetIntegral R.sheets 1 (fun y =>
          (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ)) := rfl
      _ = bridgeSheetIntegral R.sheets (S.absS (orbitK ur : S.FS) * 1)
          (fun y => (‖leadFourier sd W (y : S.FS)‖ : ℂ)) := htrans.2
      _ = ∫ y, onUnits (fun y : S.FSˣ =>
          (‖leadFourier sd W (y : S.FS)‖ : ℂ)) y
            ∂(R.sheets.sheet (orbitT ur)) := by rw [hscale]; rfl
      _ = _ := hNormData.2
  have hOrbitUnfold (ur : U.U × S.ExtIdeal) :=
    a2_bridge_SHEET_unfold (G := R.sheets) 1 (by norm_num)
      (fun y : S.FSˣ => leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS)))
      (hOrbitFourierInt ur)
  have hOrbitNormUnfold (ur : U.U × S.ExtIdeal) :=
    a2_bridge_SHEET_unfold (G := R.sheets) 1 (by norm_num)
      (fun y : S.FSˣ =>
        (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ))
      (hOrbitNormInt ur)
  have hOmegaIntEq (f : S.FSˣ → ℂ) :
      omegaInt R 1 f = bridgeOmegaInt R.sheets 1 f := rfl
  have hOmegaNormSummable (ur : U.U × S.ExtIdeal) :
      Summable (fun γ : Gamma S => omegaInt R 1
        (fun y => (‖orbitFourier ur γ y‖ : ℂ))) := by
    simpa [omegaInt, bridgeOmegaInt, omegaAt, bridgeOmegaAt,
      orbitFourier, mul_assoc] using (hOrbitNormUnfold ur).2.1
  have hOmegaNormUnfoldEq (ur : U.U × S.ExtIdeal) :
      (∑' γ : Gamma S, omegaInt R 1
        (fun y => (‖orbitFourier ur γ y‖ : ℂ))) =
      (∫ y, onUnits (fun y : S.FSˣ =>
        (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ)) y
          ∂(R.sheets.sheet 1)) := by
    simpa [omegaInt, bridgeOmegaInt, omegaAt, bridgeOmegaAt,
      bridgeSheetIntegral, orbitFourier, mul_assoc] using (hOrbitNormUnfold ur).2.2
  have hOrbitNormPoint (ur : U.U × S.ExtIdeal) (γ : Gamma S) (y : S.FS) :
      onUnits (fun t : S.FSˣ => (‖orbitFourier ur γ t‖ : ℂ)) y =
        ((‖onUnits (orbitFourier ur γ) y‖ : ℂ)) := by
    by_cases hy : IsUnit y <;> simp [onUnits, hy]
  have hOrbitNormToRe (ur : U.U × S.ExtIdeal) (γ : Gamma S) :
      orbitNorm ur γ =
        (omegaInt R 1 (fun t => (‖orbitFourier ur γ t‖ : ℂ))).re := by
    have hOrbitIntOn : IntegrableOn (onUnits (orbitFourier ur γ))
        (omegaAt R 1) (R.sheets.sheet 1) := by
      simpa [orbitFourier, omegaAt, bridgeOmegaAt, mul_assoc] using
        (hOrbitUnfold ur).1 γ
    have hOrbitInt : Integrable (onUnits (orbitFourier ur γ)) omegaMeasure := by
      change IntegrableOn (onUnits (orbitFourier ur γ))
        (omegaAt R 1) (R.sheets.sheet 1)
      exact hOrbitIntOn
    have hNormInt : Integrable
        (fun y => (‖onUnits (orbitFourier ur γ) y‖ : ℂ)) omegaMeasure :=
      hOrbitInt.norm.ofReal
    calc
      orbitNorm ur γ =
          ∫ y, ((‖onUnits (orbitFourier ur γ) y‖ : ℂ).re) ∂omegaMeasure := by
        simp [orbitNorm]
      _ = (∫ y, (‖onUnits (orbitFourier ur γ) y‖ : ℂ) ∂omegaMeasure).re :=
        integral_re hNormInt
      _ = (omegaInt R 1 (fun t => (‖orbitFourier ur γ t‖ : ℂ))).re := by
        congr 1
        unfold omegaInt
        exact integral_congr_ae (Filter.Eventually.of_forall
          (fun y => (hOrbitNormPoint ur γ y).symm))
  have hOrbitNormSummableReal (ur : U.U × S.ExtIdeal) :
      Summable (fun γ : Gamma S => orbitNorm ur γ) := by
    have hs := Complex.reCLM.summable (hOmegaNormSummable ur)
    exact hs.congr (fun γ => (hOrbitNormToRe ur γ).symm)
  have hOrbitNormSum (ur : U.U × S.ExtIdeal) :
      (∑' γ : Gamma S, orbitNorm ur γ) =
        ∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur)) := by
    calc
      _ = ∑' γ : Gamma S,
          (omegaInt R 1 (fun t => (‖orbitFourier ur γ t‖ : ℂ))).re :=
        tsum_congr (fun γ => hOrbitNormToRe ur γ)
      _ = (∑' γ : Gamma S,
          omegaInt R 1 (fun t => (‖orbitFourier ur γ t‖ : ℂ))).re :=
        (Complex.re_tsum (hOmegaNormSummable ur)).symm
      _ = (∫ y, onUnits (fun y : S.FSˣ =>
          (‖leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))‖ : ℂ)) y
            ∂(R.sheets.sheet 1)).re := congrArg Complex.re (hOmegaNormUnfoldEq ur)
      _ = (↑(∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur)) : ℝ) : ℂ).re :=
        congrArg Complex.re (hOrbitNormIntegral ur)
      _ = ∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur)) := by simp
  have hTermNormOrbit (p : (U.U × S.ExtIdeal) × Gamma S) :
      termNorm ((e p : {x : S.R // (x : F) ≠ 0}).1) =
        ‖orbitCoeff p.1‖ * orbitNorm p.1 p.2 := by
    change ∫ y, ‖fullTerm ((e p : {x : S.R // (x : F) ≠ 0}).1) y‖
        ∂omegaMeasure = _
    calc
      _ = ∫ y, ‖orbitCoeff p.1 * onUnits (orbitFourier p.1 p.2) y‖ ∂omegaMeasure := by
        congr 1
        funext y
        rw [hFullOrbit p]
      _ = ∫ y, ‖orbitCoeff p.1‖ *
          ‖onUnits (orbitFourier p.1 p.2) y‖ ∂omegaMeasure := by
        congr 1
        funext y
        rw [norm_mul]
      _ = ‖orbitCoeff p.1‖ * orbitNorm p.1 p.2 := by
        rw [integral_const_mul]
  have hInnerTermNorm (ur : U.U × S.ExtIdeal) :
      Summable (fun γ : Gamma S => termNorm ((e (ur, γ) :
        {x : S.R // (x : F) ≠ 0}).1)) := by
    have hs := (hOrbitNormSummableReal ur).mul_left (‖orbitCoeff ur‖)
    exact hs.congr (fun γ => (hTermNormOrbit (ur, γ)).symm)
  have hOrbitCoeffNorm (ur : U.U × S.ExtIdeal) :
      ‖orbitCoeff ur‖ =
        ‖leadFiniteFactor R s I a
          ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6)‖ := by
    simp [orbitCoeff, baseR, R.exterior.genR_val]
  have hInnerTermNormBound (ur : U.U × S.ExtIdeal) :
      (∑' γ : Gamma S, termNorm ((e (ur, γ) :
        {x : S.R // (x : F) ≠ 0}).1)) ≤
        orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) := by
    calc
      _ = ∑' γ : Gamma S, ‖orbitCoeff ur‖ * orbitNorm ur γ := by
        apply tsum_congr
        intro γ
        have h := hTermNormOrbit (ur, γ)
        simpa only [Prod.fst, Prod.snd] using h
      _ = ‖orbitCoeff ur‖ *
          (∑' γ : Gamma S, orbitNorm ur γ) := tsum_mul_left
      _ = ‖orbitCoeff ur‖ *
          (∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet (orbitT ur))) := by
        rw [hOrbitNormSum ur]
      _ ≤ orbitC * U.q ur.1 ^ (-2 : ℝ) * qI ur.2.1 ^ (-12 : ℝ) := by
        rw [hOrbitCoeffNorm ur]
        exact hOrbitAbsBound ur
  have hOuterTermNorm : Summable (fun ur : U.U × S.ExtIdeal =>
      ∑' γ : Gamma S, termNorm ((e (ur, γ) :
        {x : S.R // (x : F) ≠ 0}).1)) := by
    apply Summable.of_nonneg_of_le
      (fun ur => tsum_nonneg (fun γ => integral_nonneg (fun y => norm_nonneg _)))
      hInnerTermNormBound hMajorant
  have hTripTermNorm : Summable (fun p : (U.U × S.ExtIdeal) × Gamma S =>
      termNorm ((e p : {x : S.R // (x : F) ≠ 0}).1)) := by
    apply (summable_prod_of_nonneg
      (fun p => integral_nonneg (fun y => norm_nonneg _))).2
    refine ⟨?_, hOuterTermNorm⟩
    intro ur
    simpa using hInnerTermNorm ur
  have hFullTermIntegrableOrbit (p : (U.U × S.ExtIdeal) × Gamma S) :
      Integrable (fullTerm ((e p : {x : S.R // (x : F) ≠ 0}).1)) omegaMeasure := by
    have hIntOn : IntegrableOn (onUnits (orbitFourier p.1 p.2))
        (omegaAt R 1) (R.sheets.sheet 1) := by
      simpa [orbitFourier, omegaAt, bridgeOmegaAt, mul_assoc] using
        (hOrbitUnfold p.1).1 p.2
    have hInt : Integrable (onUnits (orbitFourier p.1 p.2)) omegaMeasure := by
      change IntegrableOn (onUnits (orbitFourier p.1 p.2))
        (omegaAt R 1) (R.sheets.sheet 1)
      exact hIntOn
    have hmul := hInt.const_mul (orbitCoeff p.1)
    exact hmul.congr (Filter.Eventually.of_forall
      (fun y => (congrFun (hFullOrbit p) y).symm))
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable S.R := inferInstance
  have hNonzeroTermNorm : Summable (fun x : {x : S.R // (x : F) ≠ 0} => termNorm x.1) :=
    (Equiv.summable_iff e).mp hTripTermNorm
  have hTermNormSummable : Summable termNorm := by
    have hinj : Function.Injective
        (fun x : {x : S.R // (x : F) ≠ 0} => x.1) := Subtype.val_injective
    apply (hinj.summable_iff (f := termNorm) ?_).mp hNonzeroTermNorm
    intro h hh
    have hval : (h : F) = 0 := by
      by_contra hval
      exact hh ⟨⟨h, hval⟩, rfl⟩
    have hhR : h = 0 := Subtype.ext hval
    subst h
    simp [termNorm, fullTerm, rowTerm, onUnits, hzero]
  have hTermIntegrable (h : S.R) : Integrable (fullTerm h) omegaMeasure := by
    by_cases hh : (h : F) = 0
    · have hhR : h = 0 := Subtype.ext hh
      subst h
      have hZero : fullTerm 0 = 0 := by
        funext y
        simp [fullTerm, rowTerm, onUnits, hzero]
      rw [hZero]
      exact integrable_zero S.FS ℂ omegaMeasure
    · let x : {x : S.R // (x : F) ≠ 0} := ⟨h, hh⟩
      let p := e.symm x
      have hp : (e p).1 = h := congrArg Subtype.val (e.apply_symm_apply x)
      simpa [hp] using hFullTermIntegrableOrbit p
  have hTsumIntegrable :
      Integrable (fun y => ∑' h : S.R, fullTerm h y) omegaMeasure :=
    prD_integrable_tsum_of_summable_integral_norm hTermIntegrable hTermNormSummable
  have hOnUnitsTsum (y : S.FS) :
      onUnits (fun t : S.FSˣ => ∑' h : S.R, rowTerm h t) y =
        ∑' h : S.R, fullTerm h y := by
    by_cases hy : IsUnit y <;> simp [onUnits, fullTerm, hy]
  have hTargetIntegrable :
      IntegrableOn (fun y : S.FS => onUnits (fun t : S.FSˣ =>
        ∑' h : S.R, rowTerm h t) y) (omegaAt R 1) (R.sheets.sheet 1) := by
    change Integrable _ omegaMeasure
    exact hTsumIntegrable.congr (Filter.Eventually.of_forall
      (fun y => (hOnUnitsTsum y).symm))
  let termIntegral : S.R → ℂ := fun h => ∫ y, fullTerm h y ∂omegaMeasure
  have hTermIntegralZero : termIntegral 0 = 0 := by
    have hZero : fullTerm 0 = 0 := by
      funext y
      simp [fullTerm, rowTerm, onUnits, hzero]
    simp [termIntegral, hZero]
  have hTermIntegralSummable : Summable termIntegral := by
    have h := hTermNormSummable.of_norm_bounded (fun h =>
      norm_integral_le_integral_norm (fullTerm h))
    simpa [termIntegral] using h
  have hInterchange :
      omegaInt R 1 (fun t : S.FSˣ => ∑' h : S.R, rowTerm h t) =
        ∑' h : S.R, termIntegral h := by
    calc
      _ = ∫ y, onUnits (fun t : S.FSˣ => ∑' h : S.R, rowTerm h t) y
            ∂omegaMeasure := rfl
      _ = ∫ y, ∑' h : S.R, fullTerm h y ∂omegaMeasure := by
        exact integral_congr_ae (Filter.Eventually.of_forall hOnUnitsTsum)
      _ = ∑' h : S.R, termIntegral h :=
        (integral_tsum_of_summable_integral_norm hTermIntegrable hTermNormSummable).symm
  have hSeriesSubtype :
      (∑' h : S.R, termIntegral h) =
        ∑' x : {x : S.R // (x : F) ≠ 0}, termIntegral x.1 := by
    calc
      _ = termIntegral 0 +
          ∑' h : S.R, if h = 0 then 0 else termIntegral h :=
        hTermIntegralSummable.tsum_eq_add_tsum_ite 0
      _ = ∑' h : S.R, if h ∈ {x : S.R | (x : F) ≠ 0}
            then termIntegral h else 0 := by
        rw [hTermIntegralZero, zero_add]
        apply tsum_congr
        intro h
        by_cases hh : h = 0
        · simp [hh]
        · have hval : (h : F) ≠ 0 := by
            intro hz
            exact hh (Subtype.ext hz)
          simp [hh, hval]
      _ = ∑' h : S.R,
          Set.indicator {x : S.R | (x : F) ≠ 0} termIntegral h := by
        apply tsum_congr
        intro h
        simp [Set.indicator]
      _ = ∑' x : {x : S.R // (x : F) ≠ 0}, termIntegral x.1 :=
        (tsum_subtype {x : S.R | (x : F) ≠ 0} termIntegral).symm
  have hSeriesOrbit :
      (∑' x : {x : S.R // (x : F) ≠ 0}, termIntegral x.1) =
        ∑' p : (U.U × S.ExtIdeal) × Gamma S, termIntegral ((e p).1) := by
    exact (Equiv.tsum_eq e (fun x : {x : S.R // (x : F) ≠ 0} => termIntegral x.1)).symm
  have hTripTermIntegralSummable :
      Summable (fun p : (U.U × S.ExtIdeal) × Gamma S => termIntegral ((e p).1)) := by
    have h := hTripTermNorm.of_norm_bounded (fun p =>
      norm_integral_le_integral_norm (fullTerm ((e p).1)))
    simpa [termIntegral] using h
  have hOrbitComplexSummable (ur : U.U × S.ExtIdeal) :
      Summable (fun γ : Gamma S => omegaInt R 1 (orbitFourier ur γ)) := by
    simpa [omegaInt, bridgeOmegaInt, omegaAt, bridgeOmegaAt,
      orbitFourier, mul_assoc] using (hOrbitUnfold ur).2.1
  have hOrbitComplexUnfold (ur : U.U × S.ExtIdeal) :
      (∑' γ : Gamma S, omegaInt R 1 (orbitFourier ur γ)) =
        leadV0 R sd W (orbitT ur) := by
    calc
      _ = ∫ y, onUnits (fun y : S.FSˣ =>
          leadFourier sd W (((orbitK ur * y : S.FSˣ) : S.FS))) y
            ∂(R.sheets.sheet 1) := by
        simpa [omegaInt, bridgeOmegaInt, omegaAt, bridgeOmegaAt,
          bridgeSheetIntegral, orbitFourier, mul_assoc] using (hOrbitUnfold ur).2.2
      _ = leadV0 R sd W (orbitT ur) := hOrbitFourierIntegral ur
  have hTermIntegralOrbit (p : (U.U × S.ExtIdeal) × Gamma S) :
      termIntegral ((e p).1) = orbitCoeff p.1 *
        omegaInt R 1 (orbitFourier p.1 p.2) := by
    calc
      _ = ∫ y, orbitCoeff p.1 * onUnits (orbitFourier p.1 p.2) y
            ∂omegaMeasure := by
        change ∫ y, fullTerm ((e p).1) y ∂omegaMeasure = _
        exact integral_congr_ae (Filter.Eventually.of_forall
          (fun y => congrFun (hFullOrbit p) y))
      _ = orbitCoeff p.1 *
          ∫ y, onUnits (orbitFourier p.1 p.2) y ∂omegaMeasure := by
        rw [integral_const_mul]
      _ = _ := rfl
  have hFinalIdentity :
      omegaInt R 1 (fun t : S.FSˣ => ∑' h : S.R, rowTerm h t) =
        ∑' ur : U.U × S.ExtIdeal,
          orbitCoeff ur * leadV0 R sd W (orbitT ur) := by
    calc
      _ = ∑' h : S.R, termIntegral h := hInterchange
      _ = ∑' x : {x : S.R // (x : F) ≠ 0}, termIntegral x.1 := hSeriesSubtype
      _ = ∑' p : (U.U × S.ExtIdeal) × Gamma S, termIntegral ((e p).1) := hSeriesOrbit
      _ = ∑' ur : U.U × S.ExtIdeal,
          ∑' γ : Gamma S, termIntegral ((e (ur, γ)).1) :=
        hTripTermIntegralSummable.tsum_prod
      _ = ∑' ur : U.U × S.ExtIdeal,
          orbitCoeff ur * leadV0 R sd W (orbitT ur) := by
        apply tsum_congr
        intro ur
        calc
          _ = ∑' γ : Gamma S,
              orbitCoeff ur * omegaInt R 1 (orbitFourier ur γ) :=
            tsum_congr (fun γ => hTermIntegralOrbit (ur, γ))
          _ = orbitCoeff ur *
              ∑' γ : Gamma S, omegaInt R 1 (orbitFourier ur γ) := tsum_mul_left
          _ = orbitCoeff ur * leadV0 R sd W (orbitT ur) := by
            rw [hOrbitComplexUnfold ur]
  refine ⟨?_, ?_, ?_⟩
  · simpa [orbitT] using hFirst
  · simpa [rowTerm, denom] using hTargetIntegrable
  · simpa [orbitCoeff, baseR, orbitT, R.exterior.genR_val, denom, rowTerm] using
      hFinalIdentity

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
