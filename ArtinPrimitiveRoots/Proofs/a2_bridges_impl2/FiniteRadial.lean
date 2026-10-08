import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.LocalRadial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set NumberField IsDedekindDomain Filter
open scoped Topology
open scoped Classical NNReal ENNReal
noncomputable section

namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

theorem bridgeFin_properSpace (v : FinPlace F) : ProperSpace (v.adicCompletion F) := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩

theorem bridgeFin_sixthPower_range_closed (v : FinPlace F) :
    IsClosed (Set.range (fun x : v.adicCompletion F => x ^ 6)) := by
  letI : ProperSpace (v.adicCompletion F) := bridgeFin_properSpace v
  simpa only [Set.image_univ] using
    (isClosedMap_pow (v.adicCompletion F) 6) Set.univ isClosed_univ

def bridgeFinUnitShell (v : FinPlace F) : Set (v.adicCompletion F) :=
  {x | absFin v x = 1}

def bridgeFinShell (v : FinPlace F) (k : ℤ) : Set (v.adicCompletion F) :=
  Set.image (fun x : v.adicCompletion F =>
    ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)
    (bridgeFinUnitShell v)

/-- A cutoff radial majorant at a finite place. -/
def bridgeFinMajorant (v : FinPlace F) (δ : ℝ) (N : ℕ) (x : v.adicCompletion F) : ℝ :=
  if absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N then (absFin v x) ^ δ else 0

theorem bridgeFinMajorant_nonneg (v : FinPlace F) (δ : ℝ) (N : ℕ)
    (x : v.adicCompletion F) : 0 ≤ bridgeFinMajorant v δ N x := by
  unfold bridgeFinMajorant
  split_ifs
  · exact Real.rpow_nonneg (by rw [absFin_eq_norm]; exact norm_nonneg _) δ
  · exact le_rfl

theorem bridgeFinMajorant_measurable (v : FinPlace F) (δ : ℝ) (N : ℕ) :
    Measurable (bridgeFinMajorant v δ N) := by
  have hAbs : Continuous (absFin v) := by
    change Continuous (fun x : v.adicCompletion F => absFin v x)
    simpa only [absFin_eq_norm] using (continuous_norm : Continuous fun x : v.adicCompletion F => ‖x‖)
  have hcut : MeasurableSet {x | absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N} :=
    measurableSet_le hAbs.measurable measurable_const
  have hpow : Measurable (fun x : v.adicCompletion F => absFin v x ^ δ) := by
    fun_prop
  unfold bridgeFinMajorant
  exact Measurable.ite hcut hpow measurable_const

private def bridgeFinWeightedMajorant (v : FinPlace F) (δ : ℝ) (N : ℕ)
    (x : v.adicCompletion F) : ℝ :=
  bridgeFinMajorant v δ N x * (absFin v x)⁻¹

theorem bridgeFinMajorant_mono (v : FinPlace F) (δ : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (x : v.adicCompletion F) : bridgeFinMajorant v δ N x ≤ bridgeFinMajorant v δ M x := by
  have hq : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ N ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ M := pow_le_pow_right₀ hq hNM
  unfold bridgeFinMajorant
  by_cases hN : absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N
  · have hM : absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M := hN.trans hpow
    simp [hN, hM]
  · by_cases hM : absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M
    · simp only [if_neg hN, if_pos hM]
      exact Real.rpow_nonneg (by rw [absFin_eq_norm]; exact norm_nonneg _) δ
    · simp [hN, hM]

private def bridgeFinShellDensityValue (v : FinPlace F) (δ : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if -k ≤ (N : ℤ) then
    ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ *
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k))⁻¹
  else 0

private theorem bridgeFinUniformizer_abs (v : FinPlace F) :
    absFin v (unifLoc v : v.adicCompletion F) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  let K := v.adicCompletion F
  let π : Kˣ := unifLoc v
  let q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)
  have hunif : v.valuation F (unif (F := F) v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (π : K) = algebraMap F K (unif (F := F) v) := by
      change (unifLoc v : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (unif (F := F) v)
      simp [unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif (F := F) v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπnorm : ‖(π : K)‖₊ = q⁻¹ := by
    apply NNReal.coe_injective
    rw [coe_nnnorm, ← absFin_eq_norm]
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hπval]
    have hqexp : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (-1 : ℤ)) = q⁻¹ := by
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
      rw [WithZero.toAdd_unzero_eq_log (by simp)]
      simp [q]
    rw [hqexp]
  calc
    absFin v (π : K) = ‖(π : K)‖ := absFin_eq_norm v (π : K)
    _ = (q⁻¹ : ℝ) := by
      simpa [coe_nnnorm] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hπnorm
    _ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by simp [q]

private theorem bridgeFin_nonzero_dense (v : FinPlace F) :
    ∀ U : Set (v.adicCompletion F), IsOpen U → U.Nonempty →
      ∃ x ∈ U, x ≠ 0 := by
  intro U hU ⟨x, hx⟩
  by_cases hx0 : x ≠ 0
  · exact ⟨x, hx, hx0⟩
  · have hxzero : x = 0 := not_ne_iff.mp hx0
    subst x
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let π : v.adicCompletion F := unifLoc v
    have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hπnorm : ‖π‖ < 1 := by
      rw [← absFin_eq_norm v π, bridgeFinUniformizer_abs]
      exact inv_lt_one_of_one_lt₀ hq
    have hpow : Tendsto (fun n : ℕ => π ^ n) atTop (𝓝 (0 : v.adicCompletion F)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπnorm
    have hev : ∀ᶠ n : ℕ in atTop, π ^ n ∈ Metric.ball (0 : v.adicCompletion F) r :=
      hpow.eventually (Metric.ball_mem_nhds _ hr)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hn := hN N le_rfl
    have hne : π ^ N ≠ 0 := pow_ne_zero N (Units.ne_zero (unifLoc v))
    exact ⟨π ^ N, hball hn, hne⟩

theorem bridgeFin_mulHaar_openPos (v : FinPlace F) (μ : LocHaar v) :
    Measure.IsOpenPosMeasure (ArtinPrimitiveRoots.A1.Theta.mulHaarFin μ) := by
  let f : v.adicCompletion F → ℝ≥0∞ := fun x => ENNReal.ofReal ((absFin v x)⁻¹)
  have hAbs : Continuous (absFin v) := by
    change Continuous (fun x : v.adicCompletion F => absFin v x)
    simpa only [absFin_eq_norm] using (continuous_norm : Continuous fun x : v.adicCompletion F => ‖x‖)
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.continuous_ofReal.measurable.comp (measurable_inv.comp hAbs.measurable)
  have hcont : ∀ x, x ≠ 0 → ContinuousAt f x := by
    intro x hx
    have hp : 0 < absFin v x := absFin_pos hx
    dsimp [f]
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (ContinuousAt.inv₀ (hAbs.continuousAt (x := x)) hp.ne')
  have hpos : ∀ x, x ≠ 0 → f x ≠ 0 := by
    intro x hx
    have hp : 0 < absFin v x := absFin_pos hx
    dsimp [f]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hp)).ne'
  letI : Measure.IsOpenPosMeasure μ.μ := μ.isHaar.toIsOpenPosMeasure
  simpa [ArtinPrimitiveRoots.A1.Theta.mulHaarFin, f] using
    (bridgeWithDensity_openPos_of_nonzero_dense μ.μ f hf hcont hpos
      (bridgeFin_nonzero_dense v))

private theorem bridgeFinUnitShell_compact (v : FinPlace F) :
    IsCompact (bridgeFinUnitShell v) := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  let hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  letI : ProperSpace K := hproper
  have hO : (O : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hOcomp : IsCompact (O : Set K) := by
    rw [hO]
    exact hproper.isCompact_closedBall 0 1
  have hnormcont : Continuous (fun x : K => absFin v x) := by
    simpa only [absFin_eq_norm] using (continuous_norm : Continuous fun x : K => ‖x‖)
  have hUclosed : IsClosed (bridgeFinUnitShell v) := by
    exact isClosed_singleton.preimage hnormcont
  have hUsub : bridgeFinUnitShell v ⊆ (O : Set K) := by
    intro x hx
    rw [hO]
    rw [Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm, hx]
  exact hOcomp.of_isClosed_subset hUclosed hUsub

private theorem bridgeFinShell_compact (v : FinPlace F) (k : ℤ) :
    IsCompact (bridgeFinShell v k) := by
  apply (bridgeFinUnitShell_compact v).image
  fun_prop

private theorem bridgeFinShell_real_measure (v : FinPlace F) (μ : LocHaar v) (k : ℤ) :
    μ.μ.real (bridgeFinShell v k) =
      absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        μ.μ.real (bridgeFinUnitShell v) := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ k
  let U := bridgeFinUnitShell v
  have hUmeas : MeasurableSet U := (bridgeFinUnitShell_compact v).measurableSet
  have hSmeas : MeasurableSet (bridgeFinShell v k) := (bridgeFinShell_compact v k).measurableSet
  have hpre : (fun x : v.adicCompletion F => ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ⁻¹' U =
      bridgeFinShell v k := by
    ext x
    change (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈ U) ↔
      ∃ y ∈ U, ((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y = x
    constructor
    · intro hx
      refine ⟨((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x, hx, ?_⟩
      change (a : v.adicCompletion F) *
        (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) = x
      calc
        _ = ((a : v.adicCompletion F) * ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * x := by ac_rfl
        _ = x := by
          have ha : (a : v.adicCompletion F) * ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
            have hu : a * a⁻¹ = (1 : (v.adicCompletion F)ˣ) := by group
            simpa using congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hu
          rw [ha]
          simp
    · rintro ⟨y, hy, rfl⟩
      change (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((a : v.adicCompletion F) * y)) ∈ U
      have hcancel : ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          ((a : v.adicCompletion F) * y) = y := by
        calc
          _ = (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (a : v.adicCompletion F)) * y := by ac_rfl
          _ = y := by
            have hb : ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (a : v.adicCompletion F) = 1 := by
              have hu : a⁻¹ * a = (1 : (v.adicCompletion F)ˣ) := by group
              simpa using congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hu
            rw [hb]
            simp
      rw [hcancel]
      exact hy
  let f : v.adicCompletion F → ℝ := U.indicator (fun _ => 1)
  have hleft : (∫ x, f (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ∂μ.μ) =
      μ.μ.real (bridgeFinShell v k) := by
    have hfun : (fun x => f (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)) =
        (bridgeFinShell v k).indicator (fun _ => 1) := by
      funext x
      change (if ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈ U then 1 else 0) =
        (if x ∈ bridgeFinShell v k then 1 else 0)
      have hxmem : (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈ U) ↔
          x ∈ bridgeFinShell v k := by
        have hx := congrArg (fun T : Set (v.adicCompletion F) => x ∈ T) hpre
        exact Iff.of_eq hx
      have hxmem' : ((a : v.adicCompletion F)⁻¹ * x ∈ U) ↔
          x ∈ bridgeFinShell v k := by simpa only [Units.val_inv_eq_inv_val] using hxmem
      simp [hxmem']
    rw [hfun]
    exact integral_indicator_one hSmeas
  have hright : (∫ x, f x ∂μ.μ) = μ.μ.real U := by
    exact integral_indicator_one hUmeas
  have hscale := LocHaar.integral_comp_mul μ (a⁻¹) f
  have hinv : absFin v (a⁻¹ : (v.adicCompletion F)ˣ) = (absFin v a)⁻¹ := by
    let A : ℝ := absFin v a
    let B : ℝ := absFin v (a⁻¹ : (v.adicCompletion F)ˣ)
    have hprod : absFin v a * absFin v (a⁻¹ : (v.adicCompletion F)ˣ) = 1 := by
      simpa [absFin_eq_norm] using (absFin_mul v a a⁻¹).symm
    have hAB : A = B⁻¹ := eq_inv_of_mul_eq_one_left hprod
    calc
      B = (B⁻¹)⁻¹ := by simp
      _ = A⁻¹ := by rw [← hAB]
  rw [hleft, hright, hinv, inv_inv, smul_eq_mul] at hscale
  simpa [a] using hscale

private theorem bridgeFinShell_radius (v : FinPlace F) (k : ℤ) :
    absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  let π := unifLoc v
  let q : ℝ := Ideal.absNorm v.asIdeal
  calc
    absFin v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        ‖((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ :=
      absFin_eq_norm v _
    _ = ‖(π : v.adicCompletion F)‖ ^ k := by simp
    _ = (absFin v (π : v.adicCompletion F)) ^ k := by rw [← absFin_eq_norm]
    _ = (q⁻¹) ^ k := by rw [bridgeFinUniformizer_abs]
    _ = q ^ (-k) := by rw [inv_zpow, zpow_neg]

private theorem bridgeFinShell_mem_radius (v : FinPlace F) (k : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ bridgeFinShell v k) :
    absFin v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rcases hx with ⟨y, hy, rfl⟩
  calc
    absFin v (((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) =
        absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * absFin v y := by
          simp only [absFin_eq_norm, norm_mul]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
      have hya : absFin v y = 1 := by simpa [bridgeFinUnitShell] using hy
      rw [hya, bridgeFinShell_radius]
      simp

private theorem bridgeFinUnitShell_real_measure_le_one (v : FinPlace F) (μ : LocHaar v) :
    μ.μ.real (bridgeFinUnitShell v) ≤ 1 := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have hO : (O : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hsub : bridgeFinUnitShell v ⊆ (O : Set K) := by
    intro x hx
    rw [hO, Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm, hx]
  have hfinite : μ.μ (O : Set K) ≠ ⊤ := by rw [μ.norm_O]; simp
  calc
    μ.μ.real (bridgeFinUnitShell v) ≤ μ.μ.real (O : Set K) := measureReal_mono hsub hfinite
    _ = 1 := by
      change (μ.μ (v.adicCompletionIntegers F : Set K)).toReal = 1
      rw [μ.norm_O]
      simp

private theorem bridgeFinWeightedMajorant_eq_shell_value (v : FinPlace F) (δ : ℝ)
    (N : ℕ) (k : ℤ) {x : v.adicCompletion F} (hx : x ∈ bridgeFinShell v k) :
    bridgeFinWeightedMajorant v δ N x = bridgeFinShellDensityValue v δ N k := by
  have hr := bridgeFinShell_mem_radius v k hx
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hcut : (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℕ) ↔ -k ≤ (N : ℤ) := by
    simpa [zpow_natCast] using
      (zpow_le_zpow_iff_right₀ hq :
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) ≤
          (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) ↔ -k ≤ (N : ℤ))
  dsimp [bridgeFinWeightedMajorant, bridgeFinMajorant]
  rw [bridgeFinShell_mem_radius v k hx]
  by_cases h : -k ≤ (N : ℤ)
  · rw [if_pos (hcut.mpr h)]
    simp [bridgeFinShellDensityValue, h]
  · have hnot : ¬ (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℕ) := fun hle => h (hcut.mp hle)
    rw [if_neg hnot]
    simp [bridgeFinShellDensityValue, h]

private theorem bridgeFin_rpow_shell_summable_term (v : FinPlace F) (δ : ℝ)
    (k : ℕ) :
    ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))) ^ δ =
      (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ δ) ^ k := by
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hq' : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  calc
    (q ^ (-(k : ℤ))) ^ δ = ((q⁻¹) ^ k) ^ δ := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    _ = (q⁻¹) ^ ((k : ℝ) * δ) := (Real.rpow_natCast_mul hq' k δ).symm
    _ = (q⁻¹) ^ (δ * (k : ℝ)) := by congr 1 <;> ring
    _ = ((q⁻¹) ^ δ) ^ k := Real.rpow_mul_natCast hq' δ k

private theorem bridgeFin_rpow_shell_int_nonneg (v : FinPlace F) (δ : ℝ)
    (k : ℤ) (hk : 0 ≤ k) :
    ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ =
      (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ δ) ^ Int.toNat k := by
  have hk' : (Int.toNat k : ℤ) = k := Int.toNat_of_nonneg hk
  simpa [hk'] using bridgeFin_rpow_shell_summable_term v δ (Int.toNat k)

private theorem bridgeFinWeighted_integral_shell_bound (v : FinPlace F) (μ : LocHaar v)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (k : ℤ) :
    (∫ x in bridgeFinShell v k, ‖bridgeFinWeightedMajorant v δ N x‖ ∂μ.μ) ≤
      if -k ≤ (N : ℤ) then
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ else 0 := by
  let U := bridgeFinUnitShell v
  let r : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-k)
  let c : ℝ := bridgeFinShellDensityValue v δ N k
  have hq : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact lt_trans (by norm_num) hq1
  have hc : 0 ≤ c := by
    dsimp [c, bridgeFinShellDensityValue]
    split_ifs <;> positivity
  have hval : ∀ x ∈ bridgeFinShell v k, bridgeFinWeightedMajorant v δ N x = c := by
    intro x hx
    simpa [c] using bridgeFinWeightedMajorant_eq_shell_value v δ N k hx
  have hconstInt : IntegrableOn (fun _ : v.adicCompletion F => c)
      (bridgeFinShell v k) μ.μ :=
    integrableOn_const (bridgeFinShell_compact v k).measure_lt_top.ne
  have hconstEq : EqOn (fun _ : v.adicCompletion F => c)
      (bridgeFinWeightedMajorant v δ N) (bridgeFinShell v k) := by
    intro x hx
    exact (hval x hx).symm
  have hGint : IntegrableOn (bridgeFinWeightedMajorant v δ N)
      (bridgeFinShell v k) μ.μ :=
    hconstInt.congr_fun hconstEq (bridgeFinShell_compact v k).measurableSet
  have hnormEq : EqOn (fun x => ‖bridgeFinWeightedMajorant v δ N x‖)
      (fun _ => c) (bridgeFinShell v k) := by
    intro x hx
    change ‖bridgeFinWeightedMajorant v δ N x‖ = c
    rw [hval x hx, Real.norm_eq_abs, abs_of_nonneg hc]
  have hI : (∫ x in bridgeFinShell v k,
      ‖bridgeFinWeightedMajorant v δ N x‖ ∂μ.μ) = μ.μ.real (bridgeFinShell v k) * c := by
    calc
      _ = ∫ x in bridgeFinShell v k, c ∂μ.μ :=
        setIntegral_congr_fun (bridgeFinShell_compact v k).measurableSet hnormEq
      _ = μ.μ.real (bridgeFinShell v k) * c := by simp [setIntegral_const, smul_eq_mul]
  have hmeasure : μ.μ.real (bridgeFinShell v k) =
      r * μ.μ.real U := by
    rw [bridgeFinShell_real_measure v μ k, bridgeFinShell_radius]
  by_cases hcut : -k ≤ (N : ℤ)
  · rw [hI, hmeasure]
    dsimp [c, bridgeFinShellDensityValue]
    simp only [if_pos hcut]
    have hr : 0 < r := zpow_pos hq _
    have hcancel : r * μ.μ.real U * (r ^ δ * r⁻¹) = r ^ δ * μ.μ.real U := by
      calc
        r * μ.μ.real U * (r ^ δ * r⁻¹) = (r * r⁻¹) * r ^ δ * μ.μ.real U := by ring
        _ = r ^ δ * μ.μ.real U := by rw [mul_inv_cancel₀ hr.ne']; ring
    rw [hcancel]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt hr) δ)
      (bridgeFinUnitShell_real_measure_le_one v μ)
  · rw [hI, hmeasure]
    dsimp [c, bridgeFinShellDensityValue]
    simp [hcut]

private theorem bridgeFin_abs_continuous (v : FinPlace F) :
    Continuous (fun x : v.adicCompletion F => absFin v x) := by
  have hEq : (fun x : v.adicCompletion F => absFin v x) = fun x => ‖x‖ := by
    funext x
    exact absFin_eq_norm v x
  rw [hEq]
  exact continuous_norm

private theorem sheetHypFin_continuousOn_nonzero (v : FinPlace F) (δ : ℝ)
    (f : v.adicCompletion F → ℂ) (hf : SheetHypFin v δ f) :
    ContinuousOn f {x | x ≠ 0} := by
  intro x hx
  rcases hf.1 x hx with ⟨U, hUopen, hxU, hconstant⟩
  have hEq : (fun _ : v.adicCompletion F => f x) =ᶠ[𝓝 x] f := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact (hconstant y hy).symm
  exact (continuousAt_const.congr hEq).continuousWithinAt

theorem bridgeSheetHypFin_measurable (v : FinPlace F) (δ : ℝ)
    (f : v.adicCompletion F → ℂ) (hf : SheetHypFin v δ f) : Measurable f := by
  refine measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion F) ?_
  convert sheetHypFin_continuousOn_nonzero v δ f hf using 1
  ext x
  simp

private theorem bridgeFinAnnulus_compact (v : FinPlace F) (R : ℝ) :
    IsCompact {x : v.adicCompletion F | 1 ≤ absFin v x ∧ absFin v x ≤ R} := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  let hp : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  letI : ProperSpace K := hp
  have habs : Continuous (absFin v) := bridgeFin_abs_continuous v
  have hclosed : IsClosed {x : K | 1 ≤ absFin v x ∧ absFin v x ≤ R} := by
    exact (isClosed_le continuous_const habs).inter (isClosed_le habs continuous_const)
  have hsubset : {x : K | 1 ≤ absFin v x ∧ absFin v x ≤ R} ⊆ Metric.closedBall (0 : K) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm]
    exact hx.2
  exact (hp.isCompact_closedBall 0 R).of_isClosed_subset hclosed hsubset

theorem bridgeFin_sheetHyp_radial_bound (v : FinPlace F) (δ : ℝ) (hδ : 0 < δ)
    (f : v.adicCompletion F → ℂ) (hf : SheetHypFin v δ f) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, x ≠ 0 → ‖f x‖ ≤ C * bridgeFinMajorant v δ N x := by
  have hcont : ContinuousOn f {x | x ≠ 0} := sheetHypFin_continuousOn_nonzero v δ f hf
  rcases hf with ⟨hloc, hrest⟩
  rcases hrest with ⟨⟨Cs, hsupport⟩, ⟨Cl, hsmall⟩⟩
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let T : ℝ := max Cs 1
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hq
  have hev : ∀ᶠ n : ℕ in atTop, T ≤ q ^ n := (tendsto_atTop.1 hpow) T
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hTN : T ≤ q ^ N := hN N le_rfl
  let Annulus : Set (v.adicCompletion F) :=
    {x | 1 ≤ absFin v x ∧ absFin v x ≤ q ^ N}
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  let hp : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  letI : ProperSpace K := hp
  have habs_cont : Continuous (absFin v) := bridgeFin_abs_continuous v
  have hAnn_closed : IsClosed Annulus := by
    dsimp [Annulus]
    exact (isClosed_le continuous_const habs_cont).inter (isClosed_le habs_cont continuous_const)
  have hAnn_ball : Annulus ⊆ Metric.closedBall (0 : K) (q ^ N) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm]
    exact hx.2
  have hAnn_compact : IsCompact Annulus := by
    exact (hp.isCompact_closedBall 0 (q ^ N)).of_isClosed_subset hAnn_closed hAnn_ball
  have hAnn_nonzero : Annulus ⊆ {x | x ≠ 0} := by
    intro x hx hzero
    subst x
    have h : (1 : ℝ) ≤ absFin v 0 := hx.1
    simp [absFin] at h
    norm_num at h
  have hAnn_cont : ContinuousOn f Annulus := hcont.mono hAnn_nonzero
  have hIm_compact : IsCompact (f '' Annulus) := hAnn_compact.image_of_continuousOn hAnn_cont
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hIm_compact.isBounded
  let Cann : ℝ := max B 1
  have hBann : ∀ x ∈ Annulus, ‖f x‖ ≤ Cann := by
    intro x hx
    have him : f x ∈ f '' Annulus := ⟨x, hx, rfl⟩
    have hball := hB him
    have hn : ‖f x‖ ≤ B := by simpa [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left B 1)
  let C : ℝ := max (max Cl 0) Cann
  have hCnonneg : 0 ≤ C := le_trans (le_max_right Cl 0) (le_max_left (max Cl 0) Cann)
  have hCsmall : Cl ≤ C := le_trans (le_max_left Cl 0) (le_max_left (max Cl 0) Cann)
  have hCann : Cann ≤ C := le_max_right (max Cl 0) Cann
  refine ⟨N, C, hCnonneg, ?_⟩
  intro x hx
  by_cases hcut : absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N
  · simp only [bridgeFinMajorant, if_pos hcut]
    by_cases hsmall' : absFin v x ≤ 1
    · exact le_trans (hsmall x hx hsmall')
        (mul_le_mul_of_nonneg_right hCsmall (Real.rpow_nonneg (absFin_pos hx).le δ))
    · have hlarge : 1 ≤ absFin v x := le_of_lt (lt_of_not_ge hsmall')
      have hxAnn : x ∈ Annulus := ⟨hlarge, by simpa [q] using hcut⟩
      have hrad : 1 ≤ (absFin v x) ^ δ := Real.one_le_rpow hlarge hδ.le
      exact (hBann x hxAnn).trans <|
        le_trans hCann (le_mul_of_one_le_right hCnonneg hrad)
  · have hCs : Cs < absFin v x := lt_of_le_of_lt (le_trans (le_max_left Cs 1) hTN)
        (lt_of_not_ge hcut)
    have hfzero : f x = 0 := hsupport x hCs
    simp [bridgeFinMajorant, hcut, hfzero]

private theorem bridgeFinShell_cover (v : FinPlace F) {x : v.adicCompletion F} (hx : x ≠ 0) :
    ∃ k : ℤ, x ∈ bridgeFinShell v k := by
  have hvx : Valued.v x ≠ 0 := by
    intro h
    have hzero : absFin v x = 0 := by simp [absFin, h]
    have hpos := absFin_pos (v := v) hx
    linarith
  let n : ℤ := -WithZero.log (Valued.v x)
  have hxval : Valued.v x = WithZero.exp (-n) := by
    simpa [n] using (WithZero.exp_log hvx).symm
  let π : (v.adicCompletion F)ˣ := unifLoc v
  let u : v.adicCompletion F := ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (π : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (unif (F := F) v) := by
      simp [π, unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif (F := F) v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have huval : Valued.v u = 1 := by
    dsimp [u]
    calc
      Valued.v (((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) =
          Valued.v (π : v.adicCompletion F) ^ (-n) * Valued.v x := by simp
      _ = WithZero.exp (-1 : ℤ) ^ (-n) * WithZero.exp (-n) := by rw [hπval, hxval]
      _ = 1 := by
        rw [← WithZero.exp_zsmul]
        rw [show (-n : ℤ) • (-1 : ℤ) = n by simp, ← WithZero.exp_add]
        simp
  have hu : absFin v u = 1 := by
    rw [absFin_eq_norm, FinitePlace.norm_def, huval]
    simp
  refine ⟨n, ?_⟩
  refine ⟨u, hu, ?_⟩
  have hunit : π ^ n * π ^ (-n) = 1 := by group
  have hval : ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] using
      congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hunit
  change ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u = x
  dsimp [u]
  calc
    _ = (((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * x := by ac_rfl
    _ = x := by rw [hval]; simp

theorem bridgeFinMajorant_integrable (v : FinPlace F) (μ : LocHaar v)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    Integrable (bridgeFinMajorant v δ N) (ArtinPrimitiveRoots.A1.Theta.mulHaarFin μ) := by
  let K := v.adicCompletion F
  let q : ℝ := Ideal.absNorm v.asIdeal
  let g : K → ℝ := bridgeFinWeightedMajorant v δ N
  let ρ : ℝ := (q⁻¹) ^ δ
  let B : ℤ → ℝ := fun k =>
    if 0 ≤ k then ρ ^ Int.toNat k
    else if -(N : ℤ) ≤ k then (q ^ N) ^ δ else 0
  let I : ℤ → ℝ := fun k => ∫ x in bridgeFinShell v k, ‖g x‖ ∂μ.μ
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hqinvpos : 0 < q⁻¹ := inv_pos.mpr hqpos
  have hqinvlt : q⁻¹ < 1 := (inv_lt_one₀ hqpos).2 hq
  have hρpos : 0 ≤ ρ := by positivity
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one hqinvpos.le hqinvlt hδ
  have hgeom : Summable (fun n : ℕ => ρ ^ n) :=
    summable_geometric_of_lt_one hρpos hρlt
  have hBsum : Summable B := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · simpa [B, ρ, Int.toNat_natCast, hqpos.ne'] using hgeom
    · apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
      intro n hn
      have hnN : N + 1 ≤ n := Nat.le_of_not_gt (by simpa [Finset.mem_range] using hn)
      have hnonneg : ¬ (0 ≤ -(n : ℤ)) := by omega
      have hfalse : ¬ (-(N : ℤ) ≤ -(n : ℤ)) := by omega
      dsimp [B]
      rw [if_neg hnonneg, if_neg hfalse]
  have hIntle : ∀ k : ℤ, I k ≤ B k := by
    intro k
    have hlocal := bridgeFinWeighted_integral_shell_bound v μ δ hδ N k
    have hlocal' : I k ≤ if -k ≤ (N : ℤ) then
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ else 0 := by
      simpa [I, g] using hlocal
    have hrad : (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) ≤ q ^ (N : ℤ) ↔ -k ≤ (N : ℤ) := by
      exact zpow_le_zpow_iff_right₀ hq
    by_cases hk : 0 ≤ k
    · have hcut : -k ≤ (N : ℤ) := by omega
      have hterm : ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ = ρ ^ Int.toNat k := by
        simpa [q, ρ, Int.toNat_of_nonneg hk] using bridgeFin_rpow_shell_int_nonneg v δ k hk
      have hBeq : B k = ρ ^ Int.toNat k := by simp [B, hk]
      have hlocalCase : I k ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ := by
        simpa [hcut] using hlocal'
      rw [hBeq]
      exact hlocalCase.trans_eq hterm
    · by_cases hcut : -k ≤ (N : ℤ)
      · have hradle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) ≤ q ^ N := by
          simpa [q, zpow_natCast] using hrad.mpr hcut
        have hpowle : ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ ≤ (q ^ N) ^ δ :=
          Real.rpow_le_rpow (by positivity) hradle hδ.le
        have hNle : -(N : ℤ) ≤ k := by omega
        have hBeq : B k = (q ^ N) ^ δ := by simp [B, hk, hNle]
        have hlocalCase : I k ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) ^ δ := by
          simpa [hcut] using hlocal'
        exact hlocalCase.trans (hpowle.trans_eq hBeq.symm)
      · have hNnot : ¬ (-(N : ℤ) ≤ k) := by omega
        have hBeq : B k = 0 := by simp [B, hk, hNnot]
        have hlocalCase : I k ≤ 0 := by simpa [hcut] using hlocal'
        rw [hBeq]
        exact hlocalCase
  have hIshell : ∀ k : ℤ, IntegrableOn g (bridgeFinShell v k) μ.μ := by
    intro k
    let c := bridgeFinShellDensityValue v δ N k
    have hc : 0 ≤ c := by
      dsimp [c, bridgeFinShellDensityValue]
      split_ifs <;> positivity
    have hval : ∀ x ∈ bridgeFinShell v k, g x = c := by
      intro x hx
      simpa [g, c] using bridgeFinWeightedMajorant_eq_shell_value v δ N k hx
    have hconst : IntegrableOn (fun _ : K => c) (bridgeFinShell v k) μ.μ :=
      integrableOn_const (bridgeFinShell_compact v k).measure_lt_top.ne
    apply hconst.congr_fun
      (fun x hx => (hval x hx).symm) (bridgeFinShell_compact v k).measurableSet
  have hIntSummable : Summable I := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg (g x)) hIntle hBsum
  have hcover : (⋃ k : ℤ, bridgeFinShell v k) = {x | x ≠ 0} := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
      intro hx0
      subst x
      have hr := bridgeFinShell_mem_radius v k hx
      have hzero : absFin v (0 : K) = 0 := by simp [absFin]
      rw [hzero] at hr
      have hradpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := zpow_pos hqpos _
      exact (ne_of_gt hradpos) hr.symm
    · intro hx
      obtain ⟨k, hk⟩ := bridgeFinShell_cover v hx
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hnonzero : IntegrableOn g {x : K | x ≠ 0} μ.μ := by
    rw [← hcover]
    exact integrableOn_iUnion_of_summable_integral_norm hIshell hIntSummable
  have hzero : IntegrableOn g ({(0 : K)} : Set K) μ.μ := by
    have h0 : IntegrableOn (fun _ : K => (0 : ℝ)) ({(0 : K)} : Set K) μ.μ :=
      integrableOn_zero
    apply h0.congr_fun
      (fun x hx => ?_) (measurableSet_singleton (0 : K))
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    simp [g, bridgeFinWeightedMajorant, bridgeFinMajorant, absFin]
  have hsplit : {x : K | x ≠ 0} ∪ ({(0 : K)} : Set K) = univ := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  have hg_int : Integrable g μ.μ := by
    rw [← integrableOn_univ, ← hsplit]
    exact hnonzero.union hzero
  have habs_cont : Continuous (fun x : K => absFin v x) := by
    simpa only [absFin_eq_norm] using (continuous_norm : Continuous fun x : K => ‖x‖)
  have hinv_meas : Measurable (fun x : K => (absFin v x)⁻¹) :=
    measurable_inv.comp habs_cont.measurable
  have hden : Measurable fun x : K => ENNReal.ofReal ((absFin v x)⁻¹) :=
    ENNReal.continuous_ofReal.measurable.comp hinv_meas
  have hden_finite : ∀ᵐ x : K ∂μ.μ, ENNReal.ofReal ((absFin v x)⁻¹) < ⊤ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  have hpow_cont : Continuous (fun x : K => (absFin v x) ^ δ) :=
    (Real.continuous_rpow_const hδ.le).comp habs_cont
  have hcut_meas : MeasurableSet {x : K | absFin v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N} :=
    measurableSet_le habs_cont.measurable measurable_const
  have hmajor_meas : Measurable (bridgeFinMajorant v δ N) := by
    unfold bridgeFinMajorant
    exact Measurable.ite hcut_meas hpow_cont.measurable measurable_const
  have hinv_meas : Measurable (fun x : K => (absFin v x)⁻¹) :=
    measurable_inv.comp habs_cont.measurable
  have hden : Measurable fun x : K => ENNReal.ofReal ((absFin v x)⁻¹) := by
    exact ENNReal.measurable_ofReal.comp hinv_meas
  have hweight : (fun x : K => bridgeFinMajorant v δ N x *
      (ENNReal.ofReal ((absFin v x)⁻¹)).toReal) =ᵐ[μ.μ] g := by
    filter_upwards with x
    have hnormnonneg : 0 ≤ absFin v x := by rw [absFin_eq_norm]; exact norm_nonneg _
    have hnonneg : 0 ≤ (absFin v x)⁻¹ := inv_nonneg.mpr hnormnonneg
    simp [g, bridgeFinWeightedMajorant, ENNReal.toReal_ofReal hnonneg]
  have hmul : Integrable (bridgeFinMajorant v δ N)
      (μ.μ.withDensity fun x : K => ENNReal.ofReal ((absFin v x)⁻¹)) :=
    (integrable_withDensity_iff (μ := μ.μ) hden hden_finite).2 (hg_int.congr hweight.symm)
  simpa [ArtinPrimitiveRoots.A1.Theta.mulHaarFin] using hmul

end ArtinPrimitiveRoots.A2
