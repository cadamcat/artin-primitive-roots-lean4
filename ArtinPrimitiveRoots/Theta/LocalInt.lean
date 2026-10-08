import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Shared
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

open MeasureTheory Filter

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-LOCAL-INT -/

open MeasureTheory Filter

section LocalInt

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- `q_v = N𝔭_v`. -/
def qv (v : FinPlace F) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

/-- **jq:haar-exists** (Mathlib `Measure.addHaarMeasure` on the compact open `O_v`; compactness of
`O_v` from TauCeti). -/
theorem LocHaar.nonempty (v : FinPlace F) : Nonempty (LocHaar v) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) := by
    exact Valued.isOpen_valuationSubring K
  let U : TopologicalSpace.PositiveCompacts K :=
    { toCompacts := ⟨v.adicCompletionIntegers F, hcompact⟩
      interior_nonempty' := by
        rw [hopen.interior_eq]
        exact ⟨0, by simp [HeightOneSpectrum.mem_adicCompletionIntegers]⟩ }
  refine ⟨⟨Measure.addHaarMeasure U, Measure.isAddHaarMeasure_addHaarMeasure U, ?_⟩⟩
  simpa [U] using (Measure.addHaarMeasure_self (K₀ := U))

theorem qv_gt_one (v : FinPlace F) : 1 < qv v := by
  unfold qv
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem absFin_eq_norm (v : FinPlace F) (x : v.adicCompletion F) :
    absFin v x = ‖x‖ := by
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

theorem absFin_pos {v : FinPlace F} {x : v.adicCompletion F} (hx : x ≠ 0) :
    0 < absFin v x := by
  rw [absFin_eq_norm]
  exact norm_pos_iff.mpr hx

theorem absFin_mul (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
    absFin v (x * y) = absFin v x * absFin v y := by
  simp only [absFin_eq_norm, norm_mul]

private theorem valued_lt_one_iff_ball_one (x : v.adicCompletion F) :
    Valued.v x < 1 ↔ x ∈ ball v 1 := by
  change Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1)
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · lift Valued.v x to ℤ using hx with n hn
    simp only [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private def localMulAddEquiv {K : Type} [NormedField K] (y : Kˣ) : K ≃ₜ+ K :=
  (ContinuousLinearEquiv.smulLeft (R₁ := K) y).toContinuousAddEquiv

private noncomputable def localHaarFactor {K : Type} [NormedField K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] : Kˣ →* NNReal where
  toFun y := addEquivAddHaarChar (localMulAddEquiv y)
  map_one' := by
    have h : localMulAddEquiv (1 : Kˣ) = ContinuousAddEquiv.refl K := by
      ext t
      change (1 : K) • t = t
      exact one_smul K t
    rw [h, addEquivAddHaarChar_refl]
  map_mul' x y := by
    have h : localMulAddEquiv (x * y) =
        (localMulAddEquiv y).trans (localMulAddEquiv x) := by
      ext t
      change ((x * y : K) • t) = (x : K) • ((y : K) • t)
      simpa only [smul_eq_mul] using (mul_assoc (x : K) (y : K) t)
    rw [h]
    rw [addEquivAddHaarChar_trans, mul_comm]

private theorem locHaar_regular (μ : LocHaar v) : MeasureTheory.Measure.Regular μ.μ := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let _ : ProperSpace K := hproper
  haveI : SecondCountableTopology K := inferInstance
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) :=
    Valued.isOpen_valuationSubring K
  let U : TopologicalSpace.PositiveCompacts K :=
    { toCompacts := ⟨v.adicCompletionIntegers F, hcompact⟩
      interior_nonempty' := by
        rw [hopen.interior_eq]
        exact ⟨0, by simp [HeightOneSpectrum.mem_adicCompletionIntegers]⟩ }
  let ν : Measure K := Measure.addHaarMeasure U
  have hscale : μ.μ = Measure.addHaarScalarFactor μ.μ ν • ν := by
    exact Measure.isAddLeftInvariant_eq_smul μ.μ ν
  have hνO : ν (v.adicCompletionIntegers F : Set K) = 1 := by
    simpa [ν, U] using (Measure.addHaarMeasure_self (K₀ := U))
  have hc : Measure.addHaarScalarFactor μ.μ ν = 1 := by
    have hO := congrArg (fun ρ : Measure K => ρ (v.adicCompletionIntegers F : Set K)) hscale
    have hO' : (1 : ENNReal) = (Measure.addHaarScalarFactor μ.μ ν : ENNReal) := by
      simpa [μ.norm_O, hνO] using hO
    exact_mod_cast hO'.symm
  have hμν : μ.μ = ν := by
    rw [hscale, hc, one_smul]
  rw [hμν]
  simpa [ν] using
    (inferInstance : MeasureTheory.Measure.Regular (Measure.addHaarMeasure U))

private theorem locHaar_ball_one (μ : LocHaar v) :
    μ.μ (ball v 1) = (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let H : AddSubgroup O := (IsLocalRing.maximalIdeal O).toAddSubgroup
  have hOopen : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hOmeas : MeasurableSet (O : Set K) := hOopen.measurableSet
  have hballopen : IsOpen (ball v 1) := by
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hmax (a : O) : a ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (a : K) < 1 := by
    change a ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring) ↔
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (a : K) < 1
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))) (a := a)
  have hHpre : (H : Set O) = (Subtype.val : O → K) ⁻¹' ball v 1 := by
    ext a
    change a ∈ IsLocalRing.maximalIdeal O ↔ (a : K) ∈ ball v 1
    exact (hmax a).trans (valued_lt_one_iff_ball_one (a : K))
  let f : O →+ K :=
    { toFun := fun a => (a : K)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : MeasurableEmbedding f := by
    change MeasurableEmbedding (Subtype.val : O → K)
    exact MeasurableEmbedding.subtype_coe hOmeas
  have hHmeas : MeasurableSet (H : Set O) := by
    rw [hHpre]
    exact hballopen.measurableSet.preimage hf.measurable
  let μO : Measure O := μ.μ.comap f
  haveI : MeasureTheory.Measure.IsAddLeftInvariant μO :=
    MeasureTheory.Measure.IsAddLeftInvariant.comap μ.μ hf
  have hμO_univ : μO Set.univ = 1 := by
    change μ.μ.comap f (Set.univ : Set O) = 1
    rw [hf.comap_apply]
    rw [Set.image_univ]
    simpa [f, Subtype.range_coe] using μ.norm_O
  have hball_subset : ball v 1 ⊆ Set.range f := by
    intro x hx
    have hxO : x ∈ O := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hx.trans (by simp)
    exact ⟨⟨x, hxO⟩, rfl⟩
  have himage : f '' (H : Set O) = ball v 1 := by
    rw [hHpre]
    exact Set.image_preimage_eq_of_subset hball_subset
  have hμOH : μO H = μ.μ (ball v 1) := by
    change μ.μ.comap f (H : Set O) = μ.μ (ball v 1)
    rw [hf.comap_apply]
    rw [himage]
  haveI : Finite (O ⧸ H) := by
    change Finite (IsLocalRing.ResidueField O)
    exact Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  haveI : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hindex : H.index = Ideal.absNorm v.asIdeal := by
    rw [AddSubgroup.index_eq_card]
    change Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = Ideal.absNorm v.asIdeal
    calc
      Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = Nat.card (𝓞 F ⧸ v.asIdeal) :=
        Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := F)).symm.toEquiv
      _ = Ideal.absNorm v.asIdeal := by
        simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hidxvol : (H.index : ENNReal) * μO H = 1 := by
    simpa [hμO_univ] using
      (MeasureTheory.AddSubgroup.index_mul_measure H hHmeas μO)
  have hnormvol : (Ideal.absNorm v.asIdeal : ENNReal) * μO H = 1 := by
    simpa [hindex] using hidxvol
  have hμOH' : μO H = (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hnormvol)
  calc
    μ.μ (ball v 1) = μO H := hμOH.symm
    _ = (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ := hμOH'

private theorem localHaarFactor_eq_nnnorm [LocallyCompactSpace (v.adicCompletion F)]
    (μ : LocHaar v) (y : (v.adicCompletion F)ˣ) :
    localHaarFactor y = ‖(y : v.adicCompletion F)‖₊ := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  let hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  letI : ProperSpace K := hproper
  let _ : MeasureTheory.Measure.Regular μ.μ := locHaar_regular μ
  let π : Kˣ := unifLoc v
  let q : NNReal := (Ideal.absNorm v.asIdeal : NNReal)
  have hunif : v.valuation F (unif (F := F) v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (π : K) = algebraMap F (v.adicCompletion F) (unif (F := F) v) := by
      simp [π, unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif (F := F) v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπinvval : Valued.v ((π⁻¹ : Kˣ) : K) = WithZero.exp (1 : ℤ) := by
    calc
      _ = (Valued.v (π : K))⁻¹ := by simp
      _ = WithZero.exp (1 : ℤ) := by rw [hπval]; simp
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
  have hpreπ : localMulAddEquiv (π⁻¹) ⁻¹' (v.adicCompletionIntegers F : Set K) = ball v 1 := by
    ext x
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, localMulAddEquiv,
      ContinuousLinearEquiv.toContinuousAddEquiv_coe,
      ContinuousLinearEquiv.smulLeft_apply_apply]
    change (π⁻¹ • x) ∈
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring ↔
        Valued.v x ≤ WithZero.exp (-1 : ℤ)
    rw [Valuation.mem_valuationSubring_iff]
    rw [Units.smul_def, smul_eq_mul]
    rw [map_mul, hπinvval]
    by_cases hx : Valued.v x = 0
    · simp [hx]
    · lift Valued.v x to ℤ using hx with n hn
      rw [← WithZero.exp_add, ← WithZero.exp_zero]
      rw [WithZero.exp_le_exp, WithZero.exp_le_exp]
      omega
  have hfactorπinvForm : addEquivAddHaarChar (localMulAddEquiv (π⁻¹)) •
      μ.μ (ball v 1) = 1 := by
    simpa [hpreπ, μ.norm_O, locHaar_ball_one μ] using
      (addEquivAddHaarChar_smul_preimage μ.μ (localMulAddEquiv (π⁻¹))
        (X := (v.adicCompletionIntegers F : Set K)))
  have hfactorπinvENN : (addEquivAddHaarChar (localMulAddEquiv (π⁻¹)) : ENNReal) *
      (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ = 1 := by
    rw [locHaar_ball_one μ] at hfactorπinvForm
    simpa [ENNReal.smul_def, smul_eq_mul] using hfactorπinvForm
  have hfactorπinv : localHaarFactor (π⁻¹) = q := by
    change addEquivAddHaarChar (localMulAddEquiv (π⁻¹)) = q
    have h : (addEquivAddHaarChar (localMulAddEquiv (π⁻¹)) : ENNReal) =
        (q : ENNReal) := by
      calc
        _ = ((Ideal.absNorm v.asIdeal : ENNReal)⁻¹)⁻¹ :=
          ENNReal.eq_inv_of_mul_eq_one_left hfactorπinvENN
        _ = (q : ENNReal) := by simp [q]
    exact_mod_cast h
  have hfactorπ : localHaarFactor π = q⁻¹ := by
    have h : (localHaarFactor π)⁻¹ = q := by
      simpa only [map_inv] using hfactorπinv
    calc
      localHaarFactor π = ((localHaarFactor π)⁻¹)⁻¹ := by simp
      _ = q⁻¹ := by rw [h]
  have hfactor_unit {u : Kˣ} (hu : Valued.v (u : K) = 1) : localHaarFactor u = 1 := by
    have hpre : localMulAddEquiv u ⁻¹' (v.adicCompletionIntegers F : Set K) =
        (v.adicCompletionIntegers F : Set K) := by
      ext x
      simp only [Set.mem_preimage, localMulAddEquiv,
        ContinuousLinearEquiv.toContinuousAddEquiv_coe,
        ContinuousLinearEquiv.smulLeft_apply_apply]
      change (u • x) ∈
        (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring ↔
          x ∈ (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring
      rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff]
      rw [Units.smul_def, smul_eq_mul]
      rw [map_mul, hu]
      simp
    have hForm := addEquivAddHaarChar_smul_preimage μ.μ (localMulAddEquiv u)
      (X := (v.adicCompletionIntegers F : Set K))
    rw [hpre, μ.norm_O] at hForm
    have h : (addEquivAddHaarChar (localMulAddEquiv u) : ENNReal) = 1 := by
      simpa [ENNReal.smul_def, smul_eq_mul] using hForm
    change addEquivAddHaarChar (localMulAddEquiv u) = 1
    exact_mod_cast h
  have hnny : Valued.v (y : K) ≠ 0 := by simpa using y.ne_zero
  let n : ℤ := -WithZero.log (Valued.v (y : K))
  let u : Kˣ := y * π ^ (-n)
  have hyval : Valued.v (y : K) = WithZero.exp (-n) := by
    simpa [n] using (WithZero.exp_log hnny).symm
  have hπpow : Valued.v ((π ^ (-n) : Kˣ) : K) = Valued.v (π : K) ^ (-n) := by
    simp
  have huval : Valued.v (u : K) = 1 := by
    calc
      Valued.v (u : K) = Valued.v (y : K) * Valued.v ((π ^ (-n) : Kˣ) : K) := by simp [u]
      _ = WithZero.exp (-n) * WithZero.exp (-1 : ℤ) ^ (-n) := by rw [hyval, hπpow, hπval]
      _ = 1 := by
        rw [← WithZero.exp_zsmul]
        rw [show (-n : ℤ) • (-1 : ℤ) = n by simp, ← WithZero.exp_add]
        simp
  have hnormu : ‖(u : K)‖₊ = 1 := by
    apply NNReal.coe_injective
    rw [coe_nnnorm, ← absFin_eq_norm]
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), huval]
    simp
  have hdecomp : y = π ^ n * u := by
    dsimp [u]
    calc
      y = (π ^ n * π ^ (-n)) * y := by simp
      _ = π ^ n * (y * π ^ (-n)) := by ac_rfl
  calc
    localHaarFactor y = localHaarFactor (π ^ n * u) := by rw [hdecomp]
    _ = localHaarFactor π ^ n * localHaarFactor u := by simp
    _ = ‖((π ^ n * u : Kˣ) : K)‖₊ := by
      simp [hfactorπ, hfactor_unit huval, hπnorm, hnormu, nnnorm_mul, nnnorm_zpow]
    _ = ‖(y : K)‖₊ := by rw [hdecomp]

/-- **jq:haar-scaling**: `∫ f(y t) dt = ‖y‖⁻¹ ∫ f(t) dt`. -/
theorem LocHaar.integral_comp_mul (μ : LocHaar v) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : (v.adicCompletion F)ˣ) (f : v.adicCompletion F → E) :
    ∫ t, f ((y : v.adicCompletion F) * t) ∂μ.μ = (absFin v y)⁻¹ • ∫ t, f t ∂μ.μ := by
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
  letI : MeasureTheory.Measure.Regular μ.μ := locHaar_regular μ
  let e := localMulAddEquiv y
  let eMeas : K ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  have hfactor : addEquivAddHaarChar e = ‖(y : K)‖₊ := by
    simpa [localHaarFactor] using localHaarFactor_eq_nnnorm μ y
  have hcharMap : (‖(y : K)‖₊ : NNReal) • Measure.map e μ.μ = μ.μ := by
    have h := addEquivAddHaarChar_smul_map μ.μ e
    rw [hfactor] at h
    exact h
  have hyNorm : ‖(y : K)‖₊ ≠ 0 := by simp
  have hcancel : (‖(y : K)‖₊⁻¹ : NNReal) * ‖(y : K)‖₊ = 1 :=
    inv_mul_cancel₀ hyNorm
  have hmap : Measure.map e μ.μ = (‖(y : K)‖₊⁻¹ : NNReal) • μ.μ := by
    calc
      Measure.map e μ.μ = 1 • Measure.map e μ.μ := by simp
      _ = (‖(y : K)‖₊⁻¹ * ‖(y : K)‖₊) • Measure.map e μ.μ := by
        rw [hcancel]
        simp
      _ = ‖(y : K)‖₊⁻¹ • (‖(y : K)‖₊ • Measure.map e μ.μ) := by rw [smul_smul]
      _ = ‖(y : K)‖₊⁻¹ • μ.μ := by rw [hcharMap]
  have hcoef : ((‖(y : K)‖₊⁻¹ : NNReal) : ℝ) = (absFin v y)⁻¹ := by
    rw [NNReal.coe_inv, coe_nnnorm, absFin_eq_norm]
  calc
    ∫ t, f ((y : K) * t) ∂μ.μ = ∫ t, f (eMeas t) ∂μ.μ := by
      congr 1
    _ = ∫ x, f x ∂Measure.map eMeas μ.μ :=
      (MeasureTheory.integral_map_equiv eMeas f).symm
    _ = ((‖(y : K)‖₊⁻¹ : NNReal) : ℝ) • ∫ x, f x ∂μ.μ := by
      have hmapMeas : Measure.map eMeas μ.μ = (‖(y : K)‖₊⁻¹ : NNReal) • μ.μ := by
        change Measure.map e μ.μ = (‖(y : K)‖₊⁻¹ : NNReal) • μ.μ
        exact hmap
      rw [hmapMeas, integral_smul_nnreal_measure, NNReal.smul_def]
    _ = (absFin v y)⁻¹ • ∫ x, f x ∂μ.μ := by rw [hcoef]

/-- **jq:psi-conductor**: `ψ_v` is trivial on `𝔭^{-d}` and not on `𝔭^{-d-1}` for some `d ≥ 0`
(derived from `AddCharData.trivial_on_F` and `integral`). -/
theorem psi_conductor (A : AddCharData F) (v : FinPlace F) :
    ∃ d : ℕ, (∀ x ∈ ball v (-(d : ℤ)), A.ψ v x = 1) ∧
      ∃ x ∈ ball v (-((d : ℤ) + 1)), A.ψ v x ≠ 1 := by
  sorry

/-- At `v ∤ 𝔇` the conductor exponent is `0`. -/
theorem psi_conductor_unramified (A : AddCharData F) (v : FinPlace F)
    (hv : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : ∃ x ∈ ball v (-1), A.ψ v x ≠ 1 := by
  rcases A.unramified v hv with ⟨_, hnontriv⟩
  let π : F := unif v
  have hπ : v.valuation F π = WithZero.exp (-1) := by
    dsimp [π, unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  obtain ⟨x, hx⟩ := hnontriv π hπ
  refine ⟨algebraMap F (v.adicCompletion F) ((x : F) / π), ?_, hx⟩
  change Valued.v (((x : F) / π : F) : v.adicCompletion F) ≤ WithZero.exp 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀]
  calc
    v.valuation F (x : F) / v.valuation F π ≤ 1 / WithZero.exp (-1) := by
      rw [hπ]
      exact div_le_div_of_nonneg_right
        (v.valuation_le_one (R := 𝓞 F) (K := F) (x : 𝓞 F))
        (pos_iff_ne_zero.mpr WithZero.exp_ne_zero).le
    _ = WithZero.exp 1 := by simp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **def:jacquet**: truncated vector Jacquet integral `∫_{𝔭^{-N}} ψ(-x) f(w n(x)) dx`. -/
def jacquetTrunc (L : FinLocalCover D H v) (A : AddCharData F) (μ : LocHaar v) (N : ℕ)
    (f : L.L → V) : V :=
  ∫ x in ball v (-(N : ℤ)), A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ

/-- **def:jacquet**: the stabilized vector Jacquet functional `𝒥 f = lim_N 𝒥_N f` (10:297–329). -/
def jacquet (L : FinLocalCover D H v) (A : AddCharData F) (μ : LocHaar v) (f : L.L → V) : V :=
  limUnder atTop fun N : ℕ => jacquetTrunc L A μ N f

/-- **jq:stable** (10:300–320): for every `s` and every section the truncations are eventually
constant (large shells vanish). -/
theorem jacquet_stable (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → jacquetTrunc L A μ N f = jacquet L A μ f := by
  sorry

/-- **jq:linear**: `𝒥` is linear on sections. -/
theorem jacquet_linear (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (f g : L.L → T.V) (hf : IsSection L T s f) (hg : IsSection L T s g)
    (c : ℂ) : jacquet L A μ (f + c • g) = jacquet L A μ f + c • jacquet L A μ g := by
  sorry

/-- **jq:equiv** (10:322–329): `𝒥(π(n(t))f) = ψ(t)𝒥(f)` and `𝒥(π(z(ζ))f) = ζ𝒥(f)`. -/
theorem jacquet_equiv (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) :
    (∀ t, jacquet L A μ (rtr (L.n (Multiplicative.ofAdd t)) f) = A.ψ v t • jacquet L A μ f) ∧
    ∀ ζ, jacquet L A μ (rtr (L.z ζ) f) = ((ζ : ℂˣ) : ℂ) • jacquet L A μ f := by
  sorry

/-- **jq:bigcell**: the Jacquet integral of a big-cell section on the torus:
`𝒥(π(a(y)) f_φ) = ‖y‖^{1/2-s} σ(a(y⁻¹)) φ̂(y)`, `φ̂(y) = ∫ ψ(-yt) φ(t) dt`. -/
theorem jacquet_bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (y : (v.adicCompletion F)ˣ) :
    jacquet L A μ (rtr (L.a y) (bigCell L T s φ)) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ (∫ t, A.ψ v (-((y : v.adicCompletion F) * t)) • φ t ∂μ.μ) := by
  sorry

/-- **jq:fourier-indicator**: every `1_U ⊗ x` (`U` compact open) is a Fourier transform `φ̂`
of a locally constant compactly supported `φ`. C3 of `sol-gate-theta` requires a complete target for
the Bochner integral. -/
theorem exists_fourier_indicator [CompleteSpace V] (A : AddCharData F) (μ : LocHaar v) (U : Set (v.adicCompletion F))
    (hUc : IsCompact U) (hUo : IsOpen U) (x : V) :
    ∃ φ : v.adicCompletion F → V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      ∀ y, ∫ t, A.ψ v (-(y * t)) • φ t ∂μ.μ = U.indicator (fun _ => x) y := by
  sorry

/-- **jq:T5-local** (T5 at a finite place of `S`): for `U ⊆ O^{×6}` compact open there is a
big-cell section with `𝒥(π(a(y))f) = 1_U(y)·x` for all `y ∈ K^×`. -/
theorem exists_T5_section (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (U : Set (v.adicCompletion F)) (hUc : IsCompact U) (hUo : IsOpen U)
    (hU1 : ∀ y ∈ U, Valued.v y = 1)
    (hU6 : ∀ y ∈ U, ∃ c : (v.adicCompletion F)ˣ, y = ((c ^ 6 : (v.adicCompletion F)ˣ) : v.adicCompletion F))
    (x : T.V) :
    ∃ φ : v.adicCompletion F → T.V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      ∀ y : (v.adicCompletion F)ˣ,
        jacquet L A μ (rtr (L.a y) (bigCell L T s φ)) = U.indicator (fun _ => x) (y : v.adicCompletion F) := by
  sorry

/-- **jq:rotated**: the rotated big-cell section, `𝒥(π(a(y)w) f_φ) = ‖y‖^{1/2-s} σ(a(y⁻¹)) F̂(y)` with
`F(c) = f_φ(n̄(c)) = ‖c‖^{-1-2s} σ(a(-c⁻²)) φ(c⁻¹)` (`F = 0` near `0`). -/
theorem jacquet_rotated (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) (y : (v.adicCompletion F)ˣ) :
    jacquet L A μ (rtr (L.a y * L.w) (bigCell L T s φ)) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ (∫ c, A.ψ v (-((y : v.adicCompletion F) * c)) •
          bigCell L T s φ (L.nbar (Multiplicative.ofAdd c)) ∂μ.μ) := by
  sorry

/-- The rotated Whittaker coordinate `y ↦ c(𝒥(π(a(y)w) f_φ))`, extended by `0` at `y = 0`. -/
def rotatedCoord (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (φ : v.adicCompletion F → T.V) (c : T.V →ₗ[ℂ] ℂ)
    (y : v.adicCompletion F) : ℂ :=
  if h : y ≠ 0 then c (jacquet L A μ (rtr (L.a (Units.mk0 y h) * L.w) (bigCell L T s φ))) else 0

/-- **jq:T6-local** (T6 at a finite place of `S`, `δ = 1/3`). -/
theorem rotatedCoord_sheetHyp (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (c : T.V →ₗ[ℂ] ℂ) :
    SheetHypFin v (1 / 3) (rotatedCoord L T A μ (1 / 6) φ c) := by
  sorry

/-- **def:intertwine**: `(M f)(g) = ∫ f(w n(x) g) dx`. -/
def intertwine (L : FinLocalCover D H v) (μ : LocHaar v) (f : L.L → V) : L.L → V :=
  fun g => ∫ x, f (L.w * L.n (Multiplicative.ofAdd x) * g) ∂μ.μ

/-- **int:section**: for `Re s > 0`, `M : I(σ, s) → I(σ^w, -s)` (absolutely convergent). -/
theorem intertwine_isSection (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v)
    (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f) :
    (∀ g, Integrable (fun x => f (L.w * L.n (Multiplicative.ofAdd x) * g)) μ.μ) ∧
      IsSection L T.weyl (-s) (intertwine L μ f) := by
  sorry

/-- **int:rtr**: `M` commutes with right translation. -/
theorem intertwine_rtr (L : FinLocalCover D H v) (μ : LocHaar v) (f : L.L → V) (g : L.L) :
    intertwine L μ (rtr g f) = rtr g (intertwine L μ f) := by
  funext h
  simp [intertwine, rtr, mul_assoc]

/-- The local constant `c_v(s) = (1 - q^{-1-6s})/(1 - q^{-6s})`. -/
def cv (v : FinPlace F) (s : ℂ) : ℂ :=
  (1 - (qv v : ℂ) ^ (-1 - 6 * s)) / (1 - (qv v : ℂ) ^ (-6 * s))

/-- **int:spherical**: `M f°_s = c_v(s) f°_{-s}` at a tame place, `Re s > 0`. -/
theorem intertwine_spherical (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) (hs : 0 < s.re)
    (f0 : L.L → T.V) (hf0 : IsSection L T s f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (f0' : L.L → T.V) (hf0' : IsSection L T.weyl (-s) f0') (h1' : f0' 1 = B.weyl.e 0)
    (hK' : ∀ g, ∀ k ∈ τ.Kmax, f0' (g * k) = f0' g) :
    intertwine L μ f0 = cv v s • f0' := by
  sorry

/-- **int:analytic**: on big-cell sections, `s ↦ (M f_{φ,s})(g)` is holomorphic on `Re s > 0`. -/
theorem intertwine_bigCell_analytic (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ)
    (g : L.L) :
    AnalyticOnNhd ℂ (fun s => intertwine L μ (bigCell L T s φ) g) {s | 0 < s.re} := by
  sorry

private def localUnitShell (v : FinPlace F) : Set (v.adicCompletion F) :=
  {x | Valued.v x = 1}

private theorem localUnitShell_eq_diff (v : FinPlace F) :
    localUnitShell v =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ ball v 1 := by
  ext x
  have hO : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v x = 1 ↔ x ∈ v.adicCompletionIntegers F ∧ x ∉ ball v 1
  rw [hO]
  change Valued.v x = 1 ↔ Valued.v x ≤ 1 ∧ ¬ Valued.v x ≤ WithZero.exp (-1 : ℤ)
  constructor
  · intro hx
    rw [hx]
    simp
  · rintro ⟨hO, hnot⟩
    have hne : Valued.v x ≠ 0 := by
      intro hzero
      apply hnot
      rw [hzero]
      exact bot_le
    lift Valued.v x to ℤ using hne with n hn
    have hnle : n ≤ 0 := by
      have h := hO
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h
      exact h
    have hngt : -1 < n := by
      by_contra h
      apply hnot
      exact (WithZero.exp_le_exp).mpr (by omega)
    have hn0 : n = 0 := by omega
    simpa [hn0]

private theorem localInteger_compact (v : FinPlace F) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  rw [hset]
  exact hproper.isCompact_closedBall 0 1

private theorem localPrimeBall_compact (v : FinPlace F) : IsCompact (ball v 1) := by
  let K := v.adicCompletion F
  let π := unifLoc v
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hunif : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
      dsimp [unif]
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    change Valued.v (algebraMap F K (unif v)) = WithZero.exp (-1 : ℤ)
    change Valued.v ((unif v : F) : K) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπinvval : Valued.v ((π⁻¹ : Kˣ) : K) = WithZero.exp (1 : ℤ) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hπval]
    simp
  have hball : ball v 1 =
      (fun x : K => (π : K) * x) '' (v.adicCompletionIntegers F : Set K) := by
    ext y
    constructor
    · intro hy
      change Valued.v y ≤ WithZero.exp (-1 : ℤ) at hy
      refine ⟨((π⁻¹ : Kˣ) : K) * y, ?_, ?_⟩
      · change Valued.v (((π⁻¹ : Kˣ) : K) * y) ≤ 1
        rw [map_mul, hπinvval]
        calc
          WithZero.exp (1 : ℤ) * Valued.v y ≤
              WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by gcongr
          _ = 1 := by rw [← WithZero.exp_add]; norm_num
      · simp [mul_assoc]
    · rintro ⟨x, hx, rfl⟩
      change Valued.v ((π : K) * x) ≤ WithZero.exp (-1 : ℤ)
      have hx' : x ∈ v.adicCompletionIntegers F := hx
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx'
      have hxval : Valued.v x ≤ 1 := hx'
      rw [map_mul, hπval]
      calc
        WithZero.exp (-1 : ℤ) * Valued.v x ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ = WithZero.exp (-1 : ℤ) := by simp
  rw [hball]
  exact (localInteger_compact v).image (continuous_const.mul continuous_id)

private theorem localUnitShell_compact (v : FinPlace F) : IsCompact (localUnitShell v) := by
  have hOclosed : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    have hset : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
        Metric.closedBall (0 : v.adicCompletion F) 1 := by
      change (↑((Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).integer) : Set (v.adicCompletion F)) = _
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := v.adicCompletion F)
    rw [hset]
    exact Metric.isClosed_closedBall
  have hballopen : IsOpen (ball v 1) := by
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hclosed : IsClosed (localUnitShell v) := by
    rw [localUnitShell_eq_diff]
    simpa only [Set.diff_eq] using hOclosed.inter hballopen.isClosed_compl
  exact (localInteger_compact v).of_isClosed_subset hclosed (by
    rw [localUnitShell_eq_diff]
    exact Set.diff_subset)

private theorem localUnitShell_realMeasure (μ : LocHaar v) :
    μ.μ.real (localUnitShell v) = 1 - (qv v)⁻¹ := by
  rw [localUnitShell_eq_diff]
  have hballmeas : MeasurableSet (ball v 1) := by
    exact (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).measurableSet
  have hballsub : ball v 1 ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro x hx
    change x ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
    exact hx.trans (by simp)
  have hOfinite : μ.μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ := by
    rw [μ.norm_O]
    simp
  rw [MeasureTheory.measureReal_sdiff hballsub hballmeas hOfinite]
  have hball : μ.μ.real (ball v 1) = (qv v)⁻¹ := by
    rw [MeasureTheory.measureReal_def, locHaar_ball_one μ]
    simp [qv]
  rw [hball]
  simp [MeasureTheory.measureReal_def, μ.norm_O]

private theorem localUnitShell_ne_zero (x : localUnitShell v) : (x : v.adicCompletion F) ≠ 0 := by
  intro hx
  have h := x.property
  rw [hx] at h
  simp [localUnitShell] at h

private noncomputable def localUnitShell.unit (x : localUnitShell v) : (v.adicCompletion F)ˣ :=
  Units.mk0 x (localUnitShell_ne_zero x)

private theorem localUnitShell_isLocUnit (x : localUnitShell v) :
    IsLocUnit v (localUnitShell.unit x) := by
  have hx : Valued.v (localUnitShell.unit x : v.adicCompletion F) = 1 := by
    change Valued.v (x : v.adicCompletion F) = 1
    exact x.property
  have hxi :
      Valued.v (((localUnitShell.unit x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simp [hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxi]

private theorem localUnitShell_charPower_congr (D : FieldData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (j : ℤ) (x y : localUnitShell v) (hxy : (y : v.adicCompletion F) - x ∈ ball v 1) :
    (localChi D v (localUnitShell.unit y)) ^ j =
      (localChi D v (localUnitShell.unit x)) ^ j := by
  have hlt : Valued.v ((y : v.adicCompletion F) - x) < 1 := by
    change Valued.v ((y : v.adicCompletion F) - x) ≤ WithZero.exp (-1 : ℤ) at hxy
    have hsmall : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    exact lt_of_le_of_lt hxy hsmall
  have hbasic := localChi_basic (D := D) (v := v) hv
  have hχ := hbasic.2.2.2.2 (localUnitShell.unit y) (localUnitShell.unit x)
    (localUnitShell_isLocUnit y) (localUnitShell_isLocUnit x) hlt
  rw [hχ]

private noncomputable def localUnitShell.charPower (D : FieldData F) (j : ℤ)
    (x : localUnitShell v) : ℂ := localChi D v (localUnitShell.unit x) ^ j

private theorem localUnitShell_charPower_locallyConstant (D : FieldData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) :
    IsLocallyConstant (localUnitShell.charPower (D := D) (v := v) j) := by
  apply (IsLocallyConstant.iff_eventually_eq
    (localUnitShell.charPower (D := D) (v := v) j)).2
  intro x
  have hballopen : IsOpen (ball v 1) := by
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  let U : Set (localUnitShell v) :=
    {y | (y : v.adicCompletion F) - x ∈ ball v 1}
  have hUopen : IsOpen U := by
    change IsOpen ((fun y : localUnitShell v => (y : v.adicCompletion F) - x) ⁻¹' ball v 1)
    exact hballopen.preimage (continuous_subtype_val.sub continuous_const)
  have hxU : x ∈ U := by
    change (x : v.adicCompletion F) - x ∈ ball v 1
    simp [ball]
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  exact localUnitShell_charPower_congr D hv j x y hy

private noncomputable def localChiPowerField (D : FieldData F) (j : ℤ)
    (x : v.adicCompletion F) : ℂ :=
  if hx : x ≠ 0 then localChi D v (Units.mk0 x hx) ^ j else 0

private theorem localChiPowerField_integrableOn (D : FieldData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) :
    IntegrableOn (localChiPowerField D j) (localUnitShell v) μ.μ := by
  have hcont : ContinuousOn (localChiPowerField D j) (localUnitShell v) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (localUnitShell v).domRestrict (localChiPowerField D j) =
        localUnitShell.charPower (D := D) (v := v) j := by
      funext x
      simp [localChiPowerField, localUnitShell.charPower, localUnitShell.unit,
        localUnitShell_ne_zero]
    rw [heq]
    exact (localUnitShell_charPower_locallyConstant (v := v) D hv j).continuous
  exact hcont.integrableOn_compact (localUnitShell_compact v)

local instance localResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance localResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem localResidue_rep (x : F) (a b : 𝓞 F) (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply (IsFractionRing.injective (𝓞 F) F)
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem localResidue_algebraMap (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  simpa using localResidue_rep (v := v) (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)

private theorem localResidue_ne_zero_local (x : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1) :
    residue v x ≠ 0 ↔ HeightOneSpectrum.valuation F v x = 1 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 b.property
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) := by
    have := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using this
  rw [localResidue_rep (v := v) x a b.val b.property hab, div_ne_zero_iff, hval,
    v.valuation_eq_one_iff_notMem (K := F) (r := a)]
  have hb : b.val ∉ v.asIdeal := b.property
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hb, not_false_eq_true, and_true]

private theorem localToLoc_isLocUnit (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]

private theorem localChi_toLoc_integer_eq (D : FieldData F) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (aF : Fˣ) (haF : (aF : F) = (a : F)) :
    localChi D v (toLoc v aF) = chi D v (a : F) := by
  have hcoerce : (toLoc v aF : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (a : F) := by
    simp [toLoc, haF]
  have hwit : ∃ a0 : 𝓞 F, a0 ∉ v.asIdeal ∧
      Valued.v ((toLoc v aF : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a0)) < 1 := by
    refine ⟨a, ha, ?_⟩
    rw [hcoerce]
    simp
  have hdiff : Valued.v
      (algebraMap F (v.adicCompletion F) ((a : F) - (hwit.choose : F))) < 1 := by
    have h := hwit.choose_spec.2
    simpa [hcoerce] using h
  change Valued.v (((a : F) - (hwit.choose : F) : F) : v.adicCompletion F) < 1 at hdiff
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hdiff
  have hval : HeightOneSpectrum.valuation F v ((a : F) - (hwit.choose : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    by_cases hz : HeightOneSpectrum.valuation F v ((a : F) - (hwit.choose : F)) = 0
    · rw [hz]
      exact bot_le
    · lift HeightOneSpectrum.valuation F v ((a : F) - (hwit.choose : F)) to ℤ using hz with n hn
      have hnlt : n < 0 := by
        have h := hdiff
        simpa only [← WithZero.exp_zero, WithZero.exp_lt_exp] using h
      rw [WithZero.exp_le_exp]
      omega
  have hvalO : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F (a - hwit.choose)) ≤ WithZero.exp (-1 : ℤ) := by
    simpa only [map_sub] using hval
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hvalO
  have hmemPow : a - hwit.choose ∈ v.asIdeal ^ 1 :=
    (v.intValuation_le_pow_iff_mem (a - hwit.choose) 1).1 hvalO
  have hmem : a - hwit.choose ∈ v.asIdeal := by simpa using hmemPow
  have hres : residue v (a : F) = residue v (hwit.choose : F) := by
    have hmk : Ideal.Quotient.mk v.asIdeal a -
        Ideal.Quotient.mk v.asIdeal hwit.choose = 0 := by
      rw [← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    calc
      residue v (a : F) = Ideal.Quotient.mk v.asIdeal a := localResidue_algebraMap (v := v) a
      _ = Ideal.Quotient.mk v.asIdeal hwit.choose := sub_eq_zero.mp hmk
      _ = residue v (hwit.choose : F) := (localResidue_algebraMap (v := v) hwit.choose).symm
  have hchi : chi D v (a : F) = chi D v (hwit.choose : F) := by
    simp [chi, chiAlg, hres]
  unfold localChi
  rw [dif_pos hwit]
  change chi D v (hwit.choose : F) = chi D v (a : F)
  exact hchi.symm

private theorem localUniformizer_valuation :
    HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
  dsimp [unif]
  exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec

private theorem localDiv_mem_integers (a : 𝓞 F) (ha : a ∈ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((a : F) / unif v) ∈ v.adicCompletionIntegers F := by
  have hvalNum : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) ≤
      WithZero.exp (-1 : ℤ) := by
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    apply (v.intValuation_le_pow_iff_mem a 1).2
    simpa using ha
  have hvalDiv : HeightOneSpectrum.valuation F v ((a : F) / unif v) ≤ 1 := by
    rw [map_div₀, localUniformizer_valuation]
    have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
      lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    exact (div_le_one₀ hexpPos).2 hvalNum
  change ((((a : F) / unif v : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hvalDiv

private theorem localPsi_phaseErr (A : AddCharData F) (a b : 𝓞 F)
    (hab : a - b ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v)) = 1 := by
  exact A.integral v _ (localDiv_mem_integers (a - b) hab)

private theorem localPsi_phaseCongr (A : AddCharData F) (a b : 𝓞 F)
    (hab : a - b ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) := by
  have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v) =
      algebraMap F (v.adicCompletion F) ((a : F) / unif v) -
        algebraMap F (v.adicCompletion F) ((b : F) / unif v) := by
    have hF : ((a : F) - b) / unif v = (a : F) / unif v - (b : F) / unif v := by
      field_simp [unif_ne_zero v]
    rw [hF, map_sub]
  have hphase := localPsi_phaseErr (A := A) (v := v) a b hab
  have hrep : algebraMap F (v.adicCompletion F) ((a : F) / unif v) =
      algebraMap F (v.adicCompletion F) ((b : F) / unif v) +
        algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v) := by
    rw [harg]
    abel
  rw [hrep, (A.ψ v).map_add_eq_mul, hphase, mul_one]

private noncomputable def localAddChar (A : AddCharData F) :
    AddChar (𝓞 F ⧸ v.asIdeal) ℂ := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  let ψfun : R → ℂ := fun x =>
    A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v))
  have hzero : ψfun 0 = 1 := by
    have hmem : (0 : R).out ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp
    simpa [ψfun] using localPsi_phaseCongr (A := A) (v := v) (0 : R).out 0
      (by simpa using hmem) |>.trans (by simp)
  have hrepAdd (x y : R) : (x + y).out - (x.out + y.out) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, Ideal.Quotient.mk_out]
    simp [map_add]
  have hψadd (x y : R) : ψfun (x + y) = ψfun x * ψfun y := by
    have harg : algebraMap F (v.adicCompletion F)
        (((x.out : F) + y.out) / unif v) =
      algebraMap F (v.adicCompletion F) ((x.out : F) / unif v) +
        algebraMap F (v.adicCompletion F) (y.out / unif v) := by
      have hF : ((x.out : F) + y.out) / unif v =
          (x.out : F) / unif v + y.out / unif v := by
        field_simp [unif_ne_zero v]
      rw [hF, map_add]
    calc
      ψfun (x + y) =
          A.ψ v (algebraMap F (v.adicCompletion F) (((x + y).out : F) / unif v)) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          (((x.out + y.out : 𝓞 F) : F) / unif v)) :=
        localPsi_phaseCongr (A := A) (v := v) (x + y).out (x.out + y.out) (hrepAdd x y)
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v) +
            algebraMap F (v.adicCompletion F) (y.out / unif v)) := by
        rw [show ((x.out + y.out : 𝓞 F) : F) = (x.out : F) + y.out by norm_cast, harg]
      _ = ψfun x * ψfun y := (A.ψ v).map_add_eq_mul _ _
  exact { toFun := ψfun, map_zero_eq_one' := hzero, map_add_eq_mul' := hψadd }

@[simp] private theorem localAddChar_apply (A : AddCharData F) (x : 𝓞 F ⧸ v.asIdeal) :
    localAddChar (v := v) A x =
      A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v)) := rfl

private theorem localAddChar_ne_one (A : AddCharData F)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : localAddChar (v := v) A ≠ 1 := by
  obtain ⟨_, hnontriv⟩ := A.unramified v hd
  obtain ⟨a, hψa⟩ := hnontriv (unif v) (localUniformizer_valuation (v := v))
  intro h
  have hphase : localAddChar (v := v) A (Ideal.Quotient.mk v.asIdeal a) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) := by
    rw [localAddChar_apply]
    exact localPsi_phaseCongr (A := A) (v := v)
      (Ideal.Quotient.mk v.asIdeal a).out a (by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, Ideal.Quotient.mk_out]
        simp)
  have hone : localAddChar (v := v) A (Ideal.Quotient.mk v.asIdeal a) = 1 := by
    simpa [h] using (congrArg (fun ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ => ψ
      (Ideal.Quotient.mk v.asIdeal a)) h)
  exact hψa (hphase.symm.trans hone)

private noncomputable def completionResidueClass
    (x : v.adicCompletionIntegers F) : 𝓞 F ⧸ v.asIdeal :=
  (v.residueFieldEquivAdicCompletionIntegers (K := F)).symm
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) x)

private noncomputable def completionResidueCenter
    (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletionIntegers F :=
  algebraMap (𝓞 F) (v.adicCompletionIntegers F) r.out

private noncomputable def completionResidueClassOf
    (x : v.adicCompletion F) : 𝓞 F ⧸ v.asIdeal :=
  if hx : x ∈ v.adicCompletionIntegers F then
    completionResidueClass (v := v) ⟨x, hx⟩ else 0

private theorem completionResidueClassOf_eq (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) :
    completionResidueClassOf (v := v) x =
      completionResidueClass (v := v) ⟨x, hx⟩ := by
  dsimp [completionResidueClassOf]
  rw [dif_pos hx]

private def completionResidueFiber (r : 𝓞 F ⧸ v.asIdeal) :
    Set (v.adicCompletion F) :=
  {x | x ∈ v.adicCompletionIntegers F ∧ completionResidueClassOf (v := v) x = r}

private theorem localCompletionMaximalIdeal_iff (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  change x ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
  exact Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))) (a := x)

private theorem completionResidueClass_eq_iff (x y : v.adicCompletionIntegers F) :
    completionResidueClass (v := v) x = completionResidueClass (v := v) y ↔
      (x : v.adicCompletion F) - y ∈ ball v 1 := by
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  constructor
  · intro h
    have hquot : Ideal.Quotient.mk M x = Ideal.Quotient.mk M y := by
      have heq := congrArg e h
      simpa [completionResidueClass, e, M] using heq
    have hmem : (x - y : v.adicCompletionIntegers F) ∈ M :=
      Ideal.Quotient.eq.mp hquot
    have hlt := (localCompletionMaximalIdeal_iff (v := v) (x - y)).mp hmem
    exact (valued_lt_one_iff_ball_one (v := v) (x - y : v.adicCompletion F)).mp hlt
  · intro h
    have hlt : Valued.v ((x : v.adicCompletion F) - y) < 1 :=
      (valued_lt_one_iff_ball_one (v := v) ((x : v.adicCompletion F) - y)).mpr h
    have hmem : (x - y : v.adicCompletionIntegers F) ∈ M :=
      (localCompletionMaximalIdeal_iff (v := v) (x - y)).mpr hlt
    have hquot : Ideal.Quotient.mk M x = Ideal.Quotient.mk M y := Ideal.Quotient.eq.mpr hmem
    have heq := congrArg e.symm hquot
    simpa [completionResidueClass, e, M] using heq

private theorem completionResidueClass_center (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueClass (v := v) (completionResidueCenter (v := v) r) = r := by
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  have hmap := v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r.out
  change e.symm (Ideal.Quotient.mk M (algebraMap (𝓞 F) (v.adicCompletionIntegers F) r.out)) = r
  rw [← hmap]
  simp [e]

private theorem completionResidueFiber_eq (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueFiber (v := v) r =
      {x | x ∈ v.adicCompletionIntegers F ∧
        (x : v.adicCompletion F) - completionResidueCenter (v := v) r ∈ ball v 1} := by
  ext x
  constructor
  · rintro ⟨hx, hclass⟩
    refine ⟨hx, ?_⟩
    let xO : v.adicCompletionIntegers F := ⟨x, hx⟩
    have hclass' : completionResidueClass (v := v) xO = r := by
      simpa [completionResidueClassOf, hx, xO] using hclass
    have hcent := completionResidueClass_center (v := v) r
    have hres := hclass'.trans hcent.symm
    simpa [xO] using
      (completionResidueClass_eq_iff (v := v) xO (completionResidueCenter (v := v) r)).mp hres
  · rintro ⟨hx, hball⟩
    let xO : v.adicCompletionIntegers F := ⟨x, hx⟩
    have hres :=
      (completionResidueClass_eq_iff (v := v) xO (completionResidueCenter (v := v) r)).mpr hball
    have hcent := completionResidueClass_center (v := v) r
    have hclassOf : completionResidueClassOf (v := v) x =
        completionResidueClass (v := v) xO := by
      simpa [xO] using completionResidueClassOf_eq (v := v) x hx
    refine ⟨hx, ?_⟩
    exact hclassOf.trans (hres.trans hcent)

private theorem localPrimeBall_subset_integer :
    ball v 1 ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  change x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
  exact hx.trans (by simp)

private theorem completionResidueFiber_eq_translate (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueFiber (v := v) r =
      (fun x : v.adicCompletion F => x + (completionResidueCenter (v := v) r : v.adicCompletion F)) ''
        ball v 1 := by
  rw [completionResidueFiber_eq]
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    refine ⟨x - (completionResidueCenter (v := v) r : v.adicCompletion F), hball, ?_⟩
    simp
  · rintro ⟨d, hd, rfl⟩
    constructor
    · have hdO := localPrimeBall_subset_integer (v := v) hd
      have hsum := (v.adicCompletionIntegers F).add_mem d
        (completionResidueCenter (v := v) r) hdO
        (completionResidueCenter (v := v) r).property
      change d + (completionResidueCenter (v := v) r : v.adicCompletion F) ∈
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      exact hsum
    · simpa using hd

private theorem completionResidueFiber_realMeasure (μ : LocHaar v)
    (r : 𝓞 F ⧸ v.asIdeal) :
    μ.μ.real (completionResidueFiber (v := v) r) = (qv v)⁻¹ := by
  rw [completionResidueFiber_eq_translate]
  let c : v.adicCompletion F := completionResidueCenter (v := v) r
  have himage : (fun x : v.adicCompletion F => x + c) '' ball v 1 =
      (fun x : v.adicCompletion F => x - c) ⁻¹' ball v 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨x - c, hx, ?_⟩
      simp
  have hmeasure : μ.μ ((fun x : v.adicCompletion F => x + c) '' ball v 1) =
      μ.μ (ball v 1) := by
    rw [himage]
    simpa only [sub_eq_add_neg] using
      MeasureTheory.measure_preimage_add_right μ.μ (-c) (ball v 1)
  have hreal : ENNReal.toReal (μ.μ ((fun x : v.adicCompletion F => x + c) '' ball v 1)) =
      (qv v)⁻¹ := by
    have h := congrArg ENNReal.toReal hmeasure
    rw [locHaar_ball_one μ] at h
    simpa [qv] using h
  exact hreal

private theorem completionResidueFiber_measurable (r : 𝓞 F ⧸ v.asIdeal) :
    MeasurableSet (completionResidueFiber (v := v) r) := by
  rw [completionResidueFiber_eq]
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (localInteger_compact v).measurableSet
  have hball : IsOpen {x : v.adicCompletion F |
      x - (completionResidueCenter (v := v) r : v.adicCompletion F) ∈ ball v 1} := by
    have ho : IsOpen (ball v 1) := v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
    exact ho.preimage (continuous_id.sub continuous_const)
  exact hO.inter hball.measurableSet

private theorem completionResidueFiber_pairwise :
    Pairwise fun a b => Disjoint (completionResidueFiber (v := v) a)
      (completionResidueFiber (v := v) b) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  rcases hxa with ⟨hOa, ha⟩
  rcases hxb with ⟨hOb, hb⟩
  have hclassa : completionResidueClass (v := v) ⟨x, hOa⟩ = a := by
    simpa [completionResidueClassOf, hOa] using ha
  have hclassb : completionResidueClass (v := v) ⟨x, hOb⟩ = b := by
    simpa [completionResidueClassOf, hOb] using hb
  have hsub : (⟨x, hOa⟩ : v.adicCompletionIntegers F) = ⟨x, hOb⟩ := by
    apply Subtype.ext
    rfl
  have hclass := congrArg (completionResidueClass (v := v)) hsub
  exact hab (hclassa.symm.trans (hclass.trans hclassb))

private theorem completionResidueFiber_iUnion :
    (⋃ r : 𝓞 F ⧸ v.asIdeal, completionResidueFiber (v := v) r) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact hr.1
  · intro hx
    let xO : v.adicCompletionIntegers F := ⟨x, hx⟩
    refine Set.mem_iUnion.mpr ⟨completionResidueClass (v := v) xO, ?_⟩
    exact ⟨hx, (completionResidueClassOf_eq (v := v) x hx).trans (by rfl)⟩

private theorem exists_localChi_primitive_unit (D : FieldData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    ∃ u : (v.adicCompletion F)ˣ, IsLocUnit v u ∧
      Valued.v (u : v.adicCompletion F) = 1 ∧ IsPrimitiveRoot (localChi D v u) 6 := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  let N := Ideal.absNorm v.asIdeal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype R := Fintype.ofFinite R
  have hcard : Fintype.card R = N := by
    dsimp [R, N]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hNone : 1 < N := by
    dsimp [N]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hcop : N.Coprime 6 := by
    dsimp [N]
    exact (coprime_six_of_not_mem_six v hv).1
  have hNsub : 6 ∣ N - 1 := by
    dsimp [N]
    exact six_dvd_absNorm_sub_one D v hv
  let e : ℕ := (N - 1) / 6
  have hN : N - 1 = 6 * e := by
    dsimp [e]
    have h := Nat.mul_div_cancel' hNsub
    omega
  have hunitCard : Fintype.card Rˣ = N - 1 := by
    rw [Fintype.card_units, hcard]
  have hunitCard' : Nat.card Rˣ = N - 1 := by
    rw [Nat.card_eq_fintype_card, hunitCard]
  letI : NeZero 6 := ⟨by decide⟩
  let hζ6 := D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  let ζ6 : rootsOfUnity 6 (𝓞 F) := hζ6.toInteger_isPrimitiveRoot.toRootsOfUnity
  have hζ6Order : orderOf ζ6 = 6 := by
    refine Eq.trans ?_ hζ6.toInteger_isPrimitiveRoot.eq_orderOf.symm
    rw [← hζ6.toInteger_isPrimitiveRoot.val_toRootsOfUnity_coe,
      orderOf_units, Subgroup.orderOf_coe]
  have hrootsMapInj : Function.Injective (Ideal.rootsOfUnityMapQuot v.asIdeal 6) :=
    Ideal.rootsOfUnityMapQuot_injective 6 (ne_of_gt hNone) hcop
  have hrootsMapOrder : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) = 6 := by
    apply Nat.dvd_antisymm
    · calc
        orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) ∣ orderOf ζ6 :=
          orderOf_map_dvd _ _
        _ = 6 := hζ6Order
    · have hpow := pow_orderOf_eq_one (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6)
      have hmap : Ideal.rootsOfUnityMapQuot v.asIdeal 6
          (ζ6 ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6)) =
            Ideal.rootsOfUnityMapQuot v.asIdeal 6 1 := by
        rw [map_pow, hpow, map_one]
      have hpow' : ζ6 ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) = 1 :=
        hrootsMapInj hmap
      simpa [hζ6Order] using orderOf_dvd_of_pow_eq_one hpow'
  obtain ⟨g, hgOrder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Rˣ)
  have hgOrder' : orderOf g = N - 1 := hgOrder.trans hunitCard'
  have hNpos : 0 < N - 1 := by omega
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hNpos hNsub) (by decide)
  have he_dvd : e ∣ N - 1 := by
    refine ⟨6, ?_⟩
    rw [hN]
    ring
  have horderPow : orderOf (g ^ e) = 6 := by
    rw [orderOf_pow, hgOrder', Nat.gcd_eq_right he_dvd, hN]
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left 6 hepos
  have hrootsMapPrimUnits : IsPrimitiveRoot (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) 6 :=
    IsPrimitiveRoot.iff_orderOf.mpr hrootsMapOrder
  have hrootsMapPrim : IsPrimitiveRoot
      ((Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6 : Rˣ) : R) 6 :=
    IsPrimitiveRoot.coe_units_iff.mpr hrootsMapPrimUnits
  have hresAlg (a : 𝓞 F) :
      residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a :=
    localResidue_algebraMap (v := v) a
  have hchiAlgRed :
      Ideal.rootsOfUnityMapQuot v.asIdeal 6
        (chiAlg v (algebraMap (𝓞 F) F (g : R).out)) = g ^ e := by
    have hpowCard : g ^ (N - 1) = 1 := by
      calc
        g ^ (N - 1) = g ^ Nat.card Rˣ := by rw [hunitCard']
        _ = 1 := pow_card_eq_one'
    have hpowUnit : (g ^ e) ^ 6 = 1 := by
      calc
        (g ^ e) ^ 6 = g ^ (e * 6) := by rw [← pow_mul]
        _ = g ^ (N - 1) := by rw [Nat.mul_comm, hN]
        _ = 1 := hpowCard
    have hpowR : (((g ^ e : Rˣ) : R) ^ 6) = 1 := by
      simpa using congrArg (fun z : Rˣ => (z : R)) hpowUnit
    obtain ⟨i, hi, hrootpow⟩ := hrootsMapPrim.eq_pow_of_pow_eq_one hpowR
    let ζpre : rootsOfUnity 6 (𝓞 F) := ζ6 ^ i
    have hrootpreMap : Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre = g ^ e := by
      apply Units.ext
      simpa [ζpre, map_pow, Units.val_pow_eq_pow_val] using hrootpow
    have hquotPre : Ideal.Quotient.mk v.asIdeal ((ζpre : (𝓞 F)ˣ) : 𝓞 F) =
        ((g ^ e : Rˣ) : R) := by
      have h := congrArg (fun u : Rˣ => (u : R)) hrootpreMap
      rw [Ideal.rootsOfUnityMapQuot_apply] at h
      simpa [ζpre, Units.val_pow_eq_pow_val] using h
    have hres : residue v (algebraMap (𝓞 F) F (g : R).out) = (g : R) := by
      simpa [R] using hresAlg (g : R).out
    have hchiAlgExists : ∃ ζ : rootsOfUnity 6 (𝓞 F),
        Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
          residue v (algebraMap (𝓞 F) F (g : R).out) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
      refine ⟨ζpre, ?_⟩
      rw [hres]
      simpa [e, N] using hquotPre
    unfold chiAlg
    split
    · rename_i h
      apply Units.ext
      rw [Ideal.rootsOfUnityMapQuot_apply]
      have hs := h.choose_spec
      rw [hs, hres]
      simp [e, N]
    · rename_i h
      exact (h hchiAlgExists).elim
  let χroot : rootsOfUnity 6 (𝓞 F) := chiAlg v (algebraMap (𝓞 F) F (g : R).out)
  have hmapChiOrder : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot) = 6 := by
    rw [show χroot = chiAlg v (algebraMap (𝓞 F) F (g : R).out) from rfl,
      hchiAlgRed]
    exact horderPow
  have hχrootOrder : orderOf χroot = 6 := by
    apply Nat.dvd_antisymm
    · have hpow := pow_orderOf_eq_one (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot)
      have hmap : Ideal.rootsOfUnityMapQuot v.asIdeal 6 (χroot ^
          orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot)) =
          Ideal.rootsOfUnityMapQuot v.asIdeal 6 1 := by
        rw [map_pow, hpow, map_one]
      have hpow' : χroot ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot) = 1 :=
        hrootsMapInj hmap
      calc
        orderOf χroot ∣ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot) :=
          orderOf_dvd_of_pow_eq_one hpow'
        _ = 6 := hmapChiOrder
    · calc
        6 = orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 χroot) := hmapChiOrder.symm
        _ ∣ orderOf χroot := orderOf_map_dvd (Ideal.rootsOfUnityMapQuot v.asIdeal 6) χroot
  have hχrootPrim : IsPrimitiveRoot χroot 6 := IsPrimitiveRoot.iff_orderOf.mpr hχrootOrder
  let evalRoot : rootsOfUnity 6 (𝓞 F) →* ℂˣ :=
    (Units.map (D.σ0.comp (algebraMap (𝓞 F) F))).comp
      (rootsOfUnity 6 (𝓞 F)).subtype
  have hcompInj : Function.Injective (D.σ0.comp (algebraMap (𝓞 F) F)) :=
    (RingHom.injective D.σ0).comp (IsFractionRing.injective (𝓞 F) F)
  have hevalInj : Function.Injective evalRoot := by
    intro ζ ζ' h
    apply Subtype.ext
    apply Units.ext
    apply hcompInj
    simpa [evalRoot] using congrArg (fun z : ℂˣ => (z : ℂ)) h
  have hevalPrim : IsPrimitiveRoot (evalRoot χroot) 6 :=
    hχrootPrim.map_of_injective (f := evalRoot) hevalInj
  let a : 𝓞 F := (g : R).out
  have hmk : Ideal.Quotient.mk v.asIdeal a = (g : R) := by simp [a]
  have ha : a ∉ v.asIdeal := by
    intro ha
    have hzero : Ideal.Quotient.mk v.asIdeal a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    apply g.ne_zero
    rw [hmk] at hzero
    exact hzero
  have haFne : (a : F) ≠ 0 := by
    intro hzero
    have ha0 : a = 0 := (IsFractionRing.injective (𝓞 F) F) hzero
    apply g.ne_zero
    have hzero' : Ideal.Quotient.mk v.asIdeal a = 0 := by simp [ha0]
    rw [hmk] at hzero'
    exact hzero'
  let aF : Fˣ := Units.mk0 (a : F) haFne
  have hvalle : HeightOneSpectrum.valuation F v (a : F) ≤ 1 := v.valuation_le_one a
  have hresne : residue v (a : F) ≠ 0 := by
    have hres : residue v (a : F) = (g : R) := by
      calc
        residue v (a : F) = Ideal.Quotient.mk v.asIdeal a := by
          simpa using localResidue_algebraMap (v := v) a
        _ = (g : R) := hmk
    rw [hres]
    exact g.ne_zero
  have hvalone := (localResidue_ne_zero_local (v := v) (a : F) hvalle).mp hresne
  let u := toLoc v aF
  have hu : IsLocUnit v u := localToLoc_isLocUnit (v := v) aF hvalone
  have huVal : Valued.v (u : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hvalone]
  have hlocal : localChi D v u = chi D v (a : F) :=
    localChi_toLoc_integer_eq (v := v) D a ha aF rfl
  have hchiEval : chi D v (a : F) = ((evalRoot χroot : ℂˣ) : ℂ) := by
    unfold chi
    rw [if_neg hresne]
    rfl
  refine ⟨u, hu, huVal, ?_⟩
  rw [hlocal, hchiEval]
  exact IsPrimitiveRoot.coe_units_iff.mpr hevalPrim

private theorem localUnitShell_charPower_integral_eq_zero (D : FieldData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = 1)
    (hχ : localChi D v a ^ j ≠ 1) :
    ∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ = 0 := by
  have haLoc : IsLocUnit v a := by
    have hai : Valued.v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [ha]
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ha]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hai]
  have habs : absFin v a = 1 := by
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), ha]
    simp
  let f : v.adicCompletion F → ℂ :=
    (localUnitShell v).indicator (localChiPowerField D j)
  have hmeas : MeasurableSet (localUnitShell v) := (localUnitShell_compact v).measurableSet
  have hf : Integrable f μ.μ := by
    dsimp [f]
    exact (localChiPowerField_integrableOn D μ hv j).integrable_indicator hmeas
  have hca0 : localChi D v a ≠ 0 := by
    have h := (localChi_basic (D := D) (v := v) hv).2.2.2.1 a haLoc
    intro hz
    rw [hz] at h
    norm_num at h
  have hpoint (x : v.adicCompletion F) :
      f ((a : v.adicCompletion F) * x) = localChi D v a ^ j * f x := by
    by_cases hx : x ∈ localUnitShell v
    · let xU : localUnitShell v := ⟨x, hx⟩
      have hxval : Valued.v x = 1 := hx
      have haxval : Valued.v ((a : v.adicCompletion F) * x) = 1 := by
        rw [map_mul, ha, hxval]
        simp
      have hax : (a : v.adicCompletion F) * x ∈ localUnitShell v := haxval
      let axU : localUnitShell v := ⟨(a : v.adicCompletion F) * x, hax⟩
      have hxne : x ≠ 0 := localUnitShell_ne_zero xU
      have haxne : (a : v.adicCompletion F) * x ≠ 0 := localUnitShell_ne_zero axU
      have huEq : Units.mk0 ((a : v.adicCompletion F) * x) haxne =
          a * localUnitShell.unit xU := by
        apply Units.ext
        rfl
      have hχx0 : localChi D v (localUnitShell.unit xU) ≠ 0 := by
        have h := (localChi_basic (D := D) (v := v) hv).2.2.2.1
          (localUnitShell.unit xU) (localUnitShell_isLocUnit xU)
        intro hz
        rw [hz] at h
        norm_num at h
      have hχxEq : localUnitShell.unit xU = Units.mk0 x hxne := by
        apply Units.ext
        rfl
      have hχmul :
          localChi D v (a * localUnitShell.unit xU) =
            localChi D v a * localChi D v (localUnitShell.unit xU) :=
        (localChi_basic (D := D) (v := v) hv).2.2.1 a (localUnitShell.unit xU)
          haLoc (localUnitShell_isLocUnit xU)
      have hpow :
          (localChi D v a * localChi D v (localUnitShell.unit xU)) ^ j =
            localChi D v a ^ j * localChi D v (localUnitShell.unit xU) ^ j := by
        simpa [Mathlib.Tactic.FieldSimp.zpow', hca0, hχx0] using
          (Mathlib.Tactic.FieldSimp.mul_zpow' j
            (localChi D v a) (localChi D v (localUnitShell.unit xU)))
      have hfa : f ((a : v.adicCompletion F) * x) =
          localChi D v (Units.mk0 ((a : v.adicCompletion F) * x) haxne) ^ j := by
        simp [f, hax, localChiPowerField, haxne]
      have hfx : f x = localChi D v (Units.mk0 x hxne) ^ j := by
        simp [f, hx, localChiPowerField, hxne]
      calc
        f ((a : v.adicCompletion F) * x) =
            localChi D v (a * localUnitShell.unit xU) ^ j := by rw [hfa, huEq]
        _ = (localChi D v a * localChi D v (localUnitShell.unit xU)) ^ j := by
          rw [hχmul]
        _ = localChi D v a ^ j * localChi D v (localUnitShell.unit xU) ^ j := hpow
        _ = localChi D v a ^ j * f x := by rw [hχxEq, ← hfx]
    · have hax : (a : v.adicCompletion F) * x ∉ localUnitShell v := by
        intro hax
        apply hx
        change Valued.v ((a : v.adicCompletion F) * x) = 1 at hax
        rw [map_mul, ha] at hax
        simpa [localUnitShell] using hax
      simp [f, hx, hax]
  have hlin :
      (∫ x, f ((a : v.adicCompletion F) * x) ∂μ.μ) =
        localChi D v a ^ j * ∫ x, f x ∂μ.μ := by
    calc
      _ = ∫ x, localChi D v a ^ j * f x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = localChi D v a ^ j * ∫ x, f x ∂μ.μ := by rw [integral_const_mul]
  have hscale := LocHaar.integral_comp_mul μ a f
  rw [habs] at hscale
  have hscale' :
      (∫ x, f ((a : v.adicCompletion F) * x) ∂μ.μ) = ∫ x, f x ∂μ.μ := by
    simpa using hscale
  have hI :
      (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) =
        ∫ x, f x ∂μ.μ := by
    symm
    simpa [f] using (MeasureTheory.integral_indicator hmeas
      (f := localChiPowerField D j) (μ := μ.μ))
  have hEq : localChi D v a ^ j *
      (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) =
        ∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ := by
    calc
      _ = ∫ x, f ((a : v.adicCompletion F) * x) ∂μ.μ := by rw [hI, hlin]
      _ = ∫ x, f x ∂μ.μ := hscale'
      _ = _ := hI.symm
  have hmul :
      (localChi D v a ^ j - 1) *
        (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) = 0 := by
    rw [sub_mul, one_mul, hEq]
    ring
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact (False.elim (hχ (sub_eq_zero.mp hzero)))
  · exact hzero

private theorem localUnitShell_chiPower_integral (D : FieldData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℕ) :
    ∫ x in localUnitShell v, localChiPowerField D (-2 * (l : ℤ)) x ∂μ.μ =
      if 3 ∣ l then 1 - (qv v)⁻¹ else 0 := by
  let j : ℤ := -2 * (l : ℤ)
  by_cases h3div : 3 ∣ l
  · obtain ⟨k, hk⟩ := h3div
    have h3div' : 3 ∣ l := ⟨k, hk⟩
    have hexp : j = 6 * (-(k : ℤ)) := by
      dsimp [j]
      rw [hk]
      push_cast
      ring
    have hpoint (x : v.adicCompletion F) (hx : x ∈ localUnitShell v) :
        localChiPowerField D j x = 1 := by
      let xU : localUnitShell v := ⟨x, hx⟩
      let u := localUnitShell.unit xU
      have h6 := (localChi_basic (D := D) (v := v) hv).2.2.2.1 u
        (localUnitShell_isLocUnit xU)
      have hxne : x ≠ 0 := localUnitShell_ne_zero xU
      have huEq : localUnitShell.unit xU = Units.mk0 x hxne := by
        apply Units.ext
        rfl
      have hfield : localChiPowerField D j x = localChi D v u ^ j := by
        change (if hx' : x ≠ 0 then localChi D v (Units.mk0 x hx') ^ j else 0) =
          localChi D v (localUnitShell.unit xU) ^ j
        rw [dif_pos hxne]
        exact (congrArg (fun z : (v.adicCompletion F)ˣ => localChi D v z ^ j) huEq).symm
      have h6z : localChi D v u ^ (6 : ℤ) = 1 := by simpa using h6
      rw [hfield, hexp, zpow_mul, h6z]
      simp
    have hcongr :
        (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) =
          ∫ x in localUnitShell v, (1 : ℂ) ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
      exact hpoint x hx
    have hconst :
        (∫ x in localUnitShell v, (1 : ℂ) ∂μ.μ) =
          ((μ.μ.real (localUnitShell v) : ℝ) : ℂ) := by
      simp [MeasureTheory.measureReal_def]
    have hmain :
        (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) =
          ((1 - (qv v)⁻¹ : ℝ) : ℂ) := by
      calc
        _ = ∫ x in localUnitShell v, (1 : ℂ) ∂μ.μ := hcongr
        _ = ((μ.μ.real (localUnitShell v) : ℝ) : ℂ) := hconst
        _ = ((1 - (qv v)⁻¹ : ℝ) : ℂ) := by
          rw [localUnitShell_realMeasure μ]
    rw [show -2 * (l : ℤ) = j by rfl]
    rw [if_pos (show 3 ∣ l from ⟨k, hk⟩)]
    exact hmain
  · have h3not : ¬3 ∣ l := h3div
    obtain ⟨u, hu, huval, hprim⟩ := exists_localChi_primitive_unit (D := D) hv
    have hχ : localChi D v u ^ j ≠ 1 := by
      intro hχone
      have hχ6 : localChi D v u ^ (6 : ℕ) = 1 := by
        exact (localChi_basic (D := D) (v := v) hv).2.2.2.1 u hu
      have hχne : localChi D v u ≠ 0 := by
        intro hz
        rw [hz] at hχ6
        norm_num at hχ6
      let χU : ℂˣ := Units.mk0 (localChi D v u) hχne
      have hprimU : IsPrimitiveRoot χU 6 := by
        apply IsPrimitiveRoot.coe_units_iff.mp
        simpa [χU] using hprim
      have hχoneU : χU ^ j = 1 := by
        apply Units.ext
        simpa [χU] using hχone
      have horder : (orderOf χU : ℤ) ∣ j := by
        rw [orderOf_dvd_iff_zpow_eq_one]
        exact hχoneU
      have horderNat : (6 : ℕ) = orderOf χU := hprimU.eq_orderOf
      have horder' : (6 : ℤ) ∣ j := by
        calc
          (6 : ℤ) = (orderOf χU : ℤ) := by exact_mod_cast horderNat
          _ ∣ j := horder
      have hdiv' : (6 : ℤ) ∣ -2 * (l : ℤ) := by simpa [j] using horder'
      have hdivNat : 3 ∣ l := by omega
      exact h3not hdivNat
    have hzero := localUnitShell_charPower_integral_eq_zero D μ hv j u huval hχ
    simpa [j, h3not] using hzero

private theorem localPiInv_mul_ball_mem_integer (x : v.adicCompletion F) (hx : x ∈ ball v 1) :
    (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈
      v.adicCompletionIntegers F := by
  have hπval : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hunif : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
      dsimp [unif]
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = WithZero.exp (-1 : ℤ)
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπinv : Valued.v (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (1 : ℤ) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hπval]
    simp
  change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [map_mul, hπinv]
  calc
    WithZero.exp (1 : ℤ) * Valued.v x ≤
        WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by gcongr
    _ = 1 := by rw [← WithZero.exp_add]; norm_num

private theorem localPsi_mul_inv_uniformizer_eq_of_diff_ball (A : AddCharData F)
    (x y : v.adicCompletion F) (hxy : x - y ∈ ball v 1) :
    A.ψ v (-(((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x))) =
      A.ψ v (-(((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y))) := by
  let πi : v.adicCompletion F := (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
  have hphase : A.ψ v (-(πi * (x - y))) = 1 := A.integral v _ (by
    simpa [πi] using localPiInv_mul_ball_mem_integer (v := v) (x - y) hxy)
  have harg : -(πi * x) = -(πi * y) + -(πi * (x - y)) := by ring
  rw [harg, (A.ψ v).map_add_eq_mul, hphase]
  simp [πi]

private theorem completionResidueCenter_val_one (r : 𝓞 F ⧸ v.asIdeal) (hr : r ≠ 0) :
    Valued.v (completionResidueCenter (v := v) r : v.adicCompletion F) = 1 := by
  let a : 𝓞 F := r.out
  have ha : a ∉ v.asIdeal := by
    intro hmem
    apply hr
    have hzero : Ideal.Quotient.mk v.asIdeal a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa [a] using hzero
  have hmk : Ideal.Quotient.mk v.asIdeal a = r := by
    simpa [a] using Ideal.Quotient.mk_out r
  have hresne : residue v (a : F) ≠ 0 := by
    rw [localResidue_algebraMap (v := v) a, hmk]
    exact hr
  have hvalle : HeightOneSpectrum.valuation F v (a : F) ≤ 1 := by
    exact v.valuation_le_one a
  have hval := (localResidue_ne_zero_local (v := v) (a : F) hvalle).mp hresne
  change Valued.v ((r.out : 𝓞 F) : v.adicCompletion F) = 1
  rw [v.valuedAdicCompletion_eq_valuation']
  exact hval

private theorem completionResidueFiber_val_one (r : 𝓞 F ⧸ v.asIdeal) (hr : r ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ completionResidueFiber (v := v) r) :
    Valued.v x = 1 := by
  have hx' := hx
  rw [completionResidueFiber_eq (v := v) r] at hx'
  rcases hx' with ⟨hxO, hxdiff⟩
  have hxOval : Valued.v x ≤ 1 := by
    rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hxO
  have hsmall : Valued.v (x - (completionResidueCenter (v := v) r : v.adicCompletion F)) <
      Valued.v (completionResidueCenter (v := v) r : v.adicCompletion F) := by
    have hball : Valued.v (x - (completionResidueCenter (v := v) r : v.adicCompletion F)) ≤
        WithZero.exp (-1 : ℤ) := hxdiff
    have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [completionResidueCenter_val_one (v := v) r hr]
    exact lt_of_le_of_lt hball hlt
  have heq := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).map_eq_of_sub_lt hsmall
  simpa [completionResidueCenter_val_one (v := v) r hr] using heq

private noncomputable def localTerminalScalar (D : FieldData F) (A : AddCharData F)
    (l : ℕ) (x : v.adicCompletion F) : ℂ :=
  if hx : x ∈ localUnitShell v then
    localChiPowerField D (-2 * (l : ℤ)) x *
      A.ψ v (-((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x))
  else 0

private noncomputable def localShellScale (e l : ℕ) : (v.adicCompletion F)ˣ :=
  unifLoc v ^ ((e : ℤ) - (l : ℤ))

private noncomputable def localShellScalar (D : FieldData F) (A : AddCharData F)
    (e l : ℕ) (x : v.adicCompletion F) : ℂ :=
  if hx : x ∈ localUnitShell v then
    localChiPowerField D (-2 * (l : ℤ)) x *
      A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) * x))
  else 0

private noncomputable def localShellScalarOnUnit (D : FieldData F) (A : AddCharData F)
    (e l : ℕ) (x : localUnitShell v) : ℂ :=
  localUnitShell.charPower (D := D) (-2 * (l : ℤ)) x *
    A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) * (x : v.adicCompletion F)))

private theorem localPsi_mul_eq_of_diff_integer (A : AddCharData F)
    (c x y : v.adicCompletion F) (hxy : c * (x - y) ∈ v.adicCompletionIntegers F) :
    A.ψ v (-(c * x)) = A.ψ v (-(c * y)) := by
  have hneg : -(c * (x - y)) ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).neg_mem (c * (x - y)) hxy
  have hphase : A.ψ v (-(c * (x - y))) = 1 := A.integral v _ hneg
  have harg : -(c * x) = -(c * y) + -(c * (x - y)) := by ring
  rw [harg, (A.ψ v).map_add_eq_mul, hphase]
  simp

private theorem localShellScale_valuation (e l : ℕ) :
    Valued.v (localShellScale (v := v) e l : v.adicCompletion F) =
      WithZero.exp ((l : ℤ) - (e : ℤ)) := by
  have hπval : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hunif : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
      dsimp [unif]
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = WithZero.exp (-1 : ℤ)
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  change Valued.v ((unifLoc v ^ ((e : ℤ) - (l : ℤ)) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = _
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπval, ← WithZero.exp_zsmul]
  congr 1
  push_cast
  ring

private theorem localShellScalarOnUnit_locallyConstant (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e l : ℕ) :
    IsLocallyConstant (localShellScalarOnUnit (v := v) D A e l) := by
  apply (IsLocallyConstant.iff_eventually_eq
    (localShellScalarOnUnit (v := v) D A e l)).2
  intro x
  let n : ℤ := max 1 ((l : ℤ) - (e : ℤ))
  let U : Set (localUnitShell v) :=
    {y | (y : v.adicCompletion F) - (x : v.adicCompletion F) ∈ ball v n}
  have hballopen : IsOpen (ball v n) := by
    change IsOpen {z : v.adicCompletion F | Valued.v z ≤ WithZero.exp (-n)}
    exact v.isOpen_setOf_valued_le (K := F) (by simp)
  have hUopen : IsOpen U := by
    change IsOpen ((fun y : localUnitShell v =>
      (y : v.adicCompletion F) - (x : v.adicCompletion F)) ⁻¹' ball v n)
    exact hballopen.preimage (continuous_subtype_val.sub continuous_const)
  have hxU : x ∈ U := by
    change (x : v.adicCompletion F) - x ∈ ball v n
    simp [ball]
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  have hN1 : 1 ≤ n := by dsimp [n]; omega
  have hNl : (l : ℤ) - (e : ℤ) ≤ n := by dsimp [n]; omega
  have hxySmall : (x : v.adicCompletion F) - (y : v.adicCompletion F) ∈ ball v n := by
    have hy' : Valued.v ((y : v.adicCompletion F) - (x : v.adicCompletion F)) ≤
        WithZero.exp (-n) := hy
    change Valued.v ((x : v.adicCompletion F) - (y : v.adicCompletion F)) ≤
      WithZero.exp (-n)
    rw [(Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).map_sub_swap]
    exact hy'
  have hxyOne : (y : v.adicCompletion F) - (x : v.adicCompletion F) ∈ ball v 1 := by
    have hy' : Valued.v ((y : v.adicCompletion F) - (x : v.adicCompletion F)) ≤
        WithZero.exp (-n) := hy
    change Valued.v ((y : v.adicCompletion F) - (x : v.adicCompletion F)) ≤
      WithZero.exp (-1 : ℤ)
    exact le_trans hy' ((WithZero.exp_le_exp).mpr (by omega))
  have hχ := localUnitShell_charPower_congr D hv (-2 * (l : ℤ)) x y hxyOne
  have hphaseArg :
      (localShellScale (v := v) e l : v.adicCompletion F) *
          ((x : v.adicCompletion F) - (y : v.adicCompletion F)) ∈
        v.adicCompletionIntegers F := by
    have hval := localShellScale_valuation (v := v) e l
    change Valued.v ((y : v.adicCompletion F) - (x : v.adicCompletion F)) ≤
        WithZero.exp (-n) at hy
    have hsmall : Valued.v ((x : v.adicCompletion F) - (y : v.adicCompletion F)) ≤
        WithZero.exp (-n) := by
      rw [(Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).map_sub_swap]
      exact hy
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [map_mul, hval]
    calc
      WithZero.exp ((l : ℤ) - (e : ℤ)) *
          Valued.v ((x : v.adicCompletion F) - (y : v.adicCompletion F)) ≤
        WithZero.exp ((l : ℤ) - (e : ℤ)) * WithZero.exp (-n) := by gcongr
      _ = WithZero.exp ((l : ℤ) - (e : ℤ) + (-n)) := by rw [← WithZero.exp_add]
      _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).mpr (by omega)
  have hphase := localPsi_mul_eq_of_diff_integer (v := v) A
    (localShellScale (v := v) e l : v.adicCompletion F)
    (x : v.adicCompletion F) (y : v.adicCompletion F) hphaseArg
  dsimp [localShellScalarOnUnit, localUnitShell.charPower]
  rw [hχ, hphase]

private theorem localShellScalar_integrableOn (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e l : ℕ) :
    IntegrableOn (localShellScalar (v := v) D A e l) (localUnitShell v) μ.μ := by
  have hcont : ContinuousOn (localShellScalar (v := v) D A e l) (localUnitShell v) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (localUnitShell v).domRestrict (localShellScalar (v := v) D A e l) =
        localShellScalarOnUnit (v := v) D A e l := by
      funext x
      simp [localShellScalar, localShellScalarOnUnit, localUnitShell.charPower,
        localChiPowerField, localUnitShell.unit, localUnitShell_ne_zero]
    rw [heq]
    exact (localShellScalarOnUnit_locallyConstant (v := v) D A hv e l).continuous
  exact hcont.integrableOn_compact (localUnitShell_compact v)

private theorem localChiPowerField_eq_of_ball_diff (D : FieldData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) (x y : v.adicCompletion F)
    (hx : x ∈ localUnitShell v) (hy : y ∈ localUnitShell v)
    (hxy : y - x ∈ ball v 1) :
    localChiPowerField D j y = localChiPowerField D j x := by
  let xU : localUnitShell v := ⟨x, hx⟩
  let yU : localUnitShell v := ⟨y, hy⟩
  have hfy : localChiPowerField D j y = localUnitShell.charPower (D := D) j yU := by
    change (if hy' : y ≠ 0 then localChi D v (Units.mk0 y hy') ^ j else 0) = _
    rw [dif_pos (localUnitShell_ne_zero yU)]
    rfl
  have hfx : localChiPowerField D j x = localUnitShell.charPower (D := D) j xU := by
    change (if hx' : x ≠ 0 then localChi D v (Units.mk0 x hx') ^ j else 0) = _
    rw [dif_pos (localUnitShell_ne_zero xU)]
    rfl
  rw [hfy, hfx]
  exact localUnitShell_charPower_congr D hv j xU yU hxy

private theorem localUnitShell_add_ball (δ : v.adicCompletion F) (hδ : δ ∈ ball v 1)
    (x : v.adicCompletion F) : x + δ ∈ localUnitShell v ↔ x ∈ localUnitShell v := by
  have hδval : Valued.v δ < 1 := by
    have hδ' : Valued.v δ ≤ WithZero.exp (-1 : ℤ) := hδ
    have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    exact lt_of_le_of_lt hδ' hlt
  constructor
  · intro hxplus
    change Valued.v (x + δ) = 1 at hxplus
    have hsmall : Valued.v (x - (x + δ)) < Valued.v (x + δ) := by
      have hneg : x - (x + δ) = -δ := by ring
      rw [hneg, (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).map_neg, hxplus]
      exact hδval
    have hval := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_eq_of_sub_lt hsmall
    rw [hxplus] at hval
    exact hval
  · intro hx
    change Valued.v x = 1 at hx
    have hlt : Valued.v δ < Valued.v x := by rw [hx]; exact hδval
    have hval : Valued.v (δ + x) = Valued.v x := by
      exact (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).map_add_eq_of_lt_right hlt
    change Valued.v (x + δ) = 1
    simpa [add_comm] using hval.trans hx

private theorem localShellScalar_add_ball (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e l : ℕ) (δ : v.adicCompletion F)
    (hδ : δ ∈ ball v 1) (x : v.adicCompletion F) :
    localShellScalar D A e l (x + δ) =
      A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) * δ)) * localShellScalar D A e l x := by
  by_cases hx : x ∈ localUnitShell v
  · have hxplus : x + δ ∈ localUnitShell v := (localUnitShell_add_ball δ hδ x).2 hx
    have hχ := localChiPowerField_eq_of_ball_diff D hv (-2 * (l : ℤ)) x
      (x + δ) hx hxplus (by simpa using hδ)
    have hphase : A.ψ v (-((localShellScale (v := v) e l :
        v.adicCompletion F) * (x + δ))) =
        A.ψ v (-((localShellScale (v := v) e l : v.adicCompletion F) * x)) *
          A.ψ v (-((localShellScale (v := v) e l : v.adicCompletion F) * δ)) := by
      have harg : -((localShellScale (v := v) e l : v.adicCompletion F) * (x + δ)) =
          -((localShellScale (v := v) e l : v.adicCompletion F) * x) +
            -((localShellScale (v := v) e l : v.adicCompletion F) * δ) := by ring
      rw [harg, (A.ψ v).map_add_eq_mul]
    simp only [localShellScalar, dif_pos hxplus, dif_pos hx]
    rw [hχ, hphase]
    ring
  · have hxplus : x + δ ∉ localUnitShell v := by
      intro hxplus
      exact hx ((localUnitShell_add_ball δ hδ x).1 hxplus)
    simp [localShellScalar, hx, hxplus]

private theorem completionResidueCenter_zero_mem_ball :
    (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F) ∈ ball v 1 := by
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  have hclass := completionResidueClass_center (v := v) (0 : 𝓞 F ⧸ v.asIdeal)
  have hmk : Ideal.Quotient.mk M (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal)) = 0 := by
    have heq := congrArg e hclass
    simpa [completionResidueClass, completionResidueCenter, e, M] using heq
  have hmem : completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) ∈ M :=
    Ideal.Quotient.eq_zero_iff_mem.mp hmk
  have hlt := (localCompletionMaximalIdeal_iff (v := v)
    (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal))).mp hmem
  exact (valued_lt_one_iff_ball_one (v := v) _).mp hlt

private theorem completionResidueFiber_zero_eq_ball :
    completionResidueFiber (v := v) (0 : 𝓞 F ⧸ v.asIdeal) = ball v 1 := by
  rw [completionResidueFiber_eq]
  ext x
  constructor
  · rintro ⟨_, hx⟩
    have hc := completionResidueCenter_zero_mem_ball (v := v)
    change Valued.v (x - (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
      v.adicCompletion F)) ≤ WithZero.exp (-1 : ℤ) at hx
    change Valued.v (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
      v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) at hc
    change Valued.v x ≤ WithZero.exp (-1 : ℤ)
    have hsum := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_add_le hx hc
    have harg : (x - (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
        v.adicCompletion F)) + completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) = x :=
      sub_add_cancel x _
    rw [harg] at hsum
    exact hsum
  · intro hx
    refine ⟨localPrimeBall_subset_integer (v := v) hx, ?_⟩
    have hc := completionResidueCenter_zero_mem_ball (v := v)
    change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
    change Valued.v (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
      v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) at hc
    change Valued.v (x - (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
      v.adicCompletion F)) ≤ WithZero.exp (-1 : ℤ)
    have hneg : Valued.v (-(completionResidueCenter (v := v)
        (0 : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)) ≤ WithZero.exp (-1 : ℤ) := by
      simpa using hc
    rw [sub_eq_add_neg]
    exact (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_add_le hx hneg

private theorem localTerminalScalar_const_on_fiber (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℕ) (r : 𝓞 F ⧸ v.asIdeal) (hr : r ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ completionResidueFiber (v := v) r) :
    localTerminalScalar D A l x =
      localTerminalScalar D A l (completionResidueCenter (v := v) r : v.adicCompletion F) := by
  have hx' := hx
  rw [completionResidueFiber_eq (v := v) r] at hx'
  rcases hx' with ⟨hxO, hxdiff⟩
  have hxunit : x ∈ localUnitShell v := by
    change Valued.v x = 1
    exact completionResidueFiber_val_one (v := v) r hr x hx
  have hcunit : (completionResidueCenter (v := v) r : v.adicCompletion F) ∈
      localUnitShell v := completionResidueCenter_val_one (v := v) r hr
  let xU : localUnitShell v := ⟨x, hxunit⟩
  let cU : localUnitShell v := ⟨(completionResidueCenter (v := v) r : v.adicCompletion F), hcunit⟩
  let j : ℤ := -2 * (l : ℤ)
  have hχ : localUnitShell.charPower (D := D) j xU =
      localUnitShell.charPower (D := D) j cU := by
    exact localUnitShell_charPower_congr D hv j cU xU hxdiff
  have hfx : localChiPowerField D j x = localUnitShell.charPower (D := D) j xU := by
    change (if hx' : x ≠ 0 then localChi D v (Units.mk0 x hx') ^ j else 0) = _
    rw [dif_pos (localUnitShell_ne_zero xU)]
    rfl
  have hfc : localChiPowerField D j (completionResidueCenter (v := v) r : v.adicCompletion F) =
      localUnitShell.charPower (D := D) j cU := by
    change (if hc' : (completionResidueCenter (v := v) r : v.adicCompletion F) ≠ 0 then
      localChi D v (Units.mk0 _ hc') ^ j else 0) = _
    rw [dif_pos (localUnitShell_ne_zero cU)]
    rfl
  let πi : v.adicCompletion F := (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
  have hψ : A.ψ v (-(πi * x)) = A.ψ v
      (-(πi * (completionResidueCenter (v := v) r : v.adicCompletion F))) := by
    simpa [πi] using localPsi_mul_inv_uniformizer_eq_of_diff_ball (v := v) A x
      (completionResidueCenter (v := v) r : v.adicCompletion F) hxdiff
  simp only [localTerminalScalar, dif_pos hxunit, dif_pos hcunit]
  change localChiPowerField D j x *
      A.ψ v (-(πi * x)) =
    localChiPowerField D j (completionResidueCenter (v := v) r : v.adicCompletion F) *
      A.ψ v (-(πi * (completionResidueCenter (v := v) r : v.adicCompletion F)))
  rw [hfx, hfc, hχ, hψ]

private theorem localTerminalScalar_zero_fiber (D : FieldData F) (A : AddCharData F)
    (l : ℕ) (x : v.adicCompletion F)
    (hx : x ∈ completionResidueFiber (v := v) (0 : 𝓞 F ⧸ v.asIdeal)) :
    localTerminalScalar D A l x = 0 := by
  have hxball : x ∈ ball v 1 := by
    rw [← completionResidueFiber_zero_eq_ball (v := v)]
    exact hx
  have hnot : x ∉ localUnitShell v := by
    intro hu
    rw [localUnitShell_eq_diff] at hu
    exact hu.2 hxball
  simp [localTerminalScalar, hnot]

private theorem localTerminalScalar_integral_fiber_sum (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℕ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    ∫ x in localUnitShell v, localTerminalScalar D A l x ∂μ.μ =
      ∑ r : 𝓞 F ⧸ v.asIdeal,
        ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
          localTerminalScalar D A l
            (completionResidueCenter (v := v) r : v.adicCompletion F) := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let S : R → Set (v.adicCompletion F) := fun r =>
    completionResidueFiber (v := v) r ∩ localUnitShell v
  have hS_meas (r : R) : MeasurableSet (S r) :=
    (completionResidueFiber_measurable (v := v) r).inter
      (localUnitShell_compact (v := v)).measurableSet
  have hS_disj : Pairwise fun r r' => Disjoint (S r) (S r') := by
    intro r r' hrr'
    exact (completionResidueFiber_pairwise (v := v) hrr').mono
      (fun x hx => hx.1) (fun x hx => hx.1)
  have hS_union : (⋃ r : R, S r) = localUnitShell v := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
      exact hr.2
    · intro hx
      have hxO : x ∈ v.adicCompletionIntegers F := by
        rw [localUnitShell_eq_diff] at hx
        exact hx.1
      have hxUnion : x ∈ ⋃ r : R, completionResidueFiber (v := v) r := by
        rw [completionResidueFiber_iUnion]
        exact hxO
      rcases Set.mem_iUnion.mp hxUnion with ⟨r, hr⟩
      exact Set.mem_iUnion.mpr ⟨r, ⟨hr, hx⟩⟩
  have hfinite (r : R) : μ.μ (completionResidueFiber (v := v) r) ≠ ⊤ := by
    have hle : μ.μ (completionResidueFiber (v := v) r) ≤ 1 := by
      calc
        μ.μ (completionResidueFiber (v := v) r) ≤
            μ.μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
          measure_mono (fun _ hx => hx.1)
        _ = 1 := μ.norm_O
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hS_integrable (r : R) :
      IntegrableOn (localTerminalScalar D A l) (S r) μ.μ := by
    by_cases hr : r = 0
    · rw [hr]
      have hsempty : S 0 = ∅ := by
        ext x
        constructor
        · rintro ⟨hx, hu⟩
          have hb : x ∈ ball v 1 := by
            rw [← completionResidueFiber_zero_eq_ball (v := v)]
            exact hx
          rw [localUnitShell_eq_diff] at hu
          exact (hu.2 hb).elim
        · simp [S]
      rw [hsempty]
      exact integrableOn_empty
    · have hconst : Set.EqOn (localTerminalScalar D A l)
          (fun _ => localTerminalScalar D A l
            (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) := by
        intro x hx
        exact localTerminalScalar_const_on_fiber D A hv l r hr x hx
      have hconstInt : IntegrableOn (fun _ : v.adicCompletion F =>
          localTerminalScalar D A l (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) μ.μ := integrableOn_const (hfinite r)
      have hfiber : IntegrableOn (localTerminalScalar D A l)
          (completionResidueFiber (v := v) r) μ.μ :=
        (integrableOn_congr_fun hconst (completionResidueFiber_measurable (v := v) r)).2 hconstInt
      exact hfiber.mono_set (fun _ hx => hx.1)
  have hterm (r : R) :
      ∫ x in S r, localTerminalScalar D A l x ∂μ.μ =
        ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
          localTerminalScalar D A l
            (completionResidueCenter (v := v) r : v.adicCompletion F) := by
    by_cases hr : r = 0
    · subst r
      have hsempty : S 0 = ∅ := by
        ext x
        constructor
        · rintro ⟨hx, hu⟩
          have hb : x ∈ ball v 1 := by
            rw [← completionResidueFiber_zero_eq_ball (v := v)]
            exact hx
          rw [localUnitShell_eq_diff] at hu
          exact (hu.2 hb).elim
        · simp [S]
      have hcball := completionResidueCenter_zero_mem_ball (v := v)
      have hcnot : (completionResidueCenter (v := v) (0 : R) : v.adicCompletion F) ∉
          localUnitShell v := by
        intro hc
        change Valued.v (completionResidueCenter (v := v) (0 : R) : v.adicCompletion F) = 1 at hc
        change Valued.v (completionResidueCenter (v := v) (0 : R) : v.adicCompletion F) ≤
          WithZero.exp (-1 : ℤ) at hcball
        have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num
        have hc' : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
          simpa [hc] using hcball
        exact (not_le_of_gt hlt) hc'
      rw [hsempty]
      simp [localTerminalScalar, hcnot]
    · have hS_eq : S r = completionResidueFiber (v := v) r := by
        ext x
        constructor
        · exact fun hx => hx.1
        · intro hx
          refine ⟨hx, ?_⟩
          change Valued.v x = 1
          exact completionResidueFiber_val_one (v := v) r hr x hx
      rw [hS_eq]
      have hconst : Set.EqOn (localTerminalScalar D A l)
          (fun _ => localTerminalScalar D A l
            (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) := by
        intro x hx
        exact localTerminalScalar_const_on_fiber D A hv l r hr x hx
      calc
        _ = ∫ x in completionResidueFiber (v := v) r,
              (fun _ => localTerminalScalar D A l
                (completionResidueCenter (v := v) r : v.adicCompletion F)) x ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem
            (completionResidueFiber_measurable (v := v) r)] with x hx
          exact hconst hx
        _ = ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
              localTerminalScalar D A l
                (completionResidueCenter (v := v) r : v.adicCompletion F) := by
          simp [MeasureTheory.measureReal_def]
  calc
    _ = ∫ x in ⋃ r : R, S r, localTerminalScalar D A l x ∂μ.μ := by rw [hS_union]
    _ = ∑ r : R, ∫ x in S r, localTerminalScalar D A l x ∂μ.μ :=
      integral_iUnion_fintype hS_meas hS_disj hS_integrable
    _ = _ := by
      simp_rw [hterm]
      apply Finset.sum_congr rfl
      intro r hr
      rfl

private theorem localTerminalScalar_center_eq (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℕ) (r : 𝓞 F ⧸ v.asIdeal) :
    localTerminalScalar D A l (completionResidueCenter (v := v) r : v.adicCompletion F) =
      chiPow D v (algebraMap (𝓞 F) F r.out) (-2 * (l : ℤ)) *
        A.ψ v (algebraMap F (v.adicCompletion F) (-((r.out : F) / unif v))) := by
  classical
  by_cases hr : r = 0
  · subst r
    have hcball := completionResidueCenter_zero_mem_ball (v := v)
    have hcnot : (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
        v.adicCompletion F) ∉ localUnitShell v := by
      intro hc
      change Valued.v (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
        v.adicCompletion F) = 1 at hc
      change Valued.v (completionResidueCenter (v := v) (0 : 𝓞 F ⧸ v.asIdeal) :
        v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) at hcball
      have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
      have hle : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
        simpa [hc] using hcball
      exact (not_le_of_gt hlt) hle
    have hres0 : residue v (algebraMap (𝓞 F) F
        ((0 : 𝓞 F ⧸ v.asIdeal).out)) = 0 := by
      rw [localResidue_algebraMap]
      simpa using (Ideal.Quotient.mk_out (0 : 𝓞 F ⧸ v.asIdeal))
    simp [localTerminalScalar, hcnot, chiPow, hres0]
  · let a : 𝓞 F := r.out
    have hmk : Ideal.Quotient.mk v.asIdeal a = r := by
      simpa [a] using Ideal.Quotient.mk_out r
    have ha : a ∉ v.asIdeal := by
      intro hmem
      apply hr
      calc
        r = Ideal.Quotient.mk v.asIdeal a := hmk.symm
        _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hresne : residue v (algebraMap (𝓞 F) F a) ≠ 0 := by
      rw [localResidue_algebraMap, hmk]
      exact hr
    have haFne : (a : F) ≠ 0 := by
      intro hz
      have ha0 : a = 0 := (IsFractionRing.injective (𝓞 F) F) hz
      apply hr
      rw [← hmk]
      simp [ha0]
    let aF : Fˣ := Units.mk0 (a : F) haFne
    have hcu : (completionResidueCenter (v := v) r : v.adicCompletion F) ∈
        localUnitShell v := completionResidueCenter_val_one (v := v) r hr
    let cU : localUnitShell v := ⟨(completionResidueCenter (v := v) r : v.adicCompletion F), hcu⟩
    have hunit : localUnitShell.unit cU = toLoc v aF := by
      apply Units.ext
      change (completionResidueCenter (v := v) r : v.adicCompletion F) =
        (toLoc v aF : v.adicCompletion F)
      unfold completionResidueCenter
      change ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r.out :
        v.adicCompletionIntegers F) : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) (a : F)
      rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply
        (R := 𝓞 F) (K := F) v a]
      change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) =
        (algebraMap (𝓞 F) F a : v.adicCompletion F)
      rfl
    have hχ : localChi D v (localUnitShell.unit cU) = chi D v (a : F) := by
      rw [hunit]
      exact localChi_toLoc_integer_eq (v := v) D a ha aF rfl
    let j : ℤ := -2 * (l : ℤ)
    have hfield : localChiPowerField D j
        (completionResidueCenter (v := v) r : v.adicCompletion F) =
        localChi D v (localUnitShell.unit cU) ^ j := by
      change (if hc' : (completionResidueCenter (v := v) r : v.adicCompletion F) ≠ 0 then
        localChi D v (Units.mk0 _ hc') ^ j else 0) = _
      rw [dif_pos (localUnitShell_ne_zero cU)]
      rfl
    have hpow : localChiPowerField D j
        (completionResidueCenter (v := v) r : v.adicCompletion F) =
        chiPow D v (algebraMap (𝓞 F) F r.out) j := by
      rw [hfield, hχ]
      simp [chiPow, hresne, a, j]
    let πi : v.adicCompletion F :=
      (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
    have hπi : πi = algebraMap F (v.adicCompletion F) ((unif v)⁻¹ : F) := by
      simp [πi, unifLoc, toLoc]
    have hcenter : (completionResidueCenter (v := v) r : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (a : F) := by
      simp [completionResidueCenter, a]
    have harg : -(πi * (completionResidueCenter (v := v) r : v.adicCompletion F)) =
        algebraMap F (v.adicCompletion F) (-((a : F) / unif v)) := by
      rw [hπi, hcenter, ← map_mul, ← map_neg]
      congr 1
      field_simp [unif_ne_zero v]
    have hphase : A.ψ v (-(πi * (completionResidueCenter (v := v) r : v.adicCompletion F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) (-((a : F) / unif v))) := by
      rw [harg]
    simp only [localTerminalScalar, dif_pos hcu]
    rw [hpow, hphase]

private theorem chi_congr_residue (D : FieldData F) (x y : F)
    (hxy : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, hxy]

private theorem chiPow_neg_residue (D : FieldData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (j : ℤ) (x : 𝓞 F ⧸ v.asIdeal) :
    chiPow D v (algebraMap (𝓞 F) F (-x).out) j =
      chiPow D v (algebraMap (𝓞 F) F x.out) j := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  by_cases hx : x = 0
  · subst x
    have hres : residue v (algebraMap (𝓞 F) F ((0 : R).out)) = 0 := by
      rw [localResidue_algebraMap]
      simpa using (Ideal.Quotient.mk_out (0 : R))
    simp [chiPow, hres]
  · let a : 𝓞 F := x.out
    have hmk : Ideal.Quotient.mk v.asIdeal a = x := by
      simpa [a] using Ideal.Quotient.mk_out x
    have ha : a ∉ v.asIdeal := by
      intro hmem
      apply hx
      calc
        x = Ideal.Quotient.mk v.asIdeal a := hmk.symm
        _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hresA : residue v (algebraMap (𝓞 F) F a) = x := by
      rw [localResidue_algebraMap]
      exact hmk
    have hresNegOut : residue v (algebraMap (𝓞 F) F (-x).out) = -x := by
      rw [localResidue_algebraMap]
      simpa using (Ideal.Quotient.mk_out (-x))
    have hmkNeg : Ideal.Quotient.mk v.asIdeal (-a) = -x := by
      rw [map_neg, hmk]
    have hresNegA : residue v (algebraMap (𝓞 F) F (-a)) = -x := by
      rw [localResidue_algebraMap]
      exact hmkNeg
    have hresNegOutNe : residue v (algebraMap (𝓞 F) F (-x).out) ≠ 0 := by
      rw [hresNegOut]
      exact neg_ne_zero.mpr hx
    have hresANe : residue v (algebraMap (𝓞 F) F a) ≠ 0 := by
      rw [hresA]
      exact hx
    have hresOutNe : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
      simpa [a] using hresANe
    have hnegNot : -a ∉ v.asIdeal := by
      intro hmem
      apply ha
      have hneg : -(-a) ∈ v.asIdeal := v.asIdeal.neg_mem hmem
      simpa using hneg
    have hvalA : HeightOneSpectrum.valuation F v (a : F) = 1 :=
      (localResidue_ne_zero_local (v := v) (a : F) (v.valuation_le_one a)).mp hresANe
    have hvalNegA : HeightOneSpectrum.valuation F v ((-a : 𝓞 F) : F) = 1 := by
      change (v.valuation F) (-(a : F)) = 1
      rw [(v.valuation F).map_neg]
      exact hvalA
    have hvalMinusOne : HeightOneSpectrum.valuation F v (-1 : F) = 1 := by
      calc
        HeightOneSpectrum.valuation F v (-1 : F) =
            HeightOneSpectrum.valuation F v (1 : F) := (v.valuation F).map_neg 1
        _ = 1 := by simp
    have haFne : (a : F) ≠ 0 := by
      intro hz
      have ha0 : a = 0 := (IsFractionRing.injective (𝓞 F) F) hz
      apply hx
      calc
        x = Ideal.Quotient.mk v.asIdeal a := hmk.symm
        _ = 0 := by simp [ha0]
    let aF : Fˣ := Units.mk0 (a : F) haFne
    have haFval : (aF : F) = (a : F) := rfl
    let negAF : Fˣ := -aF
    have hnegAFval : (negAF : F) = (-a : F) := rfl
    have hLocA : IsLocUnit v (toLoc v aF) := localToLoc_isLocUnit (v := v) aF hvalA
    have hLocNegA : IsLocUnit v (toLoc v negAF) := by
      exact localToLoc_isLocUnit (v := v) negAF (by simpa [hnegAFval] using hvalNegA)
    let mF : Fˣ := -1
    have hmFval : (mF : F) = (-1 : F) := rfl
    have hLocMinusOne : IsLocUnit v (toLoc v mF) :=
      localToLoc_isLocUnit (v := v) mF (by simpa [hmFval] using hvalMinusOne)
    have hmulUnit : negAF = mF * aF := by
      apply Units.ext
      simp [negAF, mF]
    have htoLocNeg : toLoc v negAF = toLoc v mF * toLoc v aF := by
      rw [hmulUnit]
      exact (toLoc v).map_mul mF aF
    have hchiA : localChi D v (toLoc v aF) = chi D v (a : F) :=
      localChi_toLoc_integer_eq (v := v) D a ha aF rfl
    have hchiNegA : localChi D v (toLoc v negAF) = chi D v ((-a : 𝓞 F) : F) := by
      exact localChi_toLoc_integer_eq (v := v) D (-a) hnegNot negAF rfl
    have hlocalMinusOne : localChi D v (toLoc v mF) = 1 := by
      have hBasic := localChi_basic (D := D) (v := v) hv
      have hminus : (toLoc v mF : (v.adicCompletion F)ˣ) = -1 := by
        apply Units.ext
        simp [toLoc, mF]
      rw [hminus]
      exact hBasic.2.1
    have hmulχ := (localChi_basic (D := D) (v := v) hv).2.2.1
      (toLoc v mF) (toLoc v aF) hLocMinusOne hLocA
    have hchiNeg : chi D v ((-a : 𝓞 F) : F) = chi D v (a : F) := by
      calc
        chi D v ((-a : 𝓞 F) : F) = localChi D v (toLoc v negAF) := hchiNegA.symm
        _ = localChi D v (toLoc v mF * toLoc v aF) := by rw [htoLocNeg]
        _ = localChi D v (toLoc v mF) * localChi D v (toLoc v aF) := hmulχ
        _ = localChi D v (toLoc v aF) := by rw [hlocalMinusOne]; simp
        _ = chi D v (a : F) := hchiA
    have hchiCongr : chi D v (algebraMap (𝓞 F) F (-x).out) =
        chi D v ((-a : 𝓞 F) : F) := by
      apply chi_congr_residue
      rw [hresNegOut, hresNegA]
    simp only [chiPow, if_neg hresNegOutNe, if_neg hresOutNe]
    rw [hchiCongr, hchiNeg]

private theorem chi_algebraMap_pow_six (D : FieldData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a : 𝓞 F) (ha : a ∉ v.asIdeal) :
    chi D v (algebraMap (𝓞 F) F a) ^ (6 : ℕ) = 1 := by
  have hval : HeightOneSpectrum.valuation F v (a : F) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := a)).2 ha
  have haFne : (a : F) ≠ 0 := by
    intro hz
    have ha0 : a = 0 := (IsFractionRing.injective (𝓞 F) F) hz
    exact ha (by simpa [ha0])
  let aF : Fˣ := Units.mk0 (a : F) haFne
  have hLoc : IsLocUnit v (toLoc v aF) := localToLoc_isLocUnit (v := v) aF hval
  have hχ := (localChi_basic (D := D) (v := v) hv).2.2.2.1 (toLoc v aF) hLoc
  have hχeq : localChi D v (toLoc v aF) = chi D v (algebraMap (𝓞 F) F a) :=
    localChi_toLoc_integer_eq (v := v) D a ha aF rfl
  rw [← hχeq]
  exact hχ

private theorem gaussLoc_six (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (m : ℤ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    gaussLoc D A v (6 * m) = -((qv v : ℂ) ^ (-(1 / 2 : ℂ))) := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let term (r : R) : ℂ :=
    chiPow D v (algebraMap (𝓞 F) F r.out) (6 * m) *
      A.ψ v (algebraMap F (v.adicCompletion F) ((r.out : F) / unif v))
  have hψne : localAddChar (v := v) A ≠ 1 := localAddChar_ne_one A hd
  have hψsum : ∑ r : R, localAddChar (v := v) A r = 0 :=
    AddChar.sum_eq_zero_of_ne_one hψne
  have hdelta : ∑ r : R, (if r = 0 then (1 : ℂ) else 0) = 1 := by simp
  have hterm (r : R) : term r = localAddChar (v := v) A r -
      (if r = 0 then (1 : ℂ) else 0) := by
    by_cases hr : r = 0
    · subst r
      have hres : residue v (algebraMap (𝓞 F) F ((0 : R).out)) = 0 := by
        rw [localResidue_algebraMap]
        simpa using (Ideal.Quotient.mk_out (0 : R))
      simp [term, chiPow, hres, localAddChar_apply]
    · have hmk : Ideal.Quotient.mk v.asIdeal r.out = r := Ideal.Quotient.mk_out r
      have ha : r.out ∉ v.asIdeal := by
        intro hmem
        apply hr
        calc
          r = Ideal.Quotient.mk v.asIdeal r.out := hmk.symm
          _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      have hres : residue v (algebraMap (𝓞 F) F r.out) ≠ 0 := by
        rw [localResidue_algebraMap, hmk]
        exact hr
      have hχ6 := chi_algebraMap_pow_six D hv r.out ha
      have hχ6z : chi D v (algebraMap (𝓞 F) F r.out) ^ (6 : ℤ) = 1 := by
        exact_mod_cast hχ6
      have hpow : chi D v (algebraMap (𝓞 F) F r.out) ^ (6 * m) = 1 := by
        rw [zpow_mul, hχ6z]
        simp
      have hchiPow : chiPow D v (algebraMap (𝓞 F) F r.out) (6 * m) = 1 := by
        simp only [chiPow, if_neg hres]
        exact hpow
      simp [term, hchiPow, hr, localAddChar_apply]
  have hsum : ∑ r : R, term r = -1 := by
    calc
      _ = ∑ r : R, (localAddChar (v := v) A r -
            (if r = 0 then (1 : ℂ) else 0)) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
      _ = (∑ r : R, localAddChar (v := v) A r) -
            ∑ r : R, (if r = 0 then (1 : ℂ) else 0) := by
        rw [Finset.sum_sub_distrib]
      _ = -1 := by rw [hψsum, hdelta]; ring
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqnorm :
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (qv v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    change (((qv v) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_cpow hqpos.le]
    congr 1
    simp
  calc
    gaussLoc D A v (6 * m) =
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑ r : R, term r := by
      unfold gaussLoc
      have hfinsum (f : R → ℂ) : (∑ᶠ r : R, f r) = ∑ r : R, f r :=
        finsum_eq_sum_of_fintype f
      rw [hfinsum]
    _ = -((qv v : ℂ) ^ (-(1 / 2 : ℂ))) := by rw [hqnorm, hsum]; ring

private theorem localPsi_phase_neg_residue (A : AddCharData F) (r : 𝓞 F ⧸ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) (-(((-r).out : F) / unif v))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((r.out : F) / unif v)) := by
  have hmkNeg : Ideal.Quotient.mk v.asIdeal (-((-r).out)) = r := by
    have h := Ideal.Quotient.mk_out (-r)
    calc
      _ = -Ideal.Quotient.mk v.asIdeal ((-r).out) := by rw [map_neg]
      _ = -(-r) := by rw [h]
      _ = r := by simp
  have hmk : Ideal.Quotient.mk v.asIdeal r.out = r := Ideal.Quotient.mk_out r
  have hquot : Ideal.Quotient.mk v.asIdeal (-((-r).out)) =
      Ideal.Quotient.mk v.asIdeal r.out := hmkNeg.trans hmk.symm
  have hmem : -((-r).out) - r.out ∈ v.asIdeal := Ideal.Quotient.eq.mp hquot
  have hphase := localPsi_phaseCongr (A := A) (v := v) (-((-r).out)) r.out hmem
  have harg : -(((-r).out : F) / unif v) = (-((-r).out : F)) / unif v := by
    rw [neg_div]
  rw [harg]
  exact hphase

private theorem localTerminalScalar_integral_gauss (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℕ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    ∫ x in localUnitShell v, localTerminalScalar D A l x ∂μ.μ =
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * (l : ℤ)) := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let termNeg : R → ℂ := fun r =>
    chiPow D v (algebraMap (𝓞 F) F r.out) (-2 * (l : ℤ)) *
      A.ψ v (algebraMap F (v.adicCompletion F) (-((r.out : F) / unif v)))
  let termPos : R → ℂ := fun r =>
    chiPow D v (algebraMap (𝓞 F) F r.out) (-2 * (l : ℤ)) *
      A.ψ v (algebraMap F (v.adicCompletion F) ((r.out : F) / unif v))
  have hvol (r : R) :
      ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) =
        (qv v : ℂ)⁻¹ := by
    rw [completionResidueFiber_realMeasure μ r]
    simp
  have hcenter (r : R) :
      localTerminalScalar D A l (completionResidueCenter (v := v) r : v.adicCompletion F) =
        termNeg r := by
    simpa [termNeg] using localTerminalScalar_center_eq D A hv l r
  have hI : ∫ x in localUnitShell v, localTerminalScalar D A l x ∂μ.μ =
      (qv v : ℂ)⁻¹ * ∑ r : R, termNeg r := by
    rw [localTerminalScalar_integral_fiber_sum D A μ hv l]
    calc
      _ = ∑ r : R, (qv v : ℂ)⁻¹ * termNeg r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hvol, hcenter]
      _ = (qv v : ℂ)⁻¹ * ∑ r : R, termNeg r := by rw [Finset.mul_sum]
  have hterm (r : R) : termNeg (-r) = termPos r := by
    dsimp [termNeg, termPos]
    rw [chiPow_neg_residue D hv (-2 * (l : ℤ)) r, localPsi_phase_neg_residue A r]
  have hsum : (∑ r : R, termNeg r) = ∑ r : R, termPos r := by
    calc
      _ = ∑ r : R, termNeg (-r) := (Equiv.sum_comp (Equiv.neg R) termNeg).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqnorm :
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (qv v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    change (((qv v) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_cpow hqpos.le]
    congr 1
    simp
  have hgauss : gaussLoc D A v (-2 * (l : ℤ)) =
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * ∑ r : R, termPos r := by
    unfold gaussLoc
    have hfinsum (f : R → ℂ) : (∑ᶠ r : R, f r) = ∑ r : R, f r :=
      finsum_eq_sum_of_fintype f
    rw [hfinsum, hqnorm]
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hhalf : (qv v : ℂ) ^ (-(1 / 2 : ℂ)) *
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) = (qv v : ℂ)⁻¹ := by
    calc
      _ = (qv v : ℂ) ^ (-(1 / 2 : ℂ) + -(1 / 2 : ℂ)) :=
        (Complex.cpow_add _ _ hqne).symm
      _ = (qv v : ℂ) ^ (-1 : ℂ) := by congr 1 <;> ring
      _ = (qv v : ℂ)⁻¹ := Complex.cpow_neg_one _
  rw [hI, hsum]
  calc
    (qv v : ℂ)⁻¹ * ∑ r : R, termPos r =
        ((qv v : ℂ) ^ (-(1 / 2 : ℂ)) *
          (qv v : ℂ) ^ (-(1 / 2 : ℂ))) * ∑ r : R, termPos r := by rw [hhalf]
    _ = (qv v : ℂ) ^ (-(1 / 2 : ℂ)) *
          ((qv v : ℂ) ^ (-(1 / 2 : ℂ)) * ∑ r : R, termPos r) := by ring
    _ = (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * (l : ℤ)) := by rw [hgauss]

/-- The terminal shell coefficient `I_{l-1,l}` (eq:app-shell-integrals, `l = e+1`). -/
def shellTerm (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (l : ℕ) : ℂ :=
  if 3 ∣ l then -((qv v : ℂ)⁻¹) else (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * (l : ℤ))

private theorem localShellScalar_integral_tail_zero (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (e l : ℕ) (hgt : e + 1 < l) :
    ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ = 0 := by
  obtain ⟨t, ht, hψt⟩ := psi_conductor_unramified A v hd
  let scale : (v.adicCompletion F)ˣ := localShellScale e l
  let δ : v.adicCompletion F := ((scale⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t
  have hinvval : Valued.v ((scale⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp ((e : ℤ) - (l : ℤ)) := by
    calc
      Valued.v ((scale⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          (Valued.v (scale : v.adicCompletion F))⁻¹ := by simp
      _ = (WithZero.exp ((l : ℤ) - (e : ℤ)))⁻¹ := by
        rw [show scale = localShellScale (v := v) e l from rfl,
          localShellScale_valuation]
      _ = WithZero.exp ((e : ℤ) - (l : ℤ)) := by
        rw [← WithZero.exp_neg]
        congr 1
        ring
  have hδball : δ ∈ ball v 1 := by
    change Valued.v t ≤ WithZero.exp 1 at ht
    change Valued.v δ ≤ WithZero.exp (-1 : ℤ)
    dsimp [δ]
    rw [map_mul, hinvval]
    calc
      WithZero.exp ((e : ℤ) - (l : ℤ)) * Valued.v t ≤
          WithZero.exp ((e : ℤ) - (l : ℤ)) * WithZero.exp 1 := by gcongr
      _ = WithZero.exp ((e : ℤ) - (l : ℤ) + 1) := by rw [← WithZero.exp_add]
      _ ≤ WithZero.exp (-1 : ℤ) := by
        exact (WithZero.exp_le_exp).mpr (by omega)
  have hcdelta : (scale : v.adicCompletion F) * δ = t := by
    dsimp [δ]
    simp [scale, mul_assoc]
  have hψneg : A.ψ v (-t) ≠ 1 := by
    intro h
    apply hψt
    have h' : (A.ψ v t)⁻¹ = 1 := by
      simpa only [AddChar.map_neg_eq_inv] using h
    exact inv_eq_one.mp h'
  let f : v.adicCompletion F → ℂ := localShellScalar D A e l
  have hsmeas : MeasurableSet (localUnitShell v) := (localUnitShell_compact v).measurableSet
  have hInd : (localUnitShell v).indicator f = f := by
    funext x
    by_cases hx : x ∈ localUnitShell v <;> simp [f, localShellScalar, hx]
  have hf : Integrable f μ.μ := by
    have hfi := localShellScalar_integrableOn D A μ hv e l
    rw [← hInd]
    exact hfi.integrable_indicator hsmeas
  have hpoint (x : v.adicCompletion F) :
      f (x + δ) = A.ψ v (-t) * f x := by
    have hphase : A.ψ v (-((scale : v.adicCompletion F) * (x + δ))) =
        A.ψ v (-((scale : v.adicCompletion F) * x)) * A.ψ v (-t) := by
      have harg : -((scale : v.adicCompletion F) * (x + δ)) =
          -((scale : v.adicCompletion F) * x) + -t := by
        rw [mul_add, hcdelta]
        ring
      rw [harg, (A.ψ v).map_add_eq_mul]
    by_cases hx : x ∈ localUnitShell v
    · have hxplus : x + δ ∈ localUnitShell v := (localUnitShell_add_ball δ hδball x).2 hx
      have hχ := localChiPowerField_eq_of_ball_diff D hv (-2 * (l : ℤ)) x
        (x + δ) hx hxplus (by simpa using hδball)
      simp only [f, localShellScalar, dif_pos hxplus, dif_pos hx]
      rw [hχ, hphase]
      ring
    · have hxplus : x + δ ∉ localUnitShell v := by
        intro hxplus
        exact hx ((localUnitShell_add_ball δ hδball x).1 hxplus)
      simp [f, localShellScalar, hx, hxplus]
  have hshift : (∫ x, f (x + δ) ∂μ.μ) = ∫ x, f x ∂μ.μ := by
    simpa [add_comm] using integral_add_left_eq_self (μ := μ.μ) f δ
  have hlinear : (∫ x, f (x + δ) ∂μ.μ) = A.ψ v (-t) * ∫ x, f x ∂μ.μ := by
    calc
      _ = ∫ x, A.ψ v (-t) * f x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = _ := by rw [integral_const_mul]
  let J : ℂ := ∫ x, f x ∂μ.μ
  have hJ : J = A.ψ v (-t) * J := by
    calc
      J = ∫ x, f (x + δ) ∂μ.μ := hshift.symm
      _ = A.ψ v (-t) * ∫ x, f x ∂μ.μ := hlinear
      _ = A.ψ v (-t) * J := rfl
  have hmul : (A.ψ v (-t) - 1) * J = 0 := by
    calc
      _ = A.ψ v (-t) * J - J := by ring
      _ = J - J := by rw [hJ.symm]
      _ = 0 := sub_self _
  have hJzero : J = 0 := by
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact (hψneg (sub_eq_zero.mp hzero)).elim
    · exact hzero
  have hset : J = ∫ x in localUnitShell v, f x ∂μ.μ := by
    dsimp [J]
    calc
      ∫ x, f x ∂μ.μ = ∫ x, (localUnitShell v).indicator f x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact (congrFun hInd x).symm
      _ = ∫ x in localUnitShell v, f x ∂μ.μ := MeasureTheory.integral_indicator hsmeas
  rw [← hset]
  exact hJzero

private theorem localShellScalar_integral_cases (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (e l : ℕ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ =
      if l ≤ e then (if 3 ∣ l then ((1 - (qv v)⁻¹ : ℝ) : ℂ) else 0)
      else if l = e + 1 then shellTerm D A v l else 0 := by
  classical
  by_cases hle : l ≤ e
  · have hphase (x : v.adicCompletion F) (hx : x ∈ localUnitShell v) :
        A.ψ v (-((localShellScale (v := v) e l : v.adicCompletion F) * x)) = 1 := by
      have hxval : Valued.v x = 1 := hx
      have hscale := localShellScale_valuation (v := v) e l
      have hprod : (localShellScale (v := v) e l : v.adicCompletion F) * x ∈
          v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        rw [map_mul, hscale, hxval, mul_one]
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).mpr (by omega)
      exact A.integral v _ ((v.adicCompletionIntegers F).neg_mem _ hprod)
    have hI :
        ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ =
          ∫ x in localUnitShell v, localChiPowerField D (-2 * (l : ℤ)) x ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
      simp only [localShellScalar, dif_pos hx]
      rw [hphase x hx]
      simp
    rw [if_pos hle, hI, localUnitShell_chiPower_integral D μ hv l]
    by_cases h3 : 3 ∣ l <;> simp [h3]
  · by_cases heq : l = e + 1
    · subst l
      have hscale : localShellScale (v := v) e (e + 1) = (unifLoc v)⁻¹ := by
        change unifLoc v ^ ((e : ℤ) - ((e + 1 : ℕ) : ℤ)) = (unifLoc v)⁻¹
        have hexp : (e : ℤ) - ((e + 1 : ℕ) : ℤ) = -1 := by omega
        rw [hexp]
        simp
      have hI :
          ∫ x in localUnitShell v, localShellScalar D A e (e + 1) x ∂μ.μ =
            ∫ x in localUnitShell v, localTerminalScalar D A (e + 1) x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
        simp only [localShellScalar, localTerminalScalar, dif_pos hx]
        rw [hscale]
      have hterminal := localTerminalScalar_integral_gauss D A μ hv (e + 1)
      have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
      have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
      have hhalf : (qv v : ℂ) ^ (-(1 / 2 : ℂ)) *
          (qv v : ℂ) ^ (-(1 / 2 : ℂ)) = (qv v : ℂ)⁻¹ := by
        calc
          _ = (qv v : ℂ) ^ (-(1 / 2 : ℂ) + -(1 / 2 : ℂ)) :=
            (Complex.cpow_add _ _ hqne).symm
          _ = (qv v : ℂ) ^ (-1 : ℂ) := by congr 1 <;> ring
          _ = (qv v : ℂ)⁻¹ := Complex.cpow_neg_one _
      have hterminalEq :
          ∫ x in localUnitShell v, localTerminalScalar D A (e + 1) x ∂μ.μ =
            shellTerm D A v (e + 1) := by
        rw [hterminal]
        by_cases hdiv : 3 ∣ e + 1
        · obtain ⟨k, hk⟩ := hdiv
          have hdiv' : 3 ∣ e + 1 := ⟨k, hk⟩
          have hj : -2 * ((e + 1 : ℕ) : ℤ) = 6 * (-(k : ℤ)) := by
            rw [hk]
            push_cast
            ring
          have hgs := gaussLoc_six D A v hv hd (-(k : ℤ))
          rw [shellTerm, if_pos hdiv', hj, hgs, mul_neg, hhalf]
        · rw [shellTerm, if_neg hdiv]
      rw [if_neg (by omega : ¬(e + 1 ≤ e)), if_pos rfl, hI, hterminalEq]
    · have hgt : e + 1 < l := by omega
      rw [if_neg hle, if_neg heq]
      exact localShellScalar_integral_tail_zero D A μ hv hd e l hgt

private theorem absFin_unifLoc : absFin v (unifLoc v : v.adicCompletion F) = (qv v)⁻¹ := by
  let K := v.adicCompletion F
  let q : NNReal := (Ideal.absNorm v.asIdeal : NNReal)
  have hunif : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπval : Valued.v (unifLoc v : K) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (unifLoc v : K) = algebraMap F K (unif v) := by
      simp [K, unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif v : F) : K) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπnorm : ‖(unifLoc v : K)‖₊ = q⁻¹ := by
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
    absFin v (unifLoc v : K) = ‖(unifLoc v : K)‖ := absFin_eq_norm v _
    _ = ((‖(unifLoc v : K)‖₊ : NNReal) : ℝ) := by simp
    _ = ((q⁻¹ : NNReal) : ℝ) := by rw [hπnorm]
    _ = (qv v)⁻¹ := by simp [q, qv]

private theorem absFin_zpow (u : (v.adicCompletion F)ˣ) (j : ℤ) :
    absFin v ((u ^ j : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      absFin v (u : v.adicCompletion F) ^ j := by
  rw [absFin_eq_norm, absFin_eq_norm]
  simp [norm_zpow]

private theorem absFin_locUnit_eq_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : absFin v (u : v.adicCompletion F) = 1 := by
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hu]
  simp

private theorem localIsLocUnit_of_valued_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : IsLocUnit v u := by
  let U : localUnitShell v := ⟨(u : v.adicCompletion F), hu⟩
  have hU : localUnitShell.unit U = u := by
    apply Units.ext
    rfl
  rw [← hU]
  exact localUnitShell_isLocUnit U

private theorem unifLoc_zpow_valuation (j : ℤ) :
    Valued.v ((unifLoc v ^ j : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-j) := by
  have hπval : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hunif : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
      dsimp [unif]
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = WithZero.exp (-1 : ℤ)
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπval, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem localSpherical_shell_value (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (s : ℂ) (f0 : L.L → T.V) (hf0 : IsSection L T s f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (l : ℕ) (hl : 0 < l)
    (u : (v.adicCompletion F)ˣ) (huval : Valued.v (u : v.adicCompletion F) = 1) :
    f0 (L.w * L.n (Multiplicative.ofAdd
      (((unifLoc v ^ (-(l : ℤ)) * u : (v.adicCompletion F)ˣ) : v.adicCompletion F)))) =
      ((qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) *
        localChi D v u ^ (-2 * (l : ℤ))) • B.e (2 * (l : ZMod 3)) := by
  let π : (v.adicCompletion F)ˣ := unifLoc v
  let Hunit : (v.adicCompletion F)ˣ := π ^ (-(l : ℤ)) * u
  let X : (v.adicCompletion F)ˣ := Hunit⁻¹
  let Y : (v.adicCompletion F)ˣ := -(X * X)
  let u0 : (v.adicCompletion F)ˣ := (-1) * u ^ (-2 : ℤ)
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    simpa [π] using unifLoc_zpow_valuation (v := v) (1 : ℤ)
  have hHval : Valued.v (Hunit : v.adicCompletion F) = WithZero.exp (l : ℤ) := by
    calc
      Valued.v (Hunit : v.adicCompletion F) =
          Valued.v ((π ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            Valued.v (u : v.adicCompletion F) := by simp [Hunit]
      _ = WithZero.exp (l : ℤ) * 1 := by
        rw [unifLoc_zpow_valuation (v := v) (-(l : ℤ)), huval]
        simp
      _ = WithZero.exp (l : ℤ) := by simp
  have hXval : Valued.v (X : v.adicCompletion F) = WithZero.exp (-(l : ℤ)) := by
    calc
      _ = (Valued.v (Hunit : v.adicCompletion F))⁻¹ := by simp [X]
      _ = (WithZero.exp (l : ℤ))⁻¹ := by rw [hHval]
      _ = WithZero.exp (-(l : ℤ)) := by rw [← WithZero.exp_neg]
  have hXlt : Valued.v (X : v.adicCompletion F) < 1 := by
    rw [hXval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu0val : Valued.v (u0 : v.adicCompletion F) = 1 := by
    simp [u0, huval]
  have hu0Loc : IsLocUnit v u0 := localIsLocUnit_of_valued_one (v := v) u0 hu0val
  have hXinv : X = π ^ (l : ℤ) * u⁻¹ := by
    dsimp [X, Hunit]
    group
    exact mul_comm _ _
  have hXcoe : (X : v.adicCompletion F) =
      (π ^ (l : ℤ) : v.adicCompletion F) * (u⁻¹ : v.adicCompletion F) := by
    have h := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hXinv
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val] using h
  have hπsqU : (π ^ (l : ℤ) : (v.adicCompletion F)ˣ) ^ 2 =
      π ^ (2 * (l : ℤ)) := by
    calc
      (π ^ (l : ℤ) : (v.adicCompletion F)ˣ) ^ 2 =
          (π ^ (l : ℤ) : (v.adicCompletion F)ˣ) ^ (2 : ℤ) :=
        (zpow_natCast (π ^ (l : ℤ)) 2).symm
      _ = π ^ ((l : ℤ) * 2) := (zpow_mul π (l : ℤ) 2).symm
      _ = π ^ (2 * (l : ℤ)) := congrArg (fun n : ℤ => π ^ n) (by ring)
  have huInvSqU : (u⁻¹ : (v.adicCompletion F)ˣ) ^ 2 = u ^ (-2 : ℤ) := by
    rw [pow_two]
    group
  have hπsqK : ((π ^ (l : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 =
      ((π ^ (2 * (l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    have h := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hπsqU
    simpa only [Units.val_pow_eq_pow_val] using h
  have huInvSqK : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 =
      ((u ^ (-2 : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    have h := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) huInvSqU
    simpa only [Units.val_pow_eq_pow_val] using h
  have hY : Y = π ^ (2 * (l : ℤ)) * u0 := by
    dsimp [Y, u0]
    rw [hXinv]
    rw [neg_eq_neg_one_mul]
    calc
      _ = (-1 : (v.adicCompletion F)ˣ) *
            (π ^ (l : ℤ) * π ^ (l : ℤ)) * (u⁻¹ * u⁻¹) := by
        ac_rfl
      _ = (-1 : (v.adicCompletion F)ˣ) * (π ^ (2 * (l : ℤ))) *
            (u ^ (-2 : ℤ)) := by
        rw [← pow_two, hπsqU]
        rw [← pow_two, huInvSqU]
      _ = π ^ (2 * (l : ℤ)) * ((-1 : (v.adicCompletion F)ˣ) * u ^ (-2 : ℤ)) := by
        rw [mul_comm (-1 : (v.adicCompletion F)ˣ) (π ^ (2 * (l : ℤ)))]
        rw [mul_assoc]
  have hAbsY : absFin v (Y : v.adicCompletion F) =
      (qv v) ^ (-2 * (l : ℤ)) := by
    rw [hY]
    change absFin v (((π ^ (2 * (l : ℤ)) : (v.adicCompletion F)ˣ) * u0 :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) = _
    calc
      _ = absFin v ((π ^ (2 * (l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            absFin v (u0 : v.adicCompletion F) := absFin_mul v _ _
      _ = (qv v)⁻¹ ^ (2 * (l : ℤ)) * 1 := by
        rw [absFin_zpow, absFin_unifLoc, absFin_locUnit_eq_one (v := v) u0 hu0val]
      _ = (qv v) ^ (-2 * (l : ℤ)) := by
        rw [inv_zpow']
        have hexp : -(2 * (l : ℤ)) = -2 * (l : ℤ) := by ring
        rw [hexp]
        simp
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hAbsYReal : absFin v (Y : v.adicCompletion F) =
      (qv v) ^ (((-2 * (l : ℤ)) : ℤ) : ℝ) := by
    rw [hAbsY]
    exact (Real.rpow_intCast (qv v) (-2 * (l : ℤ))).symm
  have hAbsYComplex : (absFin v (Y : v.adicCompletion F) : ℂ) =
      (qv v : ℂ) ^ ((-2 * (l : ℤ)) : ℂ) := by
    rw [hAbsYReal, Complex.ofReal_cpow hqpos.le]
    congr 1
    push_cast <;> rfl
  have ha : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hlog : Complex.log (qv v : ℂ) = (Real.log (qv v) : ℂ) :=
    (Complex.ofReal_log hqpos.le).symm
  let a : ℂ := (-2 * (l : ℤ) : ℂ)
  let b : ℂ := (1 : ℂ) / 2 + s
  have him : (Complex.log (qv v : ℂ) * a).im = 0 := by
    simp [a, hlog]
  have hcpow1 : -Real.pi < (Complex.log (qv v : ℂ) * a).im := by
    rw [him]
    exact neg_lt_zero.mpr Real.pi_pos
  have hcpow2 : (Complex.log (qv v : ℂ) * a).im ≤ Real.pi := by
    rw [him]
    exact le_of_lt Real.pi_pos
  have hnormPow :
      ((absFin v (Y : v.adicCompletion F) : ℝ) : ℂ) ^ b =
        (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) := by
    rw [hAbsYComplex]
    have hmul : ((qv v : ℂ) ^ a) ^ b = (qv v : ℂ) ^ (a * b) :=
      (Complex.cpow_mul b hcpow1 hcpow2).symm
    rw [hmul]
    have hexp : a * b = -(l : ℂ) * (1 + 2 * s) := by
      have hcast : ((l : ℤ) : ℂ) = (l : ℂ) := by norm_cast
      dsimp [a, b]
      rw [hcast]
      ring_nf
    rw [hexp]
  have huInvLoc : IsLocUnit v (u⁻¹) := by
    have hval : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [huval]
    exact localIsLocUnit_of_valued_one (v := v) (u⁻¹) hval
  let m : (v.adicCompletion F)ˣ := -1
  have hmval : Valued.v (m : v.adicCompletion F) = 1 := by simp [m]
  have hmLoc : IsLocUnit v m := localIsLocUnit_of_valued_one (v := v) m hmval
  have huInvSqLoc : IsLocUnit v (u ^ (-2 : ℤ)) := by
    have hval : Valued.v ((u ^ (-2 : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [huval]
    exact localIsLocUnit_of_valued_one (v := v) (u ^ (-2 : ℤ)) hval
  have hBasic := localChi_basic (D := D) (v := v) hv
  let χu : ℂ := localChi D v u
  have hχne : χu ≠ 0 := by
    have h6 := hBasic.2.2.2.1 u (localIsLocUnit_of_valued_one (v := v) u huval)
    intro hz
    have hz' : localChi D v u = 0 := by simpa [χu] using hz
    rw [hz'] at h6
    norm_num at h6
  have hχ6 : χu ^ (6 : ℤ) = 1 := by
    have h6 := hBasic.2.2.2.1 u (localIsLocUnit_of_valued_one (v := v) u huval)
    simpa [χu] using h6
  have hminusχ : localChi D v m = 1 := by
    have hminus := hBasic.2.1
    simpa [m] using hminus
  have hmulUInv := hBasic.2.2.1 u u⁻¹
    (localIsLocUnit_of_valued_one (v := v) u huval) huInvLoc
  have hmulUInv' : χu * localChi D v (u⁻¹) = 1 := by
    calc
      _ = localChi D v (u * u⁻¹) := hmulUInv.symm
      _ = localChi D v 1 := by rw [mul_inv_cancel]
      _ = 1 := hBasic.1
  have hInvχ : localChi D v (u⁻¹) = χu⁻¹ := by
    have hcomm : localChi D v (u⁻¹) * χu = 1 := by simpa [mul_comm] using hmulUInv'
    exact eq_inv_of_mul_eq_one_left hcomm
  have hmulInvSq := hBasic.2.2.1 (u⁻¹) (u⁻¹) huInvLoc huInvLoc
  have huInvSq : u⁻¹ * u⁻¹ = u ^ (-2 : ℤ) := by group
  have hchiInvSq : localChi D v (u ^ (-2 : ℤ)) = localChi D v (u⁻¹) * localChi D v (u⁻¹) := by
    rw [← huInvSq]
    exact hmulInvSq
  have hInvSqχ : χu⁻¹ * χu⁻¹ = χu ^ (-2 : ℤ) := by group
  have hmul0 := hBasic.2.2.1 m (u ^ (-2 : ℤ)) hmLoc huInvSqLoc
  have hu0χ : localChi D v u0 = χu ^ (-2 : ℤ) := by
    calc
      localChi D v u0 = localChi D v (m * (u ^ (-2 : ℤ))) := by simp [u0, m]
      _ = localChi D v m * localChi D v (u ^ (-2 : ℤ)) := hmul0
      _ = 1 * (localChi D v (u⁻¹) * localChi D v (u⁻¹)) := by rw [hminusχ, hchiInvSq]
      _ = χu ^ (-2 : ℤ) := by rw [hInvχ]; simpa using hInvSqχ
  have hchiPower : localChi D v u0 ^ (4 * (l : ℤ)) = χu ^ (-2 * (l : ℤ)) := by
    rw [hu0χ]
    calc
      (χu ^ (-2 : ℤ)) ^ (4 * (l : ℤ)) = χu ^ ((-2 : ℤ) * (4 * (l : ℤ))) :=
        (zpow_mul χu (-2 : ℤ) (4 * (l : ℤ))).symm
      _ = χu ^ ((-2 : ℤ) * (l : ℤ) + 6 * (-(l : ℤ))) :=
        congrArg (fun n : ℤ => χu ^ n) (by ring)
      _ = χu ^ ((-2 : ℤ) * (l : ℤ)) * χu ^ (6 * (-(l : ℤ))) := by
        rw [zpow_add₀ hχne]
      _ = χu ^ ((-2 : ℤ) * (l : ℤ)) := by
        have hsix : χu ^ (6 * (-(l : ℤ))) = 1 := by
          calc
            χu ^ (6 * (-(l : ℤ))) = (χu ^ (6 : ℤ)) ^ (-(l : ℤ)) := zpow_mul χu 6 (-(l : ℤ))
            _ = 1 := by rw [hχ6]; simp
        rw [hsix]
        simp
  have hAction : T.σa Y (B.e 0) =
      localChi D v u0 ^ (4 * (l : ℤ)) • B.e (2 * (l : ZMod 3)) := by
    rw [hY]
    have hAct := B.act (2 * (l : ℤ)) u0 hu0Loc 0
    simp at hAct
    have hExp : (2 : ℤ) * (2 * (l : ℤ)) = 4 * (l : ℤ) := by ring
    rw [hExp] at hAct
    simpa [π, mul_assoc] using hAct
  have hcov := hf0.1 (X : v.adicCompletion F) Y 1
  simp only [mul_one] at hcov
  rw [h1] at hcov
  have hremove : f0 (L.n (Multiplicative.ofAdd (X : v.adicCompletion F)) *
      L.a Y * L.nbar (Multiplicative.ofAdd (X : v.adicCompletion F))) =
      f0 (L.n (Multiplicative.ofAdd (X : v.adicCompletion F)) * L.a Y) := by
    apply hK
    exact τ.nbar_mem _ hXlt
  have hvalue : f0 (L.w * L.n (Multiplicative.ofAdd (Hunit : v.adicCompletion F))) =
      ((absFin v Y : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s) • T.σa Y (B.e 0) := by
    calc
      _ = f0 (L.n (Multiplicative.ofAdd (X : v.adicCompletion F)) * L.a Y *
            L.nbar (Multiplicative.ofAdd (X : v.adicCompletion F))) := by
        rw [L.lift_wn Hunit]
      _ = f0 (L.n (Multiplicative.ofAdd (X : v.adicCompletion F)) * L.a Y) := hremove
      _ = ((absFin v Y : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s) • T.σa Y (B.e 0) := hcov
  calc
    _ = ((absFin v Y : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s) •
          (localChi D v u0 ^ (4 * (l : ℤ)) • B.e (2 * (l : ZMod 3))) := by rw [hvalue, hAction]
    _ = ((qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) *
          localChi D v u ^ (-2 * (l : ℤ))) • B.e (2 * (l : ZMod 3)) := by
      rw [smul_smul, hnormPow, hchiPower]

private def localShellAnnulus (l : ℕ) : Set (v.adicCompletion F) :=
  (fun u : v.adicCompletion F =>
    ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) ''
      localUnitShell v

private theorem localShellAnnulus_isCompact (l : ℕ) : IsCompact (localShellAnnulus (v := v) l) := by
  unfold localShellAnnulus
  exact (localUnitShell_compact v).image (continuous_const.mul continuous_id)

private theorem integral_localShellAnnulus (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : LocHaar v) (l : ℕ) (f : v.adicCompletion F → E) :
    ∫ x in localShellAnnulus (v := v) l, f x ∂μ.μ =
      absFin v (unifLoc v ^ (-(l : ℤ))) •
        ∫ u in localUnitShell v,
          f (((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u)
            ∂μ.μ := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (-(l : ℤ))
  let ann := localShellAnnulus (v := v) l
  let g : v.adicCompletion F → E := ann.indicator f
  have hannMeas : MeasurableSet ann := (localShellAnnulus_isCompact (v := v) l).measurableSet
  have hshellMeas : MeasurableSet (localUnitShell v) := (localUnitShell_compact v).measurableSet
  have htrans (x : v.adicCompletion F) : g ((a : v.adicCompletion F) * x) =
      (localUnitShell v).indicator (fun u =>
        f ((a : v.adicCompletion F) * u)) x := by
    by_cases hx : x ∈ localUnitShell v
    · have hax : (a : v.adicCompletion F) * x ∈ ann := by
        exact ⟨x, hx, rfl⟩
      simp [g, ann, hax, hx]
    · have hax : (a : v.adicCompletion F) * x ∉ ann := by
        rintro ⟨y, hy, hEq⟩
        apply hx
        have hxy : y = x := by
          apply mul_left_cancel₀ (Units.ne_zero a)
          exact hEq
        simpa [hxy] using hy
      simp [g, ann, hax, hx]
  have hscale := LocHaar.integral_comp_mul μ a g
  have htransInt :
      ∫ x, g ((a : v.adicCompletion F) * x) ∂μ.μ =
        ∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ := by
    calc
      _ = ∫ x, (localUnitShell v).indicator
            (fun u => f ((a : v.adicCompletion F) * u)) x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact htrans x
      _ = _ := MeasureTheory.integral_indicator hshellMeas
  have hAnnInt : ∫ x, g x ∂μ.μ = ∫ x in ann, f x ∂μ.μ :=
    MeasureTheory.integral_indicator hannMeas
  have hsc_eq :
      ∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ =
        (absFin v a)⁻¹ • ∫ x in ann, f x ∂μ.μ := by
    calc
      _ = ∫ x, g ((a : v.adicCompletion F) * x) ∂μ.μ := htransInt.symm
      _ = (absFin v a)⁻¹ • ∫ x, g x ∂μ.μ := hscale
      _ = (absFin v a)⁻¹ • ∫ x in ann, f x ∂μ.μ := by rw [hAnnInt]
  have ha0 : absFin v (a : v.adicCompletion F) ≠ 0 :=
    ne_of_gt (absFin_pos (Units.ne_zero a))
  have hscaled : ∫ x in ann, f x ∂μ.μ =
      absFin v a • ∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ := by
    calc
      _ = absFin v a • ((absFin v a)⁻¹ • ∫ x in ann, f x ∂μ.μ) := by
        rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
      _ = _ := by rw [← hsc_eq]
  simpa [a] using hscaled

private theorem localShellAnnulus_valuation (l : ℕ) (x : v.adicCompletion F) :
    x ∈ localShellAnnulus (v := v) l ↔ Valued.v x = WithZero.exp (l : ℤ) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change Valued.v (((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) * u) = WithZero.exp (l : ℤ)
    have hscale : Valued.v ((unifLoc v ^ (-(l : ℤ) : ℤ) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) = WithZero.exp (l : ℤ) := by
      simpa using unifLoc_zpow_valuation (v := v) (-(l : ℤ))
    rw [map_mul, hscale]
    change Valued.v u = 1 at hu
    rw [hu, mul_one]
  · intro hx
    have hxne : x ≠ 0 := by
      intro hz
      rw [hz] at hx
      have hzero : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (l : ℤ) := by
        simpa using hx
      exact (Ne.symm (WithZero.exp_ne_zero : WithZero.exp (l : ℤ) ≠ 0)) hzero
    let xU : (v.adicCompletion F)ˣ := Units.mk0 x hxne
    let u : (v.adicCompletion F)ˣ := unifLoc v ^ (l : ℤ) * xU
    have huval : Valued.v (u : v.adicCompletion F) = 1 := by
      calc
        Valued.v (u : v.adicCompletion F) =
            Valued.v ((unifLoc v ^ (l : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
              Valued.v (xU : v.adicCompletion F) := by simp [u]
        _ = WithZero.exp (-(l : ℤ)) * WithZero.exp (l : ℤ) := by
          rw [unifLoc_zpow_valuation, Units.val_mk0, hx]
        _ = 1 := by rw [← WithZero.exp_add]; simp
    refine ⟨u, huval, ?_⟩
    dsimp [u, xU]
    simp [mul_assoc]

private theorem localShellAnnulus_pairwise_disjoint (M : ℕ) :
    Pairwise (fun l l' : Finset.Icc 1 M =>
      Disjoint (localShellAnnulus (v := v) l.1) (localShellAnnulus (v := v) l'.1)) := by
  intro l l' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have hval := (localShellAnnulus_valuation (v := v) l.1 x).mp hx
  have hval' := (localShellAnnulus_valuation (v := v) l'.1 x).mp hx'
  have hneq : (l.1 : ℤ) ≠ (l'.1 : ℤ) := by
    intro h
    apply hne
    apply Subtype.ext
    exact_mod_cast h
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have h : WithZero.exp (l.1 : ℤ) < WithZero.exp (l'.1 : ℤ) :=
      (WithZero.exp_lt_exp).mpr hlt
    have heq : WithZero.exp (l.1 : ℤ) = WithZero.exp (l'.1 : ℤ) := hval.symm.trans hval'
    rw [heq] at h
    exact (lt_irrefl _ h)
  · have h : WithZero.exp (l'.1 : ℤ) < WithZero.exp (l.1 : ℤ) :=
      (WithZero.exp_lt_exp).mpr hgt
    have heq : WithZero.exp (l'.1 : ℤ) = WithZero.exp (l.1 : ℤ) := hval'.symm.trans hval
    rw [heq] at h
    exact (lt_irrefl _ h)

private theorem localShellAnnulus_partition (M : ℕ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∪
      ⋃ l : Finset.Icc 1 M, localShellAnnulus (v := v) l.1 = ball v (-(M : ℤ)) := by
  ext x
  constructor
  · rintro (hxO | hxShell)
    · have hxVal : Valued.v x ≤ 1 := by
        rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hxO
      have hbound : Valued.v x ≤ WithZero.exp (M : ℤ) := hxVal.trans (by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).mpr (by omega))
      simpa [ball] using hbound
    · rcases Set.mem_iUnion.mp hxShell with ⟨l, hl⟩
      have hxVal := (localShellAnnulus_valuation (v := v) l.1 x).mp hl
      have hupper : l.1 ≤ M := (Finset.mem_Icc.mp l.property).2
      have hbound : Valued.v x ≤ WithZero.exp (M : ℤ) := by
        rw [hxVal]
        exact (WithZero.exp_le_exp).mpr (by exact_mod_cast hupper)
      simpa [ball] using hbound
  · intro hxBall
    have hxBallVal : Valued.v x ≤ WithZero.exp (M : ℤ) := by simpa [ball] using hxBall
    by_cases hxO : x ∈ v.adicCompletionIntegers F
    · exact Or.inl hxO
    · have hvalne : Valued.v x ≠ 0 := by
        intro hzero
        apply hxO
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, hzero]
        exact bot_le
      lift Valued.v x to ℤ using hvalne with n hn
      have hnPos : 1 ≤ n := by
        have hnnot : ¬WithZero.exp n ≤ 1 := by
          intro hnle
          apply hxO
          rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          rw [← hn]
          exact hnle
        have hnnot' : ¬n ≤ 0 := by
          intro hnonpos
          apply hnnot
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          exact hnonpos
        omega
      have hnLe : n ≤ (M : ℤ) := by
        have h := hxBallVal
        exact (WithZero.exp_le_exp).mp h
      have hnonneg : 0 ≤ n := by omega
      have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnonneg
      have hnPosNat : 1 ≤ n.toNat := by
        have h : (1 : ℤ) ≤ (n.toNat : ℤ) := by simpa [hcast] using hnPos
        exact_mod_cast h
      have hnLeNat : n.toNat ≤ M := by
        have h' : (n.toNat : ℤ) ≤ (M : ℤ) := by simpa [hcast] using hnLe
        exact_mod_cast h'
      let l : Finset.Icc 1 M := ⟨n.toNat, Finset.mem_Icc.mpr ⟨hnPosNat, hnLeNat⟩⟩
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨l, ?_⟩
      apply (localShellAnnulus_valuation (v := v) l.1 x).2
      rw [hcast, hn]

private theorem jacquetTrunc_scale (L : FinLocalCover D H v) (A : AddCharData F)
    (μ : LocHaar v) (e M : ℕ) (f : L.L → V) :
    jacquetTrunc L A μ M (rtr (L.a (unifLoc v ^ (e : ℤ))) f) =
      absFin v (unifLoc v ^ (e : ℤ)) •
        ∫ Hh in ball v (-((e + M : ℕ) : ℤ)),
          A.ψ v (-(((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) * Hh)) •
            f (L.w * L.n (Multiplicative.ofAdd
              (((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * Hh)) *
                L.a (unifLoc v ^ (e : ℤ))) ∂μ.μ := by
  classical
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (e : ℤ)
  let g : v.adicCompletion F → V := fun x =>
    A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x) * L.a a)
  let Fset : Set (v.adicCompletion F) := ball v (-(M : ℤ))
  let gset : v.adicCompletion F → V := Fset.indicator g
  let Hset : Set (v.adicCompletion F) := (fun x => (a : v.adicCompletion F) * x) ⁻¹' Fset
  have hvalA : Valued.v (a : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    simpa [a] using unifLoc_zpow_valuation (v := v) (e : ℤ)
  have hballMap (x : v.adicCompletion F) :
      (a : v.adicCompletion F) * x ∈ Fset ↔ x ∈ ball v (-((e + M : ℕ) : ℤ)) := by
    simp only [Fset, ball, Set.mem_setOf_eq]
    by_cases hx0 : Valued.v x = 0
    · simp [hx0]
    · lift Valued.v x to ℤ using hx0 with n hn
      rw [map_mul, hvalA, ← hn, ← WithZero.exp_add]
      simp only [WithZero.exp_le_exp]
      push_cast
      omega
  have hHsetEq : Hset = ball v (-((e + M : ℕ) : ℤ)) := by
    ext x
    exact hballMap x
  have hpoint (x : v.adicCompletion F) :
      gset ((a : v.adicCompletion F) * x) =
        Hset.indicator (fun y => g ((a : v.adicCompletion F) * y)) x := by
    by_cases hx : x ∈ Hset
    · have hax : (a : v.adicCompletion F) * x ∈ Fset := hx
      simp [gset, Hset, hax, hx]
    · have hax : (a : v.adicCompletion F) * x ∉ Fset := by
        intro h
        exact hx h
      simp [gset, Hset, hax, hx]
  have hballMeas (N : ℕ) : MeasurableSet (ball v (-(N : ℤ))) := by
    exact (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).measurableSet
  have hHsetMeas : MeasurableSet Hset := by rw [hHsetEq]; exact hballMeas (e + M)
  have hFsetMeas : MeasurableSet Fset := hballMeas M
  have hJac : jacquetTrunc L A μ M (rtr (L.a a) f) = ∫ x, gset x ∂μ.μ := by
    calc
      _ = ∫ x in Fset, g x ∂μ.μ := rfl
      _ = ∫ x, gset x ∂μ.μ := by
        symm
        simpa [gset] using (MeasureTheory.integral_indicator hFsetMeas
          (f := g) (μ := μ.μ))
  have htrans :
      ∫ x, gset ((a : v.adicCompletion F) * x) ∂μ.μ =
        ∫ x in Hset, g ((a : v.adicCompletion F) * x) ∂μ.μ := by
    calc
      _ = ∫ x, Hset.indicator
            (fun y => g ((a : v.adicCompletion F) * y)) x ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
      _ = _ := MeasureTheory.integral_indicator hHsetMeas
  have hscale := LocHaar.integral_comp_mul μ a gset
  have hscaleEq :
      ∫ x in Hset, g ((a : v.adicCompletion F) * x) ∂μ.μ =
        (absFin v a)⁻¹ • ∫ x, gset x ∂μ.μ := by
    calc
      _ = ∫ x, gset ((a : v.adicCompletion F) * x) ∂μ.μ := htrans.symm
      _ = _ := hscale
  have ha0 : absFin v (a : v.adicCompletion F) ≠ 0 :=
    ne_of_gt (absFin_pos (Units.ne_zero a))
  have hsolve : ∫ x, gset x ∂μ.μ =
      absFin v a • ∫ x in Hset, g ((a : v.adicCompletion F) * x) ∂μ.μ := by
    calc
      _ = absFin v a • ((absFin v a)⁻¹ • ∫ x, gset x ∂μ.μ) := by
        rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
      _ = _ := by rw [← hscaleEq]
  rw [hJac, hsolve]
  rw [hHsetEq]
  simp [a, g, mul_assoc]

private theorem spherical_left_unipotent_scale (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (f0 : L.L → T.V) (hf0 : IsSection L T s f0)
    (a : (v.adicCompletion F)ˣ) (Hh : v.adicCompletion F) :
    f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * Hh)) * L.a a) =
      ((absFin v a⁻¹ : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa a⁻¹ (f0 (L.w * L.n (Multiplicative.ofAdd Hh))) := by
  have harg : (a : v.adicCompletion F) * Hh * (a⁻¹ : v.adicCompletion F) = Hh := by
    calc
      _ = ((a : v.adicCompletion F) * (a⁻¹ : v.adicCompletion F)) * Hh := by ring
      _ = Hh := by simp
  have hna : L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * Hh)) * L.a a =
      L.a a * L.n (Multiplicative.ofAdd Hh) := by
    simpa [harg] using L.lift_na ((a : v.adicCompletion F) * Hh) a
  have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
  have hwa0 := L.lift_wa a
  rw [hwInv] at hwa0
  have hwa : L.w * L.a a = L.a a⁻¹ * L.w := by
    calc
      L.w * L.a a = L.w * L.a a * (L.w * L.w) := by rw [L.w_sq]; simp
      _ = (L.w * L.a a * L.w) * L.w := by group
      _ = L.a a⁻¹ * L.w := by rw [hwa0]
  have hgroup : L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * Hh)) * L.a a =
      L.a a⁻¹ * L.w * L.n (Multiplicative.ofAdd Hh) := by
    calc
      _ = L.w * (L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * Hh)) * L.a a) := by group
      _ = L.w * (L.a a * L.n (Multiplicative.ofAdd Hh)) := by rw [hna]
      _ = (L.w * L.a a) * L.n (Multiplicative.ofAdd Hh) := by group
      _ = (L.a a⁻¹ * L.w) * L.n (Multiplicative.ofAdd Hh) := by rw [hwa]
      _ = L.a a⁻¹ * L.w * L.n (Multiplicative.ofAdd Hh) := by group
  have hcov := hf0.1 0 a⁻¹ (L.w * L.n (Multiplicative.ofAdd Hh))
  have hn0 : L.n (Multiplicative.ofAdd (0 : v.adicCompletion F)) = 1 := by simp
  rw [hn0, one_mul] at hcov
  calc
    f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * Hh)) * L.a a) =
        f0 (L.a a⁻¹ * L.w * L.n (Multiplicative.ofAdd Hh)) := congrArg f0 hgroup
    _ = _ := by simpa [mul_assoc] using hcov

private theorem tameBasis_unif_action (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (T : TorusRep D H v) (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (j : ℤ) (k : ZMod 3) :
    T.σa (unifLoc v ^ j) (B.e k) = B.e (k + (j : ZMod 3)) := by
  have h1loc : IsLocUnit v (1 : (v.adicCompletion F)ˣ) :=
    localIsLocUnit_of_valued_one (v := v) 1 (by simp)
  have hact := B.act j 1 h1loc k
  have hchi := (localChi_basic (D := D) (v := v) hv).1
  simpa [hchi] using hact

private theorem qv_cpow_int_mul (n : ℤ) (z : ℂ) :
    ((qv v : ℂ) ^ (n : ℂ)) ^ z = (qv v : ℂ) ^ ((n : ℂ) * z) := by
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hlog : Complex.log (qv v : ℂ) = (Real.log (qv v) : ℂ) :=
    (Complex.ofReal_log hqpos.le).symm
  let a : ℂ := (n : ℂ)
  have him : (Complex.log (qv v : ℂ) * a).im = 0 := by simp [a, hlog]
  have h1 : -Real.pi < (Complex.log (qv v : ℂ) * a).im := by
    rw [him]
    exact neg_lt_zero.mpr Real.pi_pos
  have h2 : (Complex.log (qv v : ℂ) * a).im ≤ Real.pi := by
    rw [him]
    exact le_of_lt Real.pi_pos
  change ((qv v : ℂ) ^ a) ^ z = (qv v : ℂ) ^ (a * z)
  exact (Complex.cpow_mul z h1 h2).symm

private theorem spherical_scaled_annulus_value (L : FinLocalCover D H v)
    (τ : TameSplitting L) (T : TorusRep D H v) (B : TameTorusBasis T)
    (A : AddCharData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ)
    (f0 : L.L → T.V) (hf0 : IsSection L T s f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (e l : ℕ) (hl : 0 < l) (u : (v.adicCompletion F)ˣ)
    (huval : Valued.v (u : v.adicCompletion F) = 1) :
    A.ψ v (-(((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      ((unifLoc v ^ (-(l : ℤ)) * u : (v.adicCompletion F)ˣ) : v.adicCompletion F))) •
      f0 (L.w * L.n (Multiplicative.ofAdd
        (((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          ((unifLoc v ^ (-(l : ℤ)) * u : (v.adicCompletion F)ˣ) : v.adicCompletion F))) *
          L.a (unifLoc v ^ (e : ℤ))) =
      ((qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
        (qv v : ℂ) ^ (-((l : ℂ) * (1 + 2 * s))) *
        localChi D v u ^ (-2 * (l : ℤ)) *
        A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) * (u : v.adicCompletion F)))) •
        B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (e : ℤ)
  let Hunit : (v.adicCompletion F)ˣ := unifLoc v ^ (-(l : ℤ)) * u
  let Hh : v.adicCompletion F := Hunit
  let b : ℂ := (1 : ℂ) / 2 + s
  have hparamU : a * Hunit = localShellScale (v := v) e l * u := by
    dsimp [a, Hunit, localShellScale]
    calc
      _ = (unifLoc v ^ (e : ℤ) * unifLoc v ^ (-(l : ℤ))) * u := by ac_rfl
      _ = unifLoc v ^ ((e : ℤ) + (-(l : ℤ))) * u := by rw [← zpow_add]
      _ = unifLoc v ^ ((e : ℤ) - (l : ℤ)) * u := by rw [sub_eq_add_neg]
  have hparam : (a : v.adicCompletion F) * Hh =
      (localShellScale (v := v) e l : v.adicCompletion F) * (u : v.adicCompletion F) :=
    congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hparamU
  have hscaled := spherical_left_unipotent_scale L T s f0 hf0 a Hh
  have hshell := localSpherical_shell_value L τ T B hv s f0 hf0 h1 hK l hl u huval
  have houterUnit : a⁻¹ = unifLoc v ^ (-(e : ℤ)) := by
    dsimp [a]
    group
  have houterBasis : T.σa a⁻¹ (B.e (2 * (l : ZMod 3))) =
      B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
    have hAct := tameBasis_unif_action D H v T B hv (-(e : ℤ)) (2 * (l : ZMod 3))
    simpa [a, sub_eq_add_neg] using hAct
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hOuterAbs : absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ (e : ℤ) := by
    rw [houterUnit, absFin_zpow, absFin_unifLoc, inv_zpow']
    simp
  have hOuterReal : absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ ((e : ℤ) : ℝ) := by
    rw [hOuterAbs]
    exact (Real.rpow_intCast (qv v) (e : ℤ)).symm
  have hOuterComplex : (absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℂ) =
      (qv v : ℂ) ^ (e : ℂ) := by
    rw [hOuterReal, Complex.ofReal_cpow hqpos.le]
    congr 1 <;> norm_cast
  have hOuterPow :
      ((absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ) : ℂ) ^ b =
        (qv v : ℂ) ^ ((e : ℂ) * b) := by
    rw [hOuterComplex]
    exact qv_cpow_int_mul (v := v) (e : ℤ) b
  have hOuterPow' :
      ((absFin v (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F)⁻¹) : ℝ) : ℂ) ^ b =
        (qv v : ℂ) ^ ((e : ℂ) * b) := by
    simpa using hOuterPow
  have hphase : A.ψ v (-((a : v.adicCompletion F) * Hh)) =
      A.ψ v (-((localShellScale (v := v) e l : v.adicCompletion F) *
        (u : v.adicCompletion F))) := by rw [hparam]
  calc
    _ = A.ψ v (-((a : v.adicCompletion F) * Hh)) •
          (((absFin v (a⁻¹ : v.adicCompletion F) : ℝ) : ℂ) ^ b) •
            T.σa a⁻¹ (f0 (L.w * L.n (Multiplicative.ofAdd Hh))) := by rw [hscaled]
    _ = A.ψ v (-((localShellScale (v := v) e l : v.adicCompletion F) *
          (u : v.adicCompletion F))) •
          (((absFin v (a⁻¹ : v.adicCompletion F) : ℝ) : ℂ) ^ b) •
            T.σa a⁻¹
              ((((qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s))) *
                (localChi D v u ^ (-2 * (l : ℤ)))) • B.e (2 * (l : ZMod 3))) := by
        rw [hphase, hshell]
    _ = _ := by
      rw [map_smul, houterBasis]
      simp only [smul_smul]
      rw [hOuterPow']
      congr 1
      rw [show (qv v : ℂ) ^ ((e : ℂ) * b) =
          (qv v : ℂ) ^ ((e : ℂ) * (1 / 2) + (e : ℂ) * s) by
            congr 1
            dsimp [b]
            ring]
      ring

private noncomputable def sphericalScaledIntegrand (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (e : ℕ) (f0 : L.L → T.V) :
    v.adicCompletion F → T.V := fun x =>
  A.ψ v (-(((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)) •
    f0 (L.w * L.n (Multiplicative.ofAdd
      (((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)) *
        L.a (unifLoc v ^ (e : ℤ)))

private theorem sphericalScaledIntegrand_locallyConstant (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (s : ℂ) (e : ℕ) (f0 : L.L → T.V)
    (hf0 : IsSection L T s f0) :
    IsLocallyConstant (sphericalScaledIntegrand L T A e f0) := by
  apply (IsLocallyConstant.iff_eventually_eq (sphericalScaledIntegrand L T A e f0)).2
  intro x
  obtain ⟨m, hm0, hKc⟩ := hf0.2.2
  let n : ℕ := max m (max L.m0 1)
  have hmle : m ≤ n := Nat.le_max_left _ _
  have hm0n : L.m0 ≤ n := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have h1n : 1 ≤ n := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  let U : Set (v.adicCompletion F) :=
    {y | y - x ∈ ball v (n : ℤ)}
  have hballopen : IsOpen (ball v (n : ℤ)) := by
    change IsOpen {z : v.adicCompletion F | Valued.v z ≤ WithZero.exp (-(n : ℤ))}
    exact v.isOpen_setOf_valued_le (K := F) (by simp)
  have hUopen : IsOpen U := by
    change IsOpen ((fun y : v.adicCompletion F => y - x) ⁻¹' ball v (n : ℤ))
    exact hballopen.preimage (continuous_id.sub continuous_const)
  have hxU : x ∈ U := by
    change x - x ∈ ball v (n : ℤ)
    simp [ball]
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  let δ : v.adicCompletion F := y - x
  have hδball : δ ∈ ball v (n : ℤ) := by simpa [δ, U] using hy
  have hyEq : y = x + δ := by dsimp [δ]; abel
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (e : ℤ)
  have haVal : Valued.v (a : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    simpa [a] using unifLoc_zpow_valuation (v := v) (e : ℤ)
  have hδVal : Valued.v δ ≤ WithZero.exp (-(n : ℤ)) := by
    simpa [ball] using hδball
  have haδO : (a : v.adicCompletion F) * δ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, haVal]
    calc
      WithZero.exp (-(e : ℤ)) * Valued.v δ ≤
          WithZero.exp (-(e : ℤ)) * WithZero.exp (-(n : ℤ)) := by gcongr
      _ = WithZero.exp (-(e : ℤ) - (n : ℤ)) := by
        rw [← WithZero.exp_add]
        congr 1
      _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).mpr (by omega)
  have hψδ : A.ψ v (-((a : v.adicCompletion F) * δ)) = 1 := by
    exact A.integral v _ ((v.adicCompletionIntegers F).neg_mem _ haδO)
  have hphaseArg : -((a : v.adicCompletion F) * (x + δ)) =
      -((a : v.adicCompletion F) * x) + -((a : v.adicCompletion F) * δ) := by ring
  have hphase : A.ψ v (-((a : v.adicCompletion F) * (x + δ))) =
      A.ψ v (-((a : v.adicCompletion F) * x)) := by
    rw [hphaseArg, (A.ψ v).map_add_eq_mul, hψδ, mul_one]
  have hnadd (x₁ x₂ : v.adicCompletion F) :
      L.n (Multiplicative.ofAdd (x₁ + x₂)) =
        L.n (Multiplicative.ofAdd x₁) * L.n (Multiplicative.ofAdd x₂) := by
    simpa using map_mul L.n (Multiplicative.ofAdd x₁) (Multiplicative.ofAdd x₂)
  have hcancel :
      (a : v.adicCompletion F) * δ * ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = δ := by
    calc
      _ = δ * ((a : v.adicCompletion F) * ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by ring
      _ = δ := by simp
  have hcomm : L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * δ)) * L.a a =
      L.a a * L.n (Multiplicative.ofAdd δ) := by
    calc
      _ = L.a a * L.n (Multiplicative.ofAdd
          ((a : v.adicCompletion F) * δ *
            ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))) :=
        L.lift_na ((a : v.adicCompletion F) * δ) a
      _ = _ := by rw [hcancel]
  have hgroup :
      L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * (x + δ))) * L.a a =
        (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a) *
          L.n (Multiplicative.ofAdd δ) := by
    calc
      _ = L.w * (L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) *
            L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * δ))) * L.a a := by
          rw [show (a : v.adicCompletion F) * (x + δ) =
            (a : v.adicCompletion F) * x + (a : v.adicCompletion F) * δ by ring,
            hnadd ((a : v.adicCompletion F) * x) ((a : v.adicCompletion F) * δ)]
      _ = L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) *
            (L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * δ)) * L.a a) := by group
      _ = L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) *
            (L.a a * L.n (Multiplicative.ofAdd δ)) := by rw [hcomm]
      _ = _ := by group
  have hk : L.n (Multiplicative.ofAdd δ) ∈ L.Kc m := by
    apply (L.Kc_anti m n hm0 hmle)
    exact L.n_Kc n hm0n δ hδball
  have hvector :
      f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * (x + δ))) * L.a a) =
        f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a) := by
    rw [hgroup]
    exact hKc _ _ hk
  change A.ψ v (-((a : v.adicCompletion F) * y)) •
      f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * y)) * L.a a) =
    A.ψ v (-((a : v.adicCompletion F) * x)) •
      f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a)
  rw [hyEq, hphase, hvector]

private theorem sphericalScaledIntegrand_on_integers (L : FinLocalCover D H v)
    (τ : TameSplitting L) (T : TorusRep D H v) (B : TameTorusBasis T)
    (A : AddCharData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ)
    (f0 : L.L → T.V) (hf0 : IsSection L T s f0)
    (h1 : f0 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (e : ℕ) (x : v.adicCompletion F) (hxO : x ∈ v.adicCompletionIntegers F) :
    sphericalScaledIntegrand L T A e f0 x =
      (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) •
        B.e (-(e : ZMod 3)) := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (e : ℤ)
  let b : ℂ := (1 : ℂ) / 2 + s
  have haVal : Valued.v (a : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    simpa [a] using unifLoc_zpow_valuation (v := v) (e : ℤ)
  have haO : (a : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, haVal, ← WithZero.exp_zero]
    exact (WithZero.exp_le_exp).mpr (by omega)
  have haxO : (a : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).mul_mem _ _ haO hxO
  have hψ : A.ψ v (-((a : v.adicCompletion F) * x)) = 1 := by
    exact A.integral v _ ((v.adicCompletionIntegers F).neg_mem _ haxO)
  have hcancel : (a : v.adicCompletion F) * x *
      ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = x := by
    calc
      _ = x * ((a : v.adicCompletion F) *
          ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by ring
      _ = x := by simp
  have hna : L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a =
      L.a a * L.n (Multiplicative.ofAdd x) := by
    calc
      _ = L.a a * L.n (Multiplicative.ofAdd
          ((a : v.adicCompletion F) * x *
            ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))) :=
        L.lift_na ((a : v.adicCompletion F) * x) a
      _ = _ := by rw [hcancel]
  have hvec : f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a) =
      f0 (L.w * L.a a) := by
    rw [show L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a =
      (L.w * L.a a) * L.n (Multiplicative.ofAdd x) by rw [mul_assoc, hna]; group]
    exact hK (L.w * L.a a) (L.n (Multiplicative.ofAdd x)) (τ.n_mem x hxO)
  have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
  have hwa0 := L.lift_wa a
  rw [hwInv] at hwa0
  have hwa : L.w * L.a a = L.a a⁻¹ * L.w := by
    calc
      L.w * L.a a = L.w * L.a a * (L.w * L.w) := by rw [L.w_sq]; simp
      _ = (L.w * L.a a * L.w) * L.w := by group
      _ = L.a a⁻¹ * L.w := by rw [hwa0]
  have hw1 : f0 L.w = B.e 0 := by
    calc
      f0 L.w = f0 (1 * L.w) := by simp
      _ = f0 1 := hK 1 L.w τ.w_mem
      _ = B.e 0 := h1
  have hcov := hf0.1 0 a⁻¹ L.w
  have hn0 : L.n (Multiplicative.ofAdd (0 : v.adicCompletion F)) = 1 := by simp
  rw [hn0, one_mul] at hcov
  have hvalue : f0 (L.w * L.n (Multiplicative.ofAdd ((a : v.adicCompletion F) * x)) * L.a a) =
      (((absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ) : ℂ) ^ b) •
        T.σa a⁻¹ (B.e 0) := by
    calc
      _ = f0 (L.w * L.a a) := hvec
      _ = f0 (L.a a⁻¹ * L.w) := congrArg f0 hwa
      _ = (((absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ) : ℂ) ^ b) •
            T.σa a⁻¹ (f0 L.w) := hcov
      _ = _ := by rw [hw1]
  have houterUnit : a⁻¹ = unifLoc v ^ (-(e : ℤ)) := by dsimp [a]; group
  have hOuterAbs : absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ (e : ℤ) := by
    rw [houterUnit, absFin_zpow, absFin_unifLoc, inv_zpow']
    simp
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hOuterReal : absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ ((e : ℤ) : ℝ) := by
    rw [hOuterAbs]
    exact (Real.rpow_intCast (qv v) (e : ℤ)).symm
  have hOuterComplex :
      (absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℂ) =
        (qv v : ℂ) ^ (e : ℂ) := by
    rw [hOuterReal, Complex.ofReal_cpow hqpos.le]
    congr 1 <;> norm_cast
  have hOuterPow :
      ((absFin v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ) : ℂ) ^ b =
        (qv v : ℂ) ^ ((e : ℂ) * b) := by
    rw [hOuterComplex]
    exact qv_cpow_int_mul (v := v) (e : ℤ) b
  have hAct : T.σa a⁻¹ (B.e 0) = B.e (-(e : ZMod 3)) := by
    have h := tameBasis_unif_action D H v T B hv (-(e : ℤ)) (0 : ZMod 3)
    simpa [a] using h
  rw [sphericalScaledIntegrand, hψ, hvalue, hAct, hOuterPow]
  simp only [one_smul]
  rw [show (e : ℂ) * b = (e : ℂ) * ((1 : ℂ) / 2 + s) by dsimp [b]]

private theorem sphericalScaledIntegrand_annulus_integral
    (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (μ : LocHaar v) (s : ℂ) (f0 : L.L → T.V) (hf0 : IsSection L T s f0)
    (h1 : f0 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (e l : ℕ) (hl : 0 < l) :
    ∫ x in localShellAnnulus (v := v) l, sphericalScaledIntegrand L T A e f0 x ∂μ.μ =
      (((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) : ℝ) : ℂ) *
        (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
        (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) *
        (∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ)) •
          B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (e : ℤ)
  let y : (v.adicCompletion F)ˣ := unifLoc v ^ (-(l : ℤ))
  let C : ℂ := (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
    (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s))
  let f : v.adicCompletion F → T.V := sphericalScaledIntegrand L T A e f0
  have hUnit :
      ∫ x in localUnitShell v, f ((y : v.adicCompletion F) * x) ∂μ.μ =
        (C * ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ) •
          B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
    have hmeas : MeasurableSet (localUnitShell v) :=
      (localUnitShell_compact (v := v)).measurableSet
    have hpoint (x : v.adicCompletion F) (hx : x ∈ localUnitShell v) :
        f ((y : v.adicCompletion F) * x) =
          (C * localShellScalar D A e l x) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
      let xU : localUnitShell v := ⟨x, hx⟩
      let u : (v.adicCompletion F)ˣ := localUnitShell.unit xU
      have huval : Valued.v (u : v.adicCompletion F) = 1 := xU.property
      have hunitval : (u : v.adicCompletion F) = x := rfl
      have hpt := spherical_scaled_annulus_value L τ T B A hv s f0 hf0 h1 hK e l hl u huval
      have hscalar : localShellScalar D A e l x =
          localChi D v u ^ (-2 * (l : ℤ)) *
            A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) * x)) := by
        simp [localShellScalar, localChiPowerField, localUnitShell.charPower,
          localUnitShell.unit, u, xU, hunitval, localUnitShell_ne_zero xU, hx]
      have hpt1 : f ((y : v.adicCompletion F) * x) =
          ((qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
            (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) *
            localChi D v u ^ (-2 * (l : ℤ)) *
            A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) * x))) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
        simpa [f, sphericalScaledIntegrand, a, y, hunitval, localShellScale] using hpt
      have hcoeff :
          ((qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
            (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) *
            localChi D v u ^ (-2 * (l : ℤ)) *
            A.ψ v (-(((localShellScale (v := v) e l : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) * x))) = C * localShellScalar D A e l x := by
        rw [hscalar]
        dsimp [C]
        ring
      exact hpt1.trans (congrArg (fun c : ℂ => c •
        B.e (2 * (l : ZMod 3) - (e : ZMod 3))) hcoeff)
    calc
      _ = ∫ x in localUnitShell v,
          (C * localShellScalar D A e l x) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3)) ∂μ.μ := by
          apply MeasureTheory.setIntegral_congr_fun hmeas
          intro x hx
          exact hpoint x hx
      _ = (∫ x in localUnitShell v,
            C * localShellScalar D A e l x ∂μ.μ) •
              B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
          rw [integral_smul_const]
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hchange := integral_localShellAnnulus (E := T.V) μ l f
  calc
    _ = absFin v (y : v.adicCompletion F) •
          ∫ x in localUnitShell v, f ((y : v.adicCompletion F) * x) ∂μ.μ := by
            simpa only [f, y, Units.val_zpow_eq_zpow_val] using hchange
    _ = absFin v (y : v.adicCompletion F) •
          ((C * ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3))) := by rw [hUnit]
    _ = (((absFin v (y : v.adicCompletion F) : ℝ) : ℂ) *
          (C * ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ)) •
          B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rfl
    _ = _ := by
      apply congrArg (fun c : ℂ => c • B.e (2 * (l : ZMod 3) - (e : ZMod 3)))
      dsimp [C, y]
      ring

private theorem sphericalAnnulusAbs_complex (l : ℕ) :
    ((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) : ℝ) : ℂ) = (qv v : ℂ) ^ (l : ℂ) := by
  have hAbsInt :
      absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (qv v) ^ (l : ℤ) := by
    rw [absFin_zpow, absFin_unifLoc, inv_zpow']
    simp
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hAbsReal :
      absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (qv v) ^ ((l : ℤ) : ℝ) := by
    rw [hAbsInt]
    exact (Real.rpow_intCast (qv v) (l : ℤ)).symm
  rw [hAbsReal, Complex.ofReal_cpow hqpos.le]
  congr 1 <;> norm_cast

private theorem sphericalScaledAnnulus_factor (e l : ℕ) (s : ℂ) :
    ((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) : ℝ) : ℂ) *
        (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
        (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) =
      (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
        (qv v : ℂ) ^ (-2 * (l : ℂ) * s) := by
  rw [sphericalAnnulusAbs_complex (v := v) l]
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  calc
    _ = (qv v : ℂ) ^ ((l : ℂ) + (e : ℂ) * ((1 : ℂ) / 2 + s) +
          (-(l : ℂ) * (1 + 2 * s))) := by
      calc
        _ = ((qv v : ℂ) ^ (l : ℂ) *
              (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s))) *
              (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) := by ring
        _ = (qv v : ℂ) ^ ((l : ℂ) + (e : ℂ) * ((1 : ℂ) / 2 + s)) *
              (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) := by
                rw [← Complex.cpow_add _ _ hqne]
        _ = _ := by rw [← Complex.cpow_add _ _ hqne]
    _ = (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
          (qv v : ℂ) ^ (-2 * (l : ℂ) * s) := by
      rw [show (l : ℂ) + (e : ℂ) * ((1 : ℂ) / 2 + s) +
        (-(l : ℂ) * (1 + 2 * s)) =
          ((e : ℂ) * ((1 : ℂ) / 2 + s)) + (-2 * (l : ℂ) * s) by ring,
        Complex.cpow_add _ _ hqne]

private theorem sphericalOuterAbs_complex (e : ℕ) :
    ((absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) : ℝ) : ℂ) = (qv v : ℂ) ^ (-(e : ℂ)) := by
  have hAbsInt :
      absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (qv v) ^ (-(e : ℤ)) := by
    rw [absFin_zpow, absFin_unifLoc]
    simp
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hAbsReal :
      absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (qv v) ^ ((-(e : ℤ)) : ℝ) := by
    rw [hAbsInt]
    simpa using (Real.rpow_intCast (qv v) (-(e : ℤ))).symm
  rw [hAbsReal, Complex.ofReal_cpow hqpos.le]
  congr 1 <;> norm_cast

private theorem sphericalOuter_factor (e : ℕ) (s : ℂ) :
    ((absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) : ℝ) : ℂ) *
        (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) =
      (qv v : ℂ) ^ (-(e : ℂ) * ((1 : ℂ) / 2 - s)) := by
  rw [sphericalOuterAbs_complex (v := v) e]
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  calc
    _ = (qv v : ℂ) ^ (-(e : ℂ) + (e : ℂ) * ((1 : ℂ) / 2 + s)) := by
      rw [← Complex.cpow_add _ _ hqne]
    _ = _ := by
      congr 1
      ring

/-- **jq:shell** (10:331–436, general `s`): the spherical Jacquet integral
`J_e = 𝒥(π(a(ϖ^e)) f°_s)`, `e ≥ 0`, in the basis `e_k`. -/
theorem jacquet_spherical (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (s : ℂ) (f0 : L.L → T.V)
    (hf0 : IsSection L T s f0) (h1 : f0 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (e : ℕ) :
    jacquet L A μ (rtr (L.a (unifLoc v ^ (e : ℤ))) f0) =
      (qv v : ℂ) ^ (-(e : ℂ) * (1 / 2 - s)) •
        (((1 : ℂ) + (1 - (qv v : ℂ)⁻¹) *
            ∑ j ∈ Finset.Icc 1 (e / 3), (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) • B.e (-(e : ZMod 3)) +
          ((qv v : ℂ) ^ (-2 * ((e : ℂ) + 1) * s) * shellTerm D A v (e + 1)) •
            B.e ((e : ZMod 3) + 2)) := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 F ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  let b : ℂ := (1 : ℂ) / 2 + s
  let f : v.adicCompletion F → T.V := sphericalScaledIntegrand L T A e f0
  obtain ⟨N0, hstable⟩ := jacquet_stable L T A μ s
    (rtr (L.a (unifLoc v ^ (e : ℤ))) f0) (IsSection.rtr hf0 _)
  let N : ℕ := max N0 1
  have hN0 : N0 ≤ N := Nat.le_max_left _ _
  have hN1 : 1 ≤ N := Nat.le_max_right _ _
  let R : ℕ := e + N
  have hRlow : e + 1 ≤ R := by dsimp [R]; omega
  have hstableN := hstable N hN0
  have hscaled :
      jacquet L A μ (rtr (L.a (unifLoc v ^ (e : ℤ))) f0) =
        absFin v (unifLoc v ^ (e : ℤ)) •
          ∫ x in ball v (-(R : ℤ)), f x ∂μ.μ := by
    calc
      _ = jacquetTrunc L A μ N (rtr (L.a (unifLoc v ^ (e : ℤ))) f0) := hstableN.symm
      _ = _ := by
        simpa [R, f, sphericalScaledIntegrand] using
          (jacquetTrunc_scale L A μ e N f0)
  have hLC : IsLocallyConstant f := by
    simpa [f] using sphericalScaledIntegrand_locallyConstant L T A s e f0 hf0
  have hfcont : Continuous f := hLC.continuous
  have hOmeas : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (localInteger_compact v).measurableSet
  have hIntO : IntegrableOn f (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ.μ :=
    hfcont.continuousOn.integrableOn_compact (localInteger_compact v)
  have hIntAnn (l : ℕ) :
      IntegrableOn f (localShellAnnulus (v := v) l) μ.μ :=
    hfcont.continuousOn.integrableOn_compact (localShellAnnulus_isCompact (v := v) l)
  let U : Set (v.adicCompletion F) :=
    ⋃ l : Finset.Icc 1 R, localShellAnnulus (v := v) l.1
  have hUmeas : MeasurableSet U := by
    apply MeasurableSet.iUnion
    intro l
    exact (localShellAnnulus_isCompact (v := v) l.1).measurableSet
  have hIntU : IntegrableOn f U μ.μ := by
    rw [show U = ⋃ l : Finset.Icc 1 R, localShellAnnulus (v := v) l.1 by rfl]
    rw [MeasureTheory.integrableOn_finite_iUnion]
    intro l
    exact hIntAnn l.1
  have hdisj : Disjoint (v.adicCompletionIntegers F : Set (v.adicCompletion F)) U := by
    apply Set.disjoint_left.mpr
    intro x hxO hxU
    rcases Set.mem_iUnion.mp hxU with ⟨l, hxl⟩
    have hval := (localShellAnnulus_valuation (v := v) l.1 x).mp hxl
    have hOVal : Valued.v x ≤ 1 := by
      rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hxO
    have hl : (0 : ℤ) < (l.1 : ℤ) := by
      exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Icc.mp l.property).1)
    have hgt : 1 < WithZero.exp (l.1 : ℤ) := by
      rw [← WithZero.exp_zero]
      exact (WithZero.exp_lt_exp).mpr hl
    rw [hval] at hOVal
    exact (not_lt_of_ge hOVal) hgt
  have hsumU :
      ∫ x in U, f x ∂μ.μ =
        ∑ l : Finset.Icc 1 R,
          ∫ x in localShellAnnulus (v := v) l.1, f x ∂μ.μ := by
    simpa [U] using
      (MeasureTheory.integral_iUnion_fintype
        (s := fun l : Finset.Icc 1 R => localShellAnnulus (v := v) l.1)
        (f := f) (μ := μ.μ)
        (fun l => (localShellAnnulus_isCompact (v := v) l.1).measurableSet)
        (localShellAnnulus_pairwise_disjoint (v := v) R)
        (fun l => hIntAnn l.1))
  have hBallInt :
      ∫ x in ball v (-(R : ℤ)), f x ∂μ.μ =
        ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), f x ∂μ.μ +
          ∑ l : Finset.Icc 1 R,
            ∫ x in localShellAnnulus (v := v) l.1, f x ∂μ.μ := by
    rw [← localShellAnnulus_partition (v := v) R]
    rw [MeasureTheory.setIntegral_union hdisj hUmeas hIntO hIntU, hsumU]
  have hOvalue :
      ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), f x ∂μ.μ =
        (qv v : ℂ) ^ ((e : ℂ) * b) • B.e (-(e : ZMod 3)) := by
    calc
      _ = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
            ((qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) •
              B.e (-(e : ZMod 3))) ∂μ.μ := by
        apply MeasureTheory.setIntegral_congr_fun hOmeas
        intro x hx
        simpa [f, b] using
          (sphericalScaledIntegrand_on_integers L τ T B A hv s f0 hf0 h1 hK e x hx)
      _ = _ := by simp [b, MeasureTheory.measureReal_def, μ.norm_O]
  let I : ℕ → ℂ := fun l =>
    ∫ x in localUnitShell v, localShellScalar D A e l x ∂μ.μ
  have hIcases (l : ℕ) : I l =
      if l ≤ e then (if 3 ∣ l then ((1 - (qv v)⁻¹ : ℝ) : ℂ) else 0)
      else if l = e + 1 then shellTerm D A v l else 0 := by
    simpa [I] using localShellScalar_integral_cases D A μ hv hd e l
  have hAnnNorm (l : ℕ) (hl : 0 < l) :
      ∫ x in localShellAnnulus (v := v) l, f x ∂μ.μ =
        ((qv v : ℂ) ^ ((e : ℂ) * b) *
          (qv v : ℂ) ^ (-2 * (l : ℂ) * s) * I l) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
    have hraw := sphericalScaledIntegrand_annulus_integral
      L τ T B A hv μ s f0 hf0 h1 hK e l hl
    have hfac := sphericalScaledAnnulus_factor (v := v) e l s
    have hcoeff :
        ((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) : ℝ) : ℂ) *
            (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
            (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) * I l =
          (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
            (qv v : ℂ) ^ (-2 * (l : ℂ) * s) * I l := by
      calc
        _ = (((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) : ℝ) : ℂ) *
              (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
              (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s))) * I l := by ring
        _ = ((qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
              (qv v : ℂ) ^ (-2 * (l : ℂ) * s)) * I l := by rw [hfac]
        _ = _ := by ring
    calc
      _ = (((absFin v ((unifLoc v ^ (-(l : ℤ)) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) : ℝ) : ℂ) *
          (qv v : ℂ) ^ ((e : ℂ) * ((1 : ℂ) / 2 + s)) *
          (qv v : ℂ) ^ (-(l : ℂ) * (1 + 2 * s)) * I l) •
            B.e (2 * (l : ZMod 3) - (e : ZMod 3)) := by
        simpa [f, I] using hraw
      _ = _ := by
        exact congrArg (fun c : ℂ => c •
          B.e (2 * (l : ZMod 3) - (e : ZMod 3))) hcoeff
  have hBallTerms :
      ∫ x in ball v (-(R : ℤ)), f x ∂μ.μ =
        (qv v : ℂ) ^ ((e : ℂ) * b) • B.e (-(e : ZMod 3)) +
          ∑ l : Finset.Icc 1 R,
            ((qv v : ℂ) ^ ((e : ℂ) * b) *
              (qv v : ℂ) ^ (-2 * (l.1 : ℂ) * s) * I l.1) •
                B.e (2 * (l.1 : ZMod 3) - (e : ZMod 3)) := by
    calc
      _ = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), f x ∂μ.μ +
            ∑ l : Finset.Icc 1 R,
              ∫ x in localShellAnnulus (v := v) l.1, f x ∂μ.μ := hBallInt
      _ = _ := by
        rw [hOvalue]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        exact hAnnNorm l.1 (Finset.mem_Icc.mp l.property).1
  let Term : ℕ → T.V := fun l =>
    ((qv v : ℂ) ^ (-2 * (l : ℂ) * s) * I l) •
      B.e (2 * (l : ZMod 3) - (e : ZMod 3))
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hRatio : ((1 - (qv v)⁻¹ : ℝ) : ℂ) = 1 - (qv v : ℂ)⁻¹ := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  have hTermLow (l : ℕ) (hl : l ∈ Finset.Icc 1 e) :
      Term l = if 3 ∣ l then
        ((qv v : ℂ) ^ (-2 * (l : ℂ) * s) * (1 - (qv v : ℂ)⁻¹)) •
          B.e (-(e : ZMod 3)) else 0 := by
    have hle : l ≤ e := (Finset.mem_Icc.mp hl).2
    by_cases hdiv : 3 ∣ l
    · have hlmod : (l : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff l 3).2 hdiv
      have hidx : 2 * (l : ZMod 3) - (e : ZMod 3) = -(e : ZMod 3) := by
        rw [hlmod]
        simp
      simp [Term, hIcases l, hle, hdiv, hRatio, hidx]
    · simp [Term, hIcases l, hle, hdiv]
  have hTermZero (l : ℕ) (hl : e + 1 < l) : Term l = 0 := by
    have hle : ¬l ≤ e := by omega
    have hneq : l ≠ e + 1 := by omega
    simp [Term, hIcases l, hle, hneq]
  have hTermTerminal :
      Term (e + 1) =
        ((qv v : ℂ) ^ (-2 * ((e : ℂ) + 1) * s) * shellTerm D A v (e + 1)) •
          B.e ((e : ZMod 3) + 2) := by
    have hle : ¬e + 1 ≤ e := by omega
    have hidx : 2 * ((e + 1 : ℕ) : ZMod 3) - (e : ZMod 3) =
        (e : ZMod 3) + 2 := by push_cast; ring
    have hExp : -2 * ((e + 1 : ℕ) : ℂ) * s =
        -2 * ((e : ℂ) + 1) * s := by push_cast; ring
    dsimp [Term]
    rw [hIcases (e + 1), if_neg hle, if_pos rfl, hidx]
    rw [hExp]
  have hsmallSub : Finset.Icc 1 (e + 1) ⊆ Finset.Icc 1 R := by
    intro l hl
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1,
      le_trans (Finset.mem_Icc.mp hl).2 hRlow⟩
  have hcut :
      (∑ l ∈ Finset.Icc 1 R, Term l) =
        ∑ l ∈ Finset.Icc 1 (e + 1), Term l := by
    apply (Finset.sum_subset hsmallSub ?_).symm
    intro l hlR hnot
    have hnle : ¬l ≤ e + 1 := by
      intro h
      exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hlR).1, h⟩)
    exact hTermZero l (by omega)
  have htop :
      (∑ l ∈ Finset.Icc 1 (e + 1), Term l) =
        (∑ l ∈ Finset.Icc 1 e, Term l) + Term (e + 1) := by
    rw [Finset.sum_Icc_succ_top]
    omega
  let c : ℂ := 1 - (qv v : ℂ)⁻¹
  let J : Finset ℕ := Finset.Icc 1 (e / 3)
  let LowSet : Finset ℕ := (Finset.Icc 1 e).filter (fun l => 3 ∣ l)
  let lowVec : ℕ → T.V := fun l =>
    ((qv v : ℂ) ^ (-2 * (l : ℂ) * s) * c) • B.e (-(e : ZMod 3))
  let lowJ : ℕ → T.V := fun j =>
    ((qv v : ℂ) ^ (-6 * (j : ℂ) * s) * c) • B.e (-(e : ZMod 3))
  have hLowToFilter :
      (∑ l ∈ Finset.Icc 1 e, Term l) = ∑ l ∈ LowSet, lowVec l := by
    calc
      _ = ∑ l ∈ Finset.Icc 1 e, if 3 ∣ l then lowVec l else 0 := by
        apply Finset.sum_congr rfl
        intro l hl
        simpa [lowVec, c] using hTermLow l hl
      _ = _ := by
        symm
        dsimp [LowSet]
        rw [Finset.sum_filter]
  have hReindex :
      (∑ j ∈ J, lowJ j) = ∑ l ∈ LowSet, lowVec l := by
    apply Finset.sum_bij (fun j _ => 3 * j)
    · intro j hj
      have hjIcc := Finset.mem_Icc.mp hj
      have hbound : 3 * j ≤ e := by
        have hdiv := Nat.mul_div_le e 3
        omega
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, hbound⟩
      · exact ⟨j, rfl⟩
    · intro j hj j' hj' heq
      omega
    · intro l hl
      rcases Finset.mem_filter.mp hl with ⟨hlIcc, hdiv⟩
      rcases hdiv with ⟨j, hj⟩
      have hlower : 1 ≤ l := (Finset.mem_Icc.mp hlIcc).1
      have hupper : l ≤ e := (Finset.mem_Icc.mp hlIcc).2
      have hjlower : 1 ≤ j := by omega
      have hjupper : j ≤ e / 3 := by omega
      refine ⟨j, Finset.mem_Icc.mpr ⟨hjlower, hjupper⟩, ?_⟩
      exact hj.symm
    · intro j hj
      dsimp [lowJ, lowVec]
      have hExp : -6 * (j : ℂ) * s =
          -2 * ((3 * j : ℕ) : ℂ) * s := by push_cast; ring
      rw [hExp]
  have hSumScalars :
      (∑ j ∈ J, lowJ j) =
        (c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
          B.e (-(e : ZMod 3)) := by
    dsimp [lowJ]
    calc
      _ = ∑ j ∈ J,
            c • ((qv v : ℂ) ^ (-6 * (j : ℂ) * s) • B.e (-(e : ZMod 3))) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [smul_smul]
          congr 1
          ring
      _ = c • ∑ j ∈ J,
            (qv v : ℂ) ^ (-6 * (j : ℂ) * s) • B.e (-(e : ZMod 3)) := by
          rw [Finset.smul_sum]
      _ = c • ((∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
            B.e (-(e : ZMod 3))) := by
          rw [← Finset.sum_smul]
      _ = _ := by rw [smul_smul]
  have hLowFactor :
      (∑ l ∈ Finset.Icc 1 e, Term l) =
        (c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
          B.e (-(e : ZMod 3)) := by
    calc
      _ = ∑ l ∈ LowSet, lowVec l := hLowToFilter
      _ = ∑ j ∈ J, lowJ j := hReindex.symm
      _ = _ := hSumScalars
  have hFirst :
      B.e (-(e : ZMod 3)) +
          (c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
            B.e (-(e : ZMod 3)) =
        (1 + c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
          B.e (-(e : ZMod 3)) := by
    calc
      _ = (1 : ℂ) • B.e (-(e : ZMod 3)) +
            (c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
              B.e (-(e : ZMod 3)) := by simp
      _ = _ := by rw [← add_smul]
  have hInnerSum :
      B.e (-(e : ZMod 3)) + ∑ l ∈ Finset.Icc 1 R, Term l =
        (1 + c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
            B.e (-(e : ZMod 3)) +
          ((qv v : ℂ) ^ (-2 * ((e : ℂ) + 1) * s) * shellTerm D A v (e + 1)) •
            B.e ((e : ZMod 3) + 2) := by
    calc
      _ = B.e (-(e : ZMod 3)) +
            ((∑ l ∈ Finset.Icc 1 e, Term l) + Term (e + 1)) := by
              rw [hcut, htop]
      _ = _ := by
        rw [hLowFactor, hTermTerminal]
        calc
          _ = (B.e (-(e : ZMod 3)) +
                (c * ∑ j ∈ J, (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
                  B.e (-(e : ZMod 3))) +
                ((qv v : ℂ) ^ (-2 * ((e : ℂ) + 1) * s) * shellTerm D A v (e + 1)) •
                  B.e ((e : ZMod 3) + 2) := by abel
          _ = _ := by rw [hFirst]
  let qBase : ℂ := (qv v : ℂ) ^ ((e : ℂ) * b)
  have hpull :
      qBase • B.e (-(e : ZMod 3)) +
          ∑ l : Finset.Icc 1 R,
            (qBase * (qv v : ℂ) ^ (-2 * (l.1 : ℂ) * s) * I l.1) •
              B.e (2 * (l.1 : ZMod 3) - (e : ZMod 3)) =
        qBase • (B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1) := by
    rw [smul_add, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [Term]
    rw [smul_smul]
    congr 1
    ring
  have hOuterAbsVal :
      ((absFin v ((unifLoc v : v.adicCompletion F) ^ (e : ℤ)) : ℝ) : ℂ) =
        (qv v : ℂ) ^ (-(e : ℂ)) := by
    rw [← Units.val_zpow_eq_zpow_val]
    exact sphericalOuterAbs_complex (v := v) e
  have hOuterAbsEq :
      absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        absFin v ((unifLoc v : v.adicCompletion F) ^ (e : ℤ)) := by
    exact congrArg (absFin v) (Units.val_zpow_eq_zpow_val (unifLoc v) (e : ℤ))
  have hOuterFactorVal :
      ((absFin v ((unifLoc v : v.adicCompletion F) ^ (e : ℤ)) : ℝ) : ℂ) * qBase =
        (qv v : ℂ) ^ (-(e : ℂ) * ((1 : ℂ) / 2 - s)) := by
    rw [hOuterAbsVal]
    have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
    dsimp [qBase]
    rw [← Complex.cpow_add _ _ hqne]
    congr 1
    dsimp [b]
    ring
  have hOuterFactorUnit :
      ((absFin v ((unifLoc v ^ (e : ℤ) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) : ℝ) : ℂ) * qBase =
        (qv v : ℂ) ^ (-(e : ℂ) * ((1 : ℂ) / 2 - s)) := by
    rw [Units.val_zpow_eq_zpow_val]
    exact hOuterFactorVal
  have hSubtypeSum :
      (∑ l : Finset.Icc 1 R, Term l.1) =
        ∑ l ∈ Finset.Icc 1 R, Term l := by
    calc
      _ = ∑ l ∈ (Finset.Icc 1 R).attach, Term l.1 :=
        Finset.sum_coe_sort_eq_attach (Finset.Icc 1 R)
          (fun l : Finset.Icc 1 R => Term l.1)
      _ = _ := Finset.sum_attach (Finset.Icc 1 R) Term
  have hInnerSumSub :
      B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1 =
        (1 + (1 - (qv v : ℂ)⁻¹) *
          ∑ j ∈ Finset.Icc 1 (e / 3), (qv v : ℂ) ^ (-6 * (j : ℂ) * s)) •
            B.e (-(e : ZMod 3)) +
          ((qv v : ℂ) ^ (-2 * ((e : ℂ) + 1) * s) * shellTerm D A v (e + 1)) •
            B.e ((e : ZMod 3) + 2) := by
    calc
      _ = B.e (-(e : ZMod 3)) + ∑ l ∈ Finset.Icc 1 R, Term l := by
        rw [hSubtypeSum]
      _ = _ := by simpa [J, c] using hInnerSum
  rw [hscaled, hBallTerms, hpull]
  calc
    _ = (((absFin v ((unifLoc v : v.adicCompletion F) ^ (e : ℤ)) : ℝ) : ℂ) *
          qBase) •
          (B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      exact congrArg (fun r : ℝ =>
        (((r : ℂ) * qBase) •
          (B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1)))
        hOuterAbsEq.symm
    _ = ((qv v : ℂ) ^ (-(e : ℂ) * ((1 : ℂ) / 2 - s))) •
          (B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1) := by
      exact congrArg (fun c : ℂ => c •
        (B.e (-(e : ZMod 3)) + ∑ l : Finset.Icc 1 R, Term l.1)) hOuterFactorUnit
    _ = _ := by rw [hInnerSumSub]

/-- **jq:negative** (10:458–468): `J_e = 0` for `e < 0`. -/
theorem jacquet_spherical_neg (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (s : ℂ) (f0 : L.L → T.V)
    (hf0 : IsSection L T s f0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (e : ℤ) (he : e < 0) :
    jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) = 0 := by
  let y := unifLoc v ^ e
  obtain ⟨t, ht, hψt⟩ := psi_conductor_unramified A v hd
  have htval : Valued.v t ≤ WithZero.exp (1 : ℤ) := by
    simpa [ball] using ht
  have hπval : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (unifLoc v : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (unif v) := by
      simp [unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hyinvval : Valued.v ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp e := by
    dsimp [y]
    rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    rw [map_inv₀, map_zpow₀, hπval, ← WithZero.exp_zsmul]
    simp
  let b := t * ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
  have hbval : Valued.v b ≤ 1 := by
    dsimp [b]
    rw [map_mul, hyinvval]
    calc
      Valued.v t * WithZero.exp e ≤ WithZero.exp (1 : ℤ) * WithZero.exp e :=
        by gcongr
      _ = WithZero.exp (1 + e) := by rw [← WithZero.exp_add]
      _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).2 (by omega)
  have hbO : b ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hbval
  have hlift : L.n (Multiplicative.ofAdd t) * L.a y =
      L.a y * L.n (Multiplicative.ofAdd b) := by
    simpa [b] using L.lift_na t y
  have hfix : rtr (L.n (Multiplicative.ofAdd t)) (rtr (L.a y) f0) = rtr (L.a y) f0 := by
    funext g
    change f0 ((g * L.n (Multiplicative.ofAdd t)) * L.a y) = f0 (g * L.a y)
    rw [mul_assoc, hlift, ← mul_assoc]
    exact hK (g * L.a y) (L.n (Multiplicative.ofAdd b)) (τ.n_mem b hbO)
  have hcov := (jacquet_equiv L T A μ s (rtr (L.a y) f0)
    (IsSection.rtr hf0 (L.a y))).1 t
  have hJ : jacquet L A μ (rtr (L.a y) f0) =
      A.ψ v t • jacquet L A μ (rtr (L.a y) f0) := by
    exact (congrArg (fun f => jacquet L A μ f) hfix).symm.trans hcov
  have hscalar : A.ψ v t - 1 ≠ 0 := sub_ne_zero.mpr hψt
  have hzero : (A.ψ v t - 1) • jacquet L A μ (rtr (L.a y) f0) = 0 := by
    calc
      (A.ψ v t - 1) • jacquet L A μ (rtr (L.a y) f0) =
          A.ψ v t • jacquet L A μ (rtr (L.a y) f0) -
            jacquet L A μ (rtr (L.a y) f0) := by rw [sub_smul, one_smul]
      _ = 0 := by rw [← hJ, sub_self]
  have hJy : jacquet L A μ (rtr (L.a y) f0) = 0 :=
    (smul_eq_zero.mp hzero).resolve_left hscalar
  simpa [y] using hJy

/-- **jq:unit-rule** (eq:app-unit-rule, 10:469–482). -/
theorem jacquet_spherical_unit (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) (f0 : L.L → T.V)
    (hf0 : IsSection L T s f0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (e : ℤ)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    jacquet L A μ (rtr (L.a (unifLoc v ^ e * u)) f0) =
      localChi D v u ^ (2 * e) • jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) := by
  let y := unifLoc v ^ e
  let ζ := muThree D (H.hilb v y u)
  have hζ := muThree_hilb_unif_unit (D := D) (H := H) (v := v) hv e u hu
  have hamul : L.a y * L.a u = L.z ζ * L.a (y * u) := by
    simpa [ζ] using L.a_mul y u
  have hζinv : (L.z ζ)⁻¹ = L.z (ζ⁻¹) := by
    simpa using (map_inv L.z ζ)
  have ha : L.a (y * u) = L.z (ζ⁻¹) * L.a y * L.a u := by
    calc
      L.a (y * u) = (L.z ζ)⁻¹ * L.z ζ * L.a (y * u) := by group
      _ = (L.z ζ)⁻¹ * (L.z ζ * L.a (y * u)) := by group
      _ = (L.z ζ)⁻¹ * (L.a y * L.a u) := by rw [hamul.symm]
      _ = L.z (ζ⁻¹) * L.a y * L.a u := by rw [hζinv]; group
  have hKu : L.a u ∈ τ.Kmax := τ.a_mem u hu.1 hu.2
  have huFix : rtr (L.a u) f0 = f0 := by
    funext g
    exact hK g (L.a u) hKu
  have hnew : rtr (L.a (y * u)) f0 = rtr (L.z (ζ⁻¹)) (rtr (L.a y) f0) := by
    calc
      rtr (L.a (y * u)) f0 = rtr (L.z (ζ⁻¹) * L.a y * L.a u) f0 := by rw [ha]
      _ = rtr (L.z (ζ⁻¹)) (rtr (L.a y) (rtr (L.a u) f0)) := by
        funext g
        simp [rtr, mul_assoc]
      _ = rtr (L.z (ζ⁻¹)) (rtr (L.a y) f0) := by rw [huFix]
  have hequiv := (jacquet_equiv L T A μ s (rtr (L.a y) f0)
    (IsSection.rtr hf0 (L.a y))).2 (ζ⁻¹)
  have hscalar : (((ζ⁻¹ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) = localChi D v u ^ (2 * e) := by
    calc
      (((ζ⁻¹ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) =
          ((((ζ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ)⁻¹) := by simp
      _ = (localChi D v u ^ (-(2 * e)))⁻¹ := by rw [hζ]
      _ = localChi D v u ^ (2 * e) := by simp [zpow_neg]
  calc
    jacquet L A μ (rtr (L.a (y * u)) f0) =
        jacquet L A μ (rtr (L.z (ζ⁻¹)) (rtr (L.a y) f0)) := by rw [hnew]
    _ = (((ζ⁻¹ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) • jacquet L A μ (rtr (L.a y) f0) := by
      exact hequiv
    _ = localChi D v u ^ (2 * e) • jacquet L A μ (rtr (L.a y) f0) := by rw [hscalar]

/-- The shell vector `u = e₀ + q^{-1/6} g_{-2} e₂` (eq:app-J-values). -/
def shellVec (D : FieldData F) (A : AddCharData F) {T : TorusRep D H v} (B : TameTorusBasis T) : T.V :=
  B.e 0 + ((qv v : ℂ) ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)) • B.e 2

private theorem chiPow_add_six (D : FieldData F) (v : FinPlace F) (x : F) (j k : ℤ) :
    chiPow D v x (j + 6 * k) = chiPow D v x j := by
  by_cases hx : residue v x = 0
  · simp [chiPow, hx]
  · have hroot : chi D v x ^ 6 = 1 := by
      have hχ : ((chiAlg v x : (𝓞 F)ˣ) : 𝓞 F) ^ 6 = 1 := by
        have hp := (chiAlg v x).property
        exact congrArg (fun u : (𝓞 F)ˣ => (u : 𝓞 F)) hp
      unfold chi
      rw [if_neg hx]
      calc
        (D.σ0 (algebraMap (𝓞 F) F ((chiAlg v x : (𝓞 F)ˣ) : 𝓞 F))) ^ 6 =
            D.σ0 (algebraMap (𝓞 F) F (((chiAlg v x : (𝓞 F)ˣ) : 𝓞 F) ^ 6)) := by
          rw [map_pow, map_pow]
        _ = 1 := by rw [hχ]; simp
    have hne : chi D v x ≠ 0 := by
      intro hz
      simp [hz] at hroot
    unfold chiPow
    rw [if_neg hx, if_neg hx, zpow_add₀ hne j (6 * k), zpow_mul]
    simp [hroot]

private theorem gaussLoc_add_six (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (j k : ℤ) : gaussLoc D A v (j + 6 * k) = gaussLoc D A v j := by
  unfold gaussLoc
  congr 1
  apply finsum_congr
  intro x
  rw [chiPow_add_six D v (algebraMap (𝓞 F) F x.out) j k]

private theorem finiteGeo (q : ℂ) (hq : q ≠ 0) (k : ℕ) :
    1 + (1 - q⁻¹) * ∑ j ∈ Finset.Icc 1 k, q ^ j = q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), pow_succ]
      calc
        1 + (1 - q⁻¹) * (q ^ k * q + ∑ j ∈ Finset.Icc 1 k, q ^ j) =
            (1 + (1 - q⁻¹) * ∑ j ∈ Finset.Icc 1 k, q ^ j) +
              (1 - q⁻¹) * (q ^ k * q) := by ring
        _ = q ^ k + (1 - q⁻¹) * (q ^ k * q) := by rw [ih]
        _ = q ^ k * q := by field_simp [hq] <;> ring

/-- **jq:shell-s0** (eq:app-J-values): at `s = -1/6` (the space `I^-` of the paper, realized as
`I(T', -1/6)` with `T' = T.weyl`, `B' = B.weyl`). -/
theorem jacquet_spherical_s0 (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (f0 : L.L → T.V)
    (hf0 : IsSection L T (-(1 / 6)) f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (k : ℕ) :
    jacquet L A μ (rtr (L.a (unifLoc v ^ ((3 * k : ℕ) : ℤ))) f0) =
        (qv v : ℂ) ^ (-(k : ℂ)) • shellVec D A B ∧
    jacquet L A μ (rtr (L.a (unifLoc v ^ ((3 * k + 1 : ℕ) : ℤ))) f0) =
        ((qv v : ℂ) ^ (-(k : ℂ) - 1 / 2) * g2 D A v) • shellVec D A B ∧
    jacquet L A μ (rtr (L.a (unifLoc v ^ ((3 * k + 2 : ℕ) : ℤ))) f0) = 0 := by
  let Q : ℂ := qv v
  have hqR : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hq0 : Q ≠ 0 := by
    dsimp [Q]
    exact_mod_cast (ne_of_gt hqR)
  have hqprod (a b : ℂ) : Q ^ a * Q ^ b = Q ^ (a + b) := by
    exact (Complex.cpow_add (x := Q) a b hq0).symm
  have hgeo (n : ℕ) :
      1 + (1 - Q⁻¹) *
        ∑ j ∈ Finset.Icc 1 n, Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ))) = Q ^ (n : ℂ) := by
    have hsum :
        ∑ j ∈ Finset.Icc 1 n, Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ))) =
          ∑ j ∈ Finset.Icc 1 n, Q ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (-6 : ℂ) * (j : ℂ) * (-(1 / 6 : ℂ)) = (j : ℂ) by ring,
        Complex.cpow_natCast]
    rw [hsum]
    simpa only [Complex.cpow_natCast] using finiteGeo Q hq0 n
  have hprod : g2 D A v * gaussLoc D A v (-2) = 1 := by
    rw [g2_eq_gaussLoc]
    exact gaussLoc_mul_neg D A v hv hd 2 (by norm_num)
  have hperA : gaussLoc D A v (-2 * ((3 * k + 1 : ℕ) : ℤ)) =
      gaussLoc D A v (-2) := by
    have he : -2 * ((3 * k + 1 : ℕ) : ℤ) = -2 + 6 * (-(k : ℤ)) := by
      push_cast
      ring
    rw [he]
    exact gaussLoc_add_six D A v (-2) (-(k : ℤ))
  have hperB : gaussLoc D A v (-2 * ((3 * k + 2 : ℕ) : ℤ)) =
      g2 D A v := by
    rw [g2_eq_gaussLoc]
    have he : -2 * ((3 * k + 2 : ℕ) : ℤ) = 2 + 6 * (-(k + 1 : ℤ)) := by
      push_cast
      ring
    rw [he]
    exact gaussLoc_add_six D A v 2 (-(k + 1 : ℤ))
  have hnotA : ¬ 3 ∣ 3 * k + 1 := by
    rintro ⟨m, hm⟩
    omega
  have hnotB : ¬ 3 ∣ 3 * k + 2 := by
    rintro ⟨m, hm⟩
    omega
  have hdivC : 3 ∣ 3 * k + 3 := ⟨k + 1, by omega⟩
  have htermA : shellTerm D A v (3 * k + 1) =
      Q ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * ((3 * k + 1 : ℕ) : ℤ)) := by
    simp [shellTerm, Q, hnotA]
  have htermB : shellTerm D A v (3 * k + 2) =
      Q ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * ((3 * k + 2 : ℕ) : ℤ)) := by
    simp [shellTerm, Q, hnotB]
  have htermC : shellTerm D A v (3 * k + 3) = -Q⁻¹ := by
    simp [shellTerm, Q, hdivC]
  have houter0 :
      Q ^ (-((3 * k : ℕ) : ℂ) * (1 / 2 - (-(1 / 6 : ℂ)))) = Q ^ (-(2 * (k : ℂ))) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have houter1 :
      Q ^ (-((3 * k + 1 : ℕ) : ℂ) * (1 / 2 - (-(1 / 6 : ℂ)))) =
        Q ^ (-(2 * (k : ℂ)) - 2 / 3) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have houter2 :
      Q ^ (-((3 * k + 2 : ℕ) : ℂ) * (1 / 2 - (-(1 / 6 : ℂ)))) =
        Q ^ (-(2 * (k : ℂ)) - 4 / 3) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have htermExp0 :
      Q ^ (-2 * (((3 * k : ℕ) : ℂ) + 1) * (-(1 / 6 : ℂ))) = Q ^ ((k : ℂ) + 1 / 3) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have htermExp1 :
      Q ^ (-2 * (((3 * k + 1 : ℕ) : ℂ) + 1) * (-(1 / 6 : ℂ))) =
        Q ^ ((k : ℂ) + 2 / 3) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have htermExp2 :
      Q ^ (-2 * (((3 * k + 2 : ℕ) : ℂ) + 1) * (-(1 / 6 : ℂ))) = Q ^ ((k : ℂ) + 1) := by
    apply congrArg (fun z : ℂ => Q ^ z)
    push_cast
    ring
  have hcoeff00 :
      Q ^ (-(2 * (k : ℂ))) * (1 + (1 - Q⁻¹) *
        ∑ j ∈ Finset.Icc 1 (3 * k / 3), Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ)))) =
        Q ^ (-(k : ℂ)) := by
    have hdiv : 3 * k / 3 = k := by omega
    rw [hdiv, hgeo k]
    calc
      Q ^ (-(2 * (k : ℂ))) * Q ^ (k : ℂ) = Q ^ (-(2 * (k : ℂ)) + (k : ℂ)) :=
        hqprod _ _
      _ = Q ^ (-(k : ℂ)) := by congr 1 <;> ring
  have hcoeff02 :
      Q ^ (-(2 * (k : ℂ))) *
        (Q ^ ((k : ℂ) + 1 / 3) * (Q ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2))) =
        Q ^ (-(k : ℂ)) * Q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2) := by
    calc
      _ = (Q ^ (-(2 * (k : ℂ))) * Q ^ ((k : ℂ) + 1 / 3)) *
          Q ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2) := by ring
      _ = Q ^ (-(2 * (k : ℂ)) + ((k : ℂ) + 1 / 3)) *
          Q ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2) := by rw [hqprod]
      _ = Q ^ (-(2 * (k : ℂ)) + ((k : ℂ) + 1 / 3) + (-(1 / 2 : ℂ))) *
          gaussLoc D A v (-2) := by rw [hqprod]
      _ = Q ^ (-(k : ℂ) - 1 / 6) * gaussLoc D A v (-2) := by
        congr 2
        ring
      _ = Q ^ (-(k : ℂ)) * Q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2) := by
        exact congrArg (fun z : ℂ => z * gaussLoc D A v (-2))
          (hqprod (-(k : ℂ)) (-(1 / 6 : ℂ))).symm
  have hcoeff10 :
      Q ^ (-(2 * (k : ℂ)) - 2 / 3) * (1 + (1 - Q⁻¹) *
        ∑ j ∈ Finset.Icc 1 ((3 * k + 1) / 3),
          Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ)))) = Q ^ (-(k : ℂ) - 2 / 3) := by
    have hdiv : (3 * k + 1) / 3 = k := by omega
    rw [hdiv, hgeo k]
    calc
      Q ^ (-(2 * (k : ℂ)) - 2 / 3) * Q ^ (k : ℂ) =
          Q ^ (-(2 * (k : ℂ)) - 2 / 3 + (k : ℂ)) := hqprod _ _
      _ = Q ^ (-(k : ℂ) - 2 / 3) := by congr 1 <;> ring
  have hcoeff12 :
      Q ^ (-(2 * (k : ℂ)) - 2 / 3) *
        (Q ^ ((k : ℂ) + 2 / 3) * (Q ^ (-(1 / 2 : ℂ)) * g2 D A v)) =
        Q ^ (-(k : ℂ) - 1 / 2) * g2 D A v := by
    calc
      _ = (Q ^ (-(2 * (k : ℂ)) - 2 / 3) * Q ^ ((k : ℂ) + 2 / 3)) *
          Q ^ (-(1 / 2 : ℂ)) * g2 D A v := by ring
      _ = Q ^ (-(2 * (k : ℂ)) - 2 / 3 + ((k : ℂ) + 2 / 3)) *
          Q ^ (-(1 / 2 : ℂ)) * g2 D A v := by rw [hqprod]
      _ = Q ^ (-(2 * (k : ℂ)) - 2 / 3 + ((k : ℂ) + 2 / 3) + (-(1 / 2 : ℂ))) *
          g2 D A v := by rw [hqprod]
      _ = Q ^ (-(k : ℂ) - 1 / 2) * g2 D A v := by
        congr 2
        ring
  have hcoeff11 :
      Q ^ (-(k : ℂ) - 1 / 2) * g2 D A v *
        (Q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)) = Q ^ (-(k : ℂ) - 2 / 3) := by
    calc
      _ = Q ^ (-(k : ℂ) - 1 / 2) * Q ^ (-(1 / 6 : ℂ)) *
          (g2 D A v * gaussLoc D A v (-2)) := by ring
      _ = Q ^ (-(k : ℂ) - 1 / 2) * Q ^ (-(1 / 6 : ℂ)) := by rw [hprod, mul_one]
      _ = Q ^ (-(k : ℂ) - 1 / 2 + (-(1 / 6 : ℂ))) := hqprod _ _
      _ = Q ^ (-(k : ℂ) - 2 / 3) := by congr 1 <;> ring
  have hcoeff20 :
      Q ^ (-(2 * (k : ℂ)) - 4 / 3) * (1 + (1 - Q⁻¹) *
        ∑ j ∈ Finset.Icc 1 ((3 * k + 2) / 3),
          Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ)))) = Q ^ (-(k : ℂ) - 4 / 3) := by
    have hdiv : (3 * k + 2) / 3 = k := by omega
    rw [hdiv, hgeo k]
    calc
      Q ^ (-(2 * (k : ℂ)) - 4 / 3) * Q ^ (k : ℂ) =
          Q ^ (-(2 * (k : ℂ)) - 4 / 3 + (k : ℂ)) := hqprod _ _
      _ = Q ^ (-(k : ℂ) - 4 / 3) := by congr 1 <;> ring
  have hcoeff22 :
      Q ^ (-(2 * (k : ℂ)) - 4 / 3) *
        (Q ^ ((k : ℂ) + 1) * (-Q⁻¹)) = -Q ^ (-(k : ℂ) - 4 / 3) := by
    have hqinv : Q⁻¹ = Q ^ (-1 : ℂ) := by
      symm
      rw [Complex.cpow_neg]
      simp
    calc
      _ = -(Q ^ (-(2 * (k : ℂ)) - 4 / 3) * Q ^ ((k : ℂ) + 1) * Q ^ (-1 : ℂ)) := by
        rw [hqinv]
        ring
      _ = -(Q ^ (-(2 * (k : ℂ)) - 4 / 3 + ((k : ℂ) + 1) + (-1 : ℂ))) := by
        rw [hqprod, hqprod]
      _ = -Q ^ (-(k : ℂ) - 4 / 3) := by congr 2 <;> ring
  have hZ3 : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
  have hidx00 : ((3 * k : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_mul, hZ3]
    simp
  have hidx01 : (-(3 * k + 1 : ℕ) : ZMod 3) = 2 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    have hn : (-1 : ZMod 3) = 2 := by
      apply sub_eq_zero.mp
      change (-3 : ZMod 3) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (-3) 3).2 (by norm_num)
    simpa [hn]
  have hidx01pos : ((3 * k + 1 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    simp
  have hidx02 : ((3 * k + 2 : ℕ) : ZMod 3) = 2 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    simp
  have hidxAadd2 : ((3 * k + 1 : ℕ) : ZMod 3) + 2 = 0 := by
    rw [hidx01pos]
    apply sub_eq_zero.mp
    change (3 : ZMod 3) = 0
    exact_mod_cast hZ3
  have hidx10 : (-(3 * k + 2 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    have hn : (-2 : ZMod 3) = 1 := by
      apply sub_eq_zero.mp
      change (-3 : ZMod 3) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (-3) 3).2 (by norm_num)
    simpa [hn]
  have hidx11 : ((3 * k + 3 : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    simp
  have hsum22 : (2 : ZMod 3) + 2 = 1 := by
    apply sub_eq_zero.mp
    change (3 : ZMod 3) = 0
    exact_mod_cast hZ3
  have hidxBadd2 : ((3 * k + 2 : ℕ) : ZMod 3) + 2 = 1 := by
    rw [hidx02]
    exact hsum22
  have hidx20 : (-(3 * k + 2 : ℕ) : ZMod 3) = 1 := hidx10
  have hidx21 : ((3 * k + 4 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul, hZ3]
    have hn : (4 : ZMod 3) = 1 := by
      apply sub_eq_zero.mp
      change (3 : ZMod 3) = 0
      exact hZ3
    simpa using hn
  refine ⟨?_, ?_, ?_⟩
  · have hJ := jacquet_spherical L τ T B A μ hv hd (-(1 / 6 : ℂ)) f0 hf0 h1 hK (3 * k)
    rw [hJ, houter0, htermExp0, smul_add, smul_smul, smul_smul,
      hcoeff00, htermA, hperA, hcoeff02]
    simp only [shellVec, smul_add, smul_smul, hidx00, neg_zero, add_zero, one_smul]
    simp [mul_assoc, Q]
  · have hJ := jacquet_spherical L τ T B A μ hv hd (-(1 / 6 : ℂ)) f0 hf0 h1 hK (3 * k + 1)
    have hfirst :
        Q ^ (-(2 * (k : ℂ)) - 2 / 3) *
          (1 + (1 - Q⁻¹) *
            ∑ j ∈ Finset.Icc 1 ((3 * k + 1) / 3),
              Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ)))) =
          Q ^ (-(k : ℂ) - 2 / 3) := hcoeff10
    have hlast :
        Q ^ (-(2 * (k : ℂ)) - 2 / 3) *
          (Q ^ ((k : ℂ) + 2 / 3) *
            shellTerm D A v (3 * k + 2)) =
          Q ^ (-(k : ℂ) - 1 / 2) * g2 D A v := by
      rw [htermB, hperB]
      exact hcoeff12
    rw [hJ, houter1, htermExp1, smul_add, smul_smul, smul_smul, hfirst, hlast]
    simp only [shellVec, smul_add, smul_smul, hidx01, hidxAadd2, one_smul]
    rw [hcoeff11]
    abel
  · have hJ := jacquet_spherical L τ T B A μ hv hd (-(1 / 6 : ℂ)) f0 hf0 h1 hK (3 * k + 2)
    have hfirst :
        Q ^ (-(2 * (k : ℂ)) - 4 / 3) *
          (1 + (1 - Q⁻¹) *
            ∑ j ∈ Finset.Icc 1 ((3 * k + 2) / 3),
              Q ^ (-6 * (j : ℂ) * (-(1 / 6 : ℂ)))) =
          Q ^ (-(k : ℂ) - 4 / 3) := hcoeff20
    have hlast :
        Q ^ (-(2 * (k : ℂ)) - 4 / 3) *
          (Q ^ ((k : ℂ) + 1) * shellTerm D A v (3 * k + 3)) =
          -Q ^ (-(k : ℂ) - 4 / 3) := by
      rw [htermC]
      exact hcoeff22
    rw [hJ, houter2, htermExp2, smul_add, smul_smul, smul_smul, hfirst, hlast]
    simp only [smul_neg, neg_smul, hidx20, hidxBadd2, one_smul]
    abel

/-- **jq:table** (eq:theta-local-values through any coordinate): for the spherical vector of
`I(T, -1/6)` and every linear functional `c`, `c(J(a(ϖ^e u))) = sphericalTable(e,u) · c(J(1))`. -/
theorem jacquet_spherical_table (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (f0 : L.L → T.V)
    (hf0 : IsSection L T (-(1 / 6)) f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (c : T.V →ₗ[ℂ] ℂ) (e : ℤ)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    c (jacquet L A μ (rtr (L.a (unifLoc v ^ e * u)) f0)) =
      sphericalTable D A v e u * c (jacquet L A μ f0) := by
  have hbase : jacquet L A μ f0 = shellVec D A B := by
    have hs0 := jacquet_spherical_s0 L τ T B A μ hv hd f0 hf0 h1 hK 0
    have hrt : rtr (L.a (1 : (v.adicCompletion F)ˣ)) f0 = f0 := by
      rw [L.a_one]
      funext g
      simp [rtr]
    calc
      jacquet L A μ f0 = jacquet L A μ (rtr (L.a 1) f0) := by rw [hrt]
      _ = shellVec D A B := by simpa [unifLoc] using hs0.1
  have hunit := jacquet_spherical_unit L τ T A μ hv (-(1 / 6 : ℂ)) f0 hf0 hK e u hu
  by_cases heneg : e < 0
  · have hneg := jacquet_spherical_neg L τ T B A μ hv hd (-(1 / 6 : ℂ)) f0 hf0 hK e heneg
    rw [hunit, hneg]
    simp [sphericalTable, heneg]
  · have henonneg : 0 ≤ e := le_of_not_gt heneg
    let k : ℕ := (e / 3).toNat
    let r : ℕ := (e % 3).toNat
    have hdiv : e / 3 = (k : ℤ) := by
      dsimp [k]
      omega
    have hrem : e % 3 = (r : ℤ) := by
      dsimp [r]
      omega
    have hrlt : r < 3 := by omega
    have heq : e = ((3 * k + r : ℕ) : ℤ) := by
      omega
    have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
    have hqpow0 :
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((e / 3 : ℤ) : ℝ)) : ℝ) : ℂ) =
          (qv v : ℂ) ^ (-(k : ℂ)) := by
      rw [hdiv]
      change (((qv v) ^ (-(k : ℝ)) : ℝ) : ℂ) = _
      rw [Complex.ofReal_cpow hqpos.le]
      congr 1
      simp
    have hqpow1 :
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((e / 3 : ℤ) : ℝ) - 1 / 2) : ℝ) : ℂ) =
          (qv v : ℂ) ^ (-(k : ℂ) - 1 / 2) := by
      rw [hdiv]
      change (((qv v) ^ (-(k : ℝ) - 1 / 2) : ℝ) : ℂ) = _
      rw [Complex.ofReal_cpow hqpos.le]
      congr 1
      simp
    interval_cases r
    · have hs0 := jacquet_spherical_s0 L τ T B A μ hv hd f0 hf0 h1 hK k
      have he : e = (3 * k : ℕ) := by simpa using heq
      have hJ : jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) =
          (qv v : ℂ) ^ (-(k : ℂ)) • shellVec D A B := by
        simpa [he] using hs0.1
      have hrem0 : e % 3 = 0 := by simpa using hrem
      have htable : sphericalTable D A v e u =
          localChi D v u ^ (2 * e) * (qv v : ℂ) ^ (-(k : ℂ)) := by
        simp only [sphericalTable, if_neg heneg, if_pos hrem0]
        rw [hqpow0]
      rw [hunit, hJ, map_smul, hbase, htable]
      simp [smul_smul, mul_assoc]
    · have hs0 := jacquet_spherical_s0 L τ T B A μ hv hd f0 hf0 h1 hK k
      have he : e = (3 * k + 1 : ℕ) := by simpa using heq
      have hJ : jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) =
          ((qv v : ℂ) ^ (-(k : ℂ) - 1 / 2) * g2 D A v) • shellVec D A B := by
        simpa [he] using hs0.2.1
      have htable : sphericalTable D A v e u =
          localChi D v u ^ (2 * e) *
            ((qv v : ℂ) ^ (-(k : ℂ) - 1 / 2) * g2 D A v) := by
        have hrem1 : e % 3 = 1 := by simpa using hrem
        simp only [sphericalTable, if_neg heneg, if_neg (by omega : e % 3 ≠ 0),
          if_pos hrem1]
        rw [hqpow1]
      rw [hunit, hJ, map_smul, hbase, htable]
      simp [smul_smul, mul_assoc]
    · have hs0 := jacquet_spherical_s0 L τ T B A μ hv hd f0 hf0 h1 hK k
      have he : e = (3 * k + 2 : ℕ) := by simpa using heq
      have hJ : jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) = 0 := by
        simpa [he] using hs0.2.2
      have htable : sphericalTable D A v e u = 0 := by
        have hrem2 : e % 3 = 2 := by simpa using hrem
        simp only [sphericalTable, if_neg heneg, if_neg (by omega : e % 3 ≠ 0),
          if_neg (by omega : e % 3 ≠ 1)]
        simp
      rw [hunit, hJ, hbase, htable]
      simp

end LocalInt

/-! ## P-LOCAL-INT at complex places -/

section ComplexInt

/-- `n(x)`, `a(y)`, `w` in `PGL₂(ℂ)`. -/
def nC (x : ℂ) : PGL2 ℂ := QuotientGroup.mk (upperM ℂ x)
def aC (y : ℂˣ) : PGL2 ℂ := QuotientGroup.mk (diagM ℂ y)
def wC : PGL2 ℂ := QuotientGroup.mk (weylM ℂ)

/-- The spherical section on `PGL₂(ℂ)` (through a representative; `sphericalC` is scalar invariant). -/
def sphC (s : ℂ) (g : PGL2 ℂ) : ℂ := sphericalC s (Quotient.out g)

theorem sphC_mk (s : ℂ) (g : GL (Fin 2) ℂ) : sphC s (QuotientGroup.mk g) = sphericalC s g := by
  sorry

theorem sphC_isSection (s : ℂ) : IsSectionC s (sphC s) ∧ Continuous (sphC s) := by
  sorry

/-- **def:jacquet-C**: `𝒥_ℂ f = ∫_ℂ ψ_w(-x) f(w n(x)) dx` (Lebesgue measure). -/
def jacquetC (f : PGL2 ℂ → ℂ) : ℂ := ∫ x : ℂ, psiC (-x) * f (wC * nC x)

/-- **def:intertwine-C**. -/
def intertwineC (f : PGL2 ℂ → ℂ) (g : PGL2 ℂ) : ℂ := ∫ x : ℂ, f (wC * nC x * g)

/-- **def:derivative-vector** (03:300–312): `f_m = (∂₁ - m i ∂₂) π(n(x₁ + i x₂)) f |₀`. -/
def derivVecC (m : ℤ) (f : PGL2 ℂ → ℂ) (g : PGL2 ℂ) : ℂ :=
  fderiv ℝ (fun z : ℂ => f (g * nC z)) 0 1 -
    (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => f (g * nC z)) 0 Complex.I

/-- The constant `2π Γ(4/3)⁻¹ (2π)^{1/3}`. -/
def besselConst : ℝ := 2 * Real.pi / Real.Gamma (4 / 3) * (2 * Real.pi) ^ ((1 : ℝ) / 3)

/-- **jq:complex-equiv**: `𝒥_ℂ(π(n(u))f) = ψ_w(u) 𝒥_ℂ(f)` for continuous sections, `Re s > 0`. -/
theorem jacquetC_equiv (s : ℂ) (hs : 0 < s.re) (f : PGL2 ℂ → ℂ) (hf : IsSectionC s f)
    (hcont : Continuous f) (u : ℂ) : jacquetC (rtr (nC u) f) = psiC u * jacquetC f := by
  sorry

/-- **jq:complex-bessel** (eq:theta-complex-bessel, 03:263–290). -/
theorem jacquetC_spherical (y : ℂˣ) :
    jacquetC (rtr (aC y) (sphC (1 / 6))) =
      ((besselConst * ‖(y : ℂ)‖ * besselK (1 / 3) (4 * Real.pi * ‖(y : ℂ)‖) : ℝ) : ℂ) := by
  sorry

/-- **jq:complex-derivative** (eq:theta-complex-derivative, 03:292–312). -/
theorem jacquetC_derivative (m : ℤ) (hm : m = 1 ∨ m = -1) (y : ℂˣ) :
    jacquetC (rtr (aC y) (derivVecC m (sphC (1 / 6)))) =
      -(4 * Real.pi * Complex.I) * besselConst * (Complex.normSq (y : ℂ) : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖(y : ℂ)‖) : ℂ) := by
  sorry

/-- **jq:complex-rotation**: `π(w) f_m = f_{-m}` (`Ad(w)E_a ≡ E_{ā}` modulo `𝔰𝔲(2)`). -/
theorem derivVecC_rotate (m : ℤ) (s : ℂ) :
    rtr wC (derivVecC m (sphC s)) = derivVecC (-m) (sphC s) := by
  sorry

theorem derivVecC_isSection (m : ℤ) (s : ℂ) :
    IsSectionC s (derivVecC m (sphC s)) ∧ Continuous (derivVecC m (sphC s)) := by
  sorry

/-- **jq:complex-sheet** (eq:theta-complex-bounds, T6 at complex places, `δ = 1/3`). -/
theorem sheetHypC_bessel (m : ℤ) (hm : m = 1 ∨ m = -1) (c : ℂ) :
    SheetHypC (1 / 3) (fun y : ℂ => c * (Complex.normSq y : ℂ) * omegaAng m y *
      (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) := by
  sorry

/-- **int:complex-spherical**: `M_ℂ(s) f°_s = (π/(2s)) f°_{-s}` for `Re s > 0`. -/
theorem intertwineC_spherical (s : ℂ) (hs : 0 < s.re) :
    intertwineC (sphC s) = fun g => (Real.pi / (2 * s)) * sphC (-s) g := by
  sorry

end ComplexInt

end ArtinPrimitiveRoots.A1.Theta
