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

/-- The terminal shell coefficient `I_{l-1,l}` (eq:app-shell-integrals, `l = e+1`). -/
def shellTerm (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (l : ℕ) : ℂ :=
  if 3 ∣ l then -((qv v : ℂ)⁻¹) else (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (-2 * (l : ℤ))

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
  sorry

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
  sorry

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
