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
  sorry

/-- **jq:unit-rule** (eq:app-unit-rule, 10:469–482). -/
theorem jacquet_spherical_unit (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) (f0 : L.L → T.V)
    (hf0 : IsSection L T s f0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) (e : ℤ)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    jacquet L A μ (rtr (L.a (unifLoc v ^ e * u)) f0) =
      localChi D v u ^ (2 * e) • jacquet L A μ (rtr (L.a (unifLoc v ^ e)) f0) := by
  sorry

/-- The shell vector `u = e₀ + q^{-1/6} g_{-2} e₂` (eq:app-J-values). -/
def shellVec (D : FieldData F) (A : AddCharData F) {T : TorusRep D H v} (B : TameTorusBasis T) : T.V :=
  B.e 0 + ((qv v : ℂ) ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)) • B.e 2

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
  sorry

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
  obtain ⟨f, _, hrep⟩ := sphericalC_isSection s
  have hq : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : PGL2 ℂ)) : PGL2 ℂ) =
      QuotientGroup.mk g := by
    simp
  have hout := hrep (Quotient.out (QuotientGroup.mk g : PGL2 ℂ))
  have hg := hrep g
  rw [hq] at hout
  change sphericalC s (Quotient.out (QuotientGroup.mk g : PGL2 ℂ)) = sphericalC s g
  exact hout.symm.trans hg

theorem sphC_isSection (s : ℂ) : IsSectionC s (sphC s) ∧ Continuous (sphC s) := by
  obtain ⟨f, hf, hrep⟩ := sphericalC_isSection s
  have heq : sphC s = f := by
    funext q
    refine QuotientGroup.induction_on q ?_
    intro g
    exact (sphC_mk s g).trans (hrep g).symm
  let base : GL (Fin 2) ℂ → ℝ := fun g =>
    ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)
  have hden : ∀ g : GL (Fin 2) ℂ,
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 ≠ 0 := by
    intro g h
    have h00 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ = 0 := by
      have h0 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      have h1 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
      nlinarith
    have h01 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ = 0 := by
      have h0 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      have h1 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
      nlinarith
    have he0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := norm_eq_zero.mp h00
    have he1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := norm_eq_zero.mp h01
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, he0, he1]
  have hbase : Continuous base := by
    apply (by fun_prop : Continuous fun g : GL (Fin 2) ℂ =>
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖).div
        (by fun_prop : Continuous fun g : GL (Fin 2) ℂ =>
          ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
            ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) hden
  have hbase_ne (g : GL (Fin 2) ℂ) : base g ≠ 0 := by
    apply div_ne_zero
    · exact norm_ne_zero_iff.mpr g.det_ne_zero
    · exact hden g
  have hsph : Continuous (sphericalC s) := by
    have hpow : Continuous fun g : GL (Fin 2) ℂ =>
        ((base g : ℝ) : ℂ) ^ (1 + 2 * s) := by
      rw [continuous_iff_continuousAt]
      intro g
      have hbaseAt : ContinuousAt base g := hbase.continuousAt (x := g)
      have hpowAt : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (1 + 2 * s)) (base g) :=
        Complex.continuousAt_ofReal_cpow_const (base g) (1 + 2 * s)
          (Or.inr (hbase_ne g))
      exact hpowAt.comp hbaseAt
    change Continuous (fun g : GL (Fin 2) ℂ =>
      ((base g : ℝ) : ℂ) ^ (1 + 2 * s))
    exact hpow
  have hcont : Continuous (sphC s) := by
    apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin 2) ℂ))).continuous_iff.mpr
    convert hsph using 1
    funext g
    exact sphC_mk s g
  exact ⟨by simpa [heq] using hf, hcont⟩

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
  have hn (x z : ℂ) : nC x * nC z = nC (x + z) := by
    have hmat : upperM ℂ x * upperM ℂ z = upperM ℂ (x + z) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    change ((upperM ℂ x : GL (Fin 2) ℂ) : PGL2 ℂ) *
        ((upperM ℂ z : GL (Fin 2) ℂ) : PGL2 ℂ) =
      ((upperM ℂ (x + z) : GL (Fin 2) ℂ) : PGL2 ℂ)
    rw [← QuotientGroup.mk_mul]
    exact congrArg (fun g : GL (Fin 2) ℂ => (g : PGL2 ℂ)) hmat
  have hpsiAdd (z w : ℂ) : psiC (z + w) = psiC z * psiC w := by
    unfold psiC
    have harg :
        -(4 * Real.pi * Complex.I * ((z + w).re : ℂ)) =
          -(4 * Real.pi * Complex.I * (z.re : ℂ)) +
            -(4 * Real.pi * Complex.I * (w.re : ℂ)) := by
      rw [Complex.add_re, Complex.ofReal_add]
      ring
    rw [harg, Complex.exp_add]
  have hpsi (z : ℂ) : psiC (u - z) = psiC u * psiC (-z) := by
    rw [show u - z = u + (-z) by ring, hpsiAdd]
  let H : ℂ → ℂ := fun z => psiC (u - z) * f (wC * nC z)
  have hMP : MeasurePreserving (MeasurableEquiv.addRight u) volume volume := by
    exact measurePreserving_add_right volume u
  calc
    jacquetC (rtr (nC u) f) = ∫ x : ℂ, H (MeasurableEquiv.addRight u x) := by
      simp [jacquetC, H, rtr, MeasurableEquiv.addRight, hn, mul_assoc] <;> ring
    _ = ∫ z : ℂ, H z := hMP.integral_comp
      (MeasurableEquiv.addRight u).measurableEmbedding H
    _ = ∫ z : ℂ, psiC u * (psiC (-z) * f (wC * nC z)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [H, hpsi z, mul_assoc]
    _ = psiC u * jacquetC f := by
      rw [integral_const_mul]
      rfl

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
