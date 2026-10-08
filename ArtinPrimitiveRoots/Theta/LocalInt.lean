import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Shared
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage

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

private theorem sphericalC_continuous (s : ℂ) : Continuous (sphericalC s) := by
  have hmk : Continuous (fun g : GL (Fin 2) ℂ =>
      (QuotientGroup.mk g : PGL2 ℂ)) :=
    (QuotientGroup.isQuotientMap_mk
      (Subgroup.center (GL (Fin 2) ℂ))).continuous
  have h := (sphC_isSection s).2.comp hmk
  convert h using 1
  funext g
  exact (sphC_mk s g).symm

/-- **def:jacquet-C**: `𝒥_ℂ f = ∫_ℂ ψ_w(-x) f(w n(x)) dx` (Lebesgue measure). -/
def jacquetC (f : PGL2 ℂ → ℂ) : ℂ := ∫ x : ℂ, psiC (-x) * f (wC * nC x)

/-- **def:intertwine-C**. -/
def intertwineC (f : PGL2 ℂ → ℂ) (g : PGL2 ℂ) : ℂ := ∫ x : ℂ, f (wC * nC x * g)

private theorem sphC_w_n_right_mk (s : ℂ) (g : GL (Fin 2) ℂ) (x : ℂ) :
    sphC s (wC * nC x * QuotientGroup.mk g) =
      (↑(‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
              x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
            ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
              x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) : ℂ) ^ (1 + 2 * s) := by
  have hq : wC * nC x * QuotientGroup.mk g =
      QuotientGroup.mk (weylM ℂ * upperM ℂ x * g) := by
    change (QuotientGroup.mk (weylM ℂ) * QuotientGroup.mk (upperM ℂ x)) *
      QuotientGroup.mk g = _
    simp only [QuotientGroup.mk_mul]
  rw [hq, sphC_mk]
  unfold sphericalC
  have hdet : ‖Matrix.det ((weylM ℂ * upperM ℂ x * g : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)‖ = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    change ‖((Matrix.GeneralLinearGroup.det (weylM ℂ * upperM ℂ x * g) : ℂˣ) : ℂ)‖ = _
    rw [map_mul, map_mul]
    simp [weylM, upperM]
  have hrow :
      ‖((weylM ℂ * upperM ℂ x * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖((weylM ℂ * upperM ℂ x * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
    simp [weylM, upperM, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hdet, hrow]

private theorem complex_complete_square (a b c d x : ℂ)
    (hA : Complex.normSq c + Complex.normSq d ≠ 0) :
    Complex.normSq (a + x * c) + Complex.normSq (b + x * d) =
      (Complex.normSq c + Complex.normSq d) *
          Complex.normSq (x + (a * star c + b * star d) /
            ((Complex.normSq c + Complex.normSq d : ℝ) : ℂ)) +
        (Complex.normSq (a * d - b * c)) /
          (Complex.normSq c + Complex.normSq d) := by
  let A : ℝ := Complex.normSq c + Complex.normSq d
  have hAcne : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa [A] using hA)
  have hAcomplex : (A : ℂ) = star c * c + star d * d := by
    simp [A, Complex.normSq_eq_conj_mul_self]
  have hcast :
      ((Complex.normSq (a + x * c) + Complex.normSq (b + x * d) : ℝ) : ℂ) =
        ((A * Complex.normSq (x + (a * star c + b * star d) / (A : ℂ)) +
          Complex.normSq (a * d - b * c) / A : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.normSq_eq_conj_mul_self]
    simp only [map_add, map_mul, map_sub, map_div₀, starRingEnd_apply, star_star,
      Complex.conj_ofReal]
    field_simp [hAcne]
    rw [hAcomplex]
    simp only [star_add, star_mul, star_star]
    ring_nf
  exact Complex.ofReal_injective hcast

private theorem integral_sphC_radial (s : ℂ) (hs : 0 < s.re) (r : ℝ) (hr : 0 < r) :
    (∫ x : ℂ, (((r / (r ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (1 + 2 * s))) =
      (Real.pi / (2 * s)) * (r : ℂ) ^ (1 - 2 * s) := by
  let lam : ℂ := 1 + 2 * s
  let H : ℂ → ℂ := fun z => OAI.CubicEisenstein.hyperbolicKernel lam z
  let F : ℂ → ℂ := fun z => (((r / (r ^ 2 + ‖z‖ ^ 2) : ℝ) : ℂ) ^ lam)
  have hlam : 1 < lam.re := by
    dsimp [lam]
    simp
    linarith
  have hD (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hnorm (z : ℂ) : ‖(r • z : ℂ)‖ = r * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hratio (z : ℂ) : r / (r ^ 2 + ‖r • z‖ ^ 2) =
      r⁻¹ * (1 + ‖z‖ ^ 2)⁻¹ := by
    rw [hnorm]
    field_simp [hr.ne']
  have hF (z : ℂ) : F (r • z) = (r : ℂ) ^ (-lam) * H z := by
    change (((r / (r ^ 2 + ‖r • z‖ ^ 2) : ℝ) : ℂ) ^ lam) = _
    rw [hratio z, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hr.le)
        (inv_nonneg.mpr (le_of_lt (hD z))) lam]
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hr.le,
      ← Complex.cpow_neg, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (le_of_lt (hD z)), ← Complex.cpow_neg]
    simp [H, OAI.CubicEisenstein.hyperbolicKernel, lam]
  have hscale : (∫ x : ℂ, F x) = (r ^ 2 : ℝ) • ∫ z : ℂ, F (r • z) := by
    have h := Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      (fun z : ℂ => F (r • z)) (R := r) hr.le
    simpa [Complex.finrank_real_complex, smul_smul, hr.ne'] using h
  have hscaled : (∫ z : ℂ, F (r • z)) = (r : ℂ) ^ (-lam) * ∫ z : ℂ, H z := by
    calc
      (∫ z : ℂ, F (r • z)) = ∫ z : ℂ, (r : ℂ) ^ (-lam) * H z := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hF z
      _ = _ := by rw [integral_const_mul]
  have hresult : (∫ x : ℂ, F x) =
      (r : ℂ) ^ (2 - lam) * ∫ z : ℂ, H z := by
    calc
      (∫ x : ℂ, F x) = (r ^ 2 : ℝ) • ∫ z : ℂ, F (r • z) := hscale
      _ = (r : ℂ) ^ (2 : ℂ) * ((r : ℂ) ^ (-lam) * ∫ z : ℂ, H z) := by
        rw [hscaled]
        simp [Complex.ofReal_pow, Complex.cpow_natCast]
      _ = _ := by
        rw [← mul_assoc]
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
        congr 2 <;> ring
  have hkernel := OAI.CubicEisenstein.integral_hyperbolicKernel lam hlam
  have hden : lam - 1 = 2 * s := by dsimp [lam]; ring
  have hexp : (2 : ℂ) - lam = 1 - 2 * s := by dsimp [lam]; ring
  calc
    (∫ x : ℂ, (((r / (r ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (1 + 2 * s))) =
        ∫ x : ℂ, F x := by simp [F, lam]
    _ = (r : ℂ) ^ (2 - lam) * ∫ z : ℂ, H z := hresult
    _ = (r : ℂ) ^ (1 - 2 * s) * (Real.pi : ℂ) / (2 * s) := by
      rw [hexp, hkernel, hden]
      ring
    _ = _ := by ring

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
private theorem besselCubic_eq_prebuilt (x : ℝ) (hx : 0 < x) :
    (besselK (1 / 3) x : ℂ) = OAI.CubicEisenstein.schlafliBesselK (1 / 3) x := by
  rw [besselK_eq_schlafli (1 / 3) x hx,
    OAI.CubicEisenstein.schlafliBesselK_cubic_real x hx]
  rw [show -(1 / 3 : ℝ) = -(1 : ℝ) / 3 by ring]
  congr 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [OAI.CubicEisenstein.cubicBesselDensity]
  congr 1
  congr 1
  ring

private theorem sphC_w_n_a (y : ℂˣ) (x : ℂ) :
    sphC (1 / 6) (wC * nC x * aC y) =
      ((‖(y : ℂ)‖ / (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ) := by
  have hprod : wC * nC x * aC y =
      QuotientGroup.mk (weylM ℂ * upperM ℂ x * diagM ℂ y) := by
    change (QuotientGroup.mk (weylM ℂ) * QuotientGroup.mk (upperM ℂ x)) *
        QuotientGroup.mk (diagM ℂ y) = _
    simp only [QuotientGroup.mk_mul]
  rw [hprod, sphC_mk]
  simp [sphericalC, weylM, upperM, diagM, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

private theorem psiC_neg_eq_breveE (z : ℂ) :
    psiC (-z) = OAI.ShortDraftTrace.breveE z := by
  change Complex.exp (-(4 * Real.pi * Complex.I * ((-z).re : ℂ))) =
    Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private def jacquetMatrixC (y : ℂˣ) (x : ℂ) : GL (Fin 2) ℂ :=
  weylM ℂ * upperM ℂ x * diagM ℂ y

private theorem jacquetMatrixC_mk (y : ℂˣ) (x : ℂ) :
    wC * nC x * aC y = QuotientGroup.mk (jacquetMatrixC y x) := by
  change (QuotientGroup.mk (weylM ℂ) * QuotientGroup.mk (upperM ℂ x)) *
      QuotientGroup.mk (diagM ℂ y) =
        QuotientGroup.mk (weylM ℂ * upperM ℂ x * diagM ℂ y)
  simp only [QuotientGroup.mk_mul]

private theorem nC_add (x z : ℂ) : nC x * nC z = nC (x + z) := by
  have hmat : upperM ℂ x * upperM ℂ z = upperM ℂ (x + z) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  change ((upperM ℂ x : GL (Fin 2) ℂ) : PGL2 ℂ) *
      ((upperM ℂ z : GL (Fin 2) ℂ) : PGL2 ℂ) =
    ((upperM ℂ (x + z) : GL (Fin 2) ℂ) : PGL2 ℂ)
  rw [← QuotientGroup.mk_mul]
  exact congrArg (fun A : GL (Fin 2) ℂ => (A : PGL2 ℂ)) hmat

private theorem aC_nC (y : ℂˣ) (z : ℂ) :
    aC y * nC z = nC ((y : ℂ) * z) * aC y := by
  have hmat : diagM ℂ y * upperM ℂ z =
      upperM ℂ ((y : ℂ) * z) * diagM ℂ y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, upperM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  change ((diagM ℂ y : GL (Fin 2) ℂ) : PGL2 ℂ) *
      ((upperM ℂ z : GL (Fin 2) ℂ) : PGL2 ℂ) =
    ((upperM ℂ ((y : ℂ) * z) : GL (Fin 2) ℂ) : PGL2 ℂ) *
      ((diagM ℂ y : GL (Fin 2) ℂ) : PGL2 ℂ)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg (fun A : GL (Fin 2) ℂ => (A : PGL2 ℂ)) hmat

private theorem continuous_upperM_complex : Continuous (upperM ℂ) := by
  have hval : Continuous (fun x : ℂ =>
      ((upperM ℂ x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change Continuous (fun x : ℂ => !![(1 : ℂ), x; 0, 1])
    fun_prop
  have hmul (x : ℂ) : upperM ℂ x * upperM ℂ (-x) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
  have hinv (x : ℂ) : (upperM ℂ x)⁻¹ = upperM ℂ (-x) :=
    inv_eq_of_mul_eq_one_right (hmul x)
  have hinv_cont : Continuous (fun x : ℂ =>
      (((upperM ℂ x)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : (fun x : ℂ =>
        (((upperM ℂ x)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun x => ((upperM ℂ (-x) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext x
      exact congrArg (fun g : GL (Fin 2) ℂ =>
        (g : Matrix (Fin 2) (Fin 2) ℂ)) (hinv x)
    rw [heq]
    exact hval.comp continuous_neg
  exact Units.continuous_iff.mpr ⟨hval, hinv_cont⟩

private theorem continuous_nC_complex : Continuous (nC : ℂ → PGL2 ℂ) := by
  unfold nC
  exact continuous_quotient_mk'.comp continuous_upperM_complex

theorem jacquetC_spherical (y : ℂˣ) :
    jacquetC (rtr (aC y) (sphC (1 / 6))) =
      ((besselConst * ‖(y : ℂ)‖ * besselK (1 / 3) (4 * Real.pi * ‖(y : ℂ)‖) : ℝ) : ℂ) := by
  let r : ℝ := ‖(y : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr y.ne_zero
  let F : ℂ → ℂ := fun x =>
    psiC (-x) * (((r / (r ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ))
  have hformula : jacquetC (rtr (aC y) (sphC (1 / 6))) = ∫ x : ℂ, F x := by
    simp only [jacquetC, rtr]
    apply integral_congr_ae
    filter_upwards [] with x
    change psiC (-x) * sphC (1 / 6) (wC * nC x * aC y) =
      psiC (-x) * (((r / (r ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ))
    rw [sphC_w_n_a]
  let H : ℂ → ℂ := fun z =>
    OAI.CubicEisenstein.hyperbolicKernel (4 / 3) z *
      OAI.ShortDraftTrace.breveE ((r : ℂ) * z)
  have hscale : (∫ x : ℂ, F x) = (r ^ 2 : ℝ) • ∫ z : ℂ, F (r • z) := by
    have h := Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      (fun z : ℂ => F (r • z)) (R := r) hr.le
    simpa [Complex.finrank_real_complex, smul_smul, hr.ne'] using h
  have hF (z : ℂ) : F (r • z) = ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * H z := by
    let D : ℝ := 1 + ‖z‖ ^ 2
    have hnorm : ‖r • z‖ = r * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
    have hratio : r / (r ^ 2 + ‖r • z‖ ^ 2) = 1 / (r * D) := by
      rw [hnorm]
      dsimp [D]
      field_simp <;> ring
    have hphase : psiC (-(r • z)) = OAI.ShortDraftTrace.breveE ((r : ℂ) * z) := by
      rw [show (r • z : ℂ) = (r : ℂ) * z by simp [smul_eq_mul]]
      exact psiC_neg_eq_breveE ((r : ℂ) * z)
    have hpow : (((1 / (r * D) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) =
        ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) *
          ((D : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) := by
      have hri : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
      have hDi : 0 ≤ D⁻¹ := inv_nonneg.mpr (by dsimp [D]; positivity)
      have hrpow : ((r⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) =
          ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
        calc
          ((r⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) =
              (((r⁻¹) ^ (4 / 3 : ℝ) : ℝ) : ℂ) :=
                by
                  simpa only [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by norm_num] using
                    (Complex.ofReal_cpow hri (4 / 3 : ℝ)).symm
          _ = ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
            congr 1
            rw [← Real.rpow_neg_eq_inv_rpow]
      have hDpow : ((D⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) =
          ((D : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) := by
        calc
          ((D⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) =
              (((D⁻¹) ^ (4 / 3 : ℝ) : ℝ) : ℂ) :=
                by
                  simpa only [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by norm_num] using
                    (Complex.ofReal_cpow hDi (4 / 3 : ℝ)).symm
          _ = ((D ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
            congr 1
            rw [← Real.rpow_neg_eq_inv_rpow]
          _ = ((D : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) :=
            by
              have h := Complex.ofReal_cpow hDnonneg (-(4 / 3 : ℝ))
              have hposExp : ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) := by norm_num
              rw [Complex.ofReal_neg, hposExp] at h
              exact h
      calc
        (((1 / (r * D) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) =
            ((r⁻¹ * D⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) := by
          congr 2
          field_simp <;> ring
        _ = ((r⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) * ((D⁻¹ : ℝ) : ℂ) ^ (4 / 3 : ℂ) := by
          rw [Complex.ofReal_mul]
          exact Complex.mul_cpow_ofReal_nonneg hri hDi _
        _ = ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) *
              ((D : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) := by
          rw [hrpow, hDpow]
    change psiC (-(r • z)) *
        (((r / (r ^ 2 + ‖r • z‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) = _
    rw [hphase, hratio, hpow]
    simp only [H, OAI.CubicEisenstein.hyperbolicKernel]
    ring
  have hscaled : (∫ z : ℂ, F (r • z)) =
      ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ∫ z : ℂ, H z := by
    calc
      (∫ z : ℂ, F (r • z)) =
          ∫ z : ℂ, ((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * H z := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact hF z
      _ = _ := by rw [integral_const_mul]
  have hresult : (∫ x : ℂ, F x) =
      ((r ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ∫ z : ℂ, H z := by
    calc
      (∫ x : ℂ, F x) = (r ^ 2 : ℝ) • ∫ z : ℂ, F (r • z) := hscale
      _ = (r ^ 2 : ℝ) •
          (((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ∫ z : ℂ, H z) := by rw [hscaled]
      _ = ((r ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ∫ z : ℂ, H z := by
        change ((r ^ 2 : ℝ) : ℂ) *
            (((r ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ∫ z : ℂ, H z) = _
        rw [← mul_assoc, ← Complex.ofReal_mul]
        apply congrArg (fun c : ℂ => c * ∫ z : ℂ, H z)
        have hp : r ^ 2 * r ^ (-(4 / 3 : ℝ)) = r ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
          norm_num
        exact congrArg (fun a : ℝ => (a : ℂ)) hp
  have hkernel : (∫ z : ℂ, H z) =
      OAI.CubicEisenstein.sourceFourierKernel (4 / 3) (-(r : ℂ)) := by
    simp [H, OAI.CubicEisenstein.sourceFourierKernel,
      OAI.CubicEisenstein.hyperbolicKernel, mul_assoc]
  have hfreq : (-(r : ℂ)) ≠ 0 := by
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hr.ne')
  have hOAI := OAI.CubicEisenstein.sourceFourierKernel_four_thirds (-(r : ℂ)) hfreq
  have harg : 0 < 4 * Real.pi * r := by positivity
  calc
    jacquetC (rtr (aC y) (sphC (1 / 6))) =
        ((r ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
          OAI.CubicEisenstein.sourceFourierKernel (4 / 3) (-(r : ℂ)) := by
      rw [hformula, hresult, hkernel]
    _ = ((besselConst * r * besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ) := by
      rw [hOAI, show ‖-(r : ℂ)‖ = r by simp [r, Real.norm_eq_abs, abs_of_pos hr],
        ← besselCubic_eq_prebuilt (4 * Real.pi * r) harg]
      have hbase : 2 * (Real.pi : ℂ) * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) := by
        push_cast
        ring
      let b : ℝ := 2 * Real.pi * r
      have hb : 0 < b := by dsimp [b]; positivity
      have hbase' : ((2 * Real.pi * r : ℝ) : ℂ) = (b : ℂ) := by rfl
      have hpowBase : ((b ^ (1 / 3 : ℝ) : ℝ) : ℂ) =
          (b : ℂ) ^ (1 / 3 : ℂ) := by
        simpa only [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by norm_num] using
          Complex.ofReal_cpow hb.le (1 / 3 : ℝ)
      have hGamma : Complex.Gamma (4 / 3 : ℂ) = (Real.Gamma (4 / 3 : ℝ) : ℂ) := by
        rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
      rw [hbase, hbase', ← hpowBase, hGamma]
      push_cast [besselConst]
      let p : ℝ := 2 * Real.pi
      have hpowB : b ^ (1 / 3 : ℝ) =
          p ^ (1 / 3 : ℝ) * r ^ (1 / 3 : ℝ) := by
        dsimp [b, p]
        rw [Real.mul_rpow (by positivity) hr.le]
      have hpowBC : ((b ^ (1 / 3 : ℝ) : ℝ) : ℂ) =
          ((p ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((r ^ (1 / 3 : ℝ) : ℝ) : ℂ) :=
        (congrArg (fun t : ℝ => (t : ℂ)) hpowB).trans (Complex.ofReal_mul _ _)
      rw [hpowBC]
      have hp : r ^ (2 / 3 : ℝ) * r ^ (1 / 3 : ℝ) = r := by
        rw [← Real.rpow_add hr]
        norm_num
      have hpC : ((r ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
          ((r ^ (1 / 3 : ℝ) : ℝ) : ℂ) = (r : ℂ) := by
        calc
          _ = ((r ^ (2 / 3 : ℝ) * r ^ (1 / 3 : ℝ) : ℝ) : ℂ) :=
            (Complex.ofReal_mul _ _).symm
          _ = (r : ℂ) := congrArg (fun t : ℝ => (t : ℂ)) hp
      calc
        _ = (2 * (Real.pi : ℂ) / ((Real.Gamma (4 / 3 : ℝ)) : ℂ)) *
              ((p ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
              (((r ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
                ((r ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
                (besselK (1 / 3) (4 * Real.pi * r) : ℂ)) := by ring
        _ = _ := by rw [hpC]; ring

private theorem sphC_bottom_norm_pos (g : GL (Fin 2) ℂ) :
    0 < Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  have hrow : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, M, h.1, h.2]
  rcases hrow with hc | hd
  · have hcpos : 0 < Complex.normSq (M 1 0) := Complex.normSq_pos.mpr hc
    have hdnonneg : 0 ≤ Complex.normSq (M 1 1) := Complex.normSq_nonneg _
    simpa [M] using add_pos_of_pos_of_nonneg hcpos hdnonneg
  · have hdpos : 0 < Complex.normSq (M 1 1) := Complex.normSq_pos.mpr hd
    have hcnonneg : 0 ≤ Complex.normSq (M 1 0) := Complex.normSq_nonneg _
    simpa [M, add_comm] using add_pos_of_pos_of_nonneg hdpos hcnonneg

private theorem sphC_right_n_mk (s : ℂ) (g : GL (Fin 2) ℂ) (x : ℂ) :
    sphC s (QuotientGroup.mk g * nC x) =
      (↑(‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
          ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * x +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) : ℂ) ^ (1 + 2 * s) := by
  have hq : QuotientGroup.mk g * nC x = QuotientGroup.mk (g * upperM ℂ x) := by
    change QuotientGroup.mk g * QuotientGroup.mk (upperM ℂ x) = _
    simp only [QuotientGroup.mk_mul]
  rw [hq, sphC_mk, sphericalC]
  have hdet : ‖Matrix.det ((g * upperM ℂ x : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)‖ = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    change ‖((Matrix.GeneralLinearGroup.det (g * upperM ℂ x) : ℂˣ) : ℂ)‖ = _
    rw [map_mul]
    simp [upperM]
  have hrow :
      ‖((g * upperM ℂ x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖((g * upperM ℂ x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * x +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
    simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hdet, hrow]

private theorem sphC_right_n_fderiv (s : ℂ) (g : GL (Fin 2) ℂ) (v : ℂ) :
    fderiv ℝ (fun z : ℂ => sphC s (QuotientGroup.mk g * nC z)) 0 v =
      -((1 + 2 * s) / ((Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ)) *
        sphericalC s g *
        ((2 * (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * v *
          star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ) := by
  let c : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let d : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  let B : ℝ := Complex.normSq c + Complex.normSq d
  let N : ℝ := ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
  let lam : ℂ := 1 + 2 * s
  let D : ℂ → ℝ := fun z => ‖c‖ ^ 2 + ‖z * c + d‖ ^ 2
  let R : ℂ → ℝ := fun z => N / D z
  let H : ℂ → ℂ := fun z => ((R z : ℝ) : ℂ) ^ lam
  have hBpos : 0 < B := by
    simpa [B, c, d] using sphC_bottom_norm_pos g
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hNpos : 0 < N := by
    dsimp [N]
    exact norm_pos_iff.mpr g.det_ne_zero
  have hD0 : D 0 = B := by
    simp [D, B, c, d, Complex.normSq_eq_norm_sq]
  have hR0 : R 0 = N / B := by simp [R, hD0]
  have hR0pos : 0 < R 0 := by rw [hR0]; exact div_pos hNpos hBpos
  have hf (z : ℂ) : sphC s (QuotientGroup.mk g * nC z) = H z := by
    rw [sphC_right_n_mk]
    simpa [H, R, D, N, c, d, lam, Complex.normSq_eq_norm_sq, mul_comm]
  have hfun : (fun z : ℂ => sphC s (QuotientGroup.mk g * nC z)) = H := by
    funext z
    exact hf z
  rw [hfun]
  by_cases hlamzero : lam = 0
  · have hconst : H = fun _ : ℂ => 1 := by
      funext z
      dsimp [H]
      rw [hlamzero, Complex.cpow_zero]
    rw [hconst]
    rw [show (1 : ℂ) + 2 * s = 0 by simpa [lam] using hlamzero]
    simp
  · have hlamne : lam ≠ 0 := hlamzero
    have haff : DifferentiableAt ℝ (fun z : ℂ => z * c + d) 0 := by fun_prop
    have hDdiff : DifferentiableAt ℝ D 0 := by
      unfold D
      exact (DifferentiableAt.norm_sq (𝕜 := ℂ) haff).const_add (‖c‖ ^ 2)
    have hD0ne : D 0 ≠ 0 := by rw [hD0]; exact hBne
    have hRdiff : DifferentiableAt ℝ R 0 := by
      unfold R
      fun_prop (disch := aesop)
    have hQ : DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ lam) (R 0) :=
      (hasDerivAt_ofReal_cpow_const (ne_of_gt hR0pos) hlamne).differentiableAt
    have hHdiff : DifferentiableAt ℝ H 0 := by
      change DifferentiableAt ℝ ((fun x : ℝ => (x : ℂ) ^ lam) ∘ R) 0
      exact hQ.comp 0 hRdiff
    have hv : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hcomp : HasDerivAt (fun t : ℝ => H (t • v)) (fderiv ℝ H 0 v) 0 :=
      hHdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hv (by simp)
    have hlin : HasDerivAt (fun t : ℝ => (t • v) * c + d) (v * c) 0 := by
      simpa using (hv.mul_const c).add_const d
    have hdenLine : HasDerivAt (fun t : ℝ => D (t • v))
        (2 * (v * c * star d).re) 0 := by
      simpa [D, Complex.inner] using hlin.norm_sq.const_add (‖c‖ ^ 2)
    have hRLine := (hasDerivAt_const (0 : ℝ) N).div hdenLine
      (by simpa [hD0] using hBne)
    have hbaseEq : R 0 = (fun t : ℝ => N / D (t • v)) 0 := by simp [R, hD0]
    have hpow := HasDerivAt.scomp_of_eq (𝕜 := ℝ) (x := (0 : ℝ))
      (hg := hasDerivAt_ofReal_cpow_const (ne_of_gt hR0pos) hlamne)
      (hh := hRLine) (hy := hbaseEq)
    have hpath : (fun t : ℝ => H (t • v)) =
        (fun t : ℝ => ((N / D (t • v) : ℝ) : ℂ) ^ lam) := by
      funext t
      simp [H, R]
    have hcompPowFun : (fun t : ℝ => H (t • v)) =
        ((fun y : ℝ => (y : ℂ) ^ lam) ∘
          ((fun _ : ℝ => N) / fun t : ℝ => D (t • v))) := by
      funext t
      simp [H, R]
    have hderiv : fderiv ℝ H 0 v =
        ((0 * B - N * (2 * (v * c * star d).re)) / B ^ 2 : ℝ) •
          (lam * ((R 0 : ℝ) : ℂ) ^ (lam - 1)) := by
      calc
        fderiv ℝ H 0 v = deriv (fun t : ℝ => H (t • v)) 0 := by
          simpa using hcomp.deriv.symm
      _ = deriv ((fun y : ℝ => (y : ℂ) ^ lam) ∘
            ((fun _ : ℝ => N) / fun t : ℝ => D (t • v))) 0 :=
        congrArg (fun f : ℝ → ℂ => deriv f 0) hcompPowFun
      _ = _ := by
        have h := hpow.deriv
        rw [zero_smul, hD0] at h
        exact h
    have hderiv' : fderiv ℝ H 0 v =
        lam * ((R 0 : ℝ) : ℂ) ^ (lam - 1) *
          ((0 * B - N * (2 * (v * c * star d).re)) / B ^ 2 : ℝ) := by
      rw [hderiv]
      calc
        _ = (((0 * B - N * (2 * (v * c * star d).re)) / B ^ 2 : ℝ) : ℂ) *
              (lam * ((R 0 : ℝ) : ℂ) ^ (lam - 1)) :=
          RCLike.real_smul_eq_coe_mul _ _
        _ = _ := by ring
    have hpowMul : ((R 0 : ℝ) : ℂ) ^ (lam - 1) * ((R 0 : ℝ) : ℂ) =
        ((R 0 : ℝ) : ℂ) ^ lam := by
      calc
        _ = ((R 0 : ℝ) : ℂ) ^ (lam - 1) * ((R 0 : ℝ) : ℂ) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
        _ = ((R 0 : ℝ) : ℂ) ^ ((lam - 1) + 1) := by
          rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hR0pos.ne')]
        _ = _ := by congr 1; ring
    have hscalar :
        lam * ((R 0 : ℝ) : ℂ) ^ (lam - 1) *
            ((0 * B - N * (2 * (v * c * star d).re)) / B ^ 2 : ℝ) =
        -(lam / (B : ℂ)) * sphericalC s g *
          ((2 * (v * c * star d).re : ℝ) : ℂ) := by
      let delta : ℝ := 2 * (v * c * star d).re
      have hreal : (0 * B - N * delta) / B ^ 2 = (-R 0 / B) * delta := by
        rw [hR0]
        field_simp [hBne]
        ring
      have hrealC : (((0 * B - N * delta) / B ^ 2 : ℝ) : ℂ) =
          -((R 0 : ℝ) : ℂ) / (B : ℂ) * (delta : ℂ) := by
        have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
        simpa [Complex.ofReal_div, Complex.ofReal_mul] using hc
      have hsph : sphericalC s g = ((R 0 : ℝ) : ℂ) ^ lam := by
        rw [hR0]
        unfold sphericalC
        dsimp [N, B, c, d]
        simp only [Complex.normSq_eq_norm_sq]
        rfl
      rw [hrealC, hsph]
      calc
        _ = -(lam / (B : ℂ)) *
              (((R 0 : ℝ) : ℂ) ^ (lam - 1) * ((R 0 : ℝ) : ℂ)) * (delta : ℂ) := by ring
        _ = _ := by rw [hpowMul]
    change fderiv ℝ H 0 v = _
    rw [hderiv', hscalar]
    simp only [B, c, d, lam]
    rw [mul_comm v ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)]

private theorem derivVecC_spherical_mk (m : ℤ) (s : ℂ) (g : GL (Fin 2) ℂ) :
    derivVecC m (sphC s) (QuotientGroup.mk g) =
      -(2 * (1 + 2 * s) /
          ((Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
            Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ)) *
        sphericalC s g *
          (Complex.ofReal (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
              star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re +
            (m : ℂ) * Complex.I * Complex.ofReal ((((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
              star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).im)) := by
  let c : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let d : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  let B : ℝ := Complex.normSq c + Complex.normSq d
  let z : ℂ := c * star d
  let lam : ℂ := 1 + 2 * s
  have hzI : (Complex.I * c * star d).re = -z.im := by
    rw [mul_assoc]
    simpa [z] using (RCLike.I_mul_re (z := c * star d))
  have h1' : fderiv ℝ (fun w : ℂ => sphC s (QuotientGroup.mk g * nC w)) 0 1 =
      -(lam / (B : ℂ)) * sphericalC s g * ((2 * z.re : ℝ) : ℂ) := by
    simpa [B, c, d, z, lam, one_mul] using sphC_right_n_fderiv s g 1
  have hI' : fderiv ℝ (fun w : ℂ => sphC s (QuotientGroup.mk g * nC w)) 0 Complex.I =
      -(lam / (B : ℂ)) * sphericalC s g * ((-2 * z.im : ℝ) : ℂ) := by
    have hI0 : fderiv ℝ (fun w : ℂ => sphC s (QuotientGroup.mk g * nC w)) 0 Complex.I =
        -(lam / (B : ℂ)) * sphericalC s g *
          ((2 * (Complex.I * c * star d).re : ℝ) : ℂ) := by
      simpa [B, c, d, lam] using sphC_right_n_fderiv s g Complex.I
    calc
      _ = -(lam / (B : ℂ)) * sphericalC s g *
            ((2 * (Complex.I * c * star d).re : ℝ) : ℂ) := hI0
      _ = _ := by rw [hzI]; push_cast; ring
  unfold derivVecC
  rw [h1', hI']
  change -(lam / (B : ℂ)) * sphericalC s g * ((2 * z.re : ℝ) : ℂ) -
      (m : ℂ) * Complex.I *
        (-(lam / (B : ℂ)) * sphericalC s g * ((-2 * z.im : ℝ) : ℂ)) =
      -(2 * lam / (B : ℂ)) * sphericalC s g *
        (Complex.ofReal z.re + (m : ℂ) * Complex.I * Complex.ofReal z.im)
  push_cast
  ring_nf

private theorem sphC_right_n_differentiableAt (g : GL (Fin 2) ℂ) (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ =>
      sphC (1 / 6) (QuotientGroup.mk g * nC w)) z := by
  let N : ℝ := ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
  let c : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let d : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  let D : ℂ → ℝ := fun w => ‖c‖ ^ 2 + ‖c * w + d‖ ^ 2
  let R : ℂ → ℝ := fun w => N / D w
  have hNpos : 0 < N := by
    dsimp [N]
    exact norm_pos_iff.mpr g.det_ne_zero
  have hDpos (w : ℂ) : 0 < D w := by
    have h := sphC_bottom_norm_pos (g * upperM ℂ w)
    simpa [D, c, d, upperM, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.normSq_eq_norm_sq] using h
  have hRpos (w : ℂ) : 0 < R w := div_pos hNpos (hDpos w)
  have haff : DifferentiableAt ℝ (fun w : ℂ => c * w + d) z := by
    fun_prop
  have hDdiff : DifferentiableAt ℝ D z := by
    unfold D
    exact (DifferentiableAt.norm_sq (𝕜 := ℂ) haff).const_add (‖c‖ ^ 2)
  have hInvR : DifferentiableAt ℝ (fun t : ℝ => t⁻¹) (D z) :=
    (differentiableAt_inv_iff).2 (ne_of_gt (hDpos z))
  have hInv : DifferentiableAt ℝ (fun w : ℂ => (D w)⁻¹) z :=
    hInvR.comp z hDdiff
  have hRdiff : DifferentiableAt ℝ R z := by
    simpa [R, div_eq_mul_inv] using hInv.const_mul N
  have hQ : DifferentiableAt ℝ (fun r : ℝ =>
      ((r : ℝ) : ℂ) ^ (4 / 3 : ℂ)) (R z) :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt (hRpos z)) (by norm_num)).differentiableAt
  have hcomp := hQ.comp z hRdiff
  have heq : (fun w : ℂ => sphC (1 / 6) (QuotientGroup.mk g * nC w)) =
      fun w => ((R w : ℝ) : ℂ) ^ (4 / 3 : ℂ) := by
    funext w
    rw [sphC_right_n_mk]
    simp [R, D, N, c, d]
    norm_num
  rw [heq]
  change DifferentiableAt ℝ ((fun r : ℝ =>
    ((r : ℝ) : ℂ) ^ (4 / 3 : ℂ)) ∘ R) z
  exact hcomp

private theorem sphC_right_n_fderiv_at (s : ℂ) (g : GL (Fin 2) ℂ)
    (u v : ℂ) :
    fderiv ℝ (fun z : ℂ => sphC s (QuotientGroup.mk g * nC z)) u v =
      fderiv ℝ (fun z : ℂ =>
        sphC s (QuotientGroup.mk (g * upperM ℂ u) * nC z)) 0 v := by
  have hn (a b : ℂ) : nC a * nC b = nC (a + b) := by
    have hmat : upperM ℂ a * upperM ℂ b = upperM ℂ (a + b) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    change ((upperM ℂ a : GL (Fin 2) ℂ) : PGL2 ℂ) *
        ((upperM ℂ b : GL (Fin 2) ℂ) : PGL2 ℂ) =
      ((upperM ℂ (a + b) : GL (Fin 2) ℂ) : PGL2 ℂ)
    rw [← QuotientGroup.mk_mul]
    exact congrArg (fun A : GL (Fin 2) ℂ => (A : PGL2 ℂ)) hmat
  have hG : QuotientGroup.mk g * nC u = QuotientGroup.mk (g * upperM ℂ u) := by
    change (g : PGL2 ℂ) * ((upperM ℂ u : GL (Fin 2) ℂ) : PGL2 ℂ) =
      ((g * upperM ℂ u : GL (Fin 2) ℂ) : PGL2 ℂ)
    rw [← QuotientGroup.mk_mul]
  let h : ℂ → ℂ := fun z => sphC s (QuotientGroup.mk g * nC z)
  have hshift : (fun z : ℂ =>
      sphC s ((QuotientGroup.mk g * nC u) * nC z)) =
      fun z => h (z + u) := by
    funext z
    dsimp [h]
    calc
      sphC s ((QuotientGroup.mk g * nC u) * nC z) =
          sphC s (QuotientGroup.mk g * (nC u * nC z)) := by rw [mul_assoc]
      _ = sphC s (QuotientGroup.mk g * nC (u + z)) := by rw [hn]
      _ = sphC s (QuotientGroup.mk g * nC (z + u)) := by rw [add_comm]
  have hGfunc : (fun z : ℂ =>
      sphC s ((QuotientGroup.mk g * nC u) * nC z)) =
      fun z => sphC s (QuotientGroup.mk (g * upperM ℂ u) * nC z) := by
    funext z
    rw [hG]
  have hfd : fderiv ℝ h u = fderiv ℝ (fun z => h (z + u)) 0 := by
    simpa using (fderiv_comp_add_right (𝕜 := ℝ) (f := h) (x := (0 : ℂ)) u).symm
  calc
    fderiv ℝ h u v = fderiv ℝ (fun z => h (z + u)) 0 v :=
      congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hfd
    _ = fderiv ℝ (fun z : ℂ =>
          sphC s ((QuotientGroup.mk g * nC u) * nC z)) 0 v := by
      exact congrArg (fun f : ℂ → ℂ => fderiv ℝ f 0 v) hshift.symm
    _ = fderiv ℝ (fun z : ℂ =>
          sphC s (QuotientGroup.mk (g * upperM ℂ u) * nC z)) 0 v := by
      exact congrArg (fun f : ℂ → ℂ => fderiv ℝ f 0 v) hGfunc

private def jacquetKernelC (y : ℂˣ) (v : ℂ) (t : ℝ) (x : ℂ) : ℂ :=
  psiC (-x) * sphC (1 / 6) (wC * nC x * aC y * nC ((t : ℝ) • v))

private theorem jacquetKernelC_continuous (y : ℂˣ) (v : ℂ) (t : ℝ) :
    Continuous (jacquetKernelC y v t) := by
  have hnCcont : Continuous nC := continuous_nC_complex
  have harg : Continuous (fun x : ℂ =>
      wC * nC x * aC y * nC ((t : ℝ) • v)) := by
    fun_prop
  have hphase : Continuous fun x : ℂ => psiC (-x) := by
    unfold psiC
    fun_prop
  change Continuous fun x : ℂ =>
    psiC (-x) * sphC (1 / 6) (wC * nC x * aC y * nC ((t : ℝ) • v))
  exact hphase.mul ((sphC_isSection (1 / 6)).2.comp harg)

private def jacquetKernelC_deriv (y : ℂˣ) (v : ℂ) (t : ℝ) (x : ℂ) : ℂ :=
  let G : GL (Fin 2) ℂ := jacquetMatrixC y x
  let G' : GL (Fin 2) ℂ := G * upperM ℂ ((t : ℝ) • v)
  psiC (-x) *
    (-((4 / 3 : ℂ) /
        ((Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ))) *
    sphericalC (1 / 6) G' *
      ((2 * (v * (G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
        star ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ)

private theorem jacquetKernelC_deriv_continuous (y : ℂˣ) (v : ℂ) (t : ℝ) :
    Continuous (jacquetKernelC_deriv y v t) := by
  let G : ℂ → GL (Fin 2) ℂ := fun x =>
    jacquetMatrixC y x * upperM ℂ ((t : ℝ) • v)
  let B : ℂ → ℝ := fun x =>
    Complex.normSq ((G x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      Complex.normSq ((G x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  have hU : Continuous (upperM ℂ) := continuous_upperM_complex
  have hG : Continuous G := by
    dsimp [G, jacquetMatrixC]
    fun_prop
  have hB : Continuous B := by
    dsimp [B]
    fun_prop
  have hBpos (x : ℂ) : 0 < B x := by
    simpa [B, G] using sphC_bottom_norm_pos (G x)
  have hBne (x : ℂ) : (B x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hBpos x))
  have hcoef : Continuous fun x : ℂ =>
      -((4 / 3 : ℂ) / (B x : ℂ)) := by
    exact (continuous_const.div (Complex.continuous_ofReal.comp hB) hBne).neg
  have hsph : Continuous fun x : ℂ => sphericalC (1 / 6) (G x) :=
    (sphericalC_continuous (1 / 6)).comp hG
  have hdir : Continuous fun x : ℂ =>
      ((2 * (v * (G x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
        star ((G x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ) := by
    fun_prop
  have hphase : Continuous fun x : ℂ => psiC (-x) := by
    unfold psiC
    fun_prop
  change Continuous fun x : ℂ =>
    psiC (-x) * (-((4 / 3 : ℂ) / (B x : ℂ))) *
      sphericalC (1 / 6) (G x) *
        ((2 * (v * (G x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
          star ((G x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ)
  exact ((hphase.mul hcoef).mul hsph).mul hdir

private theorem jacquetKernelC_hasDerivAt (y : ℂˣ) (v : ℂ) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun t' : ℝ => jacquetKernelC y v t' x)
      (jacquetKernelC_deriv y v t x) t := by
  let u : ℂ := (t : ℝ) • v
  let G : GL (Fin 2) ℂ := jacquetMatrixC y x
  let G' : GL (Fin 2) ℂ := G * upperM ℂ u
  have hq : wC * nC x * aC y = QuotientGroup.mk G := by
    simpa [G, jacquetMatrixC] using jacquetMatrixC_mk y x
  let h : ℂ → ℂ := fun z => sphC (1 / 6) (QuotientGroup.mk G * nC z)
  have hdiff : DifferentiableAt ℝ h u := sphC_right_n_differentiableAt G u
  have hv : HasDerivAt (fun t' : ℝ => (t' : ℝ) • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hcomp : HasDerivAt (fun t' : ℝ => h ((t' : ℝ) • v))
      (fderiv ℝ h u v) t :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq t hv (by simp [u])
  have hfd : fderiv ℝ h u v =
      -((4 / 3 : ℂ) /
        ((Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ)) *
        sphericalC (1 / 6) G' *
          ((2 * (v * (G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
            star ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ) := by
    rw [sphC_right_n_fderiv_at]
    have hbase := sphC_right_n_fderiv (1 / 6) G' v
    change fderiv ℝ (fun z : ℂ =>
      sphC (1 / 6) (QuotientGroup.mk (G * upperM ℂ u) * nC z)) 0 v = _ at hbase
    have hcomm :
        (((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * v *
          star ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re =
        (v * ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
          star ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re := by
      congr 1
      ring
    rw [hcomm] at hbase
    rw [show (1 : ℂ) + 2 * (1 / 6 : ℂ) = (4 / 3 : ℂ) by norm_num] at hbase
    exact hbase
  have hcomp' := hcomp.const_mul (psiC (-x))
  have hfun : (fun t' : ℝ => jacquetKernelC y v t' x) =
      fun t' => psiC (-x) * h ((t' : ℝ) • v) := by
    funext t'
    simp [jacquetKernelC, h, hq]
  have hval : jacquetKernelC_deriv y v t x =
      psiC (-x) * fderiv ℝ h u v := by
    change psiC (-x) *
        (-((4 / 3 : ℂ) /
          ((Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
            Complex.normSq ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ))) *
          sphericalC (1 / 6) G' *
            ((2 * (v * (G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
              star ((G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ) =
      psiC (-x) * fderiv ℝ h u v
    rw [hfd]
    ring
  rw [hfun, hval]
  exact hcomp'

private theorem jacquetMatrixC_bottom (y : ℂˣ) (x u : ℂ) :
    ((jacquetMatrixC y x * upperM ℂ u : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
        (y : ℂ) ∧
      ((jacquetMatrixC y x * upperM ℂ u : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
        x + (y : ℂ) * u := by
  constructor
  · simp [jacquetMatrixC, weylM, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [jacquetMatrixC, weylM, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem jacquetMatrixC_spherical (y : ℂˣ) (x u : ℂ) :
    sphericalC (1 / 6) (jacquetMatrixC y x * upperM ℂ u) =
      ((‖(y : ℂ)‖ / (‖(y : ℂ)‖ ^ 2 + ‖x + (y : ℂ) * u‖ ^ 2) : ℝ) : ℂ) ^
        (4 / 3 : ℂ) := by
  let G : GL (Fin 2) ℂ := jacquetMatrixC y x
  let G' : GL (Fin 2) ℂ := G * upperM ℂ u
  have hq : wC * nC x * aC y = QuotientGroup.mk G := by
    simpa [G, jacquetMatrixC] using jacquetMatrixC_mk y x
  have hroot : (wC * nC x * aC y) * nC u =
      wC * nC (x + (y : ℂ) * u) * aC y := by
    calc
      (wC * nC x * aC y) * nC u =
          wC * nC x * (aC y * nC u) := by rw [mul_assoc]
      _ = wC * nC x * (nC ((y : ℂ) * u) * aC y) := by rw [aC_nC]
      _ = wC * (nC x * nC ((y : ℂ) * u)) * aC y := by simp [mul_assoc]
      _ = wC * nC (x + (y : ℂ) * u) * aC y := by rw [nC_add]
  have hmul : QuotientGroup.mk G * nC u = QuotientGroup.mk G' := by
    change (G : PGL2 ℂ) * ((upperM ℂ u : GL (Fin 2) ℂ) : PGL2 ℂ) =
      ((G * upperM ℂ u : GL (Fin 2) ℂ) : PGL2 ℂ)
    rw [← QuotientGroup.mk_mul]
  have hG' : QuotientGroup.mk G' = wC * nC (x + (y : ℂ) * u) * aC y := by
    calc
      QuotientGroup.mk G' = QuotientGroup.mk G * nC u := hmul.symm
      _ = (wC * nC x * aC y) * nC u := by rw [hq]
      _ = _ := hroot
  calc
    sphericalC (1 / 6) (jacquetMatrixC y x * upperM ℂ u) =
        sphericalC (1 / 6) G' := by rfl
    _ = sphC (1 / 6) (QuotientGroup.mk G') := (sphC_mk (1 / 6) G').symm
    _ = sphC (1 / 6) (wC * nC (x + (y : ℂ) * u) * aC y) :=
      congrArg (sphC (1 / 6)) hG'
    _ = _ := sphC_w_n_a y (x + (y : ℂ) * u)

private def jacquetKernelC_majorantConst (y : ℂˣ) : ℝ :=
  let r : ℝ := ‖(y : ℂ)‖
  let c : ℝ := (min (r ^ 2) 1) / (3 + 2 * r ^ 2)
  2 * (4 / 3 : ℝ) * r * (r / c) ^ (4 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ))

private theorem jacquetKernelC_deriv_bound (y : ℂˣ) (v : ℂ) (t : ℝ) (x : ℂ)
    (hv : ‖v‖ = 1) (ht : t ∈ Metric.ball (0 : ℝ) 1) :
    ‖jacquetKernelC_deriv y v t x‖ ≤
      jacquetKernelC_majorantConst y *
        ‖OAI.CubicEisenstein.hyperbolicKernel (11 / 6) x‖ := by
  let r : ℝ := ‖(y : ℂ)‖
  let u : ℂ := (t : ℝ) • v
  let d : ℂ := x + (y : ℂ) * u
  let D : ℝ := r ^ 2 + ‖d‖ ^ 2
  let q : ℝ := ‖x‖ ^ 2
  let c : ℝ := (min (r ^ 2) 1) / (3 + 2 * r ^ 2)
  let p : ℝ := 4 / 3
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr y.ne_zero
  have ht' : ‖t‖ < 1 := by
    simpa [Metric.mem_ball] using ht
  have hu : ‖u‖ ≤ 1 := by
    calc
      ‖u‖ = ‖(t : ℝ)‖ * ‖v‖ := by simp [u, norm_smul]
      _ = ‖t‖ := by rw [hv]; simp
      _ ≤ 1 := ht'.le
  have hyu : ‖(y : ℂ) * u‖ ≤ r := by
    calc
      ‖(y : ℂ) * u‖ = ‖(y : ℂ)‖ * ‖u‖ := norm_mul _ _
      _ = r * ‖u‖ := by rfl
      _ ≤ r := by nlinarith [hu]
  have hxle : ‖x‖ ≤ ‖d‖ + r := by
    have hx : x = d - (y : ℂ) * u := by
      dsimp [d]
      ring
    rw [hx]
    exact (norm_sub_le _ _).trans (by nlinarith [hyu])
  have hxq : q ≤ 2 * ‖d‖ ^ 2 + 2 * r ^ 2 := by
    dsimp [q]
    have hsq : ‖x‖ ^ 2 ≤ (‖d‖ + r) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hr.le)).2 hxle
    nlinarith [hsq, sq_nonneg (‖d‖ - r)]
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDlower : c * (1 + q) ≤ D := by
    have hA : 0 < min (r ^ 2) 1 := lt_min (sq_pos_of_pos hr) zero_lt_one
    have hA1 : min (r ^ 2) 1 ≤ 1 := min_le_right _ _
    have hA2 : min (r ^ 2) 1 ≤ r ^ 2 := min_le_left _ _
    have hDaux : min (r ^ 2) 1 * (1 + ‖d‖ ^ 2) ≤ D := by
      dsimp [D]
      nlinarith [mul_nonneg (sq_nonneg ‖d‖) (sub_nonneg.mpr hA1), hA2]
    have haux : 1 + q ≤ (3 + 2 * r ^ 2) * (1 + ‖d‖ ^ 2) := by
      dsimp [q]
      nlinarith [hxq, sq_nonneg ‖d‖]
    calc
      c * (1 + q) ≤ c * ((3 + 2 * r ^ 2) * (1 + ‖d‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left haux (le_of_lt hcpos)
      _ = min (r ^ 2) 1 * (1 + ‖d‖ ^ 2) := by
        dsimp [c]
        field_simp
      _ ≤ D := hDaux
  have hbasele : r / D ≤ (r / c) / (1 + q) := by
    have hright : 0 < c * (1 + q) := mul_pos hcpos (by positivity)
    rw [div_div]
    apply (div_le_div_iff₀ hDpos hright).2
    have hmul := mul_le_mul_of_nonneg_left hDlower hr.le
    nlinarith [hmul]
  have hbasepow : (r / D) ^ p ≤ (r / c) ^ p * (1 + q) ^ (-p) := by
    calc
      (r / D) ^ p ≤ ((r / c) / (1 + q)) ^ p :=
        Real.rpow_le_rpow (by positivity) hbasele (by norm_num [p])
      _ = (r / c) ^ p * (1 + q) ^ (-p) := by
        rw [Real.div_rpow (by positivity) (by positivity)]
        change (r / c) ^ p * ((1 + q) ^ p)⁻¹ = _
        rw [← Real.rpow_neg (by positivity) p]
  have hdsq : ‖d‖ ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg r]
  have hdroot : ‖d‖ ≤ Real.sqrt D := by
    have h := Real.sqrt_le_sqrt hdsq
    simpa [Real.sqrt_sq (norm_nonneg d)] using h
  have hrootdiv : Real.sqrt D / D = D ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hDpos]
    norm_num
  have hdirpow : ‖d‖ / D ≤ D ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖d‖ / D ≤ Real.sqrt D / D := div_le_div_of_nonneg_right hdroot (le_of_lt hDpos)
      _ = _ := hrootdiv
  have hdirpow' : ‖d‖ / D ≤ c ^ (-(1 / 2 : ℝ)) * (1 + q) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖d‖ / D ≤ (c * (1 + q)) ^ (-(1 / 2 : ℝ)) :=
        hdirpow.trans (Real.rpow_le_rpow_of_nonpos (by positivity) hDlower (by norm_num))
      _ = _ := by
        rw [Real.mul_rpow (le_of_lt hcpos) (by positivity)]
  have hphase : ‖psiC (-x)‖ = 1 := by
    rw [psiC_neg_eq_breveE, OAI.CubicEisenstein.breveE_norm]
  have hden : 0 < r ^ 2 + ‖d‖ ^ 2 := by positivity
  have hrows := jacquetMatrixC_bottom y x ((t : ℝ) • v)
  have hcM :
      (((jacquetMatrixC y x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((upperM ℂ ((t : ℂ) * v) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 =
        (y : ℂ) := by
    simpa [smul_eq_mul] using hrows.1
  have hdM :
      (((jacquetMatrixC y x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((upperM ℂ ((t : ℂ) * v) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 =
        d := by
    simpa [smul_eq_mul, d, u] using hrows.2
  have hkernelval : jacquetKernelC_deriv y v t x =
      psiC (-x) * (-((4 / 3 : ℂ) / ((r ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ))) *
        (((r / (r ^ 2 + ‖d‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) *
          ((2 * (v * (y : ℂ) * star d).re : ℝ) : ℂ) := by
    dsimp [jacquetKernelC_deriv]
    rw [hcM, hdM]
    have hsph : sphericalC (1 / 6)
        (jacquetMatrixC y x * upperM ℂ ((t : ℂ) * v)) =
        (((r / (r ^ 2 + ‖d‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) := by
      simpa [smul_eq_mul, r, D, d, u, Complex.normSq_eq_norm_sq] using
        jacquetMatrixC_spherical y x ((t : ℝ) • v)
    rw [hsph]
    simp [smul_eq_mul, r, D, d, u, Complex.normSq_eq_norm_sq]
  have hcoefnorm :
      ‖-((4 / 3 : ℂ) / ((r ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ))‖ =
        (4 / 3 : ℝ) / (r ^ 2 + ‖d‖ ^ 2) := by
    have hnum : ‖(4 / 3 : ℂ)‖ = (4 / 3 : ℝ) := by norm_num
    have hdennorm :
        ‖((r ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ)‖ = |r ^ 2 + ‖d‖ ^ 2| :=
      RCLike.norm_ofReal _
    calc
      _ = ‖(4 / 3 : ℂ)‖ / ‖((r ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ)‖ := by rw [norm_neg, norm_div]
      _ = _ := by rw [hnum, hdennorm, abs_of_pos hden]
  have hsphnorm :
      ‖(((r / (r ^ 2 + ‖d‖ ^ 2 : ℝ) : ℝ) : ℂ) ^ (4 / 3 : ℂ))‖ =
        (r / (r ^ 2 + ‖d‖ ^ 2)) ^ p := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hr hden)]
    norm_num [p]
  have hdirnorm :
      ‖((2 * (v * (y : ℂ) * star d).re : ℝ) : ℂ)‖ ≤ 2 * r * ‖d‖ := by
    calc
      ‖((2 * (v * (y : ℂ) * star d).re : ℝ) : ℂ)‖ =
          |2 * (v * (y : ℂ) * star d).re| := RCLike.norm_ofReal _
      _ =
          2 * |(v * (y : ℂ) * star d).re| := by rw [abs_mul, abs_of_pos (by norm_num)]
      _ ≤ 2 * ‖v * (y : ℂ) * star d‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ = 2 * r * ‖d‖ := by simp [norm_mul, norm_star, hv, r, mul_assoc]
  have hrough :
      ‖jacquetKernelC_deriv y v t x‖ ≤
        2 * (4 / 3 : ℝ) * r * (r / D) ^ p * (‖d‖ / D) := by
    have hleft : 0 ≤ ((4 / 3 : ℝ) / D) * (r / D) ^ p := by positivity
    calc
      _ = ((4 / 3 : ℝ) / D) * (r / D) ^ p *
          ‖((2 * (v * (y : ℂ) * star d).re : ℝ) : ℂ)‖ := by
        rw [hkernelval, norm_mul, norm_mul, norm_mul, hphase, one_mul, hcoefnorm, hsphnorm] <;> ring
      _ ≤ ((4 / 3 : ℝ) / D) * (r / D) ^ p * (2 * r * ‖d‖) :=
        mul_le_mul_of_nonneg_left hdirnorm hleft
      _ = _ := by
        field_simp [ne_of_gt hDpos] <;> ring
  have hprod : (r / D) ^ p * (‖d‖ / D) ≤
      ((r / c) ^ p * (1 + q) ^ (-p)) *
        (c ^ (-(1 / 2 : ℝ)) * (1 + q) ^ (-(1 / 2 : ℝ))) := by
    calc
      _ ≤ (r / D) ^ p *
          (c ^ (-(1 / 2 : ℝ)) * (1 + q) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hdirpow' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hbasepow (by positivity)
  have hcoef : 0 ≤ 2 * (4 / 3 : ℝ) * r := by positivity
  have hpow : (1 + q) ^ (-p) * (1 + q) ^ (-(1 / 2 : ℝ)) =
      (1 + q) ^ (-(11 / 6 : ℝ)) := by
    rw [← Real.rpow_add (by positivity : 0 < 1 + q)]
    norm_num [p]
  have hmain :
      ‖jacquetKernelC_deriv y v t x‖ ≤
        2 * (4 / 3 : ℝ) * r * (r / c) ^ p * c ^ (-(1 / 2 : ℝ)) *
          (1 + q) ^ (-(11 / 6 : ℝ)) := by
    calc
      _ ≤ 2 * (4 / 3 : ℝ) * r * ((r / D) ^ p * (‖d‖ / D)) := by
        simpa [mul_assoc] using hrough
      _ ≤ 2 * (4 / 3 : ℝ) * r *
          (((r / c) ^ p * (1 + q) ^ (-p)) *
            (c ^ (-(1 / 2 : ℝ)) * (1 + q) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hprod hcoef
      _ = (2 * (4 / 3 : ℝ) * r * (r / c) ^ p * c ^ (-(1 / 2 : ℝ))) *
            ((1 + q) ^ (-p) * (1 + q) ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hpow]
  have hK11 :
      ‖OAI.CubicEisenstein.hyperbolicKernel (11 / 6) x‖ =
        (1 + ‖x‖ ^ 2) ^ (-(11 / 6 : ℝ)) := by
    unfold OAI.CubicEisenstein.hyperbolicKernel
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
  simpa [jacquetKernelC_majorantConst, r, c, q, hK11, p] using hmain

private theorem jacquetKernelC_integrable_zero (y : ℂˣ) (v : ℂ) :
    Integrable (jacquetKernelC y v 0) := by
  let r : ℝ := ‖(y : ℂ)‖
  let A : ℝ := min (r ^ 2) 1
  let C0 : ℝ := (r / A) ^ (4 / 3 : ℝ)
  let K : ℂ → ℂ := OAI.CubicEisenstein.hyperbolicKernel (4 / 3)
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr y.ne_zero
  have hA : 0 < A := by
    dsimp [A]
    exact lt_min (sq_pos_of_pos hr) zero_lt_one
  have hu0 : upperM ℂ (0 : ℂ) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperM]
  have hn0 : nC (0 : ℂ) = 1 := by
    change ((upperM ℂ 0 : GL (Fin 2) ℂ) : PGL2 ℂ) = 1
    rw [hu0]
    simp
  have hkernel (x : ℂ) :
      jacquetKernelC y v 0 x =
        psiC (-x) * (((r / (r ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (4 / 3 : ℂ)) := by
    change psiC (-x) *
        sphC (1 / 6) (wC * nC x * aC y * nC ((0 : ℝ) • v)) = _
    rw [zero_smul, hn0, mul_one, sphC_w_n_a]
  have hphase (x : ℂ) : ‖psiC (-x)‖ = 1 := by
    rw [psiC_neg_eq_breveE, OAI.CubicEisenstein.breveE_norm]
  have hKint : Integrable K := by
    dsimp [K]
    exact OAI.CubicEisenstein.hyperbolicKernel_integrable (4 / 3) (by norm_num)
  have hKnorm (x : ℂ) : ‖K x‖ = (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
    dsimp [K, OAI.CubicEisenstein.hyperbolicKernel]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
  have hbasepos (x : ℂ) : 0 < r / (r ^ 2 + ‖x‖ ^ 2) := by
    exact div_pos hr (by positivity)
  have hF0norm (x : ℂ) :
      ‖jacquetKernelC y v 0 x‖ =
        (r / (r ^ 2 + ‖x‖ ^ 2)) ^ (4 / 3 : ℝ) := by
    rw [hkernel, norm_mul, hphase, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hbasepos x)]
    norm_num
  have hdenlower (x : ℂ) : A * (1 + ‖x‖ ^ 2) ≤ r ^ 2 + ‖x‖ ^ 2 := by
    by_cases hr2 : r ^ 2 ≤ 1
    · rw [show A = r ^ 2 by simp [A, min_eq_left hr2]]
      nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hr2)]
    · have hr2' : 1 ≤ r ^ 2 := le_of_not_ge hr2
      rw [show A = 1 by simp [A, min_eq_right hr2']]
      nlinarith [sq_nonneg ‖x‖]
  have hbasele (x : ℂ) :
      r / (r ^ 2 + ‖x‖ ^ 2) ≤ (r / A) / (1 + ‖x‖ ^ 2) := by
    have hD : 0 < r ^ 2 + ‖x‖ ^ 2 := by positivity
    have hAD : 0 < A * (1 + ‖x‖ ^ 2) := mul_pos hA (by positivity)
    rw [div_div]
    apply (div_le_div_iff₀ hD hAD).2
    have hmul := mul_le_mul_of_nonneg_left (hdenlower x) hr.le
    nlinarith [hmul]
  have hpowle (x : ℂ) :
      (r / (r ^ 2 + ‖x‖ ^ 2)) ^ (4 / 3 : ℝ) ≤
        C0 * (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
    calc
      _ ≤ ((r / A) / (1 + ‖x‖ ^ 2)) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (hbasele x) (by norm_num)
      _ = C0 * (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        rw [Real.div_rpow (by positivity) (by positivity)]
        change (r / A) ^ (4 / 3 : ℝ) *
          ((1 + ‖x‖ ^ 2) ^ (4 / 3 : ℝ))⁻¹ = _
        rw [← Real.rpow_neg (by positivity) (4 / 3 : ℝ)]
  have hmajor : Integrable (fun x : ℂ => C0 * ‖K x‖) := by
    have h := hKint.norm.const_mul C0
    simpa [mul_comm] using h
  have hmeas : AEStronglyMeasurable (jacquetKernelC y v 0) volume := by
    have hnCcont : Continuous nC := continuous_nC_complex
    have harg : Continuous (fun x : ℂ => wC * nC x * aC y * nC ((0 : ℝ) • v)) := by
      fun_prop
    have hcont : Continuous (jacquetKernelC y v 0) := by
      change Continuous (fun x : ℂ =>
        psiC (-x) * sphC (1 / 6) (wC * nC x * aC y * nC ((0 : ℝ) • v)))
      have hphase : Continuous fun x : ℂ => psiC (-x) := by
        unfold psiC
        fun_prop
      exact hphase.mul
        ((sphC_isSection (1 / 6)).2.comp harg)
    exact hcont.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with x
  calc
    ‖jacquetKernelC y v 0 x‖ = (r / (r ^ 2 + ‖x‖ ^ 2)) ^ (4 / 3 : ℝ) := hF0norm x
    _ ≤ C0 * (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := hpowle x
    _ = C0 * ‖K x‖ := by rw [hKnorm]

private theorem psiC_direction_hasDerivAt (y : ℂˣ) (v : ℂ) :
    HasDerivAt (fun t : ℝ => psiC ((y : ℂ) * ((t : ℝ) • v)))
      (-(4 * Real.pi * Complex.I) *
        Complex.ofReal (((y : ℂ) * v).re)) 0 := by
  let a : ℝ := ((y : ℂ) * v).re
  let c : ℂ := -(4 * Real.pi * Complex.I * (a : ℂ))
  have hsmul (t : ℝ) : (t : ℝ) • v = (t : ℂ) * v := by
    simp [smul_eq_mul]
  have hRe (t : ℝ) : ((y : ℂ) * ((t : ℝ) • v)).re = t * a := by
    rw [hsmul]
    have hmul : (y : ℂ) * ((t : ℂ) * v) = (t : ℂ) * ((y : ℂ) * v) := by ring
    rw [hmul, Complex.mul_re]
    simp [a]
  have harg (t : ℝ) :
      -(4 * Real.pi * Complex.I *
        (((y : ℂ) * ((t : ℝ) • v)).re : ℂ)) = (t : ℂ) * c := by
    rw [hRe]
    dsimp [c, a]
    rw [Complex.ofReal_mul]
    ring
  have hfun : (fun t : ℝ => psiC ((y : ℂ) * ((t : ℝ) • v))) =
      fun t : ℝ => Complex.exp ((t : ℂ) * c) := by
    funext t
    unfold psiC
    rw [harg]
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasDerivAt
  have hmul := hcast.const_mul c
  have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c 0 := by
    have hfun : (fun t : ℝ => (t : ℂ) * c) = fun t : ℝ => c * (t : ℂ) := by
      funext t
      ring
    rw [hfun]
    simpa using hmul
  have hExpF := (Complex.hasDerivAt_exp (0 : ℂ)).hasFDerivAt.restrictScalars ℝ
  have hcompExp := HasFDerivAt.comp_hasDerivAt_of_eq
    (f := fun t : ℝ => (t : ℂ) * c) (0 : ℝ) (y := (0 : ℂ)) hExpF hlin (by simp)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
    simpa [Function.comp_def, hExpF] using hcompExp
  have hchar : HasDerivAt (fun t : ℝ => psiC ((y : ℂ) * ((t : ℝ) • v))) c 0 := by
    rw [hfun]
    simpa using hexp
  simpa [c, a] using hchar

private theorem jacquetKernelC_deriv_zero_eq (y : ℂˣ) (v : ℂ) (x : ℂ) :
    jacquetKernelC_deriv y v 0 x =
      psiC (-x) * fderiv ℝ
        (fun z : ℂ => sphC (1 / 6) (wC * nC x * aC y * nC z)) 0 v := by
  let G : GL (Fin 2) ℂ := jacquetMatrixC y x
  have hq : wC * nC x * aC y = QuotientGroup.mk G := by
    simpa [G, jacquetMatrixC] using jacquetMatrixC_mk y x
  let h : ℂ → ℂ := fun z => sphC (1 / 6) (QuotientGroup.mk G * nC z)
  have hdiff : DifferentiableAt ℝ h 0 := sphC_right_n_differentiableAt G 0
  have hv : HasDerivAt (fun t : ℝ => (t : ℝ) • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hcomp : HasDerivAt (fun t : ℝ => h ((t : ℝ) • v))
      (fderiv ℝ h 0 v) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp)
  have hcomp' := hcomp.const_mul (psiC (-x))
  have hfun : (fun t : ℝ => jacquetKernelC y v t x) =
      fun t => psiC (-x) * h ((t : ℝ) • v) := by
    funext t
    simp [jacquetKernelC, h, hq]
  have hevent : (fun t : ℝ => jacquetKernelC y v t x) =ᶠ[nhds (0 : ℝ)]
      fun t => psiC (-x) * h ((t : ℝ) • v) :=
    Filter.Eventually.of_forall (fun t => congrFun hfun t)
  have hcompKernel : HasDerivAt (fun t : ℝ => jacquetKernelC y v t x)
      (psiC (-x) * fderiv ℝ h 0 v) 0 :=
    (Filter.EventuallyEq.hasDerivAt_iff hevent).2 hcomp'
  have heval := (jacquetKernelC_hasDerivAt y v 0 x).unique hcompKernel
  simpa [h, hq, jacquetKernelC_deriv] using heval

private theorem jacquetKernelC_integral_translate (y : ℂˣ) (v : ℂ) (t : ℝ) :
    (∫ x : ℂ, jacquetKernelC y v t x) =
      psiC ((y : ℂ) * ((t : ℝ) • v)) *
        jacquetC (rtr (aC y) (sphC (1 / 6))) := by
  let u : ℂ := (t : ℝ) • v
  let f : PGL2 ℂ → ℂ := rtr (aC y) (sphC (1 / 6))
  have hf : IsSectionC (1 / 6) f := by
    intro x z g
    simpa [f, rtr, mul_assoc] using
      (sphC_isSection (1 / 6)).1 x z (g * aC y)
  have hmul : Continuous (fun g : PGL2 ℂ => g * aC y) := by fun_prop
  have hcont : Continuous f := by
    change Continuous (fun g : PGL2 ℂ => sphC (1 / 6) (g * aC y))
    exact (sphC_isSection (1 / 6)).2.comp hmul
  have hact : rtr (aC y * nC u) (sphC (1 / 6)) =
      rtr (nC ((y : ℂ) * u)) f := by
    funext g
    simp [f, rtr, aC_nC, mul_assoc]
  have hkernel : (∫ x : ℂ, jacquetKernelC y v t x) =
      jacquetC (rtr (aC y * nC u) (sphC (1 / 6))) := by
    simp [jacquetKernelC, jacquetC, rtr, u, mul_assoc]
  calc
    (∫ x : ℂ, jacquetKernelC y v t x) =
        jacquetC (rtr (aC y * nC u) (sphC (1 / 6))) := hkernel
    _ = jacquetC (rtr (nC ((y : ℂ) * u)) f) := by rw [hact]
    _ = psiC ((y : ℂ) * u) * jacquetC f :=
      jacquetC_equiv (1 / 6) (by norm_num) f hf hcont ((y : ℂ) * u)
    _ = _ := by rfl

private theorem jacquetKernelC_line_deriv_integrable (y : ℂˣ) (v : ℂ)
    (hv : ‖v‖ = 1) :
    Integrable (jacquetKernelC_deriv y v 0) ∧
      (∫ x : ℂ, jacquetKernelC_deriv y v 0 x) =
        (-(4 * Real.pi * Complex.I) *
          Complex.ofReal (((y : ℂ) * v).re)) *
          jacquetC (rtr (aC y) (sphC (1 / 6))) := by
  classical
  let K : ℂ → ℂ := OAI.CubicEisenstein.hyperbolicKernel (11 / 6)
  let bound : ℂ → ℝ := fun x => jacquetKernelC_majorantConst y * ‖K x‖
  have hF_meas : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (jacquetKernelC y v t) volume := by
    filter_upwards [] with t
    exact (jacquetKernelC_continuous y v t).aestronglyMeasurable
  have hF_int : Integrable (jacquetKernelC y v 0) volume :=
    jacquetKernelC_integrable_zero y v
  have hF'_meas : AEStronglyMeasurable (jacquetKernelC_deriv y v 0) volume :=
    (jacquetKernelC_deriv_continuous y v 0).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖jacquetKernelC_deriv y v t x‖ ≤ bound x := by
    filter_upwards [] with x
    intro t ht
    simpa [bound, K] using jacquetKernelC_deriv_bound y v t x hv ht
  have hK_int : Integrable K := by
    dsimp [K]
    exact OAI.CubicEisenstein.hyperbolicKernel_integrable (11 / 6) (by norm_num)
  have hbound_int : Integrable bound := by
    dsimp [bound]
    have h := hK_int.norm.const_mul (jacquetKernelC_majorantConst y)
    simpa [mul_comm] using h
  have h_diff : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (jacquetKernelC y v · x) (jacquetKernelC_deriv y v t x) t := by
    filter_upwards [] with x
    intro t ht
    exact jacquetKernelC_hasDerivAt y v t x
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t : ℝ => jacquetKernelC y v t)
    (F' := fun t : ℝ => jacquetKernelC_deriv y v t)
    (s := Metric.ball (0 : ℝ) 1) (x₀ := 0) (bound := bound) (μ := volume)
    (Metric.ball_mem_nhds 0 (by norm_num)) hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff
  let J : ℂ := jacquetC (rtr (aC y) (sphC (1 / 6)))
  have hline : (fun t : ℝ => ∫ x : ℂ, jacquetKernelC y v t x) =
      fun t => psiC ((y : ℂ) * ((t : ℝ) • v)) * J := by
    funext t
    exact jacquetKernelC_integral_translate y v t
  have hchar := (psiC_direction_hasDerivAt y v).mul_const J
  have hchar' : HasDerivAt (fun t : ℝ => ∫ x : ℂ, jacquetKernelC y v t x)
      ((-(4 * Real.pi * Complex.I) *
        Complex.ofReal (((y : ℂ) * v).re)) * J) 0 := by
    rw [hline]
    simpa [J] using hchar
  have heq := hparam.2.unique hchar'
  exact ⟨hparam.1, by simpa [J] using heq⟩

/-- **jq:complex-derivative** (eq:theta-complex-derivative, 03:292–312). -/
theorem jacquetC_derivative (m : ℤ) (hm : m = 1 ∨ m = -1) (y : ℂˣ) :
    jacquetC (rtr (aC y) (derivVecC m (sphC (1 / 6)))) =
      -(4 * Real.pi * Complex.I) * besselConst * (Complex.normSq (y : ℂ) : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖(y : ℂ)‖) : ℂ) := by
  classical
  let J : ℂ := jacquetC (rtr (aC y) (sphC (1 / 6)))
  let D₁ : ℂ → ℂ := jacquetKernelC_deriv y 1 0
  let Dᵢ : ℂ → ℂ := jacquetKernelC_deriv y Complex.I 0
  have h₁ := jacquetKernelC_line_deriv_integrable y 1 (by simp)
  have hᵢ := jacquetKernelC_line_deriv_integrable y Complex.I (by simp)
  have hpoint (x : ℂ) : D₁ x - (m : ℂ) * Complex.I * Dᵢ x =
      psiC (-x) * derivVecC m (sphC (1 / 6)) (wC * nC x * aC y) := by
    dsimp only [D₁, Dᵢ]
    rw [jacquetKernelC_deriv_zero_eq y 1 x,
      jacquetKernelC_deriv_zero_eq y Complex.I x]
    simp only [derivVecC]
    ring
  have h_integral : jacquetC (rtr (aC y) (derivVecC m (sphC (1 / 6)))) =
      (∫ x : ℂ, D₁ x) - (m : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) := by
    calc
      jacquetC (rtr (aC y) (derivVecC m (sphC (1 / 6)))) =
          ∫ x : ℂ, psiC (-x) * derivVecC m (sphC (1 / 6)) (wC * nC x * aC y) := by
            simp [jacquetC, rtr, mul_assoc]
      _ = ∫ x : ℂ, D₁ x - (m : ℂ) * Complex.I * Dᵢ x := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact (hpoint x).symm
      _ = (∫ x : ℂ, D₁ x) - (m : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) := by
            rw [integral_sub h₁.1 (hᵢ.1.const_mul ((m : ℂ) * Complex.I)),
              integral_const_mul]
  have hD₁ : (∫ x : ℂ, D₁ x) =
      -(4 * Real.pi * Complex.I) * ((y : ℂ).re : ℂ) * J := by
    simpa [D₁, J] using h₁.2
  have hReᵢ : (((y : ℂ) * Complex.I).re) = -(y : ℂ).im := by
    simp [Complex.mul_re]
  have hDᵢ : (∫ x : ℂ, Dᵢ x) =
      (4 * Real.pi * Complex.I) * ((y : ℂ).im : ℂ) * J := by
    calc
      _ = -(4 * Real.pi * Complex.I) *
          Complex.ofReal (((y : ℂ) * Complex.I).re) * J := by
            simpa [Dᵢ, J] using hᵢ.2
      _ = _ := by rw [hReᵢ, Complex.ofReal_neg]; ring
  have hcomb₁ : (∫ x : ℂ, D₁ x) - (1 : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) =
      -(4 * Real.pi * Complex.I) * (y : ℂ) * J := by
    rw [hD₁, hDᵢ]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hcomb_neg1 : (∫ x : ℂ, D₁ x) - (-1 : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) =
      -(4 * Real.pi * Complex.I) * star (y : ℂ) * J := by
    rw [hD₁, hDᵢ]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  let r : ℝ := ‖(y : ℂ)‖
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr y.ne_zero
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hnormSq : (Complex.normSq (y : ℂ) : ℂ) = star (y : ℂ) * (y : ℂ) := by
    simp [Complex.normSq_eq_conj_mul_self]
  have hAng₁ : omegaAng 1 (y : ℂ) = (y : ℂ) / (r : ℂ) := by
    simp [omegaAng, r]
  have hAng_neg1 : omegaAng (-1) (y : ℂ) = (r : ℂ) / (y : ℂ) := by
    simp [omegaAng, r, zpow_neg_one]
  have hpolar₁ : (y : ℂ) * (r : ℂ) =
      (Complex.normSq (y : ℂ) : ℂ) * omegaAng 1 (y : ℂ) := by
    rw [hAng₁]
    have hnorm : (Complex.normSq (y : ℂ) : ℂ) = (r : ℂ) ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, r]
    rw [hnorm]
    field_simp [hrne]
  have hpolar_neg1 : star (y : ℂ) * (r : ℂ) =
      (Complex.normSq (y : ℂ) : ℂ) * omegaAng (-1) (y : ℂ) := by
    rw [hAng_neg1, hnormSq]
    field_simp [hrne, y.ne_zero]
  rcases hm with hm | hm
  · subst m
    calc
      jacquetC (rtr (aC y) (derivVecC 1 (sphC (1 / 6)))) =
          (∫ x : ℂ, D₁ x) - (1 : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) := by
            simpa using h_integral
      _ = -(4 * Real.pi * Complex.I) * (y : ℂ) * J := hcomb₁
      _ = -(4 * Real.pi * Complex.I) * besselConst *
            (Complex.normSq (y : ℂ) : ℂ) * omegaAng 1 (y : ℂ) *
              (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by
            rw [show J = ((besselConst * r *
              besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ) by
                dsimp [J, r]
                exact jacquetC_spherical y]
            have hpolar : (y : ℂ) *
                ((besselConst * r * besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ) =
                (besselConst : ℂ) * (Complex.normSq (y : ℂ) : ℂ) *
                  omegaAng 1 (y : ℂ) *
                    (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by
              calc
                _ = (besselConst : ℂ) * ((y : ℂ) * (r : ℂ)) *
                    (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by push_cast; ring
                _ = _ := by rw [hpolar₁]; ring
            calc
              _ = -(4 * Real.pi * Complex.I) *
                  ((y : ℂ) *
                    ((besselConst * r * besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ)) := by ring
              _ = -(4 * Real.pi * Complex.I) *
                  ((besselConst : ℂ) * (Complex.normSq (y : ℂ) : ℂ) *
                    omegaAng 1 (y : ℂ) *
                      (besselK (1 / 3) (4 * Real.pi * r) : ℂ)) := by rw [hpolar]
              _ = _ := by ring
  · subst m
    calc
      jacquetC (rtr (aC y) (derivVecC (-1) (sphC (1 / 6)))) =
          (∫ x : ℂ, D₁ x) - (-1 : ℂ) * Complex.I * (∫ x : ℂ, Dᵢ x) := by
            simpa using h_integral
      _ = -(4 * Real.pi * Complex.I) * star (y : ℂ) * J := hcomb_neg1
      _ = -(4 * Real.pi * Complex.I) * besselConst *
            (Complex.normSq (y : ℂ) : ℂ) * omegaAng (-1) (y : ℂ) *
              (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by
            rw [show J = ((besselConst * r *
              besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ) by
                dsimp [J, r]
                exact jacquetC_spherical y]
            have hpolar : star (y : ℂ) *
                ((besselConst * r * besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ) =
                (besselConst : ℂ) * (Complex.normSq (y : ℂ) : ℂ) *
                  omegaAng (-1) (y : ℂ) *
                    (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by
              calc
                _ = (besselConst : ℂ) * (star (y : ℂ) * (r : ℂ)) *
                    (besselK (1 / 3) (4 * Real.pi * r) : ℂ) := by push_cast; ring
                _ = _ := by rw [hpolar_neg1]; ring
            calc
              _ = -(4 * Real.pi * Complex.I) *
                  (star (y : ℂ) *
                    ((besselConst * r * besselK (1 / 3) (4 * Real.pi * r) : ℝ) : ℂ)) := by ring
              _ = -(4 * Real.pi * Complex.I) *
                  ((besselConst : ℂ) * (Complex.normSq (y : ℂ) : ℂ) *
                    omegaAng (-1) (y : ℂ) *
                      (besselK (1 / 3) (4 * Real.pi * r) : ℂ)) := by rw [hpolar]
              _ = _ := by ring

/-- **jq:complex-rotation**: `π(w) f_m = f_{-m}` (`Ad(w)E_a ≡ E_{ā}` modulo `𝔰𝔲(2)`). -/
private theorem sphericalC_right_w (s : ℂ) (g : GL (Fin 2) ℂ) :
    sphericalC s (g * weylM ℂ) = sphericalC s g := by
  have hdet :
      ‖Matrix.det ((g * weylM ℂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ =
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    change ‖((Matrix.GeneralLinearGroup.det (g * weylM ℂ) : ℂˣ) : ℂ)‖ = _
    rw [map_mul]
    simp [weylM]
  have hrow :
      ‖((g * weylM ℂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖((g * weylM ℂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
    simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  unfold sphericalC
  rw [hdet, hrow]

theorem derivVecC_rotate (m : ℤ) (s : ℂ) :
    rtr wC (derivVecC m (sphC s)) = derivVecC (-m) (sphC s) := by
  funext q
  refine QuotientGroup.induction_on q ?_
  intro g
  change derivVecC m (sphC s) (QuotientGroup.mk g * wC) =
    derivVecC (-m) (sphC s) (QuotientGroup.mk g)
  have hq : QuotientGroup.mk g * wC = QuotientGroup.mk (g * weylM ℂ) := by
    change QuotientGroup.mk g * QuotientGroup.mk (weylM ℂ) = _
    simp only [QuotientGroup.mk_mul]
  rw [hq, derivVecC_spherical_mk, derivVecC_spherical_mk, sphericalC_right_w]
  simp [Matrix.GeneralLinearGroup.coe_mul, weylM, Matrix.mul_apply, Fin.sum_univ_two,
    RCLike.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring_nf

theorem derivVecC_isSection (m : ℤ) (s : ℂ) :
    IsSectionC s (derivVecC m (sphC s)) ∧ Continuous (derivVecC m (sphC s)) := by
  let χ : ℂˣ → ℂ := fun y =>
    (Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)
  constructor
  · intro x y g
    refine QuotientGroup.induction_on g ?_
    intro G
    let G' : GL (Fin 2) ℂ := upperM ℂ x * diagM ℂ y * G
    have hq : (QuotientGroup.mk (upperM ℂ x) : PGL2 ℂ) *
        QuotientGroup.mk (diagM ℂ y) * QuotientGroup.mk G =
          QuotientGroup.mk (upperM ℂ x * diagM ℂ y * G) := by
      change (QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ y)) *
        QuotientGroup.mk G = _
      simp only [QuotientGroup.mk_mul]
    have hsph : sphericalC s G' = χ y * sphericalC s G := by
      have h := (sphC_isSection s).1 x y (QuotientGroup.mk G)
      rw [hq, sphC_mk, sphC_mk] at h
      exact h
    have hrow0 : (G' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
        (G : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
      simp [G', Matrix.GeneralLinearGroup.coe_mul, upperM, diagM,
        Matrix.mul_apply, Fin.sum_univ_two]
    have hrow1 : (G' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
        (G : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
      simp [G', Matrix.GeneralLinearGroup.coe_mul, upperM, diagM,
        Matrix.mul_apply, Fin.sum_univ_two]
    change derivVecC m (sphC s) (QuotientGroup.mk G') =
      χ y * derivVecC m (sphC s) (QuotientGroup.mk G)
    rw [derivVecC_spherical_mk, derivVecC_spherical_mk]
    simp only [hrow0, hrow1, hsph]
    ring
  · let B : GL (Fin 2) ℂ → ℝ := fun g =>
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
        Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
    let Z : GL (Fin 2) ℂ → ℂ := fun g =>
      ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
        star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
    let rep : GL (Fin 2) ℂ → ℂ := fun g =>
      -(2 * (1 + 2 * s) / (B g : ℂ)) * sphericalC s g *
        (Complex.ofReal (Z g).re + (m : ℂ) * Complex.I * Complex.ofReal (Z g).im)
    have hrep (g : GL (Fin 2) ℂ) :
        derivVecC m (sphC s) (QuotientGroup.mk g) = rep g := by
      simpa [rep, B, Z] using derivVecC_spherical_mk m s g
    have hBcont : Continuous B := by
      dsimp [B]
      fun_prop
    have hBpos (g : GL (Fin 2) ℂ) : 0 < B g := by
      simpa [B] using sphC_bottom_norm_pos g
    have hZcont : Continuous Z := by
      dsimp [Z]
      fun_prop
    have hsphGL : Continuous (sphericalC s) := by
      have hmk : Continuous (fun g : GL (Fin 2) ℂ =>
          (QuotientGroup.mk g : PGL2 ℂ)) :=
        (QuotientGroup.isQuotientMap_mk
          (Subgroup.center (GL (Fin 2) ℂ))).continuous
      have h := (sphC_isSection s).2.comp hmk
      convert h using 1
      funext g
      exact (sphC_mk s g).symm
    have hden (g : GL (Fin 2) ℂ) : (B g : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hBpos g))
    have hcoef : Continuous fun g : GL (Fin 2) ℂ =>
        (2 * (1 + 2 * s) : ℂ) / (B g : ℂ) := by
      exact continuous_const.div (Complex.continuous_ofReal.comp hBcont) hden
    have hlin : Continuous fun g : GL (Fin 2) ℂ =>
        Complex.ofReal (Z g).re + (m : ℂ) * Complex.I * Complex.ofReal (Z g).im := by
      fun_prop
    have hrepcont : Continuous rep := by
      dsimp [rep]
      exact hcoef.neg.mul hsphGL |>.mul hlin
    have hcont : Continuous (derivVecC m (sphC s)) := by
      apply (QuotientGroup.isQuotientMap_mk
        (Subgroup.center (GL (Fin 2) ℂ))).continuous_iff.mpr
      convert hrepcont using 1
      funext g
      exact hrep g
    exact hcont

/-- **jq:complex-sheet** (eq:theta-complex-bounds, T6 at complex places, `δ = 1/3`). -/
theorem sheetHypC_bessel (m : ℤ) (hm : m = 1 ∨ m = -1) (c : ℂ) :
    SheetHypC (1 / 3) (fun y : ℂ => c * (Complex.normSq y : ℂ) * omegaAng m y *
      (besselK (1 / 3) (4 * Real.pi * ‖y‖) : ℂ)) := by
  sorry

/-- **int:complex-spherical**: `M_ℂ(s) f°_s = (π/(2s)) f°_{-s}` for `Re s > 0`. -/
theorem intertwineC_spherical (s : ℂ) (hs : 0 < s.re) :
    intertwineC (sphC s) = fun g => (Real.pi / (2 * s)) * sphC (-s) g := by
  funext q
  refine QuotientGroup.induction_on q ?_
  intro g
  let M : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  let a : ℂ := M 0 0
  let b : ℂ := M 0 1
  let c : ℂ := M 1 0
  let d : ℂ := M 1 1
  let A : ℝ := Complex.normSq c + Complex.normSq d
  have hApos : 0 < A := by
    have hAnonneg : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (Complex.normSq_nonneg c) (Complex.normSq_nonneg d)
    by_contra hn
    have hAz : A = 0 := le_antisymm (not_lt.mp hn) hAnonneg
    have hcN : Complex.normSq c = 0 := by
      dsimp [A] at hAz
      nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]
    have hdN : Complex.normSq d = 0 := by
      dsimp [A] at hAz
      nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]
    have hc0 : c = 0 := Complex.normSq_eq_zero.mp hcN
    have hd0 : d = 0 := Complex.normSq_eq_zero.mp hdN
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, M, a, b, c, d, hc0, hd0]
  have hAne : Complex.normSq c + Complex.normSq d ≠ 0 := by
    exact ne_of_gt hApos
  let shift : ℂ := (a * star c + b * star d) / (A : ℂ)
  let r : ℝ := ‖M.det‖ / A
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (norm_pos_iff.mpr g.det_ne_zero) hApos
  let lam : ℂ := 1 + 2 * s
  let F : ℂ → ℂ := fun z => (((r / (r ^ 2 + ‖z‖ ^ 2) : ℝ) : ℂ) ^ lam)
  have hdet : M.det = a * d - b * c := by
    simp [Matrix.det_fin_two, M, a, b, c, d]
  have hconst : Complex.normSq (a * d - b * c) / A = A * r ^ 2 := by
    rw [← hdet]
    dsimp [r]
    rw [Complex.normSq_eq_norm_sq]
    field_simp [hApos.ne']
  have hden (x : ℂ) :
      Complex.normSq (a + x * c) + Complex.normSq (b + x * d) =
        A * (Complex.normSq (x + shift) + r ^ 2) := by
    rw [complex_complete_square a b c d x hAne, hconst]
    ring
  have hdenNorm (x : ℂ) :
      ‖a + x * c‖ ^ 2 + ‖b + x * d‖ ^ 2 = A * (‖x + shift‖ ^ 2 + r ^ 2) := by
    simpa only [Complex.normSq_eq_norm_sq] using hden x
  have hbase (x : ℂ) :
      ‖M.det‖ / (‖a + x * c‖ ^ 2 + ‖b + x * d‖ ^ 2) =
        r / (r ^ 2 + ‖x + shift‖ ^ 2) := by
    rw [hdenNorm x]
    dsimp [r]
    field_simp [hApos.ne']
    ring
  have hpoint (x : ℂ) : sphC s (wC * nC x * QuotientGroup.mk g) = F (x + shift) := by
    rw [sphC_w_n_right_mk]
    have hb := congrArg (fun t : ℝ => ((t : ℂ) ^ (1 + 2 * s))) (hbase x)
    simpa [F, lam, M, a, b, c, d] using hb
  have hshift : (∫ x : ℂ, F (x + shift)) = ∫ x : ℂ, F x := by
    have hMP : MeasurePreserving (MeasurableEquiv.addRight shift) volume volume := by
      exact measurePreserving_add_right volume shift
    exact hMP.integral_comp (MeasurableEquiv.addRight shift).measurableEmbedding F
  have hnegative : sphC (-s) (QuotientGroup.mk g) = (r : ℂ) ^ (1 - 2 * s) := by
    rw [sphC_mk]
    unfold sphericalC
    have hb0 : ‖M.det‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2) = r := by
      dsimp [r, A, M, c, d]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [hb0, show 1 + 2 * -s = 1 - 2 * s by ring]
  calc
    intertwineC (sphC s) (QuotientGroup.mk g) = ∫ x : ℂ, F (x + shift) := by
      rw [intertwineC]
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = ∫ x : ℂ, F x := hshift
    _ = (Real.pi / (2 * s)) * (r : ℂ) ^ (1 - 2 * s) := by
      simpa [F, lam] using integral_sphC_radial s hs r hrpos
    _ = (Real.pi / (2 * s)) * sphC (-s) (QuotientGroup.mk g) := by rw [hnegative]

end ComplexInt

end ArtinPrimitiveRoots.A1.Theta
