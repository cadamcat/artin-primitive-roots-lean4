import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Shared
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import ArtinPrimitiveRoots.Theta.Proofs.TH_JACQUET.SectionLinear

open MeasureTheory Filter
open Topology

set_option autoImplicit false

open NumberField IsDedekindDomain
open ArtinPrimitiveRoots.Proofs.th_jacquet_p
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

private theorem adicCompletion_properSpace (v : FinPlace F) :
    ProperSpace (v.adicCompletion F) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩

private theorem ball_isCompact (v : FinPlace F) (m : ℤ) :
    IsCompact (ball v m) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  letI : ProperSpace K := adicCompletion_properSpace v
  let π : Kˣ := unifLoc v
  have hπ : v.valuation F (unif (F := F) v) = WithZero.exp (-1 : ℤ) := by
    dsimp [unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπcoerce : (π : K) = algebraMap F K (unif (F := F) v) := by
    simpa [π, unifLoc, toLoc, K]
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [hπcoerce]
    change Valued.v (algebraMap F (v.adicCompletion F) (unif (F := F) v)) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  let r : K := ((π ^ m : Kˣ) : K)
  have hrval : Valued.v r = WithZero.exp (-m) := by simp [r, hπval]
  have hball : ball v m = Metric.closedBall 0 ‖r‖ := by
    ext x
    simp only [ball, Metric.mem_closedBall, dist_zero_right]
    rw [← hrval]
    change Valued.v x ≤ Valued.v r ↔ ‖x‖ ≤ ‖r‖
    exact Valued.toNormedField.norm_le_iff.symm
  rw [hball]
  exact (adicCompletion_properSpace v).isCompact_closedBall 0 ‖r‖

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

private theorem jacquetKernel_integrableOn (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (s : ℂ) (f : L.L → T.V)
    (hf : IsSection L T s f) (N : ℕ) :
    IntegrableOn (fun x => A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x)))
      (ball v (-(N : ℤ))) μ.μ := by
  let K := v.adicCompletion F
  obtain ⟨d, hψ, -⟩ := psi_conductor A v
  obtain ⟨m, hm, hK⟩ := hf.2.2
  have hψball : ∀ z ∈ ball v m, A.ψ v z = 1 := by
    intro z hz
    apply hψ z
    change Valued.v z ≤ WithZero.exp (-(m : ℤ)) at hz
    change Valued.v z ≤ WithZero.exp (-(-(d : ℤ)))
    rw [Int.neg_neg]
    change Valued.v z ≤ WithZero.exp (d : ℤ)
    exact hz.trans (WithZero.exp_le_exp.mpr (by omega))
  have hψball_neg : ∀ z ∈ ball v m, A.ψ v (-z) = 1 := by
    intro z hz
    rw [AddChar.map_neg_eq_inv (A.ψ v) z]
    simp [hψball z hz]
  let kfun : K → T.V := fun x => A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))
  have hballOpen : IsOpen (ball v m) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hkfun : IsLocallyConstant kfun := by
    apply (IsLocallyConstant.iff_exists_open kfun).mpr
    intro x
    let U := (fun x' : K => x' - x) ⁻¹' ball v m
    have hU : IsOpen U := by
      dsimp [U]
      exact hballOpen.preimage (continuous_id.sub continuous_const)
    have hxU : x ∈ U := by
      dsimp [U]
      change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
      simp
    refine ⟨U, hU, hxU, ?_⟩
    intro x' hx'
    have hdiff : x' - x ∈ ball v m := by simpa [U] using hx'
    let z := x' - x
    have hz : z ∈ ball v m := by simpa [z] using hdiff
    have hxEq : x' = x + z := by dsimp [z]; abel
    have hphase : A.ψ v (-x') = A.ψ v (-x) := by
      calc
        A.ψ v (-x') = A.ψ v (-x + -z) := by rw [hxEq, neg_add]
        _ = A.ψ v (-x) * A.ψ v (-z) := AddChar.map_add_eq_mul (A.ψ v) _ _
        _ = A.ψ v (-x) := by
          rw [AddChar.map_neg_eq_inv (A.ψ v) z, hψball z hz]
          simp
    have hgroup : L.w * L.n (Multiplicative.ofAdd x') =
        (L.w * L.n (Multiplicative.ofAdd x)) * L.n (Multiplicative.ofAdd z) := by
      rw [hxEq]
      simp [ofAdd_add, mul_assoc]
    have hsmall : L.n (Multiplicative.ofAdd z) ∈ L.Kc m := L.n_Kc m hm z hz
    have hsection : f (L.w * L.n (Multiplicative.ofAdd x')) =
        f (L.w * L.n (Multiplicative.ofAdd x)) := by
      rw [hgroup]
      exact hK (L.w * L.n (Multiplicative.ofAdd x))
        (L.n (Multiplicative.ofAdd z)) hsmall
    change A.ψ v (-x') • f (L.w * L.n (Multiplicative.ofAdd x')) =
      A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))
    rw [hphase, hsection]
  have hkcont : Continuous kfun := hkfun.continuous
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  letI : ProperSpace K := hproper
  let π : Kˣ := unifLoc v
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hπ : v.valuation F (unif (F := F) v) = WithZero.exp (-1 : ℤ) := by
      dsimp [unif]
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    have hπcoerce : (π : K) = algebraMap F K (unif (F := F) v) := by
      simpa [π, unifLoc, toLoc, K]
    rw [hπcoerce]
    change Valued.v (algebraMap F (v.adicCompletion F) (unif (F := F) v)) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  let r : K := ((π⁻¹ ^ (N : ℤ) : Kˣ) : K)
  have hrval : Valued.v r = WithZero.exp (N : ℤ) := by
    simp [r, hπval]
  have hball : ball v (-(N : ℤ)) = Metric.closedBall 0 ‖r‖ := by
    ext x
    simp only [ball, Metric.mem_closedBall, dist_zero_right, Int.neg_neg]
    rw [← hrval]
    change Valued.v x ≤ Valued.v r ↔ ‖x‖ ≤ ‖r‖
    exact Valued.toNormedField.norm_le_iff.symm
  rw [hball]
  exact hkcont.continuousOn.integrableOn_compact (hproper.isCompact_closedBall 0 ‖r‖)

private theorem jacquetTrunc_add_smul (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (s : ℂ) (f g : L.L → T.V)
    (hf : IsSection L T s f) (hg : IsSection L T s g) (c : ℂ) (N : ℕ) :
    jacquetTrunc L A μ N (f + c • g) =
      jacquetTrunc L A μ N f + c • jacquetTrunc L A μ N g := by
  let B := ball v (-(N : ℤ))
  let kf := fun x => A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))
  let kg := fun x => A.ψ v (-x) • g (L.w * L.n (Multiplicative.ofAdd x))
  have hIf : Integrable kf (μ.μ.restrict B) := jacquetKernel_integrableOn L T A μ s f hf N
  have hIg : Integrable kg (μ.μ.restrict B) := jacquetKernel_integrableOn L T A μ s g hg N
  have hpoint :
      (fun x => A.ψ v (-x) • (f + c • g) (L.w * L.n (Multiplicative.ofAdd x))) =
      fun x => kf x + c • kg x := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  unfold jacquetTrunc
  change ∫ x in B, A.ψ v (-x) • (f + c • g) (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ = _
  rw [hpoint]
  change ∫ x, kf x + c • kg x ∂(μ.μ.restrict B) =
    (∫ x, kf x ∂(μ.μ.restrict B)) + c • ∫ x, kg x ∂(μ.μ.restrict B)
  calc
    ∫ x, kf x + c • kg x ∂(μ.μ.restrict B) =
        (∫ x, kf x ∂(μ.μ.restrict B)) + ∫ x, c • kg x ∂(μ.μ.restrict B) :=
      integral_add hIf (hIg.smul c)
    _ = (∫ x, kf x ∂(μ.μ.restrict B)) + c • ∫ x, kg x ∂(μ.μ.restrict B) := by
      rw [integral_smul]

private theorem integral_comp_addLeft_ball (μ : LocHaar v) (N : ℕ) (t : v.adicCompletion F)
    (ht : t ∈ ball v (-(N : ℤ))) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : v.adicCompletion F → E) :
    ∫ x in ball v (-(N : ℤ)), f (t + x) ∂μ.μ =
      ∫ x in ball v (-(N : ℤ)), f x ∂μ.μ := by
  let K := v.adicCompletion F
  let B := ball v (-(N : ℤ))
  let e : K ≃ᵐ K := MeasurableEquiv.addLeft t
  have hadd {x y : K} (hx : x ∈ B) (hy : y ∈ B) : x + y ∈ B := by
    change x ∈ ball v (-(N : ℤ)) at hx
    change y ∈ ball v (-(N : ℤ)) at hy
    simp only [ball] at hx hy ⊢
    exact (Valued.v.map_add_le_max' x y).trans (max_le hx hy)
  have hneg {x : K} (hx : x ∈ B) : -x ∈ B := by
    change x ∈ ball v (-(N : ℤ)) at hx
    change -x ∈ ball v (-(N : ℤ))
    simp only [ball] at hx ⊢
    change Valued.v (-x) ≤ WithZero.exp (-(-(N : ℤ)))
    rw [Valuation.map_neg]
    exact hx
  have hpre : e ⁻¹' B = B := by
    ext x
    change t + x ∈ B ↔ x ∈ B
    constructor
    · intro hx
      have hsum := hadd (hneg ht) hx
      simpa using hsum
    · intro hx
      exact hadd ht hx
  have hmap := e.restrict_map μ.μ B
  have htrans : Measure.map e μ.μ = μ.μ := by
    simpa [e] using Measure.IsAddLeftInvariant.map_add_left_eq_self t
  rw [htrans, hpre] at hmap
  have hpres : MeasurePreserving e (μ.μ.restrict B) (μ.μ.restrict B) :=
    ⟨e.measurable, hmap.symm⟩
  change ∫ x, f (e x) ∂(μ.μ.restrict B) = ∫ x, f x ∂(μ.μ.restrict B)
  exact MeasurePreserving.integral_comp' hpres f

private theorem jacquetTrunc_unipotent (L : FinLocalCover D H v) (A : AddCharData F)
    (μ : LocHaar v) (N : ℕ) (f : L.L → V) (t : v.adicCompletion F)
    (ht : t ∈ ball v (-(N : ℤ))) :
    jacquetTrunc L A μ N (rtr (L.n (Multiplicative.ofAdd t)) f) =
      A.ψ v t • jacquetTrunc L A μ N f := by
  let B := ball v (-(N : ℤ))
  let kfun := fun x => A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))
  have hphase (x : v.adicCompletion F) :
      A.ψ v (-x) = A.ψ v t * A.ψ v (-(t + x)) := by
    have harg : -x = t + (-(t + x)) := by abel
    rw [harg, AddChar.map_add_eq_mul]
  have hgroup (x : v.adicCompletion F) :
      L.w * L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd t) =
        L.w * L.n (Multiplicative.ofAdd (t + x)) := by
    calc
      _ = L.w * (L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd t)) := by
        simp [mul_assoc]
      _ = L.w * L.n (Multiplicative.ofAdd x * Multiplicative.ofAdd t) := by
        rw [← map_mul]
      _ = L.w * L.n (Multiplicative.ofAdd (x + t)) := by rw [ofAdd_add]
      _ = L.w * L.n (Multiplicative.ofAdd (t + x)) := by rw [add_comm]
  have hkernel (x : v.adicCompletion F) :
      A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x) *
        L.n (Multiplicative.ofAdd t)) = A.ψ v t • kfun (t + x) := by
    rw [hphase x, hgroup x]
    simp [kfun, smul_smul]
  unfold jacquetTrunc
  change (∫ x in B, A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x) *
        L.n (Multiplicative.ofAdd t)) ∂μ.μ) =
      A.ψ v t • ∫ x in B, kfun x ∂μ.μ
  calc
    _ = ∫ x in B, A.ψ v t • kfun (t + x) ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hkernel x
    _ = A.ψ v t • ∫ x in B, kfun (t + x) ∂μ.μ := by rw [integral_smul]
    _ = A.ψ v t • ∫ x in B, kfun x ∂μ.μ := by
      congr 1
      exact integral_comp_addLeft_ball μ N t ht kfun

private theorem jacquetTrunc_central (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (s : ℂ) (N : ℕ) (f : L.L → T.V)
    (hf : IsSection L T s f) (ζ : rootsOfUnity 3 ℂ) :
    jacquetTrunc L A μ N (rtr (L.z ζ) f) =
      ((ζ : ℂˣ) : ℂ) • jacquetTrunc L A μ N f := by
  let B := ball v (-(N : ℤ))
  have hpoint (x : v.adicCompletion F) :
      A.ψ v (-x) • (rtr (L.z ζ) f) (L.w * L.n (Multiplicative.ofAdd x)) =
        ((ζ : ℂˣ) : ℂ) • (A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))) := by
    change A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x) * L.z ζ) = _
    rw [← L.z_central ζ (L.w * L.n (Multiplicative.ofAdd x)),
      hf.2.1 ζ (L.w * L.n (Multiplicative.ofAdd x))]
    module
  unfold jacquetTrunc
  calc
    ∫ x in B, A.ψ v (-x) • (rtr (L.z ζ) f) (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ =
        ∫ x in B, ((ζ : ℂˣ) : ℂ) •
          (A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))) ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = ((ζ : ℂˣ) : ℂ) • ∫ x in B,
        A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ := by
      rw [integral_smul]

private theorem exists_ballNeg_nat (t : v.adicCompletion F) :
    ∃ N : ℕ, t ∈ ball v (-(N : ℤ)) := by
  by_cases ht : t = 0
  · refine ⟨0, ?_⟩
    simp [ht, ball]
  · have hval : Valued.v t ≠ 0 := by simpa [ht]
    lift Valued.v t to ℤ using hval with n hn
    refine ⟨n.natAbs, ?_⟩
    simp only [ball, Int.neg_neg]
    change Valued.v t ≤ WithZero.exp (n.natAbs : ℤ)
    rw [← hn]
    apply WithZero.exp_le_exp.mpr
    cases n with
    | ofNat k => simp
    | negSucc k => simp [Int.natAbs]; omega

private theorem ballNeg_nat_mono {N M : ℕ} (hNM : N ≤ M) :
    ball v (-(N : ℤ)) ⊆ ball v (-(M : ℤ)) := by
  intro x hx
  simp only [ball, Int.neg_neg] at hx ⊢
  exact hx.trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hNM))

private theorem compact_subset_ballNeg_nat {s : Set (v.adicCompletion F)}
    (hs : IsCompact s) (coverPoint : ∀ x, ∃ N : ℕ, x ∈ ball v (-(N : ℤ))) :
    ∃ N : ℕ, s ⊆ ball v (-(N : ℤ)) := by
  let U : ℕ → Set (v.adicCompletion F) := fun N => ball v (-(N : ℤ))
  have hU : ∀ N, IsOpen (U N) := by
    intro N
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hcover : s ⊆ ⋃ N, U N := by
    intro x hx
    obtain ⟨N, hN⟩ := coverPoint x
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover U hU hcover
  let M := t.sup id
  refine ⟨M, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.mp (ht hx) with ⟨N, hN, hxN⟩
  apply ballNeg_nat_mono (by simpa [M] using Finset.le_sup (f := id) hN) hxN

private theorem exists_ballTranslate_subset {U : Set (v.adicCompletion F)}
    (hU : IsOpen U) {x : v.adicCompletion F} (hx : x ∈ U) :
    ∃ N : ℕ, {z | z - x ∈ ball v (N : ℤ)} ⊆ U := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  letI : NormedField K := inferInstance
  let π : Kˣ := unifLoc v
  have hπ : v.valuation F (unif (F := F) v) = WithZero.exp (-1 : ℤ) := by
    dsimp [unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπcoerce : (π : K) = algebraMap F K (unif (F := F) v) := by
    simpa [π, unifLoc, toLoc, K]
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [hπcoerce]
    change Valued.v (algebraMap F (v.adicCompletion F) (unif (F := F) v)) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  have hπnorm : ‖(π : K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hπval]
    simp
  have hpow : Tendsto (fun n : ℕ => (π : K) ^ n) atTop (𝓝 (0 : K)) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπnorm
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hx) with ⟨ε, hε, hεU⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖(π : K) ^ n‖ < ε := by
    filter_upwards [hpow.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
    simpa [Metric.mem_ball, dist_zero_right] using hn
  obtain ⟨N, hNsmall⟩ := Filter.Eventually.exists hsmall
  let r : K := ((π ^ (N : ℤ) : Kˣ) : K)
  have hrval : Valued.v r = WithZero.exp (-(N : ℤ)) := by
    simp [r, hπval, ← WithZero.exp_zsmul]
  have hball : ball v (N : ℤ) = Metric.closedBall 0 ‖r‖ := by
    ext z
    simp only [ball, Metric.mem_closedBall, dist_zero_right]
    rw [← hrval]
    change Valued.v z ≤ Valued.v r ↔ ‖z‖ ≤ ‖r‖
    exact Valued.toNormedField.norm_le_iff.symm
  refine ⟨N, ?_⟩
  intro z hz
  have hnorm : ‖z - x‖ < ε := by
    have hzClosed : z - x ∈ Metric.closedBall (0 : K) ‖r‖ := by
      rw [← hball]
      exact hz
    have hz' : ‖z - x‖ ≤ ‖r‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
    have hrnorm : ‖r‖ < ε := by simpa [r] using hNsmall
    exact lt_of_le_of_lt hz' hrnorm
  have hdist : dist z x < ε := by simpa [dist_eq_norm] using hnorm
  exact hεU (Metric.mem_ball.mpr hdist)

private theorem ballNat_add (N : ℕ) {x y : v.adicCompletion F}
    (hx : x ∈ ball v (N : ℤ)) (hy : y ∈ ball v (N : ℤ)) :
    x + y ∈ ball v (N : ℤ) := by
  simp only [ball] at hx hy ⊢
  exact (Valued.v.map_add_le_max' x y).trans (max_le hx hy)

private theorem ballNat_neg (N : ℕ) {x : v.adicCompletion F}
    (hx : x ∈ ball v (N : ℤ)) : -x ∈ ball v (N : ℤ) := by
  simp only [ball] at hx ⊢
  change Valued.v x ≤ WithZero.exp (-(N : ℤ)) at hx
  change Valued.v (-x) ≤ WithZero.exp (-(N : ℤ))
  rw [Valuation.map_neg]
  exact hx

private theorem ballNat_mono {N M : ℕ} (hNM : N ≤ M) :
    ball v (M : ℤ) ⊆ ball v (N : ℤ) := by
  intro x hx
  simp only [ball] at hx ⊢
  change Valued.v x ≤ WithZero.exp (-(M : ℤ)) at hx
  change Valued.v x ≤ WithZero.exp (-(N : ℤ))
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem ballNat_coset_eq (N : ℕ) (a b x : v.adicCompletion F)
    (hxa : x - a ∈ ball v (N : ℤ)) (hxb : x - b ∈ ball v (N : ℤ)) :
    {z | z - a ∈ ball v (N : ℤ)} = {z | z - b ∈ ball v (N : ℤ)} := by
  have hab : a - b ∈ ball v (N : ℤ) := by
    have heq : a - b = -(x - a) + (x - b) := by abel
    rw [heq]
    exact ballNat_add N (ballNat_neg N hxa) hxb
  have hba : b - a ∈ ball v (N : ℤ) := by
    convert ballNat_neg N hab using 1 <;> abel
  ext z
  constructor
  · intro hza
    have hz : z - b = (z - a) + (a - b) := by abel
    change z - b ∈ ball v (N : ℤ)
    rw [hz]
    exact ballNat_add N hza hab
  · intro hzb
    have hz : z - a = (z - b) + (b - a) := by abel
    change z - a ∈ ball v (N : ℤ)
    rw [hz]
    exact ballNat_add N hzb hba

private theorem exists_uniform_ball_translation (U : Set (v.adicCompletion F))
    (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ N : ℕ, ∀ x ∈ U, ∀ z ∈ ball v (N : ℤ), x + z ∈ U := by
  classical
  let Usub := {x : v.adicCompletion F // x ∈ U}
  choose n hn using fun x : Usub => exists_ballTranslate_subset hUo x.property
  let W : Usub → Set (v.adicCompletion F) := fun x =>
    {z | z - (x : v.adicCompletion F) ∈ ball v (n x : ℤ)}
  have hWo (x : Usub) : IsOpen (W x) := by
    dsimp [W]
    exact (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
      (continuous_id.sub continuous_const)
  have hcover : U ⊆ ⋃ x : Usub, W x := by
    intro x hx
    apply Set.mem_iUnion.2
    refine ⟨⟨x, hx⟩, ?_⟩
    simp [W, ball]
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover W hWo hcover
  let N := t.sup n
  refine ⟨N, ?_⟩
  intro x hx z hz
  rcases Set.mem_iUnion₂.mp (ht hx) with ⟨a, ha, hxa⟩
  have hna : n a ≤ N := by simpa [N] using Finset.le_sup (f := n) ha
  have hz' : z ∈ ball v (n a : ℤ) := ballNat_mono hna hz
  have hxa' : x - (a : v.adicCompletion F) ∈ ball v (n a : ℤ) := hxa
  have hsum : (x + z) - (a : v.adicCompletion F) ∈ ball v (n a : ℤ) := by
    have heq : (x + z) - (a : v.adicCompletion F) =
        (x - (a : v.adicCompletion F)) + z := by abel
    rw [heq]
    exact ballNat_add (n a) hxa' hz'
  exact hn a hsum

private theorem exists_finite_coset_cover (U : Set (v.adicCompletion F))
    (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ (N : ℕ) (C : Finset (Set (v.adicCompletion F))),
      (∀ S ∈ C, ∃ a ∈ U, S = {z | z - a ∈ ball v (N : ℤ)}) ∧
      U = ⋃ S ∈ C, S := by
  classical
  obtain ⟨N, htrans⟩ := exists_uniform_ball_translation U hUc hUo
  let Usub := {x : v.adicCompletion F // x ∈ U}
  let W : Usub → Set (v.adicCompletion F) := fun a =>
    {z | z - (a : v.adicCompletion F) ∈ ball v (N : ℤ)}
  have hWo (a : Usub) : IsOpen (W a) := by
    dsimp [W]
    exact (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
      (continuous_id.sub continuous_const)
  have hcover : U ⊆ ⋃ a : Usub, W a := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [W, ball]⟩
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover W hWo hcover
  let C := t.image W
  have hrep (S : Set (v.adicCompletion F)) (hS : S ∈ C) :
      ∃ a ∈ U, S = {z | z - a ∈ ball v (N : ℤ)} := by
    rcases Finset.mem_image.mp hS with ⟨a, ha, hEq⟩
    exact ⟨a, a.property, by simpa [W] using hEq.symm⟩
  have hsubset (a : Usub) : W a ⊆ U := by
    intro z hz
    have hzU := htrans a.1 a.property (z - a.1) hz
    simpa using hzU
  refine ⟨N, C, hrep, ?_⟩
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion₂.mp (ht hz) with ⟨a, ha, hza⟩
    exact Set.mem_iUnion₂.mpr ⟨W a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hza⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨S, hS, hzS⟩
    rcases Finset.mem_image.mp hS with ⟨a, ha, hEq⟩
    rw [← hEq] at hzS
    exact hsubset a hzS

private theorem addChar_locallyConstant (A : AddCharData F) :
    IsLocallyConstant (A.ψ v) := by
  obtain ⟨d, hψ, -⟩ := psi_conductor A v
  have hballOpen : IsOpen (ball v (-(d : ℤ))) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  apply (IsLocallyConstant.iff_exists_open (A.ψ v)).mpr
  intro x
  let U := (fun x' : v.adicCompletion F => x' - x) ⁻¹' ball v (-(d : ℤ))
  have hU : IsOpen U := by
    dsimp [U]
    exact hballOpen.preimage (continuous_id.sub continuous_const)
  have hxU : x ∈ U := by
    dsimp [U]
    change x - x ∈ ball v (-(d : ℤ))
    simp only [ball, Int.neg_neg]
    simp
  refine ⟨U, hU, hxU, ?_⟩
  intro x' hx'
  have hdiff : x' - x ∈ ball v (-(d : ℤ)) := by simpa [U] using hx'
  let z := x' - x
  have hz : z ∈ ball v (-(d : ℤ)) := by simpa [z] using hdiff
  have hxEq : x' = x + z := by dsimp [z]; abel
  calc
    A.ψ v x' = A.ψ v (x + z) := by rw [hxEq]
    _ = A.ψ v x * A.ψ v z := AddChar.map_add_eq_mul (A.ψ v) x z
    _ = A.ψ v x := by rw [hψ z hz, mul_one]

private theorem fourierKernel_locallyConstant (T : TorusRep D H v) (A : AddCharData F)
    (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (y : (v.adicCompletion F)ˣ) :
    IsLocallyConstant (fun x => A.ψ v (-x) • φ (x * (y⁻¹ : v.adicCompletion F))) := by
  have hψneg : IsLocallyConstant (fun x : v.adicCompletion F => A.ψ v (-x)) :=
    (addChar_locallyConstant A).comp_continuous continuous_neg
  have hmul : Continuous (fun x : v.adicCompletion F => x * (y⁻¹ : v.adicCompletion F)) :=
    continuous_id.mul continuous_const
  have hφcomp : IsLocallyConstant (fun x : v.adicCompletion F =>
      φ (x * (y⁻¹ : v.adicCompletion F))) := hφ.comp_continuous hmul
  exact hψneg.comp₂ hφcomp (fun a b => a • b)

private theorem fourierKernel_hasCompactSupport (T : TorusRep D H v) (A : AddCharData F)
    (φ : v.adicCompletion F → T.V)
    (hc : HasCompactSupport φ) (y : (v.adicCompletion F)ˣ) :
    HasCompactSupport (fun x => A.ψ v (-x) • φ (x * (y⁻¹ : v.adicCompletion F))) := by
  let c : v.adicCompletion F := (y⁻¹ : (v.adicCompletion F)ˣ)
  have hccomp : HasCompactSupport (fun x : v.adicCompletion F => φ (c • x)) :=
    hc.comp_smul (c := c) (by simp [c])
  have heq : (fun x : v.adicCompletion F => φ (x * (y⁻¹ : v.adicCompletion F))) =
      fun x => φ (c • x) := by
    funext x
    simp [c, smul_eq_mul, mul_comm]
  change IsCompact (tsupport (fun x : v.adicCompletion F =>
    A.ψ v (-x) • φ (x * (y⁻¹ : v.adicCompletion F))))
  rw [show (fun x : v.adicCompletion F => A.ψ v (-x) • φ (x * (y⁻¹ : v.adicCompletion F))) =
      fun x => A.ψ v (-x) • φ (c • x) by
        funext x
        exact congrArg (fun z => A.ψ v (-x) • z) (congrFun heq x)]
  exact HasCompactSupport.smul_left hccomp

private theorem setIntegral_eq_integral_of_zero_off {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (f : X → E) (hzero : ∀ x, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx, hzero x hx]

private theorem indicator_locallyConstant {X E : Type} [TopologicalSpace X] [Zero E]
    (s : Set X) (hsOpen : IsOpen s) (hsClosed : IsClosed s) (f : X → E)
    (hf : IsLocallyConstant f) : IsLocallyConstant (s.indicator f) := by
  apply (IsLocallyConstant.iff_exists_open (s.indicator f)).mpr
  intro x
  by_cases hx : x ∈ s
  · obtain ⟨t, htOpen, hxt, hconst⟩ := hf.exists_open x
    refine ⟨s ∩ t, hsOpen.inter htOpen, ⟨hx, hxt⟩, ?_⟩
    intro y hy
    rcases hy with ⟨hys, hyt⟩
    rw [Set.indicator_of_mem hys, Set.indicator_of_mem hx, hconst y hyt]
  · refine ⟨sᶜ, hsClosed.isOpen_compl, hx, ?_⟩
    intro y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem indicator_hasCompactSupport {X E : Type} [TopologicalSpace X] [R1Space X] [Zero E]
    {s : Set X} (hs : IsCompact s) (f : X → E) : HasCompactSupport (s.indicator f) := by
  apply HasCompactSupport.of_support_subset_isCompact hs
  apply Function.support_subset_iff'.mpr
  intro x hx
  simp [hx]

private theorem locallyConstant_finset_sum {ι X E : Type} [TopologicalSpace X] [AddCommMonoid E]
    (s : Finset ι) (f : ι → X → E)
    (hf : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsLocallyConstant.const (X := X) (0 : E)
  | @insert a s ha ih =>
      have hfa : IsLocallyConstant (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, IsLocallyConstant (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hsum : IsLocallyConstant (fun x => f a x + ∑ i ∈ s, f i x) :=
        hfa.comp₂ (ih hfs) (fun x y => x + y)
      simpa [Finset.sum_insert, ha] using hsum

private theorem addCharIntegral_ball_orthogonal {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (A : AddCharData F) (μ : LocHaar v) (d k : ℕ)
    (htriv : ∀ z ∈ ball v (-(d : ℤ)), A.ψ v z = 1)
    (hbad : ∃ b, b ∈ ball v (-((d : ℤ) + 1)) ∧ A.ψ v b ≠ 1)
    (z : v.adicCompletion F) (x : V) :
    ∫ t in ball v (-((k + d : ℕ) : ℤ)), A.ψ v (z * t) • x ∂μ.μ =
      if z ∈ ball v (k : ℤ) then
        (((μ.μ (ball v (-((k + d : ℕ) : ℤ)))).toReal : ℝ) : ℂ) • x else 0 := by
  classical
  let K := v.adicCompletion F
  let B := ball v (-((k + d : ℕ) : ℤ))
  let vol : ℝ := (μ.μ B).toReal
  letI : ProperSpace K := adicCompletion_properSpace v
  have hBcompact : IsCompact B := by
    simpa [B] using ball_isCompact v (-((k + d : ℕ) : ℤ))
  have hBopen : IsOpen B := by
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hBfinite : μ.μ B < ⊤ := hBcompact.measure_lt_top
  have hBne : 0 < μ.μ B := hBopen.measure_pos μ.μ ⟨0, by simp [B, ball]⟩
  have hvolpos : 0 < vol := by
    dsimp [vol]
    exact ENNReal.toReal_pos hBne.ne' (ne_of_lt hBfinite)
  have hconst (w : V) : ∫ t in B, w ∂μ.μ = (vol : ℂ) • w := by
    rw [setIntegral_const]
    dsimp [vol, Measure.real]
  by_cases hz : z ∈ ball v (k : ℤ)
  · have htrivProd : ∀ t ∈ B, A.ψ v (z * t) = 1 := by
      intro t ht
      have hzval : Valued.v z ≤ WithZero.exp (-(k : ℤ)) := by
        change z ∈ ball v (k : ℤ) at hz
        simp only [ball] at hz
        change Valued.v z ≤ WithZero.exp (-(k : ℤ)) at hz
        exact hz
      have htval : Valued.v t ≤ WithZero.exp ((k + d : ℕ) : ℤ) := by
        change t ∈ ball v (-((k + d : ℕ) : ℤ)) at ht
        simp only [ball, Int.neg_neg] at ht
        change Valued.v t ≤ WithZero.exp ((k + d : ℕ) : ℤ) at ht
        exact ht
      have hprod : Valued.v (z * t) ≤ WithZero.exp (d : ℤ) := by
        calc
          Valued.v (z * t) = Valued.v z * Valued.v t := map_mul _ _ _
          _ ≤ WithZero.exp (-(k : ℤ)) * WithZero.exp ((k + d : ℕ) : ℤ) :=
            mul_le_mul' hzval htval
          _ = WithZero.exp (d : ℤ) := by
            rw [← WithZero.exp_add]
            congr 1
            omega
      apply htriv (z * t)
      change Valued.v (z * t) ≤ WithZero.exp (-(-(d : ℤ)))
      simpa only [Int.neg_neg] using hprod
    calc
      ∫ t in B, A.ψ v (z * t) • x ∂μ.μ = ∫ t in B, x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hBopen.measurableSet] with t ht
        rw [htrivProd t ht]
        simp
      _ = (vol : ℂ) • x := hconst x
      _ = if z ∈ ball v (k : ℤ) then (vol : ℂ) • x else 0 := by simp [hz]
  · obtain ⟨b₀, hb₀, hψb₀⟩ := hbad
    have hz0 : z ≠ 0 := by
      intro hz0
      apply hz
      simp [hz0, ball]
    have hvz : Valued.v z ≠ 0 := by simpa [hz0]
    lift Valued.v z to ℤ using hvz with n hn
    have hnLower : -(k : ℤ) + 1 ≤ n := by
      have hnot : ¬ WithZero.exp n ≤ WithZero.exp (-(k : ℤ)) := by
        intro hle
        apply hz
        change Valued.v z ≤ WithZero.exp (-(k : ℤ))
        rw [← hn]
        exact hle
      have hlt : -(k : ℤ) < n := by
        have h := hnot
        simp only [WithZero.exp_le_exp] at h
        omega
      omega
    let b := b₀ / z
    have hbval₀ : Valued.v b₀ ≤ WithZero.exp ((d : ℤ) + 1) := by
      change b₀ ∈ ball v (-((d : ℤ) + 1)) at hb₀
      simp only [ball, Int.neg_neg] at hb₀
      change Valued.v b₀ ≤ WithZero.exp ((d : ℤ) + 1)
      exact hb₀
    have hbval : Valued.v b ≤ WithZero.exp ((k + d : ℕ) : ℤ) := by
      have hlow : WithZero.exp (-(k : ℤ) + 1) ≤ Valued.v z := by
        rw [← hn]
        exact WithZero.exp_le_exp.mpr hnLower
      have hdenpos : 0 < Valued.v z := by
        rw [← hn]
        exact WithZero.exp_pos
      have hupper : WithZero.exp ((d : ℤ) + 1) ≤
          WithZero.exp ((k + d : ℕ) : ℤ) * Valued.v z := by
        calc
          WithZero.exp ((d : ℤ) + 1) =
              WithZero.exp ((k + d : ℕ) : ℤ) * WithZero.exp (-(k : ℤ) + 1) := by
                rw [← WithZero.exp_add]
                congr 1
                omega
          _ ≤ WithZero.exp ((k + d : ℕ) : ℤ) * Valued.v z := by gcongr
      dsimp [b]
      rw [map_div₀]
      exact (div_le_iff₀ hdenpos).2 (hbval₀.trans hupper)
    have hbB : b ∈ B := by
      change b ∈ ball v (-((k + d : ℕ) : ℤ))
      simp only [B, ball, Int.neg_neg]
      change Valued.v b ≤ WithZero.exp ((k + d : ℕ) : ℤ)
      exact hbval
    have hzb : z * b = b₀ := by
      dsimp [b]
      field_simp [hz0]
    have hψzb : A.ψ v (z * b) ≠ 1 := by simpa [hzb] using hψb₀
    let I : V := ∫ t in B, A.ψ v (z * t) • x ∂μ.μ
    have htrans := integral_comp_addLeft_ball μ (k + d) b hbB
      (fun t => A.ψ v (z * t) • x)
    have hpoint (t : K) : A.ψ v (z * (b + t)) • x =
        A.ψ v (z * b) • (A.ψ v (z * t) • x) := by
      rw [mul_add, AddChar.map_add_eq_mul]
      simp [smul_smul]
    have hfix : I = A.ψ v (z * b) • I := by
      dsimp [I]
      calc
        ∫ t in B, A.ψ v (z * t) • x ∂μ.μ =
            ∫ t in B, A.ψ v (z * (b + t)) • x ∂μ.μ := htrans.symm
        _ = ∫ t in B, A.ψ v (z * b) • (A.ψ v (z * t) • x) ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [] with t
          exact hpoint t
        _ = A.ψ v (z * b) • ∫ t in B, A.ψ v (z * t) • x ∂μ.μ := by
          rw [integral_smul]
    have hmul : (1 - A.ψ v (z * b)) • I = 0 := by
      calc
        (1 - A.ψ v (z * b)) • I = I - A.ψ v (z * b) • I := by
          rw [sub_smul, one_smul]
        _ = 0 := by rw [← hfix]; simp
    have hcoef : 1 - A.ψ v (z * b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hψzb)
    have hI : I = 0 := (smul_eq_zero.mp hmul).resolve_left hcoef
    simp only [if_neg hz]
    change I = 0
    exact hI

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
  have hfgSection : IsSection L T s (f + c • g) := section_add_smul L T s c f g hf hg
  obtain ⟨Nfg, hfg⟩ := jacquet_stable L T A μ s (f + c • g) hfgSection
  obtain ⟨Nf, hfst⟩ := jacquet_stable L T A μ s f hf
  obtain ⟨Ng, hgst⟩ := jacquet_stable L T A μ s g hg
  let N := max (max Nfg Nf) Ng
  have hNfg : Nfg ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNf : Nf ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNg : Ng ≤ N := le_max_right _ _
  rw [← hfg N hNfg, jacquetTrunc_add_smul L T A μ s f g hf hg c N,
    hfst N hNf, hgst N hNg]

/-- **jq:equiv** (10:322–329): `𝒥(π(n(t))f) = ψ(t)𝒥(f)` and `𝒥(π(z(ζ))f) = ζ𝒥(f)`. -/
theorem jacquet_equiv (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) :
    (∀ t, jacquet L A μ (rtr (L.n (Multiplicative.ofAdd t)) f) = A.ψ v t • jacquet L A μ f) ∧
    ∀ ζ, jacquet L A μ (rtr (L.z ζ) f) = ((ζ : ℂˣ) : ℂ) • jacquet L A μ f := by
  constructor
  · intro t
    let n := L.n (Multiplicative.ofAdd t)
    have hft : IsSection L T s (rtr n f) := hf.rtr n
    obtain ⟨Nft, hstft⟩ := jacquet_stable L T A μ s (rtr n f) hft
    obtain ⟨Nf, hstf⟩ := jacquet_stable L T A μ s f hf
    obtain ⟨Nt, htball⟩ := exists_ballNeg_nat t
    let N := max (max Nft Nf) Nt
    have hNft : Nft ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hNf : Nf ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hNt : Nt ≤ N := le_max_right _ _
    have htN : t ∈ ball v (-(N : ℤ)) := ballNeg_nat_mono hNt htball
    calc
      jacquet L A μ (rtr n f) = jacquetTrunc L A μ N (rtr n f) := (hstft N hNft).symm
      _ = A.ψ v t • jacquetTrunc L A μ N f := jacquetTrunc_unipotent L A μ N f t htN
      _ = A.ψ v t • jacquet L A μ f := by rw [hstf N hNf]
  · intro ζ
    have hfζ : IsSection L T s (rtr (L.z ζ) f) := hf.rtr (L.z ζ)
    obtain ⟨Nζ, hstζ⟩ := jacquet_stable L T A μ s (rtr (L.z ζ) f) hfζ
    obtain ⟨Nf, hstf⟩ := jacquet_stable L T A μ s f hf
    let N := max Nζ Nf
    have hNζ : Nζ ≤ N := le_max_left _ _
    have hNf : Nf ≤ N := le_max_right _ _
    calc
      jacquet L A μ (rtr (L.z ζ) f) = jacquetTrunc L A μ N (rtr (L.z ζ) f) :=
        (hstζ N hNζ).symm
      _ = ((ζ : ℂˣ) : ℂ) • jacquetTrunc L A μ N f :=
        jacquetTrunc_central L T A μ s N f hf ζ
      _ = ((ζ : ℂˣ) : ℂ) • jacquet L A μ f := by rw [hstf N hNf]

/-- **jq:bigcell**: the Jacquet integral of a big-cell section on the torus:
`𝒥(π(a(y)) f_φ) = ‖y‖^{1/2-s} σ(a(y⁻¹)) φ̂(y)`, `φ̂(y) = ∫ ψ(-yt) φ(t) dt`. -/
theorem jacquet_bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (y : (v.adicCompletion F)ˣ) :
    jacquet L A μ (rtr (L.a y) (bigCell L T s φ)) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ (∫ t, A.ψ v (-((y : v.adicCompletion F) * t)) • φ t ∂μ.μ) := by
  let K := v.adicCompletion F
  let C : ℂ := ((absFin v (y⁻¹ : Kˣ) : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s)
  have hyInvVal : ((y⁻¹ : Kˣ) : K) = (y : K)⁻¹ := by simp
  let kfun : K → T.V := fun x => A.ψ v (-x) • φ (x * (y : K)⁻¹)
  let σ : T.V →L[ℂ] T.V := (T.σa y⁻¹).toContinuousLinearMap
  have hwa : L.w * L.a y = L.a y⁻¹ * L.w := by
    have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
    calc
      L.w * L.a y = (L.w * L.a y * L.w⁻¹) * L.w := by group
      _ = L.a y⁻¹ * L.w := by rw [L.lift_wa]
  have hgroup (x : K) :
      L.w * L.n (Multiplicative.ofAdd x) * L.a y =
        L.a y⁻¹ * L.w * L.n (Multiplicative.ofAdd (x * (y : K)⁻¹)) := by
    calc
      L.w * L.n (Multiplicative.ofAdd x) * L.a y =
          L.w * (L.n (Multiplicative.ofAdd x) * L.a y) := by simp [mul_assoc]
      _ = L.w * (L.a y * L.n (Multiplicative.ofAdd (x * (y : K)⁻¹))) := by
        rw [L.lift_na]
        rw [hyInvVal]
      _ = (L.w * L.a y) * L.n (Multiplicative.ofAdd (x * (y : K)⁻¹)) := by
        simp [mul_assoc]
      _ = (L.a y⁻¹ * L.w) * L.n (Multiplicative.ofAdd (x * (y : K)⁻¹)) := by rw [hwa]
      _ = L.a y⁻¹ * L.w * L.n (Multiplicative.ofAdd (x * (y : K)⁻¹)) := by simp [mul_assoc]
  have happly (x : K) :
      bigCell L T s φ (L.w * L.n (Multiplicative.ofAdd x) * L.a y) =
        C • T.σa y⁻¹ (φ (x * (y : K)⁻¹)) := by
    rw [hgroup x]
    simpa [C, smul_smul] using
      (bigCell_apply L T s φ 0 (1 : rootsOfUnity 3 ℂ) y⁻¹ (x * (y : K)⁻¹))
  have hpoint (x : K) :
      A.ψ v (-x) • (rtr (L.a y) (bigCell L T s φ))
          (L.w * L.n (Multiplicative.ofAdd x)) = C • σ (kfun x) := by
    change A.ψ v (-x) • bigCell L T s φ
      (L.w * L.n (Multiplicative.ofAdd x) * L.a y) = _
    rw [happly x]
    simp only [kfun, σ, map_smul, smul_smul]
    congr 1
    ring
  have hkLC := fourierKernel_locallyConstant T A φ hφ y
  have hkLC' : IsLocallyConstant kfun := by simpa [kfun, hyInvVal] using hkLC
  have hkCompact := fourierKernel_hasCompactSupport T A φ hc y
  have hkCompact' : HasCompactSupport kfun := by simpa [kfun, hyInvVal] using hkCompact
  have hkCont : Continuous kfun := hkLC'.continuous
  have hkInt : Integrable kfun μ.μ := hkCont.integrable_of_hasCompactSupport hkCompact'
  obtain ⟨N0, hN0⟩ := compact_subset_ballNeg_nat (s := tsupport kfun) hkCompact'
    (fun x => exists_ballNeg_nat x)
  have hkZero {x : K} (hx : x ∉ ball v (-(N0 : ℤ))) : kfun x = 0 := by
    by_contra hne
    have hsupport : x ∈ Function.support kfun := by
      change kfun x ≠ 0
      exact hne
    exact hx (hN0 (subset_tsupport kfun hsupport))
  let Fker : K → T.V := fun x => C • σ (kfun x)
  have hFkerZero {x : K} (hx : x ∉ ball v (-(N0 : ℤ))) : Fker x = 0 := by
    simp [Fker, hkZero hx]
  have hBMOpen (M : ℕ) : IsOpen (ball v (-(M : ℤ))) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have htrunc (M : ℕ) (hM : N0 ≤ M) :
      jacquetTrunc L A μ M (rtr (L.a y) (bigCell L T s φ)) = ∫ x, Fker x ∂μ.μ := by
    have hzeroM {x : K} (hx : x ∉ ball v (-(M : ℤ))) : kfun x = 0 := by
      apply hkZero
      intro hx0
      exact hx (ballNeg_nat_mono hM hx0)
    have hFzeroM {x : K} (hx : x ∉ ball v (-(M : ℤ))) : Fker x = 0 := by
      simp [Fker, hzeroM hx]
    unfold jacquetTrunc
    calc
      ∫ x in ball v (-(M : ℤ)), A.ψ v (-x) •
          (rtr (L.a y) (bigCell L T s φ)) (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ =
        ∫ x in ball v (-(M : ℤ)), Fker x ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
      _ = ∫ x, Fker x ∂μ.μ :=
        setIntegral_eq_integral_of_zero_off (hBMOpen M).measurableSet Fker
          (fun x hx => hFzeroM hx)
  have hfull : (∫ x, Fker x ∂μ.μ) =
      C • σ (∫ x, kfun x ∂μ.μ) := by
    calc
      ∫ x, Fker x ∂μ.μ = C • ∫ x, σ (kfun x) ∂μ.μ := by
        simp only [Fker]
        rw [integral_smul]
      _ = C • σ (∫ x, kfun x ∂μ.μ) := by
        rw [ContinuousLinearMap.integral_comp_comm σ hkInt]
  have hEq : (fun M : ℕ => jacquetTrunc L A μ M
        (rtr (L.a y) (bigCell L T s φ))) =ᶠ[atTop] fun _ => ∫ x, Fker x ∂μ.μ := by
    filter_upwards [eventually_atTop.2 ⟨N0, fun M hM => hM⟩] with M hM
    exact htrunc M hM
  have hlim : Tendsto (fun M : ℕ => jacquetTrunc L A μ M
      (rtr (L.a y) (bigCell L T s φ))) atTop (𝓝 (∫ x, Fker x ∂μ.μ)) :=
    tendsto_const_nhds.congr' hEq.symm
  have hjac : jacquet L A μ (rtr (L.a y) (bigCell L T s φ)) = ∫ x, Fker x ∂μ.μ := by
    change limUnder atTop (fun M : ℕ => jacquetTrunc L A μ M
      (rtr (L.a y) (bigCell L T s φ))) = _
    exact hlim.limUnder_eq
  let q : ℝ := absFin v y
  let fourier : T.V := ∫ t, A.ψ v (-((y : K) * t)) • φ t ∂μ.μ
  have hqpos : 0 < q := by dsimp [q]; exact absFin_pos y.ne_zero
  have hcompose (t : K) : (y : K) * t * (y : K)⁻¹ = t := by
    calc
      (y : K) * t * (y : K)⁻¹ = ((y : K) * (y : K)⁻¹) * t := by ring
      _ = t := by simp
  have hFourier : ∫ t, kfun ((y : K) * t) ∂μ.μ = fourier := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [kfun, fourier]
    rw [hcompose t]
  have hscale := LocHaar.integral_comp_mul μ y kfun
  have hscaleI : (∫ x, kfun x ∂μ.μ) = q • fourier := by
    calc
      ∫ x, kfun x ∂μ.μ = q • (q⁻¹ • ∫ x, kfun x ∂μ.μ) := by
        simp [smul_smul, hqpos.ne']
      _ = q • ∫ t, kfun ((y : K) * t) ∂μ.μ := by rw [← hscale]
      _ = q • fourier := by rw [hFourier]
  have hscaleC : (∫ x, kfun x ∂μ.μ) = (q : ℂ) • fourier := by
    calc
      ∫ x, kfun x ∂μ.μ = q • fourier := hscaleI
      _ = (q : ℂ) • fourier := by
        symm
        exact IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := T.V) q fourier
  have hInv : absFin v (y⁻¹ : Kˣ) = (absFin v y)⁻¹ := by
    have hprod : absFin v y * absFin v (y⁻¹ : Kˣ) = 1 := by
      calc
        absFin v y * absFin v (y⁻¹ : Kˣ) = absFin v (y * y⁻¹) :=
          (absFin_mul v y y⁻¹).symm
        _ = absFin v (1 : K) := by congr 1; simp
        _ = 1 := by
          unfold absFin
          rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
          simp
    have hqinv := eq_inv_of_mul_eq_one_left hprod
    calc
      absFin v (y⁻¹ : Kˣ) = ((absFin v (y⁻¹ : Kˣ))⁻¹)⁻¹ := by simp
      _ = (absFin v y)⁻¹ := by rw [← hqinv]
  have hbase : ((absFin v (y⁻¹ : Kˣ) : ℝ) : ℂ) = (q : ℂ)⁻¹ := by
    dsimp [q]
    exact_mod_cast hInv
  have hqComplex : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hcoef : C * (q : ℂ) = (q : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    have hbasePow : C = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) := by
      dsimp [C]
      rw [hbase, Complex.inv_cpow_ofReal_nonneg hqpos.le ((1 : ℂ) / 2 + s)]
      rw [← Complex.cpow_neg]
    calc
      C * (q : ℂ) = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) * (q : ℂ) := by rw [hbasePow]
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) * (q : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s) + 1) := by
        rw [← Complex.cpow_add _ _ hqComplex]
      _ = (q : ℂ) ^ ((1 : ℂ) / 2 - s) := by congr 1 <;> ring
  calc
    jacquet L A μ (rtr (L.a y) (bigCell L T s φ)) = ∫ x, Fker x ∂μ.μ := hjac
    _ = C • σ (∫ x, kfun x ∂μ.μ) := hfull
    _ = (C * (q : ℂ)) • σ fourier := by
      calc
        _ = C • σ ((q : ℂ) • fourier) := by rw [hscaleC]
        _ = (C * (q : ℂ)) • σ fourier := by rw [map_smul, smul_smul]
    _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ fourier := by
      rw [hcoef]
      simp [q, σ, LinearMap.coe_toContinuousLinearMap']

/-- **jq:fourier-indicator**: every `1_U ⊗ x` (`U` compact open) is a Fourier transform `φ̂`
of a locally constant compactly supported `φ`. C3 of `sol-gate-theta` requires a complete target for
the Bochner integral. -/
theorem exists_fourier_indicator [CompleteSpace V] (A : AddCharData F) (μ : LocHaar v) (U : Set (v.adicCompletion F))
    (hUc : IsCompact U) (hUo : IsOpen U) (x : V) :
    ∃ φ : v.adicCompletion F → V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      ∀ y, ∫ t, A.ψ v (-(y * t)) • φ t ∂μ.μ = U.indicator (fun _ => x) y := by
  classical
  let K := v.adicCompletion F
  letI : ProperSpace K := adicCompletion_properSpace v
  have hzero : HasCompactSupport (fun _ : K => (0 : V)) := by
    exact HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp)
  by_cases hUempty : U = ∅
  · refine ⟨fun _ => 0, IsLocallyConstant.const 0, hzero, ?_⟩
    intro y
    simp [hUempty]
  obtain ⟨d, hψ, hbad⟩ := psi_conductor A v
  obtain ⟨k, cosets, hrep, hUnion⟩ := exists_finite_coset_cover U hUc hUo
  let B := ball v (-((k + d : ℕ) : ℤ))
  let Bsmall := ball v (k : ℤ)
  have hBcompact : IsCompact B := by
    simpa [B] using ball_isCompact v (-((k + d : ℕ) : ℤ))
  have hBopen : IsOpen B := v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hBclosed : IsClosed B := hBcompact.isClosed
  have hBfinite : μ.μ B < ⊤ := hBcompact.measure_lt_top
  have hBnonempty : B.Nonempty := ⟨0, by simp [B, ball]⟩
  have hBpos : 0 < μ.μ B := hBopen.measure_pos μ.μ hBnonempty
  let volR : ℝ := (μ.μ B).toReal
  let volC : ℂ := (volR : ℂ)
  have hvolR : 0 < volR := by
    dsimp [volR]
    exact ENNReal.toReal_pos hBpos.ne' (ne_of_lt hBfinite)
  have hvolC : volC ≠ 0 := by
    change (volR : ℂ) ≠ 0
    exact_mod_cast hvolR.ne'
  let R := {S : Set K // S ∈ cosets}
  have hcenter (S : R) : ∃ a : K, a ∈ U ∧ S.1 = {z | z - a ∈ Bsmall} := by
    exact hrep S.1 S.2
  let anchor : R → K := fun S => Classical.choose (hcenter S)
  have hanchor (S : R) : anchor S ∈ U ∧ S.1 = {z | z - anchor S ∈ Bsmall} :=
    Classical.choose_spec (hcenter S)
  have hsubset (S : R) : S.1 ⊆ U := by
    intro z hz
    rw [hUnion]
    exact Set.mem_iUnion₂.mpr ⟨S.1, S.2, hz⟩
  have hcondition (y : K) (S : R) :
      anchor S - y ∈ Bsmall ↔ y ∈ S.1 := by
    have hS := hanchor S
    constructor
    · intro h
      rw [hS.2]
      simpa [sub_eq_add_neg, add_comm] using ballNat_neg k h
    · intro hy
      rw [hS.2] at hy
      simpa [sub_eq_add_neg, add_comm] using ballNat_neg k hy
  have hunique (y : K) {S S' : R} (hyS : y ∈ S.1) (hyS' : y ∈ S'.1) : S = S' := by
    obtain ⟨-, hS⟩ := hanchor S
    obtain ⟨-, hS'⟩ := hanchor S'
    have hyA : y - anchor S ∈ Bsmall := by rw [hS] at hyS; exact hyS
    have hyA' : y - anchor S' ∈ Bsmall := by rw [hS'] at hyS'; exact hyS'
    apply Subtype.ext
    calc
      S.1 = {z | z - anchor S ∈ Bsmall} := hS
      _ = {z | z - anchor S' ∈ Bsmall} :=
        ballNat_coset_eq k (anchor S) (anchor S') y hyA hyA'
      _ = S'.1 := hS'.symm
  let term : R → K → V := fun S t => B.indicator
    (fun u => A.ψ v (anchor S * u) • x) t
  have htermLC (S : R) : IsLocallyConstant (term S) := by
    have hchar : IsLocallyConstant (fun t : K => A.ψ v (anchor S * t)) :=
      (addChar_locallyConstant A).comp_continuous (continuous_const.mul continuous_id)
    have hvec : IsLocallyConstant (fun t : K => A.ψ v (anchor S * t) • x) :=
      hchar.comp₂ (IsLocallyConstant.const (X := K) x) (fun a b => a • b)
    exact indicator_locallyConstant B hBopen hBclosed _ hvec
  have htermCompact (S : R) : HasCompactSupport (term S) := by
    exact indicator_hasCompactSupport hBcompact
      (fun u => A.ψ v (anchor S * u) • x)
  let total : K → V := fun t => ∑ S ∈ Finset.univ, term S t
  have htotalLC : IsLocallyConstant total := by
    exact locallyConstant_finset_sum (Finset.univ : Finset R) term
      (fun S _ => htermLC S)
  have htotalZero (t : K) (ht : t ∉ B) : total t = 0 := by
    simp [total, term, ht]
  let φ : K → V := fun t => volC⁻¹ • total t
  have hφLC : IsLocallyConstant φ := by
    exact (IsLocallyConstant.const (X := K) (volC⁻¹)).comp₂ htotalLC (fun a b => a • b)
  have hφcompact : HasCompactSupport φ := by
    apply HasCompactSupport.of_support_subset_isCompact hBcompact
    apply Function.support_subset_iff'.mpr
    intro t ht
    simp [φ, htotalZero t ht]
  refine ⟨φ, hφLC, hφcompact, ?_⟩
  intro y
  let fterm : R → K → V := fun S t => A.ψ v (-((y : K) * t)) • term S t
  have hphase : IsLocallyConstant (fun t : K => A.ψ v (-((y : K) * t))) := by
    apply (addChar_locallyConstant A).comp_continuous
    exact continuous_neg.comp (continuous_const.mul continuous_id)
  have hftermLC (S : R) : IsLocallyConstant (fterm S) :=
    hphase.comp₂ (htermLC S) (fun a b => a • b)
  have hftermCompact (S : R) : HasCompactSupport (fterm S) :=
    HasCompactSupport.smul_left (htermCompact S)
  have hftermInt (S : R) : Integrable (fterm S) μ.μ :=
    (hftermLC S).continuous.integrable_of_hasCompactSupport (hftermCompact S)
  have hpointSum :
      (fun t => A.ψ v (-((y : K) * t)) • φ t) =
        fun t => volC⁻¹ • ∑ S ∈ Finset.univ, fterm S t := by
    funext t
    dsimp [φ, total, fterm]
    calc
      _ = volC⁻¹ • (A.ψ v (-((y : K) * t)) •
          ∑ S ∈ Finset.univ, term S t) := by rw [smul_smul, smul_smul, mul_comm]
      _ = volC⁻¹ • ∑ S ∈ Finset.univ,
          A.ψ v (-((y : K) * t)) • term S t := by rw [Finset.smul_sum]
  have hFourierSum :
      ∫ t, A.ψ v (-((y : K) * t)) • φ t ∂μ.μ =
        volC⁻¹ • ∑ S ∈ Finset.univ, ∫ t, fterm S t ∂μ.μ := by
    calc
      ∫ t, A.ψ v (-((y : K) * t)) • φ t ∂μ.μ =
          volC⁻¹ • ∫ t, ∑ S ∈ Finset.univ, fterm S t ∂μ.μ := by
            rw [hpointSum, integral_smul]
      _ = volC⁻¹ • ∑ S ∈ Finset.univ, ∫ t, fterm S t ∂μ.μ := by
            rw [integral_finsetSum Finset.univ (by intro S _; exact hftermInt S)]
  have htermFourier (S : R) :
      ∫ t, fterm S t ∂μ.μ =
        if anchor S - y ∈ Bsmall then volC • x else 0 := by
    let g : K → V := fun t => A.ψ v ((anchor S - y) * t) • x
    have hpoint (t : K) : fterm S t = B.indicator g t := by
      by_cases ht : t ∈ B
      · have hchar : A.ψ v (-((y : K) * t)) * A.ψ v (anchor S * t) =
            A.ψ v ((anchor S - y) * t) := by
          calc
            _ = A.ψ v (-((y : K) * t) + anchor S * t) :=
              (AddChar.map_add_eq_mul (A.ψ v) _ _).symm
            _ = A.ψ v ((anchor S - y) * t) := by congr 1 <;> ring
        simp only [fterm, term, Set.indicator_of_mem ht]
        rw [smul_smul, hchar]
      · simp [fterm, term, g, Set.indicator_of_notMem ht]
    calc
      ∫ t, fterm S t ∂μ.μ = ∫ t, B.indicator g t ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hpoint t
      _ = ∫ t in B, g t ∂μ.μ := integral_indicator hBopen.measurableSet
      _ = if anchor S - y ∈ Bsmall then volC • x else 0 := by
        simpa only [g, B, Bsmall] using
          (addCharIntegral_ball_orthogonal (V := V) A μ d k hψ hbad (anchor S - y) x)
  have hcosetSum :
      ∑ S ∈ Finset.univ, (if anchor S - y ∈ Bsmall then volC • x else 0) =
        volC • U.indicator (fun _ => x) y := by
    by_cases hy : y ∈ U
    · have hyUnion := hUnion ▸ hy
      rcases Set.mem_iUnion₂.mp hyUnion with ⟨S, hS, hyS⟩
      let S₀ : R := ⟨S, hS⟩
      have hyes : anchor S₀ - y ∈ Bsmall := (hcondition y S₀).2 hyS
      have hno (S' : R) (hne : S' ≠ S₀) : ¬ anchor S' - y ∈ Bsmall := by
        intro h
        have hyS' := (hcondition y S').1 h
        exact hne (hunique y hyS' hyS)
      have hsum :
          ∑ S' ∈ Finset.univ, (if anchor S' - y ∈ Bsmall then volC • x else 0) = volC • x := by
        rw [Finset.sum_eq_single_of_mem S₀ (Finset.mem_univ S₀)]
        · simp [hyes]
        · intro S' _ hne
          simp [hno S' hne]
      rw [hsum, Set.indicator_of_mem hy]
    · have hno (S : R) : ¬ anchor S - y ∈ Bsmall := by
        intro h
        exact hy (hsubset S ((hcondition y S).1 h))
      simp [hno, hy]
  rw [hFourierSum]
  have hsumTerms :
      ∑ S ∈ Finset.univ, ∫ t, fterm S t ∂μ.μ =
        ∑ S ∈ Finset.univ, (if anchor S - y ∈ Bsmall then volC • x else 0) := by
    apply Finset.sum_congr rfl
    intro S hS
    exact htermFourier S
  rw [hsumTerms, hcosetSum]
  by_cases hy : y ∈ U
  · rw [Set.indicator_of_mem hy]
    calc
      volC⁻¹ • (volC • x) = (volC⁻¹ * volC) • x := by rw [smul_smul]
      _ = x := by rw [inv_mul_cancel₀ hvolC, one_smul]
  · rw [Set.indicator_of_notMem hy]
    simp

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
  classical
  obtain ⟨φ, hφ, hc, hFourier⟩ :=
    exists_fourier_indicator (A := A) (μ := μ) U hUc hUo x
  refine ⟨φ, hφ, hc, ?_⟩
  intro y
  rw [jacquet_bigCell L T A μ s φ hφ hc y, hFourier (y : v.adicCompletion F)]
  by_cases hy : (y : v.adicCompletion F) ∈ U
  · have hyNorm : absFin v y = 1 := by
      rw [absFin_eq_norm]
      exact Valued.toNormedField.norm_eq_one_iff.mpr (hU1 (y : v.adicCompletion F) hy)
    obtain ⟨c, hc⟩ := hU6 (y : v.adicCompletion F) hy
    have hyEq : y = c ^ 6 := Units.ext hc
    have hσ : T.σa y⁻¹ = LinearMap.id := by
      rw [hyEq]
      have hpow : ((c⁻¹ : (v.adicCompletion F)ˣ) ^ 2) ^ 3 = (c ^ 6)⁻¹ := by
        group
      rw [← hpow]
      exact T.σa_cube (c⁻¹ ^ 2)
    rw [Set.indicator_of_mem hy, hσ]
    simp [hyNorm]
  · rw [Set.indicator_of_notMem hy]
    simp

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
