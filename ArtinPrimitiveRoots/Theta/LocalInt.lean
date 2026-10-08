import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».CoshControl
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».PolynomialControl
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogDerivative
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogProfile
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogBounds
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogSmooth
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import ArtinPrimitiveRoots.Theta.Proofs.TH_JACQUET.SectionLinear
import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage

open MeasureTheory Filter
open Topology

set_option autoImplicit false

open NumberField IsDedekindDomain
open ArtinPrimitiveRoots.Proofs.th_jacquet_p
open scoped Classical Valued

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

private lemma theta_count_spanSingleton_div_localInt (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma theta_count_spanSingleton_eq_neg_log_intValuation_localInt
    (v : FinPlace F) (a : 𝓞 F) (ha : a ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F a)) = -WithZero.log (v.intValuation a) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg ha, WithZero.log_exp]
  ring

private lemma theta_count_spanSingleton_eq_neg_log_valuation_localInt
    (v : FinPlace F) (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    theta_count_spanSingleton_div_localInt v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    theta_count_spanSingleton_eq_neg_log_intValuation_localInt v n hn,
    theta_count_spanSingleton_eq_neg_log_intValuation_localInt v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem theta_valuation_le_one_of_count_spanSingleton_nonneg
    (w : FinPlace F) (x : F) (hx : x ≠ 0)
    (hcount : 0 ≤ FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x)) :
    w.valuation F x ≤ 1 := by
  rw [theta_count_spanSingleton_eq_neg_log_valuation_localInt w x hx] at hcount
  have hxv : w.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  lift w.valuation F x to ℤ using hxv with k hk
  rw [WithZero.log_exp] at hcount
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem psi_global_trace_witness (v : FinPlace F) :
    ∃ z : F, (∀ w : FinPlace F, w ≠ v →
      algebraMap F (w.adicCompletion F) z ∈ w.adicCompletionIntegers F) ∧
      ¬ ∃ n : ℤ, Algebra.trace ℚ F z = (n : ℚ) := by
  let P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := v.asIdeal
  let C : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  let d : ℤ := FractionalIdeal.count F v
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  let n : ℕ := d.toNat + 1
  let J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := (P ^ n)⁻¹
  have hd_nonneg : 0 ≤ d := by
    exact FractionalIdeal.count_coe_nonneg F v (differentIdeal ℤ (𝓞 F))
  have hdiff_ne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hdiff_frac_ne :
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hdiff_ne
  have hdiff_frac :
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = C⁻¹ := by
    simpa [C] using
      (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  have hcountD : FractionalIdeal.count F v
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = d := by
    rfl
  have hcountC : FractionalIdeal.count F v C = -d := by
    have hC : C = (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹ := by
      calc
        C = (C⁻¹)⁻¹ := by simp
        _ = (differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹ := by
          rw [← hdiff_frac]
    rw [hC]
    rw [FractionalIdeal.count_inv, hcountD]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
  have hcountPv : FractionalIdeal.count F v P = 1 := by
    dsimp [P]
    exact FractionalIdeal.count_self F v
  have hcountJv : FractionalIdeal.count F v J = -(n : ℤ) := by
    dsimp [J]
    rw [FractionalIdeal.count_inv, FractionalIdeal.count_pow, hcountPv]
    simp
  have hn_cast : (n : ℤ) = d + 1 := by
    simp [n, Int.toNat_of_nonneg hd_nonneg]
  have hJ_ne : J ≠ 0 := by
    dsimp [J]
    exact inv_ne_zero (pow_ne_zero n hP_ne)
  have hcountJ_away (w : FinPlace F) (hw : w ≠ v) :
      FractionalIdeal.count F w J = 0 := by
    have hcountPw : FractionalIdeal.count F w P = 0 := by
      dsimp [P]
      exact FractionalIdeal.count_maximal_coprime F w hw.symm
    dsimp [J]
    rw [FractionalIdeal.count_inv, FractionalIdeal.count_pow, hcountPw]
    simp
  have hnot_le : ¬ J ≤ C := by
    intro hle
    have hmono := FractionalIdeal.count_mono F v hJ_ne hle
    rw [hcountC, hcountJv] at hmono
    omega
  have hex : ∃ z₀ : F, z₀ ∈ J ∧ z₀ ∉ C := by
    by_contra h
    apply hnot_le
    intro z hz
    by_contra hnot
    exact h ⟨z, hz, hnot⟩
  obtain ⟨z₀, hz₀J, hz₀C⟩ := hex
  have hz₀_ne : z₀ ≠ 0 := by
    intro hz
    subst z₀
    have hzero : (0 : F) ∈ C := by
      change (0 : F) ∈ (C : Submodule (𝓞 F) F)
      exact Submodule.zero_mem _
    exact hz₀C hzero
  have hz₀_not_dual : z₀ ∉
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    simpa [C] using hz₀C
  rw [FractionalIdeal.mem_dual (one_ne_zero :
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0)] at hz₀_not_dual
  push_neg at hz₀_not_dual
  obtain ⟨b, hb, htrace⟩ := hz₀_not_dual
  obtain ⟨a, ha_eq⟩ :=
    (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 F))).mp hb
  have htraceA : Algebra.trace ℚ F (z₀ * algebraMap (𝓞 F) F a) ∉
      (algebraMap ℤ ℚ).range := by
    simpa [Algebra.traceForm_apply, ha_eq] using htrace
  let z : F := z₀ * algebraMap (𝓞 F) F a
  have htraceZ : Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
    simpa [z] using htraceA
  have hnotInt : ¬ ∃ m : ℤ, Algebra.trace ℚ F z = (m : ℚ) := by
    rintro ⟨m, hm⟩
    apply htraceZ
    exact ⟨m, by simpa using hm.symm⟩
  have hz_integral : ∀ w : FinPlace F, w ≠ v →
      algebraMap F (w.adicCompletion F) z ∈ w.adicCompletionIntegers F := by
    intro w hw
    let Sz := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z₀
    have hSz_ne : Sz ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz₀_ne
    have hSz_le : Sz ≤ J :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr hz₀J
    have hcountSz : 0 ≤ FractionalIdeal.count F w Sz := by
      have hmono := FractionalIdeal.count_mono F w hSz_ne hSz_le
      rw [hcountJ_away w hw] at hmono
      exact hmono
    have hz₀val : w.valuation F z₀ ≤ 1 :=
      theta_valuation_le_one_of_count_spanSingleton_nonneg w z₀ hz₀_ne hcountSz
    have haval : w.valuation F (algebraMap (𝓞 F) F a) ≤ 1 :=
      w.valuation_le_one (R := 𝓞 F) (K := F) a
    have hzval : w.valuation F z ≤ 1 := by
      dsimp [z]
      rw [map_mul]
      exact mul_le_one₀ hz₀val zero_le haval
    change ((z : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hzval
  exact ⟨z, hz_integral, hnotInt⟩

/-- **jq:psi-conductor**: `ψ_v` is trivial on `𝔭^{-d}` and not on `𝔭^{-d-1}` for some `d ≥ 0`
(derived from `AddCharData.trivial_on_F` and `integral`). -/
theorem psi_conductor (A : AddCharData F) (v : FinPlace F) :
    ∃ d : ℕ, (∀ x ∈ ball v (-(d : ℤ)), A.ψ v x = 1) ∧
      ∃ x ∈ ball v (-((d : ℤ) + 1)), A.ψ v x ≠ 1 := by
  classical
  rcases psi_global_trace_witness v with ⟨z, hzIntegral, hzNotInt⟩
  have hlocalNontriv : ∃ x : v.adicCompletion F, A.ψ v x ≠ 1 := by
    by_contra h
    have htriv (x : v.adicCompletion F) : A.ψ v x = 1 := by
      by_contra hx
      exact h ⟨x, hx⟩
    have hfinprod :
        (∏ᶠ w : FinPlace F, A.ψ w (algebraMap F (w.adicCompletion F) z)) =
          A.ψ v (algebraMap F (v.adicCompletion F) z) := by
      apply finprod_eq_single
      intro w hw
      exact A.integral w _ (hzIntegral w hw)
    have hglobal := (A.trivial_on_F z).2
    rw [hfinprod] at hglobal
    have hexp : Complex.exp
        (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1 := by
      rw [htriv] at hglobal
      simpa using hglobal
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    have hcoef : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
    have hcancel : (2 * Real.pi * Complex.I : ℂ) *
        (-(Algebra.trace ℚ F z : ℂ)) =
          (2 * Real.pi * Complex.I : ℂ) * (m : ℂ) := by
      calc
        _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by ring
        _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
        _ = (2 * Real.pi * Complex.I : ℂ) * (m : ℂ) := by ring
    have hneg : -(Algebra.trace ℚ F z : ℂ) = (m : ℂ) :=
      mul_left_cancel₀ hcoef hcancel
    have htrace : (Algebra.trace ℚ F z : ℂ) = (-m : ℂ) := by
      calc
        (Algebra.trace ℚ F z : ℂ) = -(-(Algebra.trace ℚ F z : ℂ)) := by ring
        _ = -(m : ℂ) := by rw [hneg]
    have htraceQ : Algebra.trace ℚ F z = (-m : ℚ) := by exact_mod_cast htrace
    exact hzNotInt ⟨-m, htraceQ⟩
  obtain ⟨x, hx⟩ := hlocalNontriv
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    simpa using hx
  have hxVne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  let k : ℤ := WithZero.log (Valued.v x)
  have hxVal : Valued.v x = WithZero.exp k := by
    simpa [k] using (WithZero.exp_log hxVne).symm
  let N : ℕ := Int.toNat (max 0 k)
  have hkN : k ≤ (N : ℤ) := by
    by_cases hk : 0 ≤ k
    · simp [N, max_eq_right hk, Int.toNat_of_nonneg hk]
    · have hkneg : k < 0 := lt_of_not_ge hk
      simp [N, max_eq_left (le_of_lt hkneg)]
      omega
  have hxBall : x ∈ ball v (-(N : ℤ)) := by
    simp only [ball, Set.mem_setOf_eq, neg_neg]
    rw [hxVal]
    exact WithZero.exp_le_exp.mpr (by exact_mod_cast hkN)
  let P : ℕ → Prop := fun r => ∀ y ∈ ball v (-(r : ℤ)), A.ψ v y = 1
  have hP0 : P 0 := by
    intro y hy
    apply A.integral v y
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa [ball] using hy
  have hfail : ∃ r : ℕ, ¬ P r := by
    refine ⟨N, ?_⟩
    intro h
    exact hx (h x hxBall)
  let n : ℕ := Nat.find hfail
  have hnfail : ¬ P n := by simpa [n] using Nat.find_spec hfail
  have hmin (r : ℕ) (hr : r < n) : P r := by
    by_contra hnot
    have hle : Nat.find hfail ≤ r := Nat.find_min' hfail hnot
    omega
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : Nat.find hfail = 0 := by
      simpa [n] using (show n = 0 by omega)
    apply hnfail
    simpa [n, hn0] using hP0
  let d : ℕ := n - 1
  have hdAdd : d + 1 = n := Nat.sub_add_cancel hnpos
  have hPd : P d := hmin d (by omega)
  have hbad : ∃ y : v.adicCompletion F,
      y ∈ ball v (-(n : ℤ)) ∧ A.ψ v y ≠ 1 := by
    by_contra h
    apply hnfail
    intro y hy
    by_contra hψ
    exact h ⟨y, hy, hψ⟩
  refine ⟨d, ?_, ?_⟩
  · intro y hy
    exact hPd y hy
  · obtain ⟨y, hyBall, hyNot⟩ := hbad
    refine ⟨y, ?_, hyNot⟩
    have hcast : (n : ℤ) = (d : ℤ) + 1 := by exact_mod_cast hdAdd.symm
    simpa only [hcast] using hyBall

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

private theorem exists_near_one_sixth_power (v : FinPlace F) :
    ∃ m : ℕ, ∀ u : (v.adicCompletion F)ˣ,
      ((u : v.adicCompletion F) - 1) ∈ ball v (m : ℤ) → ∃ a, u = a ^ 6 := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  letI : NormedField K := inferInstance
  let f : K → K := fun x => x ^ 6
  have hderiv : HasStrictDerivAt f (6 : K) 1 := by
    simpa [f] using (hasStrictDerivAt_pow 6 (1 : K))
  have h6 : (6 : K) ≠ 0 := by norm_num
  let hf := hderiv.hasStrictFDerivAt_equiv h6
  let e := hf.toOpenPartialHomeomorph f
  have h1source : (1 : K) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  have h1target : (1 : K) ∈ e.target := by
    have h := e.map_source h1source
    simpa [e, f] using h
  have hopen : IsOpen e.target := e.open_target
  obtain ⟨m, hm⟩ := exists_ballTranslate_subset hopen h1target
  refine ⟨m, ?_⟩
  intro u hu
  have htarget : (u : K) ∈ e.target := hm hu
  have hroot : f (e.symm (u : K)) = (u : K) := by
    simpa [e] using e.right_inv htarget
  have hroot_ne : e.symm (u : K) ≠ 0 := by
    intro hz
    apply u.ne_zero
    rw [← hroot]
    simp [f, hz]
  refine ⟨Units.mk0 (e.symm (u : K)) hroot_ne, ?_⟩
  apply Units.ext
  change (u : K) = f (e.symm (u : K))
  exact hroot.symm

private theorem jacquet_ballNeg_nat_add (N : ℕ) {x y : v.adicCompletion F}
    (hx : x ∈ ball v (-(N : ℤ))) (hy : y ∈ ball v (-(N : ℤ))) :
    x + y ∈ ball v (-(N : ℤ)) := by
  simp only [ball, Int.neg_neg] at hx hy ⊢
  exact (Valued.v.map_add_le_max' x y).trans (max_le hx hy)

private theorem jacquet_ballNeg_nat_neg (N : ℕ) {x : v.adicCompletion F}
    (hx : x ∈ ball v (-(N : ℤ))) : -x ∈ ball v (-(N : ℤ)) := by
  simp only [ball, Int.neg_neg, Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.map_neg]
  exact hx

private theorem jacquet_inv_mem_ball_of_not_mem {N : ℕ} {x : v.adicCompletion F}
    (hx : x ∉ ball v (-(N : ℤ))) : x⁻¹ ∈ ball v (N : ℤ) := by
  have hx0 : x ≠ 0 := by
    intro h
    apply hx
    simp [h, ball]
  have hvx : Valued.v x ≠ 0 := by simpa [hx0]
  have hlarge : WithZero.exp (N : ℤ) < Valued.v x := by
    apply lt_of_not_ge
    intro hle
    apply hx
    simpa only [ball, Int.neg_neg, Set.mem_setOf_eq] using hle
  have hxvpos : 0 < Valued.v x := WithZero.exp_pos.trans hlarge
  have hinv : (Valued.v x)⁻¹ < (WithZero.exp (N : ℤ))⁻¹ :=
    (inv_lt_inv₀ hxvpos WithZero.exp_pos).2 hlarge
  change Valued.v x⁻¹ ≤ WithZero.exp (-(N : ℤ))
  rw [show Valued.v x⁻¹ = (Valued.v x)⁻¹ by simp]
  exact le_of_lt (hinv.trans_eq (by simp))

private theorem jacquet_ball_mul {m n : ℤ} {x y : v.adicCompletion F}
    (hx : x ∈ ball v m) (hy : y ∈ ball v n) : x * y ∈ ball v (m + n) := by
  simp only [ball, Set.mem_setOf_eq] at hx hy ⊢
  rw [map_mul]
  calc
    Valued.v x * Valued.v y ≤ WithZero.exp (-m) * WithZero.exp (-n) := mul_le_mul' hx hy
    _ = WithZero.exp (-(m + n)) := by rw [← WithZero.exp_add]; congr 1 <;> ring

private theorem jacquet_integral_comp_addLeft_set (μ : LocHaar v) (b : v.adicCompletion F)
    (S : Set (v.adicCompletion F)) (hS : MeasurableSet S)
    (hpre : (MeasurableEquiv.addLeft b) ⁻¹' S = S)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : v.adicCompletion F → E) :
    ∫ x in S, f (b + x) ∂μ.μ = ∫ x in S, f x ∂μ.μ := by
  let e : v.adicCompletion F ≃ᵐ v.adicCompletion F := MeasurableEquiv.addLeft b
  have hmap := e.restrict_map μ.μ S
  have htrans : Measure.map e μ.μ = μ.μ := by
    simpa [e] using Measure.IsAddLeftInvariant.map_add_left_eq_self b
  rw [htrans, hpre] at hmap
  have hpres : MeasurePreserving e (μ.μ.restrict S) (μ.μ.restrict S) :=
    ⟨e.measurable, hmap.symm⟩
  change ∫ x, f (e x) ∂(μ.μ.restrict S) = ∫ x, f x ∂(μ.μ.restrict S)
  exact MeasurePreserving.integral_comp' hpres f

private theorem jacquet_section_w_n_formula (L : FinLocalCover D H v) (T : TorusRep D H v)
    (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) (mf : ℕ)
    (hmf : L.m0 ≤ mf) (hK : ∀ g, ∀ k ∈ L.Kc mf, f (g * k) = f g)
    (x : v.adicCompletion F) (hx : x ≠ 0) (hxInv : x⁻¹ ∈ ball v (mf : ℤ)) :
    f (L.w * L.n (Multiplicative.ofAdd x)) =
      ((absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) (f 1) := by
  let X : (v.adicCompletion F)ˣ := Units.mk0 x hx
  let y : (v.adicCompletion F)ˣ := -(X⁻¹ * X⁻¹)
  have hBruhat : L.w * L.n (Multiplicative.ofAdd x) =
      L.n (Multiplicative.ofAdd (x⁻¹)) * L.a y *
        L.nbar (Multiplicative.ofAdd (x⁻¹)) := by
    simpa [X, y] using L.lift_wn X
  have hbarK : L.nbar (Multiplicative.ofAdd (x⁻¹)) ∈ L.Kc mf :=
    L.nbar_Kc mf hmf x⁻¹ hxInv
  have hright : f (L.nbar (Multiplicative.ofAdd (x⁻¹))) = f 1 := by
    simpa using hK 1 (L.nbar (Multiplicative.ofAdd (x⁻¹))) hbarK
  calc
    f (L.w * L.n (Multiplicative.ofAdd x)) =
        f (L.n (Multiplicative.ofAdd (x⁻¹)) * L.a y *
          L.nbar (Multiplicative.ofAdd (x⁻¹))) := by rw [hBruhat]
    _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa y (f (L.nbar (Multiplicative.ofAdd (x⁻¹)))) := hf.1 _ _ _
    _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (f 1) := by rw [hright]

set_option maxHeartbeats 5000000 in
theorem jacquet_stable (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → jacquetTrunc L A μ N f = jacquet L A μ f := by
  classical
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  letI : NormedField K := inferInstance
  obtain ⟨d, hψ, hbad⟩ := psi_conductor A v
  obtain ⟨mf, hmf, hK⟩ := hf.2.2
  obtain ⟨m6, hsix⟩ := exists_near_one_sixth_power v
  let M := max mf m6
  let N0 := M + d + 1
  let B0 : Set K := ball v (-(N0 : ℤ))
  let kfun : K → T.V := fun x => A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x))
  have hzeroB0 : (0 : K) ∈ B0 := by
    change (0 : K) ∈ {z : K | Valued.v z ≤ WithZero.exp (N0 : ℤ)}
    exact Set.mem_setOf_eq.mpr (by simp)
  have hmfM : mf ≤ M := le_max_left _ _
  have hm6M : m6 ≤ M := le_max_right _ _
  have hmfN0 : mf ≤ N0 := by dsimp [N0]; omega
  have hdN0 : d + 1 ≤ N0 := by dsimp [N0]; omega
  obtain ⟨b, hb, hψb⟩ := hbad
  have hb' : b ∈ ball v (-((d + 1 : ℕ) : ℤ)) := by simpa using hb
  have hb0 : b ∈ B0 := by
    dsimp [B0]
    exact ballNeg_nat_mono (by dsimp [N0]; omega) hb'
  have hψneg : A.ψ v (-b) ≠ 1 := by
    rw [AddChar.map_neg_eq_inv]
    exact inv_ne_one.mpr hψb
  have hB0iff (x : K) : b + x ∈ B0 ↔ x ∈ B0 := by
    constructor
    · intro hx
      have hsum := jacquet_ballNeg_nat_add N0
        (jacquet_ballNeg_nat_neg N0 hb0) hx
      simpa [add_assoc] using hsum
    · intro hx
      exact jacquet_ballNeg_nat_add N0 hb0 hx
  have hpreB0 : (MeasurableEquiv.addLeft b) ⁻¹' B0 = B0 := by
    ext x
    change b + x ∈ B0 ↔ x ∈ B0
    exact hB0iff x
  have hB0open : IsOpen B0 := by
    dsimp [B0]
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hB0meas : MeasurableSet B0 := hB0open.measurableSet
  have hBigInt (N : ℕ) : IntegrableOn kfun (ball v (-(N : ℤ))) μ.μ := by
    exact jacquetKernel_integrableOn L T A μ s f hf N
  have hAnnulusZero (N : ℕ) (hN : N0 ≤ N) :
      ∫ x in ball v (-(N : ℤ)) \ B0, kfun x ∂μ.μ = 0 := by
    let BN : Set K := ball v (-(N : ℤ))
    let S : Set K := BN \ B0
    have hbN : b ∈ BN := by
      dsimp [BN]
      exact ballNeg_nat_mono hN hb0
    have hpreBN : (MeasurableEquiv.addLeft b) ⁻¹' BN = BN := by
      ext x
      change b + x ∈ BN ↔ x ∈ BN
      constructor
      · intro hx
        have hsum := jacquet_ballNeg_nat_add N
          (jacquet_ballNeg_nat_neg N hbN) hx
        simpa [BN, add_assoc] using hsum
      · intro hx
        exact jacquet_ballNeg_nat_add N hbN hx
    have hpreS : (MeasurableEquiv.addLeft b) ⁻¹' S = S := by
      change (MeasurableEquiv.addLeft b) ⁻¹' (BN \ B0) = BN \ B0
      rw [Set.preimage_sdiff, hpreBN, hpreB0]
    have hBNopen : IsOpen BN := by
      dsimp [BN]
      exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
    have hSmeas : MeasurableSet S := hBNopen.measurableSet.diff hB0meas
    let I : T.V := ∫ x in S, kfun x ∂μ.μ
    have hsectionAdd (x : K) (hxS : x ∈ S) :
        f (L.w * L.n (Multiplicative.ofAdd (b + x))) =
          f (L.w * L.n (Multiplicative.ofAdd x)) := by
      have hxNot : x ∉ B0 := (Set.mem_sdiff x).mp hxS |>.2
      have hx'Not : b + x ∉ B0 := by
        intro hx'
        exact hxNot ((hB0iff x).mp hx')
      have hx0 : x ≠ 0 := by
        intro hx
        exact hxNot (by simpa [hx] using hzeroB0)
      have hx'0 : b + x ≠ 0 := by
        intro hx
        exact hx'Not (by simpa [hx] using hzeroB0)
      have hxInvN0 : x⁻¹ ∈ ball v (N0 : ℤ) := by
        simpa [B0] using jacquet_inv_mem_ball_of_not_mem hxNot
      have hx'InvN0 : (b + x)⁻¹ ∈ ball v (N0 : ℤ) := by
        simpa [B0] using jacquet_inv_mem_ball_of_not_mem hx'Not
      have hxInvM : x⁻¹ ∈ ball v (mf : ℤ) := ballNat_mono hmfN0 hxInvN0
      have hx'InvM : (b + x)⁻¹ ∈ ball v (mf : ℤ) := ballNat_mono hmfN0 hx'InvN0
      have hbval : Valued.v b ≤ WithZero.exp (N0 : ℤ) := by
        simpa [B0, ball, Int.neg_neg] using hb0
      have hxvalnot : ¬ Valued.v x ≤ WithZero.exp (N0 : ℤ) := by
        intro hxval
        have hxB0 : x ∈ B0 := by
          change x ∈ {z : K | Valued.v z ≤ WithZero.exp (N0 : ℤ)}
          exact Set.mem_setOf_eq.mpr hxval
        exact hxNot hxB0
      have hvalb_lt : Valued.v b < Valued.v x := lt_of_le_of_lt hbval (lt_of_not_ge hxvalnot)
      have hvalSumLe : Valued.v (b + x) ≤ Valued.v x := by
        calc
          Valued.v (b + x) ≤ max (Valued.v b) (Valued.v x) := Valued.v.map_add_le_max' b x
          _ = Valued.v x := max_eq_right (le_of_lt hvalb_lt)
      have hvalXLe : Valued.v x ≤ Valued.v (b + x) := by
        by_contra hnot
        have hlt : Valued.v (b + x) < Valued.v x := lt_of_not_ge hnot
        have htriangle : Valued.v x ≤ max (Valued.v (b + x)) (Valued.v b) := by
          calc
            Valued.v x = Valued.v ((b + x) + (-b)) := by congr 1 <;> abel
            _ ≤ max (Valued.v (b + x)) (Valued.v (-b)) := Valued.v.map_add_le_max' _ _
            _ = max (Valued.v (b + x)) (Valued.v b) := by rw [Valuation.map_neg]
        exact (not_lt_of_ge htriangle) (max_lt hlt hvalb_lt)
      have hnormSum : ‖b + x‖ = ‖x‖ := by
        apply le_antisymm
        · exact Valued.toNormedField.norm_le_iff.mpr hvalSumLe
        · exact Valued.toNormedField.norm_le_iff.mpr hvalXLe
      let X : Kˣ := Units.mk0 x hx0
      let X' : Kˣ := Units.mk0 (b + x) hx'0
      let u : Kˣ := X' * X⁻¹
      have hXnorm : ‖(X' : K)‖ = ‖(X : K)‖ := by
        change ‖b + x‖ = ‖x‖
        exact hnormSum
      have hUcast : (u : K) = (X' : K) * ((X⁻¹ : Kˣ) : K) := rfl
      have huabs : absFin v u = 1 := by
        rw [absFin_eq_norm, hUcast, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hXnorm]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr X.ne_zero)
      have hUval : (u : K) = 1 + b * x⁻¹ := by
        dsimp [u, X, X']
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp [hx0]
        ring
      have hbInvM : b * x⁻¹ ∈ ball v (M : ℤ) := by
        have hmul := jacquet_ball_mul hb' hxInvN0
        have hrad : -((d + 1 : ℕ) : ℤ) + (N0 : ℤ) = (M : ℤ) := by
          dsimp [N0]
          push_cast
          ring
        rw [hrad] at hmul
        exact hmul
      have huNear : (u : K) - 1 ∈ ball v (m6 : ℤ) := by
        have hdiff : (u : K) - 1 = b * x⁻¹ := by rw [hUval]; ring
        rw [hdiff]
        exact ballNat_mono hm6M hbInvM
      obtain ⟨a, ha⟩ := hsix u huNear
      have hX'Eq : X' = u * X := by
        dsimp [u]
        group
      let Y : Kˣ := -(X⁻¹ * X⁻¹)
      let Y' : Kˣ := -((X'⁻¹) * (X'⁻¹))
      have hYrel : Y' = Y * ((u ^ 2)⁻¹) := by
        apply Units.ext
        change -(((X'⁻¹ : Kˣ) : K) * ((X'⁻¹ : Kˣ) : K)) =
          -(((X⁻¹ : Kˣ) : K) * ((X⁻¹ : Kˣ) : K)) * (((u ^ 2)⁻¹ : Kˣ) : K)
        rw [hX'Eq]
        simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val]
        field_simp
      have huNorm : ‖(u : K)‖ = 1 := by
        calc
          ‖(u : K)‖ = absFin v u := (absFin_eq_norm v _).symm
          _ = 1 := huabs
      have hu2abs : absFin v (((u ^ 2)⁻¹ : Kˣ) : K) = 1 := by
        calc
          absFin v (((u ^ 2)⁻¹ : Kˣ) : K) = ‖(((u ^ 2)⁻¹ : Kˣ) : K)‖ := absFin_eq_norm v _
          _ = ‖((u ^ 2 : Kˣ) : K)‖⁻¹ := by simp [norm_inv]
          _ = (‖(u : K)‖ ^ 2)⁻¹ := by simp [norm_pow]
          _ = 1 := by rw [huNorm]; norm_num
      have hYabs : absFin v Y' = absFin v Y := by
        rw [absFin_eq_norm, absFin_eq_norm]
        simp [Y, Y', norm_neg, norm_mul, norm_inv, Units.val_neg, Units.val_mul,
          Units.val_inv_eq_inv_val, hXnorm]
      have huInvSix : ∃ c : Kˣ, ((u ^ 2)⁻¹ : Kˣ) = c ^ 6 := by
        refine ⟨(a⁻¹) ^ 2, ?_⟩
        rw [ha]
        group
      have hHilbOpp : H.hilb v ((u ^ 2)⁻¹) Y = 1 :=
        H.sixth_power v ((u ^ 2)⁻¹) Y huInvSix
      have hHilb : H.hilb v Y ((u ^ 2)⁻¹) = 1 := by
        have hskew := H.skew v Y ((u ^ 2)⁻¹)
        rw [hHilbOpp] at hskew
        simpa using hskew
      have huInvCube : (u ^ 2)⁻¹ = ((a⁻¹) ^ 4) ^ 3 := by
        rw [ha]
        group
      have hσCube : T.σa ((u ^ 2)⁻¹) = LinearMap.id := by
        rw [huInvCube]
        exact T.σa_cube ((a⁻¹) ^ 4)
      have hσ : T.σa (Y * ((u ^ 2)⁻¹)) = T.σa Y := by
        have hmul := T.σa_mul Y ((u ^ 2)⁻¹)
        rw [hσCube, hHilb] at hmul
        simpa [muThree] using hmul.symm
      have hformX := jacquet_section_w_n_formula L T s f hf mf hmf hK x hx0 hxInvM
      have hformX' := jacquet_section_w_n_formula L T s f hf mf hmf hK (b + x) hx'0 hx'InvM
      have hformXeq :
          f (L.w * L.n (Multiplicative.ofAdd x)) =
            ((absFin v Y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa Y (f 1) := by
        simpa [X, Y] using hformX
      have hformX'eq :
          f (L.w * L.n (Multiplicative.ofAdd (b + x))) =
            ((absFin v Y' : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa Y' (f 1) := by
        simpa [X', Y'] using hformX'
      calc
        f (L.w * L.n (Multiplicative.ofAdd (b + x))) =
            ((absFin v Y' : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa Y' (f 1) := hformX'eq
        _ = ((absFin v Y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa Y (f 1) := by
          rw [hYabs, hYrel, hσ]
        _ = f (L.w * L.n (Multiplicative.ofAdd x)) := hformXeq.symm
    have hphase (x : K) : A.ψ v (-(b + x)) = A.ψ v (-b) * A.ψ v (-x) := by
      have harg : -(b + x) = -b + -x := by abel
      rw [harg, AddChar.map_add_eq_mul]
    have hpoint (x : K) (hxS : x ∈ S) :
        kfun (b + x) = A.ψ v (-b) • kfun x := by
      dsimp [kfun]
      rw [hphase x, ← ofAdd_add, hsectionAdd x hxS]
      simp [smul_smul]
    have hfix : I = A.ψ v (-b) • I := by
      dsimp [I]
      calc
        ∫ x in S, kfun x ∂μ.μ = ∫ x in S, kfun (b + x) ∂μ.μ :=
          (jacquet_integral_comp_addLeft_set μ b S hSmeas hpreS kfun).symm
        _ = ∫ x in S, A.ψ v (-b) • kfun x ∂μ.μ := by
          apply setIntegral_congr_fun hSmeas
          intro x hxS
          exact hpoint x hxS
        _ = A.ψ v (-b) • ∫ x in S, kfun x ∂μ.μ := by rw [integral_smul]
    have hmul : (1 - A.ψ v (-b)) • I = 0 := by
      calc
        (1 - A.ψ v (-b)) • I = I - A.ψ v (-b) • I := by rw [sub_smul, one_smul]
        _ = 0 := by rw [← hfix]; simp
    have hcoef : 1 - A.ψ v (-b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hψneg)
    have hI : I = 0 := (smul_eq_zero.mp hmul).resolve_left hcoef
    simpa [I, S, BN] using hI
  have htrunc (N : ℕ) (hN : N0 ≤ N) :
      jacquetTrunc L A μ N f = jacquetTrunc L A μ N0 f := by
    let BN : Set K := ball v (-(N : ℤ))
    have hsubset : B0 ⊆ BN := by
      dsimp [B0, BN]
      exact ballNeg_nat_mono hN
    have hdiff : ∫ x in BN, kfun x ∂μ.μ = ∫ x in B0, kfun x ∂μ.μ := by
      have htail := hAnnulusZero N hN
      have hset := setIntegral_sdiff hB0meas (hBigInt N) hsubset
      rw [hset] at htail
      exact sub_eq_zero.mp htail
    unfold jacquetTrunc
    change ∫ x in BN, kfun x ∂μ.μ = ∫ x in B0, kfun x ∂μ.μ
    exact hdiff
  have hev :
      (fun N : ℕ => jacquetTrunc L A μ N f) =ᶠ[atTop]
        fun _ => jacquetTrunc L A μ N0 f := by
    filter_upwards [eventually_atTop.2 ⟨N0, fun N hN => hN⟩] with N hN
    exact htrunc N hN
  have hlim : Tendsto (fun N : ℕ => jacquetTrunc L A μ N f) atTop
      (𝓝 (jacquetTrunc L A μ N0 f)) := tendsto_const_nhds.congr' hev.symm
  refine ⟨N0, ?_⟩
  intro N hN
  calc
    jacquetTrunc L A μ N f = jacquetTrunc L A μ N0 f := htrunc N hN
    _ = jacquet L A μ f := by
      change jacquetTrunc L A μ N0 f =
        limUnder atTop (fun N : ℕ => jacquetTrunc L A μ N f)
      exact hlim.limUnder_eq.symm
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

private theorem torus_sigma_uniform_bound (T : TorusRep D H v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u (x : T.V), ‖T.σa u x‖ ≤ C * ‖x‖ := by
  classical
  let normOp : (T.V →ₗ[ℂ] T.V) → ℝ := fun f => ‖f.toContinuousLinearMap‖
  let opNorm : (v.adicCompletion F)ˣ → ℝ := fun u => normOp (T.σa u)
  have hfinite : (Set.range opNorm).Finite := by
    rw [Set.range_comp' normOp T.σa]
    exact T.σa_finite.image normOp
  have hbounded : BddAbove (Set.range opNorm) := hfinite.bddAbove
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u x
  have hle : opNorm u ≤ C := hC ⟨u, rfl⟩
  calc
    ‖T.σa u x‖ ≤ opNorm u * ‖x‖ := (T.σa u).toContinuousLinearMap.le_opNorm x
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg x)
    _ ≤ max C 0 * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

private def jacquetUnitShell (v : FinPlace F) : Set (v.adicCompletion F) :=
  {x | absFin v x = 1}

private def jacquetShell (v : FinPlace F) (k : ℤ) : Set (v.adicCompletion F) :=
  Set.image (fun x : v.adicCompletion F =>
    ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)
    (jacquetUnitShell v)

private theorem jacquetUnitShell_compact (v : FinPlace F) : IsCompact (jacquetUnitShell v) := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  letI : ProperSpace K := adicCompletion_properSpace v
  have hO : (O : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hOcomp : IsCompact (O : Set K) := by
    rw [hO]
    exact isCompact_closedBall 0 1
  have hnormcont : Continuous (fun x : K => absFin v x) := by
    simpa only [absFin_eq_norm] using (continuous_norm : Continuous fun x : K => ‖x‖)
  have hclosed : IsClosed (jacquetUnitShell v) := isClosed_singleton.preimage hnormcont
  have hsub : jacquetUnitShell v ⊆ (O : Set K) := by
    intro x hx
    rw [hO, Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm, hx]
  exact hOcomp.of_isClosed_subset hclosed hsub

private theorem jacquetShell_compact (v : FinPlace F) (k : ℤ) :
    IsCompact (jacquetShell v k) := by
  apply (jacquetUnitShell_compact v).image
  fun_prop

private theorem jacquet_unifLoc_valuation (v : FinPlace F) :
    Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  have hπcoerce : (unifLoc v : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (unif (F := F) v) := by
    simp [unifLoc, toLoc]
  rw [hπcoerce]
  change Valued.v ((unif (F := F) v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec

private theorem jacquetShell_radius (v : FinPlace F) (k : ℤ) :
    absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  let π := unifLoc v
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hπ : absFin v (π : v.adicCompletion F) = q⁻¹ := by
    rw [absFin_eq_norm, FinitePlace.norm_def]
    unfold q
    rw [jacquet_unifLoc_valuation]
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
    rw [WithZero.toAdd_unzero_eq_log (by simp)]
    simp
  calc
    absFin v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        ‖((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ := absFin_eq_norm v _
    _ = ‖(π : v.adicCompletion F)‖ ^ k := by simp
    _ = (q⁻¹) ^ k := by rw [← absFin_eq_norm, hπ]
    _ = q ^ (-k) := by rw [inv_zpow, zpow_neg]

private theorem jacquetShell_mem_radius (v : FinPlace F) (k : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ jacquetShell v k) :
    absFin v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rcases hx with ⟨u, hu, rfl⟩
  calc
    absFin v (((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) =
        absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * absFin v u := by
          simp only [absFin_eq_norm, norm_mul]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
      rw [hu, jacquetShell_radius]
      ring

private theorem jacquetShell_valuation (v : FinPlace F) (k : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ jacquetShell v k) :
    Valued.v x = WithZero.exp (-k) := by
  rcases hx with ⟨u, hu, rfl⟩
  have hnorm : ‖u‖ = 1 := by rw [← absFin_eq_norm]; exact hu
  have huval : Valued.v u = 1 := Valued.toNormedField.norm_eq_one_iff.mp hnorm
  calc
    Valued.v (((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) =
        Valued.v (unifLoc v : v.adicCompletion F) ^ k * Valued.v u := by simp
    _ = WithZero.exp (-1 : ℤ) ^ k := by rw [jacquet_unifLoc_valuation, huval]; simp
    _ = WithZero.exp (-k) := by
      rw [← WithZero.exp_zsmul]
      rw [show k • (-1 : ℤ) = -k by ring]

private theorem jacquetUnitShell_real_measure_le_one (v : FinPlace F) (μ : LocHaar v) :
    μ.μ.real (jacquetUnitShell v) ≤ 1 := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have hO : (O : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hsub : jacquetUnitShell v ⊆ (O : Set K) := by
    intro x hx
    rw [hO, Metric.mem_closedBall, dist_zero_right, ← absFin_eq_norm, hx]
  have hfinite : μ.μ (O : Set K) ≠ ⊤ := by rw [μ.norm_O]; simp
  calc
    μ.μ.real (jacquetUnitShell v) ≤ μ.μ.real (O : Set K) := measureReal_mono hsub hfinite
    _ = 1 := by
      change (μ.μ (O : Set K)).toReal = 1
      rw [μ.norm_O]
      simp

private theorem jacquetShell_cover (v : FinPlace F) {x : v.adicCompletion F} (hx : x ≠ 0) :
    ∃ k : ℤ, x ∈ jacquetShell v k := by
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
  have huval : Valued.v u = 1 := by
    dsimp [u]
    calc
      Valued.v (((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) =
          Valued.v (π : v.adicCompletion F) ^ (-n) * Valued.v x := by simp
      _ = WithZero.exp (-1 : ℤ) ^ (-n) * WithZero.exp (-n) := by
        rw [jacquet_unifLoc_valuation, hxval]
      _ = 1 := by
        rw [← WithZero.exp_zsmul]
        rw [show (-n : ℤ) • (-1 : ℤ) = n by simp, ← WithZero.exp_add]
        simp
  have hu : absFin v u = 1 := by
    rw [absFin_eq_norm, FinitePlace.norm_def, huval]
    simp
  refine ⟨n, ⟨u, hu, ?_⟩⟩
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

private theorem jacquet_integral_indicator_one (μ : LocHaar v) {U : Set (v.adicCompletion F)}
    (hU : MeasurableSet U) :
    ∫ x, U.indicator (fun _ : v.adicCompletion F => (1 : ℝ)) x ∂μ.μ = μ.μ.real U := by
  rw [integral_indicator hU]
  simp [Measure.real, setIntegral_const]

private theorem jacquetShell_real_measure (μ : LocHaar v) (k : ℤ) :
    μ.μ.real (jacquetShell v k) =
      absFin v ((unifLoc v ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        μ.μ.real (jacquetUnitShell v) := by
  let K := v.adicCompletion F
  let a : Kˣ := unifLoc v ^ k
  let U := jacquetUnitShell v
  have hU : MeasurableSet U := (jacquetUnitShell_compact v).measurableSet
  have hS : MeasurableSet (jacquetShell v k) := (jacquetShell_compact v k).measurableSet
  have hpre : (fun x : K => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' U = jacquetShell v k := by
    ext x
    change ((a⁻¹ : Kˣ) : K) * x ∈ U ↔
      ∃ y ∈ U, ((a : Kˣ) : K) * y = x
    constructor
    · intro hx
      refine ⟨((a⁻¹ : Kˣ) : K) * x, hx, ?_⟩
      calc
        ((a : Kˣ) : K) * (((a⁻¹ : Kˣ) : K) * x) =
            (((a : Kˣ) : K) * ((a⁻¹ : Kˣ) : K)) * x := by ac_rfl
        _ = x := by
          have hcancel : a * a⁻¹ = (1 : Kˣ) := by group
          simpa using congrArg (fun z : Kˣ => (z : K)) hcancel
    · rintro ⟨y, hy, rfl⟩
      change ((a⁻¹ : Kˣ) : K) * (((a : Kˣ) : K) * y) ∈ U
      have hcancel : a⁻¹ * a = (1 : Kˣ) := by group
      have hval : ((a⁻¹ : Kˣ) : K) * ((a : Kˣ) : K) = 1 := by
        simpa using congrArg (fun z : Kˣ => (z : K)) hcancel
      rw [show ((a⁻¹ : Kˣ) : K) * (((a : Kˣ) : K) * y) = y by rw [← mul_assoc, hval, one_mul]]
      exact hy
  let f : K → ℝ := U.indicator (fun _ => 1)
  have hleft : (∫ x, f (((a⁻¹ : Kˣ) : K) * x) ∂μ.μ) = μ.μ.real (jacquetShell v k) := by
    have hfun : (fun x => f (((a⁻¹ : Kˣ) : K) * x)) =
        (jacquetShell v k).indicator (fun _ => 1) := by
      funext x
      change (if ((a⁻¹ : Kˣ) : K) * x ∈ U then (1 : ℝ) else 0) =
        (if x ∈ jacquetShell v k then (1 : ℝ) else 0)
      have hxmem : ((a⁻¹ : Kˣ) : K) * x ∈ U ↔ x ∈ jacquetShell v k := by
        have hx := congrArg (fun S : Set K => x ∈ S) hpre
        exact Iff.of_eq hx
      have hxmem' : ((a : Kˣ) : K)⁻¹ * x ∈ U ↔ x ∈ jacquetShell v k := by
        simpa only [Units.val_inv_eq_inv_val] using hxmem
      simp [hxmem']
    rw [hfun]
    exact jacquet_integral_indicator_one μ hS
  have hright : (∫ x, f x ∂μ.μ) = μ.μ.real U := by
    exact jacquet_integral_indicator_one μ hU
  have hinv : absFin v (a⁻¹ : Kˣ) = (absFin v a)⁻¹ := by
    have hprod : absFin v a * absFin v (a⁻¹ : Kˣ) = 1 := by
      simpa [absFin_eq_norm] using (absFin_mul v a a⁻¹).symm
    have hAB : absFin v a = (absFin v (a⁻¹ : Kˣ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    calc
      absFin v (a⁻¹ : Kˣ) = ((absFin v (a⁻¹ : Kˣ))⁻¹)⁻¹ := by simp
      _ = (absFin v a)⁻¹ := by rw [← hAB]
  have hscale := LocHaar.integral_comp_mul μ (a⁻¹) f
  calc
    μ.μ.real (jacquetShell v k) =
        (absFin v (a⁻¹ : Kˣ))⁻¹ * μ.μ.real U := by
          rw [← hleft, hscale, smul_eq_mul, hright]
    _ = absFin v a * μ.μ.real U := by rw [hinv]; simp
    _ = absFin v ((unifLoc v ^ k : Kˣ) : K) * μ.μ.real (jacquetUnitShell v) := by
          rfl

set_option maxHeartbeats 5000000 in
private theorem section_intertwine_integrable (L : FinLocalCover D H v) (T : TorusRep D H v)
    (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V)
    (hf : IsSection L T s f) (g : L.L) :
    Integrable (fun x => f (L.w * L.n (Multiplicative.ofAdd x) * g)) μ.μ := by
  classical
  let K := v.adicCompletion F
  let f' : L.L → T.V := rtr g f
  have hf' : IsSection L T s f' := hf.rtr g
  obtain ⟨m, hm, hK⟩ := hf'.2.2
  let hfun : K → T.V := fun x => f' (L.w * L.n (Multiplicative.ofAdd x))
  have hloc : IsLocallyConstant hfun := by
    apply (IsLocallyConstant.iff_exists_open hfun).mpr
    intro x
    let U := (fun x' : K => x' - x) ⁻¹' ball v (m : ℤ)
    have hBopen : IsOpen (ball v (m : ℤ)) :=
      v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
    have hU : IsOpen U := hBopen.preimage (continuous_id.sub continuous_const)
    have hxU : x ∈ U := by
      dsimp [U]
      change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
      simp
    refine ⟨U, hU, hxU, ?_⟩
    intro x' hx'
    have hz : x' - x ∈ ball v (m : ℤ) := by simpa [U] using hx'
    let z := x' - x
    have hxEq : x' = x + z := by dsimp [z]; abel
    have hgroup : L.w * L.n (Multiplicative.ofAdd x') =
        (L.w * L.n (Multiplicative.ofAdd x)) * L.n (Multiplicative.ofAdd z) := by
      rw [hxEq]
      simp [ofAdd_add, mul_assoc]
    have hsmall : L.n (Multiplicative.ofAdd z) ∈ L.Kc m := L.n_Kc m hm z hz
    change f' (L.w * L.n (Multiplicative.ofAdd x')) =
      f' (L.w * L.n (Multiplicative.ofAdd x))
    rw [hgroup]
    exact hK (L.w * L.n (Multiplicative.ofAdd x)) _ hsmall
  have hcont : Continuous hfun := hloc.continuous
  let B : Set K := ball v (-(m : ℤ))
  have hBcompact : IsCompact B := by
    simpa [B] using ball_isCompact v (-(m : ℤ))
  have hBInt : IntegrableOn hfun B μ.μ := hcont.continuousOn.integrableOn_compact hBcompact
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hqnonneg : 0 ≤ q := hqpos.le
  obtain ⟨Cσ, hCσ, hσ⟩ := torus_sigma_uniform_bound T
  let C₀ : ℝ := Cσ * ‖f' 1‖
  have hC₀ : 0 ≤ C₀ := mul_nonneg hCσ (norm_nonneg _)
  let shell : ℕ → Set K := fun n => jacquetShell v (-((m : ℤ) + n + 1))
  let kshell : ℕ → ℤ := fun n => -((m : ℤ) + n + 1)
  have hshellInt (n : ℕ) : IntegrableOn hfun (shell n) μ.μ :=
    hcont.continuousOn.integrableOn_compact (jacquetShell_compact v (kshell n))
  have hshellBound (n : ℕ) :
      (∫ x in shell n, ‖hfun x‖ ∂μ.μ) ≤ C₀ * q ^ (2 * (kshell n : ℝ) * s.re) := by
    let k := kshell n
    let S := jacquetShell v k
    have hk : k = -((m : ℤ) + n + 1) := rfl
    have hrad (x : K) (hx : x ∈ S) :
        absFin v x = q ^ (-k) := by
      simpa [q] using jacquetShell_mem_radius v k hx
    have hval (x : K) (hx : x ∈ S) : Valued.v x = WithZero.exp (-k) :=
      jacquetShell_valuation v k hx
    have hxnot (x : K) (hx : x ∈ S) : x ∉ B := by
      intro hxB
      have hle : Valued.v x ≤ WithZero.exp (m : ℤ) := by
        change Valued.v x ≤ WithZero.exp (-(-(m : ℤ))) at hxB
        simpa using hxB
      have hklt : (m : ℤ) < -k := by dsimp [k]; omega
      have hlt : WithZero.exp (m : ℤ) < Valued.v x := by
        rw [hval x hx]
        exact WithZero.exp_lt_exp.mpr hklt
      exact (not_lt_of_ge hle) hlt
    have hxinverse (x : K) (hx : x ∈ S) : x⁻¹ ∈ ball v (m : ℤ) :=
      jacquet_inv_mem_ball_of_not_mem (N := m) (hxnot x hx)
    have hzero (x : K) (hx : x ∈ S) : x ≠ 0 := by
      intro hx0
      subst x
      have hval0 := hval 0 hx
      have hv0 : Valued.v (0 : K) = 0 := by simp
      rw [hv0] at hval0
      exact WithZero.exp_ne_zero hval0.symm
    have hformula (x : K) (hx : x ∈ S) :
        hfun x = ((absFin v (-((Units.mk0 x (hzero x hx))⁻¹ *
            (Units.mk0 x (hzero x hx))⁻¹)) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa (-((Units.mk0 x (hzero x hx))⁻¹ *
            (Units.mk0 x (hzero x hx))⁻¹)) (f' 1) := by
      have h := jacquet_section_w_n_formula L T s f' hf' m hm hK x (hzero x hx)
        (hxinverse x hx)
      simpa [hfun] using h
    have hradY (x : K) (hx : x ∈ S) :
        absFin v (-((Units.mk0 x (hzero x hx))⁻¹ *
          (Units.mk0 x (hzero x hx))⁻¹) : K) = q ^ (2 * k) := by
      have hY : absFin v (-((Units.mk0 x (hzero x hx))⁻¹ *
          (Units.mk0 x (hzero x hx))⁻¹) : K) = (absFin v x) ^ (-2 : ℤ) := by
        rw [absFin_eq_norm, absFin_eq_norm]
        simp only [norm_neg, norm_mul, norm_inv, Units.val_inv_eq_inv_val,
          Units.val_mul, Units.val_neg, Units.val_mk0]
        have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (hzero x hx)
        field_simp [hxnorm]
      rw [hY, hrad x hx]
      rw [← zpow_mul]
      congr 1
      ring
    have hscalar (x : K) (hx : x ∈ S) :
        ‖(absFin v (-((Units.mk0 x (hzero x hx))⁻¹ *
            (Units.mk0 x (hzero x hx))⁻¹) : K) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ =
          q ^ ((k : ℝ) * (1 + 2 * s.re)) := by
      have hpos : 0 < absFin v (-((Units.mk0 x (hzero x hx))⁻¹ *
          (Units.mk0 x (hzero x hx))⁻¹) : K) := by
        rw [hradY x hx]
        exact zpow_pos hqpos _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, hradY x hx]
      have hre : (((1 : ℂ) / 2 + s).re) = (1 : ℝ) / 2 + s.re := by simp
      rw [hre]
      calc
        (q ^ (2 * k)) ^ ((1 : ℝ) / 2 + s.re) =
            (q ^ ((1 : ℝ) / 2 + s.re)) ^ (2 * k) :=
              (Real.rpow_zpow_comm hqnonneg ((1 : ℝ) / 2 + s.re) (2 * k)).symm
        _ = q ^ (((1 : ℝ) / 2 + s.re) * ((2 * k : ℤ) : ℝ)) := by
          rw [← Real.rpow_intCast]
          exact (Real.rpow_mul hqnonneg _ _).symm
        _ = q ^ ((k : ℝ) * (1 + 2 * s.re)) := by congr 1 <;> push_cast <;> ring
    have hpoint (x : K) (hx : x ∈ S) :
        ‖hfun x‖ ≤ C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re)) := by
      rw [hformula x hx, norm_smul, hscalar x hx]
      calc
        q ^ ((k : ℝ) * (1 + 2 * s.re)) *
            ‖T.σa (-((Units.mk0 x (hzero x hx))⁻¹ *
              (Units.mk0 x (hzero x hx))⁻¹)) (f' 1)‖ ≤
          q ^ ((k : ℝ) * (1 + 2 * s.re)) * (Cσ * ‖f' 1‖) :=
            mul_le_mul_of_nonneg_left (hσ _ _) (Real.rpow_nonneg hqnonneg _)
        _ = C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re)) := by dsimp [C₀]; ring
    have hconstInt : IntegrableOn
        (fun _ : K => C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re))) S μ.μ :=
      integrableOn_const (jacquetShell_compact v k).measure_lt_top.ne
    have hmono := setIntegral_mono_on (hshellInt n).norm hconstInt
      (jacquetShell_compact v k).measurableSet hpoint
    have hmeasure : μ.μ.real S ≤ q ^ (-k) := by
      rw [jacquetShell_real_measure μ k]
      have hradius : absFin v ((unifLoc v ^ k : Kˣ) : K) = q ^ (-k) := by
        simpa [q] using jacquetShell_radius v k
      rw [hradius]
      exact mul_le_of_le_one_right (zpow_nonneg hqnonneg _)
        (jacquetUnitShell_real_measure_le_one v μ)
    have hpow : q ^ (-k : ℤ) * q ^ ((k : ℝ) * (1 + 2 * s.re)) =
        q ^ (2 * (k : ℝ) * s.re) := by
      rw [← Real.rpow_intCast q (-k), ← Real.rpow_add hqpos]
      congr 1 <;> push_cast <;> ring
    have hconst_nonneg : 0 ≤ C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re)) :=
      mul_nonneg hC₀ (Real.rpow_nonneg hqnonneg _)
    calc
      (∫ x in S, ‖hfun x‖ ∂μ.μ) ≤
          μ.μ.real S * (C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re))) := by
            simpa [setIntegral_const, smul_eq_mul, mul_comm] using hmono
      _ ≤ q ^ (-k) * (C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re))) :=
            mul_le_mul_of_nonneg_right hmeasure hconst_nonneg
      _ = C₀ * q ^ (2 * (k : ℝ) * s.re) := by
            calc
              q ^ (-k) * (C₀ * q ^ ((k : ℝ) * (1 + 2 * s.re))) =
                  C₀ * (q ^ (-k) * q ^ ((k : ℝ) * (1 + 2 * s.re))) := by ring
              _ = C₀ * q ^ (2 * (k : ℝ) * s.re) := by rw [hpow]
  let ρ : ℝ := q ^ (-(2 * s.re))
  have hρnonneg : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hgeom : Summable (fun n : ℕ => ρ ^ n) :=
    summable_geometric_of_lt_one hρnonneg hρlt
  let Bsum : ℕ → ℝ := fun n => C₀ * q ^ (-(2 * s.re) * ((m : ℝ) + 1)) * ρ ^ n
  have hBsum : Summable Bsum := by
    apply Summable.mul_left (C₀ * q ^ (-(2 * s.re) * ((m : ℝ) + 1))) hgeom
  have hpowtail (n : ℕ) :
      q ^ (2 * (kshell n : ℝ) * s.re) =
        q ^ (-(2 * s.re) * ((m : ℝ) + 1)) * ρ ^ n := by
    have hexp : 2 * (kshell n : ℝ) * s.re =
        (-(2 * s.re) * ((m : ℝ) + 1)) + (-(2 * s.re)) * (n : ℝ) := by
      dsimp [kshell]
      push_cast
      ring
    rw [hexp, Real.rpow_add hqpos]
    rw [Real.rpow_mul_natCast hqnonneg]
  have htailSummable : Summable (fun n : ℕ =>
      ∫ x in shell n, ‖hfun x‖ ∂μ.μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg (hfun x))
      (fun n => ?_) hBsum
    calc
      (∫ x in shell n, ‖hfun x‖ ∂μ.μ) ≤ C₀ * q ^ (2 * (kshell n : ℝ) * s.re) := hshellBound n
      _ = Bsum n := by rw [hpowtail n]; simp [Bsum]; ring
  have htail : IntegrableOn hfun (⋃ n : ℕ, shell n) μ.μ :=
    integrableOn_iUnion_of_summable_integral_norm hshellInt htailSummable
  have hcover : B ∪ (⋃ n : ℕ, shell n) = (Set.univ : Set K) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hxB : x ∈ B
      · exact Set.mem_union_left _ hxB
      · have hx0 : x ≠ 0 := by
          intro hx
          subst x
          have hzeroB : (0 : K) ∈ B := by
            change (0 : K) ∈ ball v (-(m : ℤ))
            change Valued.v (0 : K) ≤ WithZero.exp (-(-(m : ℤ)))
            have hv0 : Valued.v (0 : K) = 0 := by simp
            rw [hv0, Int.neg_neg]
            have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (m : ℤ) :=
              WithZero.exp_pos
            exact hpos.le
          exact hxB hzeroB
        obtain ⟨k, hxk⟩ := jacquetShell_cover v hx0
        have hvalx := jacquetShell_valuation v k hxk
        have hklt : (m : ℤ) < -k := by
          by_contra h
          have hk' : -k ≤ (m : ℤ) := by omega
          have hBmem : x ∈ B := by
            change x ∈ ball v (-(m : ℤ))
            change Valued.v x ≤ WithZero.exp (-(-(m : ℤ)))
            rw [hvalx]
            exact WithZero.exp_le_exp.mpr (by omega)
          exact hxB hBmem
        let n : ℕ := Int.toNat (-(m : ℤ) - 1 - k)
        have hn0 : 0 ≤ -(m : ℤ) - 1 - k := by omega
        have hncast : (n : ℤ) = -(m : ℤ) - 1 - k := Int.toNat_of_nonneg hn0
        have hkEq : k = -((m : ℤ) + n + 1) := by omega
        right
        apply Set.mem_iUnion.mpr ⟨n, ?_⟩
        simpa [shell, kshell, hkEq] using hxk
  have hwhole : IntegrableOn hfun (B ∪ (⋃ n : ℕ, shell n)) μ.μ := by
    rw [integrableOn_union]
    exact ⟨hBInt, htail⟩
  have hwhole' : IntegrableOn hfun (Set.univ : Set K) μ.μ := by
    rw [← hcover]
    exact hwhole
  have hInt : Integrable hfun μ.μ := by
    simpa only [integrableOn_univ] using hwhole'
  simpa [hfun, f', rtr] using hInt

private theorem locHaar_integral_comp_addLeft (μ : LocHaar v) (b : v.adicCompletion F)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : v.adicCompletion F → E) :
    ∫ x, f (b + x) ∂μ.μ = ∫ x, f x ∂μ.μ := by
  let e : MeasurableEquiv (v.adicCompletion F) (v.adicCompletion F) := MeasurableEquiv.addLeft b
  have hmap : Measure.map e μ.μ = μ.μ := by
    simpa [e] using Measure.IsAddLeftInvariant.map_add_left_eq_self b
  have hpres : MeasurePreserving e μ.μ μ.μ := ⟨e.measurable, hmap⟩
  change ∫ x, f (e x) ∂μ.μ = ∫ x, f x ∂μ.μ
  exact hpres.integral_comp' f

set_option maxHeartbeats 5000000 in
private theorem addChar_norm_one (A : AddCharData F) (x : v.adicCompletion F) :
    ‖A.ψ v x‖ = 1 := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let R := IsLocalRing.ResidueField O
  let q : ℕ := Ideal.absNorm v.asIdeal
  letI : Finite R :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  letI : Fintype R := Fintype.ofFinite R
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let H : AddSubgroup O := (IsLocalRing.maximalIdeal O).toAddSubgroup
  have hcard : Nat.card R = q := by
    change Nat.card (O ⧸ H) = Ideal.absNorm v.asIdeal
    calc
      Nat.card (O ⧸ H) = Nat.card (𝓞 F ⧸ v.asIdeal) :=
        Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := F)).symm.toEquiv
      _ = Ideal.absNorm v.asIdeal := by
        simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcast : (q : R) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero R
  have hres : IsLocalRing.residue O (q : O) = 0 := by
    change (q : R) = 0
    exact hcast
  have hmax : (q : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.residue_eq_zero_iff (q : O)).mp hres
  have hsmall : Valued.v (q : K) < 1 := by
    have hmax_iff (a : O) : a ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (a : K) < 1 := by
      change a ∈ IsLocalRing.maximalIdeal
          ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
      exact Valuation.mem_maximalIdeal_iff
        (v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))) (a := a)
    exact (hmax_iff (q : O)).mp hmax
  have hnorm : ‖(q : K)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hsmall
  let qK : K := q
  have hpow : Tendsto (fun n : ℕ => qK ^ n) atTop (𝓝 (0 : K)) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa [qK] using hnorm)
  have hmul : Tendsto (fun n : ℕ => qK ^ n * x) atTop (𝓝 (0 : K)) := by
    simpa using hpow.mul_const x
  have hOopen : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have h0O : (0 : K) ∈ (O : Set K) := by simp [O]
  have hev : ∀ᶠ n : ℕ in atTop, qK ^ n * x ∈ (O : Set K) :=
    hmul.eventually (hOopen.mem_nhds h0O)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hψ : A.ψ v x ^ (q ^ N) = 1 := by
    calc
      A.ψ v x ^ (q ^ N) = A.ψ v ((q ^ N) • x) :=
        (AddChar.map_nsmul_eq_pow (A.ψ v) (q ^ N) x).symm
      _ = A.ψ v (qK ^ N * x) := by congr 2; simp [qK, nsmul_eq_mul]
      _ = 1 := A.integral v _ (hN N le_rfl)
  have hfin : IsOfFinOrder (A.ψ v x) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨q ^ N, pow_pos (by omega) N, hψ⟩
  exact hfin.norm_eq_one

set_option maxHeartbeats 5000000
/-- **jq:rotated**: the rotated big-cell section, `𝒥(π(a(y)w) f_φ) = ‖y‖^{1/2-s} σ(a(y⁻¹)) F̂(y)` with
`F(c) = f_φ(n̄(c)) = ‖c‖^{-1-2s} σ(a(-c⁻²)) φ(c⁻¹)` (`F = 0` near `0`). -/
theorem jacquet_rotated (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) (y : (v.adicCompletion F)ˣ) :
    jacquet L A μ (rtr (L.a y * L.w) (bigCell L T s φ)) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ (∫ c, A.ψ v (-((y : v.adicCompletion F) * c)) •
          bigCell L T s φ (L.nbar (Multiplicative.ofAdd c)) ∂μ.μ) := by
  classical
  let K := v.adicCompletion F
  let f : L.L → T.V := bigCell L T s φ
  have hf : IsSection L T s f := bigCell_isSection L T s φ hφ hc
  let g : L.L := L.a y * L.w
  let G : K → T.V := fun x => f (L.w * L.n (Multiplicative.ofAdd x) * g)
  have hGint : Integrable G μ.μ := by
    exact section_intertwine_integrable L T μ s hs f hf g
  let phaseOuter : K → ℂ := fun x => A.ψ v (-x)
  let outer : K → T.V := fun x => phaseOuter x • G x
  have hphaseOuterLC : IsLocallyConstant phaseOuter := by
    have hpsi := addChar_locallyConstant (v := v) A
    apply hpsi.comp_continuous
    exact continuous_neg
  have houterAEStrong : AEStronglyMeasurable outer μ.μ := by
    exact hphaseOuterLC.continuous.aestronglyMeasurable.smul hGint.aestronglyMeasurable
  have houterNorm (x : K) : ‖outer x‖ = ‖G x‖ := by
    change ‖phaseOuter x • G x‖ = ‖G x‖
    rw [norm_smul, addChar_norm_one (v := v) A (-x), one_mul]
  have houterInt : Integrable outer μ.μ :=
    hGint.mono houterAEStrong (ae_of_all _ fun x => (houterNorm x).le)
  let F0 : K → T.V := fun c => f (L.nbar (Multiplicative.ofAdd c))
  have hF0base : Integrable F0 μ.μ := by
    have h := section_intertwine_integrable L T μ s hs f hf L.w
    apply h.congr
    filter_upwards [] with c
    dsimp [F0]
    rw [L.w_n_w]
  let fourierKernel : K → T.V := fun c =>
    A.ψ v (-((y : K) * c)) • F0 c
  have hfourierPhaseLC : IsLocallyConstant (fun c : K => A.ψ v (-((y : K) * c))) := by
    apply (addChar_locallyConstant A).comp_continuous
    exact continuous_neg.comp (continuous_const.mul continuous_id)
  have hfourierAEStrong : AEStronglyMeasurable fourierKernel μ.μ :=
    hfourierPhaseLC.continuous.aestronglyMeasurable.smul hF0base.aestronglyMeasurable
  have hfourierNorm (c : K) : ‖fourierKernel c‖ = ‖F0 c‖ := by
    change ‖A.ψ v (-((y : K) * c)) • F0 c‖ = ‖F0 c‖
    rw [norm_smul, addChar_norm_one (v := v) A (-((y : K) * c)), one_mul]
  have hfourierInt : Integrable fourierKernel μ.μ :=
    hF0base.mono hfourierAEStrong (ae_of_all _ fun c => (hfourierNorm c).le)
  let C : ℂ := ((absFin v (y⁻¹ : Kˣ) : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s)
  let σ : T.V →L[ℂ] T.V := (T.σa y⁻¹).toContinuousLinearMap
  let yInv : K := ((y⁻¹ : Kˣ) : K)
  have hwa : L.w * L.a y = L.a y⁻¹ * L.w := by
    have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
    calc
      L.w * L.a y = (L.w * L.a y * L.w⁻¹) * L.w := by group
      _ = L.a y⁻¹ * L.w := by rw [L.lift_wa]
  have hgroup (x : K) :
      L.w * L.n (Multiplicative.ofAdd x) * (L.a y * L.w) =
        L.a y⁻¹ * L.nbar (Multiplicative.ofAdd (x * yInv)) := by
    have htor (z : K) :
        L.w * L.n (Multiplicative.ofAdd z) * L.a y =
          L.a y⁻¹ * L.w * L.n (Multiplicative.ofAdd (z * yInv)) := by
      calc
        L.w * L.n (Multiplicative.ofAdd z) * L.a y =
            L.w * (L.n (Multiplicative.ofAdd z) * L.a y) := by simp [mul_assoc]
        _ = L.w * (L.a y * L.n (Multiplicative.ofAdd (z * yInv))) := by
          rw [L.lift_na]
        _ = (L.w * L.a y) * L.n (Multiplicative.ofAdd (z * yInv)) := by simp [mul_assoc]
        _ = (L.a y⁻¹ * L.w) * L.n (Multiplicative.ofAdd (z * yInv)) := by rw [hwa]
        _ = L.a y⁻¹ * L.w * L.n (Multiplicative.ofAdd (z * yInv)) := by simp [mul_assoc]
    calc
      L.w * L.n (Multiplicative.ofAdd x) * (L.a y * L.w) =
          (L.w * L.n (Multiplicative.ofAdd x) * L.a y) * L.w := by group
      _ = (L.a y⁻¹ * L.w * L.n (Multiplicative.ofAdd (x * yInv))) * L.w := by rw [htor]
      _ = L.a y⁻¹ * (L.w * L.n (Multiplicative.ofAdd (x * yInv)) * L.w) := by group
      _ = L.a y⁻¹ * L.nbar (Multiplicative.ofAdd (x * yInv)) := by rw [L.w_n_w]
  have hcov (c : K) :
      f (L.a y⁻¹ * L.nbar (Multiplicative.ofAdd c)) =
        C • T.σa y⁻¹ (F0 c) := by
    have h := hf.1 0 y⁻¹ (L.nbar (Multiplicative.ofAdd c))
    simpa [C, F0] using h
  have hpoint (x : K) : outer x = C • σ (fourierKernel (x * yInv)) := by
    have hcomp : (y : K) * (x * yInv) = x := by
      calc
        (y : K) * (x * yInv) = ((y : K) * yInv) * x := by ring
        _ = x := by simp [yInv]
    have hphase : A.ψ v (-x) = A.ψ v (-((y : K) * (x * yInv))) := by rw [hcomp]
    change A.ψ v (-x) • f (L.w * L.n (Multiplicative.ofAdd x) * (L.a y * L.w)) = _
    rw [hgroup x, hcov (x * yInv)]
    simp [fourierKernel, σ, map_smul, hphase, smul_smul, mul_comm]
  have hInv : absFin v (y⁻¹ : Kˣ) = (absFin v y)⁻¹ := by
    have hprod : absFin v y * absFin v (y⁻¹ : Kˣ) = 1 := by
      simpa [absFin_eq_norm] using (absFin_mul v y y⁻¹).symm
    have hAB : absFin v y = (absFin v (y⁻¹ : Kˣ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    calc
      absFin v (y⁻¹ : Kˣ) = ((absFin v (y⁻¹ : Kˣ))⁻¹)⁻¹ := by simp
      _ = (absFin v y)⁻¹ := by rw [← hAB]
  let q : ℝ := absFin v y
  have hqpos : 0 < q := by dsimp [q]; exact absFin_pos y.ne_zero
  have hqComplex : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hbase : ((absFin v (y⁻¹ : Kˣ) : ℝ) : ℂ) = (q : ℂ)⁻¹ := by
    dsimp [q]
    exact_mod_cast hInv
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
  have hballUnion : (⋃ N : ℕ, ball v (-(N : ℤ))) = (Set.univ : Set K) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨N, hN⟩ := exists_ballNeg_nat x
      exact Set.mem_iUnion.mpr ⟨N, hN⟩
  have hballUnion' :
      (⋃ N : ℕ, {z : K | Valued.v z ≤ WithZero.exp (-(-(N : ℤ)))}) =
        (Set.univ : Set K) := by
    simpa only [ball] using hballUnion
  have hballMono : Monotone (fun N : ℕ => ball v (-(N : ℤ))) := by
    intro N M hNM
    exact ballNeg_nat_mono hNM
  have hballInt := tendsto_setIntegral_of_monotone
    (fun N => (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).measurableSet)
    hballMono houterInt.integrableOn
  rw [hballUnion'] at hballInt
  have hlim : Tendsto (fun N : ℕ => jacquetTrunc L A μ N (rtr g f)) atTop
      (𝓝 (∫ x, outer x ∂μ.μ)) := by
    simpa [jacquetTrunc, ball, outer, phaseOuter, G, g, rtr, setIntegral_univ] using hballInt
  have hjac : jacquet L A μ (rtr g f) = ∫ x, outer x ∂μ.μ := by
    change limUnder atTop (fun N : ℕ => jacquetTrunc L A μ N (rtr g f)) = _
    exact hlim.limUnder_eq
  have hscale := LocHaar.integral_comp_mul μ (y⁻¹) (fun c => σ (fourierKernel c))
  have hmulComm :
      (∫ x, σ (fourierKernel (x * yInv)) ∂μ.μ) =
        ∫ x, σ (fourierKernel (yInv * x)) ∂μ.μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2 <;> ring
  have hscaled :
      (∫ x, σ (fourierKernel (x * yInv)) ∂μ.μ) =
        (q : ℂ) • σ (∫ c, fourierKernel c ∂μ.μ) := by
    calc
      _ = ∫ x, σ (fourierKernel (yInv * x)) ∂μ.μ := hmulComm
      _ = (absFin v (y⁻¹ : Kˣ))⁻¹ • ∫ x, σ (fourierKernel x) ∂μ.μ := by
        simpa [yInv] using hscale
      _ = q • σ (∫ c, fourierKernel c ∂μ.μ) := by
        rw [hInv, inv_inv, ContinuousLinearMap.integral_comp_comm σ hfourierInt]
      _ = (q : ℂ) • σ (∫ c, fourierKernel c ∂μ.μ) := by
        symm
        exact IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := T.V) q
          (σ (∫ c, fourierKernel c ∂μ.μ))
  have hfull :
      (∫ x, outer x ∂μ.μ) =
        (C * (q : ℂ)) • σ (∫ c, fourierKernel c ∂μ.μ) := by
    calc
      (∫ x, outer x ∂μ.μ) = ∫ x, C • σ (fourierKernel (x * yInv)) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpoint x
      _ = C • ∫ x, σ (fourierKernel (x * yInv)) ∂μ.μ := by rw [integral_smul]
      _ = C • ((q : ℂ) • σ (∫ c, fourierKernel c ∂μ.μ)) := by rw [hscaled]
      _ = (C * (q : ℂ)) • σ (∫ c, fourierKernel c ∂μ.μ) := by rw [smul_smul]
  calc
    jacquet L A μ (rtr (L.a y * L.w) f) = ∫ x, outer x ∂μ.μ := by simpa [g] using hjac
    _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
        T.σa y⁻¹ (∫ c, fourierKernel c ∂μ.μ) := by
      rw [hfull, hcoef]
      simp [σ, q, LinearMap.coe_toContinuousLinearMap']

/-- The rotated Whittaker coordinate `y ↦ c(𝒥(π(a(y)w) f_φ))`, extended by `0` at `y = 0`. -/
def rotatedCoord (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (φ : v.adicCompletion F → T.V) (c : T.V →ₗ[ℂ] ℂ)
    (y : v.adicCompletion F) : ℂ :=
  if h : y ≠ 0 then c (jacquet L A μ (rtr (L.a (Units.mk0 y h) * L.w) (bigCell L T s φ))) else 0

private theorem section_nbar_relative_invariance_depth (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f)
    (m : ℕ) (hm : L.m0 ≤ m) (hK : ∀ g, ∀ k ∈ L.Kc m, f (g * k) = f g) :
    ∃ M : ℕ, 0 < M ∧ m ≤ M ∧ ∀ c b : v.adicCompletion F, c ≠ 0 →
      b * c⁻¹ ∈ ball v (M : ℤ) →
        f (L.nbar (Multiplicative.ofAdd (c + b))) =
            f (L.nbar (Multiplicative.ofAdd c)) ∧
          absFin v (c + b) = absFin v c := by
  classical
  let K := v.adicCompletion F
  obtain ⟨m6, hsix⟩ := exists_near_one_sixth_power v
  let M := max 1 (max m m6)
  have hMpos : 0 < M := lt_of_lt_of_le (by omega) (le_max_left 1 (max m m6))
  have hMm : m ≤ M := le_trans (le_max_left m m6) (le_max_right 1 (max m m6))
  have hM6 : m6 ≤ M := le_trans (le_max_right m m6) (le_max_right 1 (max m m6))
  refine ⟨M, hMpos, hMm, ?_⟩
  intro c b hc hrel
  have hdelta : Valued.v (b * c⁻¹) < 1 := by
    have hball : Valued.v (b * c⁻¹) ≤ WithZero.exp (-(M : ℤ)) := by
      simpa [ball] using hrel
    have hlt : WithZero.exp (-(M : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact neg_lt_zero.mpr (show (0 : ℤ) < (M : ℤ) by exact_mod_cast hMpos)
    exact lt_of_le_of_lt hball hlt
  let uVal : K := 1 + b * c⁻¹
  have huval : Valued.v uVal = 1 := by
    have h := Valuation.map_add_eq_of_lt_right
      (v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
      (x := b * c⁻¹) (y := (1 : K)) (by simpa using hdelta)
    simpa [uVal, add_comm] using h
  have huValNe : uVal ≠ 0 := by
    intro h0
    have h := congrArg Valued.v h0
    rw [huval] at h
    simp at h
  let u : Kˣ := Units.mk0 uVal huValNe
  have huval' : Valued.v (u : K) = 1 := by simpa [u] using huval
  have huabs : absFin v u = 1 := by
    rw [absFin_eq_norm, FinitePlace.norm_def, huval']
    simp
  have huNear : ((u : K) - 1) ∈ ball v (m6 : ℤ) := by
    have hidentity : (u : K) - 1 = b * c⁻¹ := by
      dsimp [u, uVal]
      ring
    rw [hidentity]
    exact ballNat_mono hM6 hrel
  have huMinusOne : (u : K) - 1 = b * c⁻¹ := by
    dsimp [u, uVal]
    ring
  obtain ⟨a, ha⟩ := hsix u huNear
  have huInvSix : ∃ a' : Kˣ, u⁻¹ = a' ^ 6 := by
    refine ⟨a⁻¹, ?_⟩
    rw [ha]
    group
  have hhilb : H.hilb v u u⁻¹ = 1 :=
    H.sixth_power v u u⁻¹ ⟨a, ha⟩
  have hhilbInv : H.hilb v u⁻¹ u = 1 :=
    H.sixth_power v u⁻¹ u huInvSix
  have hmuOne : muThree D (1 : rootsOfUnity 6 F) = 1 := by
    apply rootsOfUnity.coe_injective
    simp [muThree]
  have haMul : L.a u * L.a u⁻¹ = 1 := by
    calc
      L.a u * L.a u⁻¹ = L.z (muThree D (H.hilb v u u⁻¹)) * L.a (u * u⁻¹) :=
        L.a_mul u u⁻¹
      _ = 1 := by rw [hhilb, mul_inv_cancel, L.a_one, hmuOne]; simp
  have haMulInv : L.a u⁻¹ * L.a u = 1 := by
    calc
      L.a u⁻¹ * L.a u = L.z (muThree D (H.hilb v u⁻¹ u)) * L.a (u⁻¹ * u) :=
        L.a_mul u⁻¹ u
      _ = 1 := by rw [hhilbInv, inv_mul_cancel, L.a_one, hmuOne]; simp
  have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
  have hwa (z : Kˣ) : L.a z⁻¹ * L.w = L.w * L.a z := by
    calc
      L.a z⁻¹ * L.w = (L.w * L.a z * L.w⁻¹) * L.w := by rw [← L.lift_wa]
      _ = L.w * L.a z := by simp [mul_assoc, hwInv, L.w_sq]
  have hAw : L.a u * L.w * L.a u = L.w := by
    have hleft : L.a u * L.w = L.w * L.a u⁻¹ := by simpa using hwa u⁻¹
    calc
      L.a u * L.w * L.a u = L.w * L.a u⁻¹ * L.a u := by rw [hleft]
      _ = L.w := by
        calc
          L.w * L.a u⁻¹ * L.a u = L.w * (L.a u⁻¹ * L.a u) := by group
          _ = L.w := by rw [haMulInv]; simp
  have hna : L.a u * L.n (Multiplicative.ofAdd c) =
      L.n (Multiplicative.ofAdd (c * (u : K))) * L.a u := by
    have h := L.lift_na (c * (u : K)) u
    have harg : c * (u : K) * (u : K)⁻¹ = c := by field_simp
    simpa [harg, mul_assoc] using h.symm
  have hconj : L.a u⁻¹ * L.nbar (Multiplicative.ofAdd c) * L.a u =
      L.nbar (Multiplicative.ofAdd (c * (u : K))) := by
    calc
      L.a u⁻¹ * L.nbar (Multiplicative.ofAdd c) * L.a u =
          (L.a u⁻¹ * L.w) * L.n (Multiplicative.ofAdd c) *
            (L.w * L.a u) := by rw [← L.w_n_w]; group
      _ = (L.w * L.a u) * L.n (Multiplicative.ofAdd c) *
            (L.w * L.a u) := by rw [hwa u]
      _ = L.w * (L.a u * L.n (Multiplicative.ofAdd c)) * L.w * L.a u := by group
      _ = L.w * (L.n (Multiplicative.ofAdd (c * (u : K))) * L.a u) *
            L.w * L.a u := by rw [hna]
      _ = L.w * L.n (Multiplicative.ofAdd (c * (u : K))) *
            (L.a u * L.w * L.a u) := by group
      _ = L.nbar (Multiplicative.ofAdd (c * (u : K))) := by rw [hAw, L.w_n_w]
  have hplus : c + b = c * (u : K) := by
    dsimp [u, uVal]
    field_simp [hc] <;> ring
  have huK : L.a u ∈ L.Kc m :=
    L.a_Kc m hm u (ballNat_mono hMm (by rw [huMinusOne]; exact hrel))
  have hleft : f (L.a u⁻¹ * L.nbar (Multiplicative.ofAdd c) * L.a u) =
      f (L.nbar (Multiplicative.ofAdd c) * L.a u) := by
    have h := hf.1 0 u⁻¹ (L.nbar (Multiplicative.ofAdd c) * L.a u)
    have huInvAbs : absFin v u⁻¹ = 1 := by
      have hprod : absFin v u * absFin v u⁻¹ = 1 := by
        calc
          absFin v u * absFin v u⁻¹ = absFin v (u * u⁻¹) := (absFin_mul v u u⁻¹).symm
          _ = absFin v (1 : K) := by congr 1; simp
          _ = 1 := by unfold absFin; rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]; simp
      simpa [huabs] using eq_inv_of_mul_eq_one_left hprod
    have hσ : T.σa u⁻¹ = LinearMap.id := by
      have hcube : u⁻¹ = ((a⁻¹) ^ 2) ^ 3 := by rw [ha]; group
      rw [hcube]
      exact T.σa_cube ((a⁻¹) ^ 2)
    simpa [huInvAbs, hσ, mul_assoc] using h
  have hright : f (L.nbar (Multiplicative.ofAdd c) * L.a u) =
      f (L.nbar (Multiplicative.ofAdd c)) := hK _ _ huK
  constructor
  · calc
      f (L.nbar (Multiplicative.ofAdd (c + b))) =
          f (L.nbar (Multiplicative.ofAdd (c * (u : K)))) := by rw [hplus]
      _ = f (L.a u⁻¹ * L.nbar (Multiplicative.ofAdd c) * L.a u) := by rw [hconj]
      _ = f (L.nbar (Multiplicative.ofAdd c) * L.a u) := hleft
      _ = f (L.nbar (Multiplicative.ofAdd c)) := hright
  · have huNorm : ‖(u : K)‖ = 1 := by simpa [absFin_eq_norm] using huabs
    calc
      absFin v (c + b) = absFin v (c * (u : K)) := by rw [hplus]
      _ = ‖c * (u : K)‖ := absFin_eq_norm v _
      _ = ‖c‖ := by rw [norm_mul, huNorm, mul_one]
      _ = absFin v c := (absFin_eq_norm v c).symm

private theorem ball_mono_int {m n : ℤ} (hmn : m ≤ n) :
    ball v n ⊆ ball v m := by
  intro x hx
  change Valued.v x ≤ WithZero.exp (-n) at hx
  change Valued.v x ≤ WithZero.exp (-m)
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem integral_fourier_shell_zero (μ : LocHaar v) (A : AddCharData F)
    (y b : v.adicCompletion F) (S : Set (v.adicCompletion F))
    (hS : MeasurableSet S) (hpre : (MeasurableEquiv.addLeft b) ⁻¹' S = S)
    (F0 : v.adicCompletion F → V)
    (hshift : ∀ x, x ∈ S → F0 (b + x) = F0 x)
    (hnontriv : A.ψ v (-(y * b)) ≠ 1) :
    ∫ x in S, A.ψ v (-(y * x)) • F0 x ∂μ.μ = 0 := by
  let ker : v.adicCompletion F → V := fun x => A.ψ v (-(y * x)) • F0 x
  let I : V := ∫ x in S, ker x ∂μ.μ
  have hphase (x : v.adicCompletion F) :
      A.ψ v (-(y * (b + x))) = A.ψ v (-(y * b)) * A.ψ v (-(y * x)) := by
    have harg : -(y * (b + x)) = -(y * b) + -(y * x) := by ring
    rw [harg, AddChar.map_add_eq_mul]
  have hpoint (x : v.adicCompletion F) (hx : x ∈ S) :
      ker (b + x) = A.ψ v (-(y * b)) • ker x := by
    dsimp [ker]
    rw [hphase, hshift x hx]
    simp [smul_smul]
  have hfix : I = A.ψ v (-(y * b)) • I := by
    dsimp [I]
    calc
      (∫ x in S, ker x ∂μ.μ) = ∫ x in S, ker (b + x) ∂μ.μ :=
        (jacquet_integral_comp_addLeft_set μ b S hS hpre ker).symm
      _ = ∫ x in S, A.ψ v (-(y * b)) • ker x ∂μ.μ := by
        apply setIntegral_congr_fun hS
        intro x hx
        exact hpoint x hx
      _ = A.ψ v (-(y * b)) • I := by rw [integral_smul]
  have hmul : (1 - A.ψ v (-(y * b))) • I = 0 := by
    calc
      (1 - A.ψ v (-(y * b))) • I = I - A.ψ v (-(y * b)) • I := by
        rw [sub_smul, one_smul]
      _ = 0 := by rw [← hfix]; simp
  have hcoef : 1 - A.ψ v (-(y * b)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hnontriv)
  exact (smul_eq_zero.mp hmul).resolve_left hcoef

private theorem jacquetShell_of_absFin (v : FinPlace F) (k : ℤ)
    {x : v.adicCompletion F} (hx : x ≠ 0)
    (hrad : absFin v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k)) :
    x ∈ jacquetShell v k := by
  obtain ⟨j, hj⟩ := jacquetShell_cover v hx
  have hradj := jacquetShell_mem_radius v j hj
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := hradj.symm.trans hrad
  have hbase : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hexp : -j = -k :=
    (zpow_right_injective₀ (lt_trans zero_lt_one hbase) (ne_of_gt hbase)) hpow
  have hjk : j = k := by omega
  simpa [hjk] using hj

/-- **jq:T6-local** (T6 at a finite place of `S`, `δ = 1/3`). -/
theorem rotatedCoord_sheetHyp (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (c : T.V →ₗ[ℂ] ℂ) :
    SheetHypFin v (1 / 3) (rotatedCoord L T A μ (1 / 6) φ c) := by
  classical
  let K := v.adicCompletion F
  let s : ℂ := 1 / 6
  let f : L.L → T.V := bigCell L T s φ
  have hf : IsSection L T s f := bigCell_isSection L T s φ hφ hc
  obtain ⟨m, hm, hK⟩ := hf.2.2
  obtain ⟨M0, hM0pos, hmM0, hrelInv⟩ :=
    section_nbar_relative_invariance_depth L T s f hf m hm hK
  obtain ⟨mT, hmT, hσsmooth⟩ := T.σa_smooth
  obtain ⟨m6, hsix⟩ := exists_near_one_sixth_power v
  let M : ℕ := max M0 (max mT (max m6 1))
  have hMM0 : M0 ≤ M := le_max_left _ _
  have hMmT : mT ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMm6 : m6 ≤ M := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMpos : 0 < M := lt_of_lt_of_le (by omega) hM1
  obtain ⟨d, hψ, hbad⟩ := psi_conductor A v
  let F0 : K → T.V := fun x => f (L.nbar (Multiplicative.ofAdd x))
  have hfone : f 1 = 0 := by
    have h := bigCell_borel L T s φ 0 1 1
    simpa [f, s, L.a_one] using h
  have hF0int : Integrable F0 μ.μ := by
    have h := section_intertwine_integrable L T μ s (by norm_num [s]) f hf L.w
    apply h.congr
    filter_upwards [] with x
    dsimp [F0, f]
    rw [L.w_n_w]
  have hF0zero {x : K} (hx : x ∈ ball v (m : ℤ)) : F0 x = 0 := by
    have hk : L.nbar (Multiplicative.ofAdd x) ∈ L.Kc m := L.nbar_Kc m hm x hx
    calc
      F0 x = f (1 * L.nbar (Multiplicative.ofAdd x)) := by simp [F0]
      _ = f 1 := hK 1 _ hk
      _ = 0 := hfone
  let lmin : ℤ := 1 - (m : ℤ)
  let lidx : ℕ → ℤ := fun n => lmin + (n : ℤ)
  let shell : ℕ → Set K := fun n => jacquetShell v (-lidx n)
  have hlower (n : ℕ) : lmin ≤ lidx n := by simp [lidx]
  let q : ℝ := Ideal.absNorm v.asIdeal
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 1 := ne_of_gt hq
  have hshellMeas (n : ℕ) : MeasurableSet (shell n) :=
    (jacquetShell_compact v (-lidx n)).measurableSet
  have hshellDisjoint : Pairwise fun i j => Disjoint (shell i) (shell j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hri := jacquetShell_mem_radius v (-lidx i) hxi
    have hrj := jacquetShell_mem_radius v (-lidx j) hxj
    have hpow : q ^ (lidx i) = q ^ (lidx j) := by simpa [q] using hri.symm.trans hrj
    have hidx : lidx i = lidx j := (zpow_right_injective₀ hqpos hqne) hpow
    have hij' : i = j := by dsimp [lidx, lmin] at hidx; omega
    exact hij hij'
  have hshellOutside (n : ℕ) : shell n ⊆ (ball v (m : ℤ))ᶜ := by
    intro x hx hxball
    have hval := jacquetShell_valuation v (-lidx n) hx
    have hvalBall : Valued.v x ≤ WithZero.exp (-(m : ℤ)) := by
      change Valued.v x ≤ WithZero.exp (-(m : ℤ)) at hxball
      exact hxball
    have hlt : WithZero.exp (-(m : ℤ)) < Valued.v x := by
      rw [hval]
      exact WithZero.exp_lt_exp.mpr (by dsimp [lmin, lidx]; omega)
    exact (not_lt_of_ge hvalBall) hlt
  have hshellCover : (⋃ n : ℕ, shell n) = (ball v (m : ℤ))ᶜ := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      exact hshellOutside n hn
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        apply hx
        subst x
        change Valued.v (0 : K) ≤ WithZero.exp (-(m : ℤ))
        rw [show Valued.v (0 : K) = 0 by simp]
        exact (WithZero.exp_pos).le
      obtain ⟨k, hk⟩ := jacquetShell_cover v hx0
      have hxval := jacquetShell_valuation v k hk
      have hnotle : ¬ Valued.v x ≤ WithZero.exp (-(m : ℤ)) := by
        intro hle
        apply hx
        exact Set.mem_setOf_eq.mpr hle
      have hlt : WithZero.exp (-(m : ℤ)) < WithZero.exp (-k) := by
        have hlt' : WithZero.exp (-(m : ℤ)) < Valued.v x := lt_of_not_ge hnotle
        rw [hxval] at hlt'
        exact hlt'
      have hl : lmin ≤ -k := by
        have hexp := WithZero.exp_lt_exp.mp hlt
        dsimp [lmin]
        omega
      let n : ℕ := Int.toNat (-k - lmin)
      have hn0 : 0 ≤ -k - lmin := by omega
      have hncast : (n : ℤ) = -k - lmin := Int.toNat_of_nonneg hn0
      have hidx : lidx n = -k := by dsimp [lidx]; omega
      have hk' : k = -lidx n := by omega
      apply Set.mem_iUnion.mpr ⟨n, ?_⟩
      simpa [shell, hk'] using hk
  let kernel : K → K → T.V := fun y x => A.ψ v (-((y : K) * x)) • F0 x
  have hkernelInt (y : K) : Integrable (kernel y) μ.μ := by
    have hphase : IsLocallyConstant (fun x : K => A.ψ v (-((y : K) * x))) := by
      apply (addChar_locallyConstant A).comp_continuous
      exact continuous_neg.comp (continuous_const.mul continuous_id)
    have hAES : AEStronglyMeasurable (kernel y) μ.μ := by
      exact hphase.continuous.aestronglyMeasurable.smul hF0int.aestronglyMeasurable
    have hnorm (x : K) : ‖kernel y x‖ = ‖F0 x‖ := by
      change ‖A.ψ v (-((y : K) * x)) • F0 x‖ = ‖F0 x‖
      rw [norm_smul, addChar_norm_one (v := v) A (-((y : K) * x)), one_mul]
    exact hF0int.mono hAES (ae_of_all _ fun x => (hnorm x).le)
  let shellIntegral : ℕ → K → T.V := fun n y => ∫ x in shell n, kernel y x ∂μ.μ
  let fourier : K → T.V := fun y => ∫ x, kernel y x ∂μ.μ
  have hfourierSum (y : K) : fourier y = ∑' n : ℕ, shellIntegral n y := by
    have hzero (x : K) (hx : x ∉ ⋃ n : ℕ, shell n) : kernel y x = 0 := by
      have hxball : x ∈ ball v (m : ℤ) := by
        rw [hshellCover] at hx
        exact not_not.mp hx
      simp [kernel, hF0zero hxball]
    have hUnionMeas : MeasurableSet (⋃ n : ℕ, shell n) :=
      MeasurableSet.iUnion hshellMeas
    calc
      fourier y = ∫ x in ⋃ n : ℕ, shell n, kernel y x ∂μ.μ := by
        dsimp [fourier]
        exact (setIntegral_eq_integral_of_zero_off hUnionMeas (kernel y) hzero).symm
      _ = ∑' n : ℕ, ∫ x in shell n, kernel y x ∂μ.μ :=
        integral_iUnion hshellMeas hshellDisjoint
          ((hkernelInt y).integrableOn.mono_set (Set.subset_univ _))
      _ = ∑' n : ℕ, shellIntegral n y := by rfl
  have hShellShift (n : ℕ) (x : K) (hx : x ∈ shell n) (b : K)
      (hb : b ∈ ball v ((M : ℤ) - lidx n)) :
      F0 (b + x) = F0 x ∧ b + x ∈ shell n := by
    have hcne : x ≠ 0 := by
      intro hx0
      have hval := jacquetShell_valuation v (-lidx n) hx
      rw [hx0] at hval
      have hzero : Valued.v (0 : K) = 0 := by simp
      rw [hzero] at hval
      exact WithZero.exp_ne_zero hval.symm
    have hvalx := jacquetShell_valuation v (-lidx n) hx
    have hxInv : x⁻¹ ∈ ball v (lidx n) := by
      change Valued.v x⁻¹ ≤ WithZero.exp (-(lidx n))
      rw [show Valued.v x⁻¹ = (Valued.v x)⁻¹ by simp, hvalx]
      simp
    have hmul := jacquet_ball_mul hb hxInv
    have hrel : b * x⁻¹ ∈ ball v (M : ℤ) := by
      have hexp : ((M : ℤ) - lidx n) + lidx n = (M : ℤ) := by omega
      simpa [hexp] using hmul
    have hshift := hrelInv x b hcne
      (ball_mono_int (show (M0 : ℤ) ≤ (M : ℤ) by exact_mod_cast hMM0) hrel)
    have hnonzero : b + x ≠ 0 := by
      intro h0
      have hr := hshift.2
      rw [show x + b = b + x by ac_rfl, h0] at hr
      have hnormzero : ‖x‖ = 0 := by
        simpa only [absFin_eq_norm, norm_zero] using hr.symm
      exact hcne (norm_eq_zero.mp hnormzero)
    have hrad : absFin v (b + x) = q ^ (lidx n) := by
      calc
        absFin v (b + x) = absFin v (x + b) := by congr 1 <;> abel
        _ = absFin v x := hshift.2
        _ = q ^ (lidx n) := by simpa [q] using jacquetShell_mem_radius v (-lidx n) hx
    have hmem : b + x ∈ shell n := by
      apply jacquetShell_of_absFin v (-lidx n) hnonzero
      simpa [q] using hrad
    constructor
    · simpa [F0, add_comm] using hshift.1
    · exact hmem
  have hShellPre (n : ℕ) (b : K) (hb : b ∈ ball v ((M : ℤ) - lidx n)) :
      (MeasurableEquiv.addLeft b) ⁻¹' shell n = shell n := by
    ext x
    change b + x ∈ shell n ↔ x ∈ shell n
    constructor
    · intro hx
      have hneg : -b ∈ ball v ((M : ℤ) - lidx n) := by
        change Valued.v (-b) ≤ WithZero.exp (-((M : ℤ) - lidx n))
        rw [Valuation.map_neg]
        change Valued.v b ≤ WithZero.exp (-((M : ℤ) - lidx n)) at hb
        exact hb
      have h := (hShellShift n (b + x) hx (-b) hneg).2
      have heq : (b + x) + -b = x := by abel
      simpa [heq] using h
    · intro hx
      have h := (hShellShift n x hx b hb).2
      simpa [add_comm] using h
  have hShellIntegralLocallyConstant (n : ℕ) (y δ : K)
      (hδ : δ ∈ ball v ((lidx n : ℤ) - (d : ℤ))) :
      shellIntegral n (y + δ) = shellIntegral n y := by
    apply setIntegral_congr_fun (jacquetShell_compact v (-lidx n)).measurableSet
    intro x hx
    have hxval := jacquetShell_valuation v (-lidx n) hx
    have hxBall : x ∈ ball v (-lidx n) := by
      change Valued.v x ≤ WithZero.exp (-(-lidx n))
      rw [hxval]
    have hprod : δ * x ∈ ball v (-(d : ℤ)) := by
      have h := jacquet_ball_mul hδ hxBall
      have hexp : ((lidx n : ℤ) - (d : ℤ)) + (-lidx n) = -(d : ℤ) := by ring
      rw [hexp] at h
      exact h
    have harg : -((y + δ) * x) = -(y * x) + -(δ * x) := by ring
    change A.ψ v (-((y + δ) * x)) • F0 x = A.ψ v (-(y * x)) • F0 x
    rw [harg, AddChar.map_add_eq_mul, hψ (-(δ * x)) (jacquet_ballNeg_nat_neg d hprod)]
    simp
  have hShellIntegralZero (n : ℕ) (y : K)
      (hy : q ^ ((M : ℤ) + (d : ℤ) - lidx n) < absFin v y) :
      shellIntegral n y = 0 := by
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hy
      have hpos : 0 < q ^ ((M : ℤ) + (d : ℤ) - lidx n) := zpow_pos hqpos _
      have hzero : absFin v (0 : K) = 0 := by unfold absFin; simp
      rw [hzero] at hy
      exact (not_lt_of_ge hpos.le) hy
    obtain ⟨k, hyk⟩ := jacquetShell_cover v hy0
    have hpow : q ^ ((M : ℤ) + (d : ℤ) - lidx n) < q ^ (-k) := by
      simpa [q, jacquetShell_mem_radius v k hyk] using hy
    have hexp : (M : ℤ) + (d : ℤ) - lidx n < -k :=
      (zpow_lt_zpow_iff_right₀ hq).mp hpow
    obtain ⟨b0, hb0, hψb0⟩ := hbad
    have hyInvBall : (y : K)⁻¹ ∈ ball v (-k) := by
      change Valued.v (y : K)⁻¹ ≤ WithZero.exp (-(-k))
      rw [show Valued.v (y : K)⁻¹ = (Valued.v (y : K))⁻¹ by simp,
        jacquetShell_valuation v k hyk]
      simp
    have hscaled := jacquet_ball_mul hb0 hyInvBall
    let msum : ℤ := -((d : ℤ) + 1) + (-k)
    have hscaledBall : (y : K)⁻¹ * b0 ∈ ball v msum := by
      simpa [msum, mul_comm] using hscaled
    have hparam : (M : ℤ) - lidx n ≤ msum := by dsimp [msum]; omega
    have hb : -((y : K)⁻¹ * b0) ∈ ball v ((M : ℤ) - lidx n) := by
      have hneg : -((y : K)⁻¹ * b0) ∈ ball v msum := by
        change Valued.v (-((y : K)⁻¹ * b0)) ≤ WithZero.exp (-msum)
        rw [Valuation.map_neg]
        change Valued.v ((y : K)⁻¹ * b0) ≤ WithZero.exp (-msum) at hscaledBall
        exact hscaledBall
      exact ball_mono_int hparam hneg
    have harg : -((y : K) * (-((y : K)⁻¹ * b0))) = b0 := by
      calc
        -((y : K) * (-((y : K)⁻¹ * b0))) = (y : K) * ((y : K)⁻¹ * b0) := by ring
        _ = ((y : K) * (y : K)⁻¹) * b0 := by ac_rfl
        _ = b0 := by rw [mul_inv_cancel₀ hy0]; simp
    have hnontriv : A.ψ v (-((y : K) * (-((y : K)⁻¹ * b0)))) ≠ 1 := by
      rw [harg]
      exact hψb0
    exact integral_fourier_shell_zero μ A y (-((y : K)⁻¹ * b0)) (shell n)
      (jacquetShell_compact v (-lidx n)).measurableSet (hShellPre n _ hb) F0
      (fun x hx => (hShellShift n x hx _ hb).1) hnontriv
  have hFourierZero {y : K}
      (hy : q ^ ((M : ℤ) + (d : ℤ) - lmin) < absFin v y) : fourier y = 0 := by
    have hzero (n : ℕ) : shellIntegral n y = 0 := by
      apply hShellIntegralZero n y
      have hpow : q ^ ((M : ℤ) + (d : ℤ) - lidx n) ≤
          q ^ ((M : ℤ) + (d : ℤ) - lmin) := by
        rw [zpow_le_zpow_iff_right₀ hq]
        have hl := hlower n
        dsimp [lidx, lmin] at *
        omega
      exact lt_of_le_of_lt hpow hy
    calc
      fourier y = ∑' n : ℕ, shellIntegral n y := hfourierSum y
      _ = ∑' n : ℕ, (0 : T.V) := tsum_congr fun n => hzero n
      _ = 0 := tsum_zero
  have hRotFormula (y : K) (hy : y ≠ 0) :
      rotatedCoord L T A μ s φ c y =
        ((absFin v y : ℂ) ^ ((1 : ℂ) / 3)) *
          c (T.σa (Units.mk0 y hy)⁻¹ (fourier y)) := by
    have hAbs : absFin v (Units.mk0 y hy : Kˣ) = absFin v y := rfl
    have hUnit : ((Units.mk0 y hy : Kˣ) : K) = y := rfl
    unfold rotatedCoord
    rw [dif_pos hy]
    calc
      c (jacquet L A μ (rtr (L.a (Units.mk0 y hy) * L.w) f)) =
      c (((absFin v (Units.mk0 y hy) : ℂ) ^ ((1 : ℂ) / 2 - s)) •
            T.σa (Units.mk0 y hy)⁻¹
              (∫ x, A.ψ v (-((y : K) * x)) •
                bigCell L T s φ (L.nbar (Multiplicative.ofAdd x)) ∂μ.μ)) := by
          change c (jacquet L A μ (rtr (L.a (Units.mk0 y hy) * L.w)
            (bigCell L T s φ))) = _
          rw [jacquet_rotated L T A μ s (by norm_num [s]) φ hφ hc (Units.mk0 y hy)]
          rw [hUnit]
      _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) *
            c (T.σa (Units.mk0 y hy)⁻¹
              (∫ x, A.ψ v (-((y : K) * x)) •
                bigCell L T s φ (L.nbar (Multiplicative.ofAdd x)) ∂μ.μ)) := by
          rw [map_smul, smul_eq_mul, hAbs]
      _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 3)) *
            c (T.σa (Units.mk0 y hy)⁻¹ (fourier y)) := by
          have hexp : (1 : ℂ) / 2 - s = (1 : ℂ) / 3 := by norm_num [s]
          have hInt :
              (∫ x, A.ψ v (-((y : K) * x)) •
                bigCell L T s φ (L.nbar (Multiplicative.ofAdd x)) ∂μ.μ) = fourier y := rfl
          rw [hexp, hInt]
  have hcut : ∃ C : ℝ, ∀ y : K, C < absFin v y →
      rotatedCoord L T A μ s φ c y = 0 := by
    let C : ℝ := q ^ ((M : ℤ) + (d : ℤ) - lmin)
    have hCpos : 0 < C := by dsimp [C]; positivity
    refine ⟨C, ?_⟩
    intro y hy
    by_cases hy0 : y = 0
    · simp [rotatedCoord, hy0]
    · rw [hRotFormula y hy0]
      have hzero : fourier y = 0 := hFourierZero (by simpa [C] using hy)
      simp [hzero]
  obtain ⟨Cσ, hCσ, hσbound⟩ := torus_sigma_uniform_bound T
  let cCLM : T.V →L[ℂ] ℂ := ⟨c, LinearMap.continuous_of_finiteDimensional c⟩
  let J : ℝ := ∫ x, ‖F0 x‖ ∂μ.μ
  let Csmall : ℝ := ‖cCLM‖ * Cσ * J
  have hJ : 0 ≤ J := by dsimp [J]; exact integral_nonneg fun x => norm_nonneg _
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hCσ) hJ
  have hFourierNorm (y : K) : ‖fourier y‖ ≤ J := by
    dsimp [fourier]
    calc
      ‖∫ x, kernel y x ∂μ.μ‖ ≤ ∫ x, ‖kernel y x‖ ∂μ.μ := norm_integral_le_integral_norm _
      _ = J := by
        dsimp [J]
        apply integral_congr_ae
        filter_upwards [] with x
        change ‖A.ψ v (-((y : K) * x)) • F0 x‖ = ‖F0 x‖
        rw [norm_smul, addChar_norm_one (v := v) A (-((y : K) * x)), one_mul]
  have hsmall : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : K, y ≠ 0 → absFin v y ≤ 1 →
      ‖rotatedCoord L T A μ s φ c y‖ ≤ C * absFin v y ^ (1 / 3 : ℝ) := by
    refine ⟨Csmall, hCsmall, ?_⟩
    intro y hy hyq
    rw [hRotFormula y hy]
    have hpos : 0 < absFin v y := absFin_pos hy
    have hscalarNorm :
        ‖((absFin v y : ℝ) : ℂ) ^ ((1 : ℂ) / 3)‖ = absFin v y ^ (1 / 3 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
    have hop (z : T.V) : ‖cCLM z‖ ≤ ‖cCLM‖ * ‖z‖ := cCLM.le_opNorm z
    have hvector :
        ‖cCLM (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ ≤ ‖cCLM‖ * (Cσ * J) := by
      calc
        ‖cCLM (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ ≤
            ‖cCLM‖ * ‖T.σa (Units.mk0 y hy)⁻¹ (fourier y)‖ := hop _
        _ ≤ ‖cCLM‖ * (Cσ * ‖fourier y‖) :=
            mul_le_mul_of_nonneg_left (hσbound _ _) (norm_nonneg _)
        _ ≤ ‖cCLM‖ * (Cσ * J) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left (hFourierNorm y) hCσ
            · exact norm_nonneg _
    have hvector' :
        ‖cCLM (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ ≤ Csmall := by
      simpa [Csmall, mul_assoc] using hvector
    have hnormmap :
        ‖c (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ =
          ‖cCLM (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ := rfl
    calc
      ‖((absFin v y : ℝ) : ℂ) ^ ((1 : ℂ) / 3) *
          c (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ =
          absFin v y ^ (1 / 3 : ℝ) *
            ‖cCLM (T.σa (Units.mk0 y hy)⁻¹ (fourier y))‖ := by
              rw [norm_mul, hscalarNorm, hnormmap]
      _ ≤ absFin v y ^ (1 / 3 : ℝ) * Csmall :=
            mul_le_mul_of_nonneg_left hvector' (Real.rpow_nonneg hpos.le _)
      _ = Csmall * absFin v y ^ (1 / 3 : ℝ) := by ring
  have hmuOne : muThree D (1 : rootsOfUnity 6 F) = 1 := by
    apply rootsOfUnity.coe_injective
    simp [muThree]
  have hlocal : ∀ y0 : K, y0 ≠ 0 →
      ∃ U : Set K, IsOpen U ∧ y0 ∈ U ∧ ∀ y ∈ U,
        rotatedCoord L T A μ s φ c y = rotatedCoord L T A μ s φ c y0 := by
    intro y0 hy0
    obtain ⟨k0, hk0⟩ := jacquetShell_cover v hy0
    let l0 : ℤ := -k0
    have hval0 : Valued.v y0 = WithZero.exp l0 := by
      simpa [l0] using jacquetShell_valuation v k0 hk0
    have hrad0 : absFin v y0 = q ^ l0 := by
      simpa [q, l0] using jacquetShell_mem_radius v k0 hk0
    let E : ℤ := (M : ℤ) + (d : ℤ) - l0
    let N : ℕ := if lmin ≤ E then Int.toNat (E - lmin + 1) else 0
    have hNtail (n : ℕ) (hn : N ≤ n) : E < lidx n := by
      by_cases h : lmin ≤ E
      · have hNcast : (N : ℤ) = E - lmin + 1 := by
          dsimp [N]
          rw [if_pos h]
          exact Int.toNat_of_nonneg (by omega)
        dsimp [lidx]
        omega
      · have hlt : E < lmin := by omega
        have hi := hlower n
        omega
    have hfourierFinite (y : K) (hyRad : absFin v y = q ^ l0) :
        fourier y = ∑ n ∈ Finset.range N, shellIntegral n y := by
      have hsum :
          (∑' n : ℕ, shellIntegral n y) = ∑ n ∈ Finset.range N, shellIntegral n y := by
        apply tsum_eq_sum (s := Finset.range N)
        intro n hn
        have hnN : N ≤ n := by
          by_contra hlt
          exact hn (Finset.mem_range.mpr (Nat.lt_of_not_ge hlt))
        have hli := hNtail n hnN
        have hpow : q ^ ((M : ℤ) + (d : ℤ) - lidx n) < q ^ l0 := by
          apply (zpow_lt_zpow_iff_right₀ hq).mpr
          dsimp [E] at hli ⊢
          omega
        have hyShellBound : q ^ ((M : ℤ) + (d : ℤ) - lidx n) < absFin v y := by
          rw [hyRad]
          exact hpow
        exact hShellIntegralZero n y hyShellBound
      exact (hfourierSum y).trans hsum
    let Dloc : ℤ := max (1 - l0)
      (max ((M : ℤ) - l0) (lmin + (N : ℤ) - 1 - (d : ℤ)))
    have hD1 : 1 - l0 ≤ Dloc := le_max_left _ _
    have hDM : (M : ℤ) - l0 ≤ Dloc := le_trans (le_max_left _ _) (le_max_right _ _)
    have hDFour : lmin + (N : ℤ) - 1 - (d : ℤ) ≤ Dloc :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    let U : Set K := {y | y - y0 ∈ ball v Dloc}
    have hUopen : IsOpen U := by
      dsimp [U]
      exact (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
        (continuous_id.sub continuous_const)
    have hy0U : y0 ∈ U := by
      change y0 - y0 ∈ ball v Dloc
      rw [sub_self]
      change Valued.v (0 : K) ≤ WithZero.exp (-Dloc)
      rw [show Valued.v (0 : K) = 0 by simp]
      exact (WithZero.exp_pos).le
    refine ⟨U, hUopen, hy0U, ?_⟩
    intro y hyU
    let δ : K := y - y0
    have hδ : δ ∈ ball v Dloc := by simpa [U, δ] using hyU
    have hyEq : y = y0 + δ := by dsimp [δ]; abel
    have hδVal : Valued.v δ < Valued.v y0 := by
      have hδball : Valued.v δ ≤ WithZero.exp (-Dloc) := by
        change Valued.v δ ≤ WithZero.exp (-Dloc) at hδ
        exact hδ
      have hle : WithZero.exp (-Dloc) ≤ WithZero.exp (l0 - 1) :=
        WithZero.exp_le_exp.mpr (by have := hD1; omega)
      have hlt : WithZero.exp (l0 - 1) < WithZero.exp l0 :=
        WithZero.exp_lt_exp.mpr (by omega)
      rw [hval0]
      exact (hδball.trans hle).trans_lt hlt
    have hvalAdd : Valued.v (y0 + δ) = Valued.v y0 := by
      have h := Valuation.map_add_eq_of_lt_right
        (v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
        (x := δ) (y := y0) hδVal
      simpa [add_comm] using h
    have hvalY : Valued.v y = Valued.v y0 := by
      calc
        Valued.v y = Valued.v (y0 + δ) := by rw [hyEq]
        _ = Valued.v y0 := hvalAdd
    have hyne : y ≠ 0 := by
      intro hzero
      have hvalZero : Valued.v (0 : K) = Valued.v y0 := by simpa [hzero] using hvalY
      rw [show Valued.v (0 : K) = 0 by simp, hval0] at hvalZero
      exact WithZero.exp_ne_zero hvalZero.symm
    have hradAdd : absFin v (y0 + δ) = absFin v y0 := by
      unfold absFin
      rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v),
        dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hvalAdd]
    have hradY : absFin v y = q ^ l0 := by
      calc
        absFin v y = absFin v y0 := by rw [hyEq]; exact hradAdd
        _ = q ^ l0 := hrad0
    have hFourierEq : fourier y = fourier y0 := by
      rw [hfourierFinite y hradY, hfourierFinite y0 hrad0]
      apply Finset.sum_congr rfl
      intro n hn
      have hnlt : n < N := Finset.mem_range.mp hn
      have hidxBound : (lidx n : ℤ) - (d : ℤ) ≤
          lmin + (N : ℤ) - 1 - (d : ℤ) := by
        dsimp [lidx, lmin]
        omega
      have hδupper : δ ∈ ball v (lmin + (N : ℤ) - 1 - (d : ℤ)) :=
        ball_mono_int hDFour hδ
      have hδn : δ ∈ ball v ((lidx n : ℤ) - (d : ℤ)) :=
        ball_mono_int hidxBound hδupper
      rw [hyEq]
      exact hShellIntegralLocallyConstant n y0 δ hδn
    let Y0 : Kˣ := Units.mk0 y0 hy0
    let Y : Kˣ := Units.mk0 y hyne
    let u : Kˣ := Y * Y0⁻¹
    have hY0val : (Y0 : K) = y0 := rfl
    have hYval : (Y : K) = y := rfl
    have hUminus : (u : K) - 1 = δ * (Y0⁻¹ : K) := by
      dsimp [u]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [hYval, hY0val, hyEq]
      calc
        (y0 + δ) * y0⁻¹ - 1 = y0 * y0⁻¹ + δ * y0⁻¹ - 1 := by rw [add_mul]
        _ = δ * y0⁻¹ := by rw [mul_inv_cancel₀ hy0]; ring
    have hY0invBall : (Y0⁻¹ : K) ∈ ball v l0 := by
      change Valued.v (Y0⁻¹ : K) ≤ WithZero.exp (-l0)
      rw [show Valued.v (Y0⁻¹ : K) = (Valued.v (Y0 : K))⁻¹ by simp,
        hY0val, hval0]
      simp
    have hrel : δ * (Y0⁻¹ : K) ∈ ball v (M : ℤ) := by
      have h := jacquet_ball_mul hδ hY0invBall
      have hparam : (M : ℤ) ≤ Dloc + l0 := by have := hDM; omega
      exact ball_mono_int hparam (by simpa [add_comm] using h)
    have huNear : (u : K) - 1 ∈ ball v (M : ℤ) := by rw [hUminus]; exact hrel
    have hUminusVal : Valued.v ((u : K) - 1) < 1 := by
      have hball : Valued.v ((u : K) - 1) ≤ WithZero.exp (-(M : ℤ)) := by
        change Valued.v ((u : K) - 1) ≤ WithZero.exp (-(M : ℤ)) at huNear
        exact huNear
      have hlt : WithZero.exp (-(M : ℤ)) < 1 := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        exact neg_lt_zero.mpr (show (0 : ℤ) < (M : ℤ) by exact_mod_cast hMpos)
      exact lt_of_le_of_lt hball hlt
    have huVal : Valued.v (u : K) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right
        (v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
        (x := (u : K) - 1) (y := (1 : K)) (by simpa using hUminusVal)
      have hiden : (u : K) = ((u : K) - 1) + 1 := by ring
      rw [hiden]
      simpa [sub_add_cancel] using h
    have huInvVal : Valued.v ((u⁻¹ : Kˣ) : K) = 1 := by
      rw [show Valued.v ((u⁻¹ : Kˣ) : K) = (Valued.v (u : K))⁻¹ by simp, huVal]
      simp
    have huInvBall0 : ((u⁻¹ : Kˣ) : K) ∈ ball v (0 : ℤ) := by
      change Valued.v ((u⁻¹ : Kˣ) : K) ≤ WithZero.exp (-(0 : ℤ))
      rw [huInvVal]
      simp
    have hInvId : ((u⁻¹ : Kˣ) : K) - 1 =
        -(((u : K) - 1) * ((u⁻¹ : Kˣ) : K)) := by
      simp only [Units.val_inv_eq_inv_val]
      change (u : K)⁻¹ - 1 = -(((u : K) - 1) * (u : K)⁻¹)
      calc
        (u : K)⁻¹ - 1 = (u : K)⁻¹ - (u : K)⁻¹ * (u : K) := by
          rw [inv_mul_cancel₀ u.ne_zero]
        _ = -(((u : K) - 1) * (u : K)⁻¹) := by ring
    have hInvDelta : -(((u : K) - 1) * ((u⁻¹ : Kˣ) : K)) ∈ ball v (M : ℤ) := by
      have hprod := jacquet_ball_mul huNear huInvBall0
      have hprod' : ((u : K) - 1) * ((u⁻¹ : Kˣ) : K) ∈ ball v (M : ℤ) := by
        simpa using hprod
      change Valued.v (-(((u : K) - 1) * ((u⁻¹ : Kˣ) : K))) ≤ WithZero.exp (-(M : ℤ))
      rw [Valuation.map_neg]
      change Valued.v (((u : K) - 1) * ((u⁻¹ : Kˣ) : K)) ≤ WithZero.exp (-(M : ℤ)) at hprod'
      exact hprod'
    have huInvNear : ((u⁻¹ : Kˣ) : K) - 1 ∈ ball v (mT : ℤ) := by
      rw [hInvId]
      exact ball_mono_int (show (mT : ℤ) ≤ (M : ℤ) by exact_mod_cast hMmT) hInvDelta
    obtain ⟨a, ha⟩ := hsix u (ball_mono_int (show (m6 : ℤ) ≤ (M : ℤ) by exact_mod_cast hMm6) huNear)
    have huInvSix : ∃ a' : Kˣ, u⁻¹ = a' ^ 6 := by
      refine ⟨a⁻¹, ?_⟩
      rw [ha]
      group
    have hσuInv : T.σa u⁻¹ = LinearMap.id := hσsmooth u⁻¹ huInvNear
    have hHilbOpp : H.hilb v u⁻¹ (Y0⁻¹) = 1 :=
      H.sixth_power v u⁻¹ (Y0⁻¹) huInvSix
    have hHilb : H.hilb v (Y0⁻¹) u⁻¹ = 1 := by
      have h := H.skew v (Y0⁻¹) u⁻¹
      rw [hHilbOpp] at h
      simpa using h
    have hσmul := T.σa_mul (Y0⁻¹) u⁻¹
    rw [hσuInv, hHilb, hmuOne] at hσmul
    have hσmap : T.σa (Y0⁻¹) = T.σa (Y0⁻¹ * u⁻¹) := by simpa using hσmul
    have hYrel : Y = u * Y0 := by dsimp [u]; group
    have hYinv : Y⁻¹ = Y0⁻¹ * u⁻¹ := by rw [hYrel]; group
    have hσeq : T.σa Y⁻¹ = T.σa (Y0⁻¹) := by
      rw [hYinv]
      simpa [mul_comm] using hσmap.symm
    have hRotEq : rotatedCoord L T A μ s φ c y =
        rotatedCoord L T A μ s φ c y0 := by
      calc
        rotatedCoord L T A μ s φ c y =
            ((absFin v y : ℂ) ^ ((1 : ℂ) / 3)) *
              c (T.σa Y⁻¹ (fourier y)) := hRotFormula y hyne
        _ = ((absFin v y0 : ℂ) ^ ((1 : ℂ) / 3)) *
              c (T.σa (Y0⁻¹) (fourier y0)) := by rw [hradY, hrad0, hσeq, hFourierEq]
        _ = rotatedCoord L T A μ s φ c y0 := (hRotFormula y0 hy0).symm
    exact hRotEq
  rcases hsmall with ⟨Cval, hCval, hbound⟩
  exact ⟨hlocal, hcut, ⟨Cval, hbound⟩⟩

/-- **def:intertwine**: `(M f)(g) = ∫ f(w n(x) g) dx`. -/
def intertwine (L : FinLocalCover D H v) (μ : LocHaar v) (f : L.L → V) : L.L → V :=
  fun g => ∫ x, f (L.w * L.n (Multiplicative.ofAdd x) * g) ∂μ.μ

/-- **int:section**: for `Re s > 0`, `M : I(σ, s) → I(σ^w, -s)` (absolutely convergent). -/
theorem intertwine_isSection (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v)
    (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f) :
    (∀ g, Integrable (fun x => f (L.w * L.n (Multiplicative.ofAdd x) * g)) μ.μ) ∧
      IsSection L T.weyl (-s) (intertwine L μ f) := by
  classical
  let K := v.adicCompletion F
  refine ⟨?_, ?_⟩
  · intro g
    exact section_intertwine_integrable L T μ s hs f hf g
  · refine ⟨?_, ?_, ?_⟩
    · intro x y g
      let yInv : Kˣ := y⁻¹
      let hfun : K → T.V := fun t => f (L.w * L.n (Multiplicative.ofAdd t) * g)
      let σ : T.V →L[ℂ] T.V := (T.σa yInv).toContinuousLinearMap
      let F : K → T.V := fun t => σ (hfun t)
      have hInt : Integrable hfun μ.μ := by
        exact section_intertwine_integrable L T μ s hs f hf g
      have hwa : L.w * L.a y = L.a yInv * L.w := by
        have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
        calc
          L.w * L.a y = (L.w * L.a y * L.w⁻¹) * L.w := by group
          _ = L.a y⁻¹ * L.w := by rw [L.lift_wa]
      have htor (z : K) :
          L.w * L.n (Multiplicative.ofAdd z) * L.a y =
            L.a yInv * L.w * L.n (Multiplicative.ofAdd (z * (yInv : K))) := by
        calc
          L.w * L.n (Multiplicative.ofAdd z) * L.a y =
              L.w * (L.n (Multiplicative.ofAdd z) * L.a y) := by simp [mul_assoc]
          _ = L.w * (L.a y * L.n (Multiplicative.ofAdd (z * (yInv : K)))) := by
            rw [L.lift_na]
          _ = (L.w * L.a y) * L.n (Multiplicative.ofAdd (z * (yInv : K))) := by
            simp [mul_assoc]
          _ = (L.a yInv * L.w) * L.n (Multiplicative.ofAdd (z * (yInv : K))) := by
            rw [hwa]
          _ = L.a yInv * L.w * L.n (Multiplicative.ofAdd (z * (yInv : K))) := by
            simp [mul_assoc]
      have hgroup (t : K) :
          L.w * L.n (Multiplicative.ofAdd t) * (L.n (Multiplicative.ofAdd x) * L.a y * g) =
            L.a yInv * L.w * L.n (Multiplicative.ofAdd ((t + x) * (yInv : K))) * g := by
        calc
          L.w * L.n (Multiplicative.ofAdd t) *
              (L.n (Multiplicative.ofAdd x) * L.a y * g) =
                (L.w * L.n (Multiplicative.ofAdd (t + x)) * L.a y) * g := by
                  simp [ofAdd_add, mul_assoc]
          _ = (L.a yInv * L.w *
                L.n (Multiplicative.ofAdd ((t + x) * (yInv : K)))) * g := by
                  rw [htor]
          _ = L.a yInv * L.w *
                L.n (Multiplicative.ofAdd ((t + x) * (yInv : K))) * g := by
                  simp [mul_assoc]
      have hpoint (t : K) :
          f (L.w * L.n (Multiplicative.ofAdd t) *
              (L.n (Multiplicative.ofAdd x) * L.a y * g)) =
            ((absFin v yInv : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              F ((yInv : K) * (t + x)) := by
        rw [hgroup]
        have h := hf.1 0 yInv
          (L.w * L.n (Multiplicative.ofAdd ((t + x) * (yInv : K))) * g)
        have hmul : ((t + x) * (yInv : K)) = (yInv : K) * (t + x) := by ring
        simpa [F, hfun, σ, hmul, mul_assoc] using h
      have hshift :
          (∫ t, F ((yInv : K) * (t + x)) ∂μ.μ) =
            ∫ t, F ((yInv : K) * t) ∂μ.μ := by
        calc
          (∫ t, F ((yInv : K) * (t + x)) ∂μ.μ) =
              ∫ t, F ((yInv : K) * (x + t)) ∂μ.μ := by
                apply integral_congr_ae
                filter_upwards [] with t
                congr 1
                ring
          _ = ∫ t, F ((yInv : K) * t) ∂μ.μ :=
                locHaar_integral_comp_addLeft μ x (fun t : K => F ((yInv : K) * t))
      have hscale := LocHaar.integral_comp_mul μ yInv F
      have hInv : absFin v yInv = (absFin v y)⁻¹ := by
        have hprod : absFin v y * absFin v yInv = 1 := by
          simpa [yInv, absFin_eq_norm] using (absFin_mul v y y⁻¹).symm
        have hAB : absFin v y = (absFin v yInv)⁻¹ :=
          eq_inv_of_mul_eq_one_left hprod
        calc
          absFin v yInv = ((absFin v yInv)⁻¹)⁻¹ := by simp
          _ = (absFin v y)⁻¹ := by rw [← hAB]
      let q : ℝ := absFin v y
      have hqpos : 0 < q := by
        dsimp [q]
        exact absFin_pos y.ne_zero
      have hqComplex : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
      let C : ℂ := ((absFin v yInv : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s)
      have hbase : ((absFin v yInv : ℝ) : ℂ) = (q : ℂ)⁻¹ := by
        dsimp [q]
        exact_mod_cast hInv
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
        intertwine L μ f (L.n (Multiplicative.ofAdd x) * L.a y * g) =
            ∫ t, f (L.w * L.n (Multiplicative.ofAdd t) *
              (L.n (Multiplicative.ofAdd x) * L.a y * g)) ∂μ.μ := rfl
        _ = C • ∫ t, F ((yInv : K) * (t + x)) ∂μ.μ := by
          rw [show (fun t => f (L.w * L.n (Multiplicative.ofAdd t) *
              (L.n (Multiplicative.ofAdd x) * L.a y * g))) =
              (fun t => C • F ((yInv : K) * (t + x))) from funext hpoint]
          rw [integral_smul]
        _ = C • ∫ t, F ((yInv : K) * t) ∂μ.μ := by rw [hshift]
        _ = C • ((absFin v yInv)⁻¹ • ∫ t, F t ∂μ.μ) := by rw [hscale]
        _ = (C * (q : ℂ)) • (σ (∫ t, hfun t ∂μ.μ)) := by
          have hreal : ((absFin v yInv)⁻¹ : ℝ) = q := by
            dsimp [q]
            rw [hInv]
            simp
          have hrealSmul (z : T.V) :
              (absFin v yInv)⁻¹ • z = (q : ℂ) • z := by
            rw [hreal]
            symm
            exact IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) q z
          rw [hrealSmul, smul_smul]
          have hmap : (∫ t, F t ∂μ.μ) = σ (∫ t, hfun t ∂μ.μ) := by
            exact ContinuousLinearMap.integral_comp_comm σ hInt
          rw [hmap]
        _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - s)) •
              T.σa y⁻¹ (intertwine L μ f g) := by
          rw [hcoef]
          simp [σ, hfun, intertwine, yInv, q]
    · intro ζ g
      change (∫ x, f (L.w * L.n (Multiplicative.ofAdd x) * (L.z ζ * g)) ∂μ.μ) =
        ((ζ : ℂˣ) : ℂ) • intertwine L μ f g
      have hgroup (x : K) :
          L.w * L.n (Multiplicative.ofAdd x) * (L.z ζ * g) =
            L.z ζ * (L.w * L.n (Multiplicative.ofAdd x) * g) := by
        calc
          L.w * L.n (Multiplicative.ofAdd x) * (L.z ζ * g) =
              (L.w * L.n (Multiplicative.ofAdd x) * L.z ζ) * g := by group
          _ = (L.z ζ * (L.w * L.n (Multiplicative.ofAdd x))) * g := by
              rw [← L.z_central ζ (L.w * L.n (Multiplicative.ofAdd x))]
          _ = L.z ζ * (L.w * L.n (Multiplicative.ofAdd x) * g) := by group
      calc
        _ = ∫ x, f (L.z ζ * (L.w * L.n (Multiplicative.ofAdd x) * g)) ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact congrArg f (hgroup x)
        _ = ∫ x, ((ζ : ℂˣ) : ℂ) •
              f (L.w * L.n (Multiplicative.ofAdd x) * g) ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hf.2.1 ζ _
        _ = ((ζ : ℂˣ) : ℂ) • intertwine L μ f g := by
          rw [integral_smul]
          rfl
    · obtain ⟨m, hm, hK⟩ := hf.2.2
      refine ⟨m, hm, ?_⟩
      intro g k hk
      change (∫ x, f (L.w * L.n (Multiplicative.ofAdd x) * (g * k)) ∂μ.μ) =
        ∫ x, f (L.w * L.n (Multiplicative.ofAdd x) * g) ∂μ.μ
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show L.w * L.n (Multiplicative.ofAdd x) * (g * k) =
          (L.w * L.n (Multiplicative.ofAdd x) * g) * k by group]
      exact hK (L.w * L.n (Multiplicative.ofAdd x) * g) k hk

/-- **int:rtr**: `M` commutes with right translation. -/
theorem intertwine_rtr (L : FinLocalCover D H v) (μ : LocHaar v) (f : L.L → V) (g : L.L) :
    intertwine L μ (rtr g f) = rtr g (intertwine L μ f) := by
  funext h
  simp [intertwine, rtr, mul_assoc]

/-- The local constant `c_v(s) = (1 - q^{-1-6s})/(1 - q^{-6s})`. -/
def cv (v : FinPlace F) (s : ℂ) : ℂ :=
  (1 - (qv v : ℂ) ^ (-1 - 6 * s)) / (1 - (qv v : ℂ) ^ (-6 * s))

private theorem spherical_wn_formula (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (x : v.adicCompletion F) (hx : x ≠ 0)
    (hxInv : Valued.v x⁻¹ < 1) :
    f (L.w * L.n (Multiplicative.ofAdd x)) =
      ((absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) : ℂ) ^
          ((1 : ℂ) / 2 + s)) •
        T.σa (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) (f 1) := by
  let X : (v.adicCompletion F)ˣ := Units.mk0 x hx
  let y : (v.adicCompletion F)ˣ := -(X⁻¹ * X⁻¹)
  have hBruhat : L.w * L.n (Multiplicative.ofAdd x) =
      L.n (Multiplicative.ofAdd x⁻¹) * L.a y *
        L.nbar (Multiplicative.ofAdd x⁻¹) := by
    simpa [X, y] using L.lift_wn X
  have hbarK : L.nbar (Multiplicative.ofAdd x⁻¹) ∈ τ.Kmax := τ.nbar_mem x⁻¹ hxInv
  have hright : f (L.nbar (Multiplicative.ofAdd x⁻¹)) = f 1 := by
    simpa using hK 1 (L.nbar (Multiplicative.ofAdd x⁻¹)) hbarK
  calc
    f (L.w * L.n (Multiplicative.ofAdd x)) =
        f (L.n (Multiplicative.ofAdd x⁻¹) * L.a y *
          L.nbar (Multiplicative.ofAdd x⁻¹)) := by rw [hBruhat]
    _ = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa y (f (L.nbar (Multiplicative.ofAdd x⁻¹))) := hf.1 _ _ _
    _ = _ := by rw [hright]; rfl

private theorem locUnit_of_valuation_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : IsLocUnit v u := by
  have hvalInv : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [show Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (Valued.v (u : v.adicCompletion F))⁻¹ by simp, hu]
    simp
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (u : v.adicCompletion F) ≤ 1
    rw [hu]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
    rw [hvalInv]

private theorem absFin_one_of_valuation_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    absFin v (u : v.adicCompletion F) = 1 := by
  rw [absFin_eq_norm]
  exact Valued.toNormedField.norm_eq_one_iff.mpr hu

private theorem spherical_shell_pointwise_aux (L : FinLocalCover D H v)
    (τ : TameSplitting L) (T : TorusRep D H v) (B : TameTorusBasis T)
    (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f)
    (h1 : f 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (l : ℕ) (x : v.adicCompletion F) (hx : x ≠ 0)
    (hxInv : Valued.v x⁻¹ < 1) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u)
    (hsplit : -((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹) =
      unifLoc v ^ (2 * (l : ℤ)) * u) :
    f (L.w * L.n (Multiplicative.ofAdd x)) =
      (((absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) : ℂ) ^
          ((1 : ℂ) / 2 + s)) *
        (localChi D v u) ^ (4 * (l : ℤ))) • B.e ((2 : ZMod 3) * (l : ZMod 3)) := by
  have hact := B.act (2 * (l : ℤ)) u hu (0 : ZMod 3)
  have hact' : T.σa (unifLoc v ^ (2 * (l : ℤ)) * u) (B.e 0) =
      (localChi D v u) ^ (4 * (l : ℤ)) • B.e ((2 : ZMod 3) * (l : ZMod 3)) := by
    have hexp : 2 * (2 * (l : ℤ)) = 4 * (l : ℤ) := by ring
    simp [ZMod.val_zero] at hact
    rw [hexp] at hact
    simpa using hact
  rw [spherical_wn_formula L τ T s f hf hK x hx hxInv, h1, hsplit, hact']
  simp only [smul_smul]

private theorem spherical_shell_torus_decomp (l : ℕ) (hl : 0 < l)
    (x : v.adicCompletion F) (hx : x ≠ 0)
    (hxS : x ∈ jacquetShell v (-(l : ℤ))) :
    ∃ u : (v.adicCompletion F)ˣ, IsLocUnit v u ∧
      Valued.v (u : v.adicCompletion F) = 1 ∧
      -((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹) =
        unifLoc v ^ (2 * (l : ℤ)) * u := by
  let X : (v.adicCompletion F)ˣ := Units.mk0 x hx
  let y : (v.adicCompletion F)ˣ := -(X⁻¹ * X⁻¹)
  let π : (v.adicCompletion F)ˣ := unifLoc v
  let u : (v.adicCompletion F)ˣ := π ^ (-(2 * (l : ℤ))) * y
  have hxval : Valued.v x = WithZero.exp (l : ℤ) := by
    simpa using jacquetShell_valuation v (-(l : ℤ)) hxS
  have hyval : Valued.v (y : v.adicCompletion F) = WithZero.exp (-(2 * (l : ℤ))) := by
    have hExp : -(l : ℤ) + -(l : ℤ) = -(2 * (l : ℤ)) := by ring
    simp [y, X, hxval, ← WithZero.exp_add, hExp]
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    simpa [π] using jacquet_unifLoc_valuation v
  have huval : Valued.v (u : v.adicCompletion F) = 1 := by
    have hmul : Valued.v (u : v.adicCompletion F) =
        Valued.v (π : v.adicCompletion F) ^ (-(2 * (l : ℤ))) *
          Valued.v (y : v.adicCompletion F) := by simp [u]
    rw [hmul, hπval, hyval]
    calc
      WithZero.exp (-1 : ℤ) ^ (-(2 * (l : ℤ))) *
          WithZero.exp (-(2 * (l : ℤ))) =
        WithZero.exp (2 * (l : ℤ)) * WithZero.exp (-(2 * (l : ℤ))) := by
          rw [← WithZero.exp_zsmul]
          rw [show (-(2 * (l : ℤ))) • (-1 : ℤ) = 2 * (l : ℤ) by ring]
      _ = WithZero.exp (2 * (l : ℤ) + -(2 * (l : ℤ))) := by
        rw [← WithZero.exp_add]
      _ = 1 := by simp
  have hsplit : y = π ^ (2 * (l : ℤ)) * u := by
    dsimp [u]
    calc
      y = (π ^ (2 * (l : ℤ)) * π ^ (-(2 * (l : ℤ)))) * y := by simp
      _ = π ^ (2 * (l : ℤ)) * (π ^ (-(2 * (l : ℤ))) * y) := by group
  refine ⟨u, locUnit_of_valuation_one u huval, huval, ?_⟩
  simpa [X, y, π] using hsplit

private theorem spherical_shell_pointwise (L : FinLocalCover D H v)
    (τ : TameSplitting L) (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) (f : L.L → T.V)
    (hf : IsSection L T s f) (h1 : f 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (l : ℕ) (hl : 0 < l) (x : v.adicCompletion F) (hx : x ≠ 0)
    (hxS : x ∈ jacquetShell v (-(l : ℤ))) :
    (3 ∣ l → f (L.w * L.n (Multiplicative.ofAdd x)) =
      ((absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) : ℂ) ^
        ((1 : ℂ) / 2 + s)) • B.e 0) ∧
    (¬ 3 ∣ l → ∃ c : ℂ,
      f (L.w * L.n (Multiplicative.ofAdd x)) =
        c • B.e ((2 : ZMod 3) * (l : ZMod 3))) := by
  obtain ⟨u, hu, huval, hsplit⟩ := spherical_shell_torus_decomp l hl x hx hxS
  have hxInv : Valued.v x⁻¹ < 1 := by
    rw [show Valued.v x⁻¹ = (Valued.v x)⁻¹ by simp,
      jacquetShell_valuation v (-(l : ℤ)) hxS]
    rw [← WithZero.exp_zero, ← WithZero.exp_neg, WithZero.exp_lt_exp]
    have hlZ : 0 < (l : ℤ) := by exact_mod_cast hl
    omega
  have hpoint := spherical_shell_pointwise_aux L τ T B s f hf h1 hK
    l x hx hxInv u hu hsplit
  constructor
  · intro hdiv
    have hlmod : (l : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff l 3).2 hdiv
    obtain ⟨j, hj⟩ := hdiv
    rcases localChi_basic (D := D) (v := v) hv with ⟨_, _, _, hχ6, _⟩
    have hχpow : (localChi D v u) ^ (4 * (l : ℤ)) = 1 := by
      have hexp : 4 * (l : ℤ) = 6 * (2 * (j : ℤ)) := by omega
      rw [hexp, zpow_mul]
      simp [hχ6 u hu]
    have hidx : (2 : ZMod 3) * (l : ZMod 3) = 0 := by rw [hlmod]; simp
    rw [hpoint, hχpow, hidx]
    simp
  · intro hndiv
    refine ⟨((absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹)) : ℂ) ^
      ((1 : ℂ) / 2 + s)) * (localChi D v u) ^ (4 * (l : ℤ)), ?_⟩
    exact hpoint

private theorem valued_eq_one_of_ball_zero_not_ball_one (x : v.adicCompletion F)
    (hx0 : x ∈ ball v 0) (hx1 : x ∉ ball v 1) : Valued.v x = 1 := by
  have hxle : Valued.v x ≤ WithZero.exp (0 : ℤ) := by simpa [ball] using hx0
  have hxnot : ¬ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by simpa [ball] using hx1
  by_cases hz : Valued.v x = 0
  · exfalso
    apply hxnot
    rw [hz]
    exact WithZero.exp_pos.le
  · lift Valued.v x to ℤ using hz with n hn
    have hnle : n ≤ 0 := by
      apply WithZero.exp_le_exp.mp
      simpa [hn, ← WithZero.exp_zero] using hxle
    have hngt : -1 < n := by
      by_contra h
      have h' : n ≤ -1 := by omega
      apply hxnot
      exact WithZero.exp_le_exp.mpr h'
    have hn0 : n = 0 := by omega
    rw [hn0]
    simp

private theorem jacquetUnitShell_eq_ball_sdiff :
    jacquetUnitShell v = ball v 0 \ ball v 1 := by
  ext x
  rw [Set.mem_sdiff]
  constructor
  · intro hx
    have hx' : absFin v x = 1 := by simpa [jacquetUnitShell] using hx
    have hnorm : ‖x‖ = 1 := by simpa [absFin_eq_norm] using hx'
    have hval : Valued.v x = 1 := Valued.toNormedField.norm_eq_one_iff.mp hnorm
    constructor
    · change Valued.v x ≤ WithZero.exp (0 : ℤ)
      rw [hval]
      simp
    · intro hx1
      have hle : WithZero.exp (0 : ℤ) ≤ WithZero.exp (-1 : ℤ) := by
        change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx1
        rw [hval] at hx1
        exact hx1
      exact (not_le_of_gt (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0))) hle
  · rintro ⟨hx0, hx1⟩
    have hval := valued_eq_one_of_ball_zero_not_ball_one x hx0 hx1
    have hnorm : ‖x‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hval
    change absFin v x = 1
    rw [absFin_eq_norm, hnorm]

private theorem jacquetUnitShell_real_measure (μ : LocHaar v) :
    μ.μ.real (jacquetUnitShell v) = 1 - (qv v)⁻¹ := by
  let K := v.adicCompletion F
  let O := (v.adicCompletionIntegers F : Set K)
  have hball0 : ball v 0 = O := by
    ext x
    change Valued.v x ≤ WithZero.exp (0 : ℤ) ↔
      x ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp
  have hsubset : ball v 1 ⊆ ball v 0 :=
    ball_mono_int (show (0 : ℤ) ≤ 1 by norm_num)
  have hball1meas : MeasurableSet (ball v 1) := (ball_isCompact v 1).measurableSet
  have hfinite : μ.μ (ball v 0) ≠ ⊤ := by rw [hball0, μ.norm_O]; simp
  have hreal0 : μ.μ.real (ball v 0) = 1 := by
    rw [hball0]
    change (μ.μ (v.adicCompletionIntegers F : Set K)).toReal = 1
    rw [μ.norm_O]
    norm_num
  have hreal1 : μ.μ.real (ball v 1) = (qv v)⁻¹ := by
    rw [Measure.real, locHaar_ball_one μ]
    simp [qv, HeightOneSpectrum.absNorm_ne_zero]
  rw [jacquetUnitShell_eq_ball_sdiff, MeasureTheory.measureReal_sdiff hsubset hball1meas hfinite,
    hreal0, hreal1]

private theorem ball_zero_eq_integerRing :
    ball v 0 = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  change Valued.v x ≤ WithZero.exp (0 : ℤ) ↔ x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

private theorem ball_zero_real_measure (μ : LocHaar v) :
    μ.μ.real (ball v 0) = 1 := by
  rw [ball_zero_eq_integerRing]
  change (μ.μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal = 1
  rw [μ.norm_O]
  norm_num

private theorem jacquetShell_ne_zero (k : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ jacquetShell v k) : x ≠ 0 := by
  intro hzero
  subst x
  have hvx := jacquetShell_valuation v k hx
  have hv0 : Valued.v (0 : v.adicCompletion F) = 0 := by simp
  rw [hv0] at hvx
  exact WithZero.exp_ne_zero hvx.symm

private theorem hilb_one_left_spherical (b : (v.adicCompletion F)ˣ) : H.hilb v 1 b = 1 := by
  let z := H.hilb v 1 b
  have hz : z * 1 = z * z := by simpa [z] using H.mul_left v 1 1 b
  exact (mul_left_cancel hz).symm

private theorem hilb_inv_left_spherical (x y : (v.adicCompletion F)ˣ) :
    H.hilb v x⁻¹ y = (H.hilb v x y)⁻¹ := by
  have h := H.mul_left v x x⁻¹ y
  rw [mul_inv_cancel, hilb_one_left_spherical] at h
  have h' : H.hilb v x y * H.hilb v x⁻¹ y = 1 := by
    simpa [mul_comm] using h.symm
  exact eq_inv_of_mul_eq_one_right h'

private theorem muThree_sq_one_spherical (ζ : rootsOfUnity 6 F) (hζ : ζ ^ 2 = 1) :
    muThree D ζ = 1 := by
  apply rootsOfUnity.coe_injective
  change D.σ0 ((((ζ ^ 2 : rootsOfUnity 6 F) : Fˣ) : F)) = 1
  rw [hζ]
  simp

private theorem torusRep_sigma_inv_spherical (T : TorusRep D H v)
    (x : (v.adicCompletion F)ˣ) : (T.σa x⁻¹).comp (T.σa x) = LinearMap.id := by
  let z := H.hilb v x x
  have hz : z ^ 2 = 1 := by simpa [z, pow_two] using H.skew v x x
  have hzinv : z⁻¹ = z := by
    calc
      z⁻¹ = z⁻¹ * 1 := by simp
      _ = z⁻¹ * (z * z) := by rw [← pow_two, hz]
      _ = z := by group
  have hcoeff : muThree D (H.hilb v x⁻¹ x) = 1 := by
    rw [hilb_inv_left_spherical, hzinv]
    exact muThree_sq_one_spherical z hz
  have h := T.σa_mul x⁻¹ x
  rw [hcoeff] at h
  simpa [T.σa_one] using h

private theorem spherical_shell_integral_unit_fixed (L : FinLocalCover D H v)
    (τ : TameSplitting L) (T : TorusRep D H v) (μ : LocHaar v) (s : ℂ)
    (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (l : ℕ) (u : (v.adicCompletion F)ˣ)
    (huval : Valued.v (u : v.adicCompletion F) = 1) :
    T.σa u (∫ x in jacquetShell v (-(l : ℤ)),
      f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ) =
      ∫ x in jacquetShell v (-(l : ℤ)),
        f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ := by
  classical
  let K := v.adicCompletion F
  let S : Set K := jacquetShell v (-(l : ℤ))
  let G : K → T.V := fun x => f (L.w * L.n (Multiplicative.ofAdd x))
  let Fshell : K → T.V := S.indicator G
  let σ : T.V →L[ℂ] T.V := (T.σa u).toContinuousLinearMap
  let σinv : T.V →L[ℂ] T.V := (T.σa u⁻¹).toContinuousLinearMap
  have hGint : Integrable G μ.μ := by
    simpa [G] using section_intertwine_integrable L T μ s hs f hf 1
  have hSmeas : MeasurableSet S := (jacquetShell_compact v (-(l : ℤ))).measurableSet
  have hFint : Integrable Fshell μ.μ := hGint.indicator hSmeas
  have hSrad (x : K) (hx : x ∈ S) : absFin v x = (qv v) ^ (l : ℤ) := by
    simpa [S, qv] using jacquetShell_mem_radius v (-(l : ℤ)) hx
  have huabs : absFin v (u : K) = 1 := absFin_one_of_valuation_one u huval
  have hmulrad (x : K) : absFin v ((u : K) * x) =
      absFin v (u : K) * absFin v x := by
    rw [absFin_eq_norm, absFin_eq_norm, absFin_eq_norm]
    exact norm_mul _ _
  have hpreS : ∀ x : K, (u : K) * x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      have hux0 : (u : K) * x ≠ 0 := jacquetShell_ne_zero (-(l : ℤ)) hx
      have hx0 : x ≠ 0 := by
        intro hzero
        apply hux0
        rw [hzero]
        simp
      have hr := hSrad ((u : K) * x) hx
      have hrx : absFin v x = (qv v) ^ (l : ℤ) := by
        calc
          absFin v x = absFin v ((u : K) * x) := by rw [hmulrad, huabs]; simp
          _ = (qv v) ^ (l : ℤ) := hr
      exact jacquetShell_of_absFin v (-(l : ℤ)) hx0 (by simpa [qv] using hrx)
    · intro hx
      have hx0 : x ≠ 0 := jacquetShell_ne_zero (-(l : ℤ)) hx
      have hu0 : (u : K) ≠ 0 := Units.ne_zero u
      apply jacquetShell_of_absFin v (-(l : ℤ)) (mul_ne_zero hu0 hx0)
      have hr : absFin v ((u : K) * x) = (qv v) ^ (l : ℤ) := by
        calc
          absFin v ((u : K) * x) = absFin v (u : K) * absFin v x := hmulrad x
          _ = (qv v) ^ (l : ℤ) := by simpa [huabs] using hSrad x hx
      exact (by simpa [qv] using hr)
  have huInvVal : Valued.v ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [show Valued.v ((u⁻¹ : Kˣ) : K) = (Valued.v (u : K))⁻¹ by simp, huval]
    simp
  have huInvLoc : IsLocUnit v u⁻¹ := locUnit_of_valuation_one u⁻¹ huInvVal
  have hKinv : L.a u⁻¹ ∈ τ.Kmax := τ.a_mem u⁻¹ huInvLoc.1 huInvLoc.2
  have hwa : L.w * L.a u⁻¹ = L.a u * L.w := by
    have hwInv : L.w⁻¹ = L.w := (eq_inv_of_mul_eq_one_left L.w_sq).symm
    calc
      L.w * L.a u⁻¹ = (L.w * L.a u⁻¹ * L.w⁻¹) * L.w := by group
      _ = L.a (u⁻¹)⁻¹ * L.w := by rw [L.lift_wa]
      _ = L.a u * L.w := by simp
  have htor (x : K) :
      L.w * L.n (Multiplicative.ofAdd x) * L.a u⁻¹ =
        L.a u * L.w * L.n (Multiplicative.ofAdd ((u : K) * x)) := by
    calc
      L.w * L.n (Multiplicative.ofAdd x) * L.a u⁻¹ =
          L.w * (L.n (Multiplicative.ofAdd x) * L.a u⁻¹) := by simp [mul_assoc]
      _ = L.w * (L.a u⁻¹ * L.n (Multiplicative.ofAdd (x * (u : K)))) := by
        rw [L.lift_na]
        simp
      _ = (L.w * L.a u⁻¹) * L.n (Multiplicative.ofAdd (x * (u : K))) := by
        rw [← mul_assoc]
      _ = (L.w * L.a u⁻¹) * L.n (Multiplicative.ofAdd ((u : K) * x)) := by
        rw [show x * (u : K) = (u : K) * x by ring]
      _ = L.a u * L.w * L.n (Multiplicative.ofAdd ((u : K) * x)) := by rw [hwa]
  have hGcov (x : K) : G x = (T.σa u) (G ((u : K) * x)) := by
    have hright := hK (L.w * L.n (Multiplicative.ofAdd x)) (L.a u⁻¹) hKinv
    have hsec := hf.1 0 u (L.w * L.n (Multiplicative.ofAdd ((u : K) * x)))
    have hunitAbs := absFin_one_of_valuation_one u huval
    calc
      G x = f (L.w * L.n (Multiplicative.ofAdd x) * L.a u⁻¹) := by
        dsimp [G]
        exact hright.symm
      _ = f (L.a u * L.w * L.n (Multiplicative.ofAdd ((u : K) * x))) := by rw [htor]
      _ = (T.σa u) (G ((u : K) * x)) := by
        dsimp [G]
        simpa [mul_assoc, hunitAbs] using hsec
  have hFcov (x : K) : Fshell ((u : K) * x) = σinv (Fshell x) := by
    by_cases hx : x ∈ S
    · have hux : (u : K) * x ∈ S := (hpreS x).2 hx
      have hsig := torusRep_sigma_inv_spherical T u
      have hGinv : G ((u : K) * x) = σinv (G x) := by
        calc
          G ((u : K) * x) = σinv ((T.σa u) (G ((u : K) * x))) := by
            have hid := congrArg (fun A : T.V →ₗ[ℂ] T.V => A (G ((u : K) * x))) hsig
            simpa [σinv, LinearMap.comp_apply] using hid.symm
          _ = σinv (G x) := by exact congrArg σinv (hGcov x).symm
      simp [Fshell, hx, hux, σinv, hGinv]
    · have hux : (u : K) * x ∉ S := by
        intro hux
        exact hx ((hpreS x).1 hux)
      simp [Fshell, hx, hux]
  have hcompInt : Integrable (fun x : K => Fshell ((u : K) * x)) μ.μ := by
    have heq : (fun x : K => Fshell ((u : K) * x)) = fun x => σinv (Fshell x) :=
      funext hFcov
    rw [heq]
    exact σinv.integrable_comp hFint
  have hscale : (∫ x, Fshell ((u : K) * x) ∂μ.μ) = ∫ x, Fshell x ∂μ.μ := by
    simpa [huabs] using (LocHaar.integral_comp_mul μ u Fshell)
  have hinvI : σinv (∫ x, Fshell x ∂μ.μ) = ∫ x, Fshell x ∂μ.μ := by
    calc
      σinv (∫ x, Fshell x ∂μ.μ) = ∫ x, σinv (Fshell x) ∂μ.μ :=
        (ContinuousLinearMap.integral_comp_comm σinv hFint).symm
      _ = ∫ x, Fshell ((u : K) * x) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hFcov x).symm
      _ = ∫ x, Fshell x ∂μ.μ := hscale
  have hsigcomp : σ.comp σinv = ContinuousLinearMap.id ℂ T.V := by
    have h := torusRep_sigma_inv_spherical T u⁻¹
    ext z
    have hz := congrArg (fun A : T.V →ₗ[ℂ] T.V => A z) h
    simpa [σ, σinv, LinearMap.comp_apply] using hz
  have hfix : σ (∫ x, Fshell x ∂μ.μ) = ∫ x, Fshell x ∂μ.μ := by
    calc
      σ (∫ x, Fshell x ∂μ.μ) = σ (σinv (∫ x, Fshell x ∂μ.μ)) := by rw [hinvI]
      _ = ∫ x, Fshell x ∂μ.μ := by
        have h := congrArg (fun A : T.V →L[ℂ] T.V => A (∫ x, Fshell x ∂μ.μ)) hsigcomp
        simpa using h
  have hset : (∫ x, Fshell x ∂μ.μ) =
      ∫ x in S, G x ∂μ.μ := by
    rw [integral_indicator hSmeas]
  calc
    T.σa u (∫ x in S, G x ∂μ.μ) =
        T.σa u (∫ x, Fshell x ∂μ.μ) := by rw [← hset]
    _ = ∫ x, Fshell x ∂μ.μ := by simpa [σ] using hfix
    _ = ∫ x in S, G x ∂μ.μ := hset

private theorem valuation_one_of_isLocUnit (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) : Valued.v (u : v.adicCompletion F) = 1 := by
  have hle : Valued.v (u : v.adicCompletion F) ≤ 1 := by
    have h := hu.1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hinvle : (Valued.v (u : v.adicCompletion F))⁻¹ ≤ 1 := by
    have h := hu.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    have hval : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (Valued.v (u : v.adicCompletion F))⁻¹ := by simp
    rw [hval] at h
    exact h
  have hne : Valued.v (u : v.adicCompletion F) ≠ 0 := by simp
  have hpos : 0 < Valued.v (u : v.adicCompletion F) := pos_iff_ne_zero.mpr hne
  have hge : 1 ≤ Valued.v (u : v.adicCompletion F) := by
    rcases (inv_le_one_iff₀).mp hinvle with hbad | hge
    · exact (False.elim ((not_le_of_gt hpos) hbad))
    · exact hge
  exact le_antisymm hle hge

private theorem spherical_nondivisible_shell_integral_zero
    (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f)
    (h1 : f 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (l : ℕ) (hl : 0 < l) (hndiv : ¬ 3 ∣ l) :
    ∫ x in jacquetShell v (-(l : ℤ)),
      f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ = 0 := by
  classical
  let K := v.adicCompletion F
  let S : Set K := jacquetShell v (-(l : ℤ))
  let G : K → T.V := fun x => f (L.w * L.n (Multiplicative.ofAdd x))
  let Fshell : K → T.V := S.indicator G
  let I : T.V := ∫ x, Fshell x ∂μ.μ
  let b : Module.Basis (ZMod 3) ℂ T.V := Module.Basis.mk B.linIndep B.spans.ge
  let c0 : T.V →ₗ[ℂ] ℂ := b.coord 0
  let c0c : T.V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap c0
  have hSmeas : MeasurableSet S := (jacquetShell_compact v (-(l : ℤ))).measurableSet
  have hGint : Integrable G μ.μ := by
    simpa [G] using section_intertwine_integrable L T μ s hs f hf 1
  have hFint : Integrable Fshell μ.μ := hGint.indicator hSmeas
  have hset : I = ∫ x in S, G x ∂μ.μ := by
    dsimp [I, Fshell]
    exact integral_indicator hSmeas
  have hinvariant : ∀ u, IsLocUnit v u → T.σa u I = I := by
    intro u hu
    have huval := valuation_one_of_isLocUnit u hu
    have hfix := spherical_shell_integral_unit_fixed L τ T μ s hs f hf hK l u huval
    calc
      T.σa u I = T.σa u (∫ x in S, G x ∂μ.μ) := by rw [hset]
      _ = ∫ x in S, G x ∂μ.μ := by simpa [S, G] using hfix
      _ = I := hset.symm
  obtain ⟨c, hc⟩ := tame_unitFixed T B hv I hinvariant
  have hidx : (2 : ZMod 3) * (l : ZMod 3) ≠ 0 := by
    intro hzero
    rcases mul_eq_zero.mp hzero with h2 | hlzero
    · exact (by decide : (2 : ZMod 3) ≠ 0) h2
    · exact hndiv ((ZMod.natCast_eq_zero_iff l 3).mp hlzero)
  have hcoord0 : c0 (B.e 0) = 1 := by
    simpa [b, c0] using
      (Module.Basis.mk_coord_apply_eq (hli := B.linIndep) (hsp := B.spans.ge) (0 : ZMod 3))
  have hcoordk : c0 (B.e ((2 : ZMod 3) * (l : ZMod 3))) = 0 := by
    simpa [b, c0] using
      (Module.Basis.mk_coord_apply_ne (hli := B.linIndep) (hsp := B.spans.ge) hidx)
  have hpointcoord (x : K) (hx : x ∈ S) : c0 (G x) = 0 := by
    have hpt := (spherical_shell_pointwise L τ T B hv s f hf h1 hK l hl x
      (jacquetShell_ne_zero (-(l : ℤ)) hx) hx).2 hndiv
    obtain ⟨a, ha⟩ := hpt
    change c0 (f (L.w * L.n (Multiplicative.ofAdd x))) = 0
    rw [ha]
    simp [hcoordk]
  have hcoordF (x : K) : c0 (Fshell x) = 0 := by
    by_cases hx : x ∈ S
    · simp [Fshell, hx, hpointcoord x hx]
    · simp [Fshell, hx]
  have hcoordInt : (∫ x, c0c (Fshell x) ∂μ.μ) = c0c I :=
    ContinuousLinearMap.integral_comp_comm c0c hFint
  have hcoordI : c0 I = 0 := by
    calc
      c0 I = c0c I := rfl
      _ = ∫ x, c0c (Fshell x) ∂μ.μ := hcoordInt.symm
      _ = 0 := by
        calc
          (∫ x, c0c (Fshell x) ∂μ.μ) = ∫ x, (0 : ℂ) ∂μ.μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            simpa [c0c] using hcoordF x
          _ = 0 := integral_zero K ℂ
  have hc0 : c = 0 := by
    have hcoord : c0 I = c := by
      calc
        c0 I = c0 (c • B.e 0) := congrArg c0 hc
        _ = c * c0 (B.e 0) := by simp [c0]
        _ = c := by rw [hcoord0]; simp
    calc
      c = c0 I := hcoord.symm
      _ = 0 := hcoordI
  have hIzero : I = 0 := by rw [hc, hc0]; simp
  rw [← hset]
  exact hIzero

private theorem jacquetShell_real_measure_exact (μ : LocHaar v) (l : ℕ) :
    μ.μ.real (jacquetShell v (-(l : ℤ))) =
      (qv v) ^ (l : ℤ) * (1 - (qv v)⁻¹) := by
  rw [jacquetShell_real_measure μ, jacquetShell_radius, jacquetUnitShell_real_measure]
  simp [qv, mul_comm]

private theorem spherical_shell_cpow (l : ℕ) (s : ℂ) :
    (((qv v) ^ (-(2 * (l : ℤ))) : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s) =
      (qv v : ℂ) ^ (-((l : ℂ) * (1 + 2 * s))) := by
  let q : ℝ := qv v
  let e : ℤ := -(2 * (l : ℤ))
  have hq : 0 < q := by dsimp [q]; exact lt_trans zero_lt_one (qv_gt_one v)
  have he : (e : ℂ) * ((1 : ℂ) / 2 + s) = -((l : ℂ) * (1 + 2 * s)) := by
    dsimp [e]
    push_cast
    ring
  have him : (Complex.log (q : ℂ) * (e : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hq.le]
    simp
  have hlow : -Real.pi < (Complex.log (q : ℂ) * (e : ℂ)).im := by
    rw [him]
    linarith [Real.pi_pos]
  have hupp : (Complex.log (q : ℂ) * (e : ℂ)).im ≤ Real.pi := by
    rw [him]
    linarith [Real.pi_pos]
  have hbase : (((q ^ e : ℝ) : ℂ)) = (q : ℂ) ^ e := by
    exact Complex.ofReal_zpow q e
  rw [show qv v = q by rfl, show -(2 * (l : ℤ)) = e by rfl, hbase,
    ← Complex.cpow_intCast]
  rw [← Complex.cpow_mul _ hlow hupp, he]

private theorem spherical_divisible_shell_integral
    (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f)
    (h1 : f 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (l : ℕ) (hl : 0 < l) (hdiv : 3 ∣ l) :
    ∫ x in jacquetShell v (-(l : ℤ)),
      f (L.w * L.n (Multiplicative.ofAdd x)) ∂μ.μ =
      ((1 - (qv v : ℂ)⁻¹) * (qv v : ℂ) ^ (-2 * (l : ℂ) * s)) • B.e 0 := by
  classical
  let K := v.adicCompletion F
  let S : Set K := jacquetShell v (-(l : ℤ))
  let G : K → T.V := fun x => f (L.w * L.n (Multiplicative.ofAdd x))
  let C : ℂ := (qv v : ℂ) ^ (-((l : ℂ) * (1 + 2 * s)))
  have hSmeas : MeasurableSet S := (jacquetShell_compact v (-(l : ℤ))).measurableSet
  have hpoint (x : K) (hxS : x ∈ S) : G x = C • B.e 0 := by
    have hx : x ≠ 0 := jacquetShell_ne_zero (-(l : ℤ)) hxS
    obtain ⟨u, hu, huval, hsplit⟩ := spherical_shell_torus_decomp l hl x hx hxS
    have hπrad : absFin v ((unifLoc v ^ (2 * (l : ℤ)) : Kˣ) : K) =
        (qv v) ^ (-(2 * (l : ℤ))) := by
      simpa [qv] using jacquetShell_radius v (2 * (l : ℤ))
    have hradY : absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹) : K) =
        (qv v) ^ (-(2 * (l : ℤ))) := by
      calc
        absFin v (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹) : K) =
            absFin v ((unifLoc v ^ (2 * (l : ℤ)) * u : Kˣ) : K) := by
              have hsplitVal := congrArg (fun y : Kˣ => (y : K)) hsplit
              exact congrArg (absFin v) hsplitVal
        _ = absFin v ((unifLoc v ^ (2 * (l : ℤ)) : Kˣ) : K) * absFin v (u : K) := by
              simpa only [Units.val_mul] using
                (absFin_mul v (unifLoc v ^ (2 * (l : ℤ))) u)
        _ = (qv v) ^ (-(2 * (l : ℤ))) := by rw [hπrad, absFin_one_of_valuation_one u huval]; simp
    have hpt := (spherical_shell_pointwise L τ T B hv s f hf h1 hK
      l hl x hx hxS).1 hdiv
    rw [hradY, spherical_shell_cpow] at hpt
    simpa [G, C] using hpt
  have hvol : μ.μ.real S = (qv v) ^ (l : ℤ) * (1 - (qv v)⁻¹) := by
    simpa [S] using jacquetShell_real_measure_exact μ l
  have hcoeVol : ((((qv v) ^ (l : ℤ) * (1 - (qv v)⁻¹) : ℝ) : ℂ)) =
      (qv v : ℂ) ^ (l : ℂ) * (1 - (qv v : ℂ)⁻¹) := by
    rw [Complex.ofReal_mul, Complex.ofReal_zpow, ← Complex.cpow_intCast]
    simp [Complex.ofReal_inv, Complex.ofReal_sub]
  calc
    (∫ x in S, G x ∂μ.μ) = ∫ x in S, (fun _ : K => C • B.e 0) x ∂μ.μ := by
      apply setIntegral_congr_fun hSmeas
      intro x hx
      exact hpoint x hx
    _ = μ.μ.real S • (C • B.e 0) := setIntegral_const _
    _ = ((qv v : ℂ) ^ (l : ℂ) * (1 - (qv v : ℂ)⁻¹) * C) • B.e 0 := by
      rw [hvol, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [smul_smul]
      apply congrArg (fun z : ℂ => z • B.e 0)
      exact congrArg (fun z : ℂ => z * C) hcoeVol
    _ = ((1 - (qv v : ℂ)⁻¹) * (qv v : ℂ) ^ (-2 * (l : ℂ) * s)) • B.e 0 := by
      congr 1
      have hq : (qv v : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (qv_gt_one v)))
      calc
        (qv v : ℂ) ^ (l : ℂ) * (1 - (qv v : ℂ)⁻¹) * C =
            (1 - (qv v : ℂ)⁻¹) * ((qv v : ℂ) ^ (l : ℂ) * C) := by ring
        _ = (1 - (qv v : ℂ)⁻¹) *
            (qv v : ℂ) ^ ((l : ℂ) + -((l : ℂ) * (1 + 2 * s))) := by
              rw [← Complex.cpow_add _ _ hq]
        _ = (1 - (qv v : ℂ)⁻¹) * (qv v : ℂ) ^ (-2 * (l : ℂ) * s) := by
              congr 2
              ring

private def sphericalOuterShell (n : ℕ) : Set (v.adicCompletion F) :=
  jacquetShell v (-((n : ℤ) + 1))

private theorem sphericalOuterShell_pairwise :
    Pairwise fun i j : ℕ => Disjoint (sphericalOuterShell (F := F) (v := v) i)
      (sphericalOuterShell (F := F) (v := v) j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hvi : Valued.v x = WithZero.exp ((i : ℤ) + 1) := by
    simpa [sphericalOuterShell] using
      (jacquetShell_valuation v (-((i : ℤ) + 1)) hxi)
  have hvj : Valued.v x = WithZero.exp ((j : ℤ) + 1) := by
    simpa [sphericalOuterShell] using
      (jacquetShell_valuation v (-((j : ℤ) + 1)) hxj)
  have hidx : (i : ℤ) + 1 = (j : ℤ) + 1 :=
    WithZero.exp_inj.mp (hvi.symm.trans hvj)
  have hij' : i = j := by exact_mod_cast (by omega : (i : ℤ) = (j : ℤ))
  exact hij hij'

private theorem sphericalOuterShell_cover :
    (⋃ n : ℕ, sphericalOuterShell (F := F) (v := v) n) =
      (ball v 0)ᶜ := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    have hval := jacquetShell_valuation v (-((n : ℤ) + 1)) (by simpa [sphericalOuterShell] using hn)
    have hxball : x ∉ ball v 0 := by
      intro hxball
      have hle : Valued.v x ≤ WithZero.exp (0 : ℤ) := by simpa [ball] using hxball
      rw [hval] at hle
      have hnle : (n : ℤ) + 1 ≤ 0 := WithZero.exp_le_exp.mp hle
      omega
    exact hxball
  · intro hx
    have hnot : ¬ Valued.v x ≤ WithZero.exp (0 : ℤ) := by
      intro hxval
      apply hx
      change Valued.v x ≤ WithZero.exp (0 : ℤ)
      exact hxval
    have hx0 : x ≠ 0 := by
      intro hxzero
      apply hx
      subst x
      change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (0 : ℤ)
      simp
    obtain ⟨k, hk⟩ := jacquetShell_cover v hx0
    have hval := jacquetShell_valuation v k hk
    have hlt : WithZero.exp (0 : ℤ) < WithZero.exp (-k) := by
      have hlt' : WithZero.exp (0 : ℤ) < Valued.v x := lt_of_not_ge hnot
      rw [hval] at hlt'
      exact hlt'
    have hpos : 0 < -k := WithZero.exp_lt_exp.mp hlt
    let n : ℕ := Int.toNat (-k - 1)
    have hn0 : 0 ≤ -k - 1 := by omega
    have hncast : (n : ℤ) = -k - 1 := Int.toNat_of_nonneg hn0
    have hkEq : k = -((n : ℤ) + 1) := by omega
    apply Set.mem_iUnion.mpr ⟨n, ?_⟩
    simpa [sphericalOuterShell, hkEq] using hk

set_option maxHeartbeats 5000000 in
private theorem intertwine_spherical_at_one
    (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (s : ℂ) (hs : 0 < s.re) (f : L.L → T.V) (hf : IsSection L T s f)
    (h1 : f 1 = B.e 0) (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g) :
    intertwine L μ f 1 = cv v s • B.e 0 := by
  classical
  let K := v.adicCompletion F
  let G : K → T.V := fun x => f (L.w * L.n (Multiplicative.ofAdd x))
  let shell : ℕ → Set K := sphericalOuterShell (F := F) (v := v)
  let A : ℕ → T.V := fun n => ∫ x in shell n, G x ∂μ.μ
  let a : ℂ := 1 - (qv v : ℂ)⁻¹
  let r : ℂ := (qv v : ℂ) ^ (-6 * s)
  have hGint : Integrable G μ.μ := by
    simpa [G] using section_intertwine_integrable L T μ s hs f hf 1
  have hballMeas : MeasurableSet (ball v 0) := (ball_isCompact v 0).measurableSet
  have hGball (x : K) (hx : x ∈ ball v 0) : G x = B.e 0 := by
    have hxO : x ∈ v.adicCompletionIntegers F := by
      have hx' : x ∈ (ball v 0 : Set K) := hx
      rw [ball_zero_eq_integerRing] at hx'
      exact hx'
    have hmem : L.w * L.n (Multiplicative.ofAdd x) ∈ τ.Kmax :=
      τ.Kmax.mul_mem τ.w_mem (τ.n_mem x hxO)
    calc
      G x = f (1 * (L.w * L.n (Multiplicative.ofAdd x))) := by simp [G]
      _ = f 1 := hK 1 _ hmem
      _ = B.e 0 := h1
  have hballIntegral :
      ∫ x in ball v 0, G x ∂μ.μ = B.e 0 := by
    calc
      (∫ x in ball v 0, G x ∂μ.μ) =
          ∫ x in ball v 0, (fun _ : K => B.e 0) x ∂μ.μ := by
            apply setIntegral_congr_fun hballMeas
            intro x hx
            exact hGball x hx
      _ = μ.μ.real (ball v 0) • B.e 0 := setIntegral_const _
      _ = B.e 0 := by rw [ball_zero_real_measure]; simp
  have hshellMeas (n : ℕ) : MeasurableSet (shell n) := by
    exact (jacquetShell_compact v (-((n : ℤ) + 1))).measurableSet
  have hshellCover : (⋃ n : ℕ, shell n) = (ball v 0)ᶜ := by
    simpa [shell] using sphericalOuterShell_cover (F := F) (v := v)
  have hGunion : IntegrableOn G (⋃ n : ℕ, shell n) μ.μ := by
    exact hGint.integrableOn.mono_set (Set.subset_univ _)
  have hseries : HasSum A (∫ x in (ball v 0)ᶜ, G x ∂μ.μ) := by
    rw [← hshellCover]
    exact hasSum_integral_iUnion hshellMeas sphericalOuterShell_pairwise hGunion
  have hcompsum : (∑' n : ℕ, A n) = ∫ x in (ball v 0)ᶜ, G x ∂μ.μ :=
    hseries.tsum_eq
  have htotal : intertwine L μ f 1 = B.e 0 + ∑' n : ℕ, A n := by
    have hsplit := integral_add_compl hballMeas hGint
    calc
      intertwine L μ f 1 = ∫ x, G x ∂μ.μ := by simp [intertwine, G]
      _ = (∫ x in ball v 0, G x ∂μ.μ) +
            ∫ x in (ball v 0)ᶜ, G x ∂μ.μ := hsplit.symm
      _ = B.e 0 + ∑' n : ℕ, A n := by rw [hballIntegral, hcompsum]
  have hAdiv (n : ℕ) (hn : 3 ∣ n + 1) :
      A n = (a * (qv v : ℂ) ^ (-2 * ((n + 1 : ℕ) : ℂ) * s)) • B.e 0 := by
    have h := spherical_divisible_shell_integral L τ T B μ hv s hs f hf h1 hK
      (n + 1) (by omega) hn
    simpa [A, shell, G, a, sphericalOuterShell] using h
  have hAzero (n : ℕ) (hn : ¬ 3 ∣ n + 1) : A n = 0 := by
    simpa [A, shell, G, sphericalOuterShell] using
      spherical_nondivisible_shell_integral_zero L τ T B μ hv s hs f hf h1 hK
        (n + 1) (by omega) hn
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqC : (qv v : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hrec (n : ℕ) : A (n + 3) = r • A n := by
    by_cases hdiv : 3 ∣ n + 1
    · have hdivKeep := hdiv
      obtain ⟨j, hj⟩ := hdiv
      have hdiv' : 3 ∣ (n + 3) + 1 := ⟨j + 1, by omega⟩
      rw [hAdiv (n + 3) hdiv', hAdiv n hdivKeep]
      have hexp : -2 * (((n + 3) + 1 : ℕ) : ℂ) * s =
          (-6 * s) + (-2 * ((n + 1 : ℕ) : ℂ) * s) := by push_cast; ring
      have hpow : (qv v : ℂ) ^ (-2 * (((n + 3) + 1 : ℕ) : ℂ) * s) =
          r * (qv v : ℂ) ^ (-2 * ((n + 1 : ℕ) : ℂ) * s) := by
        dsimp [r]
        rw [hexp, Complex.cpow_add _ _ hqC]
      rw [smul_smul]
      congr 1
      rw [hpow]
      ring
    · have hdiv' : ¬ 3 ∣ (n + 3) + 1 := by
        intro hn'
        obtain ⟨j, hj⟩ := hn'
        have hjpos : 0 < j := by omega
        have hprev : n + 1 = 3 * (j - 1) := by omega
        exact hdiv ⟨j - 1, hprev⟩
      rw [hAzero (n + 3) hdiv', hAzero n hdiv]
      simp
  have hsumSplit := hseries.summable.sum_add_tsum_nat_add 3
  have htail : (∑' n : ℕ, A (n + 3)) = r • ∑' n : ℕ, A n := by
    calc
      (∑' n : ℕ, A (n + 3)) = ∑' n : ℕ, r • A n := by
        apply tsum_congr
        intro n
        exact hrec n
      _ = r • ∑' n : ℕ, A n := tsum_const_smul'' r
  have hA0 : A 0 = 0 := hAzero 0 (by norm_num)
  have hA1 : A 1 = 0 := hAzero 1 (by norm_num)
  have hA2 : A 2 = (a * r) • B.e 0 := by
    have h := hAdiv 2 (by norm_num)
    have hexp : -2 * ((2 + 1 : ℕ) : ℂ) * s = -6 * s := by push_cast; ring
    rw [hexp] at h
    simpa [a, r] using h
  have hfirst : (∑ n ∈ Finset.range 3, A n) = (a * r) • B.e 0 := by
    simp [Finset.sum_range_succ, hA0, hA1, hA2]
  have hsumEq : (∑' n : ℕ, A n) = (a * r) • B.e 0 +
      r • (∑' n : ℕ, A n) := by
    calc
      (∑' n : ℕ, A n) = (∑ n ∈ Finset.range 3, A n) +
          ∑' n : ℕ, A (n + 3) := hsumSplit.symm
      _ = (a * r) • B.e 0 + r • (∑' n : ℕ, A n) := by rw [hfirst, htail]
  have hrnorm : ‖r‖ < 1 := by
    dsimp [r]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hre : (-6 * s).re = -6 * s.re := by simp
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg (qv_gt_one v) (by linarith)
  have hden : 1 - r ≠ 0 := by
    intro h
    have hrone : r = 1 := (sub_eq_zero.mp h).symm
    rw [hrone] at hrnorm
    norm_num at hrnorm
  have hsub : (1 - r) • (∑' n : ℕ, A n) = (a * r) • B.e 0 := by
    calc
      (1 - r) • (∑' n : ℕ, A n) =
      (∑' n : ℕ, A n) - r • (∑' n : ℕ, A n) := by rw [sub_smul, one_smul]
      _ = (a * r) • B.e 0 := by
        have h := congrArg (fun z : T.V => z - r • (∑' n : ℕ, A n)) hsumEq
        simpa [add_sub_cancel_right] using h
  have hsumValue : (∑' n : ℕ, A n) = (a * r / (1 - r)) • B.e 0 := by
    calc
      (∑' n : ℕ, A n) = (1 - r)⁻¹ • ((1 - r) • (∑' n : ℕ, A n)) := by
        rw [smul_smul, inv_mul_cancel₀ hden, one_smul]
      _ = (1 - r)⁻¹ • ((a * r) • B.e 0) := by rw [hsub]
      _ = (a * r / (1 - r)) • B.e 0 := by
        rw [smul_smul, div_eq_mul_inv]
        congr 1
        ring
  have hpowNum : (qv v : ℂ) ^ (-1 - 6 * s) =
      (qv v : ℂ)⁻¹ * r := by
    dsimp [r]
    rw [show -1 - 6 * s = (-1) + (-6 * s) by ring, Complex.cpow_add _ _ hqC]
    simp [Complex.cpow_neg_one]
  have hcv : cv v s = 1 + a * r / (1 - r) := by
    unfold cv
    rw [hpowNum]
    dsimp [a]
    change (1 - (qv v : ℂ)⁻¹ * r) / (1 - r) =
      1 + ((1 - (qv v : ℂ)⁻¹) * r) / (1 - r)
    field_simp [hden]
    ring
  calc
    intertwine L μ f 1 = B.e 0 + ∑' n : ℕ, A n := htotal
    _ = (1 + a * r / (1 - r)) • B.e 0 := by
      rw [hsumValue]
      simp only [add_smul, one_smul]
    _ = cv v s • B.e 0 := by rw [hcv]

/-- **int:spherical**: `M f°_s = c_v(s) f°_{-s}` at a tame place, `Re s > 0`. -/
theorem intertwine_spherical (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) (hs : 0 < s.re)
    (f0 : L.L → T.V) (hf0 : IsSection L T s f0) (h1 : f0 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g)
    (f0' : L.L → T.V) (hf0' : IsSection L T.weyl (-s) f0') (h1' : f0' 1 = B.weyl.e 0)
    (hK' : ∀ g, ∀ k ∈ τ.Kmax, f0' (g * k) = f0' g) :
    intertwine L μ f0 = cv v s • f0' := by
  classical
  have hfM : IsSection L T.weyl (-s) (intertwine L μ f0) :=
    (intertwine_isSection L T μ s hs f0 hf0).2
  have hKM : ∀ g, ∀ k ∈ τ.Kmax,
      (intertwine L μ f0) (g * k) = (intertwine L μ f0) g := by
    intro g k hk
    have hsource : rtr k f0 = f0 := by
      funext x
      exact hK x k hk
    have hcomm : intertwine L μ f0 = rtr k (intertwine L μ f0) := by
      calc
        intertwine L μ f0 = intertwine L μ (rtr k f0) :=
          congrArg (intertwine L μ) hsource.symm
        _ = rtr k (intertwine L μ f0) := intertwine_rtr L μ f0 k
    simpa [rtr] using (congrFun hcomm g).symm
  obtain ⟨fstd, hfstd, hfstd1, hfstdK, huniq⟩ :=
    spherical_section L τ T.weyl B.weyl hv (-s)
  obtain ⟨c', hc'⟩ := huniq f0' hf0' hK'
  have hc'V : (f0' : L.L → T.weyl.V) = c' • fstd := hc'
  have hstdEvalW : (f0' 1 : T.weyl.V) = c' • B.weyl.e 0 := by
    have h := congrFun hc'V 1
    simpa [Pi.smul_apply, hfstd1] using h
  have hstdEqW : (f0' : L.L → T.weyl.V) = fstd := by
    have he0 : B.weyl.e 0 ≠ 0 := B.weyl.linIndep.ne_zero 0
    have h1'W : (f0' 1 : T.weyl.V) = B.weyl.e 0 := by
      simpa [TorusRep.weyl, TameTorusBasis.weyl] using h1'
    have hc'val : c' = 1 := by
      have hEval' : B.weyl.e 0 = c' • B.weyl.e 0 := h1'W.symm.trans hstdEvalW
      have hEval : (1 : ℂ) • B.weyl.e 0 = c' • B.weyl.e 0 := by
        simpa only [one_smul] using hEval'
      exact (smul_left_injective ℂ he0) hEval.symm
    rw [hc'val] at hc'V
    simpa only [one_smul] using hc'V
  obtain ⟨cM, hcM⟩ := huniq (intertwine L μ f0) hfM hKM
  have hcMpointW (g : L.L) : ((intertwine L μ f0) g : T.weyl.V) = cM • fstd g := by
    have h := congrFun hcM g
    change ((intertwine L μ f0) g : T.weyl.V) = cM • fstd g at h
    exact h
  have hcMpoint (g : L.L) : (intertwine L μ f0) g = cM • fstd g := by
    have h := hcMpointW g
    change (intertwine L μ f0) g = cM • fstd g
    exact h
  have hAtOne := intertwine_spherical_at_one L τ T B μ hv s hs f0 hf0 h1 hK
  have hstd1V : fstd 1 = B.e 0 := by
    simpa [TorusRep.weyl, TameTorusBasis.weyl] using hfstd1
  have hcMval : cM = cv v s := by
    have he0 : B.e 0 ≠ 0 := B.linIndep.ne_zero 0
    have hMone : (intertwine L μ f0) 1 = cM • B.e 0 := by
      have h := hcMpoint 1
      rw [hstd1V] at h
      exact h
    have hEval : cv v s • B.e 0 = cM • B.e 0 := hAtOne.symm.trans hMone
    exact (smul_left_injective ℂ he0) hEval.symm
  have hstdEq : f0' = fstd := by
    funext g
    have h := congrFun hstdEqW g
    simpa [TorusRep.weyl] using h
  have hfinal (g : L.L) : (intertwine L μ f0) g = cv v s • f0' g := by
    have h := hcMpoint g
    rw [hcMval] at h
    exact h.trans (congrArg (fun z : T.V => cv v s • z) (congrFun hstdEq.symm g))
  funext g
  exact hfinal g

/-- **int:analytic**: on big-cell sections, `s ↦ (M f_{φ,s})(g)` is holomorphic on `Re s > 0`. -/
private theorem abs_log_mul_rpow_small {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hsmall : r ≤ 1) : |Real.log r| * r ^ δ ≤ 1 / δ := by
  have hlog := Real.abs_log_mul_self_rpow_lt r δ hr hsmall hδ
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr δ)] at hlog
  exact hlog.le

private theorem abs_log_mul_rpow_large {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hlarge : 1 ≤ r) : |Real.log r| * r ^ (-δ) ≤ 1 / δ := by
  have hu : 0 < r⁻¹ := inv_pos.mpr hr
  have hu1 : r⁻¹ ≤ 1 := (inv_le_one₀ hr).2 hlarge
  have hlog := Real.abs_log_mul_self_rpow_lt r⁻¹ δ hu hu1 hδ
  have hEq : |Real.log (r⁻¹) * (r⁻¹) ^ δ| = |Real.log r| * r ^ (-δ) := by
    rw [Real.log_inv, Real.inv_rpow hr.le δ, abs_mul, abs_neg,
      abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hr δ)), Real.rpow_neg hr.le]
  rw [← hEq]
  exact hlog.le

private theorem section_intertwine_locallyConstant (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f)
    (g : L.L) :
    IsLocallyConstant (fun x => f (L.w * L.n (Multiplicative.ofAdd x) * g)) := by
  classical
  let f' : L.L → T.V := rtr g f
  have hf' : IsSection L T s f' := hf.rtr g
  obtain ⟨m, hm, hK⟩ := hf'.2.2
  let hfun : v.adicCompletion F → T.V := fun x => f' (L.w * L.n (Multiplicative.ofAdd x))
  apply (IsLocallyConstant.iff_exists_open hfun).mpr
  intro x
  let U := (fun x' : v.adicCompletion F => x' - x) ⁻¹' ball v (m : ℤ)
  have hBopen : IsOpen (ball v (m : ℤ)) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hU : IsOpen U := hBopen.preimage (continuous_id.sub continuous_const)
  have hxU : x ∈ U := by
    dsimp [U]
    change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
    simp
  refine ⟨U, hU, hxU, ?_⟩
  intro x' hx'
  have hz : x' - x ∈ ball v (m : ℤ) := by simpa [U] using hx'
  let z := x' - x
  have hxEq : x' = x + z := by dsimp [z]; abel
  have hgroup : L.w * L.n (Multiplicative.ofAdd x') =
      (L.w * L.n (Multiplicative.ofAdd x)) * L.n (Multiplicative.ofAdd z) := by
    rw [hxEq]
    simp [ofAdd_add, mul_assoc]
  have hsmall : L.n (Multiplicative.ofAdd z) ∈ L.Kc m := L.n_Kc m hm z hz
  change f' (L.w * L.n (Multiplicative.ofAdd x')) =
    f' (L.w * L.n (Multiplicative.ofAdd x))
  rw [hgroup]
  exact hK (L.w * L.n (Multiplicative.ofAdd x)) _ hsmall

private theorem bigCell_param_hasDerivAt (L : FinLocalCover D H v)
    (T : TorusRep D H v) (φ : v.adicCompletion F → T.V) (g : L.L) (s : ℂ) :
    HasDerivAt (fun z => bigCell L T z φ g)
      (deriv (fun z => bigCell L T z φ g) s) s := by
  classical
  by_cases h : ∃ x ζ y t,
      g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t)
  · let ζ := h.choose_spec.choose
    let y := h.choose_spec.choose_spec.choose
    let t := h.choose_spec.choose_spec.choose_spec.choose
    let W := T.σa y (φ t)
    let r : ℂ := (absFin v y : ℂ)
    have hr : 0 < absFin v y := absFin_pos y.ne_zero
    have hrne : r ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hgroup : g = L.n (Multiplicative.ofAdd h.choose) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) := by
      simpa [ζ, y, t] using h.choose_spec.choose_spec.choose_spec.choose_spec
    have hlin : HasDerivAt (fun z : ℂ => (1 : ℂ) / 2 + z) 1 s :=
      (hasDerivAt_id s).const_add _
    have hpow : HasDerivAt (fun z : ℂ => r ^ ((1 : ℂ) / 2 + z))
        (r ^ ((1 : ℂ) / 2 + s) * Complex.log r) s := by
      simpa [r, mul_one] using hlin.const_cpow (Or.inl hrne)
    have hscaled : HasDerivAt (fun z : ℂ => (r ^ ((1 : ℂ) / 2 + z)) • W)
        ((r ^ ((1 : ℂ) / 2 + s) * Complex.log r) • W) s := hpow.smul_const W
    have hexpr : HasDerivAt (fun z : ℂ => (ζ : ℂˣ) •
        ((r ^ ((1 : ℂ) / 2 + z)) • W))
        ((ζ : ℂˣ) • ((r ^ ((1 : ℂ) / 2 + s) * Complex.log r) • W)) s :=
      hscaled.const_smul (ζ : ℂˣ)
    have hformula (z : ℂ) : bigCell L T z φ g =
        (ζ : ℂˣ) • ((r ^ ((1 : ℂ) / 2 + z)) • W) := by
      rw [hgroup, bigCell_apply L T z φ h.choose ζ y t]
      rfl
    have hbig : HasDerivAt (fun z => bigCell L T z φ g)
        ((ζ : ℂˣ) • ((r ^ ((1 : ℂ) / 2 + s) * Complex.log r) • W)) s :=
      hexpr.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => hformula z)
    exact hbig.congr_deriv hbig.deriv.symm
  ·
    have hnot : ¬ ∃ (x : v.adicCompletion F) (a : ℂˣ) (ha : a ^ 3 = 1)
        (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F),
        g = L.n (Multiplicative.ofAdd x) *
          L.z ⟨a, (mem_rootsOfUnity 3 a).2 ha⟩ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t) := by
      intro h'
      rcases h' with ⟨x, a, ha, y, t, h'⟩
      apply h
      let ζ : rootsOfUnity 3 ℂ := ⟨a, (mem_rootsOfUnity 3 a).2 ha⟩
      exact ⟨x, ζ, y, t, h'⟩
    have hzero : (fun z => bigCell L T z φ g) = fun _ => (0 : T.V) := by
      funext z
      simp [bigCell, hnot]
    rw [hzero]
    simpa [deriv_const] using (hasDerivAt_const s (0 : T.V))

theorem intertwine_bigCell_analytic (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ)
    (g : L.L) :
    AnalyticOnNhd ℂ (fun s => intertwine L μ (bigCell L T s φ) g) {s | 0 < s.re} := by
  classical
  let K := v.adicCompletion F
  let evalFun : ℂ → K → T.V := fun s x =>
    bigCell L T s φ (L.w * L.n (Multiplicative.ofAdd x) * g)
  let evalDeriv : ℂ → K → T.V := fun s x => deriv (fun z => evalFun z x) s
  let evalFderiv : ℂ → K → ℂ →L[ℂ] T.V := fun s x =>
    ContinuousLinearMap.toSpanSingleton ℂ (evalDeriv s x)
  let integralFamily : ℂ → T.V := fun s => ∫ x, evalFun s x ∂μ.μ
  have hloc (s : ℂ) : IsLocallyConstant (evalFun s) := by
    change IsLocallyConstant
      (fun x => bigCell L T s φ (L.w * L.n (Multiplicative.ofAdd x) * g))
    exact section_intertwine_locallyConstant L T s (bigCell L T s φ)
      (bigCell_isSection L T s φ hφ hc) g
  have hcont (s : ℂ) : Continuous (evalFun s) := (hloc s).continuous
  have hpointDeriv (s : ℂ) (x : K) :
      HasDerivAt (fun z => evalFun z x) (evalDeriv s x) s := by
    simpa [evalFun, evalDeriv] using
      (bigCell_param_hasDerivAt L T φ (L.w * L.n (Multiplicative.ofAdd x) * g) s)
  have hint (s : ℂ) (hs : 0 < s.re) : Integrable (evalFun s) μ.μ := by
    have hsec : IsSection L T s (bigCell L T s φ) := bigCell_isSection L T s φ hφ hc
    simpa [evalFun] using
      section_intertwine_integrable L T μ s hs (bigCell L T s φ) hsec g
  have hdiffAt (s₀ : ℂ) (hs₀ : 0 < s₀.re) :
      DifferentiableAt ℂ (fun s => intertwine L μ (bigCell L T s φ) g) s₀ := by
    let δ : ℝ := s₀.re / 3
    let β : ℝ := s₀.re / 3
    let γ : ℝ := 5 * s₀.re / 3
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hβ : 0 < β := by dsimp [β]; linarith
    have hγ : 0 < γ := by dsimp [γ]; linarith
    let majorant : K → ℝ := fun x => δ⁻¹ *
      (‖evalFun (β : ℂ) x‖ + ‖evalFun (γ : ℂ) x‖)
    have hIntβ : Integrable (evalFun (β : ℂ)) μ.μ :=
      hint (β : ℂ) (by simpa using hβ)
    have hIntγ : Integrable (evalFun (γ : ℂ)) μ.μ :=
      hint (γ : ℂ) (by simpa using hγ)
    have hMajorant : Integrable majorant μ.μ := by
      have hsum : Integrable
          (fun x => ‖evalFun (β : ℂ) x‖ + ‖evalFun (γ : ℂ) x‖) μ.μ :=
        hIntβ.norm.add hIntγ.norm
      simpa [majorant] using hsum.const_mul δ⁻¹
    have hrange (z : ℂ) (hz : z ∈ Metric.ball s₀ δ) :
        β + δ ≤ z.re ∧ z.re ≤ γ - δ := by
      have hdist : ‖z - s₀‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hreal : |z.re - s₀.re| < δ := by
        have hle : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
          simpa [Complex.sub_re] using (Complex.abs_re_le_norm (z - s₀))
        exact lt_of_le_of_lt hle hdist
      have hlower := (abs_lt.mp hreal).1
      have hupper := (abs_lt.mp hreal).2
      have hlower' : s₀.re - δ < z.re := by linarith [hlower]
      have hupper' : z.re < s₀.re + δ := by linarith [hupper]
      constructor
      · change s₀.re / 3 + s₀.re / 3 ≤ z.re
        have hδval : δ = s₀.re / 3 := rfl
        rw [hδval] at hlower'
        linarith [hlower']
      · change z.re ≤ 5 * s₀.re / 3 - s₀.re / 3
        have hδval : δ = s₀.re / 3 := rfl
        rw [hδval] at hupper'
        linarith [hupper']
    have hboundPoint (z : ℂ) (hz : z ∈ Metric.ball s₀ δ) (x : K) :
        ‖evalFderiv z x‖ ≤ majorant x := by
      have hCLMnorm : ‖evalFderiv z x‖ = ‖evalDeriv z x‖ := by
        simp [evalFderiv]
      let gₓ : L.L := L.w * L.n (Multiplicative.ofAdd x) * g
      by_cases h : ∃ u ζ y t,
          gₓ = L.n (Multiplicative.ofAdd u) * L.z ζ * L.a y * L.w *
            L.n (Multiplicative.ofAdd t)
      · let u := h.choose
        let ζ := h.choose_spec.choose
        let y := h.choose_spec.choose_spec.choose
        let t := h.choose_spec.choose_spec.choose_spec.choose
        let W := T.σa y (φ t)
        let r : ℝ := absFin v y
        let rC : ℂ := (r : ℂ)
        let cζ : ℂ := ((ζ : ℂˣ) : ℂ)
        have hr : 0 < r := by dsimp [r]; exact absFin_pos y.ne_zero
        have hdecomp : gₓ = L.n (Multiplicative.ofAdd u) * L.z ζ * L.a y * L.w *
            L.n (Multiplicative.ofAdd t) := by
          simpa [gₓ, u, ζ, y, t] using h.choose_spec.choose_spec.choose_spec.choose_spec
        have hformula (p : ℂ) : evalFun p x =
            cζ • ((rC ^ ((1 : ℂ) / 2 + p)) • W) := by
          change bigCell L T p φ gₓ = _
          rw [hdecomp, bigCell_apply L T p φ u ζ y t]
        have hlin : HasDerivAt (fun p : ℂ => (1 : ℂ) / 2 + p) 1 z :=
          (hasDerivAt_id z).const_add _
        have hpow : HasDerivAt (fun p : ℂ => rC ^ ((1 : ℂ) / 2 + p))
            (rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) z := by
          have hrC : rC ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
          simpa [mul_one] using hlin.const_cpow (Or.inl hrC)
        have hscaled : HasDerivAt (fun p : ℂ =>
            (rC ^ ((1 : ℂ) / 2 + p)) • W)
            ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W) z := hpow.smul_const W
        have hexpr : HasDerivAt (fun p : ℂ => cζ •
            ((rC ^ ((1 : ℂ) / 2 + p)) • W))
            (cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W)) z :=
          hscaled.const_smul cζ
        have hderiv : HasDerivAt (fun p => evalFun p x)
            (cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W)) z :=
          hexpr.congr_of_eventuallyEq (Filter.Eventually.of_forall hformula)
        have hDval : evalDeriv z x =
            cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W) := hderiv.deriv
        have hnormD : ‖cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W)‖ =
            ‖cζ‖ * (|Real.log r| * r ^ ((1 : ℝ) / 2 + z.re) * ‖W‖) := by
          rw [norm_smul, norm_smul, norm_mul,
            Complex.norm_cpow_eq_rpow_re_of_pos hr]
          rw [← Complex.ofReal_log hr.le, Complex.norm_real, Real.norm_eq_abs]
          rw [Complex.add_re]
          have hhalf : ((1 : ℂ) / 2).re = (1 : ℝ) / 2 := by norm_num
          rw [hhalf]
          ring
        have hnormF (p : ℝ) : ‖evalFun (p : ℂ) x‖ =
            ‖cζ‖ * (r ^ ((1 : ℝ) / 2 + p) * ‖W‖) := by
          rw [hformula]
          rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
          rw [Complex.add_re]
          have hhalf : ((1 : ℂ) / 2).re = (1 : ℝ) / 2 := by norm_num
          rw [hhalf]
          rw [Complex.ofReal_re]
        have hrealRange := hrange z hz
        have hsplit (p : ℝ) : r ^ ((1 : ℝ) / 2 + z.re) =
            r ^ ((1 : ℝ) / 2 + p) * r ^ (z.re - p) := by
          calc
            r ^ ((1 : ℝ) / 2 + z.re) =
                r ^ (((1 : ℝ) / 2 + p) + (z.re - p)) := by congr 1 <;> ring
            _ = _ := Real.rpow_add hr _ _
        have hsmallBase : r ≤ 1 ∨ 1 ≤ r := le_total r 1
        rcases hsmallBase with hsmall | hlarge
        · have hgap : δ ≤ z.re - β := by linarith [hrealRange.1]
          have hpowLe : r ^ (z.re - β) ≤ r ^ δ :=
            Real.rpow_le_rpow_of_exponent_ge hr hsmall hgap
          have hlogLe : |Real.log r| * r ^ (z.re - β) ≤ δ⁻¹ := by
            calc
              |Real.log r| * r ^ (z.re - β) ≤ |Real.log r| * r ^ δ :=
                mul_le_mul_of_nonneg_left hpowLe (abs_nonneg _)
              _ ≤ δ⁻¹ := by
                simpa [one_div] using abs_log_mul_rpow_small hr hδ hsmall
          have hsmallInt : ‖evalFderiv z x‖ ≤ δ⁻¹ * ‖evalFun (β : ℂ) x‖ := by
            calc
              ‖evalFderiv z x‖ = ‖evalDeriv z x‖ := hCLMnorm
              _ = ‖cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W)‖ := by
                rw [hDval]
              _ = ‖cζ‖ * (|Real.log r| * r ^ ((1 : ℝ) / 2 + z.re) * ‖W‖) := hnormD
              _ = ‖cζ‖ * ((|Real.log r| * r ^ (z.re - β)) *
                    (r ^ ((1 : ℝ) / 2 + β) * ‖W‖)) := by rw [hsplit β]; ring
              _ ≤ ‖cζ‖ * (δ⁻¹ * (r ^ ((1 : ℝ) / 2 + β) * ‖W‖)) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_right hlogLe
                    (mul_nonneg (Real.rpow_nonneg hr.le _) (norm_nonneg _))
                · exact norm_nonneg _
              _ = δ⁻¹ * (‖cζ‖ * (r ^ ((1 : ℝ) / 2 + β) * ‖W‖)) := by ring
              _ = δ⁻¹ * ‖evalFun (β : ℂ) x‖ := by rw [hnormF]
          dsimp [majorant]
          calc
            ‖evalFderiv z x‖ ≤ δ⁻¹ * ‖evalFun (β : ℂ) x‖ := hsmallInt
            _ ≤ δ⁻¹ * (‖evalFun (β : ℂ) x‖ + ‖evalFun (γ : ℂ) x‖) := by
              apply mul_le_mul_of_nonneg_left
              · exact le_add_of_nonneg_right (norm_nonneg _)
              · exact inv_nonneg.mpr hδ.le
        · have hgap : z.re - γ ≤ -δ := by linarith [hrealRange.2]
          have hpowLe : r ^ (z.re - γ) ≤ r ^ (-δ) :=
            Real.rpow_le_rpow_of_exponent_le hlarge hgap
          have hlogLe : |Real.log r| * r ^ (z.re - γ) ≤ δ⁻¹ := by
            calc
              |Real.log r| * r ^ (z.re - γ) ≤ |Real.log r| * r ^ (-δ) :=
                mul_le_mul_of_nonneg_left hpowLe (abs_nonneg _)
              _ ≤ δ⁻¹ := by
                simpa [one_div] using abs_log_mul_rpow_large hr hδ hlarge
          have hlargeInt : ‖evalFderiv z x‖ ≤ δ⁻¹ * ‖evalFun (γ : ℂ) x‖ := by
            calc
              ‖evalFderiv z x‖ = ‖evalDeriv z x‖ := hCLMnorm
              _ = ‖cζ • ((rC ^ ((1 : ℂ) / 2 + z) * Complex.log rC) • W)‖ := by
                rw [hDval]
              _ = ‖cζ‖ * (|Real.log r| * r ^ ((1 : ℝ) / 2 + z.re) * ‖W‖) := hnormD
              _ = ‖cζ‖ * ((|Real.log r| * r ^ (z.re - γ)) *
                    (r ^ ((1 : ℝ) / 2 + γ) * ‖W‖)) := by rw [hsplit γ]; ring
              _ ≤ ‖cζ‖ * (δ⁻¹ * (r ^ ((1 : ℝ) / 2 + γ) * ‖W‖)) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_right hlogLe
                    (mul_nonneg (Real.rpow_nonneg hr.le _) (norm_nonneg _))
                · exact norm_nonneg _
              _ = δ⁻¹ * (‖cζ‖ * (r ^ ((1 : ℝ) / 2 + γ) * ‖W‖)) := by ring
              _ = δ⁻¹ * ‖evalFun (γ : ℂ) x‖ := by rw [hnormF]
          dsimp [majorant]
          calc
            ‖evalFderiv z x‖ ≤ δ⁻¹ * ‖evalFun (γ : ℂ) x‖ := hlargeInt
            _ ≤ δ⁻¹ * (‖evalFun (β : ℂ) x‖ + ‖evalFun (γ : ℂ) x‖) := by
              apply mul_le_mul_of_nonneg_left
              · exact le_add_of_nonneg_left (norm_nonneg _)
              · exact inv_nonneg.mpr hδ.le
      · have hnot : ¬ ∃ (u : K) (a : ℂˣ) (ha : a ^ 3 = 1)
            (y : Kˣ) (t : K),
            gₓ = L.n (Multiplicative.ofAdd u) *
              L.z ⟨a, (mem_rootsOfUnity 3 a).2 ha⟩ * L.a y * L.w *
              L.n (Multiplicative.ofAdd t) := by
          intro h'
          rcases h' with ⟨u, a, ha, y, t, h'⟩
          apply h
          let ζ : rootsOfUnity 3 ℂ := ⟨a, (mem_rootsOfUnity 3 a).2 ha⟩
          exact ⟨u, ζ, y, t, h'⟩
        have hzero (p : ℂ) : evalFun p x = 0 := by
          change bigCell L T p φ gₓ = 0
          simp only [bigCell, dif_neg h]
        have hDzero : evalDeriv z x = 0 := by
          have h := (hpointDeriv z x).deriv
          have hEq : (fun p => evalFun p x) = fun _ => (0 : T.V) := funext hzero
          rw [hEq, deriv_const] at h
          exact h.symm
        simp [evalFderiv, evalDeriv, hDzero, majorant, hzero]
    have hFmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (evalFun s) μ.μ := by
      filter_upwards [] with s
      exact (hcont s).aestronglyMeasurable
    have hInt₀ : Integrable (evalFun s₀) μ.μ := hint s₀ hs₀
    let step : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1)
    have hstep0 : Tendsto step atTop (𝓝 (0 : ℂ)) := by
      simpa [step] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)))
    have hstepNe : Tendsto step atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hstep0, Filter.Eventually.of_forall fun n => ?_⟩
      dsimp [step]
      apply div_ne_zero one_ne_zero
      intro hn
      have hreal := congrArg Complex.re hn
      have hreal' : (n : ℝ) + 1 = 0 := by simpa using hreal
      have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    let quot : ℕ → K → ℂ →L[ℂ] T.V := fun n x =>
      ContinuousLinearMap.toSpanSingleton ℂ
        ((step n)⁻¹ • (evalFun (s₀ + step n) x - evalFun s₀ x))
    have hquotCont (n : ℕ) : Continuous (quot n) := by
      have hV : Continuous fun x =>
          (step n)⁻¹ • (evalFun (s₀ + step n) x - evalFun s₀ x) :=
        continuous_const.smul ((hcont (s₀ + step n)).sub (hcont s₀))
      change Continuous (fun x =>
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := T.V))
          ((step n)⁻¹ • (evalFun (s₀ + step n) x - evalFun s₀ x)))
      exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := T.V)).continuous.comp hV
    have hquotMeas (n : ℕ) : AEStronglyMeasurable (quot n) μ.μ :=
      (hquotCont n).aestronglyMeasurable
    have hquotLim (x : K) : Tendsto (fun n => quot n x) atTop (𝓝 (evalFderiv s₀ x)) := by
      have hlimVec : Tendsto
          (fun n => (step n)⁻¹ • (evalFun (s₀ + step n) x - evalFun s₀ x))
          atTop (𝓝 (evalDeriv s₀ x)) := (hpointDeriv s₀ x).tendsto_slope_zero.comp hstepNe
      have hlimMap :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := T.V)).continuous.tendsto
          (evalDeriv s₀ x)
      change Tendsto (fun n =>
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := T.V))
          ((step n)⁻¹ • (evalFun (s₀ + step n) x - evalFun s₀ x))) atTop
        (𝓝 ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := T.V))
          (evalDeriv s₀ x)))
      exact hlimMap.comp hlimVec
    have hFderivMeas : AEStronglyMeasurable (evalFderiv s₀) μ.μ :=
      aestronglyMeasurable_of_tendsto_ae atTop hquotMeas
        (Filter.Eventually.of_forall hquotLim)
    have hbound : ∀ᵐ x ∂μ.μ, ∀ z ∈ Metric.ball s₀ δ,
        ‖evalFderiv z x‖ ≤ majorant x := by
      filter_upwards [] with x
      intro z hz
      exact hboundPoint z hz x
    have hdiff : ∀ᵐ x ∂μ.μ, ∀ z ∈ Metric.ball s₀ δ,
        HasFDerivAt (evalFun · x) (evalFderiv z x) z := by
      filter_upwards [] with x
      intro z hz
      simpa [evalFderiv] using (hpointDeriv z x).hasFDerivAt
    have hIderiv : HasFDerivAt integralFamily
        (∫ x, evalFderiv s₀ x ∂μ.μ) s₀ := by
      simpa [integralFamily] using
        (hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F := evalFun) (F' := evalFderiv) (x₀ := s₀)
          (s := Metric.ball s₀ δ) (μ := μ.μ) (bound := majorant)
          (Metric.ball_mem_nhds _ hδ) hFmeas hInt₀ hFderivMeas hbound
          hMajorant hdiff)
    simpa [integralFamily, evalFun, intertwine] using hIderiv.differentiableAt
  have hdiff : DifferentiableOn ℂ
      (fun s => intertwine L μ (bigCell L T s φ) g) {s | 0 < s.re} := by
    intro s hs
    exact (hdiffAt s hs).differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

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
  obtain ⟨hK, hctrl⟩ := ArtinPrimitiveRoots.Proofs.thsol_smooth.bessel_cubic_log_control
  exact ⟨ArtinPrimitiveRoots.Proofs.thsol_smooth.th_c_sheet_log_smooth m hm c hK,
    ArtinPrimitiveRoots.Proofs.thsol_smooth.th_c_sheet_log_bounds m hm c (hctrl 1).2⟩

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
