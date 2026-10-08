import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».CoshControl
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».PolynomialControl
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogDerivative
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogProfile
import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogBounds
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
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

/-- **jq:complex-derivative** (eq:theta-complex-derivative, 03:292–312). -/
theorem jacquetC_derivative (m : ℤ) (hm : m = 1 ∨ m = -1) (y : ℂˣ) :
    jacquetC (rtr (aC y) (derivVecC m (sphC (1 / 6)))) =
      -(4 * Real.pi * Complex.I) * besselConst * (Complex.normSq (y : ℂ) : ℂ) * omegaAng m y *
        (besselK (1 / 3) (4 * Real.pi * ‖(y : ℂ)‖) : ℂ) := by
  sorry

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
