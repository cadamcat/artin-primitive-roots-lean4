import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableHaarScale (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelHaarScale (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private lemma absFin_eq_norm (v : FinPlace F) (x : v.adicCompletion F) :
    absFin v x = ‖x‖ := by
  dsimp [absFin]
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

private def ball (v : FinPlace F) (m : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp (-m)}

private theorem valued_lt_one_iff_ball_one (v : FinPlace F) (x : v.adicCompletion F) :
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

private noncomputable def adicPositiveCompacts (v : FinPlace F) :
    TopologicalSpace.PositiveCompacts (v.adicCompletion F) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  have hproper : ProperSpace K := inferInstance
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall 0 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) :=
    Valued.isOpen_valuationSubring K
  exact { toCompacts := ⟨v.adicCompletionIntegers F, hcompact⟩
          interior_nonempty' := by
            rw [hopen.interior_eq]
            exact ⟨0, by simp⟩ }

private lemma adicPositiveCompacts_carrier (v : FinPlace F) :
    (adicPositiveCompacts v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F :=
  rfl

private theorem adicHaar_ball_one (v : FinPlace F) :
    (Measure.addHaarMeasure (adicPositiveCompacts v)) (ball v 1) =
      (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ := by
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
    exact (hmax a).trans (valued_lt_one_iff_ball_one v (a : K))
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
  let μO : Measure O := (Measure.addHaarMeasure (adicPositiveCompacts v)).comap f
  have : MeasureTheory.Measure.IsAddLeftInvariant μO :=
    MeasureTheory.Measure.IsAddLeftInvariant.comap (Measure.addHaarMeasure (adicPositiveCompacts v)) hf
  have hμO_univ : μO Set.univ = 1 := by
    change (Measure.addHaarMeasure (adicPositiveCompacts v)).comap f (Set.univ : Set O) = 1
    rw [hf.comap_apply]
    rw [Set.image_univ]
    have hrange : Set.range f = (adicPositiveCompacts v : Set K) := by
      rw [show Set.range f = (O : Set K) by simp [f]]
      exact (adicPositiveCompacts_carrier v).symm
    rw [hrange]
    exact Measure.addHaarMeasure_self (K₀ := adicPositiveCompacts v)
  have hball_subset : ball v 1 ⊆ Set.range f := by
    intro x hx
    have hxO : x ∈ O := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 : Valued.v x ≤ WithZero.exp (-1 : ℤ) := hx
      have h2 : WithZero.exp (-1 : ℤ) ≤ (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      exact h1.trans h2
    exact ⟨⟨x, hxO⟩, rfl⟩
  have himage : f '' (H : Set O) = ball v 1 := by
    rw [hHpre]
    exact Set.image_preimage_eq_of_subset hball_subset
  have hμOH : μO H = (Measure.addHaarMeasure (adicPositiveCompacts v)) (ball v 1) := by
    change (Measure.addHaarMeasure (adicPositiveCompacts v)).comap f (H : Set O) =
      (Measure.addHaarMeasure (adicPositiveCompacts v)) (ball v 1)
    rw [hf.comap_apply]
    rw [himage]
  have : Finite (O ⧸ H) := by
    change Finite (IsLocalRing.ResidueField O)
    exact Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
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
    (Measure.addHaarMeasure (adicPositiveCompacts v)) (ball v 1) = μO H := hμOH.symm
    _ = (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ := hμOH'

private theorem localHaarFactor_eq_nnnorm (v : FinPlace F) (y : (v.adicCompletion F)ˣ) :
    localHaarFactor y = ‖(y : v.adicCompletion F)‖₊ := by
  let K := v.adicCompletion F
  let U := adicPositiveCompacts v
  let ν := Measure.addHaarMeasure U
  have : MeasureTheory.Measure.Regular ν := inferInstance
  obtain ⟨π0, hunif⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  have hπ0_ne : π0 ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hunif
    exact WithZero.exp_ne_zero hunif.symm
  have hπK_ne : algebraMap F K π0 ≠ 0 := by
    intro h0
    have : π0 = 0 := (map_eq_zero (algebraMap F K)).mp h0
    exact hπ0_ne this
  let π : Kˣ := Units.mk0 (algebraMap F K π0) hπK_ne
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F K π0) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hunif
  have hπinvval : Valued.v ((π⁻¹ : Kˣ) : K) = WithZero.exp (1 : ℤ) := by
    calc
      _ = (Valued.v (π : K))⁻¹ := by simp
      _ = WithZero.exp (1 : ℤ) := by rw [hπval]; simp
  let q : NNReal := (Ideal.absNorm v.asIdeal : NNReal)
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
    simp only [Set.mem_preimage, ball, localMulAddEquiv,
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
      ν (ball v 1) = 1 := by
    have hsmul := addEquivAddHaarChar_smul_preimage ν (localMulAddEquiv (π⁻¹))
      (X := (v.adicCompletionIntegers F : Set K))
    have hself : ν (v.adicCompletionIntegers F : Set K) = 1 :=
      Measure.addHaarMeasure_self (K₀ := U)
    rw [hpreπ, hself] at hsmul
    exact hsmul
  have hfactorπinvENN : (addEquivAddHaarChar (localMulAddEquiv (π⁻¹)) : ENNReal) *
      (Ideal.absNorm v.asIdeal : ENNReal)⁻¹ = 1 := by
    rw [adicHaar_ball_one v] at hfactorπinvForm
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
    have hForm := addEquivAddHaarChar_smul_preimage ν (localMulAddEquiv u)
      (X := (v.adicCompletionIntegers F : Set K))
    have hself : ν (v.adicCompletionIntegers F : Set K) = 1 :=
      Measure.addHaarMeasure_self (K₀ := U)
    rw [hpre, hself] at hForm
    have h : (addEquivAddHaarChar (localMulAddEquiv u) : ENNReal) = 1 := by
      simpa [ENNReal.smul_def, smul_eq_mul] using hForm
    change addEquivAddHaarChar (localMulAddEquiv u) = 1
    exact_mod_cast h
  have hnny : Valued.v (y : K) ≠ 0 := by simp [y.ne_zero]
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

/-- The Jacobian of multiplication is the normalized local absolute value.
Guide: PROOFS.md:466–470. Uses: local_absolute_value; Haar uniqueness; residue cardinality. -/
theorem local_haar_scale (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (b : (v.adicCompletion F)ˣ) :
    Measure.map (fun x => (b : v.adicCompletion F) * x) μ =
      (ENNReal.ofReal (absFin v (b : v.adicCompletion F)))⁻¹ • μ := by
  let K := v.adicCompletion F
  let U := adicPositiveCompacts v
  let ν := Measure.addHaarMeasure U
  let e := localMulAddEquiv b
  have he_fun : (fun x => (b : K) * x) = ⇑e := by
    ext x
    rfl
  have : MeasureTheory.Measure.Regular ν := inferInstance
  have hcharMap : (‖(b : K)‖₊ : NNReal) • Measure.map e ν = ν := by
    have h := addEquivAddHaarChar_smul_map ν e
    rw [show addEquivAddHaarChar e = localHaarFactor b from rfl,
      localHaarFactor_eq_nnnorm v b] at h
    exact h
  have hbNorm : ‖(b : K)‖₊ ≠ 0 := by simp
  have hcancel : (‖(b : K)‖₊⁻¹ : NNReal) * ‖(b : K)‖₊ = 1 :=
    inv_mul_cancel₀ hbNorm
  have hmapν : Measure.map e ν = (‖(b : K)‖₊⁻¹ : NNReal) • ν := by
    calc
      Measure.map e ν = 1 • Measure.map e ν := by simp
      _ = (‖(b : K)‖₊⁻¹ * ‖(b : K)‖₊) • Measure.map e ν := by rw [hcancel]; simp
      _ = ‖(b : K)‖₊⁻¹ • (‖(b : K)‖₊ • Measure.map e ν) := by rw [smul_smul]
      _ = ‖(b : K)‖₊⁻¹ • ν := by rw [hcharMap]
  have : SigmaFinite μ := inferInstance
  have hμ_unique : μ = μ U • ν := Measure.addHaarMeasure_unique μ U
  rw [he_fun]
  nth_rw 1 [hμ_unique]
  erw [Measure.map_smul (μ U) e.continuous.aemeasurable]
  erw [hmapν]
  rw [smul_comm]
  rw [← hμ_unique]
  have hcoef : ((‖(b : K)‖₊⁻¹ : NNReal) : ENNReal) = (ENNReal.ofReal (absFin v (b : K)))⁻¹ := by
    rw [absFin_eq_norm, ← coe_nnnorm (b : K), ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv hbNorm]
  exact congrFun (congrArg HSMul.hSMul hcoef) μ

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
