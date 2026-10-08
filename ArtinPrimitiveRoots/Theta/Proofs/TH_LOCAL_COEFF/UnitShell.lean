import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Theta.Proofs.TH_LOCAL_COEFF.TameKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_LOCAL_COEFF.UnitInversion

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_lcoeff_sol

open NumberField IsDedekindDomain MeasureTheory Filter
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta
open scoped Classical Valued Topology

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {v : FinPlace F}

local instance localResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance localResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

/- The scalar residue-fiber argument follows the existing spherical-shell proof in
`LocalInt`, with an independent integer character exponent. -/

private theorem valued_lt_one_iff_ball_one (x : v.adicCompletion F) :
    Valued.v x < 1 ↔ x ∈ ball v 1 := by
  change Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1)
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · lift Valued.v x to ℤ using hx with n hn
    simp only [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

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

private noncomputable def localChiPowerField (D : FieldData F) (j : ℤ)
    (x : v.adicCompletion F) : ℂ :=
  if hx : x ≠ 0 then localChi D v (Units.mk0 x hx) ^ j else 0

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
    (j : ℤ) (x : v.adicCompletion F) : ℂ :=
  if hx : x ∈ localUnitShell v then
    localChiPowerField D (j) x *
      A.ψ v (((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x))
  else 0

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

private theorem localPsi_mul_inv_uniformizer_eq_of_diff_ball (A : AddCharData F)
    (x y : v.adicCompletion F) (hxy : x - y ∈ ball v 1) :
    A.ψ v (((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)) =
      A.ψ v (((((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y)) := by
  let πi : v.adicCompletion F := (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
  have hphase : A.ψ v (πi * (x - y)) = 1 := A.integral v _ (by
    simpa [πi] using localPiInv_mul_ball_mem_integer (v := v) (x - y) hxy)
  have harg : πi * x = πi * y + πi * (x - y) := by ring
  rw [harg, (A.ψ v).map_add_eq_mul, hphase]
  simp [πi]

private theorem localTerminalScalar_const_on_fiber (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) (r : 𝓞 F ⧸ v.asIdeal) (hr : r ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ completionResidueFiber (v := v) r) :
    localTerminalScalar D A j x =
      localTerminalScalar D A j (completionResidueCenter (v := v) r : v.adicCompletion F) := by
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
  have hψ : A.ψ v ((πi * x)) = A.ψ v
      ((πi * (completionResidueCenter (v := v) r : v.adicCompletion F))) := by
    simpa [πi] using localPsi_mul_inv_uniformizer_eq_of_diff_ball (v := v) A x
      (completionResidueCenter (v := v) r : v.adicCompletion F) hxdiff
  simp only [localTerminalScalar, dif_pos hxunit, dif_pos hcunit]
  change localChiPowerField D j x *
      A.ψ v ((πi * x)) =
    localChiPowerField D j (completionResidueCenter (v := v) r : v.adicCompletion F) *
      A.ψ v ((πi * (completionResidueCenter (v := v) r : v.adicCompletion F)))
  rw [hfx, hfc, hχ, hψ]

private theorem localTerminalScalar_integral_fiber_sum (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    ∫ x in localUnitShell v, localTerminalScalar D A j x ∂μ.μ =
      ∑ r : 𝓞 F ⧸ v.asIdeal,
        ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
          localTerminalScalar D A j
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
      IntegrableOn (localTerminalScalar D A j) (S r) μ.μ := by
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
    · have hconst : Set.EqOn (localTerminalScalar D A j)
          (fun _ => localTerminalScalar D A j
            (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) := by
        intro x hx
        exact localTerminalScalar_const_on_fiber D A hv j r hr x hx
      have hconstInt : IntegrableOn (fun _ : v.adicCompletion F =>
          localTerminalScalar D A j (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) μ.μ := integrableOn_const (hfinite r)
      have hfiber : IntegrableOn (localTerminalScalar D A j)
          (completionResidueFiber (v := v) r) μ.μ :=
        (integrableOn_congr_fun hconst (completionResidueFiber_measurable (v := v) r)).2 hconstInt
      exact hfiber.mono_set (fun _ hx => hx.1)
  have hterm (r : R) :
      ∫ x in S r, localTerminalScalar D A j x ∂μ.μ =
        ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
          localTerminalScalar D A j
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
      have hconst : Set.EqOn (localTerminalScalar D A j)
          (fun _ => localTerminalScalar D A j
            (completionResidueCenter (v := v) r : v.adicCompletion F))
          (completionResidueFiber (v := v) r) := by
        intro x hx
        exact localTerminalScalar_const_on_fiber D A hv j r hr x hx
      calc
        _ = ∫ x in completionResidueFiber (v := v) r,
              (fun _ => localTerminalScalar D A j
                (completionResidueCenter (v := v) r : v.adicCompletion F)) x ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem
            (completionResidueFiber_measurable (v := v) r)] with x hx
          exact hconst hx
        _ = ((μ.μ.real (completionResidueFiber (v := v) r) : ℝ) : ℂ) *
              localTerminalScalar D A j
                (completionResidueCenter (v := v) r : v.adicCompletion F) := by
          simp [MeasureTheory.measureReal_def]
  calc
    _ = ∫ x in ⋃ r : R, S r, localTerminalScalar D A j x ∂μ.μ := by rw [hS_union]
    _ = ∑ r : R, ∫ x in S r, localTerminalScalar D A j x ∂μ.μ :=
      integral_iUnion_fintype hS_meas hS_disj hS_integrable
    _ = _ := by
      simp_rw [hterm]
      apply Finset.sum_congr rfl
      intro r hr
      rfl

private theorem localTerminalScalar_center_eq (D : FieldData F) (A : AddCharData F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) (r : 𝓞 F ⧸ v.asIdeal) :
    localTerminalScalar D A j (completionResidueCenter (v := v) r : v.adicCompletion F) =
      chiPow D v (algebraMap (𝓞 F) F r.out) (j) *
        A.ψ v (algebraMap F (v.adicCompletion F) (((r.out : F) / unif v))) := by
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
      simp [chiPow, hresne, a]
    let πi : v.adicCompletion F :=
      (((unifLoc v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
    have hπi : πi = algebraMap F (v.adicCompletion F) ((unif v)⁻¹ : F) := by
      simp [πi, unifLoc, toLoc]
    have hcenter : (completionResidueCenter (v := v) r : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (a : F) := by
      simp [completionResidueCenter, a]
    have harg : (πi * (completionResidueCenter (v := v) r : v.adicCompletion F)) =
        algebraMap F (v.adicCompletion F) (((a : F) / unif v)) := by
      rw [hπi, hcenter, ← map_mul]
      congr 1
      field_simp [unif_ne_zero v]
    have hphase : A.ψ v ((πi * (completionResidueCenter (v := v) r : v.adicCompletion F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) / unif v))) := by
      rw [harg]
    simp only [localTerminalScalar, dif_pos hcu]
    rw [hpow, hphase]

private theorem localUnitShell_chiPower_integral (D : FieldData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) :
    (∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ) =
      if (6 : ℤ) ∣ j then 1 - (qv v : ℂ)⁻¹ else 0 := by
  classical
  by_cases hdiv : (6 : ℤ) ∣ j
  · obtain ⟨a, ha⟩ := hdiv
    have hpoint (x : v.adicCompletion F) (hx : x ∈ localUnitShell v) :
        localChiPowerField D j x = 1 := by
      let xU : localUnitShell v := ⟨x, hx⟩
      have h6 := (localChi_basic (D := D) (v := v) hv).2.2.2.1
        (localUnitShell.unit xU) (localUnitShell_isLocUnit xU)
      have h6z : localChi D v (localUnitShell.unit xU) ^ (6 : ℤ) = 1 := by
        simpa using h6
      change (if hx' : x ≠ 0 then localChi D v (Units.mk0 x hx') ^ j else 0) = 1
      rw [dif_pos (localUnitShell_ne_zero xU)]
      change localChi D v (localUnitShell.unit xU) ^ j = 1
      rw [ha, zpow_mul, h6z, one_zpow]
    rw [if_pos (show (6 : ℤ) ∣ j from ⟨a, ha⟩)]
    calc
      _ = ∫ x in localUnitShell v, (1 : ℂ) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
        exact hpoint x hx
      _ = ((μ.μ.real (localUnitShell v) : ℝ) : ℂ) := by
        simp [MeasureTheory.measureReal_def]
      _ = 1 - (qv v : ℂ)⁻¹ := by rw [localUnitShell_realMeasure]; simp
  · obtain ⟨u, hu, huval, hprim⟩ := exists_localChi_primitive_unit (D := D) hv
    have hχ : localChi D v u ^ j ≠ 1 := by
      intro hχone
      have hχ6 := (localChi_basic (D := D) (v := v) hv).2.2.2.1 u hu
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
      apply hdiv
      simpa [← hprimU.eq_orderOf] using horder
    rw [if_neg hdiv]
    exact localUnitShell_charPower_integral_eq_zero D μ hv j u huval hχ

private theorem localTerminalScalar_integral_gauss (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (j : ℤ) :
    (∫ x in localUnitShell v, localTerminalScalar D A j x ∂μ.μ) =
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v j := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype R := Fintype.ofFinite R
  let term : R → ℂ := fun r =>
    chiPow D v (algebraMap (𝓞 F) F r.out) j *
      A.ψ v (algebraMap F (v.adicCompletion F) ((r.out : F) / unif v))
  have hI : (∫ x in localUnitShell v, localTerminalScalar D A j x ∂μ.μ) =
      (qv v : ℂ)⁻¹ * ∑ r : R, term r := by
    rw [localTerminalScalar_integral_fiber_sum D A μ hv j]
    simp_rw [completionResidueFiber_realMeasure μ,
      localTerminalScalar_center_eq D A hv j]
    simp only [Complex.ofReal_inv, ← Finset.mul_sum]
    rfl
  have hqpos : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hqnorm :
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (qv v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    change (((qv v) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_cpow hqpos.le]
    congr 1
    simp
  have hgauss : gaussLoc D A v j =
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * ∑ r : R, term r := by
    unfold gaussLoc
    rw [finsum_eq_sum_of_fintype, hqnorm]
  have hhalf : (qv v : ℂ) ^ (-(1 / 2 : ℂ)) *
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) = (qv v : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hqne]
    convert Complex.cpow_neg_one (qv v : ℂ) using 1 <;> congr 1 <;> ring
  rw [hI, hgauss, ← mul_assoc, hhalf]

private theorem uniformizer_zpow_valuation (l : ℤ) :
    Valued.v ((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-l) := by
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem localUnitShell_add_ball (δ : v.adicCompletion F) (hδ : δ ∈ ball v 1)
    (x : v.adicCompletion F) : x + δ ∈ localUnitShell v ↔ x ∈ localUnitShell v := by
  have hδval : Valued.v δ < 1 := (valued_lt_one_iff_ball_one δ).mpr hδ
  constructor
  · intro hxplus
    change Valued.v (x + δ) = 1 at hxplus
    have hsmall : Valued.v (x - (x + δ)) < Valued.v (x + δ) := by
      simpa [hxplus] using hδval
    have hval := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_eq_of_sub_lt hsmall
    rw [hxplus] at hval
    exact hval
  · intro hx
    change Valued.v x = 1 at hx
    have hlt : Valued.v δ < Valued.v x := by rw [hx]; exact hδval
    have hval : Valued.v (δ + x) = Valued.v x :=
      (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).map_add_eq_of_lt_right hlt
    simpa [add_comm, localUnitShell] using hval.trans hx

private theorem unit_shell_tail_zero (D : FieldData F) (A : AddCharData F)
    (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (j l : ℤ) (hl : l < -1) :
    (∫ x in localUnitShell v, localChiPowerField D j x *
      A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ∂μ.μ) = 0 := by
  obtain ⟨t, ht, hψt⟩ := psi_conductor_unramified A v hd
  let scale : (v.adicCompletion F)ˣ := unifLoc v ^ l
  let δ : v.adicCompletion F := ((scale⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t
  have hinvval : Valued.v ((scale⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp l := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    change (Valued.v ((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ = _
    rw [uniformizer_zpow_valuation, ← WithZero.exp_neg, neg_neg]
  have hδball : δ ∈ ball v 1 := by
    change Valued.v t ≤ WithZero.exp 1 at ht
    change Valued.v δ ≤ WithZero.exp (-1 : ℤ)
    dsimp [δ]
    rw [map_mul, hinvval]
    calc
      WithZero.exp l * Valued.v t ≤ WithZero.exp l * WithZero.exp 1 := by gcongr
      _ = WithZero.exp (l + 1) := by rw [← WithZero.exp_add]
      _ ≤ WithZero.exp (-1 : ℤ) := (WithZero.exp_le_exp).mpr (by omega)
  have hcdelta : (scale : v.adicCompletion F) * δ = t := by
    dsimp [δ]
    simp [mul_assoc]
  let f : v.adicCompletion F → ℂ := (localUnitShell v).indicator (fun x =>
    localChiPowerField D j x * A.ψ v ((scale : v.adicCompletion F) * x))
  have hpoint (x : v.adicCompletion F) : f (x + δ) = A.ψ v t * f x := by
    have hphase : A.ψ v ((scale : v.adicCompletion F) * (x + δ)) =
        A.ψ v ((scale : v.adicCompletion F) * x) * A.ψ v t := by
      rw [mul_add, hcdelta, (A.ψ v).map_add_eq_mul]
    by_cases hx : x ∈ localUnitShell v
    · have hxplus : x + δ ∈ localUnitShell v := (localUnitShell_add_ball δ hδball x).2 hx
      let xU : localUnitShell v := ⟨x, hx⟩
      let yU : localUnitShell v := ⟨x + δ, hxplus⟩
      have hχ := localUnitShell_charPower_congr D hv j xU yU (by
        simpa [xU, yU] using hδball)
      have hχ' : localChiPowerField D j (x + δ) = localChiPowerField D j x := by
        have hxne : x ≠ 0 := localUnitShell_ne_zero xU
        have hyne : x + δ ≠ 0 := localUnitShell_ne_zero yU
        simpa [localChiPowerField, localUnitShell.unit, hxne, hyne, xU, yU] using hχ
      simp only [f, Set.indicator_of_mem hxplus, Set.indicator_of_mem hx]
      rw [hχ', hphase]
      ring
    · have hxplus : x + δ ∉ localUnitShell v := by
        intro hxplus
        exact hx ((localUnitShell_add_ball δ hδball x).1 hxplus)
      simp [f, hx, hxplus]
  have hshift : (∫ x, f (x + δ) ∂μ.μ) = ∫ x, f x ∂μ.μ := by
    simpa [add_comm] using integral_add_left_eq_self (μ := μ.μ) f δ
  have hlinear : (∫ x, f (x + δ) ∂μ.μ) = A.ψ v t * ∫ x, f x ∂μ.μ := by
    simp_rw [hpoint]
    rw [integral_const_mul]
  have hmul : (A.ψ v t - 1) * (∫ x, f x ∂μ.μ) = 0 := by
    rw [sub_mul, one_mul, ← hlinear, hshift, sub_self]
  have hzero : (∫ x, f x ∂μ.μ) = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact (hψt (sub_eq_zero.mp h)).elim
    · exact h
  rw [MeasureTheory.integral_indicator (localUnitShell_compact v).measurableSet] at hzero
  exact hzero

/-- Scalar tame kernel on a valuation-one unit shell. -/
theorem tame_unit_shell_integral (A : AddCharData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (l : ℤ) (k : ZMod 3) :
    (∫ x in {x : v.adicCompletion F | Valued.v x = 1},
      (if hx : x ≠ 0 then
        (localChi D v (Units.mk0 x hx)) ^ (2 * (l + (k.val : ℤ))) *
          A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)
      else 0) ∂μ.μ) =
      if 0 ≤ l then
        if ((l + (k.val : ℤ) : ℤ) : ZMod 3) = 0 then 1 - (qv v : ℂ)⁻¹ else 0
      else if l = -1 then
        (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (2 * ((k.val : ℤ) - 1))
      else 0 := by
  classical
  let j : ℤ := 2 * (l + (k.val : ℤ))
  have hform :
      (∫ x in {x : v.adicCompletion F | Valued.v x = 1},
        (if hx : x ≠ 0 then localChi D v (Units.mk0 x hx) ^ j *
          A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)
        else 0) ∂μ.μ) =
      ∫ x in localUnitShell v, localChiPowerField D j x *
        A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ∂μ.μ := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x = 0 <;> simp [localChiPowerField, hx]
  rw [hform]
  by_cases hl : 0 ≤ l
  · rw [if_pos hl]
    have hphase (x : v.adicCompletion F) (hx : x ∈ localUnitShell v) :
        A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) = 1 := by
      apply A.integral
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
        uniformizer_zpow_valuation, show Valued.v x = 1 from hx, mul_one]
      rw [← WithZero.exp_zero]
      exact (WithZero.exp_le_exp).mpr (by omega)
    calc
      _ = ∫ x in localUnitShell v, localChiPowerField D j x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
        rw [hphase x hx, mul_one]
      _ = if (6 : ℤ) ∣ j then 1 - (qv v : ℂ)⁻¹ else 0 :=
        localUnitShell_chiPower_integral D μ hv j
      _ = _ := by
        have hcond : ((6 : ℤ) ∣ j) ↔ ((l + (k.val : ℤ) : ℤ) : ZMod 3) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          dsimp [j]
          change (2 * 3 : ℤ) ∣ 2 * (l + (k.val : ℤ)) ↔ _
          exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)
        simp only [hcond]
  · rw [if_neg hl]
    by_cases heq : l = -1
    · subst l
      rw [if_pos rfl]
      have hterminal :
          (∫ x in localUnitShell v, localChiPowerField D j x *
            A.ψ v (((unifLoc v ^ (-1 : ℤ) : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) * x) ∂μ.μ) =
          ∫ x in localUnitShell v, localTerminalScalar D A j x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
        simp [localTerminalScalar, hx]
      rw [hterminal, localTerminalScalar_integral_gauss D A μ hv j]
      congr 2
    · rw [if_neg heq]
      exact unit_shell_tail_zero D A μ hv hd j l (by omega)

variable {H : HilbertData F}

/-- The shell indexed by the valuation of the inverse Jacquet parameter. -/
def inverseValShell (v : FinPlace F) (l : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x = WithZero.exp l}

/-- The truncated inverse-parameter kernel after the inner Fourier integral. -/
def inverseKernel (T : TorusRep D H v) (B : TameTorusBasis T)
    (A : AddCharData F) (s : ℂ) (N : ℕ) (k : ZMod 3)
    (x : v.adicCompletion F) : T.V :=
  if hx : x ≠ 0 then
    if (((Units.mk0 x hx)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        ball v (-(N : ℤ)) then
      ((absFin v (Units.mk0 x hx) : ℂ) ^ (-1 - 2 * s)) •
        T.σa (-((Units.mk0 x hx)⁻¹ * (Units.mk0 x hx)⁻¹))
          (A.ψ v (((Units.mk0 x hx)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • B.e k)
    else 0
  else 0

private theorem inverseValShell_eq_image (l : ℤ) :
    inverseValShell v l = (fun x : v.adicCompletion F =>
      ((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ''
        localUnitShell v := by
  ext x
  constructor
  · intro hx
    have hxval : Valued.v x = WithZero.exp l := hx
    refine ⟨((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x, ?_, ?_⟩
    · change Valued.v _ = 1
      rw [map_mul, uniformizer_zpow_valuation, hxval, ← WithZero.exp_add]
      simp
    · dsimp only
      rw [← mul_assoc, ← Units.val_mul]
      rw [show unifLoc v ^ (-l) * unifLoc v ^ l = 1 by group]
      simp
  · rintro ⟨y, hy, rfl⟩
    change Valued.v _ = WithZero.exp l
    rw [map_mul, uniformizer_zpow_valuation, show Valued.v y = 1 from hy]
    simp

private theorem inverseValShell_compact (l : ℤ) : IsCompact (inverseValShell v l) := by
  rw [inverseValShell_eq_image]
  exact (localUnitShell_compact v).image (continuous_const.mul continuous_id)

private theorem inverseValShell_integral {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : LocHaar v) (l : ℤ) (f : v.adicCompletion F → E) :
    (∫ x in inverseValShell v l, f x ∂μ.μ) =
      absFin v ((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) •
        ∫ u in localUnitShell v,
          f (((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) ∂μ.μ := by
  let a : (v.adicCompletion F)ˣ := unifLoc v ^ (-l)
  let ann := inverseValShell v l
  let g : v.adicCompletion F → E := ann.indicator f
  have hannMeas : MeasurableSet ann := (inverseValShell_compact l).measurableSet
  have hshellMeas : MeasurableSet (localUnitShell v) := (localUnitShell_compact v).measurableSet
  have htrans (x : v.adicCompletion F) : g ((a : v.adicCompletion F) * x) =
      (localUnitShell v).indicator (fun u => f ((a : v.adicCompletion F) * u)) x := by
    by_cases hx : x ∈ localUnitShell v
    · have hax : (a : v.adicCompletion F) * x ∈ ann := by
        change (a : v.adicCompletion F) * x ∈ inverseValShell v l
        rw [inverseValShell_eq_image]
        exact ⟨x, hx, rfl⟩
      simp [g, ann, hax, hx]
    · have hax : (a : v.adicCompletion F) * x ∉ ann := by
        change (a : v.adicCompletion F) * x ∉ inverseValShell v l
        rw [inverseValShell_eq_image]
        rintro ⟨y, hy, hEq⟩
        apply hx
        have hxy : y = x := mul_left_cancel₀ (Units.ne_zero a) hEq
        simpa [hxy] using hy
      simp [g, ann, hax, hx]
  have hscale := LocHaar.integral_comp_mul μ a g
  have htransInt :
      (∫ x, g ((a : v.adicCompletion F) * x) ∂μ.μ) =
        ∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ := by
    calc
      _ = ∫ x, (localUnitShell v).indicator
            (fun u => f ((a : v.adicCompletion F) * u)) x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact htrans x
      _ = _ := MeasureTheory.integral_indicator hshellMeas
  have hAnnInt : (∫ x, g x ∂μ.μ) = ∫ x in ann, f x ∂μ.μ :=
    MeasureTheory.integral_indicator hannMeas
  have hsc_eq :
      (∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ) =
        (absFin v a)⁻¹ • ∫ x in ann, f x ∂μ.μ := by
    calc
      _ = ∫ x, g ((a : v.adicCompletion F) * x) ∂μ.μ := htransInt.symm
      _ = (absFin v a)⁻¹ • ∫ x, g x ∂μ.μ := hscale
      _ = _ := by rw [hAnnInt]
  have ha0 : absFin v (a : v.adicCompletion F) ≠ 0 :=
    ne_of_gt (absFin_pos (Units.ne_zero a))
  change (∫ x in ann, f x ∂μ.μ) =
    absFin v (a : v.adicCompletion F) •
      ∫ x in localUnitShell v, f ((a : v.adicCompletion F) * x) ∂μ.μ
  calc
    _ = absFin v a • ((absFin v a)⁻¹ • ∫ x in ann, f x ∂μ.μ) := by
      rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
    _ = _ := by rw [← hsc_eq]

private theorem uniformizer_zpow_absFin (l : ℤ) :
    absFin v ((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ (-l) := by
  have hπ : absFin v (unifLoc v : v.adicCompletion F) = (qv v)⁻¹ := by
    rw [absFin_eq_norm, FinitePlace.norm_def]
    rw [show Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) by
      simpa using uniformizer_zpow_valuation (v := v) 1]
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
    rw [WithZero.toAdd_unzero_eq_log (by simp)]
    simp [qv]
  rw [absFin_eq_norm]
  simp only [Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [← absFin_eq_norm, hπ, inv_zpow, zpow_neg]

private theorem inverseKernel_scaled_unit (T : TorusRep D H v) (B : TameTorusBasis T)
    (A : AddCharData F) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ)
    (N : ℕ) (k : ZMod 3) (l : ℤ) (x : v.adicCompletion F)
    (hx : x ∈ localUnitShell v) :
    inverseKernel T B A s N k
      (((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) =
      if -(N : ℤ) ≤ l then
        ((((qv v ^ l : ℝ) : ℂ) ^ (-1 - 2 * s)) *
          (if hy : x⁻¹ ≠ 0 then
            localChi D v (Units.mk0 x⁻¹ hy) ^ (2 * (l + (k.val : ℤ))) *
              A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x⁻¹)
          else 0)) • B.e (k + 2 * (l : ZMod 3))
      else 0 := by
  let xU : localUnitShell v := ⟨x, hx⟩
  have hxne : x ≠ 0 := localUnitShell_ne_zero xU
  let u : (v.adicCompletion F)ˣ := Units.mk0 x hxne
  let y : (v.adicCompletion F)ˣ := unifLoc v ^ (-l) * u
  have hyne : (y : v.adicCompletion F) ≠ 0 := y.ne_zero
  have hival : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v x⁻¹ = 1
    rw [map_inv₀, show Valued.v x = 1 from hx, inv_one]
  have hiLoc : IsLocUnit v (u⁻¹) := by
    change IsLocUnit v ((localUnitShell.unit xU)⁻¹)
    exact ⟨(localUnitShell_isLocUnit xU).2, by simpa using (localUnitShell_isLocUnit xU).1⟩
  have hyInv : y⁻¹ = unifLoc v ^ l * u⁻¹ := by
    dsimp [y]
    rw [mul_inv_rev, ← zpow_neg]
    simp [mul_comm]
  have hval : Valued.v ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-l) := by
    rw [hyInv, Units.val_mul, map_mul, uniformizer_zpow_valuation, hival, mul_one]
  have hcut : (((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      ball v (-(N : ℤ))) ↔ -(N : ℤ) ≤ l := by
    simp only [ball, Set.mem_setOf_eq, Int.neg_neg, hval, WithZero.exp_le_exp]
    omega
  have hyabs : absFin v (y : v.adicCompletion F) = qv v ^ l := by
    rw [show (y : v.adicCompletion F) =
      ((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x by rfl]
    simp only [absFin_eq_norm, norm_mul]
    rw [← absFin_eq_norm, uniformizer_zpow_absFin, neg_neg]
    have hnorm : ‖x‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hx
    rw [hnorm, mul_one]
  have hmk : Units.mk0 (y : v.adicCompletion F) hyne = y := by ext; rfl
  have huInv : Units.mk0 x⁻¹ (inv_ne_zero hxne) = u⁻¹ := by ext; rfl
  change inverseKernel T B A s N k (y : v.adicCompletion F) = _
  unfold inverseKernel
  rw [dif_pos hyne, hmk, hcut]
  by_cases hnl : -(N : ℤ) ≤ l
  · rw [if_pos hnl, if_pos hnl, hyabs, LinearMap.map_smul,
      hyInv, tame_square_action T B hv l (u⁻¹) hiLoc k, dif_pos (inv_ne_zero hxne), huInv]
    simp only [Units.val_mul, smul_smul, Units.val_inv_eq_inv_val, u, Units.val_mk0]
    congr 1
    ring
  · rw [if_neg hnl, if_neg hnl]

private theorem inverse_shell_cpow (l : ℤ) (s : ℂ) :
    ((qv v ^ l : ℝ) : ℂ) * (((qv v ^ l : ℝ) : ℂ) ^ (-1 - 2 * s)) =
      (qv v : ℂ) ^ (-2 * (l : ℂ) * s) := by
  have hq : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hqne : (qv v : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have harg : (qv v : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hq.le
  have hlo : -Real.pi < (l : ℝ) * (qv v : ℂ).arg := by rw [harg]; linarith [Real.pi_pos]
  have hhi : (l : ℝ) * (qv v : ℂ).arg ≤ Real.pi := by rw [harg]; linarith [Real.pi_pos]
  rw [Complex.ofReal_zpow, ← Complex.cpow_int_mul' hlo hhi,
    ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hqne]
  congr 1
  ring

/-- Exact contribution of one valuation shell to the inverse-parameter kernel. -/
theorem inverse_kernel_shell_integral (T : TorusRep D H v) (B : TameTorusBasis T)
    (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (s : ℂ)
    (N : ℕ) (k : ZMod 3) (l : ℤ) :
    (∫ x in inverseValShell v l, inverseKernel T B A s N k x ∂μ.μ) =
      if -(N : ℤ) ≤ l then
        ((qv v : ℂ) ^ (-2 * (l : ℂ) * s) *
          (if 0 ≤ l then
            if ((l + (k.val : ℤ) : ℤ) : ZMod 3) = 0 then 1 - (qv v : ℂ)⁻¹ else 0
          else if l = -1 then
            (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (2 * ((k.val : ℤ) - 1))
          else 0)) • B.e (k + 2 * (l : ZMod 3))
      else 0 := by
  classical
  letI : CompleteSpace T.V := inferInstance
  rw [inverseValShell_integral, uniformizer_zpow_absFin, neg_neg]
  let scalar : v.adicCompletion F → ℂ := fun y =>
    if hy : y ≠ 0 then localChi D v (Units.mk0 y hy) ^ (2 * (l + (k.val : ℤ))) *
      A.ψ v (((unifLoc v ^ l : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y)
    else 0
  have hcongr :
      (∫ x in localUnitShell v,
        inverseKernel T B A s N k
          (((unifLoc v ^ (-l) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ∂μ.μ) =
      ∫ x in localUnitShell v,
        (if -(N : ℤ) ≤ l then
          ((((qv v ^ l : ℝ) : ℂ) ^ (-1 - 2 * s)) * scalar x⁻¹) •
            B.e (k + 2 * (l : ZMod 3)) else 0) ∂μ.μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (localUnitShell_compact v).measurableSet] with x hx
    exact inverseKernel_scaled_unit T B A hv s N k l x hx
  rw [hcongr]
  by_cases hnl : -(N : ℤ) ≤ l
  · simp only [if_pos hnl, mul_smul]
    rw [integral_smul, integral_smul_const]
    have hinv : (∫ x in localUnitShell v, scalar x⁻¹ ∂μ.μ) =
        ∫ x in localUnitShell v, scalar x ∂μ.μ := unit_integral_inv μ scalar
    rw [hinv]
    have hscalar := tame_unit_shell_integral (D := D) A μ hv hd l k
    change (∫ x in localUnitShell v, scalar x ∂μ.μ) = _ at hscalar
    rw [hscalar]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_smul]
    rw [← mul_assoc]
    exact congrArg (fun c : ℂ => (c *
      (if 0 ≤ l then
        if ((l + (k.val : ℤ) : ℤ) : ZMod 3) = 0 then 1 - (qv v : ℂ)⁻¹ else 0
      else if l = -1 then
        (qv v : ℂ) ^ (-(1 / 2 : ℂ)) * gaussLoc D A v (2 * ((k.val : ℤ) - 1))
      else 0)) • B.e (k + 2 * (l : ZMod 3))) (inverse_shell_cpow (v := v) l s)
  · simp [hnl]

end ArtinPrimitiveRoots.Proofs.th_lcoeff_sol
