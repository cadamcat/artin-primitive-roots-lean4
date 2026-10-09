import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueAdditive
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_f.Prelim

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance gaussianPrimeIntegralMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance gaussianPrimeIntegralBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Compute the stabilized uniformizer Gaussian as the exact exterior residue square sum.
Guide: PROOFS.md:476–477. Uses: A.integral; A.trivial_on_F; A.unramified; W.stable; residue-ball cosets. -/
theorem exterior_prime_index_square_sum (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    ((W.index v (toLoc v (p⁻¹)) : ℂˣ) : ℂ) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
  classical
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let k := 𝓞 F ⧸ v.asIdeal
  letI : Field k := Ideal.Quotient.field v.asIdeal
  letI : Finite k := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hcardR : (Fintype.card k : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast hcard
  let μ := W.measure v
  let π : (v.adicCompletion F)ˣ := toLoc v p
  have hπfield :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.gen_local_valuation S v hv p hp
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hcoerce : (π : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (p : F) := by
      simp [π, toLoc]
    calc
      _ = Valued.v (algebraMap F (v.adicCompletion F) (p : F)) := by rw [hcoerce]
      _ = Valued.v ((p : F) : v.adicCompletion F) := by
        rw [HeightOneSpectrum.algebraMap_adicCompletion]
        rfl
      _ = WithZero.exp (-1 : ℤ) := by
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact hπfield
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hv (S.over6 v ?_)
    simpa [show (6 : 𝓞 F) = (3 : 𝓞 F) * 2 by norm_num] using
      v.asIdeal.mul_mem_left (3 : 𝓞 F) h
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
    intro h
    exact hv (S.different_mem v h)
  obtain ⟨_, hunramified⟩ := A.unramified v hdiff
  obtain ⟨b, hψ⟩ := hunramified (p : F)
    (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.gen_local_valuation S v hv p hp)
  obtain ⟨ψbar, hψbar, hψprim⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_additive_character_exists
      D S A v hp.1 (p : F) hp
  let a : (v.adicCompletion F)ˣ := toLoc v (p⁻¹)
  let N := max (W.cutoff v a) (W.cutoff v 1)
  have hnumStable := W.stable v a N (Nat.le_max_left _ _)
  have hdenStable := W.stable v 1 N (Nat.le_max_right _ _)
  letI : Measure.IsAddHaarMeasure μ := W.isHaar v
  have hball0 :
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.localBall v 0 =
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    change Valued.v x ≤ WithZero.exp (0 : ℤ) ↔ x ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp
  have hdenBall0 :
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 0 =
        ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) := by
    unfold ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral
    change (∫ x in ArtinPrimitiveRoots.Proofs.a1_weil_sol.localBall v 0,
      A.ψ v (((1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2) ∂μ) = _
    rw [hball0]
    calc
      _ = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
          (fun _ : v.adicCompletion F => (1 : ℂ)) x ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem
          ((ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completion_integers_compact v).measurableSet)]
          with x hx
        have hx2 : x ^ 2 ∈ v.adicCompletionIntegers F := by
          simpa [pow_two] using (v.adicCompletionIntegers F).mul_mem x x hx hx
        simpa using A.integral v _ hx2
      _ = _ := by simp [MeasureTheory.measureReal_def]
  let E : k → ℂ := fun r =>
    S.e A (S.diag (((r.out : F) ^ 2) / (p : F)))
  have hterm (r : k) : ψbar (r ^ 2) = E r := by
    have hmk : Ideal.Quotient.mk v.asIdeal (r.out ^ 2) = r ^ 2 := by
      calc
        Ideal.Quotient.mk v.asIdeal (r.out ^ 2) =
            (Ideal.Quotient.mk v.asIdeal r.out) ^ 2 := by rw [map_pow]
        _ = r ^ 2 := by rw [Ideal.Quotient.mk_out]
    calc
      ψbar (r ^ 2) = ψbar (Ideal.Quotient.mk v.asIdeal (r.out ^ 2)) := by rw [← hmk]
      _ = S.e A (S.diag (algebraMap (𝓞 F) F (r.out ^ 2) / (p : F))) := hψbar (r.out ^ 2)
      _ = E r := by
        congr 1
  have hζintZ : IsIntegral ℤ D.ζ12 := by
    apply IsIntegral.of_pow (n := 12) (by decide)
    simpa [D.hζ12.pow_eq_one] using (isIntegral_one : IsIntegral ℤ (1 : F))
  have hζintO : IsIntegral (𝓞 F) D.ζ12 := hζintZ.tower_top
  obtain ⟨ζO, hζO⟩ := IsIntegrallyClosed.isIntegral_iff.mp hζintO
  have hnegone : (Ideal.Quotient.mk v.asIdeal (ζO ^ 3) : k) ^ 2 = -1 := by
    have hζsq : (D.ζ12 ^ 6) ^ 2 = 1 := by
      calc
        (D.ζ12 ^ 6) ^ 2 = D.ζ12 ^ (6 * 2) := by rw [pow_mul]
        _ = D.ζ12 ^ 12 := by norm_num
        _ = 1 := D.hζ12.pow_eq_one
    have hζne : D.ζ12 ^ 6 ≠ 1 :=
      D.hζ12.pow_ne_one_of_pos_of_lt (by decide) (by decide)
    have hζ6 : D.ζ12 ^ 6 = -1 := (sq_eq_one_iff.mp hζsq).resolve_left hζne
    have hζO6 : ζO ^ 6 = -1 := by
      apply (IsFractionRing.injective (𝓞 F) F)
      calc
        algebraMap (𝓞 F) F (ζO ^ 6) = (algebraMap (𝓞 F) F ζO) ^ 6 := by rw [map_pow]
        _ = D.ζ12 ^ 6 := by rw [hζO]
        _ = -1 := hζ6
    rw [← map_pow, show (ζO ^ 3) ^ 2 = ζO ^ 6 by ring, hζO6]
    simp
  have hroot0 : (Ideal.Quotient.mk v.asIdeal (ζO ^ 3) : k) ≠ 0 := by
    intro h
    rw [h] at hnegone
    norm_num at hnegone
  let ι : kˣ := Units.mk0 (Ideal.Quotient.mk v.asIdeal (ζO ^ 3)) hroot0
  have hι : (ι : k) ^ 2 = -1 := hnegone
  let eMul : k ≃ k :=
    { toFun := fun x => (ι : k) * x
      invFun := fun x => ((ι⁻¹ : kˣ) : k) * x
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc] }
  have hsumInv : (∑ r : k, (E r)⁻¹) = ∑ r : k, E r := by
    calc
      (∑ r : k, (E r)⁻¹) = ∑ r : k, (ψbar (r ^ 2))⁻¹ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hterm]
      _ = ∑ r : k, ψbar (-r ^ 2) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact (ψbar.map_neg_eq_inv (r ^ 2)).symm
      _ = ∑ r : k, ψbar ((ι * r) ^ 2) := by
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        rw [mul_pow, hι]
        ring
      _ = ∑ r : k, ψbar (r ^ 2) :=
        Equiv.sum_comp eMul (fun r : k => ψbar (r ^ 2))
      _ = ∑ r : k, E r := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
  have houter (r : k) (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
      w.valuation F (((r.out : F) ^ 2) / (p : F)) ≤ 1 := by
    have hpw := ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.gen_local_valuation_other
      S v w hv p hp hw hwv
    have hrv : w.valuation F (r.out : F) ≤ 1 := w.valuation_le_one r.out
    rw [map_div₀, map_pow, hpw, div_one]
    exact Left.pow_le_one_of_le hrv 2
  have hlocal (r : k) :
      A.ψ v (algebraMap F (v.adicCompletion F) (((r.out : F) ^ 2) / (p : F))) =
        (E r)⁻¹ := by
    exact ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.globalCharacterInverse
      D S A v hv (((r.out : F) ^ 2) / (p : F)) (houter r)
  have hcenterCast (r : k) :
      (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionResidueCenter v r :
        v.adicCompletion F) = algebraMap F (v.adicCompletion F) (r.out : F) :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionIntegerCast v r.out
  have hcenterArg (r : k) :
      ((toLoc v (p⁻¹) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionResidueCenter v r :
            v.adicCompletion F) ^ 2 =
        algebraMap F (v.adicCompletion F) (((r.out : F) ^ 2) / (p : F)) := by
    calc
      _ = algebraMap F (v.adicCompletion F)
          ((p : F)⁻¹ * (r.out : F) ^ 2) := by
        rw [show ((toLoc v (p⁻¹) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) ((p : F)⁻¹) by simp [toLoc], hcenterCast]
        rw [← map_pow, ← map_mul]
      _ = algebraMap F (v.adicCompletion F) (((r.out : F) ^ 2) / (p : F)) := by
        congr 1
        rw [div_eq_mul_inv]
        ring
  have hcenterChar (r : k) :
      A.ψ v (((toLoc v (p⁻¹) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionResidueCenter v r :
            v.adicCompletion F) ^ 2) = (E r)⁻¹ := by
    rw [hcenterArg]
    exact hlocal r
  have hmeasureFiber (r : k) :
      μ.real (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r) =
        μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
          (Fintype.card k : ℝ) := by
    letI : Measure.IsAddHaarMeasure μ := W.isHaar v
    let β := μ.real (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.primeBall v)
    have hsameAll (r : k) :=
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_measure
        v π hπ μ (W.isHaar v) r
    have hsame := hsameAll r
    have hsum := ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_measure_sum
      v π hπ μ (W.isHaar v)
    have hcardpos : 0 < Fintype.card k := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardne : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcardpos.ne'
    have hmul : (Fintype.card k : ℝ) * β =
        μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      calc
        _ = ∑ r : k, β := by simp [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ r : k,
            μ.real (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r) := by
              apply Finset.sum_congr rfl
              intro r hr
              rw [hsameAll r]
        _ = _ := hsum.symm
    calc
      _ = β := hsame
      _ = μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
          (Fintype.card k : ℝ) := by
        field_simp [hcardne]
        linarith [hmul]
  have hbaseNum :
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ a 0 =
        (((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
          (Fintype.card k : ℝ)) : ℝ) : ℂ) * ∑ r : k, E r := by
    unfold ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral
    change (∫ x in ArtinPrimitiveRoots.Proofs.a1_weil_sol.localBall v 0,
      A.ψ v (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2) ∂μ) = _
    rw [hball0]
    conv_lhs =>
      rw [← ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_iUnion v π hπ]
    let hf : v.adicCompletion F → ℂ := fun x =>
      A.ψ v (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
    have hcont : Continuous hf := by
      have hψcont : Continuous (A.ψ v) :=
        (ArtinPrimitiveRoots.Proofs.a1_weil_sol.local_character_regular D A v).1
      have hquad : Continuous (fun x : v.adicCompletion F =>
          ((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2) := by fun_prop
      dsimp [hf]
      exact hψcont.comp hquad
    have hInt (r : k) : IntegrableOn hf
        (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r) μ :=
      hcont.continuousOn.integrableOn_compact
        (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_compact
          v π hπ r)
    have hdecompInt : (∫ x in ⋃ r : k,
        ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r, hf x ∂μ) =
        ∑ r : k, ∫ x in ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r,
          hf x ∂μ := integral_iUnion_fintype
      (fun r => ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_measurable
        v π hπ r)
      (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_pairwise v π hπ) hInt
    calc
      _ = ∫ x in ⋃ r : k,
          ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r, hf x ∂μ := rfl
      _ = ∑ r : k, ∫ x in ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r,
          hf x ∂μ := hdecompInt
      _ = ∑ r : k,
          (((μ.real (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r) : ℝ) : ℂ) *
            A.ψ v (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
              (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionResidueCenter v r :
                v.adicCompletion F) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro r hr
        calc
          _ = ∫ x in ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber v r,
              (fun _ : v.adicCompletion F => A.ψ v
                (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
                  (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.completionResidueCenter v r :
                    v.adicCompletion F) ^ 2)) x ∂μ := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem
              (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.localIntResidueFiber_measurable
                v π hπ r)] with x hx
            simpa [hf, a] using
              (ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.quadraticIntFiber_phase_eq
                A v π hπ p rfl r x hx)
          _ = _ := by simp [MeasureTheory.measureReal_def]
      _ = (((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
          (Fintype.card k : ℝ)) : ℝ) : ℂ) * ∑ r : k, (E r)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [hmeasureFiber r, hcenterChar r]
      _ = (((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
          (Fintype.card k : ℝ)) : ℝ) : ℂ) * ∑ r : k, E r := by rw [hsumInv]
  have hnumN :
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ a N =
        ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ a 0 := by
    simpa [a] using ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.quadraticIntegral_eq_ball_zero
      D A v μ (W.isHaar v) p hπ h2 b hψ 1 N (by omega)
  have hdenN :
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 N =
        ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 0 := by
    simpa using ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.quadraticIntegral_eq_ball_zero
      D A v μ (W.isHaar v) p hπ h2 b hψ 0 N (by omega)
  have hdenO : ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 N =
      ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) :=
    hdenN.trans hdenBall0
  have hmuO_ne : μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 := by
    have hcut := W.integral_ne_zero v 1
    have hdenN_ne : ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 N ≠ 0 := by
      rw [hdenStable]
      exact hcut
    intro hzero
    apply hdenN_ne
    rw [hdenO, hzero]
    simp
  have hnormCoeff :
      (((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) *
          (((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
            (Fintype.card k : ℝ)) : ℝ) : ℂ) /
            ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) =
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) := by
    have habs : absFin v (a : v.adicCompletion F) = (Ideal.absNorm v.asIdeal : ℝ) := by
      dsimp [a]
      exact ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f.absFin_toLoc_inv v p hπ
    rw [habs, hcardR]
    have hqne : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
      exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    have hqpow :
        (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) /
          (Ideal.absNorm v.asIdeal : ℝ) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) /
            (Ideal.absNorm v.asIdeal : ℝ) =
          (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) /
            (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := by simp
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ ((1 / 2 : ℝ) - 1) := by
          exact (Real.rpow_sub
            (by positivity : 0 < (Ideal.absNorm v.asIdeal : ℝ)) (1 / 2 : ℝ) (1 : ℝ)).symm
        _ = _ := by congr 1 <;> norm_num
    have hcoeffR :
        (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) *
          (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
            (Ideal.absNorm v.asIdeal : ℝ)) /
          μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) /
            (Ideal.absNorm v.asIdeal : ℝ) := by
          field_simp [hmuO_ne, hqne]
        _ = _ := hqpow
    exact_mod_cast hcoeffR
  have hsumTarget : (∑ r : k, E r) =
      ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
        S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
    rw [finsum_eq_sum_of_fintype]
  calc
    ((W.index v (toLoc v (p⁻¹)) : ℂˣ) : ℂ) =
        (((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) *
          ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ a
            (W.cutoff v a) /
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1
                (W.cutoff v 1) := by
      simp [ArtinPrimitiveRoots.Proofs.a1_weil_sol.LocalGaussianData.index, a, μ]
    _ = (((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) *
          ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ a N /
            ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ 1 N := by
      rw [← hnumStable, ← hdenStable]
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ r : k, E r := by
      rw [hnumN, hbaseNum, hdenO]
      calc
        _ = ((((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) *
            (((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
              (Fintype.card k : ℝ)) : ℝ) : ℂ) /
              ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ)) *
              ∑ r : k, E r := by ring
        _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
              ∑ r : k, E r := by rw [hnormCoeff]
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
            S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
      rw [hsumTarget]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
