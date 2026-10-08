import ArtinPrimitiveRoots.A1.ThetaInterface
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

private def unifLoc (v : FinPlace F) : (v.adicCompletion F)ˣ :=
  toLoc v (Units.mk0 (unif v) (unif_ne_zero v))

private def IsLocUnit (v : FinPlace F) (u : (v.adicCompletion F)ˣ) : Prop :=
  (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
  ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F

local instance theta_residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance theta_residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem theta_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal) (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
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

private theorem theta_residue_algInt (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  have h := theta_residue_rep v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  simpa using h

private theorem theta_residue_integral_congr (v : FinPlace F) (a b : 𝓞 F)
    (hab : Valued.v (((a : F) : v.adicCompletion F) - ((b : F) : v.adicCompletion F)) < 1) :
    residue v (a : F) = residue v (b : F) := by
  have hab' : Valued.v (algebraMap F (v.adicCompletion F) ((a : F) - (b : F))) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_sub] using hab
  have hval : v.valuation F ((a : F) - (b : F)) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hab'
  have hmem : a - b ∈ v.asIdeal := (v.valuation_lt_one_iff_mem (K := F) _).1 hval
  rw [theta_residue_algInt, theta_residue_algInt]
  rw [← sub_eq_zero, ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem

private theorem theta_chi_congr (D : FieldData F) (v : FinPlace F) (x y : F)
    (h : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, h]

private theorem localChi_of_approx (D : FieldData F) (v : FinPlace F)
    (t : (v.adicCompletion F)ˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hta : Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1) :
    localChi D v t = chi D v (a : F) := by
  have hex : ∃ b : 𝓞 F, b ∉ v.asIdeal ∧ Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1 := ⟨a, ha, hta⟩
  have hcmp' : Valued.v (((hex.choose : F) : v.adicCompletion F) -
      ((a : F) : v.adicCompletion F)) < 1 := by
    have h := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_sub_lt hta hex.choose_spec.2
    have hEq : ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) -
        ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose)) =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose) -
            algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by ring
    rw [hEq] at h
    exact h
  have hres : residue v (hex.choose : F) = residue v (a : F) := by
    exact theta_residue_integral_congr v hex.choose a hcmp'
  unfold localChi
  rw [dif_pos hex]
  exact theta_chi_congr D v _ _ hres

private theorem local_unit_approximant (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) :
    ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 := by
  let O := v.adicCompletionIntegers F
  let uO : O := ⟨(u : v.adicCompletion F), hu.1⟩
  let uInvO : O := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hu.2⟩
  have hprod : uO * uInvO = (1 : O) := by
    apply Subtype.ext
    simp [uO, uInvO]
  have hresNe : IsLocalRing.residue O uO ≠ 0 := by
    intro hz
    have hp := congrArg (IsLocalRing.residue O) hprod
    rw [map_mul, map_one, hz, zero_mul] at hp
    exact zero_ne_one hp
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let r := e.symm (IsLocalRing.residue O uO)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective r
  have hbar : e (Ideal.Quotient.mk v.asIdeal a) = IsLocalRing.residue O uO := by
    rw [ha]
    exact e.apply_symm_apply _
  have hresA : IsLocalRing.residue O uO =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a) := by
    rw [← hbar, v.residueFieldEquivAdicCompletionIntegers_apply_mk]
  have ha_not : a ∉ v.asIdeal := by
    intro hamem
    have hmk : Ideal.Quotient.mk v.asIdeal a = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hamem
    have hzero : IsLocalRing.residue O uO = 0 := by
      rw [← hbar, hmk]
      rfl
    exact hresNe hzero
  have hdiff_mem : uO - algebraMap (𝓞 F) O a ∈ IsLocalRing.maximalIdeal O := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    have hzero : IsLocalRing.residue O (uO - algebraMap (𝓞 F) O a) = 0 := by
      rw [map_sub]
      have hresA' : IsLocalRing.residue O uO =
          IsLocalRing.residue O (algebraMap (𝓞 F) O a) := by
        change IsLocalRing.residue O uO =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a)
        exact hresA
      rw [hresA', sub_self]
    exact hzero
  have hmax (z : O) : z ∈ IsLocalRing.maximalIdeal O ↔
      Valued.v (z : v.adicCompletion F) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (v.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))
  have hlt : Valued.v ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) < 1 :=
    (hmax _).1 hdiff_mem
  have hmap : ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    exact (HeightOneSpectrum.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers
      (K := F) (v := v) a).symm
  have hcoerce : ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      (u : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    change (uO : v.adicCompletion F) -
      ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) = _
    rw [hmap]
  rw [hcoerce] at hlt
  refine ⟨a, ha_not, ?_⟩
  exact hlt

private lemma theta_count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma theta_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (a : 𝓞 F) (ha : a ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F a)) = -WithZero.log (v.intValuation a) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg ha, WithZero.log_exp]
  ring

private lemma theta_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
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
    theta_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    theta_count_spanSingleton_eq_neg_log_intValuation v n hn,
    theta_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem exists_globalUnit_symbol_approx (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    ∃ a : Fˣ, residue v (a : F) ≠ 0 ∧ v.valuation F (a : F) = 1 ∧
      localChi D v u = chi D v (a : F) ∧
      ∀ b, H.hilb v u b = H.hilb v (toLoc v a) b := by
  obtain ⟨a, ha, hta⟩ := local_unit_approximant v u hu
  let a₀ : Fˣ := Units.mk0 (a : F) (by
    intro hz
    apply ha
    have h : a = 0 := IsFractionRing.injective (𝓞 F) F (by simpa using hz)
    rw [h]
    exact Ideal.zero_mem _)
  let aLoc : (v.adicCompletion F)ˣ := toLoc v a₀
  let O := v.adicCompletionIntegers F
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let uO : O := ⟨(u : v.adicCompletion F), hu.1⟩
  let aO : O := algebraMap (𝓞 F) O a
  have hvalA : v.valuation F (a : F) = 1 := by
    apply le_antisymm (v.valuation_le_one (R := 𝓞 F) (K := F) a)
    apply le_of_not_gt
    intro hlt
    exact ha ((v.valuation_lt_one_iff_mem (K := F) a).mp hlt)
  have hmapA : (aO : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (a : F) := by
    exact (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers a).symm
  have hvalAO : Valued.v (aO : v.adicCompletion F) = 1 := by
    rw [hmapA]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hvalA
  have haUnit : IsUnit aO :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).2 hvalAO
  let aOUnit : Oˣ := haUnit.unit
  have haOUnit : (aOUnit : O) = aO := haUnit.unit_spec
  let huInvO : O := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hu.2⟩
  have huOInv : uO * huInvO = 1 := by
    apply Subtype.ext
    simp [uO, huInvO]
  have huInvO' : huInvO * uO = 1 := by
    apply Subtype.ext
    simp [uO, huInvO]
  have huUnit : IsUnit uO := ⟨⟨uO, huInvO, huOInv, huInvO'⟩, rfl⟩
  let uOUnit : Oˣ := huUnit.unit
  have huOUnit : (uOUnit : O) = uO := huUnit.unit_spec
  let rOUnit : Oˣ := uOUnit * aOUnit⁻¹
  let rLoc : (v.adicCompletion F)ˣ := u * aLoc⁻¹
  have hmapA₀ : (aLoc : v.adicCompletion F) = (aO : v.adicCompletion F) := by
    rw [hmapA]
    simp [aLoc, a₀, toLoc]
  have hratioO : (rOUnit : O) - 1 = (uO - aO) * ((aOUnit⁻¹ : Oˣ) : O) := by
    have haInv : aO * ((aOUnit⁻¹ : Oˣ) : O) = 1 := by
      rw [← haOUnit]
      simp
    calc
      (rOUnit : O) - 1 = uO * ((aOUnit⁻¹ : Oˣ) : O) - 1 := by
        simp [rOUnit, huOUnit]
      _ = (uO - aO) * ((aOUnit⁻¹ : Oˣ) : O) := by
        rw [sub_mul, haInv]
  have hmax (z : O) : z ∈ m ↔
      Valued.v (z : v.adicCompletion F) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (v.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))
  have hdiffO : uO - aO ∈ m := by
    apply (hmax _).2
    have hcoerce : ((uO - aO : O) : v.adicCompletion F) =
        (u : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (a : F) := by
      change (uO : v.adicCompletion F) - (aO : v.adicCompletion F) = _
      rw [hmapA]
    rw [hcoerce]
    exact hta
  have hrNear : (rOUnit : O) - 1 ∈ m := by
    rw [hratioO]
    exact m.mul_mem_right _ hdiffO
  have h6val : v.valuation F (6 : F) = 1 := by
    apply le_antisymm (v.valuation_le_one (R := 𝓞 F) (K := F) (6 : 𝓞 F))
    apply le_of_not_gt
    intro hlt
    exact hv ((v.valuation_lt_one_iff_mem (K := F) (6 : 𝓞 F)).mp hlt)
  have h6map : (6 : O) = algebraMap (𝓞 F) O (6 : 𝓞 F) := by
    exact (map_natCast (algebraMap (𝓞 F) O) 6).symm
  have hmap6 : ((algebraMap (𝓞 F) O (6 : 𝓞 F) : O) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (6 : F) :=
    (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (6 : 𝓞 F)).symm
  have hval6O : Valued.v ((6 : O) : v.adicCompletion F) = 1 := by
    rw [h6map, hmap6]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using h6val
  have h6not : (6 : O) ∉ m := by
    intro h
    have hlt := (hmax (6 : O)).1 h
    rw [hval6O] at hlt
    exact (lt_irrefl 1) hlt
  have h6Unit : IsUnit (6 : O) := IsLocalRing.notMem_maximalIdeal.mp h6not
  letI : HenselianRing O m := inferInstance
  obtain ⟨cO, hcPow, hcNear⟩ :=
    TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
      (I := m) (J := m) le_rfl (n := 6) h6Unit hrNear
  have hc0 : (cO : O) ≠ 0 := by
    intro hc
    have hr0 : (rOUnit : O) = 0 := by rw [← hcPow, hc]; simp
    exact rOUnit.ne_zero hr0
  let cLoc : (v.adicCompletion F)ˣ := Units.mk0 (cO : v.adicCompletion F) (by
    simpa using hc0)
  let algU : Oˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap O (v.adicCompletion F)).toMonoidHom
  have hmapu : algU uOUnit = u := by
    apply Units.ext
    change algebraMap O (v.adicCompletion F) (uOUnit : O) = (u : v.adicCompletion F)
    rw [huOUnit]
    rfl
  have hmapa : algU aOUnit = aLoc := by
    apply Units.ext
    change algebraMap O (v.adicCompletion F) (aOUnit : O) = (aLoc : v.adicCompletion F)
    rw [haOUnit]
    exact hmapA₀.symm
  have hmapr : algU rOUnit = rLoc := by
    calc
      algU rOUnit = algU uOUnit * (algU aOUnit)⁻¹ := by simp [rOUnit]
      _ = rLoc := by rw [hmapu, hmapa]
  have hrOtoK : (rOUnit : v.adicCompletion F) = (rLoc : v.adicCompletion F) := by
    have h := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hmapr
    change algebraMap O (v.adicCompletion F) (rOUnit : O) = (rLoc : v.adicCompletion F) at h
    change algebraMap O (v.adicCompletion F) (rOUnit : O) = (rLoc : v.adicCompletion F)
    exact h
  have hcLoc : cLoc ^ 6 = rLoc := by
    apply Units.ext
    change ((cO : O) : v.adicCompletion F) ^ 6 = (rLoc : v.adicCompletion F)
    calc
      ((cO : O) : v.adicCompletion F) ^ 6 = (rOUnit : v.adicCompletion F) := by
        exact congrArg (algebraMap O (v.adicCompletion F)) hcPow
      _ = (rLoc : v.adicCompletion F) := hrOtoK
  have hfactor : rLoc * aLoc = u := by
    dsimp [rLoc]
    simp [mul_assoc]
  have hsymbol_local (b : (v.adicCompletion F)ˣ) :
      H.hilb v u b = H.hilb v aLoc b := by
    calc
      H.hilb v u b = H.hilb v (rLoc * aLoc) b := by rw [hfactor]
      _ = H.hilb v rLoc b * H.hilb v aLoc b := H.mul_left v rLoc aLoc b
      _ = H.hilb v aLoc b := by
        rw [H.sixth_power v rLoc b ⟨cLoc, hcLoc.symm⟩]
        simp
  have hresA : residue v (a : F) ≠ 0 := by
    rw [theta_residue_algInt]
    exact fun hz => ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  exact ⟨a₀, hresA, hvalA, localChi_of_approx D v u a ha hta, hsymbol_local⟩

private theorem effective_hilb_unif_unit (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e : ℤ)
    (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) =
      localChi D v u ^ (-(2 * e)) := by
  obtain ⟨a₀, hresA, hvalA, hχ, hsymbol_local⟩ :=
    exists_globalUnit_symbol_approx D H v hv u hu
  let aLoc := toLoc v a₀
  let π : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
  have hπval : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) := by
    dsimp [unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (unif v)) = 1 := by
    rw [theta_count_spanSingleton_eq_neg_log_valuation v (unif v) (unif_ne_zero v),
      hπval, WithZero.log_exp]
    norm_num
  have htame := H.tame v hv a₀ π hresA
  have htame' : (((H.hilb v aLoc (unifLoc v) : rootsOfUnity 6 F) : Fˣ) : F) =
      algebraMap (𝓞 F) F (((chiAlg v (a₀ : F) : (𝓞 F)ˣ) : 𝓞 F)) := by
    simpa [aLoc, π, unifLoc, hcount, zpow_one] using htame
  have hchi : D.σ0 ((((H.hilb v aLoc (unifLoc v) : rootsOfUnity 6 F) : Fˣ) : F)) =
      chi D v (a₀ : F) := by
    rw [chi, if_neg hresA]
    exact congrArg D.σ0 htame'
  let φ : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F := {
    toFun := fun b => H.hilb v aLoc b
    map_one' := by
      have h := H.skew v aLoc 1
      rw [H.sixth_power v 1 aLoc ⟨1, by simp⟩] at h
      simpa using h
    map_mul' := by intro b b'; exact H.mul_right v aLoc b b'
  }
  let ζ : rootsOfUnity 6 F := H.hilb v aLoc (unifLoc v)
  have hpow : H.hilb v u (unifLoc v ^ e) = ζ ^ e := by
    rw [hsymbol_local]
    change φ (unifLoc v ^ e) = φ (unifLoc v) ^ e
    exact φ.map_zpow (unifLoc v) e
  have htarget : H.hilb v (unifLoc v ^ e) u = ζ ^ (-e) := by
    have h := H.skew v (unifLoc v ^ e) u
    rw [hpow] at h
    rw [mul_comm] at h
    calc
      H.hilb v (unifLoc v ^ e) u = (ζ ^ e)⁻¹ := eq_inv_of_mul_eq_one_right h
      _ = ζ ^ (-e) := by simp
  have hmuEval (ξ : rootsOfUnity 6 F) :
      ((muThree D ξ : ℂˣ) : ℂ) = (D.σ0 ((ξ : Fˣ) : F)) ^ 2 := by
    simp [muThree]
  let σu : Fˣ →* ℂˣ := Units.map D.σ0.toMonoidHom
  have hσzpow (n : ℤ) :
      D.σ0 ((((ζ : Fˣ) ^ n : Fˣ) : F)) =
        (D.σ0 ((ζ : Fˣ) : F)) ^ n := by
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) (σu.map_zpow (ζ : Fˣ) n)
    simpa [σu] using h
  have hζcoe (n : ℤ) :
      ((ζ ^ n : rootsOfUnity 6 F) : Fˣ) = (ζ : Fˣ) ^ n := by
    rfl
  have hmu : ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) =
      D.σ0 ((((ζ ^ (-(2 * e)) : rootsOfUnity 6 F) : Fˣ) : F)) := by
    rw [htarget, hmuEval]
    change (D.σ0 (((ζ : Fˣ) ^ (-e) : Fˣ) : F)) ^ 2 =
      D.σ0 (((ζ : Fˣ) ^ (-(2 * e)) : Fˣ) : F)
    rw [hσzpow (-e), hσzpow (-(2 * e))]
    let s : ℂ := D.σ0 ((ζ : Fˣ) : F)
    change (s ^ (-e)) ^ 2 = s ^ (-(2 * e))
    calc
      (s ^ (-e)) ^ 2 = s ^ ((-e) * 2) := by
        rw [← zpow_natCast]
        exact (zpow_mul s (-e) 2).symm
      _ = s ^ (-(2 * e)) := by congr 1 <;> ring
  have hσpow : D.σ0 (((ζ : Fˣ) : F) ^ (-(2 * e))) =
      (D.σ0 ((ζ : Fˣ) : F)) ^ (-(2 * e)) := by
    simpa using hσzpow (-(2 * e))
  calc
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) =
        D.σ0 ((((ζ ^ (-(2 * e)) : rootsOfUnity 6 F) : Fˣ) : F)) := hmu
    _ = D.σ0 (((ζ : Fˣ) : F) ^ (-(2 * e))) := by simp
    _ = (D.σ0 ((ζ : Fˣ) : F)) ^ (-(2 * e)) := hσpow
    _ = chi D v (a₀ : F) ^ (-(2 * e)) := by rw [hchi]
    _ = localChi D v u ^ (-(2 * e)) := by
      rw [hχ]


private theorem effective_hilb_units (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (u u' : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) (hu' : IsLocUnit v u') :
    H.hilb v u u' = 1 := by
  obtain ⟨a, ha, hva, hχa, hsymbola⟩ :=
    exists_globalUnit_symbol_approx D H v hv u hu
  obtain ⟨b, hb, hvb, hχb, hsymbolb⟩ :=
    exists_globalUnit_symbol_approx D H v hv u' hu'
  have hright : H.hilb v (toLoc v a) u' = H.hilb v (toLoc v a) (toLoc v b) := by
    have h := H.skew v (toLoc v a) u'
    rw [hsymbolb] at h
    have h' := H.skew v (toLoc v a) (toLoc v b)
    exact mul_right_cancel (h.trans h'.symm)
  rw [hsymbola, hright]
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) = 0 := by
    rw [theta_count_spanSingleton_eq_neg_log_valuation v (b : F) b.ne_zero, hvb]
    simp
  have h := H.tame v hv a b ha
  rw [hcount, zpow_zero] at h
  apply rootsOfUnity.coe_injective
  exact h

private theorem unitPart_isLocUnit (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    IsLocUnit v (unitPart v x) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hxv : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
    rw [← WithZero.exp_log hx0]
    simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_exists_uniformizer F).choose_spec
  have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
    simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
    change Valued.v ((x : v.adicCompletion F) *
      (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
    rw [map_mul, map_zpow₀, hxv, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    congr 1
    simp
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hval' : Valued.v (((unitPart v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [hval]
    rw [hval']

private def effectiveMu (D : FieldData F) : rootsOfUnity 6 F →* ℂˣ where
  toFun ζ := (muThree D ζ : ℂˣ)
  map_one' := by
    apply Units.ext
    simp [muThree]
  map_mul' ζ ξ := by
    apply Units.ext
    simp [muThree, mul_pow]

private def effectiveSymbolLeft (H : HilbertData F) (v : FinPlace F)
    (b : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F where
  toFun a := H.hilb v a b
  map_one' := H.sixth_power v 1 b ⟨1, by simp⟩
  map_mul' a a' := H.mul_left v a a' b

private def effectiveSymbolRight (H : HilbertData F) (v : FinPlace F)
    (a : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F where
  toFun b := H.hilb v a b
  map_one' := by
    have h := H.skew v a 1
    rw [H.sixth_power v 1 a ⟨1, by simp⟩, mul_one] at h
    exact h
  map_mul' b b' := H.mul_right v a b b'

private theorem effectiveMu_self (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    effectiveMu D (H.hilb v x x) = 1 := by
  apply Units.ext
  have h := congrArg (fun ζ : rootsOfUnity 6 F => ((ζ : Fˣ) : F)) (H.skew v x x)
  have hsq : (((H.hilb v x x : rootsOfUnity 6 F) : Fˣ) : F) ^ 2 = 1 := by
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one, pow_two] using h
  simpa [effectiveMu, muThree, ← map_pow] using congrArg D.σ0 hsq

/-- The tame local torus cocycle in the frozen exterior coordinates. -/
theorem muThree_hilb_eq_extCocycle (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (x y : (v.adicCompletion F)ˣ) :
    ((muThree D (H.hilb v x y) : ℂˣ) : ℂ) = extCocycle D v x y := by
  let π := unifLoc v
  let e := ordv v x
  let f := ordv v y
  let u := unitPart v x
  let u' := unitPart v y
  have hu : IsLocUnit v u := unitPart_isLocUnit v x
  have hu' : IsLocUnit v u' := unitPart_isLocUnit v y
  have hx : x = π ^ e * u := by
    dsimp [π, e, u, unitPart, unifLoc]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hy : y = π ^ f * u' := by
    dsimp [π, f, u', unitPart, unifLoc]
    simp [mul_comm, mul_left_comm, mul_assoc]
  let μ := effectiveMu D
  have hpp : μ (H.hilb v (π ^ e) (π ^ f)) = 1 := by
    change μ ((effectiveSymbolLeft H v (π ^ f)) (π ^ e)) = 1
    rw [map_zpow, map_zpow]
    change (μ ((effectiveSymbolRight H v π) (π ^ f))) ^ e = 1
    rw [map_zpow, map_zpow]
    change ((effectiveMu D (H.hilb v π π)) ^ f) ^ e = 1
    rw [effectiveMu_self]
    simp
  have hpu : ((μ (H.hilb v (π ^ e) u') : ℂˣ) : ℂ) =
      localChi D v u' ^ (-(2 * e)) := effective_hilb_unif_unit D H v hv e u' hu'
  have hup : ((μ (H.hilb v u (π ^ f)) : ℂˣ) : ℂ) =
      localChi D v u ^ (2 * f) := by
    have hs : μ (H.hilb v u (π ^ f)) = (μ (H.hilb v (π ^ f) u))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, H.skew, map_one]
    have hpu' : ((μ (H.hilb v (π ^ f) u) : ℂˣ) : ℂ) =
        localChi D v u ^ (-(2 * f)) := effective_hilb_unif_unit D H v hv f u hu
    rw [hs, Units.val_inv_eq_inv_val, hpu']
    simp
  have huu : μ (H.hilb v u u') = 1 := by
    rw [effective_hilb_units D H v hv u u' hu hu', map_one]
  have hsplit : μ (H.hilb v x y) =
      μ (H.hilb v (π ^ e) (π ^ f)) * μ (H.hilb v (π ^ e) u') *
      (μ (H.hilb v u (π ^ f)) * μ (H.hilb v u u')) := by
    rw [hx, hy, H.mul_left, H.mul_right, H.mul_right, map_mul, map_mul, map_mul]
  change ((μ (H.hilb v x y) : ℂˣ) : ℂ) = _
  rw [hsplit, hpp, huu, one_mul, mul_one, Units.val_mul, hpu, hup]
  exact mul_comm _ _

end ArtinPrimitiveRoots.Proofs.th_cover_sol
