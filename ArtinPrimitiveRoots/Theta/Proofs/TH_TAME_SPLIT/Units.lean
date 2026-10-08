import ArtinPrimitiveRoots.A1.ThetaInterface
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.thsol_tame
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- The local units, in a module that can be imported before `Cover`. -/
def LocalUnit (v : FinPlace F) (u : (v.adicCompletion F)ˣ) : Prop :=
  (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F

local instance residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem local_unit_approximant (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
    (hu : LocalUnit v u) :
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

/-- A local unit is a global integral unit modulo a local sixth power. -/
theorem local_unit_sixth_approx (v : FinPlace F) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (u : (v.adicCompletion F)ˣ) (hu : LocalUnit v u) :
    ∃ (a : 𝓞 F) (ha : (a : F) ≠ 0), a ∉ v.asIdeal ∧
      ∃ r : (v.adicCompletion F)ˣ,
        u = toLoc v (Units.mk0 (a : F) ha) * r ^ 6 := by
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
  refine ⟨a, a₀.ne_zero, ha, cLoc, ?_⟩
  change u = aLoc * cLoc ^ 6
  calc
    u = rLoc * aLoc := hfactor.symm
    _ = aLoc * cLoc ^ 6 := by rw [hcLoc]; exact mul_comm _ _

private theorem residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
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

private theorem residue_algInt (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  have h := residue_rep v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  simpa using h

private lemma count_spanSingleton_int (v : FinPlace F)
    (a : 𝓞 F) (ha : a ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F a)) = -WithZero.log (v.intValuation a) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg ha, WithZero.log_exp]
  ring

private theorem hilb_sixth_right (H : HilbertData F) (v : FinPlace F)
    (a c : (v.adicCompletion F)ˣ) : H.hilb v a (c ^ 6) = 1 := by
  have h := H.skew v a (c ^ 6)
  rw [H.sixth_power v (c ^ 6) a ⟨c, rfl⟩, mul_one] at h
  exact h

/-- At a tame place the sextic Hilbert symbol of two local units is trivial. -/
theorem hilb_local_units (H : HilbertData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (u u' : (v.adicCompletion F)ˣ) (hu : LocalUnit v u) (hu' : LocalUnit v u') :
    H.hilb v u u' = 1 := by
  obtain ⟨a, ha, hpa, r, hur⟩ := local_unit_sixth_approx v hv u hu
  obtain ⟨b, hb, hpb, s, hus⟩ := local_unit_sixth_approx v hv u' hu'
  let aU : Fˣ := Units.mk0 (a : F) ha
  let bU : Fˣ := Units.mk0 (b : F) hb
  have hres : residue v (aU : F) ≠ 0 := by
    change residue v (algebraMap (𝓞 F) F a) ≠ 0
    rw [residue_algInt]
    exact fun h => hpa ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  have hb0 : b ≠ 0 := by
    intro h
    apply hb
    rw [h]
    simp
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (bU : F)) = 0 := by
    change FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F b)) = 0
    rw [count_spanSingleton_int v b hb0,
      HeightOneSpectrum.intValuation_eq_one_iff.mpr hpb]
    simp
  have htame := H.tame v hv aU bU hres
  rw [hcount, zpow_zero] at htame
  have hglobal : H.hilb v (toLoc v aU) (toLoc v bU) = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact htame
  calc
    H.hilb v u u' = H.hilb v (toLoc v aU) u' := by
      rw [hur, H.mul_left, H.sixth_power v (r ^ 6) u' ⟨r, rfl⟩, mul_one]
    _ = H.hilb v (toLoc v aU) (toLoc v bU) := by
      rw [hus, H.mul_right, hilb_sixth_right H v (toLoc v aU) s, mul_one]
    _ = 1 := hglobal

end ArtinPrimitiveRoots.Proofs.thsol_tame
