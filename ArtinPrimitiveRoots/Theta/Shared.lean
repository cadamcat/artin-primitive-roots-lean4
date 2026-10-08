import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import Mathlib.NumberTheory.GaussSum

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance residueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance residueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

/-! Shared declarations used by the local Jacquet packages and P-ANALYSIS-S. -/

open MeasureTheory Filter

private theorem residue_rep_tame (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal) (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
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

private theorem residue_algebraMap_tame (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  simpa using residue_rep_tame v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)

/-- Borel σ-algebra on a completion (Mathlib has no `MeasurableSpace` instance on `adicCompletion`). -/
noncomputable instance instMeasurableSpaceAdicCompletion (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance instBorelSpaceAdicCompletion (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- **def:loc-haar**: the additive Haar measure of `K_v` normalized by `μ(O_v) = 1`. -/
structure LocHaar (v : FinPlace F) where
  μ : Measure (v.adicCompletion F)
  isHaar : μ.IsAddHaarMeasure
  norm_O : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1

attribute [instance] LocHaar.isHaar

section SharedJacquet

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- **jq:localchi**: basic properties of `localChi` on local units at `v ∤ 6`. -/
theorem localChi_basic (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    localChi D v 1 = 1 ∧ localChi D v (-1) = 1 ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' → localChi D v (u * u') = localChi D v u * localChi D v u') ∧
    (∀ u, IsLocUnit v u → localChi D v u ^ 6 = 1) ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' →
      Valued.v ((u : v.adicCompletion F) - u') < 1 → localChi D v u = localChi D v u') := by
  sorry

/-- **jq:hilb-unit** (tame case of P-COVER cov:ext-law): `C(ϖ^e, u) = χ(u)^{-2e}`. -/
theorem muThree_hilb_unif_unit (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e : ℤ) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) :
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) = localChi D v u ^ (-(2 * e)) := by
  sorry

/-- Normalized prime Gauss sums `g_j = q^{-1/2} Σ_{x mod 𝔭} χ(x)^j ψ(x/ϖ)` (10:384–390). -/
def gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (j : ℤ) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) j *
      A.ψ v (algebraMap F _ (algebraMap (𝓞 F) F x.out / unif v))

theorem g2_eq_gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) :
    g2 D A v = gaussLoc D A v 2 := rfl

set_option maxHeartbeats 1000000 in
/-- **jq:gauss-product** (10:391–400): `g_j g_{-j} = 1` for `6 ∤ j` at `v ∤ 6𝔇`. -/
theorem gaussLoc_mul_neg (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (j : ℤ)
    (hj : ¬ (6 : ℤ) ∣ j) : gaussLoc D A v j * gaussLoc D A v (-j) = 1 := by
  classical
  let R := 𝓞 F ⧸ v.asIdeal
  let N := Ideal.absNorm v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype R := Fintype.ofFinite R
  have hcard : Fintype.card R = N := by
    dsimp [R, N]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hnormOne : 1 < N := by
    dsimp [N]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hnormCoprimeSix : N.Coprime 6 := by
    dsimp [N]
    exact (coprime_six_of_not_mem_six v hv).1
  have hnormSubOne : 6 ∣ N - 1 := by
    dsimp [N]
    exact six_dvd_absNorm_sub_one D v hv
  let e : ℕ := (N - 1) / 6
  have hN : N - 1 = 6 * e := by
    dsimp [e]
    have h := Nat.mul_div_cancel' hnormSubOne
    omega
  have hunitCard : Fintype.card Rˣ = N - 1 := by
    rw [Fintype.card_units, hcard]
  letI : NeZero 6 := ⟨by decide⟩
  let hζ6 := D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  let ζ6 : rootsOfUnity 6 (𝓞 F) := hζ6.toInteger_isPrimitiveRoot.toRootsOfUnity
  have hζ6Order : orderOf ζ6 = 6 := by
    refine Eq.trans ?_ hζ6.toInteger_isPrimitiveRoot.eq_orderOf.symm
    rw [← hζ6.toInteger_isPrimitiveRoot.val_toRootsOfUnity_coe,
      orderOf_units, Subgroup.orderOf_coe]
  have hrootsMapInj : Function.Injective (Ideal.rootsOfUnityMapQuot v.asIdeal 6) :=
    Ideal.rootsOfUnityMapQuot_injective 6 (ne_of_gt hnormOne) hnormCoprimeSix
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
  have hcyclic : IsCyclic Rˣ := inferInstance
  obtain ⟨g, hgOrder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Rˣ)
  have hunitCard' : Nat.card Rˣ = N - 1 := by
    calc
      Nat.card Rˣ = Fintype.card Rˣ := Nat.card_eq_fintype_card
      _ = N - 1 := hunitCard
  have hgOrder' : orderOf g = N - 1 := hgOrder.trans hunitCard'
  have hNpos : 0 < N - 1 := by omega
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hNpos hnormSubOne) (by decide)
  have he_dvd : e ∣ N - 1 := by
    refine ⟨6, ?_⟩
    rw [hN]
    ring
  have horderPow : orderOf (g ^ e) = 6 := by
    rw [orderOf_pow, hgOrder', Nat.gcd_eq_right he_dvd, hN]
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left 6 hepos
  have hπval : HeightOneSpectrum.valuation F v (unif v) = WithZero.exp (-1 : ℤ) := by
    dsimp [unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hrootsMapPrimUnits : IsPrimitiveRoot (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) 6 :=
    IsPrimitiveRoot.iff_orderOf.mpr hrootsMapOrder
  have hrootsMapPrim : IsPrimitiveRoot
      ((Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6 : Rˣ) : R) 6 :=
    IsPrimitiveRoot.coe_units_iff.mpr hrootsMapPrimUnits
  have hresAlg (a : 𝓞 F) :
      residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a :=
    residue_algebraMap_tame v a
  have hchiAlgRed (x : Rˣ) :
      Ideal.rootsOfUnityMapQuot v.asIdeal 6
        (chiAlg v (algebraMap (𝓞 F) F (x : R).out)) = x ^ e := by
    have hpowCard : x ^ (N - 1) = 1 := by
      calc
        x ^ (N - 1) = x ^ Nat.card Rˣ := by rw [hunitCard']
        _ = 1 := pow_card_eq_one'
    have hpowUnit : (x ^ e) ^ 6 = 1 := by
      calc
        (x ^ e) ^ 6 = x ^ (e * 6) := by rw [← pow_mul]
        _ = x ^ (N - 1) := by rw [Nat.mul_comm, hN]
        _ = 1 := hpowCard
    have hpowR : (((x ^ e : Rˣ) : R) ^ 6) = 1 := by
      simpa using congrArg (fun z : Rˣ => (z : R)) hpowUnit
    obtain ⟨i, hi, hrootpow⟩ := hrootsMapPrim.eq_pow_of_pow_eq_one hpowR
    let ζpre : rootsOfUnity 6 (𝓞 F) := ζ6 ^ i
    have hrootpreMap : Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre = x ^ e := by
      apply Units.ext
      simpa [ζpre, map_pow, Units.val_pow_eq_pow_val] using hrootpow
    have hquotPre : Ideal.Quotient.mk v.asIdeal ((ζpre : (𝓞 F)ˣ) : 𝓞 F) =
        ((x ^ e : Rˣ) : R) := by
      have h := congrArg (fun u : Rˣ => (u : R)) hrootpreMap
      rw [Ideal.rootsOfUnityMapQuot_apply] at h
      simpa [ζpre, Units.val_pow_eq_pow_val] using h
    have hres : residue v (algebraMap (𝓞 F) F (x : R).out) = (x : R) := by
      simpa [R] using hresAlg (x : R).out
    have hchiAlgExists : ∃ ζ : rootsOfUnity 6 (𝓞 F),
        Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
          residue v (algebraMap (𝓞 F) F (x : R).out) ^
            ((Ideal.absNorm v.asIdeal - 1) / 6) := by
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
  have hchiAlgCongr {x y : F} (h : residue v x = residue v y) :
      chiAlg v x = chiAlg v y := by
    simp only [chiAlg, h]
  have hchiCongr {x y : F} (h : residue v x = residue v y) :
      chi D v x = chi D v y := by
    simp only [chi, chiAlg, h]
  have hresProd (x y : Rˣ) :
      residue v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out)) = (x : R) * (y : R) := by
    rw [residue_algebraMap_tame]
    simp
  have hchiAlgMul (x y : Rˣ) :
      chiAlg v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out)) =
        chiAlg v (algebraMap (𝓞 F) F (x : R).out) *
          chiAlg v (algebraMap (𝓞 F) F (y : R).out) := by
    apply hrootsMapInj
    calc
      Ideal.rootsOfUnityMapQuot v.asIdeal 6
          (chiAlg v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out))) =
          (x * y) ^ e := by
            have hres : residue v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out)) =
                (x * y : R) := by simpa using hresProd x y
            have hresRep : residue v (algebraMap (𝓞 F) F ((x * y : R).out)) =
                (x * y : R) := by
              rw [residue_algebraMap_tame]
              simp
            have hchiAlgRep := hchiAlgCongr (hres.trans hresRep.symm)
            rw [hchiAlgRep]
            exact hchiAlgRed (x * y)
      _ = x ^ e * y ^ e := by rw [mul_pow]
      _ = Ideal.rootsOfUnityMapQuot v.asIdeal 6
          (chiAlg v (algebraMap (𝓞 F) F (x : R).out) *
            chiAlg v (algebraMap (𝓞 F) F (y : R).out)) := by
          rw [map_mul, hchiAlgRed x, hchiAlgRed y]
  have hchiMul (x y : Rˣ) :
      chi D v (algebraMap (𝓞 F) F ((x * y : Rˣ).val.out)) =
        chi D v (algebraMap (𝓞 F) F (x : R).out) *
          chi D v (algebraMap (𝓞 F) F (y : R).out) := by
    have hresXY : residue v (algebraMap (𝓞 F) F ((x * y : Rˣ).val.out)) =
        (x : R) * (y : R) := by
      rw [residue_algebraMap_tame]
      simp
    have hresX : residue v (algebraMap (𝓞 F) F (x : R).out) ≠ 0 := by
      simpa [residue_algebraMap_tame] using x.ne_zero
    have hresY : residue v (algebraMap (𝓞 F) F (y : R).out) ≠ 0 := by
      simpa [residue_algebraMap_tame] using y.ne_zero
    have hresXYne : residue v (algebraMap (𝓞 F) F ((x * y : Rˣ).val.out)) ≠ 0 := by
      rw [hresXY]
      exact mul_ne_zero x.ne_zero y.ne_zero
    have hresProdNe : residue v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out)) ≠ 0 := by
      rw [hresProd]
      exact mul_ne_zero x.ne_zero y.ne_zero
    calc
      chi D v (algebraMap (𝓞 F) F ((x * y : Rˣ).val.out)) =
          chi D v (algebraMap (𝓞 F) F ((x : R).out * (y : R).out)) := by
            apply hchiCongr
            rw [hresXY, hresProd]
      _ = chi D v (algebraMap (𝓞 F) F (x : R).out) *
          chi D v (algebraMap (𝓞 F) F (y : R).out) := by
        unfold chi
        rw [if_neg hresProdNe, if_neg hresX, if_neg hresY, hchiAlgMul]
        simp [map_mul]
  have hchiNonzero (x : Rˣ) :
      chi D v (algebraMap (𝓞 F) F (x : R).out) ≠ 0 := by
    have hres : residue v (algebraMap (𝓞 F) F (x : R).out) ≠ 0 := by
      rw [residue_algebraMap_tame]
      simpa using x.ne_zero
    unfold chi
    rw [if_neg hres]
    intro h
    have h₀ : D.σ0 (algebraMap (𝓞 F) F
        ((chiAlg v (algebraMap (𝓞 F) F (x : R).out) : (𝓞 F)ˣ) : 𝓞 F)) = D.σ0 0 := by
      simpa only [map_zero] using h
    have h₁ : algebraMap (𝓞 F) F
        ((chiAlg v (algebraMap (𝓞 F) F (x : R).out) : (𝓞 F)ˣ) : 𝓞 F) = 0 :=
      (RingHom.injective D.σ0) h₀
    have h₂ : ((chiAlg v (algebraMap (𝓞 F) F (x : R).out) : (𝓞 F)ˣ) : 𝓞 F) = 0 :=
      (IsFractionRing.injective (𝓞 F) F) h₁
    exact Units.ne_zero _ h₂
  have hchiOne : chi D v (algebraMap (𝓞 F) F ((1 : R).out)) = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F ((1 : R).out)) = 1 := by
      rw [hresAlg]
      simp
    have hroot : chiAlg v (algebraMap (𝓞 F) F ((1 : R).out)) = 1 := by
      apply hrootsMapInj
      have hred := hchiAlgRed (1 : Rˣ)
      simpa using hred
    simp [chi, hres, hroot]
  let chiUnit : Rˣ →* ℂˣ := {
    toFun := fun x => Units.mk0 (chi D v (algebraMap (𝓞 F) F (x : R).out)) (hchiNonzero x)
    map_one' := by
      apply Units.ext
      exact hchiOne
    map_mul' := by
      intro x y
      apply Units.ext
      exact hchiMul x y
  }
  let chiChar : MulChar R ℂ := MulChar.ofUnitHom chiUnit
  have hchiCharUnit (x : Rˣ) : chiChar (x : R) = chi D v (algebraMap (𝓞 F) F (x : R).out) := by
    change MulChar.ofUnitHom chiUnit (x : R) = _
    rw [MulChar.ofUnitHom_coe]
    rfl
  have hchiCharApply (x : R) :
      chiChar x = chiPow D v (algebraMap (𝓞 F) F x.out) 1 := by
    by_cases hx : IsUnit x
    · rw [← hx.unit_spec]
      let u := hx.unit
      have hres : residue v (algebraMap (𝓞 F) F (u : R).out) ≠ 0 := by
        rw [residue_algebraMap_tame]
        simpa using u.ne_zero
      calc
        chiChar (u : R) = chi D v (algebraMap (𝓞 F) F (u : R).out) := hchiCharUnit u
        _ = chiPow D v (algebraMap (𝓞 F) F (u : R).out) 1 := by
          simp [chiPow, hres]
    · have hx0 : x = 0 := by
        by_contra hn
        exact hx (isUnit_iff_ne_zero.mpr hn)
      subst x
      rw [MulChar.map_nonunit chiChar (by simp)]
      simp [chiPow, hresAlg]
  have hchiSix (x : Rˣ) :
      chi D v (algebraMap (𝓞 F) F (x : R).out) ^ (6 : ℕ) = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F (x : R).out) ≠ 0 := by
      rw [residue_algebraMap_tame]
      simpa using x.ne_zero
    have hroot : (((chiAlg v (algebraMap (𝓞 F) F (x : R).out) : (𝓞 F)ˣ) : 𝓞 F) ^ 6) = 1 := by
      have h := (mem_rootsOfUnity 6
        (chiAlg v (algebraMap (𝓞 F) F (x : R).out) : (𝓞 F)ˣ)).1
        (chiAlg v (algebraMap (𝓞 F) F (x : R).out)).property
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun z : (𝓞 F)ˣ => (z : 𝓞 F)) h
    unfold chi
    rw [if_neg hres, ← map_pow, ← map_pow]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using
      congrArg (fun a : 𝓞 F => D.σ0 (algebraMap (𝓞 F) F a)) hroot
  have hchiCharSix : chiChar ^ (6 : ℕ) = 1 := by
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hchiCharUnit]
    exact hchiSix x
  have hchiCharGen : orderOf (chiUnit g) = 6 := by
    have hunitRootOrder : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6
        (chiAlg v (algebraMap (𝓞 F) F (g : R).out))) = 6 := by
      rw [hchiAlgRed, horderPow]
    have hrootPow : (chiAlg v (algebraMap (𝓞 F) F (g : R).out)) ^ 6 = 1 := by
      apply hrootsMapInj
      rw [map_pow, hchiAlgRed]
      rw [map_one]
      simpa [horderPow] using pow_orderOf_eq_one (g ^ e)
    have hrootOrder : orderOf (chiAlg v (algebraMap (𝓞 F) F (g : R).out)) = 6 := by
      apply Nat.dvd_antisymm
      · have := orderOf_dvd_of_pow_eq_one hrootPow
        exact this
      · have := orderOf_map_dvd (Ideal.rootsOfUnityMapQuot v.asIdeal 6)
          (chiAlg v (algebraMap (𝓞 F) F (g : R).out))
        rw [hunitRootOrder] at this
        exact this
    let evalRoot : rootsOfUnity 6 (𝓞 F) →* ℂˣ :=
      (Units.map (D.σ0.comp (algebraMap (𝓞 F) F))).comp
        (rootsOfUnity 6 (𝓞 F)).subtype
    have hcompInj : Function.Injective (D.σ0.comp (algebraMap (𝓞 F) F)) :=
      (RingHom.injective D.σ0).comp (IsFractionRing.injective (𝓞 F) F)
    have hevalInj : Function.Injective
        (evalRoot) := by
      intro ζ ζ' h
      apply Subtype.ext
      apply Units.ext
      apply hcompInj
      simpa [evalRoot] using congrArg (fun z : ℂˣ => (z : ℂ)) h
    have hrootPrim := IsPrimitiveRoot.iff_orderOf.mpr hrootOrder
    have hevalPrim := hrootPrim.map_of_injective (f := evalRoot) hevalInj
    have hEval : chiUnit g = evalRoot (chiAlg v (algebraMap (𝓞 F) F (g : R).out)) := by
      apply Units.ext
      have hres : residue v (algebraMap (𝓞 F) F (g : R).out) ≠ 0 := by
        rw [residue_algebraMap_tame]
        simpa using g.ne_zero
      simp [chiUnit, chi, hres, evalRoot]
    rw [hEval]
    exact hevalPrim.eq_orderOf.symm
  have hchiCharOrder : orderOf chiChar = 6 := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one hchiCharSix
    · have hpow := pow_orderOf_eq_one chiChar
      have hgen : (chiChar (g : R)) ^ orderOf chiChar = 1 := by
        have h := congrArg (fun χ : MulChar R ℂ => χ (g : R)) hpow
        simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
      have hunitPow : (chiUnit g) ^ orderOf chiChar = 1 := by
        apply Units.ext
        have hunitVal : (chiUnit g : ℂ) = chiChar (g : R) := by
          rw [hchiCharUnit]
          rfl
        rw [Units.val_pow_eq_pow_val, Units.val_one, hunitVal]
        exact hgen
      rw [← hchiCharGen]
      exact orderOf_dvd_of_pow_eq_one hunitPow
  have hchiPowers (k : ℤ) (x : R) :
      (chiChar ^ k) x = chiPow D v (algebraMap (𝓞 F) F x.out) k := by
    by_cases hx : IsUnit x
    · rw [← hx.unit_spec]
      let u := hx.unit
      have hu : residue v (algebraMap (𝓞 F) F (u : R).out) ≠ 0 := by
        rw [residue_algebraMap_tame]
        simpa using u.ne_zero
      calc
        (chiChar ^ k) (u : R) = chiChar (u ^ k : Rˣ) :=
          MulChar.zpow_apply_coe chiChar k u
        _ = chiChar u ^ k := by
          have h := chiChar.toUnitHom.map_zpow u k
          calc
            chiChar (u ^ k : Rˣ) = (chiChar.toUnitHom (u ^ k) : ℂ) :=
              (MulChar.coe_toUnitHom chiChar (u ^ k)).symm
            _ = ((chiChar.toUnitHom u : ℂ) ^ k) := by
              simpa only [Units.val_zpow_eq_zpow_val] using congrArg Units.val h
            _ = chiChar u ^ k := by rw [MulChar.coe_toUnitHom]
        _ = chiPow D v (algebraMap (𝓞 F) F (u : R).out) 1 ^ k := by
          rw [hchiCharApply]
        _ = chiPow D v (algebraMap (𝓞 F) F (u : R).out) k := by
          simp [chiPow, hu, chi]
    · have hx0 : x = 0 := by
        by_contra hn
        exact hx (isUnit_iff_ne_zero.mpr hn)
      subst x
      rw [MulChar.map_nonunit (chiChar ^ k) (by simp)]
      simp [chiPow, hresAlg]
  have hdivO (a : 𝓞 F) (ha : a ∈ v.asIdeal) :
      algebraMap F (v.adicCompletion F) ((a : F) / unif v) ∈ v.adicCompletionIntegers F := by
    have hvalNum : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) ≤
        WithZero.exp (-1 : ℤ) := by
      change v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-1 : ℤ)
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem a 1).2
      simpa using ha
    have hvalDiv : HeightOneSpectrum.valuation F v ((a : F) / unif v) ≤ 1 := by
      rw [map_div₀, hπval]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hvalNum
    change ((((a : F) / unif v : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hvalDiv
  have hphaseErr (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v)) = 1 := by
    have hvalNum : HeightOneSpectrum.valuation F v ((a : F) - b) ≤ WithZero.exp (-1 : ℤ) := by
      change v.valuation F (algebraMap (𝓞 F) F (a - b)) ≤ WithZero.exp (-1 : ℤ)
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (a - b) 1).2
      simpa using hab
    have hvalDiv : HeightOneSpectrum.valuation F v (((a : F) - b) / unif v) ≤ 1 := by
      rw [map_div₀, hπval]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hvalNum
    have hlocal : algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v) ∈
        v.adicCompletionIntegers F := by
      change ((((a : F) - b) / unif v : F) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    exact A.integral v _ hlocal
  have hphaseCongr (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) =
        A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) := by
    have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v) =
        algebraMap F (v.adicCompletion F) ((a : F) / unif v) -
          algebraMap F (v.adicCompletion F) ((b : F) / unif v) := by
      have hF : ((a : F) - b) / unif v = (a : F) / unif v - (b : F) / unif v := by
        field_simp [unif_ne_zero v]
      rw [hF, map_sub]
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) ((a : F) / unif v))
      (algebraMap F (v.adicCompletion F) ((b : F) / unif v))
    have hbne : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) ((b : F) / unif v))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) =
          (A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) /
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v))) *
              A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) :=
        (div_mul_cancel₀ _ hbne).symm
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / unif v)) *
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) := by
        rw [hphaseErr a b hab, one_mul]
  have hrepAdd (x y : R) : (x + y).out - (x.out + y.out) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, Ideal.Quotient.mk_out]
    simp [map_add]
  let ψfun : R → ℂ := fun x =>
    A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v))
  have hψzero : ψfun 0 = 1 := by
    have hmem : (0 : R).out ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp
    calc
      ψfun 0 = A.ψ v (algebraMap F (v.adicCompletion F)
          (((0 : R).out : F) / unif v)) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (0 / unif v)) :=
        hphaseCongr (0 : R).out 0 (by simpa using hmem)
      _ = 1 := by simp
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
      ψfun (x + y) = A.ψ v (algebraMap F (v.adicCompletion F)
          (((x + y).out : F) / unif v)) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          (((x.out + y.out : 𝓞 F) : F) / unif v)) :=
        hphaseCongr (x + y).out (x.out + y.out) (hrepAdd x y)
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v) +
            algebraMap F (v.adicCompletion F) (y.out / unif v)) := by
        rw [show ((x.out + y.out : 𝓞 F) : F) = (x.out : F) + y.out by norm_cast, harg]
      _ = ψfun x * ψfun y := (A.ψ v).map_add_eq_mul _ _
  let ψR : AddChar R ℂ :=
    { toFun := ψfun, map_zero_eq_one' := hψzero, map_add_eq_mul' := hψadd }
  have hψApply (x : R) :
      ψR x = A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / unif v)) := rfl
  rcases A.unramified v hd with ⟨_, hnontriv⟩
  obtain ⟨a, hψa⟩ := hnontriv (unif v) hπval
  have hψNe : ψR ≠ 1 := by
    intro h
    have hphase : ψR (Ideal.Quotient.mk v.asIdeal a) =
        A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) := by
      rw [hψApply]
      exact hphaseCongr (Ideal.Quotient.mk v.asIdeal a).out a (by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, Ideal.Quotient.mk_out]
        simp)
    have hval : ψR (Ideal.Quotient.mk v.asIdeal a) = 1 := by
      rw [h]
      simp
    apply hψa
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) =
          ψR (Ideal.Quotient.mk v.asIdeal a) := hphase.symm
      _ = 1 := hval
  have hψprim : ψR.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψNe
  have hχminus : chiChar (-1 : R) = 1 := by
    have hcop12 : N.Coprime 12 := by
      apply Nat.coprime_of_dvd
      intro k hkPrime hkN hk12
      have hcopk6 : k.Coprime 6 := Nat.Coprime.of_dvd_left hkN hnormCoprimeSix
      have hk6 : k ∣ 6 := by
        have hkprod : k ∣ 3 * 4 := by simpa using hk12
        rcases (Nat.Prime.dvd_mul hkPrime).mp hkprod with hk3 | hk4
        · exact dvd_mul_of_dvd_left hk3 2
        · have hk4' : k ∣ 2 ^ 2 := by simpa using hk4
          have hk2 : k ∣ 2 := Nat.Prime.dvd_of_dvd_pow hkPrime hk4'
          exact dvd_mul_of_dvd_right hk2 3
      exact (Nat.Prime.coprime_iff_not_dvd hkPrime).mp hcopk6 hk6
    have hrootsMapInj12 : Function.Injective (Ideal.rootsOfUnityMapQuot v.asIdeal 12) :=
      Ideal.rootsOfUnityMapQuot_injective 12 (ne_of_gt hnormOne) hcop12
    let ζ12 : rootsOfUnity 12 (𝓞 F) := D.hζ12.toInteger_isPrimitiveRoot.toRootsOfUnity
    have hζ12Order : orderOf ζ12 = 12 := by
      refine Eq.trans ?_ D.hζ12.toInteger_isPrimitiveRoot.eq_orderOf.symm
      rw [← D.hζ12.toInteger_isPrimitiveRoot.val_toRootsOfUnity_coe,
        orderOf_units, Subgroup.orderOf_coe]
    have hrootsMapOrder12 : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12) = 12 := by
      apply Nat.dvd_antisymm
      · calc
          orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12) ∣ orderOf ζ12 :=
            orderOf_map_dvd _ _
          _ = 12 := hζ12Order
      · have hpow := pow_orderOf_eq_one (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12)
        have hmap : Ideal.rootsOfUnityMapQuot v.asIdeal 12
            (ζ12 ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12)) =
              Ideal.rootsOfUnityMapQuot v.asIdeal 12 1 := by
          rw [map_pow, hpow, map_one]
        have hpow' : ζ12 ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12) = 1 :=
          hrootsMapInj12 hmap
        simpa [hζ12Order] using orderOf_dvd_of_pow_eq_one hpow'
    have h12dvd : 12 ∣ N - 1 := by
      have horderDiv : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 12 ζ12) ∣
          Fintype.card Rˣ := orderOf_dvd_card
      rw [hrootsMapOrder12, hunitCard] at horderDiv
      exact horderDiv
    have heven : Even e := by
      obtain ⟨k, hk⟩ := h12dvd
      refine ⟨k, ?_⟩
      rw [hN] at hk
      omega
    have hneg : ((-1 : Rˣ) ^ e) = 1 := by
      simpa [Even.neg_one_pow heven]
    let m : Rˣ := -1
    have hresTarget : residue v (algebraMap (𝓞 F) F ((-1 : R).out)) = (-1 : R) := by
      rw [residue_algebraMap_tame]
      simp
    have hresUnit : residue v (algebraMap (𝓞 F) F (m : R).out) = (-1 : R) := by
      rw [residue_algebraMap_tame]
      simp [m]
    have hχrootUnit : chiAlg v (algebraMap (𝓞 F) F (m : R).out) = 1 := by
      apply hrootsMapInj
      rw [hchiAlgRed m, hneg, map_one]
    have hχroot : chiAlg v (algebraMap (𝓞 F) F ((-1 : R).out)) = 1 :=
      (hchiAlgCongr (hresTarget.trans hresUnit.symm)).trans hχrootUnit
    rw [hchiCharApply]
    have hresNe : residue v (algebraMap (𝓞 F) F ((-1 : R).out)) ≠ 0 := by
      rw [residue_algebraMap_tame]
      norm_num
    simp [chiPow, chi, hresNe, hχroot]
  have hchiMinusPow (k : ℤ) : (chiChar ^ k) (-1 : R) = 1 := by
    let m : Rˣ := -1
    change (chiChar ^ k) (m : R) = 1
    have hunit : chiChar.toUnitHom m = 1 := by
      apply Units.ext
      change chiChar (m : R) = 1
      simpa [m] using hχminus
    have hmap := chiChar.toUnitHom.map_zpow m k
    have hpow : chiChar.toUnitHom (m ^ k) = 1 := by
      rw [hmap, hunit]
      simp
    calc
      (chiChar ^ k) (m : R) = chiChar ((m ^ k : Rˣ) : R) :=
        MulChar.zpow_apply_coe chiChar k m
      _ = (chiChar.toUnitHom (m ^ k) : ℂ) :=
        (MulChar.coe_toUnitHom chiChar _).symm
      _ = 1 := by rw [hpow]; simp
  have hgauss (k : ℤ) : gaussLoc D A v k =
      (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum (chiChar ^ k) ψR := by
    unfold gaussLoc
    have hfinsum (f : R → ℂ) : (∑ᶠ x : R, f x) = ∑ x : R, f x :=
      finsum_eq_sum_of_fintype f
    rw [hfinsum]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [hchiPowers k x, hψApply x]
  have hchiNe : chiChar ^ j ≠ 1 := by
    intro h
    have hdvd : (orderOf chiChar : ℤ) ∣ j := by
      rw [orderOf_dvd_iff_zpow_eq_one]
      exact h
    rw [hchiCharOrder] at hdvd
    exact hj hdvd
  have hψsame : gaussSum ((chiChar ^ j)⁻¹) ψR⁻¹ =
      gaussSum ((chiChar ^ j)⁻¹) ψR := by
    have h := mul_gaussSum_inv_eq_gaussSum ((chiChar ^ j)⁻¹) ψR
    have hminus : ((chiChar ^ j)⁻¹) (-1 : R) = 1 := by
      simp [MulChar.inv_apply', hchiMinusPow]
    rw [hminus, one_mul] at h
    exact h
  have hprod : gaussSum (chiChar ^ j) ψR *
      gaussSum ((chiChar ^ j)⁻¹) ψR = Fintype.card R := by
    calc
      gaussSum (chiChar ^ j) ψR * gaussSum ((chiChar ^ j)⁻¹) ψR =
          gaussSum (chiChar ^ j) ψR * gaussSum ((chiChar ^ j)⁻¹) ψR⁻¹ := by
            rw [hψsame.symm]
      _ = Fintype.card R := gaussSum_mul_gaussSum_eq_card hchiNe hψprim
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnormOne)
  have hscale : (((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) * (N : ℝ) = 1 := by
    have hpow : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
      calc
        ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 =
            ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by rw [Real.rpow_two]
        _ = (N : ℝ) ^ ((-(1 / 2 : ℝ)) * 2) := by rw [← Real.rpow_mul hNreal.le]
        _ = (N : ℝ) ^ (-1 : ℝ) := by norm_num
        _ = (N : ℝ)⁻¹ := Real.rpow_neg_one _
    rw [hpow]
    field_simp [ne_of_gt hNreal]
  have hscaleC :
      ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ 2) * (Fintype.card R : ℂ) = 1 := by
    rw [hcard]
    exact_mod_cast hscale
  have hpowerInv : chiChar ^ (-j) = (chiChar ^ j)⁻¹ := by
    rw [zpow_neg]
  rw [hgauss j, hgauss (-j), hpowerInv]
  calc
    ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum (chiChar ^ j) ψR) *
        ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          gaussSum ((chiChar ^ j)⁻¹) ψR) =
        ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ 2) *
          (gaussSum (chiChar ^ j) ψR * gaussSum ((chiChar ^ j)⁻¹) ψR) := by ring
    _ = ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ 2) * (Fintype.card R : ℂ) := by
      rw [hprod]
    _ = 1 := hscaleC

/-- **jq:bessel-bridge**: the frozen `besselK` (cosh form) equals Schläfli's form. -/
theorem besselK_eq_schlafli (ν x : ℝ) (hx : 0 < x) :
    besselK ν x = 1 / 2 * (x / 2) ^ (-ν) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  sorry

end SharedJacquet

end ArtinPrimitiveRoots.A1.Theta
