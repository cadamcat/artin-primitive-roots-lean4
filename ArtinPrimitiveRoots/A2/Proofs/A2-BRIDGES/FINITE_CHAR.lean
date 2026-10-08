import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SYMBOL

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma bridge_count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma bridge_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma bridge_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
    bridge_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    bridge_count_spanSingleton_eq_neg_log_intValuation v n hn,
    bridge_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

/-- Construct the actual residue multiplicative characters and primitive additive phase.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses SYMBOL and AddCharData.unramified.
Power zero is the unit mask because the target is MulChar. -/
theorem a2_bridge_FINITE_CHAR (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    letI := bridgeResidueField v
    letI := bridgeResidueFintype v
    (∀ j : ℤ, ∃ χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ,
      ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) j) ∧
    (∃ χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ, orderOf χ = 6 ∧
      ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 1) ∧
    (∃ ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ, ψ.IsPrimitive ∧
      ∀ t x, ψ (t * x) = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F t.out / (p : F)))) := by
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  classical
  let SB := a2_bridge_SYMBOL D S
  have hresAlg (x : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hresProd (x y : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F y.out) =
        residue v (algebraMap (𝓞 F) F x.out) * residue v (algebraMap (𝓞 F) F y.out) := by
    rw [← map_mul (algebraMap (𝓞 F) F), SB.residue_algebraMap, SB.residue_algebraMap,
      SB.residue_algebraMap]
    simp
  have hresMul (x y : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F (x * y).out) =
        residue v (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F y.out) := by
    calc
      residue v (algebraMap (𝓞 F) F (x * y).out) = x * y := hresAlg (x * y)
      _ = residue v (algebraMap (𝓞 F) F x.out) *
          residue v (algebraMap (𝓞 F) F y.out) := by rw [hresAlg x, hresAlg y]
      _ = residue v (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F y.out) :=
        (hresProd x y).symm
  have hchiPowMul (x y : 𝓞 F ⧸ v.asIdeal) :
      chiPow D v (algebraMap (𝓞 F) F (x * y).out) 1 =
        chiPow D v (algebraMap (𝓞 F) F x.out) 1 *
          chiPow D v (algebraMap (𝓞 F) F y.out) 1 := by
    let hgx : F := algebraMap (𝓞 F) F x.out
    let hgy : F := algebraMap (𝓞 F) F y.out
    have hχcongr : chi D v (algebraMap (𝓞 F) F (x * y).out) = chi D v (hgx * hgy) := by
      apply SB.chi_congr
      simpa [hgx, hgy] using hresMul x y
    have hresx : residue v hgx = x := by simpa [hgx] using hresAlg x
    have hresy : residue v hgy = y := by simpa [hgy] using hresAlg y
    have hresxy : residue v (hgx * hgy) = x * y := by
      calc
        residue v (hgx * hgy) = residue v hgx * residue v hgy := by
          simpa [hgx, hgy] using hresProd x y
        _ = x * y := by rw [hresx, hresy]
    unfold chiPow
    rw [hresMul x y, hresProd x y, hresAlg x, hresAlg y]
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hy : y = 0
      · simp [hy]
      · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        rw [if_neg hxy, if_neg hx, if_neg hy, hχcongr]
        rw [SB.chi_mul v hv hgx hgy (v.valuation_le_one x.out) (v.valuation_le_one y.out)]
        simp [hgx, hgy]
  have hchiPowUnit_ne_zero (x : (𝓞 F ⧸ v.asIdeal)ˣ) :
      chiPow D v (algebraMap (𝓞 F) F (x : 𝓞 F ⧸ v.asIdeal).out) 1 ≠ 0 := by
    have hx : residue v (algebraMap (𝓞 F) F (x : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact x.ne_zero
    have hnorm := SB.chi_norm v _ hx
    have hχne : chi D v (algebraMap (𝓞 F) F (x : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hnorm]
      norm_num
    rw [SB.chiPow_nonzero v _ 1 hx]
    simpa [pow_one] using hχne
  have hresOne : residue v (1 : F) = 1 := by
    have h := SB.residue_algebraMap v (1 : 𝓞 F)
    simpa using h
  have hchiOne : chi D v (1 : F) = 1 := by
    have hres : residue v (1 : F) ≠ 0 := by rw [hresOne]; exact one_ne_zero
    have hnorm := SB.chi_norm v (1 : F) hres
    have hne : chi D v (1 : F) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hnorm]
      norm_num
    have hmul := SB.chi_mul v hv (1 : F) 1
      (v.valuation_le_one (1 : 𝓞 F)) (v.valuation_le_one (1 : 𝓞 F))
    have hmul' : chi D v (1 : F) * 1 = chi D v (1 : F) * chi D v (1 : F) := by
      simpa using hmul
    exact (mul_left_cancel₀ hne hmul').symm
  have hchiPowOne : chiPow D v (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) 1 = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact one_ne_zero
    have hchiRep : chi D v (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) = 1 := by
      calc
        chi D v (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) = chi D v 1 :=
          SB.chi_congr v _ _ ((hresAlg 1).trans hresOne.symm)
        _ = 1 := hchiOne
    rw [SB.chiPow_nonzero v _ 1 hres]
    simpa [pow_one] using hchiRep
  let chiUnit : (𝓞 F ⧸ v.asIdeal)ˣ →* ℂˣ := {
    toFun := fun x => Units.mk0
      (chiPow D v (algebraMap (𝓞 F) F (x : 𝓞 F ⧸ v.asIdeal).out) 1)
      (hchiPowUnit_ne_zero x)
    map_one' := by
      apply Units.ext
      exact hchiPowOne
    map_mul' := by
      intro x y
      apply Units.ext
      exact hchiPowMul x y }
  let chiChar : MulChar (𝓞 F ⧸ v.asIdeal) ℂ := MulChar.ofUnitHom chiUnit
  have hchiChar (x : 𝓞 F ⧸ v.asIdeal) :
      chiChar x = chiPow D v (algebraMap (𝓞 F) F x.out) 1 := by
    by_cases hx : IsUnit x
    · rw [← hx.unit_spec]
      change MulChar.ofUnitHom chiUnit (hx.unit : 𝓞 F ⧸ v.asIdeal) = _
      rw [MulChar.ofUnitHom_coe]
      rfl
    · have hx0 : x = 0 := by
        by_contra hn
        exact hx (isUnit_iff_ne_zero.mpr hn)
      subst x
      rw [MulChar.map_nonunit chiChar (by simp)]
      have hz : residue v (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ v.asIdeal).out) = 0 := by
        exact hresAlg 0
      exact (SB.chiPow_zero v _ 1 hz).symm
  have hchars : ∀ j : ℤ, ∃ χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ,
      ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) j := by
    intro j
    refine ⟨chiChar ^ j, ?_⟩
    intro x
    by_cases hx : IsUnit x
    · rw [← hx.unit_spec]
      let u := hx.unit
      have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresAlg]
        exact u.ne_zero
      calc
        (chiChar ^ j) (u : 𝓞 F ⧸ v.asIdeal) = chiChar (u ^ j : (𝓞 F ⧸ v.asIdeal)ˣ) :=
          MulChar.zpow_apply_coe chiChar j u
        _ = chiChar u ^ j := by
          have h := chiChar.toUnitHom.map_zpow u j
          calc
            chiChar (u ^ j : (𝓞 F ⧸ v.asIdeal)ˣ) =
                (chiChar.toUnitHom (u ^ j) : ℂ) :=
              (MulChar.coe_toUnitHom chiChar (u ^ j)).symm
            _ = ((chiChar.toUnitHom u : ℂ) ^ j) := by
              simpa only [Units.val_zpow_eq_zpow_val] using congrArg Units.val h
            _ = chiChar u ^ j := by rw [MulChar.coe_toUnitHom]
        _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 ^ j := by
          rw [hchiChar]
        _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) j := by
          calc
            chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 ^ j =
                (chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ 1) ^ j :=
              congrArg (fun z : ℂ => z ^ j) (SB.chiPow_nonzero v _ 1 hu)
            _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ j := by simp
            _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) j :=
              (SB.chiPow_nonzero v _ j hu).symm
    · have hx0 : x = 0 := by
        by_contra hn
        exact hx (isUnit_iff_ne_zero.mpr hn)
      subst x
      rw [MulChar.map_nonunit (chiChar ^ j) (by simp)]
      have hz : residue v (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ v.asIdeal).out) = 0 := by
        exact hresAlg 0
      exact (SB.chiPow_zero v _ j hz).symm
  have hcardNat : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hnormOne : 1 < Ideal.absNorm v.asIdeal := by
    have hcard : 1 < Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      Fintype.one_lt_card_iff.mpr ⟨0, 1, zero_ne_one⟩
    rw [hcardNat] at hcard
    exact hcard
  have hnormCoprimeSix : Nat.Coprime (Ideal.absNorm v.asIdeal) 6 := by
    have hsixNotMem : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
    let p0 : ℕ := Ideal.absNorm (v.asIdeal.under ℤ)
    have hp0 : p0.Prime := by
      dsimp [p0]
      exact Nat.absNorm_under_prime v.asIdeal
    have hnormFactor : p0 ^ v.asIdeal.inertiaDeg ℤ = Ideal.absNorm v.asIdeal := by
      simpa [p0] using Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
    have hp0_not_dvd : ¬p0 ∣ 6 := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      have hp0_mem : (p0 : 𝓞 F) ∈ v.asIdeal := by
        simpa [p0] using Int.absNorm_under_mem v.asIdeal
      have h6_mem : (6 : 𝓞 F) ∈ v.asIdeal := by
        have hcast : (6 : 𝓞 F) = (p0 : 𝓞 F) * k := by exact_mod_cast hk
        rw [hcast]
        exact Ideal.mul_mem_right _ _ hp0_mem
      exact hsixNotMem h6_mem
    have hp0_coprime : Nat.Coprime p0 6 :=
      (Nat.Prime.coprime_iff_not_dvd hp0).2 hp0_not_dvd
    rw [← hnormFactor, Nat.coprime_pow_left_iff (v.asIdeal.inertiaDeg_pos ℤ)]
    exact hp0_coprime
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
  have hnormSubOne : 6 ∣ Ideal.absNorm v.asIdeal - 1 := by
    have hunitCard : Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
      calc
        Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 :=
          Fintype.card_units (α := 𝓞 F ⧸ v.asIdeal)
        _ = Ideal.absNorm v.asIdeal - 1 := by rw [hcardNat]
    have horderDiv : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) ∣
        Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ := orderOf_dvd_card
    rw [hrootsMapOrder] at horderDiv
    rw [hunitCard] at horderDiv
    exact horderDiv
  have hcyclic : IsCyclic (𝓞 F ⧸ v.asIdeal)ˣ := inferInstance
  obtain ⟨g, hgOrder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (𝓞 F ⧸ v.asIdeal)ˣ)
  have hunitCard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
    calc
      Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ :=
        Nat.card_eq_fintype_card
      _ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 :=
        Fintype.card_units (α := 𝓞 F ⧸ v.asIdeal)
      _ = Ideal.absNorm v.asIdeal - 1 := by rw [hcardNat]
  have hgOrder' : orderOf g = Ideal.absNorm v.asIdeal - 1 := hgOrder.trans hunitCard
  let e : ℕ := (Ideal.absNorm v.asIdeal - 1) / 6
  have hdivN := hnormSubOne
  obtain ⟨k, hk⟩ := hnormSubOne
  have heq : e = k := by dsimp [e]; rw [hk]; simp
  have hN : Ideal.absNorm v.asIdeal - 1 = 6 * e := by rw [hk, heq]
  have hNpos : 0 < Ideal.absNorm v.asIdeal - 1 := by omega
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hNpos hdivN) (by decide)
  have he_dvd : e ∣ Ideal.absNorm v.asIdeal - 1 := by
    refine ⟨6, ?_⟩
    rw [hN]
    ring
  have horderPow : orderOf (g ^ e) = 6 := by
    rw [orderOf_pow, hgOrder', Nat.gcd_eq_right he_dvd, hN]
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left 6 hepos
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := bridge_count_spanSingleton_eq_neg_log_valuation v (p : F) hp.2.1
    rw [hcountP] at h
    linarith
  have hvalP : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hp.2.1
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hpvalne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  have hphaseErr (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) = 1 := by
    have hvalNum : HeightOneSpectrum.valuation F v ((a : F) - b) ≤ WithZero.exp (-1 : ℤ) := by
      change v.valuation F (algebraMap (𝓞 F) F (a - b)) ≤ WithZero.exp (-1 : ℤ)
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (a - b) 1).2
      simpa using hab
    have hvalDiv : HeightOneSpectrum.valuation F v (((a : F) - b) / (p : F)) ≤ 1 := by
      rw [map_div₀, hvalP]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hvalNum
    have hlocal : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) ∈
        v.adicCompletionIntegers F := by
      change ((((a : F) - b) / (p : F) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    exact A.integral v _ hlocal
  have hphaseCongr (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
    have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) =
        algebraMap F (v.adicCompletion F) ((a : F) / (p : F)) -
          algebraMap F (v.adicCompletion F) ((b : F) / (p : F)) := by
      have hF : ((a : F) - b) / (p : F) =
          (a : F) / (p : F) - (b : F) / (p : F) := by
        field_simp [Units.ne_zero p]
      calc
        algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) =
            algebraMap F (v.adicCompletion F)
              ((a : F) / (p : F) - (b : F) / (p : F)) := by rw [hF]
        _ = _ := map_sub _ _ _
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) ((a : F) / (p : F)))
      (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))
    have hbne : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
          (A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) /
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))) *
              A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [div_mul_cancel₀ _ hbne]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) *
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [hphaseErr a b hab, one_mul]
  have hrepAdd (x y : 𝓞 F ⧸ v.asIdeal) : (x + y).out - (x.out + y.out) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, Ideal.Quotient.mk_out]
    simp [map_add]
  have hrepMul (t x : 𝓞 F ⧸ v.asIdeal) : (t * x).out - x.out * t.out ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, Ideal.Quotient.mk_out]
    simp [map_mul, mul_comm]
  let ψfun : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x =>
    A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F)))
  have hψzero : ψfun 0 = 1 := by
    have hmem : (0 : 𝓞 F ⧸ v.asIdeal).out ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp
    calc
      ψfun 0 = A.ψ v (algebraMap F (v.adicCompletion F)
          (((0 : 𝓞 F ⧸ v.asIdeal).out : F) / (p : F))) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (0 / (p : F))) :=
        hphaseCongr (0 : 𝓞 F ⧸ v.asIdeal).out 0 (by simpa using hmem)
      _ = 1 := by simp
  have hψadd (x y : 𝓞 F ⧸ v.asIdeal) : ψfun (x + y) = ψfun x * ψfun y := by
    have harg : algebraMap F (v.adicCompletion F)
        (((x.out : F) + y.out) / (p : F)) =
      algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F)) +
        algebraMap F (v.adicCompletion F) (y.out / (p : F)) := by
      have hF : ((x.out : F) + y.out) / (p : F) =
          (x.out : F) / (p : F) + y.out / (p : F) := by
        field_simp [Units.ne_zero p]
      calc
        algebraMap F (v.adicCompletion F) (((x.out : F) + y.out) / (p : F)) =
            algebraMap F (v.adicCompletion F)
              ((x.out : F) / (p : F) + y.out / (p : F)) := by rw [hF]
        _ = _ := map_add _ _ _
    calc
      ψfun (x + y) = A.ψ v (algebraMap F (v.adicCompletion F)
          (((x + y).out : F) / (p : F))) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          (((x.out + y.out : 𝓞 F) : F) / (p : F))) :=
        hphaseCongr (x + y).out (x.out + y.out) (hrepAdd x y)
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((x.out : F) / (p : F)) +
            algebraMap F (v.adicCompletion F) (y.out / (p : F))) := by
        rw [show ((x.out + y.out : 𝓞 F) : F) = (x.out : F) + y.out by simp, harg]
      _ = ψfun x * ψfun y := by rw [(A.ψ v).map_add_eq_mul]
  let ψchar : AddChar (𝓞 F ⧸ v.asIdeal) ℂ :=
    { toFun := ψfun, map_zero_eq_one' := hψzero, map_add_eq_mul' := hψadd }
  have hψMulFormula (t x : 𝓞 F ⧸ v.asIdeal) :
      ψchar (t * x) = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F t.out / (p : F))) := by
    calc
      ψchar (t * x) = A.ψ v (algebraMap F (v.adicCompletion F)
          (((t * x).out : F) / (p : F))) := rfl
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          ((x.out * t.out : 𝓞 F) / (p : F))) := hphaseCongr (t * x).out
            (x.out * t.out) (hrepMul t x)
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F t.out / (p : F))) := by
        simp [map_mul]
  have hnotDiff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
    fun h => hv (S.different_mem v h)
  obtain ⟨_, hUnram⟩ := A.unramified v hnotDiff
  obtain ⟨a, ha⟩ := hUnram (p : F) hvalP
  have hψprim : ψchar.IsPrimitive := by
    intro t ht htriv
    let tu : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ht).unit
    let x : 𝓞 F ⧸ v.asIdeal := tu⁻¹ * Ideal.Quotient.mk v.asIdeal a
    have htu : (tu : 𝓞 F ⧸ v.asIdeal) = t := (isUnit_iff_ne_zero.mpr ht).unit_spec
    have htx : t * x = Ideal.Quotient.mk v.asIdeal a := by
      change t * (tu⁻¹ * Ideal.Quotient.mk v.asIdeal a) = _
      rw [← htu]
      simp [mul_assoc]
    have hrep : (t * x).out - a ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, Ideal.Quotient.mk_out, htx]
      simp
    have hphase : ψchar (t * x) = A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) := by
      calc
        ψchar (t * x) = A.ψ v (algebraMap F (v.adicCompletion F)
            (((t * x).out : F) / (p : F))) := rfl
        _ = A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) :=
          hphaseCongr (t * x).out a hrep
    have htrivx : ψchar (t * x) = 1 := by
      have h := congrArg (fun ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ => ψ x) htriv
      simpa [AddChar.mulShift_apply] using h
    apply ha
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) = ψchar (t * x) :=
        hphase.symm
      _ = 1 := htrivx
  have hprimMapUnits : IsPrimitiveRoot (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6) 6 :=
    IsPrimitiveRoot.iff_orderOf.mpr hrootsMapOrder
  have hprimMap : IsPrimitiveRoot
      ((Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζ6 : (𝓞 F ⧸ v.asIdeal)ˣ) : 𝓞 F ⧸ v.asIdeal) 6 :=
    IsPrimitiveRoot.coe_units_iff.mpr hprimMapUnits
  have hgenPow : (g ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) ^ 6 = 1 := by
    rw [← horderPow]
    exact pow_orderOf_eq_one _
  have hgenPowR : ((g ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) : 𝓞 F ⧸ v.asIdeal) ^ 6 = 1 := by
    simpa using congrArg (fun z : (𝓞 F ⧸ v.asIdeal)ˣ => (z : 𝓞 F ⧸ v.asIdeal)) hgenPow
  obtain ⟨i, hi, hrootpow⟩ := hprimMap.eq_pow_of_pow_eq_one hgenPowR
  let ζpre : rootsOfUnity 6 (𝓞 F) := ζ6 ^ i
  have hrootpreMap : Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre = g ^ e := by
    apply Units.ext
    simpa [ζpre, map_pow, Units.val_pow_eq_pow_val] using hrootpow
  have hquotPre : Ideal.Quotient.mk v.asIdeal ((ζpre : (𝓞 F)ˣ) : 𝓞 F) =
      (g ^ e : (𝓞 F ⧸ v.asIdeal)) := by
    have h := congrArg (fun u : (𝓞 F ⧸ v.asIdeal)ˣ => (u : 𝓞 F ⧸ v.asIdeal)) hrootpreMap
    rw [Ideal.rootsOfUnityMapQuot_apply] at h
    simpa [ζpre, Units.val_pow_eq_pow_val] using h
  have hresG : residue v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out) =
      (g : 𝓞 F ⧸ v.asIdeal) := hresAlg _
  have hchiAlgExists : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out) ^
          ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    refine ⟨ζpre, ?_⟩
    rw [hresG]
    simpa [e] using hquotPre
  have hchiAlgMap : Ideal.rootsOfUnityMapQuot v.asIdeal 6
      (chiAlg v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out)) = g ^ e := by
    unfold chiAlg
    split
    · rename_i h
      apply Units.ext
      rw [Ideal.rootsOfUnityMapQuot_apply]
      have hs := h.choose_spec
      rw [hs, hresG]
      simpa [e] using hquotPre
    · rename_i h
      exact (h hchiAlgExists).elim
  have hchiAlgEq : chiAlg v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out) = ζpre := by
    apply hrootsMapInj
    rw [hchiAlgMap, hrootpreMap]
  let evalRoot : rootsOfUnity 6 (𝓞 F) →* ℂˣ :=
    (Units.map (D.σ0.comp (algebraMap (𝓞 F) F))).comp
      (rootsOfUnity 6 (𝓞 F)).subtype
  have hcompInj : Function.Injective (D.σ0.comp (algebraMap (𝓞 F) F)) :=
    (RingHom.injective D.σ0).comp (IsFractionRing.injective (𝓞 F) F)
  have hevalInj : Function.Injective evalRoot := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply hcompInj
    simpa [evalRoot] using congrArg (fun z : ℂˣ => (z : ℂ)) hab
  have hrootpreMapOrder : orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre) = 6 := by
    rw [hrootpreMap, horderPow]
  have hrootpreOrder : orderOf ζpre = 6 := by
    apply Nat.dvd_antisymm
    · have hpow := pow_orderOf_eq_one (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre)
      have hmap : Ideal.rootsOfUnityMapQuot v.asIdeal 6
          (ζpre ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre)) =
            Ideal.rootsOfUnityMapQuot v.asIdeal 6 1 := by
        rw [map_pow, hpow, map_one]
      have hpow' : ζpre ^ orderOf (Ideal.rootsOfUnityMapQuot v.asIdeal 6 ζpre) = 1 :=
        hrootsMapInj hmap
      simpa [hrootpreMapOrder] using orderOf_dvd_of_pow_eq_one hpow'
    · have h := orderOf_map_dvd (Ideal.rootsOfUnityMapQuot v.asIdeal 6) ζpre
      rw [hrootpreMapOrder] at h
      exact h
  have hprimPre : IsPrimitiveRoot ζpre 6 := IsPrimitiveRoot.iff_orderOf.mpr hrootpreOrder
  have hprimEval : IsPrimitiveRoot (evalRoot ζpre) 6 :=
    hprimPre.map_of_injective (f := evalRoot) hevalInj
  have hEvalOrder : orderOf (evalRoot ζpre) = 6 := hprimEval.eq_orderOf.symm
  have hresGne : residue v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
    rw [hresG]
    exact g.ne_zero
  have hchiG : (chiUnit g : ℂ) = (evalRoot ζpre : ℂ) := by
    change chiPow D v (algebraMap (𝓞 F) F (g : 𝓞 F ⧸ v.asIdeal).out) 1 = _
    rw [SB.chiPow_nonzero v _ 1 hresGne]
    unfold chi
    rw [if_neg hresGne, hchiAlgEq]
    simp [evalRoot]
  have hchiUnitOrder : orderOf (chiUnit g) = 6 := by
    have hunitEq : chiUnit g = evalRoot ζpre := Units.ext hchiG
    rw [hunitEq]
    exact hEvalOrder
  have hchiCharAt : chiChar (g : 𝓞 F ⧸ v.asIdeal) = (chiUnit g : ℂ) := by
    rw [hchiChar]
    rfl
  have hchiCharPrim : IsPrimitiveRoot (chiChar (g : 𝓞 F ⧸ v.asIdeal)) 6 := by
    rw [hchiCharAt, hchiG]
    exact IsPrimitiveRoot.coe_units_iff.mpr hprimEval
  have hchiCharOrder : orderOf (chiChar (g : 𝓞 F ⧸ v.asIdeal)) = 6 :=
    hchiCharPrim.eq_orderOf.symm
  have hchiCharSix : chiChar ^ 6 = 1 := by
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have hx : residue v (algebraMap (𝓞 F) F (x : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact x.ne_zero
    rw [hchiChar x, SB.chiPow_nonzero v _ 1 hx]
    simpa [pow_one] using SB.chi_six v _ hx
  have hcharAtPow : (chiChar (g : 𝓞 F ⧸ v.asIdeal)) ^ orderOf chiChar = 1 := by
    have h := congrArg (fun χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ => χ (g : 𝓞 F ⧸ v.asIdeal))
      (pow_orderOf_eq_one chiChar)
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  have hchiOrderLower : 6 ∣ orderOf chiChar := by
    rw [← hchiCharOrder]
    exact orderOf_dvd_of_pow_eq_one hcharAtPow
  have hchiOrder : orderOf chiChar = 6 :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hchiCharSix) hchiOrderLower
  refine ⟨hchars, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨chiChar, hchiOrder, hchiChar⟩
  · exact ⟨ψchar, hψprim, hψMulFormula⟩

/-- Finite additive orthogonality with no finsum ambiguity.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses FINITE_CHAR; Mathlib AddChar orthogonality. -/
theorem a2_bridge_FINITE_CHAR_orthogonality (v : FinPlace F) :
    letI := bridgeResidueField v
    letI := bridgeResidueFintype v
    ∀ (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ), ψ.IsPrimitive → ∀ t,
      (∑ x : 𝓞 F ⧸ v.asIdeal, ψ (t * x)) =
        if t = 0 then (Ideal.absNorm v.asIdeal : ℂ) else 0 := by
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  classical
  intro ψ hψ t
  by_cases ht : t = 0
  · subst t
    have hcard : (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) =
        (Ideal.absNorm v.asIdeal : ℂ) := by
      have hcardNat : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      exact_mod_cast hcardNat
    simp [hcard]
  · rw [if_neg ht]
    have hψne : ψ ≠ 1 := by
      have h := hψ (a := (1 : 𝓞 F ⧸ v.asIdeal)) (by simp)
      simpa using h
    rw [Fintype.sum_bijective (fun x : 𝓞 F ⧸ v.asIdeal => t * x)
      (mulLeft_bijective₀ t ht) (fun x => ψ (t * x)) ψ (fun _ => rfl)]
    exact AddChar.sum_eq_zero_of_ne_one hψne

/-- Rewrite every finite residue finsum as the actual univ sum.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses bridgeResidueFintype. -/
theorem a2_bridge_FINITE_CHAR_finsum (v : FinPlace F) (f : (𝓞 F ⧸ v.asIdeal) → ℂ) :
    letI := bridgeResidueFintype v
    (∑ᶠ x, f x) = ∑ x : 𝓞 F ⧸ v.asIdeal, f x := by
  letI := bridgeResidueFintype v
  classical
  exact finsum_eq_sum_of_fintype f

end ArtinPrimitiveRoots.A2
