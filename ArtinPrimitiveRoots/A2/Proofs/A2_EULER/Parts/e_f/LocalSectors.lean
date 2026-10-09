import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_f
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private theorem po_chi_norm_one (D : FieldData F) (P : FinPlace F) (x : F)
    (hx : residue P x ≠ 0) : ‖chi D P x‖ = 1 := by
  let ζ : rootsOfUnity 6 (𝓞 F) := chiAlg P x
  have hζ : (ζ : (𝓞 F)ˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 (ζ : (𝓞 F)ˣ)).mp ζ.property
  let ζ0 : 𝓞 F := ((ζ : (𝓞 F)ˣ) : 𝓞 F)
  have hζOF : ζ0 ^ 6 = 1 := by
    simpa [ζ0] using congrArg Units.val hζ
  have hζC : (D.σ0 (algebraMap (𝓞 F) F ζ0)) ^ 6 = 1 := by
    calc
      _ = D.σ0 (algebraMap (𝓞 F) F (ζ0 ^ 6)) := by simp only [map_pow]
      _ = 1 := by rw [hζOF]; simp
  have hpow : (chi D P x) ^ 6 = 1 := by
    rw [chi, if_neg hx]
    exact hζC
  have hfin : IsOfFinOrder (chi D P x) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, hpow⟩
  exact hfin.norm_eq_one


private instance eulerResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal

private noncomputable instance eulerResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal


private lemma euler_count_spanSingleton_div (v : FinPlace F) (x y : F)
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


private lemma euler_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring


private lemma euler_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
    euler_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    euler_count_spanSingleton_eq_neg_log_intValuation v n hn,
    euler_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring


private lemma euler_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
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


theorem po_C_local_T_values : ∀ v, v ∉ S.Sf → ∀ e : ℤ, ∀ y : S.R,
  localT R v e (y : F) =
    (if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e * localT R v e 1
      else if e % 6 = 0 then qI v.asIdeal - 1 else 0) ∧
  (e % 6 ≠ 0 → ‖localT R v e 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ)) ∧ localT R v 0 1 = -1 := by
  intro v hv e y
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let SB := a2_bridge_SYMBOL D S
  let p : Fˣ := primeGen R v
  have hp0 : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v hv)).1
    simpa [p, primeGen, hv, R.exterior.prime_val] using h
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp0.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := euler_count_spanSingleton_eq_neg_log_valuation v (p : F) hp0.2.1
    rw [hcountP] at h
    linarith
  have hvalP : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hp0.2.1
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hpvalne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  obtain ⟨hchars, hchiSix, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp0
  obtain ⟨χ₁, hχ₁order, hχ₁eval⟩ := hchiSix
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  obtain ⟨χe, hχeeval⟩ := hchars e
  have hresAlg (x : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hmulchar_zpow (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
      (u : (𝓞 F ⧸ v.asIdeal)ˣ) : χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = χ u ^ e := by
    have h := χ.toUnitHom.map_zpow u e
    calc
      χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = (χ.toUnitHom (u ^ e) : ℂ) :=
        (MulChar.coe_toUnitHom χ (u ^ e)).symm
      _ = (χ.toUnitHom u : ℂ) ^ e := by
        simpa only [Units.val_zpow_eq_zpow_val] using congrArg Units.val h
      _ = χ u ^ e := by rw [MulChar.coe_toUnitHom]
  have hχpow_eq : χe = χ₁ ^ e := by
    apply MulChar.ext
    intro u
    have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact u.ne_zero
    calc
      χe (u : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
      _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
        SB.chiPow_nonzero v _ e hu
      _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 ^ e := by
        rw [SB.chiPow_nonzero v _ 1 hu, zpow_one]
      _ = χ₁ (u : 𝓞 F ⧸ v.asIdeal) ^ e := by rw [hχ₁eval]
      _ = χ₁ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) := (hmulchar_zpow χ₁ u).symm
      _ = (χ₁ ^ e) (u : 𝓞 F ⧸ v.asIdeal) :=
        (MulChar.zpow_apply_coe χ₁ e u).symm
  have hχe_one : e % 6 = 0 → χe = 1 := by
    intro he
    have hdvd : (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.mpr he
    have horderDvd : (orderOf χ₁ : ℤ) ∣ e := by rw [hχ₁order]; exact hdvd
    have hpow : χ₁ ^ e = 1 := (orderOf_dvd_iff_zpow_eq_one).mp horderDvd
    rw [hχpow_eq, hpow]
  have hχe_ne_one : e % 6 ≠ 0 → χe ≠ 1 := by
    intro he hχ
    have hpow : χ₁ ^ e = 1 := hχpow_eq.symm.trans hχ
    have hdvd : (orderOf χ₁ : ℤ) ∣ e := (orderOf_dvd_iff_zpow_eq_one).mpr hpow
    rw [hχ₁order] at hdvd
    exact he (Int.dvd_iff_emod_eq_zero.mp hdvd)
  have hphaseErr (z : F)
      (hz : HeightOneSpectrum.valuation F v z ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z / (p : F))) = 1 := by
    have hvalDiv : HeightOneSpectrum.valuation F v (z / (p : F)) ≤ 1 := by
      rw [map_div₀, hvalP]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hz
    have hlocal : algebraMap F (v.adicCompletion F) (z / (p : F)) ∈
        v.adicCompletionIntegers F := by
      change ((z / (p : F) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    exact A.integral v _ hlocal
  have hphaseCongr (z₁ z₂ : F)
      (hz : HeightOneSpectrum.valuation F v (z₁ - z₂) ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
    have harg : algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F)) =
        algebraMap F (v.adicCompletion F) (z₁ / (p : F)) -
          algebraMap F (v.adicCompletion F) (z₂ / (p : F)) := by
      have hF : (z₁ - z₂) / (p : F) = z₁ / (p : F) - z₂ / (p : F) := by
        field_simp [Units.ne_zero p]
      rw [hF, map_sub]
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) (z₁ / (p : F)))
      (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))
    have hz₂ : A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
          (A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) /
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))) *
              A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) :=
        (div_mul_cancel₀ _ hz₂).symm
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F))) *
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [hphaseErr (z₁ - z₂) hz, one_mul]
  have hphase (y : S.R) (x : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
        ψ (-(residue v (y : F)) * x) := by
    have hyval : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
    obtain ⟨ay, dy, hdy⟩ := v.exists_primeCompl_mul_eq_of_integer (y : F) hyval
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have hdyNot : dy.1 ∉ v.asIdeal := by
      exact Ideal.mem_primeCompl_iff.mp dy.2
    have hresY : residue v (y : F) =
        Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy :=
      euler_residue_rep v (y : F) ay dy.1 hdyNot hdy
    let b : 𝓞 F := (-a).out
    have hdq : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
      intro hzero
      exact hdyNot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have hmkB : Ideal.Quotient.mk v.asIdeal b = -a := by
      simp [b]
    have hmk : Ideal.Quotient.mk v.asIdeal (ay + b * dy) = 0 := by
      calc
        Ideal.Quotient.mk v.asIdeal (ay + b * dy) =
            Ideal.Quotient.mk v.asIdeal ay +
              Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by simp
        _ = (Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy +
              Ideal.Quotient.mk v.asIdeal b) * Ideal.Quotient.mk v.asIdeal dy := by
          have hcancel : (Ideal.Quotient.mk v.asIdeal ay /
              Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy =
                Ideal.Quotient.mk v.asIdeal ay := div_mul_cancel₀ _ hdq
          calc
            _ = (Ideal.Quotient.mk v.asIdeal ay /
                Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy +
                  Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by rw [hcancel]
            _ = _ := by ring
        _ = (residue v (y : F) + Ideal.Quotient.mk v.asIdeal b) *
              Ideal.Quotient.mk v.asIdeal dy := by rw [hresY]
        _ = 0 := by rw [hmkB]; ring
    have hmem : ay + b * dy ∈ v.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    have hvalNum : HeightOneSpectrum.valuation F v
        (algebraMap (𝓞 F) F (ay + b * dy)) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (ay + b * dy) 1).2
      simpa using hmem
    have hvalDy : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_eq_one_iff_mem_primeCompl dy.1).2 dy.2
    have hmul : ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
        algebraMap (𝓞 F) F (ay + b * dy) := by
      calc
        ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
            (y : F) * algebraMap (𝓞 F) F dy +
              (b : F) * algebraMap (𝓞 F) F dy := by ring
        _ = algebraMap (𝓞 F) F ay + algebraMap (𝓞 F) F (b * dy) := by
          rw [hdy, map_mul]
        _ = algebraMap (𝓞 F) F (ay + b * dy) := by rw [map_add]
    have hvalYb : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) ≤
        WithZero.exp (-1 : ℤ) := by
      have heq : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) =
          HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F (ay + b * dy)) := by
        calc
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) * 1 := by simp
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
                HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) := by rw [hvalDy]
          _ = HeightOneSpectrum.valuation F v
                (((y : F) + (b : F)) * algebraMap (𝓞 F) F dy) := by
            rw [(v.valuation F).map_mul]
          _ = _ := by rw [hmul]
      rw [heq]
      exact hvalNum
    have hvalErr : HeightOneSpectrum.valuation F v
        (-(y : F) * algebraMap (𝓞 F) F x.out - (b : F) * algebraMap (𝓞 F) F x.out) ≤
          WithZero.exp (-1 : ℤ) := by
      have hident : -(y : F) * algebraMap (𝓞 F) F x.out -
          (b : F) * algebraMap (𝓞 F) F x.out =
            -(((y : F) + (b : F)) * algebraMap (𝓞 F) F x.out) := by ring
      rw [hident, (v.valuation F).map_neg, (v.valuation F).map_mul]
      have hxval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤ 1 :=
        v.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
            HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤
            WithZero.exp (-1 : ℤ) * 1 :=
          mul_le_mul hvalYb hxval (zero_le) (zero_le)
        _ = WithZero.exp (-1 : ℤ) := mul_one _
    have hphase' := hphaseCongr
      (-(y : F) * algebraMap (𝓞 F) F x.out)
      ((b : F) * algebraMap (𝓞 F) F x.out) hvalErr
    have harg : -((y : F) * algebraMap (𝓞 F) F x.out / (p : F)) =
        (-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F) := by ring
    calc
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := by rw [harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (((b : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := hphase'
      _ = ψ (-(residue v (y : F)) * x) := by
        symm
        simpa [a, b, mul_comm] using hψeval (-a) x
  have hfiniteT (y : S.R) : localT R v e (y : F) =
      ∑ x : 𝓞 F ⧸ v.asIdeal,
        χe x * ψ (-(residue v (y : F)) * x) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = χe x * A.ψ v (algebraMap F (v.adicCompletion F)
          (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) := by
        rw [← hχeeval x]
      _ = _ := by rw [hphase y x]
  have hresOne : residue v (1 : F) = 1 := by
    simpa using SB.residue_algebraMap v (1 : 𝓞 F)
  have hresZero : residue v (0 : F) = 0 := by
    simpa using SB.residue_algebraMap v (0 : 𝓞 F)
  have hfiniteShift (y : S.R) : localT R v e (y : F) =
      gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
    calc
      localT R v e (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
          χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
      _ = gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
        simp [gaussSum, AddChar.mulShift_apply]
  have hfiniteOne : localT R v e 1 = gaussSum χe (ψ.mulShift (-1)) := by
    simpa [hresOne] using hfiniteShift (1 : S.R)
  have hχ₁minus : χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) = -1 := by
      simpa using hresAlg (-1 : 𝓞 F ⧸ v.asIdeal)
    have hresNeg : residue v (-1 : F) = -1 := by
      simpa using SB.residue_algebraMap v (-1 : 𝓞 F)
    calc
      χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 1 := hχ₁eval _
      _ = chi D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) :=
        by simpa [pow_one] using
          SB.chiPow_nonzero v _ 1 (by rw [hres]; exact neg_ne_zero.mpr one_ne_zero)
      _ = chi D v (-1 : F) := SB.chi_congr v _ _ (hres.trans hresNeg.symm)
      _ = 1 := SB.chi_minus_one v hv
  have hχeminus : χe (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hχ₁unit : χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχ₁minus
    calc
      χe (-1 : 𝓞 F ⧸ v.asIdeal) = χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by simp
      _ = (χ₁ ^ e) (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by rw [hχpow_eq]
      _ = χ₁ ((↑((-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e) : 𝓞 F ⧸ v.asIdeal)) :=
        MulChar.zpow_apply_coe χ₁ e (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
      _ = χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e := hmulchar_zpow χ₁ (-1)
      _ = 1 := by rw [hχ₁unit]; simp
  have hshiftGauss : gaussSum χe (ψ.mulShift (-1)) = gaussSum χe ψ := by
    have h := gaussSum_mulShift_eq χe ψ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
    have hχeunit : χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχeminus
    have hinvχ : χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      calc
        χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) =
            (χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ))⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = 1 := by rw [hχeunit]; simp
    calc
      gaussSum χe (ψ.mulShift (-1)) = χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) *
          gaussSum χe ψ := h
      _ = gaussSum χe ψ := by rw [hinvχ, one_mul]
  have hfiniteOneGauss : localT R v e 1 = gaussSum χe ψ := hfiniteOne.trans hshiftGauss
  have hscale : residue v (y : F) ≠ 0 →
      localT R v e (y : F) =
        star (chi D v (y : F)) ^ e * localT R v e 1 := by
    intro hy
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have ha : a ≠ 0 := by simpa [a] using hy
    let u : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ha).unit
    have hu : (u : 𝓞 F ⧸ v.asIdeal) = a :=
      (isUnit_iff_ne_zero.mpr ha).unit_spec
    have hshift : ψ.mulShift (-a) = (ψ.mulShift (-1)).mulShift (u : 𝓞 F ⧸ v.asIdeal) := by
      ext x
      simp [AddChar.mulShift_apply, hu, mul_assoc]
    have hsum := gaussSum_mulShift_eq χe (ψ.mulShift (-1)) u
    have hunitGauss : gaussSum χe (ψ.mulShift (-a)) =
        χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := by
      rw [hshift]
      exact hsum
    have hchiA : χe u = chi D v (y : F) ^ e := by
      have hresu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
          residue v (y : F) := by rw [hresAlg, hu]
      have hresu_ne : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresu]
        exact hy
      calc
        χe u = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
        _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
          SB.chiPow_nonzero v _ e hresu_ne
        _ = chi D v (y : F) ^ e := by rw [SB.chi_congr v _ _ hresu]
    have hnormChi : ‖chi D v (y : F)‖ = 1 := SB.chi_norm v _ hy
    have hnormPow : ‖chi D v (y : F) ^ e‖ = 1 := by
      rw [Complex.norm_zpow, hnormChi]
      norm_num
    have hinv : (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F)) ^ e := by
      calc
        (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F) ^ e) :=
          Complex.inv_eq_conj hnormPow
        _ = star (chi D v (y : F)) ^ e := by simp
    have hχinv : χe⁻¹ u = star (chi D v (y : F)) ^ e := by
      calc
        χe⁻¹ u = (χe u)⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = star (chi D v (y : F)) ^ e := by rw [hchiA, hinv]
    calc
      localT R v e (y : F) = gaussSum χe (ψ.mulShift (-a)) := by
        simpa [a] using hfiniteShift y
      _ = χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := hunitGauss
      _ = star (chi D v (y : F)) ^ e * localT R v e 1 := by
        rw [hχinv, ← hfiniteOne]
  have hzeroSum : localT R v e (0 : F) =
      (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
    have hsum : localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := by
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χe x * ψ (-(residue v (0 : F)) * x) := by
          simpa [hresZero] using hfiniteT (0 : S.R)
        _ = _ := by simp [hresZero]
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hcardPos : 1 ≤ Ideal.absNorm v.asIdeal := by
      have h : 1 ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
        exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
      rw [hcard] at h
      exact h
    by_cases he : e % 6 = 0
    · have hunitCard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
        calc
          Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ :=
          Nat.card_eq_fintype_card
          _ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 := Fintype.card_units (α := 𝓞 F ⧸ v.asIdeal)
          _ = Ideal.absNorm v.asIdeal - 1 := by rw [hcard]
      have hunitReal : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℝ) = qI v.asIdeal - 1 := by
        rw [hunitCard]
        dsimp [qI]
        rw [Nat.cast_sub hcardPos]
        norm_num
      have hunitComplex : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) =
          (qI v.asIdeal : ℂ) - 1 := by exact_mod_cast hunitReal
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = ∑ x : 𝓞 F ⧸ v.asIdeal,
              (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hχe_one he]
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by simp [gaussSum]
        _ = (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) := by rw [gaussSum_one_one]
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
          simpa [he] using hunitComplex
    ·
      have hsumZero : (∑ x : 𝓞 F ⧸ v.asIdeal, χe x) = 0 := by
        simpa [gaussSum] using (MulChar.sum_eq_zero_of_ne_one (hχe_ne_one he))
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = 0 := hsumZero
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by simp [he]
  constructor
  · by_cases hy : residue v (y : F) ≠ 0
    · simpa [hy] using hscale hy
    · have hresY0 : residue v (y : F) = 0 := by simpa using hy
      have hfiniteTzero : localT R v e (0 : F) =
          ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
        simpa using hfiniteT (0 : S.R)
      have hlocalY0 : localT R v e (y : F) = localT R v e (0 : F) := by
        calc
          localT R v e (y : F) =
              ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
          _ = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
            rw [hresY0, hresZero]
          _ = localT R v e (0 : F) := hfiniteTzero.symm
      calc
        localT R v e (y : F) = localT R v e (0 : F) := hlocalY0
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := hzeroSum
        _ = if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e *
              localT R v e 1 else if e % 6 = 0 then qI v.asIdeal - 1 else 0 := by
          have hdiv : (e % 6 = 0) ↔ (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.symm
          have hresNot : ¬(residue v (y : F) ≠ 0) := by simp [hresY0]
          by_cases h : (6 : ℤ) ∣ e
          · rw [if_pos (hdiv.mpr h), if_pos (hdiv.mpr h)]
            rw [if_neg hresNot]
            exact Complex.ofReal_sub _ _
          · rw [if_neg (fun he => h (hdiv.mp he)), if_neg (fun he => h (hdiv.mp he))]
            rw [if_neg hresNot]
            rfl
  constructor
  · intro he
    have hχne := hχe_ne_one he
    have hlocalEq : localT R v e 1 = gaussSum χe ψ := hfiniteOneGauss
    have hprod : gaussSum χe ψ * star (gaussSum χe ψ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        gaussSum χe ψ * star (gaussSum χe ψ) =
            gaussSum χe ψ * gaussSum χe⁻¹ ψ⁻¹ := by rw [star_gaussSum_eq]
        _ = _ := gaussSum_mul_gaussSum_eq_card hχne hψprim
    have hnormSqC : (Complex.normSq (gaussSum χe ψ) : ℂ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        (Complex.normSq (gaussSum χe ψ) : ℂ) =
            gaussSum χe ψ * star (gaussSum χe ψ) := (Complex.mul_conj _).symm
        _ = _ := hprod
    have hnormSq : ‖gaussSum χe ψ‖ ^ 2 =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast hnormSqC
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hnormSqQ : ‖gaussSum χe ψ‖ ^ 2 = qI v.asIdeal := by
      rw [hnormSq, hcard]
      rfl
    have hnormG : ‖gaussSum χe ψ‖ = qI v.asIdeal ^ (1 / 2 : ℝ) := by
      calc
        ‖gaussSum χe ψ‖ = Real.sqrt (‖gaussSum χe ψ‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        _ = Real.sqrt (qI v.asIdeal) := by rw [hnormSqQ]
        _ = qI v.asIdeal ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    simpa [hlocalEq] using hnormG
  · obtain ⟨χ0, hχ0eval⟩ := hchars (0 : ℤ)
    have hχ0one : χ0 = 1 := by
      apply MulChar.ext
      intro u
      have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresAlg]
        exact u.ne_zero
      rw [hχ0eval u, SB.chiPow_nonzero v _ 0 hu, zpow_zero]
      simp
    have hfiniteT0 (y : S.R) : localT R v 0 (y : F) =
        ∑ x : 𝓞 F ⧸ v.asIdeal, χ0 x * ψ (-(residue v (y : F)) * x) := by
      unfold localT
      rw [a2_bridge_FINITE_CHAR_finsum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hχ0eval x, hphase y x]
    have hfiniteShift0 (y : S.R) : localT R v 0 (y : F) =
        gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
      calc
        localT R v 0 (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χ0 x * ψ (-(residue v (y : F)) * x) := hfiniteT0 y
        _ = gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
          simp [gaussSum, AddChar.mulShift_apply]
    have hlocalZero : localT R v 0 1 =
        gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
          (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)) := by
      calc
        localT R v 0 1 = gaussSum χ0 (ψ.mulShift (-1)) := by
          simpa [hresOne] using hfiniteShift0 (1 : S.R)
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (ψ.mulShift (-1)) := by rw [hχ0one]
    have hψshiftPrim : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).IsPrimitive := by
      intro a ha htriv
      have hnonzero : (-1 : 𝓞 F ⧸ v.asIdeal) * a ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha
      have htriv' : ψ.mulShift ((-1 : 𝓞 F ⧸ v.asIdeal) * a) = 1 := by
        simpa only [AddChar.mulShift_mulShift] using htriv
      exact (hψprim hnonzero) htriv'
    have hψshiftNe : ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal) ≠ 1 := by
      intro h
      have h' : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).mulShift 1 = 1 := by
        simpa using h
      exact (hψshiftPrim one_ne_zero) h'
    rw [hlocalZero]
    exact gaussSum_one_left hψshiftNe


private lemma euler_generators_unit_ratio (I : Ideal (𝓞 F))
    (x y : F) (hx : S.IsGen x I) (hy : S.IsGen y I) :
    ∃ u : S.US, x = (u : Fˣ) * y := by
  have hxy0 : x / y ≠ 0 := div_ne_zero hx.2.1 hy.2.1
  let r : Fˣ := Units.mk0 (x / y) hxy0
  have hrVal : ∀ w : FinPlace F, w ∉ S.Sf →
      HeightOneSpectrum.valuation F w (r : Fˣ) = 1 := by
    intro w hw
    have hcountW : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) = 0 := by
      rw [euler_count_spanSingleton_div w x y hx.2.1 hy.2.1,
        hx.2.2 w hw, hy.2.2 w hw]
      ring
    have hlogW : WithZero.log (HeightOneSpectrum.valuation F w (x / y)) = 0 := by
      have h := euler_count_spanSingleton_eq_neg_log_valuation w (x / y) hxy0
      rw [hcountW] at h
      omega
    have hne : HeightOneSpectrum.valuation F w (x / y) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr hxy0
    calc
      HeightOneSpectrum.valuation F w (r : Fˣ) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F w (x / y))) := by
        change HeightOneSpectrum.valuation F w (x / y) = _
        exact (WithZero.exp_log hne).symm
      _ = 1 := by rw [hlogW]; simp
  have hrUnit : r ∈ S.US := by
    change r ∈ (S.Sf : Set (FinPlace F)).unit F
    exact hrVal
  refine ⟨⟨r, hrUnit⟩, ?_⟩
  change x = (r : Fˣ) * y
  dsimp [r]
  field_simp [hy.2.1]


private lemma euler_residue_add_integral (v : FinPlace F) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1) :
    residue v (x + y) = residue v x + residue v y := by
  letI := eulerResidueMaximal v
  letI := eulerResidueField v
  obtain ⟨a, b, hxb⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hyd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbd : b.1 * d.1 ∉ v.asIdeal := by
    intro hmem
    rcases v.isPrime.mem_or_mem hmem with hb | hd
    · exact b.2 hb
    · exact d.2 hd
  have hsumrep : (x + y) * algebraMap (𝓞 F) F (b.1 * d.1) =
      algebraMap (𝓞 F) F (a * d.1 + c * b.1) := by
    calc
      (x + y) * algebraMap (𝓞 F) F (b.1 * d.1) =
          x * algebraMap (𝓞 F) F b.1 * algebraMap (𝓞 F) F d.1 +
            y * algebraMap (𝓞 F) F d.1 * algebraMap (𝓞 F) F b.1 := by
        rw [map_mul]
        ring
      _ = algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F d.1 +
            algebraMap (𝓞 F) F c * algebraMap (𝓞 F) F b.1 := by
        rw [hxb, hyd]
      _ = algebraMap (𝓞 F) F (a * d.1 + c * b.1) := by
        rw [map_add, map_mul, map_mul]
  have hbnot : b.1 ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp b.property
  have hdnot : d.1 ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp d.property
  have hbq : Ideal.Quotient.mk v.asIdeal b.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hbnot
  have hdq : Ideal.Quotient.mk v.asIdeal d.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hdnot
  calc
    residue v (x + y) = Ideal.Quotient.mk v.asIdeal (a * d.1 + c * b.1) /
        Ideal.Quotient.mk v.asIdeal (b.1 * d.1) :=
      euler_residue_rep v (x + y) (a * d.1 + c * b.1) (b.1 * d.1) hbd hsumrep
    _ = residue v x + residue v y := by
      rw [euler_residue_rep v x a b.1 hbnot hxb,
        euler_residue_rep v y c d.1 hdnot hyd]
      simp only [map_add, map_mul]
      field_simp [hbq, hdq]


private lemma euler_span_singleton_eq_of_generators (v : FinPlace F) (hv : v ∉ S.Sf)
    (I : Ideal (𝓞 F)) (x y : S.R)
    (hx : S.IsGen (x : F) I) (hy : S.IsGen (y : F) I) :
    Ideal.span ({x} : Set S.R) = Ideal.span {y} := by
  classical
  rcases euler_generators_unit_ratio I (x : F) (y : F) hx hy with ⟨u, hu⟩
  let uR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F u
  have huF : (uR : F) = (u : Fˣ) := rfl
  have hrel : x = uR * y := by
    apply Subtype.ext
    change (x : F) = (uR : F) * (y : F)
    rw [huF]
    exact hu
  calc
    Ideal.span ({x} : Set S.R) = Ideal.span {uR * y} := by rw [hrel]
    _ = Ideal.span {y} := Ideal.span_singleton_mul_left_unit uR.isUnit y


private lemma euler_prime_power_associated (v : FinPlace F) (hv : v ∉ S.Sf) (k : ℕ) :
    ∃ (u : S.US) (c : S.Rˣ),
      (primeGen R v : F) ^ k = (c : F) *
        (R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k) : F) := by
  classical
  let pi := R.exterior.prime v hv
  let I := R.exterior.pow pi k
  let p := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  have hIideal : I.1 = v.asIdeal ^ k := by
    change (R.exterior.pow pi k).1 = _
    rw [R.exterior.pow_val, R.exterior.prime_val]
  have hIcoerce : (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k := by
    calc
      (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          ((v.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        congrArg (fun J : Ideal (𝓞 F) =>
          (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hIideal
      _ = (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k :=
        FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 F)) F v.asIdeal k
  have hpPow : S.IsGen ((p : F) ^ k) I.1 := by
    refine ⟨I.2, pow_ne_zero k hp.2.1, ?_⟩
    intro w hw
    have hsp : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((p : F) ^ k)) =
        (k : ℤ) * FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) := by
      rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
    calc
      FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((p : F) ^ k)) =
          (k : ℤ) * FractionalIdeal.count F w
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) := hsp
      _ = (k : ℤ) * FractionalIdeal.count F w
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [hp.2.2 w hw]
      _ = FractionalIdeal.count F w
            ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k) := by
          rw [FractionalIdeal.count_pow]
      _ = FractionalIdeal.count F w
            (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by rw [← hIcoerce]
  have hgen : S.IsGen (R.exterior.genR I : F) I.1 := by
    rw [R.exterior.genR_val I]
    exact (bc.gen_spec I).1
  rcases euler_generators_unit_ratio I.1 ((p : F) ^ k)
      (R.exterior.genR I : F) hpPow hgen with ⟨u, hu⟩
  let c : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F u
  have hcF : (c : F) = (u : Fˣ) := rfl
  refine ⟨u, c, ?_⟩
  change (p : F) ^ k = (c : F) * (R.exterior.genR I : F)
  rw [hcF]
  exact hu


private lemma euler_prime_power_quotient_generator (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : ℕ) :
    ∃ (u : S.US) (c : S.Rˣ) (pR : S.R),
      (primeGen R v : F) ^ k = (pR : F) ∧
      pR = (c : S.R) * R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k) := by
  obtain ⟨u, c, hc⟩ := euler_prime_power_associated R v hv k
  refine ⟨u, c, (c : S.R) *
    R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k), ?_, rfl⟩
  exact hc


private lemma euler_power_divisibility_iff (p : Fˣ) (k : ℕ) (pR : S.R)
    (hpR : (p : F) ^ k = (pR : F)) (A0 : S.R) :
    (∃ x : S.R, (A0 : F) = (p : F) ^ k * (x : F)) ↔
      A0 ∈ Ideal.span ({pR} : Set S.R) := by
  constructor
  · rintro ⟨x, hx⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (A0 : F) = (pR : F) * (x : F)
    rw [← hpR]
    exact hx
  · intro hA
    rcases Ideal.mem_span_singleton.mp hA with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hxF : (A0 : F) = (pR : F) * (x : F) := congrArg (fun z : S.R => (z : F)) hx
    simpa [← hpR] using hxF


private lemma euler_residue_card_pow (v : FinPlace F) (hv : v ∉ S.Sf) (k : ℕ) :
    @Fintype.card (ResidueRing R.exterior
      (R.exterior.pow (R.exterior.prime v hv) k))
      (R.exterior.residueFinite (R.exterior.pow (R.exterior.prime v hv) k)) =
      Ideal.absNorm v.asIdeal ^ k := by
  let pi := R.exterior.prime v hv
  let I := R.exterior.pow pi k
  have hI : I.1 = v.asIdeal ^ k := by
    change (R.exterior.pow pi k).1 = _
    rw [R.exterior.pow_val, R.exterior.prime_val]
  calc
    @Fintype.card _ (R.exterior.residueFinite I) = Ideal.absNorm I.1 :=
      R.exterior.residue_card I
    _ = Ideal.absNorm (v.asIdeal ^ k) := by rw [hI]
    _ = Ideal.absNorm v.asIdeal ^ k := map_pow Ideal.absNorm v.asIdeal k


private lemma euler_addchar_one_of_S_R (v : FinPlace F) (hv : v ∉ S.Sf) (x : S.R) :
    A.ψ v (algebraMap F (v.adicCompletion F) (x : F)) = 1 := by
  have hxval : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hv
  have hxint : algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
    change ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxval
  exact A.integral v _ hxint


private lemma euler_primeGen_valuation (v : FinPlace F) (hv : v ∉ S.Sf) :
    HeightOneSpectrum.valuation F v (primeGen R v : F) = WithZero.exp (-1 : ℤ) := by
  let pi := R.exterior.prime v hv
  let p := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := euler_count_spanSingleton_eq_neg_log_valuation v (p : F) hp.2.1
    rw [hcount] at h
    linarith
  have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hp.2.1
  calc
    HeightOneSpectrum.valuation F v (p : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
      (WithZero.exp_log hpvalne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]


private lemma euler_residueRing_bijective (v : FinPlace F) (hv : v ∉ S.Sf) :
    ∃ f : ResidueRing R.exterior (R.exterior.prime v hv) → 𝓞 F ⧸ v.asIdeal,
      Function.Bijective f ∧ ∀ a : S.R,
        f (Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.prime v hv)}) a) =
          residue v (a : F) := by
  classical
  let pi := R.exterior.prime v hv
  let g := R.exterior.genR pi
  letI : Fintype (ResidueRing R.exterior pi) := R.exterior.residueFinite pi
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let rho : S.R →+* (𝓞 F ⧸ v.asIdeal) := by
    refine {
      toFun := fun x => residue v (x : F)
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
    · simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (1 : 𝓞 F)
    · intro x y
      exact (a2_bridge_SYMBOL D S).residue_mul v (x : F) (y : F)
        (x.property v hv) (y.property v hv)
    · simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
    · intro x y
      exact euler_residue_add_integral v (x : F) (y : F)
        (x.property v hv) (y.property v hv)
  let SB : SymbolBridge D S := a2_bridge_SYMBOL D S
  have hp : S.IsGen (primeGen R v : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [pi, primeGen, hv, R.exterior.prime_val] using h
  have hg : S.IsGen (g : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [g, pi, R.exterior.genR_val, R.exterior.prime_val] using h
  obtain ⟨u, hu⟩ := euler_generators_unit_ratio v.asIdeal
    (primeGen R v : F) (g : F) hp hg
  have huVal : HeightOneSpectrum.valuation F v (u : Fˣ) = 1 := u.property v hv
  have hvalpg : HeightOneSpectrum.valuation F v (primeGen R v : F) =
      HeightOneSpectrum.valuation F v (u : Fˣ) * HeightOneSpectrum.valuation F v (g : F) := by
    calc
      _ = HeightOneSpectrum.valuation F v ((u : Fˣ) * (g : F)) := by rw [hu]
      _ = _ := (v.valuation F).map_mul _ _
  have hvalg : HeightOneSpectrum.valuation F v (g : F) =
      WithZero.exp (-1 : ℤ) := by
    rw [huVal, one_mul] at hvalpg
    rw [← hvalpg]
    exact euler_primeGen_valuation R v hv
  have hvalgLt : HeightOneSpectrum.valuation F v (g : F) < 1 := by
    rw [hvalg]
    simp
  have hresg : residue v (g : F) = 0 := by
    by_contra hne
    have hvalone := (SB.residue_ne_zero v (g : F) hvalgLt.le).mp hne
    exact (ne_of_lt hvalgLt) hvalone
  have hIle : Ideal.span ({g} : Set S.R) ≤ RingHom.ker rho := by
    rw [Ideal.span_singleton_le_iff_mem]
    change rho g = 0
    exact hresg
  have hIzero : ∀ a : S.R, a ∈ Ideal.span ({g} : Set S.R) → rho a = 0 := by
    intro a ha
    have h : a ∈ RingHom.ker rho := hIle ha
    simpa using h
  let f : ResidueRing R.exterior pi →+* (𝓞 F ⧸ v.asIdeal) :=
    Ideal.Quotient.lift (Ideal.span {g}) rho hIzero
  have hsurj : Function.Surjective f := by
    intro z
    let a : S.R := ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
    refine ⟨Ideal.Quotient.mk (Ideal.span {g}) a, ?_⟩
    change Ideal.Quotient.lift (Ideal.span {g}) rho hIzero
      (Ideal.Quotient.mk (Ideal.span {g}) a) = z
    rw [Ideal.Quotient.lift_mk]
    change residue v (a : F) = z
    simpa [a] using SB.residue_algebraMap v z.out
  have hcardQ : Fintype.card (ResidueRing R.exterior pi) = Ideal.absNorm v.asIdeal := by
    calc
      Fintype.card (ResidueRing R.exterior pi) = Ideal.absNorm pi.1 := R.exterior.residue_card pi
      _ = Ideal.absNorm v.asIdeal := by rw [R.exterior.prime_val]
  have hcardO : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcardQ.trans hcardO.symm⟩
  refine ⟨f, hbij, ?_⟩
  intro a
  change (Ideal.Quotient.lift (Ideal.span {g}) rho hIzero)
      (Ideal.Quotient.mk (Ideal.span {g}) a) = residue v (a : F)
  rw [Ideal.Quotient.lift_mk]
  rfl


private lemma euler_primePower_reduction (v : FinPlace F) (hv : v ∉ S.Sf) (t : ℕ)
    (ht : 0 < t) :
    ∃ rho : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v hv) t) →+*
        ResidueRing R.exterior (R.exterior.prime v hv),
      Function.Surjective rho ∧ ∀ a : S.R,
        rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) t)}) a) =
          Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.prime v hv)}) a := by
  classical
  let pi := R.exterior.prime v hv
  let It := R.exterior.pow pi t
  let I1 := pi
  let gt := R.exterior.genR It
  let g1 := R.exterior.genR I1
  obtain ⟨_, ct, pt, hpt, hptgen⟩ := euler_prime_power_quotient_generator R v hv t
  obtain ⟨_, c1, p1, hp1, hp1gen⟩ := euler_prime_power_quotient_generator R v hv 1
  obtain ⟨_, _, pm, hpm, _⟩ := euler_prime_power_quotient_generator R v hv (t - 1)
  have hptmul : pt = p1 * pm := by
    apply Subtype.ext
    change (pt : F) = (p1 : F) * (pm : F)
    rw [← hpt, ← hp1, ← hpm]
    have he : 1 + (t - 1) = t := by omega
    calc
      (primeGen R v : F) ^ t = (primeGen R v : F) ^ (1 + (t - 1)) := by rw [he]
      _ = (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (t - 1) := by rw [pow_add]
  have hspanT : Ideal.span ({pt} : Set S.R) = Ideal.span {gt} := by
    rw [hptgen]
    exact Ideal.span_singleton_mul_left_unit ct.isUnit gt
  have hgenP : S.IsGen (primeGen R v : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [pi, primeGen, hv, R.exterior.prime_val] using h
  have hp1eq : (p1 : F) = (primeGen R v : F) := by simpa using hp1.symm
  have hgenP1 : S.IsGen (p1 : F) v.asIdeal := by rw [hp1eq]; exact hgenP
  have hgenG1 : S.IsGen (g1 : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [g1, pi, R.exterior.genR_val, R.exterior.prime_val] using h
  have hspan1 : Ideal.span ({p1} : Set S.R) = Ideal.span {g1} := by
    exact euler_span_singleton_eq_of_generators v hv v.asIdeal p1 g1 hgenP1 hgenG1
  have hdiv : p1 ∣ pt := ⟨pm, hptmul⟩
  have hle : Ideal.span ({gt} : Set S.R) ≤ Ideal.span {g1} := by
    calc
      Ideal.span ({gt} : Set S.R) = Ideal.span {pt} := hspanT.symm
      _ ≤ Ideal.span {p1} := Ideal.span_singleton_le_span_singleton.mpr hdiv
      _ = Ideal.span {g1} := hspan1
  let rho : ResidueRing R.exterior It →+* ResidueRing R.exterior I1 :=
    Ideal.quotientMap (Ideal.span {g1}) (RingHom.id S.R) hle
  have hsurj : Function.Surjective rho := by
    change Function.Surjective
      (Ideal.quotientMap (Ideal.span {g1}) (RingHom.id S.R) hle)
    exact Ideal.quotientMap_surjective (f := RingHom.id S.R) (H := hle)
      (fun x => ⟨x, rfl⟩)
  refine ⟨rho, hsurj, ?_⟩
  intro a
  exact Ideal.quotientMap_mk (J := Ideal.span {gt}) (I := Ideal.span {g1})
    (f := RingHom.id S.R) (H := hle) (x := a)


private lemma euler_addHom_fiber_card {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = 0} := by
  classical
  obtain ⟨x₀, hx₀⟩ := hf b
  let e : {x : A // f x = b} ≃ {x : A // f x = 0} := {
    toFun := fun x => ⟨x.1 - x₀, by simp [map_sub, x.2, hx₀]⟩
    invFun := fun x => ⟨x.1 + x₀, by simp [map_add, x.2, hx₀]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp [add_sub_cancel_right]
    right_inv := by
      intro x
      apply Subtype.ext
      simp [sub_add_cancel]
  }
  exact Fintype.card_congr e


private lemma euler_addHom_card_eq_card_mul_fiber {A B : Type}
    [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Fintype.card A = Fintype.card B * Fintype.card {x : A // f x = 0} := by
  calc
    Fintype.card A = ∑ x : A, (1 : ℕ) := Fintype.card_eq_sum_ones
    _ = ∑ b : B, ∑ x : {x : A // f x = b}, (1 : ℕ) :=
      (Fintype.sum_fiberwise (fun x : A => f x) (fun _ => (1 : ℕ))).symm
    _ = ∑ b : B, Fintype.card {x : A // f x = b} := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (Fintype.card_eq_sum_ones (α := {x : A // f x = b})).symm
    _ = ∑ b : B, Fintype.card {x : A // f x = 0} := by
      apply Finset.sum_congr rfl
      intro b hb
      exact euler_addHom_fiber_card f hf b
    _ = Fintype.card B * Fintype.card {x : A // f x = 0} := by simp


private lemma euler_sum_fiberwise_const {A B M : Type} [Fintype A] [Fintype B]
    [AddCommMonoid M] (rho : A → B) (hrho : Function.Surjective rho)
    (g : A → M) (hg : ∀ x y, rho x = rho y → g x = g y) :
    ∑ x : A, g x = ∑ b : B,
      Fintype.card {x : A // rho x = b} • g (Classical.choose (hrho b)) := by
  classical
  rw [← Fintype.sum_fiberwise rho g]
  apply Finset.sum_congr rfl
  intro b hb
  let x₀ := Classical.choose (hrho b)
  have hx₀ : rho x₀ = b := Classical.choose_spec (hrho b)
  calc
    (∑ x : {x : A // rho x = b}, g x.1) =
        ∑ x : {x : A // rho x = b}, g x₀ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hg x.1 x₀ (x.2.trans hx₀.symm)
    _ = Fintype.card {x : A // rho x = b} • g x₀ := by simp


private lemma euler_residue_zero_valuation_bound (D : FieldData F)
    (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : S.R) (hx : residue v (x : F) = 0) :
    HeightOneSpectrum.valuation F v (x : F) ≤ WithZero.exp (-1 : ℤ) := by
  let SB := a2_bridge_SYMBOL D S
  have hxval : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hv
  by_cases hx0 : (x : F) = 0
  · simp [hx0]
  · have hxneVal : HeightOneSpectrum.valuation F v (x : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hx0
    have hxneOne : HeightOneSpectrum.valuation F v (x : F) ≠ 1 := by
      intro hxone
      have hresne := (SB.residue_ne_zero v (x : F) hxval).mpr hxone
      rw [hx] at hresne
      exact hresne rfl
    have hloglt : WithZero.log (HeightOneSpectrum.valuation F v (x : F)) < 0 := by
      have h := (WithZero.log_lt_log hxneVal (by simp : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).2
        (lt_of_le_of_ne hxval hxneOne)
      simpa using h
    have hlogle : WithZero.log (HeightOneSpectrum.valuation F v (x : F)) ≤ -1 := by omega
    exact (WithZero.log_le_iff_le_exp hxneVal).mp hlogle


private lemma euler_chiPow_residue_congr (D : FieldData F)
    (S : SData F CE condη) (v : FinPlace F)
    (x y : F) (e : ℤ) (hres : residue v x = residue v y) :
    chiPow D v x e = chiPow D v y e := by
  by_cases hx : residue v x = 0
  · have hy : residue v y = 0 := by rw [← hres, hx]
    simp [chiPow, hx, hy]
  · have hy : residue v y ≠ 0 := by rw [← hres]; exact hx
    rw [chiPow, if_neg hx, chiPow, if_neg hy]
    rw [(a2_bridge_SYMBOL D S).chi_congr v x y hres]


private lemma euler_addchar_congr_integral (A : AddCharData F) (v : FinPlace F) (x y : F)
    (hxy : HeightOneSpectrum.valuation F v (x - y) ≤ 1) :
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
      A.ψ v (algebraMap F (v.adicCompletion F) y) := by
  have hInt : algebraMap F (v.adicCompletion F) (x - y) ∈ v.adicCompletionIntegers F := by
    change ((x - y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxy
  have hψdiff := A.integral v (algebraMap F (v.adicCompletion F) (x - y)) hInt
  have hψy : A.ψ v (algebraMap F (v.adicCompletion F) y) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v) (algebraMap F (v.adicCompletion F) y)).ne_zero
  have harg : algebraMap F (v.adicCompletion F) (x - y) =
      algebraMap F (v.adicCompletion F) x - algebraMap F (v.adicCompletion F) y := by simp
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) x) (algebraMap F (v.adicCompletion F) y)
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
        (A.ψ v (algebraMap F (v.adicCompletion F) x) /
          A.ψ v (algebraMap F (v.adicCompletion F) y)) *
            A.ψ v (algebraMap F (v.adicCompletion F) y) :=
      (div_mul_cancel₀ _ hψy).symm
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (x - y)) *
          A.ψ v (algebraMap F (v.adicCompletion F) y) := by
      rw [← hdiv, ← harg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) y) := by rw [hψdiff, one_mul]


private lemma euler_addchar_div_residue_congr (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ)
    (hpVal : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (x y : S.R) (hres : residue v (x : F) = residue v (y : F)) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((x : F) / (p : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((y : F) / (p : F))) := by
  have hresDiff : residue v ((x : F) - (y : F)) = 0 := by
    have hadd := euler_residue_add_integral v
      ((x : F) - (y : F)) (y : F)
      ((x - y).property v hv) (y.property v hv)
    have hident : ((x : F) - (y : F)) + (y : F) = (x : F) := by ring
    rw [hident] at hadd
    have hcancel : residue v ((x : F) - (y : F)) + residue v (y : F) =
        0 + residue v (y : F) := by
      calc
        _ = residue v (x : F) := hadd.symm
        _ = residue v (y : F) := hres
        _ = 0 + residue v (y : F) := by simp
    exact add_right_cancel hcancel
  have hvalDiff := euler_residue_zero_valuation_bound D v hv (x - y) hresDiff
  have hpPos : 0 < HeightOneSpectrum.valuation F v (p : F) := by
    rw [hpVal]
    exact lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  have harg : (x : F) / (p : F) - (y : F) / (p : F) =
      ((x : F) - (y : F)) / (p : F) := by field_simp [Units.ne_zero p]
  have hval : HeightOneSpectrum.valuation F v
      ((x : F) / (p : F) - (y : F) / (p : F)) ≤ 1 := by
    rw [harg, map_div₀]
    exact (div_le_one₀ hpPos).2 (by rw [hpVal]; exact hvalDiff)
  exact euler_addchar_congr_integral A v ((x : F) / (p : F))
    ((y : F) / (p : F)) hval


private lemma euler_localT_norm_le (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (y : S.R) : ‖localT R v e (y : F)‖ ≤ qI v.asIdeal := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let p : Fˣ := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v hv)).1
    simpa [p, primeGen, hv, R.exterior.prime_val] using h
  obtain ⟨_, _, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  let SB := a2_bridge_SYMBOL D S
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
    ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
  have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue a : S.R) : F) = a := by
    change residue v (algebraMap (𝓞 F) F a.out) = a
    calc
      _ = Ideal.Quotient.mk v.asIdeal a.out := SB.residue_algebraMap v a.out
      _ = a := Ideal.Quotient.mk_out a
  have hψnorm (a : 𝓞 F ⧸ v.asIdeal) : ‖ψ a‖ = 1 := by
    have hzero : addOrderOf a • a = 0 := addOrderOf_nsmul_eq_zero a
    have hpow : ψ a ^ addOrderOf a = 1 := by
      rw [← ψ.map_nsmul_eq_pow]
      rw [hzero, ψ.map_zero_eq_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpow (addOrderOf_pos a).ne'
  let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
  have hphase (x : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
      ψ (a * -x) := by
    let targetR : S.R := -(y * liftResidue x)
    let finiteR : S.R := liftResidue (-x) * liftResidue a
    have hresMul : residue v ((y * liftResidue x : S.R) : F) = a * x := by
      change residue v ((y : F) * (liftResidue x : F)) = a * x
      rw [SB.residue_mul v (y : F) (liftResidue x : F)
        (y.property v hv) ((liftResidue x).property v hv), hresLift]
    have hresZero : residue v (0 : F) = 0 := by
      simpa using SB.residue_algebraMap v (0 : 𝓞 F)
    have hresTarget : residue v (targetR : F) = -(a * x) := by
      have hadd := euler_residue_add_integral v
        (targetR : F) ((y * liftResidue x : S.R) : F)
        (targetR.property v hv) ((y * liftResidue x).property v hv)
      have hident : (targetR : F) + (y * liftResidue x : S.R) = 0 := by
        dsimp [targetR]
        ring
      rw [hident, hresZero, hresMul] at hadd
      exact eq_neg_iff_add_eq_zero.mpr hadd.symm
    have hresFinite : residue v (finiteR : F) = -(a * x) := by
      change residue v ((liftResidue (-x) : S.R) * (liftResidue a : S.R) : F) = _
      rw [SB.residue_mul v (liftResidue (-x) : F) (liftResidue a : F)
        ((liftResidue (-x)).property v hv) ((liftResidue a).property v hv),
        hresLift, hresLift]
      dsimp [a]
      ring
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = -(a * x) := hresTarget
        _ = residue v (finiteR : F) := hresFinite.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval a (-x)
    have htarget : (targetR : F) =
        -((y : F) * algebraMap (𝓞 F) F x.out) := by
      simp [targetR, liftResidue]
    have hfinite : (finiteR : F) =
        algebraMap (𝓞 F) F (-x).out * algebraMap (𝓞 F) F a.out := by
      simp [finiteR, liftResidue]
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        congr 1
        rw [htarget]
        ring
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ (a * -x) := by simpa [p, hfinite] using heval.symm
  have hfinite : localT R v e (y : F) =
      ∑ x : 𝓞 F ⧸ v.asIdeal,
        chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hphase]
  have hterm (x : 𝓞 F ⧸ v.asIdeal) :
      ‖chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (SB.chiPow_norm_le v _ e)
        (hψnorm _).le (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  calc
    ‖localT R v e (y : F)‖ =
        ‖∑ x : 𝓞 F ⧸ v.asIdeal,
          chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ :=
      congrArg norm hfinite
    _ ≤ ∑ x : 𝓞 F ⧸ v.asIdeal,
          ‖chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : 𝓞 F ⧸ v.asIdeal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hterm x
    _ = Ideal.absNorm v.asIdeal := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp [hcard]
    _ = qI v.asIdeal := by simp [qI]


private lemma euler_localD_gauss_sum (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : S.R) (hx : residue v (x : F) ≠ 0)
    [instQ1 : Fintype (ResidueRing R.exterior (R.exterior.prime v hv))] :
    ∑ d : ResidueRing R.exterior (R.exterior.prime v hv), chiPow D v (d.out : F) 1 *
      A.ψ v (algebraMap F (v.adicCompletion F)
        ((d.out : F) * (x : F) / (primeGen R v : F))) =
      localT R v 1 1 * star (chi D v (x : F)) := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let Q1 := ResidueRing R.exterior pi
  letI : Fintype Q1 := instQ1
  let SB := a2_bridge_SYMBOL D S
  let p : Fˣ := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
  let resEquiv : Q1 ≃ 𝓞 F ⧸ v.asIdeal := Equiv.ofBijective resEq hresEqBij
  obtain ⟨_, hchiSix, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp
  obtain ⟨χ, hχorder, hχeval⟩ := hchiSix
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  let SB := a2_bridge_SYMBOL D S
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
    ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
  have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue z : S.R) : F) = z := by
    change residue v (algebraMap (𝓞 F) F z.out) = z
    calc
      _ = Ideal.Quotient.mk v.asIdeal z.out := SB.residue_algebraMap v z.out
      _ = z := Ideal.Quotient.mk_out z
  let a : 𝓞 F ⧸ v.asIdeal := residue v (x : F)
  have ha : a ≠ 0 := by simpa [a] using hx
  have hresD (d : Q1) : residue v (d.out : F) = resEq d := by
    calc
      residue v (d.out : F) = resEq
          (Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out) :=
        (hresEqMk d.out).symm
      _ = resEq d := by rw [Ideal.Quotient.mk_out d]
  have hchiD (d : Q1) : chiPow D v (d.out : F) 1 = χ (resEq d) := by
    have hres : residue v (d.out : F) =
        residue v ((liftResidue (resEq d) : S.R) : F) := by
      calc
        _ = resEq d := hresD d
        _ = _ := (hresLift (resEq d)).symm
    calc
      chiPow D v (d.out : F) 1 =
          chiPow D v ((liftResidue (resEq d) : S.R) : F) 1 :=
        euler_chiPow_residue_congr D S v (d.out : F)
          ((liftResidue (resEq d) : S.R) : F) 1 hres
      _ = χ (resEq d) := (hχeval (resEq d)).symm
  have hphaseD (d : Q1) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        ((d.out : F) * (x : F) / (p : F))) =
      ψ (resEq d * a) := by
    let targetR : S.R := d.out * x
    let finiteR : S.R := liftResidue a * liftResidue (resEq d)
    have hresTarget : residue v (targetR : F) = (resEq d) * a := by
      calc
        residue v (targetR : F) =
            residue v ((d.out : F) * (x : F)) := rfl
        _ = residue v (d.out : F) * residue v (x : F) :=
          SB.residue_mul v (d.out : F) (x : F)
            ((d.out).property v hv) (x.property v hv)
        _ = (resEq d) * a := by rw [hresD]
    have hresFinite : residue v (finiteR : F) = (resEq d) * a := by
      calc
        residue v (finiteR : F) =
            residue v (liftResidue a : F) *
              residue v (liftResidue (resEq d) : F) :=
          SB.residue_mul v (liftResidue a : F) (liftResidue (resEq d) : F)
            ((liftResidue a).property v hv) ((liftResidue (resEq d)).property v hv)
        _ = a * resEq d := by rw [hresLift, hresLift]
        _ = (resEq d) * a := mul_comm _ _
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = (resEq d) * a := hresTarget
        _ = _ := hresFinite.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval (resEq d) a
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        have harg : (d.out : F) * (x : F) / (p : F) =
            (targetR : F) / (p : F) := rfl
        exact congrArg (fun z : F => A.ψ v (algebraMap F (v.adicCompletion F) z)) harg
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ (resEq d * a) := by
        simpa [finiteR, liftResidue, p] using heval.symm
  have hresidueSum :
      (∑ d : Q1, chiPow D v (d.out : F) 1 *
        A.ψ v (algebraMap F (v.adicCompletion F)
          ((d.out : F) * (x : F) / (p : F)))) =
        ∑ z : 𝓞 F ⧸ v.asIdeal, χ z * ψ (z * a) := by
    exact Fintype.sum_equiv resEquiv _ _ (by
      intro d
      rw [hchiD d, hphaseD d]
      simpa [resEquiv])
  have houterGauss :
      (∑ d : Q1, chiPow D v (d.out : F) 1 *
        A.ψ v (algebraMap F (v.adicCompletion F)
          ((d.out : F) * (x : F) / (p : F)))) =
        gaussSum χ (ψ.mulShift a) := by
    rw [hresidueSum]
    simp [gaussSum, AddChar.mulShift_apply, mul_comm]
  have hTphase (z : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-(algebraMap (𝓞 F) F z.out) / (p : F))) =
      ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
    let targetR : S.R := -liftResidue z
    let finiteR : S.R := liftResidue z * liftResidue (-1)
    have hresNeg : residue v (targetR : F) = -z := by
      have hadd := euler_residue_add_integral v (targetR : F)
        (liftResidue z : F) (targetR.property v hv) ((liftResidue z).property v hv)
      have hident : (targetR : F) + (liftResidue z : S.R) = 0 := by
        dsimp [targetR]
        ring
      have hzero : residue v (0 : F) = 0 := by
        simpa using SB.residue_algebraMap v (0 : 𝓞 F)
      rw [hident, hzero, hresLift] at hadd
      exact eq_neg_iff_add_eq_zero.mpr hadd.symm
    have hresProd : residue v (finiteR : F) = -z := by
      change residue v ((liftResidue z : S.R) *
        (liftResidue (-1) : S.R) : F) = _
      rw [SB.residue_mul v (liftResidue z : F) (liftResidue (-1) : F)
        ((liftResidue z).property v hv) ((liftResidue (-1)).property v hv),
        hresLift, hresLift]
      simp
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = -z := hresNeg
        _ = _ := hresProd.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval (-1 : 𝓞 F ⧸ v.asIdeal) z
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        simpa [targetR, liftResidue]
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
        simpa [finiteR, liftResidue, p] using heval.symm
  have hTone : localT R v 1 1 = gaussSum χ (ψ.mulShift (-1)) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    calc
      _ = ∑ z : 𝓞 F ⧸ v.asIdeal, χ z * ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(hχeval z).symm]
        calc
          _ = χ z * A.ψ v (algebraMap F (v.adicCompletion F)
                ((-(algebraMap (𝓞 F) F z.out)) / (p : F))) := by
            apply congrArg (fun w : F => χ z * A.ψ v (algebraMap F (v.adicCompletion F) w))
            ring
          _ = _ := by rw [hTphase z]
      _ = _ := by simp [gaussSum, AddChar.mulShift_apply]
  have hresMinusAlg : residue v
      (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) = -1 := by
    simpa using SB.residue_algebraMap v ((-1 : 𝓞 F ⧸ v.asIdeal).out)
  have hresMinus : residue v (-1 : F) = -1 := by
    simpa using SB.residue_algebraMap v (-1 : 𝓞 F)
  have hchiMinus : χ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    calc
      χ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 1 :=
        hχeval _
      _ = chiPow D v (-1 : F) 1 :=
        euler_chiPow_residue_congr D S v _ _ 1 (hresMinusAlg.trans hresMinus.symm)
      _ = chi D v (-1 : F) := by
        rw [SB.chiPow_nonzero v (-1 : F) 1 (by rw [hresMinus]; exact neg_ne_zero.mpr one_ne_zero)]
        simp
      _ = 1 := SB.chi_minus_one v hv
  let u : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ha).unit
  have hu : (u : 𝓞 F ⧸ v.asIdeal) = a := (isUnit_iff_ne_zero.mpr ha).unit_spec
  have hshift : ψ.mulShift a = (ψ.mulShift (-1)).mulShift (-u) := by
    ext z
    simp [AddChar.mulShift_apply, hu, mul_assoc]
  have hGaussShift := gaussSum_mulShift_eq χ (ψ.mulShift (-1)) (-u)
  have hchiU : χ u = chi D v (x : F) := by
    have hresU : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
        residue v (x : F) := by
      have hresAlgU : residue v
          (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
            (u : 𝓞 F ⧸ v.asIdeal) := by
        simpa using SB.residue_algebraMap v (u : 𝓞 F ⧸ v.asIdeal).out
      calc
        _ = (u : 𝓞 F ⧸ v.asIdeal) := hresAlgU
        _ = a := hu
        _ = _ := rfl
    calc
      χ u = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 := hχeval u
      _ = chiPow D v (x : F) 1 :=
        euler_chiPow_residue_congr D S v _ _ 1 hresU
      _ = chi D v (x : F) := by
        rw [SB.chiPow_nonzero v (x : F) 1 hx]
        simp
  have hchiMinusUnit : χ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
    simpa using hchiMinus
  have hchiNegU : χ (-u) = chi D v (x : F) := by
    calc
      χ (-u) = χ ((-1 : (𝓞 F ⧸ v.asIdeal)ˣ) * u) := by congr 1 <;> simp
      _ = χ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) * χ u := map_mul χ _ _
      _ = chi D v (x : F) := by rw [hchiMinusUnit, hchiU]; simp
  have hchiInv : χ⁻¹ (-u) = star (chi D v (x : F)) := by
    calc
      χ⁻¹ (-u) = (χ (-u))⁻¹ := MulChar.inv_apply_eq_inv' χ _
      _ = (chi D v (x : F))⁻¹ := by rw [hchiNegU]
      _ = star (chi D v (x : F)) := Complex.inv_eq_conj (SB.chi_norm v _ hx)
  calc
    _ = gaussSum χ (ψ.mulShift a) := houterGauss
    _ = χ⁻¹ (-u) * gaussSum χ (ψ.mulShift (-1)) := by
      rw [hshift]
      exact hGaussShift
    _ = localT R v 1 1 * star (chi D v (x : F)) := by
      rw [hchiInv, ← hTone]
      ring


private lemma euler_localFactor_residue_congr
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (v : FinPlace F) (hv : v ∉ S.Sf) (y x₁ x₂ : S.R) (e : ℤ)
    (hres : residue v (x₁ : F) = residue v (x₂ : F)) :
    chiPow D v (x₁ : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x₁ : F) / (primeGen R v : F)))) =
    chiPow D v (x₂ : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x₂ : F) / (primeGen R v : F)))) := by
  have hresDiff : residue v ((x₁ : F) - (x₂ : F)) = 0 := by
    have hsum := euler_residue_add_integral v
      ((x₁ : F) - (x₂ : F)) (x₂ : F)
      ((x₁ - x₂).property v hv) (x₂.property v hv)
    have hident : ((x₁ : F) - (x₂ : F)) + (x₂ : F) = (x₁ : F) := by ring
    rw [hident] at hsum
    have hsum' : residue v ((x₁ : F) - (x₂ : F)) + residue v (x₂ : F) =
        0 + residue v (x₂ : F) := by
      simpa using hsum.symm.trans hres
    exact add_right_cancel hsum'
  have hvalDiff := euler_residue_zero_valuation_bound D v hv (x₁ - x₂) hresDiff
  have hyVal : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
  have hvalProd : HeightOneSpectrum.valuation F v
      ((y : F) * ((x₁ : F) - (x₂ : F))) ≤ WithZero.exp (-1 : ℤ) := by
    rw [(v.valuation F).map_mul]
    calc
      HeightOneSpectrum.valuation F v (y : F) *
          HeightOneSpectrum.valuation F v ((x₁ : F) - (x₂ : F)) ≤
          1 * WithZero.exp (-1 : ℤ) :=
        mul_le_mul hyVal hvalDiff (zero_le) (zero_le)
      _ = WithZero.exp (-1 : ℤ) := one_mul _
  have hpVal := euler_primeGen_valuation R v hv
  have hpPos : 0 < HeightOneSpectrum.valuation F v (primeGen R v : F) := by
    rw [hpVal]
    exact lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  have harg : -((y : F) * (x₁ : F) / (primeGen R v : F)) -
      -((y : F) * (x₂ : F) / (primeGen R v : F)) =
        -((y : F) * ((x₁ : F) - (x₂ : F)) / (primeGen R v : F)) := by
    field_simp [Units.ne_zero (primeGen R v)]
    ring
  have hargVal : HeightOneSpectrum.valuation F v
      (-((y : F) * (x₁ : F) / (primeGen R v : F)) -
        -((y : F) * (x₂ : F) / (primeGen R v : F))) ≤ 1 := by
    rw [harg, (v.valuation F).map_neg, map_div₀]
    exact (div_le_one₀ hpPos).2 (by rw [hpVal]; exact hvalProd)
  have hpsi := euler_addchar_congr_integral A v
      (-((y : F) * (x₁ : F) / (primeGen R v : F)))
      (-((y : F) * (x₂ : F) / (primeGen R v : F))) hargVal
  have hchi := euler_chiPow_residue_congr D S v (x₁ : F) (x₂ : F) e hres
  rw [hchi, hpsi]


private lemma euler_primePower_localT_sum (v : FinPlace F) (hv : v ∉ S.Sf)
    (t : ℕ) (ht : 0 < t) (e : ℤ) (y : S.R)
    [instQt : Fintype (ResidueRing R.exterior
      (R.exterior.pow (R.exterior.prime v hv) t))] :
    let pi := R.exterior.prime v hv
    let It := R.exterior.pow pi t
    let Qt := ResidueRing R.exterior It
    letI : Fintype Qt := instQt
    ∑ x : Qt,
      chiPow D v (x.out : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * (x.out : F) / (primeGen R v : F) ^ 1))) =
      (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v e (y : F) := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let It := R.exterior.pow pi t
  let Qt := ResidueRing R.exterior It
  let Q1 := ResidueRing R.exterior pi
  letI : Fintype Qt := instQt
  letI : Fintype Q1 := R.exterior.residueFinite pi
  obtain ⟨rho, hrho, hrhoMk⟩ := euler_primePower_reduction R v hv t ht
  have hcardQt : @Fintype.card Qt instQt = Ideal.absNorm v.asIdeal ^ t := by
    have hinst : instQt = R.exterior.residueFinite It := Subsingleton.elim _ _
    calc
      @Fintype.card Qt instQt = @Fintype.card Qt (R.exterior.residueFinite It) := by
        rw [hinst]
      _ = Ideal.absNorm v.asIdeal ^ t := by
        simpa [Qt, It, pi] using euler_residue_card_pow R v hv t
  have hcardQ1 : @Fintype.card Q1 (R.exterior.residueFinite pi) =
      Ideal.absNorm v.asIdeal := by
    change @Fintype.card _ (R.exterior.residueFinite pi) = _
    rw [R.exterior.residue_card, R.exterior.prime_val]
  obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
  have hresReduce (x : Qt) : resEq (rho x) = residue v (x.out : F) := by
    have hxmk : rho x = Ideal.Quotient.mk
        (Ideal.span {R.exterior.genR pi}) x.out := by
      calc
        rho x = rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out) :=
          congrArg rho (Ideal.Quotient.mk_out x).symm
        _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := hrhoMk x.out
    rw [hxmk]
    exact hresEqMk x.out
  let f : Qt →+ Q1 := rho.toAddMonoidHom
  have hcardSum := euler_addHom_card_eq_card_mul_fiber f hrho
  rw [hcardQt, hcardQ1] at hcardSum
  have hpow : Ideal.absNorm v.asIdeal ^ t =
      Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal ^ (t - 1) := by
    have ht' : (t - 1) + 1 = t := by omega
    calc
      _ = Ideal.absNorm v.asIdeal ^ ((t - 1) + 1) :=
        congrArg (fun n : ℕ => Ideal.absNorm v.asIdeal ^ n) ht'.symm
      _ = Ideal.absNorm v.asIdeal ^ (t - 1) * Ideal.absNorm v.asIdeal := by rw [pow_succ]
      _ = _ := Nat.mul_comm _ _
  have hfiber0 : Fintype.card {x : Qt // f x = 0} =
      Ideal.absNorm v.asIdeal ^ (t - 1) := by
    have hqpos : 0 < Ideal.absNorm v.asIdeal :=
      lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
    rw [hpow] at hcardSum
    exact Nat.mul_left_cancel hqpos hcardSum.symm
  have hfiber (b : Q1) : Fintype.card {x : Qt // rho x = b} =
      Ideal.absNorm v.asIdeal ^ (t - 1) := by
    simpa [f] using (euler_addHom_fiber_card f hrho b).trans hfiber0
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
    ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
  have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue z : S.R) : F) = z := by
    change residue v (algebraMap (𝓞 F) F z.out) = z
    calc
      _ = Ideal.Quotient.mk v.asIdeal z.out :=
        (a2_bridge_SYMBOL D S).residue_algebraMap v z.out
      _ = z := Ideal.Quotient.mk_out z
  let G' : (𝓞 F ⧸ v.asIdeal) → ℂ := fun z =>
    chiPow D v ((liftResidue z : S.R) : F) e *
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * ((liftResidue z : S.R) : F) / (primeGen R v : F))))
  let g : Qt → ℂ := fun x =>
    chiPow D v (x.out : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x.out : F) / (primeGen R v : F))))
  have hconst (x₁ x₂ : Qt) (h : rho x₁ = rho x₂) : g x₁ = g x₂ := by
    have hres : residue v (x₁.out : F) = residue v (x₂.out : F) := by
      rw [← hresReduce x₁, h, hresReduce x₂]
    simpa [g] using euler_localFactor_residue_congr R v hv y x₁.out x₂.out e hres
  have hpoint (b : Q1) :
      g (Classical.choose (hrho b)) = G' (resEq b) := by
    let x₀ : Qt := Classical.choose (hrho b)
    have hx₀ : rho x₀ = b := Classical.choose_spec (hrho b)
    have hres : residue v (x₀.out : F) =
        residue v ((liftResidue (resEq b) : S.R) : F) := by
      calc
        _ = resEq (rho x₀) := (hresReduce x₀).symm
        _ = resEq b := by rw [hx₀]
        _ = _ := (hresLift (resEq b)).symm
    simpa [g, G', x₀] using
      euler_localFactor_residue_congr R v hv y x₀.out
        (liftResidue (resEq b)) e hres
  have hfiberSum : ∑ x : Qt, g x =
      ∑ b : Q1,
        Fintype.card {x : Qt // rho x = b} • G' (resEq b) := by
    calc
      _ = ∑ b : Q1,
          Fintype.card {x : Qt // rho x = b} • g (Classical.choose (hrho b)) :=
        euler_sum_fiberwise_const rho hrho g hconst
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hpoint b]
  have hfactor :
      ∑ b : Q1, Fintype.card {x : Qt // rho x = b} • G' (resEq b) =
        (qI v.asIdeal : ℂ) ^ (t - 1) *
          ∑ z : 𝓞 F ⧸ v.asIdeal, G' z := by
    have hcardComplex (b : Q1) :
        (Fintype.card {x : Qt // rho x = b} : ℂ) =
          (qI v.asIdeal : ℂ) ^ (t - 1) := by
      rw [hfiber b]
      simp [qI]
    calc
      _ = ∑ b : Q1,
          (qI v.asIdeal : ℂ) ^ (t - 1) * G' (resEq b) := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          _ = (Fintype.card {x : Qt // rho x = b} : ℂ) * G' (resEq b) := by simp
          _ = _ := by rw [hcardComplex b]
      _ = (qI v.asIdeal : ℂ) ^ (t - 1) *
          ∑ b : Q1, G' (resEq b) := by rw [Finset.mul_sum]
      _ = _ := by
        exact congrArg (fun z : ℂ =>
          (qI v.asIdeal : ℂ) ^ (t - 1) * z)
          (Fintype.sum_equiv (Equiv.ofBijective resEq hresEqBij)
            _ _ (by intro z; rfl))
  have hG : ∑ z : 𝓞 F ⧸ v.asIdeal, G' z = localT R v e (y : F) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
  calc
    _ = ∑ x : Qt, g x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [g, pow_one]
    _ = (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v e (y : F) := by
      rw [hfiberSum, hfactor, hG]


theorem po_C_local_values : ∀ v (hv : v ∉ S.Sf) J,
  localC R v hv 0 0 J = 1 ∧
  (∀ k : ℕ, 0 < k → localC R v hv 0 k J = if J = 0 then 1 else 0) ∧
  (∀ t : ℕ, 0 < t →
    localC R v hv t 0 J = (if t - 1 ≤ J then
      (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v t ((primeGen R v : F) ^ (J + 1 - t)) else 0) ∧
    localC R v hv t 1 J = (if t ≤ J then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
      localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (J - t)) else 0) ∧
    (∀ k : ℕ, 2 ≤ k → localC R v hv t k J = 0) ∧
    ‖localC R v hv t 0 J‖ ≤ qI v.asIdeal ^ (t : ℝ) ∧
    ‖localC R v hv t 1 J‖ ≤ qI v.asIdeal ^ ((t : ℝ) + 1 / 2)) := by
  intro v hv J
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let I0 := R.exterior.pow pi 0
  let Q0 := ResidueRing R.exterior I0
  letI : Fintype Q0 := R.exterior.residueFinite I0
  have hcard0 : Fintype.card Q0 = 1 := by
    have h := euler_residue_card_pow R v hv 0
    simpa [Q0, I0, pi] using h
  letI : Unique Q0 := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hcard0)
  obtain ⟨_, cJ, pRJ, hpJ, hpJgen⟩ := euler_prime_power_quotient_generator R v hv J
  have hcondition (d : Q0) : ∃ x : S.R,
      (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
        (primeGen R v : F) ^ 0 * (x : F) := by
    refine ⟨pRJ - d.out, ?_⟩
    rw [hpJ]
    simp
  have hphase (d x : Q0) : A.ψ v (algebraMap F (v.adicCompletion F)
      (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F)) *
        (x.out : F) / (primeGen R v : F) ^ (0 + 0)))) = 1 := by
    let z : S.R := (pRJ - d.out) * x.out
    have hz : -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F)) *
        (x.out : F) / (primeGen R v : F) ^ (0 + 0)) = (-(z : S.R) : F) := by
      rw [hpJ]
      simp [z]
    rw [hz]
    exact euler_addchar_one_of_S_R v hv (-z)
  have hcase00 : localC R v hv 0 0 J = 1 := by
    let d0 : Q0 := 0
    let x0 : Q0 := 0
    have hcondD := hcondition d0
    unfold localC
    rw [finsum_eq_sum_of_fintype]
    rw [Finset.sum_eq_single_of_mem d0 (Finset.mem_univ _) (by
      intro d hd hne
      exact False.elim (hne (Subsingleton.elim d d0)))]
    split
    · simp only [if_pos (by norm_num : 0 = 0), one_mul]
      rw [finsum_eq_sum_of_fintype]
      rw [Finset.sum_eq_single_of_mem x0 (Finset.mem_univ _) (by
        intro x hx hne
        exact False.elim (hne (Subsingleton.elim x x0)))]
      simpa using hphase d0 x0
    · rename_i hfalse
      exact False.elim (hfalse hcondD)
  let p : Fˣ := primeGen R v
  let SB := a2_bridge_SYMBOL D S
  have hpVal : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    simpa [p] using euler_primeGen_valuation R v hv
  have hpValLt : HeightOneSpectrum.valuation F v (p : F) < 1 := by
    rw [hpVal]
    simp
  have hpValLe : HeightOneSpectrum.valuation F v (p : F) ≤ 1 := hpValLt.le
  have hvalPowLe (n : ℕ) : HeightOneSpectrum.valuation F v ((p : F) ^ n) ≤ 1 := by
    obtain ⟨_, _, pRn, hpRn, _⟩ := euler_prime_power_quotient_generator R v hv n
    rw [hpRn]
    exact pRn.property v hv
  have hvalPowLt (n : ℕ) (hn : 0 < n) :
      HeightOneSpectrum.valuation F v ((p : F) ^ n) < 1 := by
    rw [(v.valuation F).map_pow]
    exact pow_lt_one₀ zero_le hpValLt hn.ne'
  have hresOne : residue v (1 : F) = 1 := by
    simpa using SB.residue_algebraMap v (1 : 𝓞 F)
  have hresPow : ∀ n : ℕ, residue v ((p : F) ^ n) = residue v (p : F) ^ n := by
    intro n
    induction n with
    | zero => simp [hresOne]
    | succ n ih =>
      calc
        residue v ((p : F) ^ (n + 1)) =
            residue v ((p : F) ^ n * (p : F)) := by rw [pow_succ]
        _ = residue v ((p : F) ^ n) * residue v (p : F) :=
          SB.residue_mul v _ _ (hvalPowLe n) hpValLe
        _ = residue v (p : F) ^ n * residue v (p : F) := by rw [ih]
        _ = residue v (p : F) ^ (n + 1) := by rw [pow_succ]
  have hresPzero : residue v (p : F) = 0 := by
    by_contra hne
    have hvalOne := (SB.residue_ne_zero v (p : F) hpValLe).mp hne
    have hexpOne : WithZero.exp (-1 : ℤ) = 1 := hpVal.symm.trans hvalOne
    have hlog := congrArg WithZero.log hexpOne
    simp at hlog
  have hresPowZero (n : ℕ) (hn : 0 < n) : residue v ((p : F) ^ n) = 0 := by
    rw [hresPow, hresPzero]
    simp [hn.ne']
  have hchiOne : chi D v (1 : F) = 1 := by
    have hresne : residue v (1 : F) ≠ 0 := by rw [hresOne]; exact one_ne_zero
    have hnorm := SB.chi_norm v (1 : F) hresne
    have hχne : chi D v (1 : F) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hnorm]
      norm_num
    have hmul := SB.chi_mul v hv (1 : F) 1
      (v.valuation_le_one (1 : 𝓞 F)) (v.valuation_le_one (1 : 𝓞 F))
    have hmul' : chi D v (1 : F) * 1 = chi D v (1 : F) * chi D v (1 : F) := by
      simpa using hmul
    exact (mul_left_cancel₀ hχne hmul').symm
  constructor
  · exact hcase00
  · constructor
    · intro k hk
      let Ik := R.exterior.pow pi k
      let Qk := ResidueRing R.exterior Ik
      letI : Fintype Qk := R.exterior.residueFinite Ik
      obtain ⟨_, cK, pRK, hpK, hpKgen⟩ := euler_prime_power_quotient_generator R v hv k
      let gK := R.exterior.genR Ik
      have hspanK : Ideal.span ({pRK} : Set S.R) = Ideal.span {gK} := by
        rw [hpKgen]
        exact Ideal.span_singleton_mul_left_unit cK.isUnit gK
      let d0 : Qk := Ideal.Quotient.mk (Ideal.span {gK}) pRJ
      have hdivMem (d : Qk) :
          (∃ x : S.R, (pRJ : F) - (d.out : F) = (p : F) ^ k * (x : F)) ↔
            (pRJ - d.out) ∈ Ideal.span {gK} := by
        have h := euler_power_divisibility_iff p k pRK hpK (pRJ - d.out)
        rw [hspanK] at h
        exact h
      have hcondition (d : Qk) :
          (∃ x : S.R, (p : F) ^ J - (d.out : F) = (p : F) ^ k * (x : F)) ↔ d = d0 := by
        have hmem : (∃ x : S.R, (p : F) ^ J - (d.out : F) =
            (p : F) ^ k * (x : F)) ↔ (pRJ - d.out) ∈ Ideal.span {gK} := by
          constructor
          · rintro ⟨x, hx⟩
            apply hdivMem d |>.mp
            exact ⟨x, by rw [← hpJ]; exact hx⟩
          · intro hm
            rcases (hdivMem d).mpr hm with ⟨x, hx⟩
            exact ⟨x, by rw [hpJ]; exact hx⟩
        have hquot : (pRJ - d.out) ∈ Ideal.span {gK} ↔ d = d0 := by
          constructor
          · intro hm
            have hmk : Ideal.Quotient.mk (Ideal.span {gK}) pRJ =
                Ideal.Quotient.mk (Ideal.span {gK}) d.out :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ d.out).2 hm
            calc
              d = Ideal.Quotient.mk (Ideal.span {gK}) d.out := (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {gK}) pRJ := hmk.symm
              _ = d0 := rfl
          · intro hd
            have hmk : Ideal.Quotient.mk (Ideal.span {gK}) pRJ =
                Ideal.Quotient.mk (Ideal.span {gK}) d.out := by
              calc
                Ideal.Quotient.mk (Ideal.span {gK}) pRJ = d0 := rfl
                _ = d := hd.symm
                _ = Ideal.Quotient.mk (Ideal.span {gK}) d.out := (Ideal.Quotient.mk_out d).symm
            exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ d.out).mp hmk
        exact hmem.trans hquot
      have hconditionLocal (d : Qk) :
          (∃ x : S.R, (p : F) ^ J - (p : F) ^ 0 * (d.out : F) =
            (p : F) ^ k * (x : F)) ↔ d = d0 := by
        simpa [pow_zero] using hcondition d
      have hinner (d : Qk) (hd :
          ∃ x : S.R, (p : F) ^ J - (d.out : F) = (p : F) ^ k * (x : F)) :
          ∑ᶠ x : Q0, (if 0 = 0 then 1 else chiPow D v (x.out : F) 0) *
            A.ψ v (algebraMap F (v.adicCompletion F)
              (-(((p : F) ^ J - (p : F) ^ 0 * (d.out : F)) *
                (x.out : F) / (p : F) ^ (k + 0)))) = 1 := by
        obtain ⟨y, hy⟩ := hd
        let x0 : Q0 := 0
        have hphaseK (x : Q0) : A.ψ v (algebraMap F (v.adicCompletion F)
            (-(((p : F) ^ J - (d.out : F)) * (x.out : F) / (p : F) ^ k))) = 1 := by
          let z : S.R := y * x.out
          have hz : -(((p : F) ^ J - (d.out : F)) * (x.out : F) / (p : F) ^ k) =
              (-(z : S.R) : F) := by
            rw [hy]
            field_simp [pow_ne_zero k (Units.ne_zero p)]
            change -((y : F) * (x.out : F)) = -(z : F)
            simp [z]
          rw [hz]
          exact euler_addchar_one_of_S_R v hv (-z)
        rw [finsum_eq_sum_of_fintype]
        rw [Finset.sum_eq_single_of_mem x0 (Finset.mem_univ _) (by
          intro x hx hne
          exact False.elim (hne (Subsingleton.elim x x0)))]
        have hphaseK0 : A.ψ v (algebraMap F (v.adicCompletion F)
            (-(((p : F) ^ J - (p : F) ^ 0 * (d.out : F)) *
              (x0.out : F) / (p : F) ^ (k + 0)))) = 1 := by
          simpa [pow_zero, Nat.add_zero] using hphaseK x0
        simp only [if_pos (by norm_num : 0 = 0), one_mul]
        rw [hphaseK0]
        simp
      have hcond0 : ∃ x : S.R, (p : F) ^ J - (d0.out : F) =
          (p : F) ^ k * (x : F) := (hcondition d0).2 rfl
      have hcond0Local : ∃ x : S.R, (p : F) ^ J - (p : F) ^ 0 * (d0.out : F) =
          (p : F) ^ k * (x : F) := (hconditionLocal d0).2 rfl
      have hchar : chiPow D v (d0.out : F) k = if J = 0 then 1 else 0 := by
        obtain ⟨y, hy⟩ := hcond0
        have hvalDiff : HeightOneSpectrum.valuation F v
            ((p : F) ^ J - (d0.out : F)) < 1 := by
          have hvalY : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
          have hmul : HeightOneSpectrum.valuation F v ((p : F) ^ k * (y : F)) < 1 := by
            rw [(v.valuation F).map_mul]
            by_cases hy0 : HeightOneSpectrum.valuation F v (y : F) = 0
            · rw [hy0, mul_zero]
              exact zero_lt_one
            · have hypos : 0 < HeightOneSpectrum.valuation F v (y : F) :=
                lt_of_le_of_ne (zero_le) (Ne.symm hy0)
              calc
                _ < 1 * HeightOneSpectrum.valuation F v (y : F) :=
                  mul_lt_mul_of_pos_right (hvalPowLt k hk) hypos
                _ ≤ 1 := by simpa using hvalY
          calc
            HeightOneSpectrum.valuation F v ((p : F) ^ J - (d0.out : F)) =
                HeightOneSpectrum.valuation F v ((p : F) ^ k * (y : F)) := by rw [hy]
            _ < 1 := hmul
        have hresEq := SB.residue_congr v ((p : F) ^ J) (d0.out : F)
          (hvalPowLe J) (d0.out.property v hv) hvalDiff
        by_cases hJ : J = 0
        · subst J
          have hresD : residue v (d0.out : F) = 1 := by
            simpa [hresOne] using hresEq.symm
          have hresD' : residue v (d0.out : F) = residue v (1 : F) := by
            calc
              residue v (d0.out : F) = 1 := hresD
              _ = residue v (1 : F) := hresOne.symm
          have hχD : chi D v (d0.out : F) = 1 := by
            calc
              chi D v (d0.out : F) = chi D v (1 : F) :=
                SB.chi_congr v (d0.out : F) 1 hresD'
              _ = 1 := hchiOne
          have hresDne : residue v (d0.out : F) ≠ 0 := by
            rw [hresD]
            exact one_ne_zero
          have hmask : chiPow D v (d0.out : F) (k : ℤ) = 1 := by
            rw [SB.chiPow_nonzero v (d0.out : F) (k : ℤ) hresDne, hχD]
            simp
          simpa using hmask
        · have hresD : residue v (d0.out : F) = 0 := by
            calc
              residue v (d0.out : F) = residue v ((p : F) ^ J) := hresEq.symm
              _ = 0 := hresPowZero J (Nat.pos_of_ne_zero hJ)
          rw [if_neg hJ]
          exact SB.chiPow_zero v (d0.out : F) (k : ℤ) hresD
      unfold localC
      rw [finsum_eq_sum_of_fintype]
      rw [Finset.sum_eq_single_of_mem d0 (Finset.mem_univ _) (by
        intro d hd hne
        have hnot : ¬ (∃ x : S.R,
            (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
              (primeGen R v : F) ^ k * (x : F)) := by
          intro h
          have hsimp : ∃ x : S.R, (p : F) ^ J - (d.out : F) =
              (p : F) ^ k * (x : F) := by simpa [p, pow_zero] using h
          exact hne ((hcondition d).mp hsimp)
        simp only [if_neg hnot])]
      split
      · have hinnerEq : ∑ᶠ x : Q0,
            A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d0.out : F)) *
                  (x.out : F) / (primeGen R v : F) ^ (k + 0)))) = 1 := by
          simpa [p, pow_zero, Nat.add_zero] using hinner d0 hcond0
        have hchar' : chiPow D v (d0.out : F) k = if J = 0 then 1 else 0 := by
          simpa [p] using hchar
        have hcond0' : ∃ x : S.R, (primeGen R v : F) ^ J -
            (primeGen R v : F) ^ 0 * (d0.out : F) =
              (primeGen R v : F) ^ k * (x : F) := by
          simpa [p] using hcond0Local
        have hmask := hchar'
        simp only [if_neg (Nat.ne_of_gt hk), if_true, one_mul]
        have hinnerEq' :
            (∑ᶠ x : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v hv) 0),
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d0.out : F)) *
                  (x.out : F) / (primeGen R v : F) ^ (k + 0))))) = 1 := by
          simpa [Q0, I0, pi] using hinnerEq
        rw [hinnerEq']
        simpa using hmask
      · rename_i hfalse
        have hcond0' : ∃ x : S.R, (primeGen R v : F) ^ J -
            (primeGen R v : F) ^ 0 * (d0.out : F) =
              (primeGen R v : F) ^ k * (x : F) := by simpa [p] using hcond0Local
        exact False.elim (hfalse hcond0')
    · intro t ht
      let It := R.exterior.pow pi t
      let Qt := ResidueRing R.exterior It
      let Q1 := ResidueRing R.exterior pi
      letI : Fintype Qt := R.exterior.residueFinite It
      letI : Fintype Q1 := R.exterior.residueFinite pi
      obtain ⟨rho, hrho, hrhoMk⟩ := euler_primePower_reduction R v hv t ht
      let f : Qt →+ Q1 := rho.toAddMonoidHom
      have hcardQt : Fintype.card Qt = Ideal.absNorm v.asIdeal ^ t := by
        simpa [Qt, It, pi] using euler_residue_card_pow R v hv t
      have hcardQ1 : Fintype.card Q1 = Ideal.absNorm v.asIdeal := by
        change @Fintype.card _ (R.exterior.residueFinite pi) = _
        rw [R.exterior.residue_card, R.exterior.prime_val]
      obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
      have hresReduce (x : Qt) : resEq (rho x) = residue v (x.out : F) := by
        have hxmk : rho x = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := by
          calc
            rho x = rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out) :=
              congrArg rho (Ideal.Quotient.mk_out x).symm
            _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := hrhoMk x.out
        rw [hxmk]
        exact hresEqMk x.out
      have hcardSum := euler_addHom_card_eq_card_mul_fiber f hrho
      rw [hcardQt, hcardQ1] at hcardSum
      have hpow : Ideal.absNorm v.asIdeal ^ t =
          Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal ^ (t - 1) := by
        have ht' : (t - 1) + 1 = t := by omega
        calc
          _ = Ideal.absNorm v.asIdeal ^ ((t - 1) + 1) :=
            congrArg (fun n : ℕ => Ideal.absNorm v.asIdeal ^ n) ht'.symm
          _ = Ideal.absNorm v.asIdeal ^ (t - 1) * Ideal.absNorm v.asIdeal := by
            rw [pow_succ]
          _ = _ := Nat.mul_comm _ _
      have hfiber0 : Fintype.card {x : Qt // f x = 0} =
          Ideal.absNorm v.asIdeal ^ (t - 1) := by
        have hqpos : 0 < Ideal.absNorm v.asIdeal := by
          exact lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
        rw [hpow] at hcardSum
        exact Nat.mul_left_cancel hqpos hcardSum.symm
      have hfiber (a : Q1) : Fintype.card {x : Qt // rho x = a} =
          Ideal.absNorm v.asIdeal ^ (t - 1) := by
        simpa [f] using (euler_addHom_fiber_card f hrho a).trans hfiber0
      let d₀ : Q0 := 0
      obtain ⟨_, cT, pRT, hpT, hpTgen⟩ := euler_prime_power_quotient_generator R v hv t
      have houterCond (d : Q0) : ∃ x : S.R,
          (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
            (primeGen R v : F) ^ 0 * (x : F) := by
        refine ⟨pRJ - pRT * d.out, ?_⟩
        rw [hpJ, hpT, pow_zero]
        simp
      have hlocalC0 : localC R v hv t 0 J =
          ∑ᶠ x : Qt, (if t = 0 then 1 else chiPow D v (x.out : F) t) *
            A.ψ v (algebraMap F (v.adicCompletion F)
              (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d₀.out : F)) *
                (x.out : F) / (primeGen R v : F) ^ t))) := by
        unfold localC
        rw [finsum_eq_sum_of_fintype]
        rw [Finset.sum_eq_single_of_mem d₀ (Finset.mem_univ _) (by
          intro d hd hne
          exact False.elim (hne (Subsingleton.elim d d₀)))]
        split
        · simp only [if_pos (by norm_num : (0 : ℕ) = 0), one_mul]
          simp [Qt, It, pi]
        · rename_i hfalse
          exact False.elim (hfalse (houterCond d₀))
      have h0 : localC R v hv t 0 J = (if t - 1 ≤ J then
          (qI v.asIdeal : ℂ) ^ (t - 1) *
            localT R v t ((primeGen R v : F) ^ (J + 1 - t)) else 0) := by
        by_cases hcut : t - 1 ≤ J
        · let m : ℕ := J + 1 - t
          have hm : m + t = J + 1 := by
            dsimp [m]
            omega
          have hm' : t + m = J + 1 := by omega
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hfrac : (primeGen R v : F) ^ J / (primeGen R v : F) ^ t =
              (primeGen R v : F) ^ m / (primeGen R v : F) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            field_simp [hpne]
            rw [← pow_succ, ← pow_add, hm']
          have hbase (x : Qt) :
              -((primeGen R v : F) ^ J * (x.out : F) /
                (primeGen R v : F) ^ t) =
              -((pRm : F) * (x.out : F) / (primeGen R v : F)) := by
            have hmul : (primeGen R v : F) ^ J * (x.out : F) /
                (primeGen R v : F) ^ t =
                ((primeGen R v : F) ^ J / (primeGen R v : F) ^ t) * (x.out : F) := by
              ring
            rw [hmul, hfrac, hpm]
            ring
          have harg (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                    (d₀.out : F)) * (x.out : F) /
                  (primeGen R v : F) ^ t))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((pRm : F) * (x.out : F) / (primeGen R v : F)))) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            let a := -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
              (d₀.out : F)) * (x.out : F) / (primeGen R v : F) ^ t)
            let b := -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
            have hab : a - b = (d₀.out * x.out : S.R) := by
              dsimp [a, b]
              field_simp [hpne]
              ring
            have habVal : HeightOneSpectrum.valuation F v (a - b) ≤ 1 := by
              rw [hab]
              exact (d₀.out * x.out).property v hv
            calc
              A.ψ v (algebraMap F (v.adicCompletion F) a) =
                  A.ψ v (algebraMap F (v.adicCompletion F) b) :=
                euler_addchar_congr_integral A v a b habVal
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((pRm : F) * (x.out : F) / (primeGen R v : F)))) := by
                rw [← hbase x]
          let g : Qt → ℂ := fun x =>
            chiPow D v (x.out : F) t * A.ψ v (algebraMap F (v.adicCompletion F)
              (-((pRm : F) * (x.out : F) / (primeGen R v : F))))
          have hCsum : localC R v hv t 0 J = ∑ x : Qt, g x := by
            rw [hlocalC0, finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro x hx
            change (if t = 0 then 1 else chiPow D v (x.out : F) t) *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                      (d₀.out : F)) * (x.out : F) /
                    (primeGen R v : F) ^ t))) = g x
            rw [if_neg (Nat.ne_of_gt ht), harg x]
          have hconst (x y : Qt) (hxy : rho x = rho y) : g x = g y := by
            have hres : residue v (x.out : F) = residue v (y.out : F) := by
              rw [← hresReduce x, hxy, hresReduce y]
            simpa [g] using euler_localFactor_residue_congr R v hv pRm x.out y.out t hres
          let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
            ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
          have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
              residue v ((liftResidue z : S.R) : F) = z := by
            change residue v (algebraMap (𝓞 F) F z.out) = z
            calc
              _ = Ideal.Quotient.mk v.asIdeal z.out :=
                (a2_bridge_SYMBOL D S).residue_algebraMap v z.out
              _ = z := Ideal.Quotient.mk_out z
          have hresEqLift (z : 𝓞 F ⧸ v.asIdeal) :
              resEq (Ideal.Quotient.mk
                (Ideal.span {R.exterior.genR pi}) (liftResidue z)) = z := by
            rw [hresEqMk, hresLift]
          let G : (𝓞 F ⧸ v.asIdeal) → ℂ := fun z =>
            chiPow D v ((liftResidue z : S.R) : F) t *
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((pRm : F) * ((liftResidue z : S.R) : F) /
                  (primeGen R v : F))))
          have hfiberSum : ∑ x : Qt, g x =
              ∑ b : Q1,
                (Fintype.card {x : Qt // rho x = b} : ℂ) *
                  g (Classical.choose (hrho b)) := by
            calc
              _ = ∑ b : Q1,
                    Fintype.card {x : Qt // rho x = b} •
                      g (Classical.choose (hrho b)) :=
                euler_sum_fiberwise_const rho hrho g hconst
              _ = _ := by
                apply Finset.sum_congr rfl
                intro b hb
                simp
          have hcardComplex (b : Q1) :
              (Fintype.card {x : Qt // rho x = b} : ℂ) =
                (qI v.asIdeal : ℂ) ^ (t - 1) := by
            rw [hfiber b]
            simp [qI]
          have hpoint (b : Q1) :
              g (Classical.choose (hrho b)) = G (resEq b) := by
            let x : Qt := Classical.choose (hrho b)
            have hx : rho x = b := Classical.choose_spec (hrho b)
            have hres : residue v (x.out : F) =
                residue v ((liftResidue (resEq b) : S.R) : F) := by
              calc
                residue v (x.out : F) = resEq (rho x) := (hresReduce x).symm
                _ = resEq b := by rw [hx]
                _ = residue v ((liftResidue (resEq b) : S.R) : F) :=
                  (hresLift (resEq b)).symm
            simpa [g, G, x] using
              euler_localFactor_residue_congr R v hv pRm x.out
                (liftResidue (resEq b)) t hres
          have hreindex :
              ∑ b : Q1, g (Classical.choose (hrho b)) =
                ∑ z : 𝓞 F ⧸ v.asIdeal, G z := by
            exact Fintype.sum_equiv (Equiv.ofBijective resEq hresEqBij)
              _ _ hpoint
          have hfactor :
              ∑ b : Q1,
                (Fintype.card {x : Qt // rho x = b} : ℂ) *
                  g (Classical.choose (hrho b)) =
                (qI v.asIdeal : ℂ) ^ (t - 1) *
                  ∑ z : 𝓞 F ⧸ v.asIdeal, G z := by
            calc
              _ = ∑ b : Q1,
                    (qI v.asIdeal : ℂ) ^ (t - 1) *
                      g (Classical.choose (hrho b)) := by
                apply Finset.sum_congr rfl
                intro b hb
                rw [hcardComplex]
              _ = (qI v.asIdeal : ℂ) ^ (t - 1) *
                    ∑ b : Q1, g (Classical.choose (hrho b)) := by
                rw [Finset.mul_sum]
              _ = _ := by rw [hreindex]
          have hG : ∑ z : 𝓞 F ⧸ v.asIdeal, G z =
              localT R v t (pRm : F) := by
            unfold localT
            rw [a2_bridge_FINITE_CHAR_finsum]
          rw [hCsum, hfiberSum, hfactor, hG]
          rw [if_pos (by omega)]
          rw [← hpm]
        · let gl : Qt → ℂ := fun x =>
            chiPow D v (x.out : F) t *
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((primeGen R v : F) ^ J * (x.out : F) /
                  (primeGen R v : F) ^ t)))
          have hphaseBase (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                    (d₀.out : F)) * (x.out : F) /
                  (primeGen R v : F) ^ t))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((primeGen R v : F) ^ J * (x.out : F) /
                  (primeGen R v : F) ^ t))) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            let a := -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
              (d₀.out : F)) * (x.out : F) / (primeGen R v : F) ^ t)
            let b := -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
            have hab : a - b = (d₀.out * x.out : S.R) := by
              dsimp [a, b]
              field_simp [hpne]
              ring
            have habVal : HeightOneSpectrum.valuation F v (a - b) ≤ 1 := by
              rw [hab]
              exact (d₀.out * x.out).property v hv
            exact euler_addchar_congr_integral A v a b habVal
          have hCsumLow : localC R v hv t 0 J = ∑ x : Qt, gl x := by
            rw [hlocalC0, finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Nat.ne_of_gt ht), hphaseBase x]
          obtain ⟨hchars, hchiSix, hpsi⟩ :=
            a2_bridge_FINITE_CHAR D S A v hv (primeGen R v) (by
              have h := (bc.gen_spec pi).1
              simpa [pi, primeGen, hv, R.exterior.prime_val] using h)
          obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
          have hψne : ψ ≠ (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by
            intro h
            have hshift : ψ.mulShift (1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
              ext z
              simp [AddChar.mulShift_apply, h]
            exact (hψprim one_ne_zero) hshift
          have hψwitness : ∃ z : 𝓞 F ⧸ v.asIdeal, ψ z ≠ 1 := by
            by_contra h
            push_neg at h
            apply hψne
            ext z
            exact h z
          obtain ⟨z, hz⟩ := hψwitness
          have hz0 : z ≠ 0 := by
            intro hz0
            subst z
            simpa using hz
          let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
            ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
          have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
              residue v ((liftResidue a : S.R) : F) = a := by
            change residue v (algebraMap (𝓞 F) F a.out) = a
            calc
              _ = Ideal.Quotient.mk v.asIdeal a.out :=
                (a2_bridge_SYMBOL D S).residue_algebraMap v a.out
              _ = a := Ideal.Quotient.mk_out a
          let posProdR : S.R := liftResidue 1 * liftResidue z
          have hresPosProd : residue v (posProdR : F) = z := by
            change residue v ((liftResidue 1 : S.R) * (liftResidue z : S.R) : F) = z
            rw [(a2_bridge_SYMBOL D S).residue_mul v
              (liftResidue 1 : F) (liftResidue z : F)
              ((liftResidue 1).property v hv) ((liftResidue z).property v hv),
              hresLift, hresLift]
            simp
          let negProdR : S.R := -posProdR
          have hresZero : residue v (0 : F) = 0 := by
            simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
          have hresNegProd : residue v (negProdR : F) = -z := by
            have hsum := euler_residue_add_integral v
              (negProdR : F) (posProdR : F)
              ((negProdR).property v hv) ((posProdR).property v hv)
            have hident : (negProdR : F) + (posProdR : F) = 0 := by
              dsimp [negProdR]
              ring
            rw [hident, hresZero, hresPosProd] at hsum
            exact eq_neg_iff_add_eq_zero.mpr hsum.symm
          let lambdaR : S.R := liftResidue (-z)
          have hresLambda : residue v (lambdaR : F) = -z := hresLift (-z)
          have hresNegEq : residue v (negProdR : F) = residue v (lambdaR : F) :=
            hresNegProd.trans hresLambda.symm
          have hnegProdNe : residue v (negProdR : F) ≠ 0 := by
            rw [hresNegProd]
            exact neg_ne_zero.mpr hz0
          have hlambdaNe : residue v (lambdaR : F) ≠ 0 := by
            rw [hresLambda]
            exact neg_ne_zero.mpr hz0
          have hmaskNeg : chiPow D v (negProdR : F) (0 : ℤ) = 1 := by
            simp [chiPow, hnegProdNe]
          have hmaskLambda : chiPow D v (lambdaR : F) (0 : ℤ) = 1 := by
            simp [chiPow, hlambdaNe]
          have hlocalCompare :=
            euler_localFactor_residue_congr R v hv 1 negProdR lambdaR 0 hresNegEq
          have hargPos : -((1 : F) * (negProdR : F) /
              (primeGen R v : F)) = (posProdR : F) / (primeGen R v : F) := by
            dsimp [negProdR]
            ring
          have hargLambda : -((1 : F) * (lambdaR : F) /
              (primeGen R v : F)) = -((lambdaR : F) / (primeGen R v : F)) := by
            ring
          have hψCompare :
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((posProdR : F) / (primeGen R v : F))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((lambdaR : F) / (primeGen R v : F)))) := by
            rw [hmaskNeg, hmaskLambda, one_mul, one_mul] at hlocalCompare
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((1 : F) * (negProdR : F) / (primeGen R v : F)))) :=
                congrArg (fun w : F => A.ψ v (algebraMap F (v.adicCompletion F) w))
                  hargPos.symm
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((1 : F) * (lambdaR : F) / (primeGen R v : F)))) := hlocalCompare
              _ = _ := congrArg
                (fun w : F => A.ψ v (algebraMap F (v.adicCompletion F) w)) hargLambda
          have hψevalProd : ψ z =
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((posProdR : F) / (primeGen R v : F))) := by
            simpa [posProdR, liftResidue] using hψeval z (1 : 𝓞 F ⧸ v.asIdeal)
          let c : ℂ := ψ z
          have hψconst :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((lambdaR : F) / (primeGen R v : F)))) = c := by
            exact (hψevalProd.trans hψCompare).symm
          let r : ℕ := t - 1 - J
          have hr : 0 < r := by
            dsimp [r]
            omega
          have hJr : J + r + 1 = t := by
            dsimp [r]
            omega
          obtain ⟨_, _, pRr, hpRr, _⟩ :=
            euler_prime_power_quotient_generator R v hv r
          obtain ⟨_, _, pRprev, hpRprev, _⟩ :=
            euler_prime_power_quotient_generator R v hv (r - 1)
          obtain ⟨_, c1, pR1, hpR1, hpR1gen⟩ :=
            euler_prime_power_quotient_generator R v hv 1
          have hpPowMul : (primeGen R v : F) ^ r =
              (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (r - 1) := by
            have hr' : 1 + (r - 1) = r := by omega
            calc
              _ = (primeGen R v : F) ^ (1 + (r - 1)) :=
                congrArg (fun n : ℕ => (primeGen R v : F) ^ n) hr'.symm
              _ = _ := by rw [pow_add]
          have hprev : pRr = pR1 * pRprev := by
            apply Subtype.ext
            calc
              (pRr : F) = (primeGen R v : F) ^ r := hpRr.symm
              _ = (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (r - 1) := hpPowMul
              _ = (pR1 : F) * (pRprev : F) := by rw [← hpR1, ← hpRprev]
          have hpGen : S.IsGen (primeGen R v : F) v.asIdeal := by
            have h := (bc.gen_spec pi).1
            simpa [pi, primeGen, hv, R.exterior.prime_val] using h
          have hpR1Gen : S.IsGen (pR1 : F) v.asIdeal := by
            rw [← hpR1, pow_one]
            exact hpGen
          have hpiGen : S.IsGen (R.exterior.genR pi : F) v.asIdeal := by
            rw [R.exterior.genR_val pi]
            have h := (bc.gen_spec pi).1
            simpa [pi, R.exterior.prime_val] using h
          have hspan1 : Ideal.span ({pR1} : Set S.R) =
              Ideal.span {R.exterior.genR pi} :=
            euler_span_singleton_eq_of_generators v hv v.asIdeal pR1
              (R.exterior.genR pi) hpR1Gen hpiGen
          have hspanT : Ideal.span ({pRT} : Set S.R) =
              Ideal.span {R.exterior.genR It} := by
            rw [hpTgen]
            exact Ideal.span_singleton_mul_left_unit cT.isUnit
              (R.exterior.genR It)
          let zR : S.R := pRr * lambdaR
          have hzMem : zR ∈ Ideal.span ({pR1} : Set S.R) := by
            apply Ideal.mem_span_singleton.mpr
            refine ⟨pRprev * lambdaR, ?_⟩
            dsimp [zR]
            rw [hprev]
            ring
          let δ : Qt := Ideal.Quotient.mk
            (Ideal.span {R.exterior.genR It}) zR
          have hredδ : rho δ = 0 := by
            change rho (Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR It}) zR) = 0
            rw [hrhoMk]
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            rw [← hspan1]
            exact hzMem
          let τ : Qt ≃ Qt := {
            toFun := fun x => x + δ
            invFun := fun x => x - δ
            left_inv := by intro x; simp
            right_inv := by intro x; simp }
          have hredτ (x : Qt) : rho (τ x) = rho x := by
            change rho (x + δ) = rho x
            calc
              rho (x + δ) = rho x + rho δ := rho.map_add x δ
              _ = rho x := by rw [hredδ]; simp
          have hresτ (x : Qt) :
              residue v ((τ x).out : F) = residue v (x.out : F) := by
            calc
              residue v ((τ x).out : F) = resEq (rho (τ x)) :=
                (hresReduce (τ x)).symm
              _ = resEq (rho x) := by rw [hredτ]
              _ = residue v (x.out : F) := hresReduce x
          have hquotτ (x : Qt) :
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) (τ x).out =
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR It})
                  (x.out + zR) := by
            calc
              _ = τ x := Ideal.Quotient.mk_out (τ x)
              _ = x + δ := rfl
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out +
                    Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) zR := by
                rw [Ideal.Quotient.mk_out x]
              _ = _ := by simp [δ]
          have hmemT (x : Qt) :
              (τ x).out - (x.out + zR) ∈ Ideal.span ({pRT} : Set S.R) := by
            have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
              (τ x).out (x.out + zR)).mp (hquotτ x)
            exact hspanT.symm ▸ hm
          let aLift (x : Qt) : S.R :=
            Classical.choose (Ideal.mem_span_singleton.mp (hmemT x))
          have haLift (x : Qt) :
              (τ x).out - (x.out + zR) = pRT * aLift x :=
            Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemT x))
          have hdelta (x : Qt) :
              ((τ x).out : F) - (x.out : F) =
                (zR : F) + (pRT : F) * (aLift x : F) := by
            have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
            change ((τ x).out : F) - ((x.out : F) + (zR : F)) =
              (pRT : F) * (aLift x : F) at haF
            calc
              ((τ x).out : F) - (x.out : F) =
                  (((τ x).out : F) - ((x.out : F) + (zR : F))) + (zR : F) := by ring
              _ = (pRT : F) * (aLift x : F) + (zR : F) := by rw [haF]
              _ = (zR : F) + (pRT : F) * (aLift x : F) := by ring
          have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
          have hratio : (primeGen R v : F) ^ J *
              (primeGen R v : F) ^ r / (primeGen R v : F) ^ t =
                1 / (primeGen R v : F) := by
            calc
              _ = (primeGen R v : F) ^ (J + r) /
                    (primeGen R v : F) ^ t := by rw [← pow_add]
              _ = 1 / (primeGen R v : F) := by
                field_simp [hpne]
                rw [← pow_succ, hJr]
          have hscale : (primeGen R v : F) ^ J * (zR : F) /
              (primeGen R v : F) ^ t = (lambdaR : F) /
                (primeGen R v : F) := by
            calc
              _ = ((primeGen R v : F) ^ J * (primeGen R v : F) ^ r /
                    (primeGen R v : F) ^ t) * (lambdaR : F) := by
                dsimp [zR]
                rw [← hpRr]
                ring
              _ = (1 / (primeGen R v : F)) * (lambdaR : F) := by rw [hratio]
              _ = _ := by ring
          let arg (x : Qt) : F :=
            -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
          let cArg : F := -((lambdaR : F) / (primeGen R v : F))
          have hargDiff (x : Qt) :
              arg (τ x) - (arg x + cArg) =
                -((primeGen R v : F) ^ J * (aLift x : F)) := by
            have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
            change ((τ x).out : F) - ((x.out : F) + (zR : F)) =
              (pRT : F) * (aLift x : F) at haF
            have hfirst : arg (τ x) - (arg x + cArg) =
                -((primeGen R v : F) ^ J * (zR : F) /
                    (primeGen R v : F) ^ t) -
                  (primeGen R v : F) ^ J * (aLift x : F) +
                    (lambdaR : F) / (primeGen R v : F) := by
              dsimp [arg, cArg]
              calc
                _ = -((primeGen R v : F) ^ J *
                      (((τ x).out : F) - (x.out : F)) /
                      (primeGen R v : F) ^ t) +
                    (lambdaR : F) / (primeGen R v : F) := by ring
                _ = _ := by
                  rw [hdelta x, ← hpT]
                  field_simp [hpne]
                  ring
            rw [hfirst, hscale, hpJ]
            ring
          have hphaseTrans (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ x))) =
                c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
            have hval : HeightOneSpectrum.valuation F v
                (arg (τ x) - (arg x + cArg)) ≤ 1 := by
              rw [hargDiff x, hpJ]
              exact (-(pRJ * aLift x)).property v hv
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (arg x + cArg)) :=
                euler_addchar_congr_integral A v (arg (τ x)) (arg x + cArg) hval
              _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) *
                    A.ψ v (algebraMap F (v.adicCompletion F) cArg) := by
                rw [← (A.ψ v).map_add_eq_mul]
                simp
              _ = c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
                rw [show cArg = -((lambdaR : F) / (primeGen R v : F)) by rfl,
                  hψconst]
                ring
          have htrans (x : Qt) : gl (τ x) = c * gl x := by
            have hchi := euler_chiPow_residue_congr D S v
              (x.out : F) ((τ x).out : F) (t : ℤ) (hresτ x).symm
            dsimp [gl]
            rw [hchi, hphaseTrans]
            ring
          have hsumShift : (∑ x : Qt, gl x) = ∑ x : Qt, gl (τ x) := by
            exact Fintype.sum_equiv τ.symm _ _ (by intro x; simp)
          have hsumMul : (∑ x : Qt, gl (τ x)) =
              c * ∑ x : Qt, gl x := by
            calc
              _ = ∑ x : Qt, c * gl x := by
                apply Finset.sum_congr rfl
                intro x hx
                exact htrans x
              _ = _ := by rw [Finset.mul_sum]
          have hsumEq : (∑ x : Qt, gl x) = c * ∑ x : Qt, gl x :=
            hsumShift.trans hsumMul
          have hsumZero : (∑ x : Qt, gl x) = 0 := by
            have hmul : (1 - c) * (∑ x : Qt, gl x) = 0 := by
              calc
                _ = (∑ x : Qt, gl x) - c * ∑ x : Qt, gl x := by ring
                _ = 0 := by rw [← hsumEq]; ring
            have hcnz : 1 - c ≠ 0 := by
              apply sub_ne_zero.mpr
              intro heq
              apply hz
              simpa [c] using heq.symm
            exact (mul_eq_zero.mp hmul).resolve_left hcnz
          rw [hCsumLow]
          rw [if_neg hcut]
          exact hsumZero
      have hC1 : localC R v hv t 1 J =
          (if t ≤ J then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
            localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (J - t)) else 0) := by
        by_cases hJ0 : J = 0
        · subst J
          let I1 := R.exterior.pow pi 1
          let Q1local := ResidueRing R.exterior I1
          letI : Fintype Q1local := R.exterior.residueFinite I1
          let p : Fˣ := primeGen R v
          have hpValLocal : HeightOneSpectrum.valuation F v (p : F) =
              WithZero.exp (-1 : ℤ) := by simpa [p] using euler_primeGen_valuation R v hv
          have hpLtLocal : HeightOneSpectrum.valuation F v (p : F) < 1 := by
            rw [hpValLocal]
            simp
          obtain ⟨_, _, pRTprev, hpRTprev, _⟩ :=
            euler_prime_power_quotient_generator R v hv (t - 1)
          have hpTfactor : (p : F) ^ t = (p : F) * (pRTprev : F) := by
            have ht' : t = 1 + (t - 1) := by omega
            rw [ht', pow_add, hpRTprev]
            simp [p]
          have hnoSupport (d : Q1local) :
              ¬ ∃ z : S.R, (p : F) ^ 0 - (p : F) ^ t * (d.out : F) =
                (p : F) ^ 1 * (z : F) := by
            rintro ⟨z, hz⟩
            have hz' : 1 - (p : F) ^ t * (d.out : F) =
                (p : F) * (z : F) := by simpa [pow_zero, pow_one] using hz
            let w : S.R := z + pRTprev * d.out
            have hw : (p : F) * (w : F) = 1 := by
              dsimp [w]
              have hz'' := hz'
              rw [hpTfactor] at hz''
              calc
                (p : F) * ((z : F) + (pRTprev : F) * (d.out : F)) =
                    (p : F) * (z : F) +
                      (p : F) * ((pRTprev : F) * (d.out : F)) := by rw [mul_add]
                _ = 1 := by
                  rw [← mul_assoc, ← hz'']
                  exact sub_add_cancel _ _
            have hwVal : HeightOneSpectrum.valuation F v (w : F) ≤ 1 := w.property v hv
            have hwProd : HeightOneSpectrum.valuation F v ((p : F) * (w : F)) < 1 := by
              rw [(v.valuation F).map_mul]
              by_cases hw0 : HeightOneSpectrum.valuation F v (w : F) = 0
              · rw [hw0, mul_zero]
                exact zero_lt_one
              · have hwpos : 0 < HeightOneSpectrum.valuation F v (w : F) :=
                  lt_of_le_of_ne zero_le (Ne.symm hw0)
                calc
                  _ < 1 * HeightOneSpectrum.valuation F v (w : F) :=
                    mul_lt_mul_of_pos_right hpLtLocal hwpos
                  _ ≤ 1 := by simpa using hwVal
            rw [hw] at hwProd
            simp at hwProd
          unfold localC
          rw [finsum_eq_sum_of_fintype]
          change (∑ d ∈ (Finset.univ : Finset Q1local),
              (if ∃ z : S.R, (primeGen R v : F) ^ 0 -
                  (primeGen R v : F) ^ t * (d.out : F) =
                    (primeGen R v : F) ^ 1 * (z : F) then
                (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                  ∑ᶠ z : Qt,
                    (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                      A.ψ v (algebraMap F (v.adicCompletion F)
                        (-(((primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t *
                            (d.out : F)) * (z.out : F) /
                          (primeGen R v : F) ^ (1 + t)))) else 0)) =
            if t ≤ 0 then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
              localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (0 - t)) else 0
          rw [if_neg (by omega)]
          apply Finset.sum_eq_zero
          intro d hd
          have hcond : ¬ ∃ z : S.R,
              (primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) := by
            simpa only [p, pow_zero, pow_one] using hnoSupport d
          change (if ∃ z : S.R,
              (primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) then
              (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                ∑ᶠ z : Qt,
                  (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-(((primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t *
                          (d.out : F)) * (z.out : F) /
                        (primeGen R v : F) ^ (1 + t)))) else 0) = 0
          rw [if_neg hcond]
        · have hJpos : 0 < J := by omega
          let I1 := R.exterior.pow pi 1
          let Q1local := ResidueRing R.exterior I1
          letI : Fintype Q1local := R.exterior.residueFinite I1
          let p : Fˣ := primeGen R v
          have hpne : (p : F) ≠ 0 := Units.ne_zero _
          have hpValLocal : HeightOneSpectrum.valuation F v (p : F) =
              WithZero.exp (-1 : ℤ) := by simpa [p] using euler_primeGen_valuation R v hv
          obtain ⟨_, _, pRJm1, hpRJm1, _⟩ :=
            euler_prime_power_quotient_generator R v hv (J - 1)
          obtain ⟨_, _, pRTm1, hpRTm1, _⟩ :=
            euler_prime_power_quotient_generator R v hv (t - 1)
          have hpJfactor : (p : F) ^ J = (p : F) * (pRJm1 : F) := by
            have hJ' : J = 1 + (J - 1) := by omega
            rw [hJ', pow_add, hpRJm1]
            simp [p]
          have hpTfactor1 : (p : F) ^ t = (p : F) * (pRTm1 : F) := by
            have ht' : t = 1 + (t - 1) := by omega
            rw [ht', pow_add, hpRTm1]
            simp [p]
          obtain ⟨rho1, hrho1, hrho1Mk⟩ :=
            euler_primePower_reduction R v hv 1 (by norm_num)
          have hcardQ1local : Fintype.card Q1local = Ideal.absNorm v.asIdeal := by
            simpa [Q1local, I1, pi] using euler_residue_card_pow R v hv 1
          have hcardSame : Fintype.card Q1local = Fintype.card Q1 :=
            hcardQ1local.trans hcardQ1.symm
          have hbij1 : Function.Bijective rho1 :=
            (Fintype.bijective_iff_surjective_and_card rho1).2 ⟨hrho1, hcardSame⟩
          let e1 : Q1local ≃ Q1 := Equiv.ofBijective rho1 hbij1
          have hredMk1 (d : Q1local) :
              rho1 d = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out := by
            calc
              rho1 d = rho1 (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR I1}) d.out) :=
                congrArg rho1 (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out :=
                hrho1Mk d.out
          have hresD1 (d : Q1local) :
              residue v (d.out : F) = residue v ((rho1 d).out : F) := by
            calc
              residue v (d.out : F) =
                  resEq (Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out) :=
                (hresEqMk d.out).symm
              _ = resEq (rho1 d) := by rw [hredMk1]
              _ = resEq (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) (rho1 d).out) := by
                rw [Ideal.Quotient.mk_out]
              _ = residue v ((rho1 d).out : F) := hresEqMk (rho1 d).out
          have houterLocal (x₀ : Qt) (hx₀ : residue v (x₀.out : F) ≠ 0) :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F)))) =
                localT R v 1 1 * star (chi D v (x₀.out : F)) := by
            let f₁ : Q1 → ℂ := fun b =>
              chiPow D v (b.out : F) 1 * A.ψ v (algebraMap F (v.adicCompletion F)
                ((b.out : F) * (x₀.out : F) / (p : F)))
            have hterm (d : Q1local) :
                chiPow D v (d.out : F) 1 * A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F))) = f₁ (rho1 d) := by
              have hchi := euler_chiPow_residue_congr D S v
                (d.out : F) ((rho1 d).out : F) 1 (hresD1 d)
              have hresProd : residue v ((d.out * x₀.out : S.R) : F) =
                  residue v (((rho1 d).out * x₀.out : S.R) : F) := by
                calc
                  _ = residue v (d.out : F) * residue v (x₀.out : F) :=
                    SB.residue_mul v (d.out : F) (x₀.out : F)
                      (d.out.property v hv) (x₀.out.property v hv)
                  _ = residue v ((rho1 d).out : F) * residue v (x₀.out : F) := by
                    rw [hresD1]
                  _ = _ := (SB.residue_mul v ((rho1 d).out : F) (x₀.out : F)
                    ((rho1 d).out.property v hv) (x₀.out.property v hv)).symm
              have hpsi := euler_addchar_div_residue_congr D A v hv p hpValLocal
                (d.out * x₀.out) ((rho1 d).out * x₀.out) hresProd
              have hpsi' : A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F))) =
                  A.ψ v (algebraMap F (v.adicCompletion F)
                  (((rho1 d).out : F) * (x₀.out : F) / (p : F))) := by
                simpa only [Subalgebra.coe_mul] using hpsi
              calc
                _ = chiPow D v ((rho1 d).out : F) 1 *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((d.out : F) * (x₀.out : F) / (p : F))) := by rw [hchi]
                _ = _ := by rw [hpsi']
            calc
              _ = ∑ d : Q1local, f₁ (rho1 d) := by
                apply Finset.sum_congr rfl
                intro d hd
                exact hterm d
              _ = ∑ b : Q1, f₁ b := by
                exact Fintype.sum_equiv e1 (fun d => f₁ (e1 d)) f₁
                  (by intro d; rfl)
              _ = localT R v 1 1 * star (chi D v (x₀.out : F)) :=
                euler_localD_gauss_sum R v hv x₀.out hx₀
          let yD : Q1local → S.R := fun d => pRJm1 - pRTm1 * d.out
          have hnum (d : Q1local) :
              (p : F) ^ J - (p : F) ^ t * (d.out : F) =
                (p : F) * (yD d : F) := by
            rw [hpJfactor, hpTfactor1]
            dsimp [yD]
            ring
          have hsupport (d : Q1local) : ∃ z : S.R,
              (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) := by
            refine ⟨yD d, ?_⟩
            simpa [p, pow_one] using hnum d
          have hargSplit (d : Q1local) (z : Qt) :
              -(((p : F) ^ J - (p : F) ^ t * (d.out : F)) * (z.out : F) /
                  (p : F) ^ (1 + t)) =
                -((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) +
                  (d.out : F) * (z.out : F) / (p : F) := by
            field_simp [hpne]
            ring
          have hphaseFactor (d : Q1local) (z : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) * (z.out : F) /
                    (p : F) ^ (1 + t)))) =
                A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
              A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (z.out : F) / (p : F))) := by
            have hmap : algebraMap F (v.adicCompletion F)
                (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) +
                  (d.out : F) * (z.out : F) / (p : F)) =
                algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))) +
                  algebraMap F (v.adicCompletion F)
                    ((d.out : F) * (z.out : F) / (p : F)) := by simp
            rw [hargSplit]
            rw [hmap]
            exact (A.ψ v).map_add_eq_mul _ _
          have hCsum : localC R v hv t 1 J =
              ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
                        (z.out : F) / (p : F) ^ (1 + t)))) := by
            unfold localC
            simp_rw [finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro d hd
            have hs := hsupport d
            change (if ∃ z : S.R,
                (primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                  (d.out : F) = (primeGen R v : F) ^ 1 * (z : F) then
                (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                  ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                          (d.out : F)) * (z.out : F) /
                        (primeGen R v : F) ^ (1 + t)))) else 0) =
              chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                        (d.out : F)) * (z.out : F) /
                      (primeGen R v : F) ^ (1 + t))))
            rw [if_pos hs]
            simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0)]
          have hsumRearrange :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
                        (z.out : F) / (p : F) ^ (1 + t))))) =
                ∑ z : Qt, chiPow D v (z.out : F) t *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                  ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((d.out : F) * (z.out : F) / (p : F))) := by
            simp only [if_neg (Nat.ne_of_gt ht)]
            simp_rw [hphaseFactor]
            calc
              _ = ∑ d : Q1local, ∑ z : Qt,
                  chiPow D v (d.out : F) 1 *
                    (chiPow D v (z.out : F) t *
                      (A.ψ v (algebraMap F (v.adicCompletion F)
                        (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                        A.ψ v (algebraMap F (v.adicCompletion F)
                          ((d.out : F) * (z.out : F) / (p : F))))) := by
                apply Finset.sum_congr rfl
                intro d hd
                rw [Finset.mul_sum]
              _ = ∑ z : Qt, ∑ d : Q1local,
                  chiPow D v (d.out : F) 1 *
                    (chiPow D v (z.out : F) t *
                      (A.ψ v (algebraMap F (v.adicCompletion F)
                        (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                        A.ψ v (algebraMap F (v.adicCompletion F)
                          ((d.out : F) * (z.out : F) / (p : F))))) :=
                Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro z hz
                conv_rhs => rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro d hd
                ring
          have houter (z : Qt) (hz : residue v (z.out : F) ≠ 0) :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (z.out : F) / (p : F)))) =
                localT R v 1 1 * star (chi D v (z.out : F)) := by
            exact houterLocal z hz
          have hcharTimes (z : Qt) :
              chiPow D v (z.out : F) t * star (chi D v (z.out : F)) =
                chiPow D v (z.out : F) ((t : ℤ) - 1) := by
            by_cases hz : residue v (z.out : F) = 0
            · rw [SB.chiPow_zero v (z.out : F) t hz,
                SB.chiPow_zero v (z.out : F) ((t : ℤ) - 1) hz]
              simp
            · rw [SB.chiPow_nonzero v (z.out : F) t hz,
                SB.chiPow_nonzero v (z.out : F) ((t : ℤ) - 1) hz]
              have hstar : star (chi D v (z.out : F)) =
                  (chi D v (z.out : F))⁻¹ := by
                exact (Complex.inv_eq_conj
                  (SB.chi_norm v (z.out : F) hz)).symm
              have hchiNe : chi D v (z.out : F) ≠ 0 := by
                apply norm_ne_zero_iff.mp
                rw [SB.chi_norm v (z.out : F) hz]
                norm_num
              rw [hstar]
              rw [← zpow_neg_one]
              rw [show (t : ℤ) - 1 = (t : ℤ) + (-1 : ℤ) by omega]
              conv_rhs => rw [zpow_add₀ hchiNe]
          have hcollapsed :
              (∑ z : Qt, chiPow D v (z.out : F) t *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    ((d.out : F) * (z.out : F) / (p : F)))) =
              localT R v 1 1 *
                ∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) := by
            calc
              _ = ∑ z : Qt, localT R v 1 1 *
                  (chiPow D v (z.out : F) ((t : ℤ) - 1) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) := by
                apply Finset.sum_congr rfl
                intro z hz
                by_cases hz0 : residue v (z.out : F) = 0
                · rw [SB.chiPow_zero v (z.out : F) t hz0,
                    SB.chiPow_zero v (z.out : F) ((t : ℤ) - 1) hz0]
                  simp
                · rw [houter z hz0]
                  calc
                    _ = localT R v 1 1 *
                        ((chiPow D v (z.out : F) t *
                            star (chi D v (z.out : F))) *
                          A.ψ v (algebraMap F (v.adicCompletion F)
                            (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) := by
                      ring
                    _ = _ := by rw [hcharTimes]
              _ = _ := by rw [Finset.mul_sum]
          by_cases hcut1 : t ≤ J
          · let m : ℕ := J - t
            obtain ⟨_, _, pRm, hpm, _⟩ :=
              euler_prime_power_quotient_generator R v hv m
            have hm : J = t + m := by
              dsimp [m]
              omega
            have hpNum : (p : F) ^ J = (p : F) ^ t * (pRm : F) := by
              rw [hm, pow_add, hpm]
            have hpDen : (p : F) ^ (1 + t) = (p : F) ^ t * (p : F) := by
              rw [show 1 + t = t + 1 by omega, pow_succ]
            have hpne : (p : F) ≠ 0 := Units.ne_zero _
            have hbase (z : Qt) :
                -((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) =
                  -((pRm : F) * (z.out : F) / (p : F)) := by
              rw [hpNum, hpDen]
              field_simp [hpne]
            have hlocalSum :
                (∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) =
                  (qI v.asIdeal : ℂ) ^ (t - 1) *
                    localT R v ((t : ℤ) - 1) (pRm : F) := by
              calc
                _ = ∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-((pRm : F) * (z.out : F) / (p : F)))) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [hbase z]
                _ = _ := by
                  simpa [Qt, It, pi] using
                    (euler_primePower_localT_sum R v hv t ht ((t : ℤ) - 1) pRm)
            rw [hCsum, hsumRearrange, hcollapsed, hlocalSum, if_pos hcut1]
            rw [hpm]
            ring
          · let r : ℕ := t - J
            have hr : 0 < r := by dsimp [r]; omega
            have hJr : J + r = t := by dsimp [r]; omega
            obtain ⟨_, _, pRr, hpRr, _⟩ :=
              euler_prime_power_quotient_generator R v hv r
            obtain ⟨_, cTt, pRTt, hpRTt, hpRTtgen⟩ :=
              euler_prime_power_quotient_generator R v hv t
            have hspanT : Ideal.span ({pRTt} : Set S.R) =
                Ideal.span {R.exterior.genR It} := by
              rw [hpRTtgen]
              exact Ideal.span_singleton_mul_left_unit cTt.isUnit
                (R.exterior.genR It)
            have hpGen' : S.IsGen (p : F) v.asIdeal := by
              have h := (bc.gen_spec pi).1
              simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
            obtain ⟨_, _, hpsi⟩ :=
              a2_bridge_FINITE_CHAR D S A v hv p hpGen'
            obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
            have hψne : ψ ≠ (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by
              intro hψone
              have hshift : ψ.mulShift (1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
                ext z
                simp [AddChar.mulShift_apply, hψone]
              exact (hψprim one_ne_zero) hshift
            have hψwitness : ∃ z : 𝓞 F ⧸ v.asIdeal, ψ z ≠ 1 := by
              by_contra h
              push_neg at h
              apply hψne
              ext z
              exact h z
            obtain ⟨z, hz⟩ := hψwitness
            have hz0 : z ≠ 0 := by
              intro hz0
              subst z
              simpa using hz
            let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
              ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
            have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
                residue v ((liftResidue a : S.R) : F) = a := by
              change residue v (algebraMap (𝓞 F) F a.out) = a
              calc
                _ = Ideal.Quotient.mk v.asIdeal a.out :=
                  SB.residue_algebraMap v a.out
                _ = a := Ideal.Quotient.mk_out a
            let lambdaR : S.R := liftResidue z
            let posProdR : S.R := liftResidue 1 * liftResidue z
            let c : ℂ := ψ z
            have hresPosProd : residue v (posProdR : F) = z := by
              change residue v ((liftResidue 1 : S.R) *
                (liftResidue z : S.R) : F) = z
              rw [SB.residue_mul v (liftResidue 1 : F) (liftResidue z : F)
                ((liftResidue 1).property v hv) ((liftResidue z).property v hv),
                hresLift, hresLift]
              simp
            have hψevalLambda :
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((lambdaR : F) / (p : F))) = c := by
              have hψevalProd : ψ z = A.ψ v (algebraMap F (v.adicCompletion F)
                  ((posProdR : F) / (p : F))) := by
                simpa [posProdR, liftResidue, p] using
                  hψeval z (1 : 𝓞 F ⧸ v.asIdeal)
              calc
                _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    ((posProdR : F) / (p : F))) :=
                  (euler_addchar_div_residue_congr D A v hv p hpValLocal
                    posProdR lambdaR (hresPosProd.trans (hresLift z).symm)).symm
                _ = ψ z := hψevalProd.symm
                _ = c := rfl
            have hpRrRes : residue v (pRr : F) = 0 := by
              rw [← hpRr, hresPowZero r hr]
            let deltaR : S.R := pRr * lambdaR
            have hresDelta : residue v (deltaR : F) = 0 := by
              change residue v ((pRr : F) * (lambdaR : F)) = 0
              rw [SB.residue_mul v (pRr : F) (lambdaR : F)
                (pRr.property v hv) (lambdaR.property v hv), hpRrRes]
              simp
            have hresZero : residue v (0 : F) = 0 := by
              simpa using SB.residue_algebraMap v (0 : 𝓞 F)
            have hresEqZero : resEq (0 : Q1) = 0 := by
              have hmk0 : Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) (0 : S.R) = (0 : Q1) := by simp
              rw [← hmk0]
              exact (hresEqMk 0).trans hresZero
            let δ : Qt := Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR It}) deltaR
            have hresRhoδ : resEq (rho δ) = 0 := by
              have hmkδ : rho δ = Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) deltaR := by
                dsimp [δ]
                exact hrhoMk deltaR
              rw [hmkδ, hresEqMk]
              exact hresDelta
            have hrhoδ : rho δ = 0 :=
              hresEqBij.1 (hresRhoδ.trans hresEqZero.symm)
            let τ : Qt ≃ Qt := {
              toFun := fun x => x - δ
              invFun := fun x => x + δ
              left_inv := by intro x; simp
              right_inv := by intro x; simp }
            have hredτ (x : Qt) : rho (τ x) = rho x := by
              calc
                rho (τ x) = rho (x - δ) := rfl
                _ = rho x - rho δ := rho.map_sub x δ
                _ = rho x := by rw [hrhoδ]; simp
            have hresτ (x : Qt) :
                residue v ((τ x).out : F) = residue v (x.out : F) := by
              calc
                _ = resEq (rho (τ x)) := (hresReduce (τ x)).symm
                _ = resEq (rho x) := by rw [hredτ]
                _ = _ := hresReduce x
            have hquotτ (x : Qt) :
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) (τ x).out =
                  Ideal.Quotient.mk (Ideal.span {R.exterior.genR It})
                    (x.out - deltaR) := by
              calc
                _ = τ x := Ideal.Quotient.mk_out (τ x)
                _ = x - δ := rfl
                _ = _ := by simp [δ]
            have hmemT (x : Qt) :
                (τ x).out - (x.out - deltaR) ∈
                  Ideal.span ({pRTt} : Set S.R) := by
              have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
                (τ x).out (x.out - deltaR)).mp (hquotτ x)
              exact hspanT.symm ▸ hm
            let aLift (x : Qt) : S.R :=
              Classical.choose (Ideal.mem_span_singleton.mp (hmemT x))
            have haLift (x : Qt) :
                (τ x).out - (x.out - deltaR) = pRTt * aLift x :=
              Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemT x))
            have hdelta (x : Qt) :
                ((τ x).out : F) - (x.out : F) =
                  -((deltaR : F)) + (pRTt : F) * (aLift x : F) := by
              have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
              change ((τ x).out : F) - ((x.out : F) - (deltaR : F)) =
                (pRTt : F) * (aLift x : F) at haF
              calc
                _ = (((τ x).out : F) - ((x.out : F) - (deltaR : F))) -
                    (deltaR : F) := by ring
                _ = (pRTt : F) * (aLift x : F) - (deltaR : F) := by rw [haF]
                _ = _ := by ring
            have hpPowShift : (p : F) ^ J * (p : F) ^ r = (p : F) ^ t := by
              calc
                _ = (p : F) ^ (J + r) := by rw [← pow_add]
                _ = _ := by rw [hJr]
            have hscaleDelta :
                (p : F) ^ J * (deltaR : F) / (p : F) ^ (1 + t) =
                  (lambdaR : F) / (p : F) := by
              dsimp [deltaR]
              rw [← hpRr, show 1 + t = t + 1 by omega, pow_succ]
              rw [show (p : F) ^ J * ((p : F) ^ r * (lambdaR : F)) =
                ((p : F) ^ J * (p : F) ^ r) * (lambdaR : F) by ring,
                hpPowShift]
              field_simp [hpne]
            have hscaleError :
                (p : F) ^ J * (pRTt : F) / (p : F) ^ (1 + t) =
                  (p : F) ^ (J - 1) := by
              rw [← hpRTt, show 1 + t = t + 1 by omega]
              have hexp : J + t = (J - 1) + (t + 1) := by omega
              calc
                _ = (p : F) ^ (J + t) / (p : F) ^ (t + 1) := by
                  rw [← pow_add]
                _ = ((p : F) ^ (J - 1) * (p : F) ^ (t + 1)) /
                    (p : F) ^ (t + 1) := by rw [hexp, pow_add]
                _ = _ := by
                  rw [pow_succ]
                  field_simp [hpne]
            have hscaleErrorMul (x : Qt) :
                (p : F) ^ J * (pRTt : F) * (aLift x : F) /
                    (p : F) ^ (1 + t) =
                  (p : F) ^ (J - 1) * (aLift x : F) := by
              calc
                _ = ((p : F) ^ J * (pRTt : F) /
                    (p : F) ^ (1 + t)) * (aLift x : F) := by ring
                _ = _ := by rw [hscaleError]
            have hdeltaPoint (x : Qt) :
                ((τ x).out : F) =
                  (x.out : F) - (deltaR : F) +
                    (pRTt : F) * (aLift x : F) := by
              calc
                _ = (((τ x).out : F) - (x.out : F)) + (x.out : F) := by ring
                _ = (-((deltaR : F)) + (pRTt : F) * (aLift x : F)) +
                    (x.out : F) := by rw [hdelta]
                _ = _ := by ring
            let arg (x : Qt) : F :=
              -((p : F) ^ J * (x.out : F) / (p : F) ^ (1 + t))
            have hargDiff (x : Qt) :
                arg (τ x) - (arg x + (lambdaR : F) / (p : F)) =
                  -((pRJm1 * aLift x : S.R) : F) := by
              calc
                _ = (p : F) ^ J * (deltaR : F) / (p : F) ^ (1 + t) -
                    (p : F) ^ J * (pRTt : F) * (aLift x : F) /
                      (p : F) ^ (1 + t) - (lambdaR : F) / (p : F) := by
                  dsimp [arg]
                  rw [hdeltaPoint x]
                  field_simp [hpne]
                  ring
                _ = (lambdaR : F) / (p : F) -
                    (p : F) ^ (J - 1) * (aLift x : F) -
                      (lambdaR : F) / (p : F) := by
                  rw [hscaleDelta, hscaleErrorMul]
                _ = -((pRJm1 * aLift x : S.R) : F) := by
                  rw [hpRJm1]
                  simp
            have hargVal (x : Qt) :
                HeightOneSpectrum.valuation F v
                  (arg (τ x) - (arg x + (lambdaR : F) / (p : F))) ≤ 1 := by
              rw [hargDiff x]
              exact (-(pRJm1 * aLift x)).property v hv
            have hphaseTrans (x : Qt) :
                A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ x))) =
                  c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
              calc
                _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (arg x + (lambdaR : F) / (p : F))) :=
                  euler_addchar_congr_integral A v (arg (τ x))
                    (arg x + (lambdaR : F) / (p : F)) (hargVal x)
                _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((lambdaR : F) / (p : F))) := by
                  rw [← (A.ψ v).map_add_eq_mul]
                  simp
                _ = _ := by rw [hψevalLambda]; dsimp [c]; ring
            let g : Qt → ℂ := fun x =>
              chiPow D v (x.out : F) ((t : ℤ) - 1) *
                A.ψ v (algebraMap F (v.adicCompletion F) (arg x))
            have htrans (x : Qt) : g (τ x) = c * g x := by
              have hchi := euler_chiPow_residue_congr D S v
                (x.out : F) ((τ x).out : F) ((t : ℤ) - 1) (hresτ x).symm
              dsimp [g]
              rw [hchi, hphaseTrans]
              ring
            have hsumShift : (∑ x : Qt, g x) = ∑ x : Qt, g (τ x) := by
              exact Fintype.sum_equiv τ.symm _ _ (by intro x; simp)
            have hsumMul : (∑ x : Qt, g (τ x)) = c * ∑ x : Qt, g x := by
              calc
                _ = ∑ x : Qt, c * g x := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  exact htrans x
                _ = _ := by rw [Finset.mul_sum]
            have hsumEq : (∑ x : Qt, g x) = c * ∑ x : Qt, g x :=
              hsumShift.trans hsumMul
            have hsumZero : (∑ x : Qt, g x) = 0 := by
              have hmul : (1 - c) * (∑ x : Qt, g x) = 0 := by
                calc
                  _ = (∑ x : Qt, g x) - c * ∑ x : Qt, g x := by ring
                  _ = 0 := by rw [← hsumEq]; ring
              have hcnz : 1 - c ≠ 0 := by
                apply sub_ne_zero.mpr
                intro heq
                apply hz
                simpa [c] using heq.symm
              exact (mul_eq_zero.mp hmul).resolve_left hcnz
            have hbaseZero :
                (∑ x : Qt, chiPow D v (x.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F) (arg x))) = 0 := by
              simpa [g] using hsumZero
            rw [hCsum, hsumRearrange, hcollapsed, if_neg hcut1]
            rw [hbaseZero]
            simp
      refine ⟨h0, hC1, ?_, ?_, ?_⟩
      · intro k hk
        have hkpos : 0 < k := by omega
        have hkne : k ≠ 0 := by omega
        let Ik := R.exterior.pow pi k
        let Qk := ResidueRing R.exterior Ik
        letI : Fintype Qk := R.exterior.residueFinite Ik
        let p : Fˣ := primeGen R v
        obtain ⟨_, cK, pRK, hpK, hpKgen⟩ :=
          euler_prime_power_quotient_generator R v hv k
        have hspanK : Ideal.span ({pRK} : Set S.R) =
            Ideal.span {R.exterior.genR Ik} := by
          rw [hpKgen]
          exact Ideal.span_singleton_mul_left_unit cK.isUnit
            (R.exterior.genR Ik)
        obtain ⟨rhoK, hrhoK, hrhoKMk⟩ :=
          euler_primePower_reduction R v hv k hkpos
        have hresReduceK (d : Qk) : resEq (rhoK d) =
            residue v (d.out : F) := by
          have hmk : rhoK d = Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR pi}) d.out := by
            calc
              rhoK d = rhoK (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR Ik}) d.out) :=
                congrArg rhoK (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out :=
                hrhoKMk d.out
          rw [hmk]
          exact hresEqMk d.out
        obtain ⟨_, cKm1, pRKm1, hpRKm1, _⟩ :=
          euler_prime_power_quotient_generator R v hv (k - 1)
        obtain ⟨_, cTm1, pRTm1, hpRTm1, _⟩ :=
          euler_prime_power_quotient_generator R v hv (t - 1)
        have hpCross : (pRT : F) * (pRKm1 : F) =
            (pRK : F) * (pRTm1 : F) := by
          calc
            _ = (p : F) ^ t * (p : F) ^ (k - 1) := by
              rw [hpT, hpRKm1]
            _ = (p : F) ^ (t + (k - 1)) := by rw [← pow_add]
            _ = (p : F) ^ (k + (t - 1)) := by congr 1 <;> omega
            _ = (p : F) ^ k * (p : F) ^ (t - 1) := by rw [pow_add]
            _ = _ := by rw [← hpK, ← hpRTm1]
        let supports : Qk → Prop := fun d =>
          ∃ y : S.R, (p : F) ^ J - (p : F) ^ t * (d.out : F) =
            (p : F) ^ k * (y : F)
        have hsupportMem (d : Qk) : supports d ↔
            pRJ - pRT * d.out ∈ Ideal.span ({pRK} : Set S.R) := by
          have hdiv := euler_power_divisibility_iff p k pRK hpK
            (pRJ - pRT * d.out)
          constructor
          · rintro ⟨y, hy⟩
            apply hdiv.mp
            refine ⟨y, ?_⟩
            change (pRJ : F) - (pRT : F) * (d.out : F) =
              (p : F) ^ k * (y : F)
            calc
              _ = (p : F) ^ J - (p : F) ^ t * (d.out : F) := by
                rw [hpJ, hpT]
              _ = _ := hy
          · intro hmem
            rcases hdiv.mpr hmem with ⟨y, hy⟩
            refine ⟨y, ?_⟩
            calc
              (p : F) ^ J - (p : F) ^ t * (d.out : F) =
                  (pRJ : F) - (pRT : F) * (d.out : F) := by
                rw [hpJ, hpT]
              _ = (p : F) ^ k * (y : F) := hy
        have hsupportQuot (d : Qk) : supports d ↔
            Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik}) pRJ =
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                (pRT * d.out) := by
          calc
            _ ↔ pRJ - pRT * d.out ∈ Ideal.span {pRK} := hsupportMem d
            _ ↔ pRJ - pRT * d.out ∈
                Ideal.span {R.exterior.genR Ik} := by rw [hspanK]
            _ ↔ _ :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ (pRT * d.out)).symm
        let arg (d : Qk) (x : Qt) : F :=
          -(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
            (x.out : F) / (p : F) ^ (k + t))
        have hCsum : localC R v hv t k J =
            ∑ x : Qt, chiPow D v (x.out : F) t *
              ∑ d : Qk, (if supports d then
                  chiPow D v (d.out : F) k *
                  A.ψ v (algebraMap F (v.adicCompletion F) (arg d x))
                else 0) := by
          unfold localC
          simp_rw [finsum_eq_sum_of_fintype]
          simp only [if_neg hkne, if_neg (Nat.ne_of_gt ht)]
          calc
            _ = ∑ d : Qk, ∑ x : Qt,
                (if supports d then chiPow D v (d.out : F) k *
                  (chiPow D v (x.out : F) t *
                    A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)))
                 else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hs : supports d
              · have hsRaw : ∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F) := by
                  change ∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)
                  exact hs
                conv_lhs => rw [if_pos hsRaw]
                conv_rhs => simp only [if_pos hs]
                rw [Finset.mul_sum]
              · have hsRaw : ¬ (∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)) := by
                  change ¬ (∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F))
                  exact hs
                conv_lhs => rw [if_neg hsRaw]
                conv_rhs => simp only [if_neg hs]
                simp
            _ = ∑ x : Qt, ∑ d : Qk,
                (if supports d then chiPow D v (d.out : F) k *
                  (chiPow D v (x.out : F) t *
                    A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)))
                 else 0) := Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                _ = ∑ d : Qk, chiPow D v (x.out : F) t *
                    (if supports d then chiPow D v (d.out : F) k *
                      A.ψ v (algebraMap F (v.adicCompletion F) (arg d x))
                     else 0) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  by_cases hs : supports d
                  · have hsRaw : ∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F) := by
                      change ∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)
                      exact hs
                    conv_lhs => rw [if_pos hs]
                    conv_rhs => simp only [if_pos hs]
                    ring
                  · have hsRaw : ¬ (∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)) := by
                      change ¬ (∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F))
                      exact hs
                    conv_lhs => rw [if_neg hs]
                    conv_rhs => simp only [if_neg hs]
                    simp
                _ = _ := by rw [Finset.mul_sum]
        have hpGen : S.IsGen (p : F) v.asIdeal := by
          have h := (bc.gen_spec pi).1
          simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
        obtain ⟨_, _, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hpGen
        obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
        let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
          ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
        have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
            residue v ((liftResidue a : S.R) : F) = a := by
          change residue v (algebraMap (𝓞 F) F a.out) = a
          calc
            _ = Ideal.Quotient.mk v.asIdeal a.out :=
              (a2_bridge_SYMBOL D S).residue_algebraMap v a.out
            _ = a := Ideal.Quotient.mk_out a
        have hresZero : residue v (0 : F) = 0 := by
          simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
        have hresEqZero : resEq (0 : Q1) = 0 := by
          have hmk0 : Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR pi}) (0 : S.R) = (0 : Q1) := by simp
          rw [← hmk0]
          exact (hresEqMk 0).trans hresZero
        have hresRhoDelta (deltaR : S.R)
            (hdelta : residue v (deltaR : F) = 0) :
            rhoK (Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR Ik}) deltaR) = 0 := by
          apply hresEqBij.1
          calc
            resEq (rhoK (Ideal.Quotient.mk
                (Ideal.span {R.exterior.genR Ik}) deltaR)) =
                residue v (deltaR : F) := by
              rw [hrhoKMk, hresEqMk]
            _ = 0 := hdelta
            _ = resEq 0 := hresEqZero.symm
        have hresPkm1 : residue v (pRKm1 : F) = 0 := by
          rw [← hpRKm1, hresPowZero (k - 1) (by omega)]
        have hcoeffDelta :
            (p : F) ^ t * (pRKm1 : F) / (p : F) ^ (k + t) =
              1 / (p : F) := by
          rw [← hpRKm1]
          have hexp : k + t = t + (k - 1) + 1 := by omega
          calc
            _ = (p : F) ^ (t + (k - 1)) / (p : F) ^ (k + t) := by
              rw [← pow_add]
            _ = (p : F) ^ (t + (k - 1)) /
                (p : F) ^ (t + (k - 1) + 1) := by rw [hexp]
            _ = _ := by
              rw [pow_succ]
              field_simp [Units.ne_zero p]
        have hcoeffError :
            (p : F) ^ t * (pRK : F) / (p : F) ^ (k + t) = 1 := by
          rw [← hpK]
          calc
            _ = (p : F) ^ (t + k) / (p : F) ^ (k + t) := by
              rw [← pow_add]
            _ = _ := by rw [Nat.add_comm t k]; field_simp [Units.ne_zero p]
        let supportsD : Qk → Prop := supports
        have hDsumZero (x : Qt)
            (hxmask : chiPow D v (x.out : F) t ≠ 0) :
            (∑ d : Qk, (if supportsD d then chiPow D v (d.out : F) k *
              A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) else 0)) = 0 := by
          let a : 𝓞 F ⧸ v.asIdeal := resEq (rho x)
          have hresx : residue v (x.out : F) = a := (hresReduce x).symm
          have hresxNe : residue v (x.out : F) ≠ 0 := by
            intro hzero
            have hzpow := SB.chiPow_zero v (x.out : F) (t : ℤ) hzero
            rw [hzpow] at hxmask
            exact hxmask rfl
          have ha : a ≠ 0 := by rw [← hresx]; exact hresxNe
          have hψshiftNe : ψ.mulShift a ≠ 1 := hψprim ha
          have hψwitness : ∃ b : 𝓞 F ⧸ v.asIdeal, ψ.mulShift a b ≠ 1 := by
            by_contra h
            push_neg at h
            apply hψshiftNe
            ext b
            exact h b
          obtain ⟨b, hb⟩ := hψwitness
          let c : ℂ := ψ.mulShift a b
          have hcne : c ≠ 1 := hb
          have hcval : c = ψ (b * a) := by
            change ψ (a * b) = ψ (b * a)
            exact congrArg ψ (mul_comm a b)
          let lambdaR : S.R := liftResidue b
          let prodLift : S.R := liftResidue b * liftResidue a
          let prodR : S.R := liftResidue b * x.out
          have hresProdR : residue v (prodR : F) = b * a := by
            change residue v ((liftResidue b : S.R) * x.out : F) = b * a
            rw [SB.residue_mul v (liftResidue b : F) (x.out : F)
              ((liftResidue b).property v hv) (x.out.property v hv),
              hresLift, hresx]
          have hresProdLift : residue v (prodLift : F) = b * a := by
            change residue v ((liftResidue b : S.R) *
              (liftResidue a : S.R) : F) = b * a
            rw [SB.residue_mul v (liftResidue b : F) (liftResidue a : F)
              ((liftResidue b).property v hv) ((liftResidue a).property v hv),
              hresLift, hresLift]
          have hψevalProd : ψ (b * a) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((prodLift : F) / (p : F))) := by
            have hprodLift : (prodLift : F) =
                (liftResidue b : F) * (liftResidue a : F) := by
              rfl
            calc
              ψ (b * a) = ψ (a * b) := by congr 1 <;> exact (mul_comm b a)
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (((liftResidue b : F) * (liftResidue a : F)) / (p : F))) :=
                hψeval a b
              _ = _ := by rw [← hprodLift]
          have hphaseValue :
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((prodR : F) / (p : F))) = c := by
            have hresProd : residue v (prodR : F) = residue v (prodLift : F) :=
              hresProdR.trans hresProdLift.symm
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    ((prodLift : F) / (p : F))) :=
                euler_addchar_div_residue_congr D A v hv p hpVal
                  prodR prodLift hresProd
              _ = ψ (b * a) := hψevalProd.symm
              _ = c := hcval.symm
          let deltaR : S.R := pRKm1 * lambdaR
          have hresDelta : residue v (deltaR : F) = 0 := by
            change residue v ((pRKm1 : F) * (lambdaR : F)) = 0
            rw [SB.residue_mul v (pRKm1 : F) (lambdaR : F)
              (pRKm1.property v hv) (lambdaR.property v hv), hresPkm1]
            simp
          let δ : Qk := Ideal.Quotient.mk
            (Ideal.span {R.exterior.genR Ik}) deltaR
          have hrhoδ : rhoK δ = 0 := hresRhoDelta deltaR hresDelta
          let τ : Qk ≃ Qk := {
            toFun := fun d => d + δ
            invFun := fun d => d - δ
            left_inv := by intro d; simp
            right_inv := by intro d; simp }
          have hresτ (d : Qk) :
              residue v ((τ d).out : F) = residue v (d.out : F) := by
            have hredτ : rhoK (τ d) = rhoK d := by
              calc
                rhoK (τ d) = rhoK (d + δ) := rfl
                _ = rhoK d + rhoK δ := rhoK.map_add d δ
                _ = rhoK d := by rw [hrhoδ]; simp
            calc
              _ = resEq (rhoK (τ d)) := (hresReduceK (τ d)).symm
              _ = resEq (rhoK d) := by rw [hredτ]
              _ = _ := hresReduceK d
          have hquotτ (d : Qk) :
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik}) (τ d).out =
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                  (d.out + deltaR) := by
            calc
              _ = τ d := Ideal.Quotient.mk_out (τ d)
              _ = d + δ := rfl
              _ = _ := by simp [δ]
          have hmemK (d : Qk) :
              (τ d).out - (d.out + deltaR) ∈
                Ideal.span ({pRK} : Set S.R) := by
            have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
              (τ d).out (d.out + deltaR)).mp (hquotτ d)
            exact hspanK.symm ▸ hm
          let aLift (d : Qk) : S.R :=
            Classical.choose (Ideal.mem_span_singleton.mp (hmemK d))
          have haLift (d : Qk) :
              (τ d).out - (d.out + deltaR) = pRK * aLift d :=
            Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemK d))
          have hdelta (d : Qk) :
              (τ d).out - d.out = deltaR + pRK * aLift d := by
            calc
              _ = ((τ d).out - (d.out + deltaR)) + deltaR := by ring
              _ = pRK * aLift d + deltaR := by rw [haLift]
              _ = _ := by ring
          have hmulDiff (d : Qk) :
              pRT * (τ d).out - pRT * d.out ∈
                Ideal.span ({pRK} : Set S.R) := by
            apply Ideal.mem_span_singleton.mpr
            refine ⟨pRTm1 * lambdaR + pRT * aLift d, ?_⟩
            apply Subtype.ext
            calc
              ((pRT * (τ d).out - pRT * d.out : S.R) : F) =
                  (pRT : F) * (((τ d).out : F) - (d.out : F)) := by
                simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
                ring
              _ = (pRT : F) *
                    ((deltaR : F) + (pRK : F) * (aLift d : F)) := by
                have hdeltaF := congrArg (fun y : S.R => (y : F)) (hdelta d)
                change ((τ d).out : F) - (d.out : F) =
                  (deltaR : F) + (pRK : F) * (aLift d : F) at hdeltaF
                rw [hdeltaF]
              _ = (pRK : F) *
                    ((pRTm1 : F) * (lambdaR : F) +
                      (pRT : F) * (aLift d : F)) := by
                dsimp [deltaR]
                calc
                  _ = ((pRT : F) * (pRKm1 : F)) * (lambdaR : F) +
                      ((pRT : F) * (pRK : F)) * (aLift d : F) := by ring
                  _ = ((pRK : F) * (pRTm1 : F)) * (lambdaR : F) +
                      ((pRT : F) * (pRK : F)) * (aLift d : F) := by rw [hpCross]
                  _ = _ := by ring
          have hsupportτ (d : Qk) : supports (τ d) ↔ supports d := by
            have hmkMul :
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                    (pRT * (τ d).out) =
                  Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                    (pRT * d.out) := by
              apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
              have hmemMul : pRT * (τ d).out - pRT * d.out ∈
                  Ideal.span {R.exterior.genR Ik} := by
                simpa only [hspanK] using hmulDiff d
              exact hmemMul
            rw [hsupportQuot (τ d), hsupportQuot d]
            constructor
            · intro h
              exact h.trans hmkMul
            · intro h
              exact h.trans hmkMul.symm
          let f : Qk → ℂ := fun d =>
            if supportsD d then chiPow D v (d.out : F) k *
              A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) else 0
          have hphaseTrans (d : Qk) :
              A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ d) x)) =
                c * A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) := by
            have hpne : (p : F) ≠ 0 := Units.ne_zero p
            have hcoeffDelta :
                (p : F) ^ t * (pRKm1 : F) / (p : F) ^ (k + t) =
                  1 / (p : F) := by
              rw [← hpRKm1]
              have hexp : k + t = t + (k - 1) + 1 := by omega
              calc
                _ = (p : F) ^ (t + (k - 1)) / (p : F) ^ (k + t) := by
                  rw [← pow_add]
                _ = (p : F) ^ (t + (k - 1)) /
                    (p : F) ^ (t + (k - 1) + 1) := by rw [hexp]
                _ = _ := by rw [pow_succ]; field_simp [hpne]
            have hcoeffError :
                (p : F) ^ t * (pRK : F) / (p : F) ^ (k + t) = 1 := by
              rw [← hpK]
              calc
                _ = (p : F) ^ (t + k) / (p : F) ^ (k + t) := by
                  rw [← pow_add]
                _ = _ := by rw [Nat.add_comm t k]; field_simp [hpne]
            have hscaleDelta :
                (p : F) ^ t * (deltaR : F) / (p : F) ^ (k + t) =
                  (lambdaR : F) / (p : F) := by
              dsimp [deltaR]
              calc
                _ = ((p : F) ^ t * (pRKm1 : F) /
                    (p : F) ^ (k + t)) * (lambdaR : F) := by ring
                _ = _ := by rw [hcoeffDelta]; ring
            have hargDiff (d : Qk) :
                arg (τ d) x - (arg d x +
                    (prodR : F) / (p : F)) =
                  ((aLift d * x.out : S.R) : F) := by
              calc
                _ = (((p : F) ^ t * (deltaR : F) /
                      (p : F) ^ (k + t)) * (x.out : F)) +
                    (((p : F) ^ t * (pRK : F) /
                      (p : F) ^ (k + t)) * (aLift d : F) * (x.out : F)) -
                    (prodR : F) / (p : F) := by
                  dsimp [arg]
                  have hrep : (τ d).out = d.out + deltaR + pRK * aLift d := by
                    calc
                      _ = ((τ d).out - d.out) + d.out := by ring
                      _ = deltaR + pRK * aLift d + d.out := by rw [hdelta]
                      _ = _ := by ring
                  rw [hrep]
                  dsimp [prodR]
                  field_simp [hpne]
                  ring
                _ = ((aLift d * x.out : S.R) : F) := by
                  rw [hscaleDelta, hcoeffError]
                  dsimp [prodR]
                  ring
            have hargVal (d : Qk) :
                HeightOneSpectrum.valuation F v
                  (arg (τ d) x - (arg d x + (prodR : F) / (p : F))) ≤ 1 := by
              rw [hargDiff d]
              exact (aLift d * x.out).property v hv
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                  (arg d x + (prodR : F) / (p : F))) :=
                euler_addchar_congr_integral A v (arg (τ d) x)
                  (arg d x + (prodR : F) / (p : F)) (hargVal d)
              _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    ((prodR : F) / (p : F))) := by
                rw [← (A.ψ v).map_add_eq_mul]
                simp
              _ = _ := by rw [hphaseValue]; ring
          have htrans (d : Qk) : f (τ d) = c * f d := by
            by_cases hs : supportsD d
            · have hsτ : supportsD (τ d) := (hsupportτ d).2 hs
              have hchi := euler_chiPow_residue_congr D S v
                ((τ d).out : F) (d.out : F) k (hresτ d)
              simp only [f, if_pos hsτ, if_pos hs]
              rw [hchi, hphaseTrans]
              ring
            · have hsτ : ¬ supportsD (τ d) := by
                intro h
                exact hs ((hsupportτ d).1 h)
              simp [f, hs, hsτ]
          have hsumShift : (∑ d : Qk, f d) = ∑ d : Qk, f (τ d) := by
            exact Fintype.sum_equiv τ.symm _ _ (by intro d; simp)
          have hsumMul : (∑ d : Qk, f (τ d)) = c * ∑ d : Qk, f d := by
            calc
              _ = ∑ d : Qk, c * f d := by
                apply Finset.sum_congr rfl
                intro d hd
                exact htrans d
              _ = _ := by rw [Finset.mul_sum]
          have hsumEq : (∑ d : Qk, f d) = c * ∑ d : Qk, f d :=
            hsumShift.trans hsumMul
          have hsumZero : (∑ d : Qk, f d) = 0 := by
            have hmul : (1 - c) * (∑ d : Qk, f d) = 0 := by
              calc
                _ = (∑ d : Qk, f d) - c * ∑ d : Qk, f d := by ring
                _ = 0 := by rw [← hsumEq]; ring
            have hcnz : 1 - c ≠ 0 := by
              intro heq
              exact hcne (sub_eq_zero.mp heq).symm
            exact (mul_eq_zero.mp hmul).resolve_left hcnz
          exact hsumZero
        have hresSum : localC R v hv t k J = 0 := by
          rw [hCsum]
          apply Finset.sum_eq_zero
          intro x hx
          by_cases hχx : chiPow D v (x.out : F) t = 0
          · simp [hχx]
          · rw [hDsumZero x hχx]
            simp
        exact hresSum
      · by_cases hcut : t - 1 ≤ J
        · let m : ℕ := J + 1 - t
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hT := euler_localT_norm_le R v hv (t : ℤ) pRm
          have hT' : ‖localT R v t ((primeGen R v : F) ^ m)‖ ≤
              qI v.asIdeal := by
            simpa [hpm] using hT
          have hqnonneg : 0 ≤ qI v.asIdeal := by simp [qI]
          have hpowNorm :
              ‖(qI v.asIdeal : ℂ) ^ (t - 1)‖ = qI v.asIdeal ^ (t - 1) := by
            rw [norm_pow]
            simp [qI, Real.norm_eq_abs, abs_of_nonneg hqnonneg]
          rw [h0, if_pos hcut]
          calc
            ‖(qI v.asIdeal : ℂ) ^ (t - 1) *
                localT R v t ((primeGen R v : F) ^ (J + 1 - t))‖ =
                qI v.asIdeal ^ (t - 1) *
                  ‖localT R v t ((primeGen R v : F) ^ (J + 1 - t))‖ := by
              rw [norm_mul, hpowNorm]
            _ ≤ qI v.asIdeal ^ (t - 1) * qI v.asIdeal :=
              mul_le_mul_of_nonneg_left hT'
                (pow_nonneg hqnonneg (t - 1))
            _ = qI v.asIdeal ^ t := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega)]
            _ = qI v.asIdeal ^ (t : ℝ) := by
              rw [Real.rpow_natCast]
        · rw [h0, if_neg hcut]
          simpa only [norm_zero] using
            (Real.rpow_nonneg (show 0 ≤ qI v.asIdeal by simp [qI]) (t : ℝ))
      · by_cases hcut : t ≤ J
        · rw [hC1, if_pos hcut]
          let m : ℕ := J - t
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hT2 :
              ‖localT R v ((t : ℤ) - 1)
                ((primeGen R v : F) ^ (J - t))‖ ≤ qI v.asIdeal := by
            have h := euler_localT_norm_le R v hv ((t : ℤ) - 1) pRm
            simpa [m, hpm] using h
          have hT1 : ‖localT R v 1 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ) := by
            exact (po_C_local_T_values R v hv (1 : ℤ) (1 : S.R)).2.1
              (by norm_num)
          have hqnonneg : 0 ≤ qI v.asIdeal := by simp [qI]
          have hqpos : 0 < qI v.asIdeal := by
            have hqone : 1 < qI v.asIdeal := by
              have hn : 1 < Ideal.absNorm v.asIdeal :=
                HeightOneSpectrum.one_lt_absNorm v
              have hr : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
                exact_mod_cast hn
              simpa [qI] using hr
            linarith
          have hpowNorm :
              ‖(qI v.asIdeal : ℂ) ^ (t - 1)‖ = qI v.asIdeal ^ (t - 1) := by
            rw [norm_pow]
            simp [qI, Real.norm_eq_abs, abs_of_nonneg hqnonneg]
          have hpowComb :
              qI v.asIdeal ^ (1 / 2 : ℝ) *
                qI v.asIdeal ^ (t - 1) * qI v.asIdeal =
                  qI v.asIdeal ^ ((t : ℝ) + 1 / 2) := by
            calc
              _ = qI v.asIdeal ^ (1 / 2 : ℝ) *
                  qI v.asIdeal ^ ((t - 1 : ℕ) : ℝ) *
                  qI v.asIdeal ^ (1 : ℝ) := by simp [Real.rpow_natCast]
              _ = qI v.asIdeal ^ ((1 / 2 : ℝ) +
                  ((t - 1 : ℕ) : ℝ) + 1) := by
                rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
              _ = _ := by
                congr 1
                have ht : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
                  norm_cast
                  omega
                calc
                  _ = ((t - 1 : ℕ) : ℝ) + 1 + (1 / 2 : ℝ) := by ring
                  _ = (t : ℝ) + 1 / 2 := by rw [ht]
          calc
            _ = ‖localT R v 1 1‖ * qI v.asIdeal ^ (t - 1) *
                ‖localT R v ((t : ℤ) - 1)
                  ((primeGen R v : F) ^ (J - t))‖ := by
              simp only [norm_mul, hpowNorm]
            _ ≤ qI v.asIdeal ^ (1 / 2 : ℝ) *
                qI v.asIdeal ^ (t - 1) * qI v.asIdeal := by
              rw [hT1]
              exact mul_le_mul_of_nonneg_left hT2
                (mul_nonneg (Real.rpow_nonneg hqnonneg _)
                  (pow_nonneg hqnonneg _))
            _ = qI v.asIdeal ^ ((t : ℝ) + 1 / 2) := hpowComb
        · rw [hC1, if_neg hcut]
          simpa only [norm_zero] using
            (Real.rpow_nonneg (show 0 ≤ qI v.asIdeal by simp [qI])
              ((t : ℝ) + 1 / 2))


private theorem euler_hecke_prime_norm_le
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) :
    ‖ϑ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with h
  · have hunit := ReflectionSetup.vartheta_unitary R0
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) )
    exact le_of_eq (by simpa [HeckeChar.loc] using hunit)
  · simp


private theorem euler_chi_zpow_norm_le_one (v : FinPlace F) (x : F) (n : ℤ) :
    ‖chi D v x ^ n‖ ≤ 1 := by
  by_cases hx : residue v x = 0
  · cases n with
    | ofNat k => by_cases hk : k = 0 <;> simp [chi, hx, hk]
    | negSucc k => simp [chi, hx]
  · simpa [norm_zpow, po_chi_norm_one D v x hx]


private theorem euler_trace_eq_pair_sum_re [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
  have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
    rw [hring.symm] at htrace
    exact htrace
  rw [hall]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
  apply Finset.sum_congr rfl
  intro w hw
  have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
      φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w] at h
      have h' := InfinitePlace.mk_eq_iff.mp h
      rcases h' with h' | h'
      · exact Or.inl (by simpa using h')
      · right
        have hc := congrArg ComplexEmbedding.conjugate h'
        simpa using hc
    · intro h
      rw [← InfinitePlace.mk_embedding w]
      apply InfinitePlace.mk_eq_iff.mpr
      rcases h with h | h
      · exact Or.inl (by simpa using h)
      · right
        have hc := congrArg ComplexEmbedding.conjugate h
        simpa using hc
  have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    apply (IsTotallyComplex.complexEmbedding_not_isReal w.embedding)
    rw [ComplexEmbedding.isReal_iff]
    exact h.symm
  have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
    ext φ
    simp [hmk]
  change (∑ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
  rw [hset, Finset.sum_pair hneq]


private theorem euler_trace_eq_two_real_sum [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  rw [euler_trace_eq_pair_sum_re]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]


private theorem euler_arch_exp_eq_trace [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F, psiC (w.embedding z)) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  change (∏ w : InfinitePlace F,
      Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) = _
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F, -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
          rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
          rw [euler_trace_eq_two_real_sum]
          ring


private theorem euler_primeGen_isGen (v : FinPlace F) (hv : v ∉ S.Sf) :
    S.IsGen (primeGen R v : F) v.asIdeal := by
  have h := (bc.gen_spec (R.exterior.prime v hv)).1
  simpa [primeGen, hv, R.exterior.prime_val] using h


private theorem euler_primeGen_other_valuation (v : FinPlace F) (hv : v ∉ S.Sf)
    (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
    HeightOneSpectrum.valuation F w (primeGen R v : F) = 1 := by
  have hpGen := euler_primeGen_isGen R v hv
  have hnotdvd : ¬ w.asIdeal ∣ v.asIdeal := by
    intro hdiv
    have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd hdiv
    have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hwv (HeightOneSpectrum.ext heq.symm)
  have hcountNat : (Associates.mk w.asIdeal).count (Associates.mk v.asIdeal).factors = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hnotdvd ((Associates.count_ne_zero_iff_dvd v.ne_bot w.irreducible).mp
      (Nat.ne_of_gt hpos))
  have hcount0 : FractionalIdeal.count F w
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    rw [FractionalIdeal.count_coe F w v.ne_bot]
    exact_mod_cast hcountNat
  have hcountp := hpGen.2.2 w hw
  rw [hcount0] at hcountp
  have hlog := euler_count_spanSingleton_eq_neg_log_valuation w
    (primeGen R v : F) hpGen.2.1
  rw [hcountp] at hlog
  have hlog0 : WithZero.log (HeightOneSpectrum.valuation F w (primeGen R v : F)) = 0 := by
    linarith
  have hvalne : HeightOneSpectrum.valuation F w (primeGen R v : F) ≠ 0 :=
    (w.valuation F).ne_zero_iff.mpr hpGen.2.1
  calc
    HeightOneSpectrum.valuation F w (primeGen R v : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F w (primeGen R v : F))) :=
      (WithZero.exp_log hvalne).symm
    _ = 1 := by rw [hlog0, WithZero.exp_zero]


private theorem euler_additive_phase_at_prime (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : 𝓞 F ⧸ v.asIdeal) :
    S.e A (S.diag (algebraMap (𝓞 F) F x.out / (primeGen R v : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-(algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) := by
  classical
  let z : F := algebraMap (𝓞 F) F x.out / (primeGen R v : F)
  let f : FinPlace F → ℂ := fun w => A.ψ w (algebraMap F (w.adicCompletion F) z)
  have hvalz (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
      HeightOneSpectrum.valuation F w z ≤ 1 := by
    by_cases hx : x.out = 0
    · simp [z, hx]
    have hvalx : HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) ≤ 1 :=
      w.valuation_le_one x.out
    calc
      HeightOneSpectrum.valuation F w z =
          HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) /
            HeightOneSpectrum.valuation F w (primeGen R v : F) := by
              dsimp [z]
              rw [map_div₀]
      _ = HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) := by
            rw [euler_primeGen_other_valuation R v hv w hw hwv, div_one]
      _ ≤ 1 := hvalx
  have hsupport : Function.mulSupport f ⊆
      ((insert v S.Sf : Finset (FinPlace F)) : Set (FinPlace F)) := by
    intro w hw
    change f w ≠ 1 at hw
    by_cases hws : w ∈ S.Sf
    · exact Finset.mem_insert_of_mem hws
    · by_cases hwv : w = v
      · simp [hwv]
      · have hmem : (algebraMap F (w.adicCompletion F) z) ∈
          w.adicCompletionIntegers F := by
          change ((z : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
          rw [HeightOneSpectrum.mem_adicCompletionIntegers,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
          exact hvalz w hws hwv
        exact (hw (A.integral w _ hmem)).elim
  have hfinprod : (∏ᶠ w : FinPlace F, f w) = ∏ w ∈ insert v S.Sf, f w :=
    finprod_eq_prod_of_mulSupport_subset f hsupport
  have hattach : (∏ w : S.Sf, f w) = ∏ w ∈ S.Sf, f w := by
    simp [Finset.prod_attach]
  have hglobal := (A.trivial_on_F z).2
  have hglobal' : f v * ((∏ w : S.Sf, f w) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) = 1 := by
    rw [hfinprod, Finset.prod_insert (by simpa using hv)] at hglobal
    rw [← hattach] at hglobal
    simpa [f, z, mul_assoc] using hglobal
  have hSprod : (∏ w : S.Sf, f w) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = (f v)⁻¹ := by
    have hcomm : ((∏ w : S.Sf, f w) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) * f v = 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hglobal'
    exact eq_inv_of_mul_eq_one_left hcomm
  have hE : S.e A (S.diag z) = (∏ w : S.Sf, f w) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
    letI : IsTotallyComplex F := D.isTotallyComplex
    change (∏ w : S.Sf, A.ψ w.1 (algebraMap F (w.1.adicCompletion F) z)) *
      ∏ w : InfinitePlace F, psiC (w.embedding z) = _
    rw [euler_arch_exp_eq_trace]
  calc
    S.e A (S.diag z) = (∏ w : S.Sf, f w) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := hE
    _ = (f v)⁻¹ := hSprod
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (-z)) := by
      change (A.ψ v (algebraMap F (v.adicCompletion F) z))⁻¹ = _
      rw [← AddChar.inv_apply' (A.ψ v) (algebraMap F (v.adicCompletion F) z)]
      rw [AddChar.inv_apply]
      simp


private theorem euler_gamma_localT (v : FinPlace F) (hv : v ∉ S.Sf) (e : ℤ) :
    gamma D S A e v.asIdeal (primeGen R v : F) =
      (((qI v.asIdeal) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * localT R v e 1 := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let Q := 𝓞 F ⧸ v.asIdeal
  have hvprime : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
  have hIdealPow (x : Q) :
      chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) e =
        chiPow D v (algebraMap (𝓞 F) F x.out) e := by
    unfold chiIdealPow
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hvprime.irreducible]
    simp [v.isPrime, v.ne_bot]
  have hsum :
      (∑ x : Q, chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) e *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) =
      ∑ x : Q, chiPow D v (algebraMap (𝓞 F) F x.out) e *
        A.ψ v (algebraMap F (v.adicCompletion F)
          (-(algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hIdealPow x, euler_additive_phase_at_prime R v hv x]
  unfold gamma localT
  simp only [qI, one_mul]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  congr 1


private theorem po_H_absolute_gamma_norm_one
    (v : FinPlace F) (hv : v ∉ S.Sf) (e : ℤ) (he : e % 6 ≠ 0) :
    ‖gamma D S A e v.asIdeal (primeGen R v : F)‖ = 1 := by
  have hq : 0 < qI v.asIdeal := lt_trans zero_lt_one (qI_prime_gt_one v)
  have hT := (po_C_local_T_values R v hv e (1 : S.R)).2.1 he
  rw [euler_gamma_localT R v hv e, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _)]
  rw [hT, ← Real.rpow_add hq]
  norm_num


theorem po_H_absolute_positive_term_norm_le
    (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (i : Fin 2 × ℕ × ℕ × ℕ)
    (ht : 0 < i.1.1 + 3 * i.2.1) (hk : i.2.2.1 ≤ 1) :
    ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
      qI v.asIdeal ^
        ((i.1.1 : ℝ) * (1 / 2 - ξ.re) +
          (i.2.1 : ℝ) * (2 - 3 * ξ.re) +
          (i.2.2.1 : ℝ) * (1 / 2 - w.re) -
          6 * (i.2.2.2 : ℝ) * z.re) := by
  let e : ℕ := i.1.1
  let l : ℕ := i.2.1
  let k : ℕ := i.2.2.1
  let m : ℕ := i.2.2.2
  let j : ℕ := frequencyValuation η U u v
  let E : ℂ := -(e : ℂ) * (1 / 2 + ξ) - (l : ℂ) * (1 + 3 * ξ) -
    (k : ℂ) * w - 6 * (m : ℂ) * z
  have hqpos : 0 < qI v.asIdeal := lt_trans zero_lt_one (qI_prime_gt_one v)
  have hgamma : ‖gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e‖ = 1 := by
    rw [norm_pow, po_H_absolute_gamma_norm_one R v hv 2 (by norm_num), one_pow]
  have htheta : ‖ϑ.primeValue v ^ (e + 3 * l)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (euler_hecke_prime_norm_le R v)
  have hchi := euler_chi_zpow_norm_le_one (D := D) v
    ((U.repr u : F) / (primeGen R v : F) ^ j)
    ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ))
  have hCT := (po_C_local_values R v hv (j + 6 * m)).2.2 (e + 3 * l) ht
  have hC : ‖localC R v hv (e + 3 * l) k (j + 6 * m)‖ ≤
      qI v.asIdeal ^ (((e + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2) := by
    by_cases hk0 : k = 0
    · simpa [hk0, Real.rpow_natCast] using hCT.2.2.2.1
    · have hk1 : k = 1 := by change i.2.2.1 = 1; omega
      simpa [hk1] using hCT.2.2.2.2
  have hpow : ‖(qI v.asIdeal : ℂ) ^ E‖ = qI v.asIdeal ^ E.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hqpos E
  have hEre : E.re =
      -(e : ℝ) * (1 / 2 + ξ.re) - (l : ℝ) * (1 + 3 * ξ.re) -
        (k : ℝ) * w.re - 6 * (m : ℝ) * z.re := by
    simp [E, Complex.mul_re] <;> ring
  have htotal : ((e + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2 + E.re =
      (e : ℝ) * (1 / 2 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
        (k : ℝ) * (1 / 2 - w.re) - 6 * (m : ℝ) * z.re := by
    rw [hEre]
    push_cast
    ring
  change ‖gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e *
      ϑ.primeValue v ^ (e + 3 * l) *
      chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^
        ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
      localC R v hv (e + 3 * l) k (j + 6 * m) *
      (qI v.asIdeal : ℂ) ^ E‖ ≤
    qI v.asIdeal ^ ((e : ℝ) * (1 / 2 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
      (k : ℝ) * (1 / 2 - w.re) - 6 * (m : ℝ) * z.re)
  calc
    _ = 1 * ‖ϑ.primeValue v ^ (e + 3 * l)‖ *
        ‖chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^
          ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ))‖ *
        ‖localC R v hv (e + 3 * l) k (j + 6 * m)‖ *
        qI v.asIdeal ^ E.re := by rw [norm_mul, norm_mul, norm_mul, norm_mul, hgamma, hpow]
    _ ≤ 1 * 1 * 1 *
        qI v.asIdeal ^ (((e + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2) *
        qI v.asIdeal ^ E.re := by gcongr
    _ = qI v.asIdeal ^ (((e + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2 + E.re) := by
      simp only [one_mul]
      rw [← Real.rpow_add hqpos]
    _ = _ := by rw [htotal]


theorem term_norm_le (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (ξ w z : ℂ) (hξ : 2 / 3 < ξ.re) (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
      qI v.asIdeal ^ (1 / 2 + (i.2.1 : ℝ) * (2 - 3 * ξ.re) -
        (i.2.2.1 : ℝ) * w.re - 6 * (i.2.2.2 : ℝ) * z.re) := by
  let q : ℝ := qI v.asIdeal
  have hq : 1 < q := qI_prime_gt_one v
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  let e : ℕ := i.1.1
  let l : ℕ := i.2.1
  let k : ℕ := i.2.2.1
  let m : ℕ := i.2.2.2
  let j : ℕ := frequencyValuation η U u v
  change ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
    q ^ (1 / 2 + (l : ℝ) * (2 - 3 * ξ.re) - (k : ℝ) * w.re -
      6 * (m : ℝ) * z.re)
  by_cases ht : e + 3 * l = 0
  · have he : e = 0 := by omega
    have hl : l = 0 := by omega
    have hC : ‖localC R v hv 0 k (j + 6 * m)‖ ≤ 1 := by
      by_cases hk : k = 0
      · simp [hk, (po_C_local_values R v hv (j + 6 * m)).1]
      · rw [(po_C_local_values R v hv (j + 6 * m)).2.1 k
          (Nat.pos_of_ne_zero hk)]
        split_ifs <;> simp
    have hchi := euler_chi_zpow_norm_le_one (D := D) v
      ((U.repr u : F) / (primeGen R v : F) ^ j) (k : ℤ)
    let E : ℂ := -(k : ℂ) * w - 6 * (m : ℂ) * z
    have hpow : ‖(q : ℂ) ^ E‖ = q ^ E.re :=
      Complex.norm_cpow_eq_rpow_re_of_pos hqpos E
    have hEre : E.re = -(k : ℝ) * w.re - 6 * (m : ℝ) * z.re := by
      simp [E, Complex.mul_re] <;> ring
    have hn :
        ‖chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^ (k : ℤ) *
          localC R v hv 0 k (j + 6 * m) * (q : ℂ) ^ E‖ ≤ q ^ E.re := by
      rw [norm_mul, norm_mul, hpow]
      calc
        _ ≤ 1 * 1 * q ^ E.re := by gcongr
        _ = _ := by ring
    rw [hEre] at hn
    have he' : i.1.1 = 0 := he
    have hl' : i.2.1 = 0 := hl
    have hn' : ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
        q ^ (-(k : ℝ) * w.re - 6 * (m : ℝ) * z.re) := by
      simpa [localEulerTerm, he', hl', q, j, k, m, E] using hn
    refine hn'.trans (Real.rpow_le_rpow_of_exponent_le hq.le ?_)
    rw [hl]
    simp
  · have htpos : 0 < e + 3 * l := Nat.pos_of_ne_zero ht
    by_cases hk : k ≤ 1
    · have hs := po_H_absolute_positive_term_norm_le R η U u v hv ξ w z i htpos hk
      have hepart : (e : ℝ) * (1 / 2 - ξ.re) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg e) (by linarith)
      have hkcast : (k : ℝ) ≤ 1 := by exact_mod_cast hk
      have hexp : (e : ℝ) * (1 / 2 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
          (k : ℝ) * (1 / 2 - w.re) - 6 * (m : ℝ) * z.re ≤
          1 / 2 + (l : ℝ) * (2 - 3 * ξ.re) - (k : ℝ) * w.re -
            6 * (m : ℝ) * z.re := by
        nlinarith only [hepart, hkcast]
      exact hs.trans (Real.rpow_le_rpow_of_exponent_le hq.le hexp)
    · have hkge : 2 ≤ k := by omega
      have hCzero := ((po_C_local_values R v hv (j + 6 * m)).2.2
        (e + 3 * l) htpos).2.2.1 k hkge
      have hzero : localEulerTerm R η U u v hv ξ w z i = 0 := by
        simp [localEulerTerm, hCzero, e, l, k, m, j]
      rw [hzero, norm_zero]
      exact Real.rpow_nonneg hqpos.le _
end ArtinPrimitiveRoots.Proofs.e_f
