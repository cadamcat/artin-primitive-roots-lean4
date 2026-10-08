import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.Hecke.Dictionary

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rf_mom_p

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem finite_order_locInf_eq_one (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (w : InfinitePlace F) (hw : w.IsComplex) (z : ℂˣ) :
    χ.locInf w (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) = 1 := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    have hz' : (z : ℂ) = 0 := by
      calc
        (z : ℂ) = z₀ ^ n := hz₀.symm
        _ = 0 := by rw [hz]; simp [zero_pow hn0]
    exact (Units.ne_zero z) hz'
  let u : w.Completionˣ := Units.map e.symm.toMonoidHom (Units.mk0 z₀ hz₀ne)
  have hu : u ^ n = Units.map e.symm.toMonoidHom z := by
    apply Units.ext
    change (e.symm z₀) ^ n = e.symm (z : ℂ)
    simpa only [map_pow] using congrArg e.symm hz₀
  have hlocal (x : w.Completionˣ) : (χ.locInf w x) ^ n = 1 := by
    have h := congrArg (fun ψ : HeckeChar F => ψ.locInf w x) hpow
    simpa [HeckeChar.locInf] using h
  calc
    χ.locInf w (Units.map e.symm.toMonoidHom z) = χ.locInf w (u ^ n) := by rw [hu]
    _ = (χ.locInf w u) ^ n := by simp
    _ = 1 := hlocal u

private theorem heckeChar_mul_unramified_primeValue (χ ψ : HeckeChar F)
    (v : FinPlace F) (hχ : χ.UnramifiedAt v) (hψ : ψ.UnramifiedAt v) :
    (χ * ψ).UnramifiedAt v ∧ (χ * ψ).primeValue v = χ.primeValue v * ψ.primeValue v := by
  have hmul : (χ * ψ).UnramifiedAt v := by
    intro u hu huinv
    change χ.loc v u * ψ.loc v u = 1
    rw [hχ u hu huinv, hψ u hu huinv]
    simp
  refine ⟨hmul, ?_⟩
  simp [HeckeChar.primeValue, hmul, hχ, hψ, HeckeChar.loc]

private theorem finitePlace_isExterior {S : SData F CE condη} (v : FinPlace F)
    (hv : v ∉ S.Sf) : S.IsExterior v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  intro w hw hle
  have heqI : v.asIdeal = w.asIdeal :=
    Ideal.IsMaximal.eq_of_le (v.isPrime.isMaximal v.ne_bot) w.isPrime.ne_top hle
  have heq : v = w := HeightOneSpectrum.ext heqI
  subst w
  exact hv hw

/-- Recover the angular condition from the prime relation in `prop_reflection`. -/
theorem reflection_lambda_angular_of_gauss
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (A : AddCharData F)
    (Λ G : HeckeChar F) (hΛunit : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hGfin : IsOfFinOrder G)
    (hGauss : ∀ v : FinPlace F, v ∉ S.Sf →
      Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
          -(Λ.primeValue v * G.primeValue v)) :
    HeckeChar.HasAngularType D Λ := by
  obtain ⟨Λ₀, G₀, hG₀fin, hΛ₀unit, hΛ₀angular, htheta, hGauss₀⟩ :=
    gauss_characters D S A H Bd
  have hprodUnram : ∀ v, v ∉ S.Sf → (Λ * G).UnramifiedAt v := by
    intro v hv
    exact (heckeChar_mul_unramified_primeValue Λ G v (hGauss v hv).1 (hGauss v hv).2.1).1
  have hprodCanUnram : ∀ v, v ∉ S.Sf → (Λ₀ * G₀).UnramifiedAt v := by
    intro v hv
    exact (heckeChar_mul_unramified_primeValue Λ₀ G₀ v (hGauss₀ v hv).1
      (hGauss₀ v hv).2.1).1
  have hprime : ∀ v, v ∉ S.Sf →
      (Λ * G).primeValue v = (Λ₀ * G₀).primeValue v := by
    intro v hv
    have hIext : S.IsExterior v.asIdeal := finitePlace_isExterior v hv
    let p : Fˣ := Classical.choose (Bd.exists_allowed v.asIdeal hIext)
    have hp := Classical.choose_spec (Bd.exists_allowed v.asIdeal hIext)
    have hcur := (hGauss v hv).2.2 p hp.1 hp.2
    have hcan := ((hGauss₀ v hv).2.2 p hp.1 hp.2).2.2
    have hpair : Λ.primeValue v * G.primeValue v =
        Λ₀.primeValue v * G₀.primeValue v := by
      have hc : Λ.primeValue v * G.primeValue v =
          -(gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p) := by
        rw [hcur]
        simp
      have h₀ : Λ₀.primeValue v * G₀.primeValue v =
          -(gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p) := by
        rw [hcan]
        simp
      exact hc.trans h₀.symm
    rw [(heckeChar_mul_unramified_primeValue Λ G v (hGauss v hv).1
        (hGauss v hv).2.1).2,
      (heckeChar_mul_unramified_primeValue Λ₀ G₀ v (hGauss₀ v hv).1
        (hGauss₀ v hv).2.1).2]
    exact hpair
  have hprod : Λ * G = Λ₀ * G₀ := by
    apply ArtinPrimitiveRoots.Dictionary.heckeChar_eq_of_primeValue
      (Λ * G) (Λ₀ * G₀) S.Sf
    intro v hv
    exact ⟨hprodUnram v hv, hprodCanUnram v hv, hprime v hv⟩
  have hΛeq : Λ = Λ₀ * G₀ * G⁻¹ := by
    calc
      Λ = (Λ * G) * G⁻¹ := by group
      _ = (Λ₀ * G₀) * G⁻¹ := by rw [hprod]
  intro w
  rcases hΛ₀angular w with ⟨m, hm, hloc⟩
  refine ⟨m, hm, ?_⟩
  intro z
  let u := Units.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z
  have hglobalLocal := congrArg (fun χ : HeckeChar F => χ.locInf w u) hΛeq
  have hprodLocal : (Λ₀ * G₀ * G⁻¹).locInf w u =
      Λ₀.locInf w u * G₀.locInf w u * (G⁻¹).locInf w u := by
    simp [HeckeChar.locInf]
  have hInvLocal : (G⁻¹).locInf w u = (G.locInf w u)⁻¹ := by
    change (G⁻¹ (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) =
      (G (IdeleClassGroup.ofCompletion (𝓞 F) F w u))⁻¹
    rfl
  have hpoint : Λ.locInf w u =
      Λ₀.locInf w u * G₀.locInf w u * (G.locInf w u)⁻¹ :=
    hglobalLocal.trans (hprodLocal.trans (by rw [hInvLocal]))
  have hGvalue := finite_order_locInf_eq_one G hGfin w
    (D.isTotallyComplex.isComplex w) z
  have hG₀value := finite_order_locInf_eq_one G₀ hG₀fin w
    (D.isTotallyComplex.isComplex w) z
  have hGvalue' : G.locInf w u = 1 := by simpa [u] using hGvalue
  have hG₀value' : G₀.locInf w u = 1 := by simpa [u] using hG₀value
  change ((Λ.locInf w u : ℂˣ) : ℂ) = _
  rw [hpoint]
  rw [hG₀value', hGvalue']
  simp only [Units.val_mul, Units.val_inv, map_one, one_mul, inv_one]
  simpa [u] using hloc z

end ArtinPrimitiveRoots.Proofs.a2_rf_mom_p
