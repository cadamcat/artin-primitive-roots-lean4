import ArtinPrimitiveRoots.Theta.Cover
import TauCeti.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Every divisor supported outside `S_f` is the exterior divisor of a rational unit. -/
theorem th_classical_exterior_divisor_principal (D : FieldData F)
    (S : SData F CE condη) (H : HilbertData F)
    (e : FinPlace F →₀ ℤ) (he : ∀ v ∈ S.Sf, e v = 0) :
    ∃ a : Fˣ, ∀ v : FinPlace F, v ∉ S.Sf →
      v.valuation F (a : F) = WithZero.exp (-(e v)) := by
  classical
  have hprod (f : FinPlace F → ℕ) (hf : ∀ v ∉ e.support, f v = 0) :
      S.IsExterior (∏ v ∈ e.support, v.asIdeal ^ f v) ∧
        ∀ v : FinPlace F, FractionalIdeal.count F v
          ((∏ w ∈ e.support, w.asIdeal ^ f w : Ideal (𝓞 F)) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (f v : ℤ) := by
    let I : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ f v
    have hI : I ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv => pow_ne_zero _ v.ne_bot
    refine ⟨⟨hI, ?_⟩, ?_⟩
    · intro v hv hIv
      obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp hIv
      have hwv' : w.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le hwv
      have hwv'' : w = v :=
        HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv')
      subst w
      exact (e.mem_support_iff.mp hw) (he v hv)
    · intro v
      have hcast : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          ∏ w ∈ e.support,
            (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ f w := by
        change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F)
          (∏ w ∈ e.support, w.asIdeal ^ f w) = _
        simp only [map_prod, map_pow]
        rfl
      change FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = _
      rw [hcast, FractionalIdeal.count_prod F v _ _
        (fun w hw => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot))]
      simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      by_cases hv : v ∈ e.support
      · simp only [ite_eq_left hv]
      · simp only [ite_eq_right hv, hf v hv, Nat.cast_zero]
  let Ip : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ (e v).toNat
  let In : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ (-e v).toNat
  have hp := hprod (fun v => (e v).toNat) (by
    intro v hv
    simp only [Finsupp.notMem_support_iff.mp hv, Int.toNat_zero])
  have hn := hprod (fun v => (-e v).toNat) (by
    intro v hv
    simp only [Finsupp.notMem_support_iff.mp hv, neg_zero, Int.toNat_zero])
  obtain ⟨Bd⟩ := BData.nonempty D S H
  obtain ⟨ap, hap, _⟩ := Bd.exists_allowed Ip hp.1
  obtain ⟨an, han, _⟩ := Bd.exists_allowed In hn.1
  let a : Fˣ := ap / an
  refine ⟨a, ?_⟩
  intro v hv
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = e v := by
    simp only [a, Units.val_div_eq_div_val]
    rw [FractionalIdeal.count_spanSingleton_div F v ap.ne_zero an.ne_zero,
      hap.2.2 v hv, han.2.2 v hv, hp.2 v, hn.2 v]
    omega
  have hlog : -WithZero.log (v.valuation F (a : F)) = e v := by
    rw [← FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation F v a,
      coe_toPrincipalIdeal]
    exact hcount
  have hlog' : WithZero.log (v.valuation F (a : F)) = -(e v) := by omega
  rw [← hlog', WithZero.exp_log (by simpa only [ne_eq, Valuation.zero_iff] using a.ne_zero)]

end ArtinPrimitiveRoots.A1.Theta
