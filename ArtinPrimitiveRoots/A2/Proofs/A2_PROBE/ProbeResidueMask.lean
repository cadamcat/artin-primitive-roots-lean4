import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The sextic symbol masks every nonunit of the exact Gauss residue ring. -/
theorem probe_nonzero_residue_symbol_isUnit {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) :
    ∀ s : S.ExtIdeal, ∀ d : ResidueRing E s,
      chiIdealPow D s.1 (d.out : F) 1 ≠ 0 → IsUnit d := by
  intro s d hsymbol
  let J : Ideal S.R := Ideal.span {E.genR s}
  have hg : S.IsGen (E.genR s : F) s.1 := by
    rw [E.genR_val]
    exact (bc.gen_spec s).1
  have hintegral (a : 𝓞 F) (ha : a ∈ s.1) : algebraMap (𝓞 F) S.R a ∈ J := by
    by_cases ha0 : a = 0
    · simp [ha0, J]
    have haF : (a : F) ≠ 0 := (IsFractionRing.injective (𝓞 F) F).ne ha0
    have hspan : Ideal.span {a} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using ha0
    have hspanle : Ideal.span {a} ≤ s.1 :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)
    have hspanleF :
        (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
          (s.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
      (FractionalIdeal.coeIdeal_le_coeIdeal F).2 hspanle
    have hspanF : (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using hspan)
    have hratio : (a : F) / (E.genR s : F) ∈ S.R := by
      intro v hv
      have hcount : FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (E.genR s : F)) ≤
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
        calc
          _ = FractionalIdeal.count F v
              (s.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hg.2.2 v hv
          _ ≤ FractionalIdeal.count F v
              (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
            FractionalIdeal.count_mono F v hspanF hspanleF
          _ = _ := by rw [← FractionalIdeal.coeIdeal_span_singleton]
      rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ hg.2.1,
        qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ haF] at hcount
      have hlog : WithZero.log (v.valuation F (a : F)) ≤
          WithZero.log (v.valuation F (E.genR s : F)) := by linarith
      have hval := (WithZero.log_le_log ((v.valuation F).ne_zero_iff.mpr haF)
        ((v.valuation F).ne_zero_iff.mpr hg.2.1)).mp hlog
      rw [Valuation.map_div]
      exact (div_le_one₀
        (WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr hg.2.1))).2 hval
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨⟨(a : F) / (E.genR s : F), hratio⟩, ?_⟩
    apply Subtype.ext
    change ((a : F) / (E.genR s : F)) * (E.genR s : F) = (a : F)
    exact div_mul_cancel₀ _ hg.2.1
  have hlocal (v : FinPlace F) (hv : v.asIdeal ∣ s.1) :
      v.valuation F (d.out : F) = 1 := by
    apply (qs_nq0_residue_ne_zero_iff_valuation_one v _).mp
    intro hzero
    apply hsymbol
    unfold chiIdealPow
    apply Multiset.prod_eq_zero
    apply Multiset.mem_map.mpr
    refine ⟨v.asIdeal, (Ideal.mem_normalizedFactors_iff s.2.1).mpr
      ⟨v.isPrime, Ideal.dvd_iff_le.mp hv⟩, ?_⟩
    simp only [dite_eq_left (show v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ from
      ⟨v.isPrime, v.ne_bot⟩)]
    change chiPow D v (d.out : F) 1 = 0
    simp [chiPow, hzero]
  obtain ⟨a, denominator, hfrac⟩ := conductorSInteger_fraction S d.out
  have hnotmem (v : FinPlace F) (hv : v.asIdeal ∣ s.1) : a ∉ v.asIdeal := by
    have hvS : v ∉ S.Sf := fun h => s.2.2 v h (Ideal.le_of_dvd hv)
    have hval : v.valuation F (a : F) = 1 := by
      rw [← hfrac, map_mul, hlocal v hv, denominator.property.2 v hvS, one_mul]
    exact v.valuation_eq_one_iff_notMem.mp hval
  have htop : Ideal.span {a} ⊔ s.1 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hsM : s.1 ≤ M := le_trans le_sup_right hle
    have hM0 : M ≠ ⊥ := by
      intro hMbot
      exact s.2.1 (bot_unique (by simpa [hMbot] using hsM))
    let v : FinPlace F := ⟨M, hM.isPrime, hM0⟩
    exact hnotmem v (Ideal.dvd_iff_le.mpr hsM)
      ((le_trans le_sup_left hle) (Ideal.subset_span (by simp)))
  have hone : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ s.1 := by simp [htop]
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hzero : Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hintegral y hy)
  have hnumInv : Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R a) *
      Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R b) = 1 := by
    have h := congrArg ((Ideal.Quotient.mk J).comp (algebraMap (𝓞 F) S.R)) hxy
    simp only [RingHom.comp_apply, map_add, map_mul, map_one, hzero, add_zero] at h
    simpa [mul_comm] using h
  have hfracR : d.out * algebraMap (𝓞 F) S.R (denominator : 𝓞 F) =
      algebraMap (𝓞 F) S.R a := Subtype.ext hfrac
  have hfracQ : d * Ideal.Quotient.mk J
      (algebraMap (𝓞 F) S.R (denominator : 𝓞 F)) =
        Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R a) := by
    have h := congrArg (Ideal.Quotient.mk J) hfracR
    simpa only [map_mul, Ideal.Quotient.mk_out] using h
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R (denominator : 𝓞 F)) *
    Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R b), ?_⟩
  rw [← mul_assoc, hfracQ, hnumInv]

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
