import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A reduced S-integer residue has a coprime integral representative, including
the residue of the unit ideal. -/
theorem probe_residue_lift {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) :
    ∀ s : S.ExtIdeal, ∀ d : ResidueRing E s, IsUnit d →
      ∃ c : 𝓞 F, IsCoprime (Ideal.span {c}) s.1 ∧
        ∃ r : S.R, (d.out : F) - algebraMap (𝓞 F) F c =
          (bc.gen s : F) * (r : F) := by
  intro s d hd
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
  let f : (𝓞 F ⧸ s.1) →+* ResidueRing E s :=
    Ideal.Quotient.lift s.1
      ((Ideal.Quotient.mk J).comp (algebraMap (𝓞 F) S.R))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hintegral a ha))
  have hf (a : 𝓞 F) : f (Ideal.Quotient.mk s.1 a) =
      Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R a) := rfl
  have hden (v : conductorDenominators S) :
      IsUnit (Ideal.Quotient.mk s.1 (v : 𝓞 F)) := by
    have htop : Ideal.span {(v : 𝓞 F)} ⊔ s.1 = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have hsM : s.1 ≤ M := le_trans le_sup_right hle
      have hM0 : M ≠ ⊥ := by
        intro hMbot
        exact s.2.1 (bot_unique (by simpa [hMbot] using hsM))
      let w : FinPlace F := ⟨M, hM.isPrime, hM0⟩
      by_cases hw : w ∈ S.Sf
      · exact s.2.2 w hw hsM
      · have hvw := v.property.2 w hw
        have hnot := w.valuation_eq_one_iff_notMem.mp hvw
        exact hnot ((le_trans le_sup_left hle) (Ideal.subset_span (by simp)))
    have hone : (1 : 𝓞 F) ∈ Ideal.span {(v : 𝓞 F)} ⊔ s.1 := by simp [htop]
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk s.1 b, ?_⟩
    have heq := congrArg (Ideal.Quotient.mk s.1) hxy
    rw [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at heq
    simpa [mul_comm] using heq
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, v, hxv⟩ := conductorSInteger_fraction S x
    obtain ⟨vb, hvb⟩ := isUnit_iff_exists_inv.mp (hden v)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective vb
    have hxvR : x * algebraMap (𝓞 F) S.R (v : 𝓞 F) =
        algebraMap (𝓞 F) S.R a := Subtype.ext hxv
    have hmul := congrArg f hvb
    rw [map_mul, map_one, hf, hf] at hmul
    refine ⟨Ideal.Quotient.mk s.1 (a * b), ?_⟩
    rw [hf, map_mul, map_mul, ← hxvR, map_mul, mul_assoc, hmul, mul_one]
  let : Fintype (ResidueRing E s) := E.residueFinite s
  have hcard : Fintype.card (𝓞 F ⧸ s.1) = Fintype.card (ResidueRing E s) := by
    rw [E.residue_card s, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
  let e : (𝓞 F ⧸ s.1) ≃+* ResidueRing E s :=
    RingEquiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard⟩)
  let c : 𝓞 F := (e.symm d).out
  have hc : Ideal.Quotient.mk s.1 c = e.symm d := Quotient.out_eq _
  have hcunit : IsUnit (Ideal.Quotient.mk s.1 c) := by
    rw [hc]
    exact hd.map e.symm.toMonoidHom
  have hcop : IsCoprime (Ideal.span {c}) s.1 := by
    obtain ⟨bq, hbq⟩ := isUnit_iff_exists_inv.mp hcunit
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
    have hmem : 1 - c * b ∈ s.1 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_one, map_mul, hbq, sub_self]
    apply Ideal.isCoprime_iff_sup_eq.mpr
    rw [Ideal.eq_top_iff_one]
    apply Submodule.mem_sup.mpr
    refine ⟨c * b, Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)),
      1 - c * b, hmem, ?_⟩
    ring
  have hmc : Ideal.Quotient.mk J (algebraMap (𝓞 F) S.R c) = d := by
    change e (Ideal.Quotient.mk s.1 c) = d
    rw [hc, e.apply_symm_apply]
  have hdelta : d.out - algebraMap (𝓞 F) S.R c ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, Ideal.Quotient.mk_out, hmc, sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdelta
  refine ⟨c, hcop, r, ?_⟩
  have hfield := congrArg (fun x : S.R => (x : F)) hr.symm
  change (d.out : F) - algebraMap (𝓞 F) F c = (r : F) * (E.genR s : F) at hfield
  rw [E.genR_val] at hfield
  simpa [mul_comm] using hfield

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
