import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Reduced denominator/residue labels give distinct frequency classes modulo
S-integers, including the single residue of the unit ideal. -/
theorem probe_residue_frequencies_separated {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) :
    ∀ s t : S.ExtIdeal, ∀ d : ResidueRing E s, ∀ e : ResidueRing E t,
      IsUnit d → IsUnit e →
      (d.out : F) / (bc.gen s : F) - (e.out : F) / (bc.gen t : F) ∈ S.R →
      s = t ∧ HEq d e := by
  have hratio (s t : S.ExtIdeal) (d : ResidueRing E s) (e : ResidueRing E t)
      (hd : IsUnit d)
      (hdiff : (d.out : F) / (bc.gen s : F) -
        (e.out : F) / (bc.gen t : F) ∈ S.R) :
      (bc.gen t : F) / (bc.gen s : F) ∈ S.R := by
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    have hmem : b.out * d.out - 1 ∈ Ideal.span {E.genR s} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, map_one, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
        mul_comm, hb, sub_self]
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hmem
    have hbez : (b.out : F) * (d.out : F) =
        1 + (bc.gen s : F) * (k : F) := by
      have h := congrArg (fun x : S.R => (x : F)) hk
      change (k : F) * (E.genR s : F) = (b.out : F) * (d.out : F) - 1 at h
      rw [E.genR_val] at h
      linear_combination -h
    let r : S.R := ⟨(d.out : F) / (bc.gen s : F) -
      (e.out : F) / (bc.gen t : F), hdiff⟩
    have hdiffF : (d.out : F) / (bc.gen s : F) -
        (e.out : F) / (bc.gen t : F) = (r : F) := rfl
    have hcross : (d.out : F) * (bc.gen t : F) =
        (bc.gen s : F) * ((e.out : F) + (r : F) * (bc.gen t : F)) := by
      field_simp [Units.ne_zero (bc.gen s), Units.ne_zero (bc.gen t)] at hdiffF
      linear_combination hdiffF
    have heq : (bc.gen t : F) / (bc.gen s : F) =
        (b.out : F) * ((e.out : F) + (r : F) * (E.genR t : F)) -
          (E.genR t : F) * (k : F) := by
      rw [E.genR_val]
      field_simp [Units.ne_zero (bc.gen s)]
      linear_combination -(bc.gen t : F) * hbez + (b.out : F) * hcross
    rw [heq]
    exact S.R.sub_mem
      (S.R.mul_mem b.out.property (S.R.add_mem e.out.property
        (S.R.mul_mem r.property (E.genR t).property)))
      (S.R.mul_mem (E.genR t).property k.property)
  intro s t d e hd he hdiff
  have hts := hratio s t d e hd hdiff
  have hdiffRev : (e.out : F) / (bc.gen t : F) -
      (d.out : F) / (bc.gen s : F) ∈ S.R := by
    convert S.R.neg_mem hdiff using 1
    ring
  have hst := hratio t s e d he hdiffRev
  have hcountZero (I : S.ExtIdeal) (v : FinPlace F) (hv : v ∈ S.Sf) :
      FractionalIdeal.count F v
        (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    have hI0 : I.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using I.2.1
    rw [FractionalIdeal.count_coe F v hI0]
    have hc : (Associates.mk v.asIdeal).count (Associates.mk I.1).factors = 0 := by
      by_contra hne
      exact I.2.2 v hv
        (Ideal.le_of_dvd ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne))
    rw [hc, Nat.cast_zero]
  have hcounts (v : FinPlace F) : FractionalIdeal.count F v
      (s.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
    FractionalIdeal.count F v
      (t.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    by_cases hv : v ∈ S.Sf
    · rw [hcountZero s v hv, hcountZero t v hv]
    · have htsVal := hts v hv
      have hstVal := hst v hv
      rw [Valuation.map_div] at htsVal hstVal
      have hspos : 0 < v.valuation F (bc.gen s : F) :=
        WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr (Units.ne_zero _))
      have htpos : 0 < v.valuation F (bc.gen t : F) :=
        WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr (Units.ne_zero _))
      have hvals : v.valuation F (bc.gen s : F) = v.valuation F (bc.gen t : F) :=
        le_antisymm ((div_le_one₀ htpos).mp hstVal) ((div_le_one₀ hspos).mp htsVal)
      rw [← (bc.gen_spec s).1.2.2 v hv, ← (bc.gen_spec t).1.2.2 v hv,
        qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ (Units.ne_zero _),
        qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ (Units.ne_zero _), hvals]
  have hsF : (s.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr s.2.1
  have htF : (t.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr t.2.1
  have hsameF : (s.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (t.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hsF,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F htF]
    exact finprod_congr fun v => congrArg (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ n) (hcounts v)
  have hsame : s = t := Subtype.ext (FractionalIdeal.coeIdeal_injective hsameF)
  subst t
  refine ⟨rfl, ?_⟩
  let r : S.R := ⟨(d.out : F) / (bc.gen s : F) -
    (e.out : F) / (bc.gen s : F), hdiff⟩
  have hdelta : d.out - e.out = r * E.genR s := by
    apply Subtype.ext
    change (d.out : F) - (e.out : F) =
      ((d.out : F) / (bc.gen s : F) - (e.out : F) / (bc.gen s : F)) * (E.genR s : F)
    rw [E.genR_val]
    field_simp [Units.ne_zero (bc.gen s)]
  have hmem : d.out - e.out ∈ Ideal.span {E.genR s} := by
    rw [hdelta]
    exact Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩
  have hde : d = e := by
    simpa only [Ideal.Quotient.mk_out] using (Ideal.Quotient.eq.mpr hmem)
  exact heq_of_eq hde

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
