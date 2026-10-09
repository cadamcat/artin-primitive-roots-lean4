import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.MaskedSummands

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory Function
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_c
open ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)









include R

theorem global_summand_product (s I : S.ExtIdeal) (a h : S.R)
    (ha : S.IsGen (a : F) I.1) (V : Finset (ExteriorPrime S))
    (hsV : ∀ v : ExteriorPrime S, idealExp v.1 s.1 ≠ 0 → v ∈ V)
    (hIV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) (d x : S.R) :
    (if h - a * d ∈ Ideal.span {R.exterior.genR s} then
      chiIdealPow D s.1 (d : F) 1 * chiIdealPow D I.1 (x : F) 1 *
        S.e A (S.diag ((((h - a * d) * x : S.R) : F) /
          ((R.exterior.genR s : F) * (a : F)))) else 0) =
      ∏ v ∈ V, localizedSummand R s I a h v d x := by
  classical
  let n : S.R := (h - a * d) * x
  let z : F := (n : F) / ((R.exterior.genR s : F) * (a : F))
  have hphase := exterior_additive_phase R V z (by
    intro w hw hwV
    let v : ExteriorPrime S := ⟨w, hw⟩
    have hvV : v ∉ V := by
      intro h
      exact hwV (Finset.mem_image.mpr ⟨v, h, rfl⟩)
    have hs0 : idealExp w s.1 = 0 := by
      by_contra he
      exact hvV (hsV v he)
    have hI0 : idealExp w I.1 = 0 := by
      by_contra he
      exact hvV (hIV v he)
    have hsval : w.valuation F (R.exterior.genR s : F) = 1 := by
      rw [R.exterior.genR_val, generator_valuation R s (bc.gen s) (bc.gen_spec s).1 v]
      simp only [v, hs0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    have hAval : w.valuation F (a : F) = 1 := by
      rw [generatorR_valuation R I a ha v]
      simp only [v, hI0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    dsimp [z]
    rw [map_div₀, map_mul, hsval, hAval, one_mul, div_one]
    exact n.property w hw)
  have hCs := chiIdealPow_product R s V hsV (d : F) 1
  have hCI := chiIdealPow_product R I V hIV (x : F) 1
  by_cases hm : h - a * d ∈ Ideal.span {R.exterior.genR s}
  · have hcoords (v : ExteriorPrime S) (hv : v ∈ V) :
        h - a * d ∈ coordinateSpan R s v :=
      (mask_mem_coordinates R s V hsV _).mp hm ⟨v, hv⟩
    rw [if_pos hm, hCs, hCI, hphase, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [localizedSummand, if_pos (hcoords v hv), z, n, neg_div]
  · have hnot : ¬∀ v : V, h - a * d ∈ coordinateSpan R s v.1 := by
      intro h
      exact hm ((mask_mem_coordinates R s V hsV _).mpr h)
    push_neg at hnot
    obtain ⟨v, hv⟩ := hnot
    rw [if_neg hm]
    symm
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨v.1, v.2, by simp only [localizedSummand, if_neg hv]⟩

theorem residueCRT_out_congr (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V)
    (x : ResidueRing R.exterior I) (v : V) :
    x.out - (residueCRT R I V hV x v).out ∈ coordinateSpan R I v.1 := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  calc
    Ideal.Quotient.mk _ x.out = residueCRT R I V hV x v := by
      rw [← residueCRT_mk R I V hV x.out v, Ideal.Quotient.mk_out]
    _ = Ideal.Quotient.mk _ (residueCRT R I V hV x v).out :=
      (Ideal.Quotient.mk_out _).symm

omit R in
 theorem finite_double_product {ι : Type*} [Fintype ι]
    (D X : ι → Type*) [∀ v, Fintype (D v)] [∀ v, Fintype (X v)]
    (f : ∀ v, D v → X v → ℂ) :
    (∏ v, ∑ d, ∑ x, f v d x) = ∑ d : ∀ v, D v, ∑ x : ∀ v, X v, ∏ v, f v (d v) (x v) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact Fintype.prod_sum _

theorem finiteFactor_crt (s I : S.ExtIdeal) (a h : S.R)
    (ha : S.IsGen (a : F) I.1) (V : Finset (ExteriorPrime S))
    (hsV : ∀ v : ExteriorPrime S, idealExp v.1 s.1 ≠ 0 → v ∈ V)
    (hIV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    finiteFactor R s I (Units.mk0 (a : F) ha.2.1) (h : F) =
      ∏ v ∈ V,
        ∑ᶠ d : ResidueRing R.exterior (coordinateIdeal R s v),
        ∑ᶠ x : ResidueRing R.exterior (coordinateIdeal R I v),
          localizedSummand R s I a h v d.out x.out := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : Fintype (ResidueRing R.exterior s) := R.exterior.residueFinite s
  letI : Fintype (ResidueRing R.exterior I) := R.exterior.residueFinite I
  letI : ∀ v : V, Fintype (ResidueRing R.exterior (coordinateIdeal R s v.1)) :=
    fun v => R.exterior.residueFinite _
  letI : ∀ v : V, Fintype (ResidueRing R.exterior (coordinateIdeal R I v.1)) :=
    fun v => R.exterior.residueFinite _
  let Es := residueCRT R s V hsV
  let EI := residueCRT R I V hIV
  have hsum : finiteFactor R s I (Units.mk0 (a : F) ha.2.1) (h : F) =
      ∑ d : ResidueRing R.exterior s, ∑ x : ResidueRing R.exterior I,
        ∏ v : V, localizedSummand R s I a h v.1 (Es d v).out (EI x v).out := by
    rw [finiteFactor_double_sum R, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    rw [finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro x hx
    have hlocal (v : V) : localizedSummand R s I a h v.1 d.out x.out =
        localizedSummand R s I a h v.1 (Es d v).out (EI x v).out := by
      rw [localizedSummand_congr_d R s I a h ha v.1 d.out (Es d v).out x.out
          (residueCRT_out_congr R s V hsV d v),
        localizedSummand_congr_x R s I a h ha v.1 (Es d v).out x.out (EI x v).out
          (residueCRT_out_congr R I V hIV x v)]
    have hg := global_summand_product R s I a h ha V hsV hIV d.out x.out
    simp only [Units.val_mk0]
    rw [mask_iff_mem R s a h d.out, ← R.exterior.genR_val s]
    rw [← Finset.prod_coe_sort V (fun v => localizedSummand R s I a h v d.out x.out)] at hg
    simp only [hlocal] at hg
    simpa using hg
  rw [hsum]
  let f (v : V) (d : ResidueRing R.exterior (coordinateIdeal R s v.1))
      (x : ResidueRing R.exterior (coordinateIdeal R I v.1)) :=
    localizedSummand R s I a h v.1 d.out x.out
  calc
    _ = ∑ d : ∀ v : V, ResidueRing R.exterior (coordinateIdeal R s v.1),
        ∑ x : ResidueRing R.exterior I, ∏ v : V, f v (d v) (EI x v) :=
      Es.toEquiv.sum_comp (fun d => ∑ x : ResidueRing R.exterior I,
        ∏ v : V, f v (d v) (EI x v))
    _ = ∑ d : ∀ v : V, ResidueRing R.exterior (coordinateIdeal R s v.1),
        ∑ x : ∀ v : V, ResidueRing R.exterior (coordinateIdeal R I v.1),
          ∏ v : V, f v (d v) (x v) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact EI.toEquiv.sum_comp (fun x => ∏ v : V, f v (d v) (x v))
    _ = ∏ v : V, ∑ d, ∑ x, f v d x := (finite_double_product _ _ f).symm
    _ = _ := by
      rw [← Finset.prod_coe_sort V (fun v =>
        ∑ᶠ d : ResidueRing R.exterior (coordinateIdeal R s v),
        ∑ᶠ x : ResidueRing R.exterior (coordinateIdeal R I v),
          localizedSummand R s I a h v d.out x.out)]
      apply Finset.prod_congr rfl
      intro v hv
      letI := R.exterior.residueFinite (coordinateIdeal R s v.1)
      letI := R.exterior.residueFinite (coordinateIdeal R I v.1)
      simp only [f, finsum_eq_sum_of_fintype]

end ArtinPrimitiveRoots.Proofs.e_c
