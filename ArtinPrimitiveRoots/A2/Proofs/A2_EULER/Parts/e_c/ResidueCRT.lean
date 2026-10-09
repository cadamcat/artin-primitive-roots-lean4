import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.PrimeInfrastructure

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



local macro "interface% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A2.Interface
    (`ArtinPrimitiveRoots.A2 ++ n.getId)))
include R

def coordinateIdeal (I : S.ExtIdeal) (v : ExteriorPrime S) : S.ExtIdeal :=
  R.exterior.pow (R.exterior.prime v.1 v.2) (idealExp v.1 I.1)

def coordinateSpan (I : S.ExtIdeal) (v : ExteriorPrime S) : Ideal S.R :=
  Ideal.span {R.exterior.genR (coordinateIdeal R I v)}

theorem residue_span_map (I : S.ExtIdeal) :
    Ideal.map (algebraMap (𝓞 F) S.R) I.1 = Ideal.span {R.exterior.genR I} := by
  apply (interface% a2p_map_eq_span_genR) S I (R.exterior.genR I)
  rw [R.exterior.genR_val]
  exact (bc.gen_spec I).1

theorem coordinateSpan_map (I : S.ExtIdeal) (v : ExteriorPrime S) :
    Ideal.map (algebraMap (𝓞 F) S.R) (v.1.asIdeal ^ idealExp v.1 I.1) =
      coordinateSpan R I v := by
  simpa only [coordinateSpan, coordinateIdeal, R.exterior.pow_val,
    R.exterior.prime_val] using residue_span_map R (coordinateIdeal R I v)

theorem coordinateSpan_pairwise (I : S.ExtIdeal) :
    Pairwise (IsCoprime on coordinateSpan R I) := by
  intro v w hvw
  have hne : v.1.asIdeal ≠ w.1.asIdeal := by
    intro h
    exact hvw (Subtype.ext (HeightOneSpectrum.ext h))
  have hp : IsCoprime v.1.asIdeal w.1.asIdeal :=
    Ideal.isCoprime_iff_sup_eq.mpr (v.1.isMaximal.coprime_of_ne w.1.isMaximal hne)
  have hpPow : IsCoprime (v.1.asIdeal ^ idealExp v.1 I.1)
      (w.1.asIdeal ^ idealExp w.1 I.1) := hp.pow
  apply Ideal.isCoprime_iff_sup_eq.mpr
  rw [← coordinateSpan_map R I v, ← coordinateSpan_map R I w,
    ← Ideal.map_sup, hpPow.sup_eq, Ideal.map_top]

theorem residue_span_product (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    Ideal.span {R.exterior.genR I} = ∏ v ∈ V, coordinateSpan R I v := by
  classical
  calc
    _ = Ideal.map (algebraMap (𝓞 F) S.R) I.1 := (residue_span_map R I).symm
    _ = (Ideal.mapHom (algebraMap (𝓞 F) S.R))
        (∏ v ∈ V, v.1.asIdeal ^ idealExp v.1 I.1) := by
      rw [← ideal_factorization_on R I V hV]
      rfl
    _ = ∏ v ∈ V, Ideal.map (algebraMap (𝓞 F) S.R)
        (v.1.asIdeal ^ idealExp v.1 I.1) := map_prod _ _ _
    _ = _ := Finset.prod_congr rfl (fun v hv => coordinateSpan_map R I v)

theorem residue_span_iInf (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    Ideal.span {R.exterior.genR I} = ⨅ v : V, coordinateSpan R I v.1 := by
  classical
  calc
    _ = ∏ v ∈ V, coordinateSpan R I v := residue_span_product R I V hV
    _ = ∏ v : V, coordinateSpan R I v.1 := (Finset.prod_coe_sort V _).symm
    _ = _ := by
      apply (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (J := fun v : V => coordinateSpan R I v.1) ?_).trans
        (by simp)
      intro v hv w hw hne
      exact coordinateSpan_pairwise R I (by intro h; exact hne (Subtype.ext h))

noncomputable def residueCRT (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    ResidueRing R.exterior I ≃+* ∀ v : V, ResidueRing R.exterior (coordinateIdeal R I v.1) :=
  (Ideal.quotEquivOfEq (residue_span_iInf R I V hV)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun v : V => coordinateSpan R I v.1)
      (fun v w hne => coordinateSpan_pairwise R I (by intro h; exact hne (Subtype.ext h))))

theorem residueCRT_mk (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) (r : S.R) (v : V) :
    residueCRT R I V hV (Ideal.Quotient.mk _ r) v = Ideal.Quotient.mk _ r := by
  simp only [residueCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

end ArtinPrimitiveRoots.Proofs.e_c
