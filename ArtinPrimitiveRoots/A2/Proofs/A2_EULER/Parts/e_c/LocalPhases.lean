import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.ResidueCRT

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




local macro "reflection% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A2.Reflection.Missing
    (`ArtinPrimitiveRoots.A2 ++ n.getId)))
local macro "interface% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A2.Interface
    (`ArtinPrimitiveRoots.A2 ++ n.getId)))
local macro "addchar% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A1.AddChar
    (`ArtinPrimitiveRoots.A1 ++ n.getId)))
include R

def primeR (v : ExteriorPrime S) : S.R := R.exterior.genR (R.exterior.prime v.1 v.2)

theorem primeR_val (v : ExteriorPrime S) : (primeR R v : F) = (primeGen R v.1 : F) := by
  simp [primeR, primeGen, v.2, R.exterior.genR_val]

theorem prime_power_span (v : ExteriorPrime S) (k : ℕ) :
    Ideal.span {R.exterior.genR (R.exterior.pow (R.exterior.prime v.1 v.2) k)} =
      Ideal.span {primeR R v ^ k} := by
  let pi := R.exterior.prime v.1 v.2
  let I := R.exterior.pow pi k
  have hp : S.IsGen ((primeR R v ^ k : S.R) : F) I.1 := by
    have h := (reflection% rf_isGen_extPow) R pi (bc.gen pi) (bc.gen_spec pi).1 k
    simpa [primeR, pi, I, R.exterior.genR_val] using h
  calc
    _ = Ideal.map (algebraMap (𝓞 F) S.R) I.1 := (residue_span_map R I).symm
    _ = _ := (interface% a2p_map_eq_span_genR) S I (primeR R v ^ k) hp

theorem primeGen_valuation (v : ExteriorPrime S) :
    v.1.valuation F (primeGen R v.1 : F) = WithZero.exp (-1 : ℤ) :=
  (reflection% rf_local_primeGen_valuation) R v.1 v.2

theorem primeGen_other_valuation (v w : ExteriorPrime S) (hne : v ≠ w) :
    w.1.valuation F (primeGen R v.1 : F) = 1 :=
  (reflection% rf_primeGen_globalVal_one_of_ne) R v.1 w.1 v.2 w.2
    (fun h => hne (Subtype.ext h))

theorem addchar_congr_integral (v : FinPlace F) (x y : F)
    (hxy : v.valuation F (x - y) ≤ 1) :
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
      A.ψ v (algebraMap F (v.adicCompletion F) y) := by
  have hInt : algebraMap F (v.adicCompletion F) (x - y) ∈ v.adicCompletionIntegers F := by
    change ((x - y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxy
  have hψ := A.integral v _ hInt
  have hdiff := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) x) (algebraMap F (v.adicCompletion F) y)
  have hy : A.ψ v (algebraMap F (v.adicCompletion F) y) ≠ 0 :=
    (AddChar.val_isUnit _ _).ne_zero
  rw [map_sub, hdiff, div_eq_one_iff_eq hy] at hψ
  exact hψ

theorem chiPow_residue_congr (v : FinPlace F) (x y : F) (e : ℤ)
    (hres : residue v x = residue v y) : chiPow D v x e = chiPow D v y e :=
  (addchar% crt_chiPow_residue_congr) D v e hres

theorem exterior_additive_phase (V : Finset (ExteriorPrime S)) (z : F)
    (hval : ∀ w : FinPlace F, w ∉ S.Sf → w ∉ V.image Subtype.val → w.valuation F z ≤ 1) :
    S.e A (S.diag z) =
      ∏ v ∈ V, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (-z)) := by
  classical
  let W := V.image Subtype.val
  let f (w : FinPlace F) := A.ψ w (algebraMap F (w.adicCompletion F) z)
  have hdisj : Disjoint S.Sf W := by
    apply Finset.disjoint_left.mpr
    intro w hws hwW
    obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp hwW
    subst w
    exact v.2 hws
  have hsupp : Function.mulSupport f ⊆ (S.Sf ∪ W : Finset (FinPlace F)) := by
    intro w hw
    by_contra hnot
    have hws : w ∉ S.Sf := fun hs => hnot (Finset.mem_union_left W hs)
    have hwW : w ∉ W := fun hW => hnot (Finset.mem_union_right S.Sf hW)
    have hInt : algebraMap F (w.adicCompletion F) z ∈ w.adicCompletionIntegers F := by
      change ((z : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hval w hws hwW
    exact hw (A.integral w _ hInt)
  have hfin := finprod_eq_prod_of_mulSupport_subset f hsupp
  have hglobal := (A.trivial_on_F z).2
  rw [hfin, Finset.prod_union hdisj] at hglobal
  have hE : S.e A (S.diag z) = (∏ w ∈ S.Sf, f w) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
    letI : IsTotallyComplex F := D.isTotallyComplex
    change (∏ w : S.Sf, f w.1) *
      (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) = _
    rw [(addchar% arch_exp_eq_trace) z, Finset.prod_coe_sort]
  have hprod : S.e A (S.diag z) * (∏ w ∈ W, f w) = 1 := by
    rw [hE]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hglobal
  calc
    _ = (∏ w ∈ W, f w)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    _ = ∏ w ∈ W, A.ψ w (algebraMap F (w.adicCompletion F) (-z)) := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro w hw
      simp only [f, map_neg, AddChar.map_neg_eq_inv]
    _ = _ := Finset.prod_image Subtype.val_injective.injOn

end ArtinPrimitiveRoots.Proofs.e_c
