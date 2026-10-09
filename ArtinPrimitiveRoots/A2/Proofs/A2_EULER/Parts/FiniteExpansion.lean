import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.FiniteProducts

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private theorem localC_zero (v : FinPlace F) (hv : v ∉ S.Sf) (J : ℕ) :
    localC R v hv 0 0 J = 1 := by
  let pi := R.exterior.prime v hv
  let I0 := R.exterior.pow pi 0
  let Q0 := ResidueRing R.exterior I0
  letI : Fintype Q0 := R.exterior.residueFinite I0
  have hcard : Fintype.card Q0 = 1 := by
    simpa [Q0, I0, R.exterior.pow_val] using R.exterior.residue_card I0
  letI : Unique Q0 := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hcard)
  let pR : S.R := R.exterior.genR pi
  have hpR : (primeGen R v : F) = (pR : F) := by
    simp [pR, pi, primeGen, hv, R.exterior.genR_val]
  have hcond (d : Q0) : ∃ x : S.R,
      (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
      (primeGen R v : F) ^ 0 * (x : F) := by
    refine ⟨pR ^ J - d.out, ?_⟩
    simp [hpR]
  have hphase (d x : Q0) : A.ψ v (algebraMap F (v.adicCompletion F)
      (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F)) *
        (x.out : F) / (primeGen R v : F) ^ (0 + 0)))) = 1 := by
    let y : S.R := -((pR ^ J - d.out) * x.out)
    have hy : algebraMap F (v.adicCompletion F) (y : F) ∈
        v.adicCompletionIntegers F := by
      change ((y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact y.property v hv
    simpa [y, hpR] using A.integral v _ hy
  unfold localC
  change (∑ᶠ d : Q0, if ∃ x : S.R,
      (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
        (primeGen R v : F) ^ 0 * (x : F) then
      (if (0 : ℕ) = 0 then 1 else chiPow D v (d.out : F) 0) *
        ∑ᶠ x : Q0, (if (0 : ℕ) = 0 then 1 else chiPow D v (x.out : F) 0) *
          A.ψ v (algebraMap F _ (-(((primeGen R v : F) ^ J -
            (primeGen R v : F) ^ 0 * (d.out : F)) * (x.out : F) /
              (primeGen R v : F) ^ (0 + 0)))) else 0) = 1
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_unique, hcond, if_pos]
  simp only [if_pos (by rfl : (0 : ℕ) = 0), one_mul]
  exact hphase _ _

private theorem localEulerTerm_zero (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (ξ w z : ℂ) : localEulerTerm R η U u v hv ξ w z (0 : LocalIndex) = 1 := by
  simp [localEulerTerm, localC_zero R v hv]

theorem finite_expansion (B : PrimeTupleBridge S) (u : U.U) (ξ w z : ℂ)
    (hs : ∀ v hv, Summable (fun i : LocalIndex => ‖localEulerTerm R η U u v hv ξ w z i‖))
    (hcoeff : ∀ p : IdealTuple S, calFTerm R η U u ξ w z p =
      ∏ v ∈ (B.equiv p).support, localEulerTerm R η U u v.1 v.2 ξ w z (B.equiv p v))
    (V : Finset (ExteriorPrime S)) :
    (∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z) =
      ∑' p : IdealTuple S, if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0 := by
  classical
  let f (v : ExteriorPrime S) (i : LocalIndex) :=
    localEulerTerm R η U u v.1 v.2 ξ w z i
  let C := {d : ExteriorPrime S →₀ LocalIndex // d.support ⊆ V}
  let E : C ≃ (V → LocalIndex) :=
    (Equiv.subtypeEquivRight (fun d => by
      simp only [Finset.coe_subset])).trans
      ((Finsupp.restrictSupportEquiv (V : Set (ExteriorPrime S)) LocalIndex).trans
        Finsupp.equivFunOnFinite)
  have hEval (d : C) (v : V) : E d v = d.1 v.1 := rfl
  have hprod (d : C) :
      (∏ v : V, f v.1 (E d v)) = ∏ v ∈ d.1.support, f v (d.1 v) := by
    simp only [hEval]
    rw [Finset.prod_coe_sort V (fun v => f v (d.1 v))]
    symm
    apply Finset.prod_subset d.2
    intro v hv hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    exact localEulerTerm_zero R η U u v.1 v.2 ξ w z
  have hpi := (ArtinPrimitiveRoots.Proofs.e_c.finite_pi_hasSum V (fun v => f v.1) (fun v => hs v.1.1 v.1.2)).2
  have hsum : HasSum (fun d : C => ∏ v ∈ d.1.support, f v (d.1 v))
      (∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z) := by
    have h := E.hasSum_iff.mpr hpi
    rw [show (∏ v : V, ∑' i, f v.1 i) =
      ∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z by
        exact Finset.prod_coe_sort V (fun v => localEuler R η U u v.1 v.2 ξ w z)] at h
    simpa only [Function.comp_def, hprod] using h
  calc
    _ = ∑' d : C, ∏ v ∈ d.1.support, f v (d.1 v) := hsum.tsum_eq.symm
    _ = ∑' d : ExteriorPrime S →₀ LocalIndex,
        if d.support ⊆ V then ∏ v ∈ d.support, f v (d v) else 0 := by
      calc
        _ = ∑' d : ExteriorPrime S →₀ LocalIndex,
            {d : ExteriorPrime S →₀ LocalIndex | d.support ⊆ V}.indicator
              (fun d => ∏ v ∈ d.support, f v (d v)) d := tsum_subtype _ _
        _ = _ := by
          apply tsum_congr
          intro d
          by_cases hd : d.support ⊆ V
          · have hd' : d ∈ {d : ExteriorPrime S →₀ LocalIndex | d.support ⊆ V} := hd
            simp only [Set.indicator_of_mem hd', if_pos hd]
          · have hd' : d ∉ {d : ExteriorPrime S →₀ LocalIndex | d.support ⊆ V} := hd
            simp only [Set.indicator_of_notMem hd', if_neg hd]
    _ = ∑' p : IdealTuple S,
        if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0 := by
      rw [← B.equiv.tsum_eq]
      apply tsum_congr
      intro p
      simp only [Function.comp_def, hcoeff, f]

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
