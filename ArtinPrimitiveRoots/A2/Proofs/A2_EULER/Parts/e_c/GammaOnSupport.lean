import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.GeneratorCharacters

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
include R



theorem idealExp_ne_zero_iff (I : S.ExtIdeal) (v : FinPlace F) :
    idealExp v I.1 ≠ 0 ↔ v.asIdeal ∣ I.1 := by
  unfold idealExp
  exact Associates.count_ne_zero_iff_dvd I.property.1 v.irreducible

theorem tuple_support_contains (B : PrimeTupleBridge S) (p : IdealTuple S) :
    (∀ v : ExteriorPrime S, idealExp v.1 (R.exterior.ofSqf p.1).1 ≠ 0 → v ∈ (B.equiv p).support) ∧
    (∀ v : ExteriorPrime S, idealExp v.1 p.2.1.1 ≠ 0 → v ∈ (B.equiv p).support) ∧
    (∀ v : ExteriorPrime S, idealExp v.1 p.2.2.1.1 ≠ 0 → v ∈ (B.equiv p).support) ∧
    (∀ v : ExteriorPrime S, idealExp v.1 p.2.2.2.1 ≠ 0 → v ∈ (B.equiv p).support) := by
  have hz := tuple_exponents_zero R B p
  refine ⟨?_,?_,?_,?_⟩ <;> intro v hn <;> by_contra hv
  · exact hn (by simpa only [R.exterior.ofSqf_val] using (hz v hv).1)
  · exact hn (hz v hv).2.1
  · exact hn (hz v hv).2.2.1
  · exact hn (hz v hv).2.2.2

theorem tuple_gamma_on (B : PrimeTupleBridge S) (p : IdealTuple S) :
    gamma D S A 2 p.1.1 (cgen R p.1) =
      ∏ v ∈ (B.equiv p).support,
        gamma D S A 2 v.1.asIdeal (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ) *
          chi D v.1 ((cgen R p.1) / (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ)) ^
            (2 * (((B.equiv p v).1 : ℕ) : ℤ)) := by
  classical
  let V := (B.equiv p).support
  let f (v : ExteriorPrime S) : ℂ :=
    gamma D S A 2 v.1.asIdeal (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ) *
      chi D v.1 ((cgen R p.1) / (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ)) ^
        (2 * (((B.equiv p v).1 : ℕ) : ℤ))
  let T := V.filter (fun v => idealExp v.1 p.1.1 ≠ 0)
  have hcount (v : ExteriorPrime S) : idealExp v.1 p.1.1 = ((B.equiv p v).1 : ℕ) :=
    (tuple_exponents R B p v).1
  have hone (v : ExteriorPrime S) (hv : v ∈ T) : ((B.equiv p v).1 : ℕ) = 1 := by
    have hn : idealExp v.1 p.1.1 ≠ 0 := (Finset.mem_filter.mp hv).2
    rw [hcount v] at hn
    have hb := (B.equiv p v).1.isLt
    omega
  have hcrt : (∏ v ∈ T, f v) = gamma D S A 2 p.1.1 (cgen R p.1) := by
    rw [gamma_squarefree_factorization R p.1]
    apply Finset.prod_bij (fun v _ => v.1)
    · intro v hv
      apply (R.exterior.mem_support _ _).mpr
      apply (idealExp_ne_zero_iff R (R.exterior.ofSqf p.1) v.1).mp
      simpa only [R.exterior.ofSqf_val] using (Finset.mem_filter.mp hv).2
    · intro v hv w hw heq
      exact Subtype.ext heq
    · intro w hw
      let v : ExteriorPrime S := ⟨w, R.exterior.support_exterior _ w hw⟩
      have hn : idealExp w (R.exterior.ofSqf p.1).1 ≠ 0 :=
        (idealExp_ne_zero_iff R _ w).mpr ((R.exterior.mem_support _ _).mp hw)
      have hvV := (tuple_support_contains R B p).1 v hn
      refine ⟨v, Finset.mem_filter.mpr ⟨hvV, ?_⟩, rfl⟩
      simpa only [R.exterior.ofSqf_val] using hn
    · intro v hv
      simp only [f, hone v hv, pow_one, Nat.cast_one, mul_one]
  rw [← hcrt]
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro v hv hn
  have he : ((B.equiv p v).1 : ℕ) = 0 := by
    have hz : idealExp v.1 p.1.1 = 0 := by
      by_contra hz
      exact hn (Finset.mem_filter.mpr ⟨hv,hz⟩)
    rw [hcount v] at hz
    exact hz
  simp [f, he]

end ArtinPrimitiveRoots.Proofs.e_c
