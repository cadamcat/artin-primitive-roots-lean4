import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.CoordinateArithmetic

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

theorem ideal_mem_iff_of_sub_mem (K : Ideal S.R) (a b : S.R) (hab : a - b ∈ K) :
    a ∈ K ↔ b ∈ K := by
  constructor
  · intro ha
    convert K.sub_mem ha hab using 1 <;> ring
  · intro hb
    convert K.add_mem hab hb using 1 <;> ring

theorem local_mask_congr (s : S.ExtIdeal) (a h d d' : S.R) (v : ExteriorPrime S)
    (hd : d - d' ∈ coordinateSpan R s v) :
    h - a * d ∈ coordinateSpan R s v ↔ h - a * d' ∈ coordinateSpan R s v := by
  apply ideal_mem_iff_of_sub_mem R
  have hmem := (coordinateSpan R s v).mul_mem_left (-a) hd
  convert hmem using 1 <;> ring

def localizedSummand (s I : S.ExtIdeal) (a h : S.R) (v : ExteriorPrime S)
    (d x : S.R) : ℂ :=
  if h - a * d ∈ coordinateSpan R s v then
    chiPow D v.1 (d : F) 1 ^ idealExp v.1 s.1 *
      chiPow D v.1 (x : F) 1 ^ idealExp v.1 I.1 *
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
          (-(((h - a * d) * x : S.R) : F) /
            ((R.exterior.genR s : F) * (a : F))))
  else 0

theorem localizedSummand_congr_d (s I : S.ExtIdeal) (a h : S.R)
    (ha : S.IsGen (a : F) I.1) (v : ExteriorPrime S) (d d' x : S.R)
    (hd : d - d' ∈ coordinateSpan R s v) :
    localizedSummand R s I a h v d x = localizedSummand R s I a h v d' x := by
  classical
  have hmask := local_mask_congr R s a h d d' v hd
  by_cases hm : h - a * d ∈ coordinateSpan R s v
  · have hm' := hmask.mp hm
    simp only [localizedSummand, if_pos hm, if_pos hm']
    rw [local_character_congr R s v d d' hd]
    congr 1
    have hs0 : (R.exterior.genR s : F) ≠ 0 := by
      rw [R.exterior.genR_val]
      exact (bc.gen s).ne_zero
    apply psi_div_congr R v.1 _ _ _ (mul_ne_zero hs0 ha.2.1)
    have harg : (((h - a * d) * x : S.R) : F) - (((h - a * d') * x : S.R) : F) =
        -(a : F) * ((d - d' : S.R) : F) * (x : F) := by
      push_cast
      ring
    rw [harg]
    simp only [map_mul, Valuation.map_neg]
    calc
      _ ≤ (v.1.valuation F (a : F) * v.1.valuation F (R.exterior.genR s : F)) * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl (mem_coordinate_valuation_le R s v (d - d') hd))
          (x.property v.1 v.2)
      _ = _ := by simp only [mul_one, one_mul, mul_comm]
  · have hm' : h - a * d' ∉ coordinateSpan R s v := fun H => hm (hmask.mpr H)
    simp only [localizedSummand, if_neg hm, if_neg hm']

theorem localizedSummand_congr_x (s I : S.ExtIdeal) (a h : S.R)
    (ha : S.IsGen (a : F) I.1) (v : ExteriorPrime S) (d x x' : S.R)
    (hx : x - x' ∈ coordinateSpan R I v) :
    localizedSummand R s I a h v d x = localizedSummand R s I a h v d x' := by
  classical
  by_cases hm : h - a * d ∈ coordinateSpan R s v
  · simp only [localizedSummand, if_pos hm]
    rw [local_character_congr R I v x x' hx]
    congr 1
    have hs0 : (R.exterior.genR s : F) ≠ 0 := by
      rw [R.exterior.genR_val]
      exact (bc.gen s).ne_zero
    apply psi_div_congr R v.1 _ _ _ (mul_ne_zero hs0 ha.2.1)
    have harg : (((h - a * d) * x : S.R) : F) - (((h - a * d) * x' : S.R) : F) =
        ((h - a * d : S.R) : F) * ((x - x' : S.R) : F) := by
      push_cast
      ring
    rw [harg, map_mul, map_mul]
    have hδ := mem_coordinate_valuation_le R s v (h - a * d) hm
    have hX := (mem_coordinate_valuation_le R I v (x - x') hx).trans_eq
      (generatorR_valuation_eq R I a ha v)
    exact mul_le_mul' hδ hX
  · simp only [localizedSummand, if_neg hm]

theorem mask_iff_mem (s : S.ExtIdeal) (a h d : S.R) :
    (∃ y : S.R, (h : F) - (a : F) * (d : F) = (bc.gen s : F) * (y : F)) ↔
      h - a * d ∈ Ideal.span {R.exterior.genR s} := by
  constructor
  · rintro ⟨y, hy⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simpa [R.exterior.genR_val] using hy
  · intro hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
    refine ⟨y, ?_⟩
    simpa [R.exterior.genR_val] using
      congrArg (fun t : S.R => (t : F)) hy

theorem mask_mem_coordinates (s : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 s.1 ≠ 0 → v ∈ V) (r : S.R) :
    r ∈ Ideal.span {R.exterior.genR s} ↔ ∀ v : V, r ∈ coordinateSpan R s v.1 := by
  rw [residue_span_iInf R s V hV]
  simp only [Submodule.mem_iInf]

end ArtinPrimitiveRoots.Proofs.e_c
