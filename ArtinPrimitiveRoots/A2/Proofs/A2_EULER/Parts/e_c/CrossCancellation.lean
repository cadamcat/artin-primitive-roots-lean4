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



theorem prime_chi_symm (v w : ExteriorPrime S) (hne : v ≠ w) :
    chi D v.1 (primeGen R w.1 : F) = chi D w.1 (primeGen R v.1 : F) :=
  sextic_reciprocity D S H Bd v.1 w.1 v.2 w.2
    (fun h => hne (Subtype.ext h)) (primeGen R v.1) (primeGen R w.1)
    (primeGen_spec R v) (primeGen_spec R w)

theorem prime_chi_six (v w : ExteriorPrime S) (hne : v ≠ w) :
    chi D v.1 (primeGen R w.1 : F) ^ (6 : ℤ) = 1 := by
  have hu := primeGen_other_valuation R w v hne.symm
  have hres := (a2_bridge_SYMBOL D S).residue_ne_zero v.1 (primeGen R w.1 : F) hu.le
  have h6 := (a2_bridge_SYMBOL D S).chi_six v.1 _ (hres.mpr hu)
  simpa using h6

omit R in
 theorem symmetric_cross_product {ι : Type*} [DecidableEq ι] (V : Finset ι) (χ : ι → ι → ℂ)
    (e l k : ι → ℤ)
    (hχ : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → χ v w = χ w v)
    (h6 : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → χ v w ^ (6 : ℤ) = 1) :
    (∏ v ∈ V, ∏ w ∈ V.erase v, χ v w ^
      (k w * (e v + 3 * l v) + (e w + 3 * l w) * (e v + 3 * l v - k v) + 2 * e v * e w)) = 1 := by
  classical
  let E (v w : ι) : ℤ :=
    k w * (e v + 3 * l v) + (e w + 3 * l w) * (e v + 3 * l v - k v) + 2 * e v * e w
  let f (p : ι × ι) : ℂ := if p.1 = p.2 then 1 else χ p.1 p.2 ^ E p.1 p.2
  have hp : (∏ p ∈ V.product V, f p) = 1 := by
    apply Finset.prod_involution (fun p _ => p.swap)
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hv, hw⟩
      by_cases heq : p.1 = p.2
      · simp only [f, Prod.fst_swap, Prod.snd_swap, if_pos heq, if_pos heq.symm, one_mul]
      · have hz6 := h6 p.1 hv p.2 hw heq
        have hz0 : χ p.1 p.2 ≠ 0 := by
          intro hz
          simp [hz] at hz6
        simp only [f, Prod.fst_swap, Prod.snd_swap, if_neg heq, if_neg (Ne.symm heq)]
        rw [← hχ p.1 hv p.2 hw heq, ← zpow_add₀ hz0]
        have hE : E p.1 p.2 + E p.2 p.1 =
          6 * (e p.1 * e p.2 + e p.1 * l p.2 + l p.1 * e p.2 + 3 * l p.1 * l p.2) := by
          dsimp [E]
          ring
        rw [hE, zpow_mul, hz6, one_zpow]
    · intro p hp hf heq
      have he : p.1 = p.2 := (congrArg Prod.snd heq)
      exact hf (by simp [f, he])
    · intro p hp
      exact Prod.swap_swap p
    · intro p hp
      exact Finset.mem_product.mpr (Finset.mem_product.mp hp).symm
  have hp' : (∏ v ∈ V, ∏ w ∈ V, f (v,w)) = 1 := by
    rw [← Finset.prod_product]
    exact hp
  apply Eq.trans _ hp'
  apply Finset.prod_congr rfl
  intro v hv
  change (∏ w ∈ V.erase v, χ v w ^ E v w) = ∏ w ∈ V, f (v,w)
  calc
    _ = ∏ w ∈ V.erase v, f (v,w) := by
      apply Finset.prod_congr rfl
      intro w hw
      simp [f, (Finset.mem_erase.mp hw).1.symm]
    _ = _ := by
      apply Finset.prod_subset (Finset.erase_subset v V)
      intro w hw hn
      have he : w = v := by
        by_contra he
        exact hn (Finset.mem_erase.mpr ⟨he,hw⟩)
      simp [f, he]

end ArtinPrimitiveRoots.Proofs.e_c
