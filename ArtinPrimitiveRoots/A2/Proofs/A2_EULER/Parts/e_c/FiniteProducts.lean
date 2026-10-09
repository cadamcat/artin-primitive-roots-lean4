import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fintype.Option
import Mathlib.Analysis.Complex.Basic

noncomputable section
open scoped Classical
namespace ArtinPrimitiveRoots.Proofs.e_c
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem finite_pi_hasSum {ι : Type*} (α : Type*) [Fintype α]
    (f : α → ι → ℂ) (hs : ∀ a, Summable (fun i => ‖f a i‖)) :
    Summable (fun x : α → ι => ‖∏ a, f a (x a)‖) ∧
      HasSum (fun x : α → ι => ∏ a, f a (x a)) (∏ a, ∑' i, f a i) := by
  classical
  revert f hs
  apply Fintype.induction_empty_option
    (P := fun α [Fintype α] => ∀ (f : α → ι → ℂ),
      (∀ a, Summable (fun i => ‖f a i‖)) →
      Summable (fun x : α → ι => ‖∏ a, f a (x a)‖) ∧
      HasSum (fun x : α → ι => ∏ a, f a (x a)) (∏ a, ∑' i, f a i))
    (α := α)
  · intro α β _ e ih f hs
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨hns, hsum⟩ := ih (fun a => f (e a)) (fun a => hs (e a))
    let E : (α → ι) ≃ (β → ι) := Equiv.arrowCongr e (Equiv.refl ι)
    have hprod (x : α → ι) :
        (∏ b, f b (E x b)) = ∏ a, f (e a) (x a) := by
      rw [← e.prod_comp]
      simp only [E, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
    have hscalar : (∏ a, ∑' i, f (e a) i) = ∏ b, ∑' i, f b i := e.prod_comp (fun b => ∑' i, f b i)
    constructor
    · apply E.summable_iff.mp
      simpa only [Function.comp_def, hprod] using hns
    · apply E.hasSum_iff.mp
      simpa only [Function.comp_def, hprod, hscalar] using hsum
  · intro f hs
    letI : Unique (PEmpty → ι) :=
      ⟨⟨fun x => PEmpty.elim x⟩, fun g => by funext x; exact PEmpty.elim x⟩
    constructor
    · exact Summable.of_finite
    · simpa only [Fintype.prod_empty] using
        (hasSum_unique (fun x : PEmpty → ι => ∏ a, f a (x a)))
  · intro α _ ih f hs
    obtain ⟨hns, hsum⟩ := ih (fun a => f (some a)) (fun a => hs (some a))
    let E : (Option α → ι) ≃ ι × (α → ι) := Equiv.piOptionEquivProd
    have hprod (x : ι × (α → ι)) :
        (∏ a, f a (E.symm x a)) = f none x.1 * ∏ a, f (some a) (x.2 a) := by
      rw [Fintype.prod_option]
      rfl
    have hmul := (hs none).mul_norm hns
    constructor
    · apply E.symm.summable_iff.mp
      simpa only [Function.comp_def, hprod] using hmul
    · apply E.symm.hasSum_iff.mp
      have h := (hs none).of_norm.hasSum.mul hsum hmul.of_norm
      have hscalar : (∏ a : Option α, ∑' i, f a i) =
          (∑' i, f none i) * ∏ a, ∑' i, f (some a) i := Fintype.prod_option _
      rw [hscalar]
      simpa only [Function.comp_def, hprod] using h

end ArtinPrimitiveRoots.Proofs.e_c
