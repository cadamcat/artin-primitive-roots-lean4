import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false

open MeasureTheory AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

/-- A continuous function periodic under every integer vector descends to a
continuous function on the product of unit circles. -/
theorem periodic_torus_lift {d : Type*} [Fintype d]
    (f : (d → ℝ) → ℂ) (hf : Continuous f)
    (hper : ∀ (x : d → ℝ) (k : d → ℤ),
      f (x + fun i => (k i : ℝ)) = f x) :
    ∃ F : C(UnitAddTorus d, ℂ),
      ∀ x : d → ℝ, F (fun i => (x i : UnitAddCircle)) = f x := by
  classical
  let q : (d → ℝ) → UnitAddTorus d := fun x i => (x i : UnitAddCircle)
  let r : UnitAddTorus d → (d → ℝ) := fun z i =>
    (AddCircle.equivIco (1 : ℝ) 0 (z i) : ℝ)
  have hr (z : UnitAddTorus d) : q (r z) = z := by
    funext i
    exact AddCircle.coe_equivIco
  let F₀ : UnitAddTorus d → ℂ := fun z => f (r z)
  have hLift (x : d → ℝ) : F₀ (q x) = f x := by
    have hz (i : d) : ((r (q x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      change q (r (q x)) i - q x i = 0
      rw [hr]
      exact sub_self _
    choose k hk using fun i => (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hz i)
    have heq : r (q x) = x + fun i => (k i : ℝ) := by
      funext i
      change r (q x) i = x i + (k i : ℝ)
      have hi := hk i
      simp only [zsmul_eq_mul, mul_one] at hi
      linarith
    change f (r (q x)) = f x
    rw [heq]
    exact hper x k
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  have hF : Continuous F₀ := by
    apply hq.continuous_comp_iff.mp
    have heq : F₀ ∘ q = f := by
      funext x
      exact hLift x
    rw [heq]
    exact hf
  exact ⟨⟨F₀, hF⟩, hLift⟩

end ArtinPrimitiveRoots.Proofs.thsol_torusf
