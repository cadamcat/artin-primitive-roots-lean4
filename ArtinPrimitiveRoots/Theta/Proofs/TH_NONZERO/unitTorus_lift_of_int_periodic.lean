import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Constructions

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A continuous function invariant under integer translations descends
continuously to the standard unit torus. -/
theorem unitTorus_lift_of_int_periodic {d : Type*} [Fintype d]
    (f : C(d → ℝ, ℂ))
    (hper : ∀ m : d → ℤ, ∀ x : d → ℝ,
      f (x + (fun i => (m i : ℝ))) = f x) :
    ∃ g : C(UnitAddTorus d, ℂ), ∀ x : d → ℝ,
      g (fun i => (x i : UnitAddCircle)) = f x := by
  let q : (d → ℝ) → UnitAddTorus d := fun x i => (x i : UnitAddCircle)
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  have hfiber : ∀ x y : d → ℝ, q x = q y → f x = f y := by
    intro x y hxy
    have hdiff : ∀ i : d, ∃ m : ℤ, (m : ℝ) = x i - y i := by
      intro i
      have hzero : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.mpr (congrFun hxy i)
      obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
      exact ⟨m, by simpa [zsmul_eq_mul] using hm⟩
    choose m hm using hdiff
    have hx : x = y + (fun i => (m i : ℝ)) := by
      funext i
      change x i = y i + (m i : ℝ)
      rw [hm i, add_comm, sub_add_cancel]
    rw [hx, hper]
  let r : UnitAddTorus d → (d → ℝ) := fun u => (hq.surjective u).choose
  have hr : ∀ u, q (r u) = u := fun u => (hq.surjective u).choose_spec
  let g : UnitAddTorus d → ℂ := fun u => f (r u)
  have hgq : ∀ x, g (q x) = f x := fun x => hfiber (r (q x)) x (hr (q x))
  have hg : Continuous g := hq.continuous_comp_iff.mp (by
    have heq : g ∘ q = f := funext hgq
    rw [heq]
    exact f.continuous)
  exact ⟨⟨g, hg⟩, hgq⟩

end ArtinPrimitiveRoots.A1.Theta
