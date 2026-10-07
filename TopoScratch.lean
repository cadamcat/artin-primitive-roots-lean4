import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Order.Filter.Cofinite
set_option autoImplicit false
open scoped RestrictedProduct
universe u v
variable {ι : Type u} {G : ι → Type v} {A : ∀ i, Set (G i)}
variable [∀ i, TopologicalSpace (G i)]
variable (x : Πʳ i, [G i, A i])
set_option pp.explicit true in
#check @nhds (Πʳ i, [G i, A i]) (RestrictedProduct.topologicalSpace G A cofinite) x
set_option pp.explicit true in
#check @nhds (Πʳ i, [G i, A i]) (inferInstance : TopologicalSpace (Πʳ i, [G i, A i])) x
set_option pp.explicit true in
#check (inferInstance : TopologicalSpace (Πʳ i, [G i, A i]))
#print RestrictedProduct.topologicalSpace
example : @nhds (Πʳ i, [G i, A i])
    (RestrictedProduct.topologicalSpace G A Filter.cofinite) x =
    @nhds (Πʳ i, [G i, A i])
      (inferInstance : TopologicalSpace (Πʳ i, [G i, A i])) x := by
  rfl
